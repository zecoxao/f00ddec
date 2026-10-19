"""
Interactive IDA custom viewer for f00ddec pseudocode.

Provides:
- Right-click context menu and hotkeys for:
  - Renaming variables and functions ('N') with IDB netnode persistence.
  - Setting variable and function types ('Y') with IDA type system integration.
  - Linking / synchronizing with IDA's disassembly view (follows cursor across functions).
  - Jumping to disassembly and clicking through to callee functions ('Enter' / 'Space' / double-click).
  - Refreshing decompilation ('F5').
- Reusable dockable window that updates in place during navigation.
"""

import re
import ida_kernwin
import ida_funcs
import ida_lines
import ida_typeinf
import idaapi

from . import highlight, ida_bridge, db

_EA = re.compile(r"\b(?:loc_|sub_)([0-9A-Fa-f]+)\b")
_ADDR_HEX = re.compile(r"\b0x([0-9A-Fa-f]{5,8})\b")
_VIEW_TITLE = "f00ddec - Pseudocode"

ACTION_RENAME = "f00ddec:rename_var"
ACTION_SET_TYPE = "f00ddec:set_type"
ACTION_TOGGLE_SYNC = "f00ddec:toggle_sync"
ACTION_JUMP_DISASM = "f00ddec:jump_disasm"
ACTION_REFRESH = "f00ddec:refresh"

_active_viewer = None
_ui_hooks = None
_view_hooks = None


def _is_dark_theme():
    """Detect if IDA is currently using a dark theme."""
    try:
        from PySide6 import QtWidgets, QtGui
        app = QtWidgets.QApplication.instance()
        if app:
            pal = app.palette()
            role = QtGui.QPalette.ColorRole.Base if hasattr(QtGui.QPalette, "ColorRole") else QtGui.QPalette.Base
            return pal.color(role).lightness() < 128
    except Exception:
        pass
    try:
        from PyQt5 import QtWidgets, QtGui
        app = QtWidgets.QApplication.instance()
        if app:
            pal = app.palette()
            role = QtGui.QPalette.ColorRole.Base if hasattr(QtGui.QPalette, "ColorRole") else QtGui.QPalette.Base
            return pal.color(role).lightness() < 128
    except Exception:
        pass
    return False


def _get_highlight_colors():
    """Return (asm_highlight_color, decomp_highlight_bg) based on active IDA theme."""
    if _is_dark_theme():
        # Soft slate blue / dark cyan highlight in dark mode
        return 0x304855, 0x283848
    else:
        # Soft sky blue / cyan highlight in light mode
        return 0xC0E0FF, 0xD0E8FF


def _line_ea(line):
    """Extract code linear address from loc_XXXXX, sub_XXXXX, or 0xXXXXX in line."""
    clean = ida_lines.tag_remove(line) if hasattr(ida_lines, "tag_remove") else line
    m = _EA.search(clean)
    if m:
        try:
            return int(m.group(1), 16)
        except ValueError:
            pass
    m = _ADDR_HEX.search(clean)
    if m:
        try:
            return int(m.group(1), 16)
        except ValueError:
            pass
    return None


def _jumpto_disasm(ea):
    """Jump to ea in IDA disassembly view (IDA View-A)."""
    if ea is None:
        return False
    try:
        flags = getattr(ida_kernwin, "UIJMP_IDAVIEW", 0x0001)
        return ida_kernwin.jumpto(ea, -1, flags)
    except Exception:
        try:
            return idaapi.jumpto(ea)
        except Exception:
            return False


class _ActionHandler(ida_kernwin.action_handler_t):
    def __init__(self, view, callback):
        super().__init__()
        self.view = view
        self.callback = callback

    def activate(self, ctx):
        self.callback()
        return 1

    def update(self, ctx):
        if not self.view:
            return ida_kernwin.AST_DISABLE_FOR_WIDGET
        widget = self.view.GetWidget()
        if widget and ctx.widget == widget:
            return ida_kernwin.AST_ENABLE_FOR_WIDGET
        return ida_kernwin.AST_DISABLE_FOR_WIDGET


class _DecompilerView(ida_kernwin.simplecustviewer_t):
    def __init__(self):
        super().__init__()
        self.current_func_ea = None
        self.current_func_name = None
        self.line_ea = []
        self.line_to_eas = {}
        self.ea_to_line = {}
        self.raw_lines = []
        self.header_count = 0
        self._selected_line = None
        self._highlighted_asm_eas = set()
        self._sync_lock = False
        self.sync_with_disasm = db.get_sync_enabled()

    def build_or_refresh(self, fn):
        """Populate or update lines with decompiled Function fn."""
        self.header_count = getattr(fn, "header_count", 0) or getattr(fn.lines, "header_count", 0)
        self.clear_asm_highlights()
        self.current_func_ea = fn.entry
        self.current_func_name = fn.name
        self.line_ea = []
        self.line_to_eas = getattr(fn, "line_to_eas", {}) or {}
        self.ea_to_line = getattr(fn, "ea_to_line", {}) or {}
        self.raw_lines = list(fn.lines)
        self._selected_line = None

        self.ClearLines()
        fn_line_eas = getattr(fn, "line_eas", None) or getattr(fn.lines, "line_eas", None)
        for i, ln in enumerate(fn.lines):
            self.AddLine(highlight.colorize(ln))
            ea = fn_line_eas[i] if (fn_line_eas and i < len(fn_line_eas)) else None
            self.line_ea.append(ea if ea is not None else _line_ea(ln))
        self.Refresh()

        # If IDA's screen cursor is already at a specific executable body statement,
        # scroll to and highlight that statement.
        initial_stmt_line = None
        try:
            screen_ea = ida_kernwin.get_screen_ea()
            if screen_ea is not None and screen_ea in self.ea_to_line:
                cand = self.ea_to_line[screen_ea]
                if cand >= self.header_count:
                    initial_stmt_line = cand
        except Exception:
            pass

        if initial_stmt_line is not None and initial_stmt_line < len(self.raw_lines):
            self.select_line(initial_stmt_line, jump=True, update_asm=True, jump_asm=False)
        else:
            # When selecting a function, position view at the top without highlighting row 0
            self._selected_line = None
            try:
                self.Jump(0, 0)
            except Exception:
                pass

    def clear_asm_highlights(self):
        """Restore default background color for all previously highlighted asm instructions."""
        if not self._highlighted_asm_eas:
            return
        import ida_nalt
        for ea in list(self._highlighted_asm_eas):
            try:
                ida_nalt.del_item_color(ea)
            except Exception:
                pass
        self._highlighted_asm_eas.clear()
        try:
            ida_kernwin.refresh_idaview_anyway()
        except Exception:
            pass

    def select_line(self, lineno, jump=False, update_asm=True, jump_asm=True):
        """Move selection to lineno, visually highlight row, and sync asm highlight."""
        if lineno < 0 or lineno >= len(self.raw_lines):
            return
        prev_line = self._selected_line
        self._selected_line = lineno

        asm_color, decomp_bg = _get_highlight_colors()

        # Unhighlight previous decompiled line
        if prev_line is not None and prev_line != lineno and 0 <= prev_line < len(self.raw_lines):
            try:
                self.EditLine(prev_line, highlight.colorize(self.raw_lines[prev_line]), bgcolor=0xFFFFFFFF)
            except Exception:
                pass

        # Highlight current decompiled line if it has content
        if self.raw_lines[lineno].strip():
            try:
                self.EditLine(lineno, highlight.colorize(self.raw_lines[lineno]), bgcolor=decomp_bg)
                self.RefreshCurrent()
            except Exception:
                pass
        else:
            self._selected_line = None

        if jump:
            try:
                self.Jump(lineno, 0)
            except Exception:
                pass

        if update_asm:
            self._update_asm_highlight_for_line(lineno, jump_asm=jump_asm)

    def _update_asm_highlight_for_line(self, lineno, jump_asm=True):
        """Highlight assembly instructions in IDA disassembly corresponding to decompiled line."""
        import ida_nalt

        # Clear previous asm highlights
        for ea in list(self._highlighted_asm_eas):
            try:
                ida_nalt.del_item_color(ea)
            except Exception:
                pass
        self._highlighted_asm_eas.clear()

        eas = self.line_to_eas.get(lineno, [])
        if not eas and lineno < len(self.line_ea) and self.line_ea[lineno] is not None:
            eas = [self.line_ea[lineno]]

        if not eas:
            if self.line_to_eas:
                nearest_line = min(self.line_to_eas.keys(), key=lambda l: abs(l - lineno))
                eas = self.line_to_eas[nearest_line]
            elif self.current_func_ea is not None:
                eas = [self.current_func_ea]

        if eas:
            asm_color, _ = _get_highlight_colors()
            for ea in eas:
                try:
                    ida_nalt.set_item_color(ea, asm_color)
                    self._highlighted_asm_eas.add(ea)
                except Exception:
                    pass
            try:
                ida_kernwin.refresh_idaview_anyway()
            except Exception:
                pass

            if self.sync_with_disasm and jump_asm:
                try:
                    self._sync_lock = True
                    _jumpto_disasm(eas[0])
                except Exception:
                    pass
                finally:
                    self._sync_lock = False
        else:
            try:
                ida_kernwin.refresh_idaview_anyway()
            except Exception:
                pass

    def sync_from_disasm_ea(self, ea):
        """Called when cursor moves in disassembly; syncs selection in decompiled view."""
        if self._sync_lock:
            return
        lineno = self.ea_to_line.get(ea)
        if lineno is None:
            lineno = self._find_closest_line(ea)

        # If cursor in disassembly is at the function entry or prologue (header lines),
        # clear body statement highlight and position at top of function without highlighting row 0
        if lineno is None or lineno < self.header_count:
            if self._selected_line is not None:
                if 0 <= self._selected_line < len(self.raw_lines):
                    try:
                        self.EditLine(self._selected_line, highlight.colorize(self.raw_lines[self._selected_line]), bgcolor=0xFFFFFFFF)
                    except Exception:
                        pass
                self._selected_line = None
            self.clear_asm_highlights()
            return

        if lineno == self._selected_line:
            return

        self._sync_lock = True
        try:
            self.select_line(lineno, jump=True, update_asm=True, jump_asm=False)
        finally:
            self._sync_lock = False

    def _find_closest_line(self, ea):
        """Find the decompiled line whose instruction EA is closest to ea."""
        if not self.ea_to_line:
            return None
        closest_ea = min(self.ea_to_line.keys(), key=lambda e: abs(e - ea))
        return self.ea_to_line[closest_ea]

    def on_cursor_changed(self):
        """Called when user clicks or navigates in decompiler window."""
        if self._sync_lock:
            return
        pos = self.GetPos()
        if not pos:
            return
        lineno = pos[0]
        if lineno < 0 or lineno >= len(self.raw_lines):
            return
        if lineno == self._selected_line:
            return

        self._sync_lock = True
        try:
            self.select_line(lineno, jump=False, update_asm=True, jump_asm=True)
        finally:
            self._sync_lock = False

    def OnCursorPosChanged(self):
        self.on_cursor_changed()

    def OnClick(self, shift):
        self.on_cursor_changed()

    def Close(self):
        self.clear_asm_highlights()
        return super().Close()

    def show_func(self, ea):
        """Decompile function at ea and refresh view."""
        pfn = ida_funcs.get_func(ea)
        entry = pfn.start_ea if pfn else ea
        try:
            fn = ida_bridge.decompile_one(entry)
            self.build_or_refresh(fn)
            return True
        except Exception as exc:
            print("f00ddec: decompilation failed for 0x%X: %s" % (entry, exc))
            return False

    def get_word_under_cursor(self):
        """Return the identifier under cursor and the line number."""
        pos = self.GetPos()
        if not pos:
            word = self.GetCurrentWord()
            return word or "", 0
        lineno, col = pos[0], pos[1]
        if lineno < 0 or lineno >= len(self.raw_lines):
            return "", lineno
        line = self.raw_lines[lineno]
        if not line:
            return "", lineno
        if col < 0:
            col = 0
        elif col >= len(line):
            col = len(line) - 1

        # Check identifier character boundary
        if not (line[col].isalnum() or line[col] == "_"):
            if col > 0 and (line[col - 1].isalnum() or line[col - 1] == "_"):
                col -= 1
            elif col + 1 < len(line) and (line[col + 1].isalnum() or line[col + 1] == "_"):
                col += 1
            else:
                return "", lineno

        start = col
        while start > 0 and (line[start - 1].isalnum() or line[start - 1] == "_"):
            start -= 1
        end = col
        while end < len(line) and (line[end].isalnum() or line[end] == "_"):
            end += 1
        return line[start:end], lineno

    def on_rename(self):
        """Rename variable or function under cursor and persist in IDB netnode."""
        if self.current_func_ea is None:
            return
        word, lineno = self.get_word_under_cursor()
        if not word:
            word = ida_kernwin.ask_str("", 0, "Enter variable name to rename")
            if not word:
                return

        new_name = ida_kernwin.ask_str(word, 0, f"Rename '{word}' in {self.current_func_name or 'function'}")
        if new_name is None:
            return
        new_name = new_name.strip()

        # If renaming the function itself
        if word == self.current_func_name or (lineno == 0 and ("(" in self.raw_lines[0])):
            import ida_name
            if new_name:
                ida_name.set_name(self.current_func_ea, new_name)
                self.current_func_name = new_name
            self.show_func(self.current_func_ea)
            return

        # Save variable rename to persistent IDB netnode
        db.set_var_rename(self.current_func_ea, word, new_name)

        # If word is a global symbol in IDA, also rename in IDA's name table
        try:
            import ida_name, ida_idaapi
            ea = ida_name.get_name_ea(ida_idaapi.BADADDR, word)
            if ea != ida_idaapi.BADADDR and new_name:
                ida_name.set_name(ea, new_name)
        except Exception:
            pass

        # If it's a stack frame variable, also rename in IDA's frame struct
        self._rename_frame_member(word, new_name)

        # Refresh decompile
        self.show_func(self.current_func_ea)

    def _rename_frame_member(self, old_name, new_name):
        """Rename stack variable member in IDA's frame structure if present."""
        try:
            import ida_frame
            pfn = ida_funcs.get_func(self.current_func_ea)
            if not pfn:
                return
            tif = ida_typeinf.tinfo_t()
            if ida_frame.get_func_frame(tif, pfn):
                udt = ida_typeinf.udt_type_data_t()
                if tif.get_udt_details(udt):
                    for m in udt:
                        if m.name == old_name:
                            m.name = new_name
                            tif.create_udt(udt, ida_typeinf.BTF_STRUCT)
                            break
        except Exception:
            pass

    def on_set_type(self):
        """Set variable type or function prototype and persist in IDB netnode."""
        if self.current_func_ea is None:
            return
        word, lineno = self.get_word_under_cursor()
        is_sig_line = (lineno == 0) or ("(" in self.raw_lines[lineno] and ")" in self.raw_lines[lineno] and not self.raw_lines[lineno].strip().endswith(";"))

        if is_sig_line or word == self.current_func_name:
            # Edit function prototype
            data = db.get_func_data(self.current_func_ea)
            curr_proto = data.get("proto") or (self.raw_lines[0] if self.raw_lines else "")
            new_proto = ida_kernwin.ask_str(curr_proto, 0, f"Set Function Prototype for {self.current_func_name}")
            if new_proto is None:
                return
            new_proto = new_proto.strip()
            db.set_func_proto(self.current_func_ea, new_proto)

            # Apply to IDA type system
            if new_proto:
                try:
                    ida_typeinf.apply_cdecl(None, self.current_func_ea, new_proto)
                except Exception:
                    pass

            self.show_func(self.current_func_ea)
            return

        if not word:
            return

        # Edit variable type
        data = db.get_func_data(self.current_func_ea)
        curr_type = data.get("types", {}).get(word, "int")
        new_type = ida_kernwin.ask_str(curr_type, 0, f"Set Type for variable '{word}'")
        if new_type is None:
            return
        new_type = new_type.strip()
        db.set_var_type(self.current_func_ea, word, new_type)

        self.show_func(self.current_func_ea)

    def toggle_sync(self):
        """Toggle synchronization with IDA disassembly view."""
        self.sync_with_disasm = not self.sync_with_disasm
        db.set_sync_enabled(self.sync_with_disasm)
        state_str = "ENABLED" if self.sync_with_disasm else "DISABLED"
        print(f"f00ddec: Sync with Disassembly {state_str}")
        if self.sync_with_disasm:
            ea = ida_kernwin.get_screen_ea()
            pfn = ida_funcs.get_func(ea)
            if pfn and pfn.start_ea != self.current_func_ea:
                self.show_func(pfn.start_ea)

    def jump_disasm(self):
        """Jump to the linear address or switch decompiler view to callee function."""
        word, lineno = self.get_word_under_cursor()
        if word:
            # 1. Check if word is a function in IDA -> click-through to that function!
            try:
                import ida_name, ida_idaapi
                target_ea = ida_name.get_name_ea(ida_idaapi.BADADDR, word)
                if target_ea != ida_idaapi.BADADDR:
                    pfn = ida_funcs.get_func(target_ea)
                    if pfn and pfn.start_ea == target_ea:
                        _jumpto_disasm(target_ea)
                        if target_ea != self.current_func_ea:
                            self.show_func(target_ea)
                        return True
                    else:
                        _jumpto_disasm(target_ea)
                        return True
            except Exception:
                pass

            # 2. Check if word is sub_XXXXXX or loc_XXXXXX
            m = _EA.search(word)
            if m:
                try:
                    target_ea = int(m.group(1), 16)
                    pfn = ida_funcs.get_func(target_ea)
                    _jumpto_disasm(target_ea)
                    if pfn and pfn.start_ea == target_ea and target_ea != self.current_func_ea:
                        self.show_func(target_ea)
                    return True
                except ValueError:
                    pass

            # 3. Check hex address
            m = _ADDR_HEX.search(word)
            if m:
                try:
                    target_ea = int(m.group(1), 16)
                    _jumpto_disasm(target_ea)
                    return True
                except ValueError:
                    pass

        # Fallback: jump to line_ea or line_to_eas of current line
        target_ea = None
        if lineno is not None:
            if lineno in self.line_to_eas and self.line_to_eas[lineno]:
                target_ea = self.line_to_eas[lineno][0]
            elif lineno < len(self.line_ea) and self.line_ea[lineno] is not None:
                target_ea = self.line_ea[lineno]
            elif self.line_to_eas:
                nearest_line = min(self.line_to_eas.keys(), key=lambda l: abs(l - lineno))
                target_ea = self.line_to_eas[nearest_line][0]
            elif self.current_func_ea is not None:
                target_ea = self.current_func_ea

        if target_ea is not None:
            _jumpto_disasm(target_ea)
            return True
        return False

    def OnDblClick(self, shift):
        return self.jump_disasm()

    def OnKeydown(self, vkey, shift):
        if vkey in (ord('N'), ord('n')):
            self.on_rename()
            return True
        if vkey in (ord('Y'), ord('y')):
            self.on_set_type()
            return True
        if vkey == 116:  # F5
            if self.current_func_ea is not None:
                self.show_func(self.current_func_ea)
            return True
        if vkey in (13, 32):  # Enter or Space
            return self.jump_disasm()
        if vkey == 9:  # Tab
            self.toggle_sync()
            return True
        if vkey == 27:  # Esc
            global _active_viewer
            self.clear_asm_highlights()
            _active_viewer = None
            self.Close()
            return True
        # Navigation keys: Up(38), Down(40), PageUp(33), PageDown(34), Home(36), End(35)
        if vkey in (38, 40, 33, 34, 36, 35):
            try:
                ida_kernwin.execute_ui_requests([self.on_cursor_changed])
            except Exception:
                pass
        return False


class _UiHooks(ida_kernwin.UI_Hooks):
    def __init__(self, view):
        super().__init__()
        self.view = view

    def screen_ea_changed(self, ea, prev_ea):
        """Automatically follow current function in disassembly and sync line selection."""
        if not self.view or self.view._sync_lock:
            return
        if _active_viewer is not self.view:
            return
        pfn = ida_funcs.get_func(ea)
        if pfn is None:
            return
        if pfn.start_ea != self.view.current_func_ea:
            if self.view.sync_with_disasm:
                self.view.show_func(pfn.start_ea)
            else:
                return
        self.view.sync_from_disasm_ea(ea)

    def widget_invisible(self, widget):
        """Reset active viewer when the decompiler window is closed."""
        if self.view and widget == self.view.GetWidget():
            global _active_viewer
            self.view.clear_asm_highlights()
            _active_viewer = None

    def finish_populating_widget_popup(self, widget, popup_handle):
        """Attach decompiler context actions to the right-click popup menu."""
        if not self.view:
            return
        view_widget = self.view.GetWidget()
        if widget != view_widget:
            return

        ida_kernwin.attach_action_to_popup(widget, popup_handle, ACTION_RENAME)
        ida_kernwin.attach_action_to_popup(widget, popup_handle, ACTION_SET_TYPE)
        ida_kernwin.attach_action_to_popup(widget, popup_handle, ACTION_TOGGLE_SYNC)
        ida_kernwin.attach_action_to_popup(widget, popup_handle, ACTION_JUMP_DISASM)
        ida_kernwin.attach_action_to_popup(widget, popup_handle, ACTION_REFRESH)


class _CustViewHooks(ida_kernwin.View_Hooks):
    def __init__(self, view):
        super().__init__()
        self.view = view

    def view_curpos(self, view):
        """Called whenever cursor position changes in any view."""
        if self.view and view == self.view.GetWidget():
            self.view.on_cursor_changed()

    def view_click(self, view, event):
        """Called on mouse click in view."""
        if self.view and view == self.view.GetWidget():
            self.view.on_cursor_changed()

    def view_close(self, view):
        """Called when view is closed."""
        if self.view and view == self.view.GetWidget():
            self.view.clear_asm_highlights()


def _register_actions(view):
    """Register IDA actions for popup menu."""
    actions = [
        (ACTION_RENAME, "Rename variable/symbol... (N)", view.on_rename),
        (ACTION_SET_TYPE, "Set variable/function type... (Y)", view.on_set_type),
        (ACTION_TOGGLE_SYNC, "Sync with Disassembly (Tab)", view.toggle_sync),
        (ACTION_JUMP_DISASM, "Jump to Disassembly / Callee (Enter)", view.jump_disasm),
        (ACTION_REFRESH, "Refresh Decompilation (F5)", lambda: view.show_func(view.current_func_ea)),
    ]
    for action_id, label, callback in actions:
        ida_kernwin.unregister_action(action_id)
        desc = ida_kernwin.action_desc_t(
            action_id,
            label,
            _ActionHandler(view, callback),
            None,
            label
        )
        ida_kernwin.register_action(desc)


def show(function):
    """Open or refresh the dockable decompiler view for the specified function."""
    global _active_viewer, _ui_hooks, _view_hooks
    if _active_viewer is None or _active_viewer.GetWidget() is None:
        v = _DecompilerView()
        if not v.Create(_VIEW_TITLE):
            return None
        _active_viewer = v
        _register_actions(_active_viewer)

        if _ui_hooks is None:
            _ui_hooks = _UiHooks(_active_viewer)
            _ui_hooks.hook()
        else:
            _ui_hooks.view = _active_viewer

        if _view_hooks is None:
            _view_hooks = _CustViewHooks(_active_viewer)
            _view_hooks.hook()
        else:
            _view_hooks.view = _active_viewer

    _active_viewer.build_or_refresh(function)
    _active_viewer.Show()
    return _active_viewer


def show_listing(title, lines):
    """Fallback simple viewer for whole-program export listing."""
    v = ida_kernwin.simplecustviewer_t()
    if v.Create(title):
        for ln in lines:
            v.AddLine(highlight.colorize(ln))
        v.Show()
        return v
    return None


def cleanup():
    """Unregister hooks and actions on plugin unload."""
    global _active_viewer, _ui_hooks, _view_hooks
    if _active_viewer is not None:
        try:
            _active_viewer.clear_asm_highlights()
        except Exception:
            pass
    if _ui_hooks is not None:
        try:
            _ui_hooks.unhook()
        except Exception:
            pass
        _ui_hooks = None
    if _view_hooks is not None:
        try:
            _view_hooks.unhook()
        except Exception:
            pass
        _view_hooks = None
    for action_id in [ACTION_RENAME, ACTION_SET_TYPE, ACTION_TOGGLE_SYNC, ACTION_JUMP_DISASM, ACTION_REFRESH]:
        try:
            ida_kernwin.unregister_action(action_id)
        except Exception:
            pass
    _active_viewer = None
