from __future__ import annotations

import ast
import ctypes
import hashlib
import json
import locale
import math
import os
import queue
import re
import sys
import time
import tkinter as tk
from collections import OrderedDict
from copy import deepcopy
from ctypes import wintypes
from dataclasses import dataclass, field
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
from typing import Optional

from PIL import Image, ImageFilter, ImageSequence, ImageTk

try:
    import windnd
except Exception:
    windnd = None

APP_VERSION = "0.88"
SUPPORTED_EXTS = {".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp"}
if getattr(sys, "frozen", False):
    APP_DIR = Path(sys.executable).resolve().parent
    RESOURCE_DIR = Path(getattr(sys, "_MEIPASS", APP_DIR))
else:
    APP_DIR = Path(__file__).resolve().parent
    RESOURCE_DIR = APP_DIR
STATE_DIR = APP_DIR / "state"
TEMPLATE_DIR = STATE_DIR / "templates"
HISTORY_DIR = STATE_DIR / "history"
THUMB_CACHE_DIR = STATE_DIR / "thumbs"
I18N_DIR = RESOURCE_DIR / "i18n"
SESSION_FILE = STATE_DIR / "session.json"
UI_STATE_FILE = STATE_DIR / "ui_state.json"
CACHE_LIMIT = 2200
THUMB_CACHE_LIMIT = 280
ICON_ICO_PATH = RESOURCE_DIR / "assets" / "picread_icon.ico"
ICON_PNG_PATH = RESOURCE_DIR / "assets" / "picread_icon.png"
LOAD_PROFILES = {
    "低负载": {
        "cache_limit": 2200,
        "budget_scale": 1.0,
        "memory_hint_gb": 7,
    },
    "中负载": {
        "cache_limit": 5200,
        "budget_scale": 1.35,
        "memory_hint_gb": 16,
    },
    "高负载": {
        "cache_limit": 7800,
        "budget_scale": 1.7,
        "memory_hint_gb": 24,
    },
    "极限负载": {
        "cache_limit": 12800,
        "budget_scale": 2.35,
        "memory_hint_gb": 40,
    },
}
PERF_MODES = {
    "高画质": {
        "tick_ms": 16,
        "frame_budget": 36,
        "resample": Image.Resampling.LANCZOS,
        "multi_step": True,
        "two_pass": True,
        "pre_blur": 0.15,
        "sharpen": False,
        "strategy": "LANCZOS 多段缩放",
    },
    "平衡": {
        "tick_ms": 20,
        "frame_budget": 26,
        "resample": Image.Resampling.LANCZOS,
        "multi_step": True,
        "two_pass": False,
        "pre_blur": 0.0,
        "sharpen": False,
        "strategy": "LANCZOS 平衡",
    },
    "高流畅": {
        "tick_ms": 28,
        "frame_budget": 18,
        "resample": Image.Resampling.BICUBIC,
        "multi_step": False,
        "two_pass": False,
        "pre_blur": 0.0,
        "sharpen": False,
        "strategy": "BICUBIC 快速",
    },
}
DEFAULT_PERF_MODES = deepcopy(PERF_MODES)
LAYOUT_ALGORITHMS = {
    "legacy": "算法1",
    "justified": "算法2",
    "balanced": "算法3",
}
RESAMPLE_NAME_TO_VALUE = {
    "LANCZOS": Image.Resampling.LANCZOS,
    "BICUBIC": Image.Resampling.BICUBIC,
    "BILINEAR": Image.Resampling.BILINEAR,
}
RESAMPLE_VALUE_TO_NAME = {v: k for k, v in RESAMPLE_NAME_TO_VALUE.items()}
LANGUAGE_OPTIONS = {
    "zh_CN": "简体中文",
    "en_US": "English",
}
BATCH_ORDER_OPTIONS = {
    "normal": "正序",
    "reverse": "倒序",
}


class Win32DropManager:
    WM_DROPFILES = 0x0233
    GWL_WNDPROC = -4

    def __init__(self) -> None:
        if not sys.platform.startswith("win"):
            raise RuntimeError("Win32 drop is only available on Windows.")

        self._user32 = ctypes.windll.user32
        self._shell32 = ctypes.windll.shell32
        self._is_64bit = ctypes.sizeof(ctypes.c_void_p) == 8
        self._wndproc_type = ctypes.WINFUNCTYPE(
            ctypes.c_longlong if self._is_64bit else ctypes.c_long,
            wintypes.HWND,
            wintypes.UINT,
            wintypes.WPARAM,
            wintypes.LPARAM,
        )
        self._callbacks: dict[int, object] = {}
        self._orig_wndprocs: dict[int, int] = {}
        self._wndproc_refs: dict[int, object] = {}

        self._shell32.DragAcceptFiles.argtypes = [wintypes.HWND, wintypes.BOOL]
        self._shell32.DragAcceptFiles.restype = None
        self._shell32.DragQueryFileW.argtypes = [wintypes.HANDLE, wintypes.UINT, wintypes.LPWSTR, wintypes.UINT]
        self._shell32.DragQueryFileW.restype = wintypes.UINT
        self._shell32.DragFinish.argtypes = [wintypes.HANDLE]
        self._shell32.DragFinish.restype = None
        self._change_msg_filter = getattr(self._user32, "ChangeWindowMessageFilterEx", None)
        if self._change_msg_filter is not None:
            self._change_msg_filter.restype = wintypes.BOOL
            self._change_msg_filter.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.DWORD, ctypes.c_void_p]

        if self._is_64bit:
            self._set_wndproc = self._user32.SetWindowLongPtrW
            self._set_wndproc.restype = ctypes.c_void_p
            self._set_wndproc.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
            self._call_wndproc = self._user32.CallWindowProcW
            self._call_wndproc.restype = ctypes.c_longlong
            self._call_wndproc.argtypes = [
                ctypes.c_void_p,
                wintypes.HWND,
                wintypes.UINT,
                wintypes.WPARAM,
                wintypes.LPARAM,
            ]
        else:
            self._set_wndproc = self._user32.SetWindowLongW
            self._set_wndproc.restype = ctypes.c_void_p
            self._set_wndproc.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
            self._call_wndproc = self._user32.CallWindowProcW
            self._call_wndproc.restype = ctypes.c_long
            self._call_wndproc.argtypes = [
                ctypes.c_void_p,
                wintypes.HWND,
                wintypes.UINT,
                wintypes.WPARAM,
                wintypes.LPARAM,
            ]

    def bind(self, widget: tk.Misc, callback) -> None:
        widget.update_idletasks()
        hwnd = int(widget.winfo_id())
        self._callbacks[hwnd] = callback
        if self._change_msg_filter is not None:
            try:
                MSGFLT_ALLOW = 1
                self._change_msg_filter(hwnd, self.WM_DROPFILES, MSGFLT_ALLOW, None)
                self._change_msg_filter(hwnd, 0x0049, MSGFLT_ALLOW, None)  # WM_COPYGLOBALDATA
                self._change_msg_filter(hwnd, 0x004A, MSGFLT_ALLOW, None)  # WM_COPYDATA
            except Exception:
                pass
        self._shell32.DragAcceptFiles(hwnd, True)

        if hwnd in self._orig_wndprocs:
            return

        @self._wndproc_type
        def _wndproc(h_wnd, msg, w_param, l_param):
            if msg == self.WM_DROPFILES:
                try:
                    cb = self._callbacks.get(int(h_wnd))
                    paths = self._extract_paths(w_param)
                    if cb is not None:
                        cb(paths)
                except Exception:
                    pass
                finally:
                    try:
                        self._shell32.DragFinish(w_param)
                    except Exception:
                        pass
                return 0

            orig = self._orig_wndprocs.get(int(h_wnd))
            if orig:
                return self._call_wndproc(orig, h_wnd, msg, w_param, l_param)
            return 0

        prev = self._set_wndproc(hwnd, self.GWL_WNDPROC, ctypes.cast(_wndproc, ctypes.c_void_p).value)
        if not prev:
            raise RuntimeError(f"SetWindowLongPtr failed for hwnd={hwnd}")
        self._orig_wndprocs[hwnd] = int(prev)
        self._wndproc_refs[hwnd] = _wndproc

    def _extract_paths(self, hdrop) -> list[str]:
        files: list[str] = []
        count = int(self._shell32.DragQueryFileW(hdrop, 0xFFFFFFFF, None, 0))
        for idx in range(count):
            length = int(self._shell32.DragQueryFileW(hdrop, idx, None, 0))
            if length <= 0:
                continue
            buf = ctypes.create_unicode_buffer(length + 1)
            self._shell32.DragQueryFileW(hdrop, idx, buf, length + 1)
            if buf.value:
                files.append(buf.value)
        return files


class BoxToggle(tk.Frame):
    def __init__(
        self,
        master,
        text: str,
        variable,
        *,
        command=None,
        bg: str,
        fg: str,
        accent: str,
        box_size: int = 18,
        font=("Microsoft YaHei UI", 11),
    ):
        super().__init__(master, bg=bg, bd=0, highlightthickness=0)
        self.variable = variable
        self.command = command
        self.bg = bg
        self.fg = fg
        self.accent = accent
        self.box_size = box_size
        self.canvas = tk.Canvas(self, width=box_size, height=box_size, bg=bg, highlightthickness=0, bd=0)
        self.canvas.pack(side=tk.LEFT, padx=(0, 8))
        self.label = tk.Label(self, text=text, bg=bg, fg=fg, font=font)
        self.label.pack(side=tk.LEFT)
        self.bind("<Button-1>", self._toggle)
        self.canvas.bind("<Button-1>", self._toggle)
        self.label.bind("<Button-1>", self._toggle)
        self._trace_id = self.variable.trace_add("write", lambda *_: self._redraw())
        self._redraw()

    def _toggle(self, _evt=None) -> None:
        self.variable.set(not bool(self.variable.get()))
        if self.command:
            self.command()

    def _redraw(self) -> None:
        s = self.box_size
        self.canvas.delete("all")
        self.canvas.create_rectangle(1, 1, s - 1, s - 1, outline="#cfcfcf", width=1, fill=self.bg)
        if bool(self.variable.get()):
            self.canvas.create_rectangle(3, 3, s - 3, s - 3, outline=self.accent, width=1, fill=self.accent)
            self.canvas.create_line(5, s // 2, s // 2 - 1, s - 5, fill="#ffffff", width=2)
            self.canvas.create_line(s // 2 - 1, s - 5, s - 4, 5, fill="#ffffff", width=2)

    def set_text(self, text: str) -> None:
        self.label.configure(text=text)


class DotRadio(tk.Frame):
    def __init__(
        self,
        master,
        text: str,
        variable,
        value: str,
        *,
        command=None,
        bg: str,
        fg: str,
        accent: str,
        box_size: int = 18,
        font=("Microsoft YaHei UI", 11),
    ):
        super().__init__(master, bg=bg, bd=0, highlightthickness=0)
        self.variable = variable
        self.value = value
        self.command = command
        self.bg = bg
        self.fg = fg
        self.accent = accent
        self.box_size = box_size
        self.canvas = tk.Canvas(self, width=box_size, height=box_size, bg=bg, highlightthickness=0, bd=0)
        self.canvas.pack(side=tk.LEFT, padx=(0, 8))
        self.label = tk.Label(self, text=text, bg=bg, fg=fg, font=font)
        self.label.pack(side=tk.LEFT)
        self.bind("<Button-1>", self._select)
        self.canvas.bind("<Button-1>", self._select)
        self.label.bind("<Button-1>", self._select)
        self._trace_id = self.variable.trace_add("write", lambda *_: self._redraw())
        self._redraw()

    def _select(self, _evt=None) -> None:
        self.variable.set(self.value)
        if self.command:
            self.command()

    def _redraw(self) -> None:
        s = self.box_size
        self.canvas.delete("all")
        self.canvas.create_oval(1, 1, s - 1, s - 1, outline="#cfcfcf", width=1, fill=self.bg)
        if str(self.variable.get()) == str(self.value):
            self.canvas.create_oval(5, 5, s - 5, s - 5, outline=self.accent, width=1, fill=self.accent)

    def set_text(self, text: str) -> None:
        self.label.configure(text=text)


@dataclass
class ImageItem:
    path: Path
    pil_image: Image.Image
    width: int
    height: int
    is_gif: bool = False
    gif_frames: list[Image.Image] = field(default_factory=list)
    gif_durations: list[int] = field(default_factory=list)
    gif_index: int = 0
    next_due: float = 0.0

    @classmethod
    def from_path(cls, path: Path) -> "ImageItem":
        img = Image.open(path)
        is_gif = path.suffix.lower() == ".gif" and getattr(img, "is_animated", False)

        if is_gif:
            frames: list[Image.Image] = []
            durations: list[int] = []
            for frame in ImageSequence.Iterator(img):
                rgba = frame.convert("RGBA")
                frames.append(rgba)
                durations.append(max(int(frame.info.get("duration", 100)), 20))
            first = frames[0]
            return cls(
                path=path,
                pil_image=first,
                width=first.width,
                height=first.height,
                is_gif=True,
                gif_frames=frames,
                gif_durations=durations,
            )

        rgba = img.convert("RGBA")
        return cls(path=path, pil_image=rgba, width=rgba.width, height=rgba.height)


class GroupWindow:
    def __init__(
        self,
        app: "PicReadApp",
        group_id: int,
        name: str,
        rows: int,
        smart_layout: bool,
        layout_algorithm: str = "legacy",
        template_path: Optional[Path] = None,
    ):
        self.app = app
        self.group_id = group_id
        self.name = name
        self.rows = max(1, rows)
        self.smart_layout = smart_layout
        self.layout_algorithm = layout_algorithm if layout_algorithm in LAYOUT_ALGORITHMS else "legacy"
        self.template_path = template_path
        self.items: list[ImageItem] = []

        self.top = tk.Toplevel(app.root)
        self.top.geometry("920x620")
        self.top.minsize(420, 280)
        self.top.protocol("WM_DELETE_WINDOW", self._close)
        self.app.apply_window_icon(self.top)

        self.canvas = tk.Canvas(self.top, bg="#111111", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.focus_set()

        self.top.bind("<Configure>", self._on_resize)
        self.top.bind("<FocusIn>", lambda _e: self.app.set_active_group(self.group_id))
        self.canvas.bind("<ButtonPress-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.canvas.bind("<Button-3>", self._on_right_click)
        self.top.bind("<Delete>", self._on_delete_key)

        self._image_refs: list[ImageTk.PhotoImage] = []
        self._last_layout_size: tuple[int, int] = (0, 0)

        self._layout_rows = 1
        self._layout_cols = 1
        self._cell_w = 1
        self._cell_h = 1
        self._layout_rects: list[tuple[int, int, int, int]] = []
        self._slot_image_ids: list[int] = []
        self._slot_frame_ids: list[int] = []
        self._slot_draw_sizes: list[tuple[int, int]] = []
        self._cell_lookup_rects: list[tuple[int, int, int, int]] = []

        self._drag_source_idx: Optional[int] = None
        self._drag_target_idx: Optional[int] = None
        self._drag_active = False
        self._drag_moved = False
        self._press_xy: Optional[tuple[int, int]] = None
        self._press_on_selected_idx: Optional[int] = None
        self._selected_idx: Optional[int] = None
        self._selected_indexes: set[int] = set()
        self._context_idx: Optional[int] = None
        self._select_box_active = False
        self._select_box_start: Optional[tuple[int, int]] = None
        self._select_box_current: Optional[tuple[int, int]] = None

        self._photo_cache: OrderedDict[tuple[str, int, int, int], ImageTk.PhotoImage] = OrderedDict()
        self.cache_hits = 0
        self.cache_misses = 0
        self._last_geometry = ""
        self._gif_round_robin_start = 0
        self.suppress_template_geometry_persist = False
        self._resize_after_id: Optional[str] = None
        self._resizing_until = 0.0
        self._static_render_token = 0
        self._render_batch_after_id: Optional[str] = None
        self._geometry_idle_ms = 950

        self._menu = tk.Menu(self.top, tearoff=0)
        self._menu.add_command(label=self.app.tr("menu.remove_image", "从窗口组移除图片"), command=self._remove_context_item)
        self._menu.add_command(label=self.app.tr("menu.restart_all_gifs", "重播本窗口所有 GIF"), command=self._restart_all_gifs)
        self._menu.add_separator()
        self._menu.add_command(label=self.app.tr("button.save_template", "保存为模板"), command=self._save_as_template_here)
        self._menu.add_command(label=self.app.tr("button.update_template", "更新该模板"), command=self._update_template_here)
        self._menu.add_command(label=self.app.tr("button.reload_template", "重新加载模板"), command=self._reload_template_here)

        self._update_title()
        self._last_geometry = self.top.geometry()

        self.app.bind_drop_target(self.top, self.app.make_drop_handler(self.group_id))
        self.app.bind_drop_target(self.canvas, self.app.make_drop_handler(self.group_id))

    def _save_as_template_here(self) -> None:
        self.app.save_group_template(self)

    def _update_template_here(self) -> None:
        self.app.update_linked_template(self)

    def _reload_template_here(self) -> None:
        self.app.reload_linked_template(self)

    def _restart_all_gifs(self) -> None:
        restarted = False
        for item in self.items:
            if not item.is_gif or not item.gif_frames:
                continue
            item.gif_index = 0
            item.next_due = 0.0
            restarted = True
        if not restarted:
            return
        self._gif_round_robin_start = 0
        self.app.pause_heavy_work(0.25)
        self.render(force=True)

    def _update_title(self) -> None:
        self.top.title(self.name)

    def refresh_localized_texts(self) -> None:
        self._menu.entryconfigure(0, label=self.app.tr("menu.remove_image", "从窗口组移除图片"))
        self._menu.entryconfigure(1, label=self.app.tr("menu.restart_all_gifs", "重播本窗口所有 GIF"))
        self._menu.entryconfigure(3, label=self.app.tr("button.save_template", "保存为模板"))
        self._menu.entryconfigure(4, label=self.app.tr("button.update_template", "更新该模板"))
        self._menu.entryconfigure(5, label=self.app.tr("button.reload_template", "重新加载模板"))

    def set_layout(self, rows: int, smart_layout: bool, layout_algorithm: Optional[str] = None) -> None:
        old_layout = (self.rows, self.smart_layout, self.layout_algorithm)
        self.rows = max(1, rows)
        self.smart_layout = smart_layout
        if layout_algorithm:
            self.layout_algorithm = layout_algorithm if layout_algorithm in LAYOUT_ALGORITHMS else "legacy"
        if old_layout != (self.rows, self.smart_layout, self.layout_algorithm):
            self._last_layout_size = (0, 0)
            self._photo_cache.clear()
        self.app.mark_dirty()
        self.render(force=True)

    def add_paths(self, paths: list[Path], show_errors: bool = True) -> None:
        added = 0
        for p in paths:
            try:
                item = ImageItem.from_path(p)
                self.items.append(item)
                added += 1
            except Exception as exc:
                if show_errors:
                    messagebox.showwarning(self.app.tr("msg.read_failed", "读取失败"), self.app.tr("msg.cannot_read_image", "无法读取图片:\n{path}\n\n{error}", path=p, error=exc))
        if added:
            self.app.mark_dirty()
            self.render(force=True)

    def remove_item_at(self, idx: int) -> None:
        if idx < 0 or idx >= len(self.items):
            return
        self.items.pop(idx)
        self._selected_idx = None
        self._selected_indexes.clear()
        self._context_idx = None
        self.app.mark_dirty()
        self.render(force=True)

    def remove_items_at(self, indexes: list[int]) -> None:
        unique_indexes = sorted({idx for idx in indexes if 0 <= idx < len(self.items)}, reverse=True)
        if not unique_indexes:
            return
        for idx in unique_indexes:
            self.items.pop(idx)
        self._selected_idx = None
        self._selected_indexes.clear()
        self._context_idx = None
        self.app.mark_dirty()
        self.render(force=True)

    def to_state(self) -> dict:
        return {
            "name": self.name,
            "rows": self.rows,
            "smart_layout": self.smart_layout,
            "layout_algorithm": self.layout_algorithm,
            "template_path": str(self.template_path) if self.template_path else "",
            "pinned": self.group_id in self.app._pinned_groups,
            "geometry": self.top.geometry(),
            "images": [str(i.path) for i in self.items],
        }

    def _cancel_render_batch(self) -> None:
        if self._render_batch_after_id:
            try:
                self.top.after_cancel(self._render_batch_after_id)
            except Exception:
                pass
            self._render_batch_after_id = None
        self._static_render_token += 1

    def _on_resize(self, _evt: tk.Event) -> None:
        current_geo = self.top.geometry()
        geometry_changed = current_geo != self._last_geometry
        if geometry_changed:
            self._last_geometry = current_geo
            self.app.mark_dirty()
            self._resizing_until = time.time() + (self._geometry_idle_ms / 1000.0)
            self.app.pause_heavy_work(self._geometry_idle_ms / 1000.0)
            self._cancel_render_batch()

        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        if w <= 1 or h <= 1:
            return
        if geometry_changed or (w, h) != self._last_layout_size:
            if self._resize_after_id:
                try:
                    self.top.after_cancel(self._resize_after_id)
                except Exception:
                    pass
            self._resize_after_id = self.top.after(self._geometry_idle_ms, self._flush_resize_render)

    def _flush_resize_render(self) -> None:
        self._resize_after_id = None
        remaining = self._resizing_until - time.time()
        if remaining > 0:
            self._resize_after_id = self.top.after(max(20, int(remaining * 1000)), self._flush_resize_render)
            return
        size_now = (self.canvas.winfo_width(), self.canvas.winfo_height())
        if size_now != self._last_layout_size:
            self._photo_cache.clear()
        self.render(force=True)

    def _close(self) -> None:
        self.app.persist_template_geometry(self)
        self.app.unregister_group(self.group_id)
        self.top.destroy()

    def _grid_score(self, rows: int, total_w: int, total_h: int) -> float:
        count = len(self.items)
        cols = max(1, math.ceil(count / rows))
        cell_w = max(1, total_w // cols)
        cell_h = max(1, total_h // rows)

        used_area = 0.0
        for item in self.items:
            scale = min(cell_w / item.width, cell_h / item.height)
            used_area += item.width * item.height * (scale * scale)

        holes = rows * cols - count
        hole_penalty = holes * 0.015
        return (used_area / (total_w * total_h)) - hole_penalty

    def _compute_grid(self, total_w: int, total_h: int) -> tuple[int, int, int, int]:
        count = len(self.items)
        rows = self.rows

        if self.smart_layout and count > 0:
            best_rows = 1
            best_score = -1.0
            max_rows = min(count, 12)
            for candidate_rows in range(1, max_rows + 1):
                score = self._grid_score(candidate_rows, total_w, total_h)
                if score > best_score:
                    best_score = score
                    best_rows = candidate_rows
            rows = best_rows

        cols = max(1, math.ceil(count / rows))
        cell_w = max(1, total_w // cols)
        cell_h = max(1, total_h // rows)
        return rows, cols, cell_w, cell_h

    def _smart_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        count = len(self.items)
        if count <= 0:
            return []

        prefix_ratio = [0.0]
        for item in self.items:
            prefix_ratio.append(prefix_ratio[-1] + max(0.05, item.width / max(1, item.height)))
        total_ratio = prefix_ratio[-1]
        if total_ratio <= 0:
            return []

        # 智能排版下以“铺满当前窗口”为核心目标，不再强依赖用户填写的行数。
        ideal_row_height = max(72.0, min(total_h * 0.30, 220.0))
        estimated_rows = max(1, int(round(total_h / max(1.0, ideal_row_height))))
        min_rows = 1
        max_rows = min(count, max(estimated_rows + 10, min(count, 18)))

        best_cost = float("inf")
        best_partitions: list[tuple[int, int]] = []

        for candidate_rows in range(min_rows, max_rows + 1):
            target_row_ratio = max(0.25, total_ratio / candidate_rows)
            dp: list[list[float]] = [[float("inf")] * (count + 1) for _ in range(candidate_rows + 1)]
            prev: list[list[int]] = [[-1] * (count + 1) for _ in range(candidate_rows + 1)]
            dp[0][0] = 0.0

            for row in range(1, candidate_rows + 1):
                remaining_rows = candidate_rows - row
                for end in range(row, count - remaining_rows + 1):
                    start_min = row - 1
                    start_max = end - 1
                    for start in range(start_min, start_max + 1):
                        prior = dp[row - 1][start]
                        if prior == float("inf"):
                            continue
                        row_ratio = prefix_ratio[end] - prefix_ratio[start]
                        items_in_row = end - start
                        variance_penalty = ((row_ratio - target_row_ratio) / max(0.25, target_row_ratio)) ** 2
                        single_penalty = 0.55 if items_in_row == 1 and count > 3 else 0.0
                        overwide_penalty = 0.18 if row_ratio > target_row_ratio * 1.75 else 0.0
                        underwide_penalty = 0.12 if row_ratio < target_row_ratio * 0.55 else 0.0
                        cost = prior + variance_penalty + single_penalty + overwide_penalty + underwide_penalty
                        if cost < dp[row][end]:
                            dp[row][end] = cost
                            prev[row][end] = start

            candidate_cost = dp[candidate_rows][count]
            if candidate_cost == float("inf"):
                continue

            partitions: list[tuple[int, int]] = []
            end = count
            row = candidate_rows
            while row > 0 and end > 0:
                start = prev[row][end]
                if start < 0:
                    partitions = []
                    break
                partitions.append((start, end))
                end = start
                row -= 1
            partitions.reverse()
            if not partitions:
                continue

            row_heights = []
            single_rows = 0
            for start, end in partitions:
                ratio_sum = prefix_ratio[end] - prefix_ratio[start]
                row_heights.append(total_w / max(0.05, ratio_sum))
                if end - start == 1:
                    single_rows += 1

            natural_total_h = sum(row_heights)
            blank_ratio = max(0.0, total_h - natural_total_h) / max(1.0, total_h)
            overflow_ratio = max(0.0, natural_total_h - total_h) / max(1.0, total_h)
            # overflow 会导致全行被压缩，视觉上表现为右侧成片留白，所以惩罚更高。
            fit_penalty = blank_ratio * 4.6 + overflow_ratio * 8.8
            fit_penalty += abs(natural_total_h - total_h) / max(1.0, total_h) * 1.8
            single_rows_penalty = 0.18 * single_rows
            total_cost = candidate_cost * 0.28 + fit_penalty + single_rows_penalty

            if total_cost < best_cost:
                best_cost = total_cost
                best_partitions = partitions

        partitions = best_partitions
        if not partitions:
            rows, cols, cell_w, cell_h = self._compute_grid(total_w, total_h)
            rects: list[tuple[int, int, int, int]] = []
            for idx in range(count):
                row = idx // cols
                col = idx % cols
                x0 = col * cell_w
                y0 = row * cell_h
                x1 = x0 + cell_w
                y1 = y0 + cell_h
                rects.append((x0, y0, x1, y1))
            return rects

        row_heights: list[float] = []
        for start, end in partitions:
            ratio_sum = prefix_ratio[end] - prefix_ratio[start]
            row_heights.append(total_w / max(0.05, ratio_sum))

        total_height = sum(row_heights)
        if total_height <= 0:
            return []
        # 只在高度超出容器时压缩，避免为“填满高度”而把行宽放大到超出窗口。
        scale_y = min(total_h / total_height, 1.0)
        scaled_heights = [max(1, int(h * scale_y)) for h in row_heights]

        rects: list[tuple[int, int, int, int]] = []
        y = 0
        for row_idx, (start, end) in enumerate(partitions):
            row_h = max(1, scaled_heights[row_idx])
            x = 0
            row_items = self.items[start:end]
            widths: list[int] = []
            for item in row_items:
                ratio = item.width / max(1, item.height)
                widths.append(max(1, int(row_h * ratio)))
            row_width = sum(widths)
            if row_width > total_w and row_width > 0:
                shrink = total_w / row_width
                widths = [max(1, int(w * shrink)) for w in widths]
                width_fix = total_w - sum(widths)
                widths[-1] = max(1, widths[-1] + width_fix)

            for item_idx, draw_w in enumerate(widths):
                x0 = x
                if item_idx == len(widths) - 1:
                    x1 = min(total_w, x + max(1, draw_w))
                else:
                    x1 = min(total_w, x + max(1, draw_w))
                y1 = min(total_h, y + row_h)
                rects.append((x0, y, x1, y1))
                x = x1
            y += row_h

        while len(rects) < count:
            rects.append((0, 0, total_w, total_h))
        return rects[:count]

    def _justified_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        count = len(self.items)
        if count <= 0:
            return []

        ratios = [max(0.05, item.width / max(1, item.height)) for item in self.items]
        prefix_ratio = [0.0]
        for ratio in ratios:
            prefix_ratio.append(prefix_ratio[-1] + ratio)

        min_target_h = max(90.0, min(total_h * 0.12, 180.0))
        max_target_h = max(min_target_h + 20.0, min(total_h * 0.58, 420.0))
        step = 10.0

        best_cost = float("inf")
        best_partitions: list[tuple[int, int]] = []
        best_row_heights: list[float] = []

        target_h = min_target_h
        while target_h <= max_target_h + 0.1:
            dp = [float("inf")] * (count + 1)
            prev = [-1] * (count + 1)
            row_heights = [0.0] * (count + 1)
            dp[0] = 0.0

            for end in range(1, count + 1):
                start_floor = max(0, end - 8)
                for start in range(start_floor, end):
                    if dp[start] == float("inf"):
                        continue
                    ratio_sum = prefix_ratio[end] - prefix_ratio[start]
                    if ratio_sum <= 0:
                        continue
                    height = total_w / ratio_sum
                    items_in_row = end - start
                    cost = dp[start]
                    cost += ((height - target_h) / max(1.0, target_h)) ** 2
                    if items_in_row == 1 and count > 3:
                        cost += 0.45
                    if height < 82:
                        cost += ((82 - height) / 82) * 2.6
                    if height > target_h * 1.9:
                        cost += ((height / max(1.0, target_h)) - 1.9) * 0.9
                    if cost < dp[end]:
                        dp[end] = cost
                        prev[end] = start
                        row_heights[end] = height

            if dp[count] == float("inf"):
                target_h += step
                continue

            partitions: list[tuple[int, int]] = []
            heights_out: list[float] = []
            end = count
            while end > 0:
                start = prev[end]
                if start < 0:
                    partitions = []
                    break
                partitions.append((start, end))
                heights_out.append(row_heights[end])
                end = start
            partitions.reverse()
            heights_out.reverse()
            if not partitions:
                target_h += step
                continue

            total_layout_h = sum(heights_out)
            blank_ratio = max(0.0, total_h - total_layout_h) / max(1.0, total_h)
            overflow_ratio = max(0.0, total_layout_h - total_h) / max(1.0, total_h)
            if overflow_ratio > 0.02:
                target_h += step
                continue
            min_height = min(heights_out) if heights_out else 0.0
            short_penalty = max(0.0, 110.0 - min_height) / 110.0
            total_cost = dp[count] * 0.35 + blank_ratio * 3.8 + overflow_ratio * 2.4 + short_penalty * 1.8

            if total_cost < best_cost:
                best_cost = total_cost
                best_partitions = partitions
                best_row_heights = heights_out

            target_h += step

        if not best_partitions:
            return self._smart_layout_rects(total_w, total_h)

        rects: list[tuple[int, int, int, int]] = []
        y = 0
        for row_idx, (start, end) in enumerate(best_partitions):
            row_h = max(1, int(round(best_row_heights[row_idx])))
            row_ratios = ratios[start:end]
            widths = [max(1, int(round(row_h * ratio))) for ratio in row_ratios]
            width_fix = total_w - sum(widths)
            if widths:
                widths[-1] = max(1, widths[-1] + width_fix)
            x = 0
            for col_idx, draw_w in enumerate(widths):
                x0 = x
                x1 = total_w if col_idx == len(widths) - 1 else x + max(1, draw_w)
                y1 = min(total_h, y + row_h)
                rects.append((x0, y, x1, y1))
                x = x1
            y += row_h

        return rects[:count]

    def _layout_quality_score(self, rects: list[tuple[int, int, int, int]], total_w: int, total_h: int) -> float:
        if len(rects) != len(self.items) or not self.items:
            return -1_000_000.0

        image_area = 0.0
        draw_heights: list[float] = []
        draw_areas: list[float] = []
        draw_short_sides: list[float] = []
        for item, (x0, y0, x1, y1) in zip(self.items, rects):
            cell_w = max(1, x1 - x0)
            cell_h = max(1, y1 - y0)
            scale = min(cell_w / item.width, cell_h / item.height)
            draw_w = max(1.0, item.width * scale)
            draw_h = max(1.0, item.height * scale)
            image_area += draw_w * draw_h
            draw_heights.append(draw_h)
            draw_areas.append(draw_w * draw_h)
            draw_short_sides.append(min(draw_w, draw_h))

        coverage = image_area / max(1.0, total_w * total_h)
        used_bottom = max((y1 for _, _, _, y1 in rects), default=0)
        bottom_blank = max(0.0, total_h - used_bottom) / max(1.0, total_h)
        min_h = min(draw_heights)
        max_h = max(draw_heights)
        area_ratio = max(draw_areas) / max(1.0, min(draw_areas))
        ideal_area = max(1.0, (total_w * total_h) / max(1, len(self.items)))
        readable_area = ideal_area * 0.30
        readable_short_side = max(58.0, min(124.0, math.sqrt(ideal_area) * 0.55))
        too_small = sum(1 for area in draw_areas if area < readable_area)
        severe_too_narrow = sum(1 for side in draw_short_sides if side < readable_short_side * 0.84)
        area_deficit = sum(max(0.0, (readable_area - area) / readable_area) ** 2 for area in draw_areas)
        short_deficit = sum(
            max(0.0, (readable_short_side - side) / readable_short_side) for side in draw_short_sides
        )
        too_large = sum(1 for h in draw_heights if h > total_h * 0.62)
        height_ratio = max_h / max(1.0, min_h)

        score = coverage * 3.0
        score -= bottom_blank * 1.4
        score -= too_small * 0.25
        score -= severe_too_narrow * 0.55
        score -= area_deficit * 0.35
        score -= short_deficit * 2.4
        score -= too_large * 0.35
        score -= max(0.0, height_ratio - 3.2) * 0.18
        score -= max(0.0, area_ratio - 12.0) * 0.025
        return score

    def _balanced_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        count = len(self.items)
        if count <= 0:
            return []

        ratios = [max(0.05, item.width / max(1, item.height)) for item in self.items]
        prefix_ratio = [0.0]
        for ratio in ratios:
            prefix_ratio.append(prefix_ratio[-1] + ratio)

        min_row_h = max(88.0, min(150.0, total_h * 0.12))
        preferred_min_h = max(112.0, min(180.0, total_h * 0.17))
        preferred_max_h = max(preferred_min_h + 26.0, min(330.0, total_h * 0.42))
        hard_max_h = max(preferred_max_h + 40.0, min(520.0, total_h * 0.72))
        max_items_per_row = min(count, 8)
        max_rows = min(count, max(1, int(math.ceil(total_h / max(1.0, min_row_h))) + 5))
        ideal_area = max(1.0, (total_w * total_h) / max(1, count))
        readable_area = ideal_area * 0.30
        readable_short_side = max(58.0, min(124.0, math.sqrt(ideal_area) * 0.55))

        best_cost = float("inf")
        best_partitions: list[tuple[int, int]] = []
        best_heights: list[float] = []

        for row_count in range(1, max_rows + 1):
            target_h = total_h / row_count
            dp = [[float("inf")] * (count + 1) for _ in range(row_count + 1)]
            prev = [[-1] * (count + 1) for _ in range(row_count + 1)]
            row_height_at = [[0.0] * (count + 1) for _ in range(row_count + 1)]
            dp[0][0] = 0.0

            for row in range(1, row_count + 1):
                remaining_rows = row_count - row
                end_min = row
                end_max = count - remaining_rows
                for end in range(end_min, end_max + 1):
                    start_min = max(row - 1, end - max_items_per_row)
                    start_max = end - 1
                    for start in range(start_min, start_max + 1):
                        prior = dp[row - 1][start]
                        if prior == float("inf"):
                            continue
                        ratio_sum = prefix_ratio[end] - prefix_ratio[start]
                        if ratio_sum <= 0:
                            continue
                        row_h = total_w / ratio_sum
                        if row_h < min_row_h * 0.74:
                            continue
                        items_in_row = end - start

                        cost = ((row_h - target_h) / max(1.0, target_h)) ** 2
                        if row_h < preferred_min_h:
                            cost += ((preferred_min_h - row_h) / preferred_min_h) ** 2 * 4.6
                        if row_h > preferred_max_h:
                            cost += ((row_h - preferred_max_h) / preferred_max_h) ** 2 * 2.8
                        if row_h < min_row_h:
                            cost += ((min_row_h - row_h) / min_row_h) ** 2 * 24.0
                        if row_h > hard_max_h:
                            cost += ((row_h - hard_max_h) / hard_max_h) ** 2 * 4.4
                        for ratio in ratios[start:end]:
                            draw_area = max(1.0, ratio * row_h * row_h)
                            short_side = min(row_h, row_h * ratio)
                            if draw_area < readable_area:
                                cost += ((readable_area - draw_area) / readable_area) ** 2 * 0.45
                            if short_side < readable_short_side:
                                cost += ((readable_short_side - short_side) / readable_short_side) ** 2 * 2.2
                        if items_in_row == 1 and count > 3:
                            cost += 0.95
                        if items_in_row >= 9:
                            cost += (items_in_row - 8) * 0.18

                        total_cost = prior + cost
                        if total_cost < dp[row][end]:
                            dp[row][end] = total_cost
                            prev[row][end] = start
                            row_height_at[row][end] = row_h

            if dp[row_count][count] == float("inf"):
                continue

            partitions: list[tuple[int, int]] = []
            heights: list[float] = []
            end = count
            row = row_count
            while row > 0:
                start = prev[row][end]
                if start < 0:
                    partitions = []
                    break
                partitions.append((start, end))
                heights.append(row_height_at[row][end])
                end = start
                row -= 1
            partitions.reverse()
            heights.reverse()
            if not partitions:
                continue

            natural_h = sum(heights)
            blank_ratio = max(0.0, total_h - natural_h) / max(1.0, total_h)
            overflow_ratio = max(0.0, natural_h - total_h) / max(1.0, total_h)
            if overflow_ratio > 0.015:
                continue
            avg_h = natural_h / max(1, len(heights))
            variance = sum(((h - avg_h) / max(1.0, avg_h)) ** 2 for h in heights) / max(1, len(heights))
            min_h = min(heights)
            max_h = max(heights)
            extreme_ratio = max_h / max(1.0, min_h)
            extreme_penalty = max(0.0, extreme_ratio - 2.2) ** 2 * 0.8
            total_cost = dp[row_count][count] * 0.34
            total_cost += blank_ratio * 2.7 + overflow_ratio * 9.0
            total_cost += abs(natural_h - total_h) / max(1.0, total_h) * 1.3
            total_cost += variance * 0.9 + extreme_penalty

            if total_cost < best_cost:
                best_cost = total_cost
                best_partitions = partitions
                best_heights = heights

        candidates = [
            self._smart_layout_rects(total_w, total_h),
            self._justified_layout_rects(total_w, total_h),
        ]
        slot_mosaic_candidate = self._slot_mosaic_layout_rects(total_w, total_h)
        if slot_mosaic_candidate:
            candidates.append(slot_mosaic_candidate)
        mosaic_candidate = self._orientation_mosaic_layout_rects(total_w, total_h)
        if mosaic_candidate:
            candidates.append(mosaic_candidate)
        short_side_candidate = self._short_side_balanced_layout_rects(total_w, total_h)
        if short_side_candidate:
            candidates.append(short_side_candidate)
        area_candidate = self._area_balanced_layout_rects(total_w, total_h)
        if area_candidate:
            candidates.append(area_candidate)

        if best_partitions:
            rects: list[tuple[int, int, int, int]] = []
            y = 0
            for row_idx, (start, end) in enumerate(best_partitions):
                row_h = max(1, int(round(best_heights[row_idx])))
                row_ratios = ratios[start:end]
                widths = [max(1, int(round(row_h * ratio))) for ratio in row_ratios]
                width_fix = total_w - sum(widths)
                if widths:
                    widths[-1] = max(1, widths[-1] + width_fix)
                x = 0
                for col_idx, draw_w in enumerate(widths):
                    x0 = x
                    x1 = total_w if col_idx == len(widths) - 1 else min(total_w, x + max(1, draw_w))
                    y1 = min(total_h, y + row_h)
                    rects.append((x0, y, x1, y1))
                    x = x1
                y += row_h
            candidates.append(rects[:count])

        return max(candidates, key=lambda rects: self._layout_quality_score(rects, total_w, total_h))

    def _pack_span_mosaic_rects(
        self,
        span_sets: list[tuple[list[tuple[int, int]], float]],
        total_w: int,
        total_h: int,
    ) -> list[tuple[int, int, int, int]]:
        count = len(self.items)
        if count <= 0:
            return []

        best_rects: list[tuple[int, int, int, int]] = []
        best_score = -1_000_000.0

        for spans, score_bonus in span_sets:
            if len(spans) != count or all(span == (1, 1) for span in spans):
                continue

            max_span_w = max(w for w, _ in spans)
            min_cols = max(max_span_w, 2)
            max_cols = min(18, max(min_cols, int(math.ceil(math.sqrt(count * 2.4))) + 7))

            for cols in range(min_cols, max_cols + 1):
                grid: list[list[bool]] = []
                placements: list[tuple[int, int, int, int]] = []

                def _ensure_rows(row_count: int) -> None:
                    while len(grid) < row_count:
                        grid.append([False] * cols)

                def _can_place(row: int, col: int, span_w: int, span_h: int) -> bool:
                    if col + span_w > cols:
                        return False
                    _ensure_rows(row + span_h)
                    for rr in range(row, row + span_h):
                        for cc in range(col, col + span_w):
                            if grid[rr][cc]:
                                return False
                    return True

                def _occupy(row: int, col: int, span_w: int, span_h: int) -> None:
                    _ensure_rows(row + span_h)
                    for rr in range(row, row + span_h):
                        for cc in range(col, col + span_w):
                            grid[rr][cc] = True

                for span_w, span_h in spans:
                    if span_w > cols:
                        placements = []
                        break
                    placed = False
                    row = 0
                    while not placed and row < count * 4 + 8:
                        for col in range(0, cols - span_w + 1):
                            if _can_place(row, col, span_w, span_h):
                                _occupy(row, col, span_w, span_h)
                                placements.append((col, row, span_w, span_h))
                                placed = True
                                break
                        if not placed:
                            row += 1
                    if not placed:
                        placements = []
                        break

                if len(placements) != count:
                    continue

                rows_used = max(row + span_h for _, row, _, span_h in placements)
                if rows_used <= 0:
                    continue
                unit = min(total_w / max(1, cols), total_h / max(1, rows_used))
                if unit < 24:
                    continue

                layout_w = unit * cols
                x_offset = max(0.0, (total_w - layout_w) / 2.0)
                square_rects: list[tuple[int, int, int, int]] = []
                for col, row, span_w, span_h in placements:
                    x0 = int(round(x_offset + col * unit))
                    y0 = int(round(row * unit))
                    x1 = int(round(x_offset + (col + span_w) * unit))
                    y1 = int(round((row + span_h) * unit))
                    square_rects.append((max(0, x0), max(0, y0), min(total_w, x1), min(total_h, y1)))

                fill_rects: list[tuple[int, int, int, int]] = []
                unit_w = total_w / max(1, cols)
                unit_h = total_h / max(1, rows_used)
                for col, row, span_w, span_h in placements:
                    x0 = int(round(col * unit_w))
                    y0 = int(round(row * unit_h))
                    x1 = int(round((col + span_w) * unit_w))
                    y1 = int(round((row + span_h) * unit_h))
                    fill_rects.append((max(0, x0), max(0, y0), min(total_w, x1), min(total_h, y1)))

                for rects, mode_bonus in ((square_rects, 0.0), (fill_rects, 0.12)):
                    if len(rects) != count:
                        continue
                    score = self._layout_quality_score(rects, total_w, total_h) + score_bonus + mode_bonus
                    if score > best_score:
                        best_score = score
                        best_rects = rects

        return best_rects

    def _slot_mosaic_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        if not self.items:
            return []

        def _adaptive_span_for_ratio(ratio: float) -> tuple[int, int]:
            if 0.92 <= ratio <= 1.08:
                return (1, 1)
            candidates = [(1, 1), (2, 1), (3, 1), (3, 2), (4, 3), (1, 2), (1, 3), (2, 3), (3, 4)]
            best_span = (1, 1)
            best_cost = float("inf")
            wants_landscape = ratio > 1.0
            for span_w, span_h in candidates:
                span_ratio = span_w / max(1, span_h)
                area = span_w * span_h
                cost = abs(math.log(max(0.05, ratio) / max(0.05, span_ratio)))
                cost += max(0, area - 2) * 0.035
                if wants_landscape and span_w <= span_h:
                    cost += 0.42
                if not wants_landscape and span_h <= span_w:
                    cost += 0.42
                if (wants_landscape and (span_w, span_h) == (2, 1)) or (
                    not wants_landscape and (span_w, span_h) == (1, 2)
                ):
                    cost -= 0.06
                if cost < best_cost:
                    best_cost = cost
                    best_span = (span_w, span_h)
            return best_span

        adaptive_spans: list[tuple[int, int]] = []
        review_spans: list[tuple[int, int]] = []
        gentle_spans: list[tuple[int, int]] = []
        for item in self.items:
            ratio = item.width / max(1, item.height)
            adaptive_spans.append(_adaptive_span_for_ratio(ratio))
            if ratio >= 2.35:
                review_spans.append((3, 1))
            elif ratio >= 1.08:
                review_spans.append((2, 1))
            elif ratio <= 0.43:
                review_spans.append((1, 3))
            elif ratio <= 0.92:
                review_spans.append((1, 2))
            else:
                review_spans.append((1, 1))

            if ratio >= 1.38:
                gentle_spans.append((2, 1))
            elif ratio <= 0.72:
                gentle_spans.append((1, 2))
            else:
                gentle_spans.append((1, 1))

        return self._pack_span_mosaic_rects(
            [
                (review_spans, 0.55),
                (adaptive_spans, 0.35),
                (gentle_spans, 0.25),
            ],
            total_w,
            total_h,
        )

    def _orientation_mosaic_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        count = len(self.items)
        if count <= 0:
            return []

        ratios = [max(0.05, item.width / max(1, item.height)) for item in self.items]
        units: list[dict] = []
        made_pair = False
        idx = 0
        while idx < count:
            ratio = ratios[idx]
            is_landscape = ratio >= 1.25
            is_portrait = ratio <= 0.80
            if idx + 1 < count:
                next_ratio = ratios[idx + 1]
                next_landscape = next_ratio >= 1.25
                next_portrait = next_ratio <= 0.80
                if is_landscape and next_portrait:
                    portrait_w = min(0.95, max(0.34, next_ratio))
                    land_h = portrait_w
                    land_w = max(0.35, ratio * land_h)
                    unit_w = land_w + portrait_w
                    units.append(
                        {
                            "ratio": unit_w,
                            "parts": [
                                (idx, 0.0, 0.0, land_w, land_h),
                                (idx + 1, land_w, 0.0, unit_w, 1.0),
                            ],
                        }
                    )
                    made_pair = True
                    idx += 2
                    continue
                if is_portrait and next_landscape:
                    portrait_w = min(0.95, max(0.34, ratio))
                    land_h = portrait_w
                    land_w = max(0.35, next_ratio * land_h)
                    unit_w = portrait_w + land_w
                    units.append(
                        {
                            "ratio": unit_w,
                            "parts": [
                                (idx, 0.0, 0.0, portrait_w, 1.0),
                                (idx + 1, portrait_w, 0.0, unit_w, land_h),
                            ],
                        }
                    )
                    made_pair = True
                    idx += 2
                    continue

            units.append({"ratio": ratio, "parts": [(idx, 0.0, 0.0, ratio, 1.0)]})
            idx += 1

        if not made_pair:
            return []

        unit_count = len(units)
        prefix_ratio = [0.0]
        for unit in units:
            prefix_ratio.append(prefix_ratio[-1] + float(unit["ratio"]))

        min_target_h = max(96.0, min(total_h * 0.13, 190.0))
        max_target_h = max(min_target_h + 24.0, min(total_h * 0.62, 460.0))
        max_units_per_row = min(unit_count, 8)
        best_cost = float("inf")
        best_partitions: list[tuple[int, int]] = []
        best_heights: list[float] = []

        target_h = min_target_h
        while target_h <= max_target_h + 0.1:
            dp = [float("inf")] * (unit_count + 1)
            prev = [-1] * (unit_count + 1)
            row_h_at = [0.0] * (unit_count + 1)
            dp[0] = 0.0

            for end in range(1, unit_count + 1):
                for start in range(max(0, end - max_units_per_row), end):
                    if dp[start] == float("inf"):
                        continue
                    ratio_sum = prefix_ratio[end] - prefix_ratio[start]
                    if ratio_sum <= 0:
                        continue
                    row_h = total_w / ratio_sum
                    units_in_row = end - start
                    cost = dp[start]
                    cost += ((row_h - target_h) / max(1.0, target_h)) ** 2
                    if row_h < 90:
                        cost += ((90 - row_h) / 90) ** 2 * 5.0
                    if row_h > target_h * 2.25:
                        cost += ((row_h / max(1.0, target_h)) - 2.25) ** 2 * 0.8
                    if units_in_row == 1 and unit_count > 2:
                        cost += 0.35
                    if cost < dp[end]:
                        dp[end] = cost
                        prev[end] = start
                        row_h_at[end] = row_h

            if dp[unit_count] == float("inf"):
                target_h += 10.0
                continue

            partitions: list[tuple[int, int]] = []
            heights: list[float] = []
            end = unit_count
            while end > 0:
                start = prev[end]
                if start < 0:
                    partitions = []
                    break
                partitions.append((start, end))
                heights.append(row_h_at[end])
                end = start
            partitions.reverse()
            heights.reverse()
            if not partitions:
                target_h += 10.0
                continue

            natural_h = sum(heights)
            blank_ratio = max(0.0, total_h - natural_h) / max(1.0, total_h)
            overflow_ratio = max(0.0, natural_h - total_h) / max(1.0, total_h)
            if overflow_ratio > 0.03:
                target_h += 10.0
                continue
            avg_h = natural_h / max(1, len(heights))
            variance = sum(((h - avg_h) / max(1.0, avg_h)) ** 2 for h in heights) / max(1, len(heights))
            total_cost = dp[unit_count] * 0.35 + blank_ratio * 2.4 + overflow_ratio * 7.0
            total_cost += abs(natural_h - total_h) / max(1.0, total_h) * 1.1
            total_cost += variance * 0.8
            if total_cost < best_cost:
                best_cost = total_cost
                best_partitions = partitions
                best_heights = heights

            target_h += 10.0

        if not best_partitions:
            return []

        rects_by_idx: list[Optional[tuple[int, int, int, int]]] = [None] * count
        y = 0
        for row_idx, (start, end) in enumerate(best_partitions):
            row_h = max(1, int(round(best_heights[row_idx])))
            row_ratios = [float(unit["ratio"]) for unit in units[start:end]]
            unit_widths = [max(1, int(round(row_h * ratio))) for ratio in row_ratios]
            width_fix = total_w - sum(unit_widths)
            if unit_widths:
                unit_widths[-1] = max(1, unit_widths[-1] + width_fix)

            x = 0
            for unit_offset, unit_w in enumerate(unit_widths):
                unit = units[start + unit_offset]
                norm_w = max(0.01, float(unit["ratio"]))
                scale_x = unit_w / norm_w
                x_limit = total_w if unit_offset == len(unit_widths) - 1 else min(total_w, x + unit_w)
                for item_idx, lx0, ly0, lx1, ly1 in unit["parts"]:
                    x0 = min(total_w, x + int(round(lx0 * scale_x)))
                    y0 = min(total_h, y + int(round(ly0 * row_h)))
                    x1 = min(total_w, x + int(round(lx1 * scale_x)))
                    y1 = min(total_h, y + int(round(ly1 * row_h)))
                    if x1 <= x0:
                        x1 = min(total_w, x0 + 1)
                    if y1 <= y0:
                        y1 = min(total_h, y0 + 1)
                    rects_by_idx[item_idx] = (x0, y0, x1, y1)
                x = x_limit
            y += row_h

        if any(rect is None for rect in rects_by_idx):
            return []
        return [rect for rect in rects_by_idx if rect is not None]

    def _short_side_balanced_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        count = len(self.items)
        if count <= 0:
            return []

        ratios = [max(0.05, item.width / max(1, item.height)) for item in self.items]
        viewport_area = max(1.0, total_w * total_h)
        ideal_area = viewport_area / max(1, count)
        readable_short = max(58.0, min(132.0, math.sqrt(ideal_area) * 0.52))
        short_values = sorted(
            {
                max(42.0, readable_short * factor)
                for factor in (0.78, 0.88, 0.98, 1.08, 1.18, 1.30, 1.44)
            },
            reverse=True,
        )
        max_items_per_row = min(count, 10)
        best_rects: list[tuple[int, int, int, int]] = []
        best_score = -1_000_000.0

        for short_side in short_values:
            base_widths: list[float] = []
            base_heights: list[float] = []
            for ratio in ratios:
                if ratio >= 1.0:
                    base_widths.append(short_side * ratio)
                    base_heights.append(short_side)
                else:
                    base_widths.append(short_side)
                    base_heights.append(short_side / ratio)

            dp = [float("inf")] * (count + 1)
            prev = [-1] * (count + 1)
            row_scale_at = [1.0] * (count + 1)
            dp[0] = 0.0

            for end in range(1, count + 1):
                for start in range(max(0, end - max_items_per_row), end):
                    if dp[start] == float("inf"):
                        continue
                    row_w = sum(base_widths[start:end])
                    if row_w <= 0:
                        continue
                    row_scale = min(1.0, total_w / row_w)
                    # 缩得太狠会重新制造“竖图很窄”的问题，因此宁可多分一行。
                    if row_scale < 0.90:
                        continue
                    scaled_w = row_w * row_scale
                    row_h = max(base_heights[start:end]) * row_scale
                    items_in_row = end - start
                    width_blank = max(0.0, total_w - scaled_w) / max(1.0, total_w)
                    shrink_penalty = max(0.0, 1.0 - row_scale)

                    row_cost = width_blank * width_blank * 2.4 + shrink_penalty * shrink_penalty * 8.0
                    if items_in_row == 1 and count > 3:
                        row_cost += 0.8
                    if items_in_row >= 9:
                        row_cost += (items_in_row - 8) * 0.18
                    if row_h < readable_short:
                        row_cost += ((readable_short - row_h) / readable_short) ** 2 * 1.2

                    total_cost = dp[start] + row_cost
                    if total_cost < dp[end]:
                        dp[end] = total_cost
                        prev[end] = start
                        row_scale_at[end] = row_scale

            if dp[count] == float("inf"):
                continue

            rows: list[tuple[int, int, float, list[float]]] = []
            end = count
            while end > 0:
                start = prev[end]
                if start < 0:
                    rows = []
                    break
                scale = row_scale_at[end]
                widths = [max(1.0, w * scale) for w in base_widths[start:end]]
                row_h = max(max(base_heights[start:end]) * scale, 1.0)
                rows.append((start, end, row_h, widths))
                end = start
            rows.reverse()
            if not rows:
                continue

            natural_h = sum(row[2] for row in rows)
            if natural_h <= 0:
                continue
            y_scale = min(1.0, total_h / natural_h)
            if y_scale < 0.86:
                continue

            rects: list[tuple[int, int, int, int]] = []
            y = 0
            for _start, _end, row_h_float, widths_float in rows:
                row_h = max(1, int(round(row_h_float * y_scale)))
                draw_widths = [max(1, int(round(w * y_scale))) for w in widths_float]
                used_w = sum(draw_widths)
                gap = max(0, total_w - used_w) / max(1, len(draw_widths))
                x_float = 0.0
                for idx, draw_w in enumerate(draw_widths):
                    cell_w = draw_w + int(round(gap))
                    x0 = int(round(x_float))
                    x1 = total_w if idx == len(draw_widths) - 1 else min(total_w, x0 + max(1, cell_w))
                    y1 = min(total_h, y + row_h)
                    rects.append((x0, y, x1, y1))
                    x_float = x1
                y += row_h

            rects = rects[:count]
            if len(rects) != count:
                continue
            score = self._layout_quality_score(rects, total_w, total_h)
            if score > best_score:
                best_score = score
                best_rects = rects

        return best_rects

    def _area_balanced_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        count = len(self.items)
        if count <= 0:
            return []

        ratios = [max(0.05, item.width / max(1, item.height)) for item in self.items]
        viewport_area = max(1.0, total_w * total_h)
        max_items_per_row = min(count, 12)
        best_cost = float("inf")
        best_rows: list[tuple[int, int, float, list[float], list[float]]] = []

        for area_factor in (0.42, 0.48, 0.54, 0.60, 0.66, 0.72):
            target_area = viewport_area / max(1, count) * area_factor
            base_widths = [math.sqrt(target_area * ratio) for ratio in ratios]
            base_heights = [math.sqrt(target_area / ratio) for ratio in ratios]
            dp = [float("inf")] * (count + 1)
            prev = [-1] * (count + 1)
            row_scale_at = [1.0] * (count + 1)
            dp[0] = 0.0

            for end in range(1, count + 1):
                for start in range(max(0, end - max_items_per_row), end):
                    if dp[start] == float("inf"):
                        continue
                    row_w = sum(base_widths[start:end])
                    if row_w <= 0:
                        continue
                    row_scale = min(total_w / row_w, 1.32)
                    scaled_w = row_w * row_scale
                    row_h = max(base_heights[start:end]) * row_scale
                    items_in_row = end - start
                    width_blank = max(0.0, total_w - scaled_w) / max(1.0, total_w)
                    width_overflow = max(0.0, scaled_w - total_w) / max(1.0, total_w)
                    row_cost = width_blank * 0.8 + width_overflow * 4.0
                    if items_in_row == 1 and count > 3:
                        row_cost += 0.75
                    if row_h < 70:
                        row_cost += ((70 - row_h) / 70) ** 2 * 3.0
                    total_cost = dp[start] + row_cost
                    if total_cost < dp[end]:
                        dp[end] = total_cost
                        prev[end] = start
                        row_scale_at[end] = row_scale

            if dp[count] == float("inf"):
                continue

            rows: list[tuple[int, int, float, list[float], list[float]]] = []
            end = count
            while end > 0:
                start = prev[end]
                if start < 0:
                    rows = []
                    break
                scale = row_scale_at[end]
                widths = [w * scale for w in base_widths[start:end]]
                heights = [h * scale for h in base_heights[start:end]]
                rows.append((start, end, max(heights), widths, heights))
                end = start
            rows.reverse()
            if not rows:
                continue

            natural_h = sum(row[2] for row in rows)
            blank_ratio = max(0.0, total_h - natural_h) / max(1.0, total_h)
            overflow_ratio = max(0.0, natural_h - total_h) / max(1.0, total_h)
            if overflow_ratio > 0.12:
                continue
            fit_cost = dp[count] + blank_ratio * 1.2 + overflow_ratio * 5.2
            if fit_cost < best_cost:
                best_cost = fit_cost
                best_rows = rows

        if not best_rows:
            return []

        total_rows_h = sum(row[2] for row in best_rows)
        y_scale = min(1.0, total_h / max(1.0, total_rows_h))
        rects: list[tuple[int, int, int, int]] = []
        y = 0
        for _start, _end, row_h_float, widths_float, heights_float in best_rows:
            row_h = max(1, int(round(row_h_float * y_scale)))
            draw_widths = [max(1, int(round(w * y_scale))) for w in widths_float]
            used_w = sum(draw_widths)
            gap = max(0, total_w - used_w) / max(1, len(draw_widths))
            x_float = 0.0
            for idx, draw_w in enumerate(draw_widths):
                cell_w = draw_w + int(round(gap))
                x0 = int(round(x_float))
                x1 = total_w if idx == len(draw_widths) - 1 else min(total_w, x0 + max(1, cell_w))
                y1 = min(total_h, y + row_h)
                rects.append((x0, y, x1, y1))
                x_float = x1
            y += row_h

        return rects[:count]

    def _resize_frame(self, src: Image.Image, target_w: int, target_h: int) -> Image.Image:
        target_w = max(1, target_w)
        target_h = max(1, target_h)
        profile = self.app.current_profile()
        ratio = max(src.width / target_w, src.height / target_h)
        base = src
        if profile["multi_step"] and ratio > 1.8:
            # 多段缩小可减少锯齿/振铃。
            w, h = src.size
            while w // 2 >= target_w and h // 2 >= target_h:
                w = max(target_w, w // 2)
                h = max(target_h, h // 2)
                base = base.resize((w, h), Image.Resampling.BOX)

        if profile["pre_blur"] > 0 and ratio > 2.0:
            base = base.filter(ImageFilter.GaussianBlur(profile["pre_blur"]))

        resample = profile["resample"]
        if profile["two_pass"] and ratio > 1.2:
            mid_w = max(target_w, int(target_w * 1.35))
            mid_h = max(target_h, int(target_h * 1.35))
            try:
                base = base.resize((mid_w, mid_h), resample, reducing_gap=2.0)
            except TypeError:
                base = base.resize((mid_w, mid_h), resample)
        try:
            out = base.resize((target_w, target_h), resample, reducing_gap=3.0)
        except TypeError:
            out = base.resize((target_w, target_h), resample)

        if profile["sharpen"] and ratio > 1.35:
            out = out.filter(ImageFilter.UnsharpMask(radius=0.9, percent=90, threshold=3))
        return out

    def _photo_for(self, item: ImageItem, frame_idx: int, src: Image.Image, w: int, h: int) -> ImageTk.PhotoImage:
        profile_name = self.app.perf_mode_var.get()
        key = (str(item.path), frame_idx, w, h, hash(profile_name))
        cached = self._photo_cache.get(key)
        if cached is not None:
            self.cache_hits += 1
            self._photo_cache.move_to_end(key)
            return cached

        self.cache_misses += 1
        resized = self._resize_frame(src, w, h)
        tk_img = ImageTk.PhotoImage(resized)
        self._photo_cache[key] = tk_img
        self._trim_photo_cache()
        return tk_img

    def _trim_photo_cache(self) -> None:
        limit = self.app.current_cache_limit()
        while len(self._photo_cache) > limit:
            self._photo_cache.popitem(last=False)

    def gif_item_count(self) -> int:
        return sum(1 for item in self.items if item.is_gif and item.gif_frames)

    def _render_slice_budget_ms(self) -> float:
        gif_count = self.gif_item_count()
        if gif_count >= 45:
            return 4.0
        if gif_count >= 25:
            return 6.0
        return 9.0

    def _render_slice_batch(self, default: int) -> int:
        gif_count = self.gif_item_count()
        if gif_count >= 45:
            return 1
        if gif_count >= 25:
            return min(default, 2)
        if gif_count >= 12:
            return min(default, 4)
        return default

    def _render_slice_delay_ms(self) -> int:
        gif_count = self.gif_item_count()
        if gif_count >= 45:
            return 10
        if gif_count >= 25:
            return 6
        if gif_count >= 12:
            return 3
        return 1

    def _index_from_xy(self, x: int, y: int) -> Optional[int]:
        if not self.items:
            return None
        x = max(0, x)
        y = max(0, y)
        for idx, (x0, y0, x1, y1) in enumerate(self._cell_lookup_rects):
            if x0 <= x < x1 and y0 <= y < y1:
                return idx
        if self._cell_lookup_rects:
            nearest_idx = min(
                range(len(self._cell_lookup_rects)),
                key=lambda i: abs((self._cell_lookup_rects[i][0] + self._cell_lookup_rects[i][2]) // 2 - x)
                + abs((self._cell_lookup_rects[i][1] + self._cell_lookup_rects[i][3]) // 2 - y),
            )
            return nearest_idx
        return len(self.items) - 1

    def _on_press(self, evt: tk.Event) -> None:
        self.app.set_active_group(self.group_id)
        self.app.pause_heavy_work(0.8)
        self.canvas.focus_set()
        idx = self._index_from_xy(evt.x, evt.y)
        self._press_xy = (evt.x, evt.y)
        self._drag_moved = False
        self._press_on_selected_idx = idx if idx is not None and idx in self._selected_indexes else None
        ctrl_down = bool(evt.state & 0x0004)
        shift_down = bool(evt.state & 0x0001)

        if shift_down:
            self._drag_active = False
            self._select_box_active = True
            self._select_box_start = (evt.x, evt.y)
            self._select_box_current = (evt.x, evt.y)
            if not ctrl_down:
                self._selected_indexes.clear()
            self._redraw_overlays()
            return

        self._selected_idx = idx
        if idx is None:
            self._drag_active = False
            if not ctrl_down:
                self._selected_indexes.clear()
            self._redraw_overlays()
            return

        if ctrl_down:
            if idx in self._selected_indexes:
                self._selected_indexes.remove(idx)
                if self._selected_idx == idx:
                    self._selected_idx = next(iter(self._selected_indexes), None)
            else:
                self._selected_indexes.add(idx)
                self._selected_idx = idx
            self._drag_active = False
            self._redraw_overlays()
            return

        self._selected_indexes = {idx}
        self._drag_active = True
        self._drag_source_idx = idx
        self._drag_target_idx = idx

    def _on_drag(self, evt: tk.Event) -> None:
        self.app.pause_heavy_work(0.45)
        if self._press_xy is not None:
            dx = abs(evt.x - self._press_xy[0])
            dy = abs(evt.y - self._press_xy[1])
            if dx >= 4 or dy >= 4:
                self._drag_moved = True
        if self._select_box_active:
            self._select_box_current = (evt.x, evt.y)
            self._redraw_overlays()
            return
        if not self._drag_active:
            return
        idx = self._index_from_xy(evt.x, evt.y)
        if idx is None:
            return
        if idx != self._drag_target_idx:
            self._drag_target_idx = idx
            self._redraw_overlays()

    def _on_release(self, _evt: tk.Event) -> None:
        self.app.pause_heavy_work(0.8)
        if self._select_box_active:
            self._select_box_active = False
            start = self._select_box_start
            end = self._select_box_current
            self._select_box_start = None
            self._select_box_current = None
            if start and end:
                x0, y0 = start
                x1, y1 = end
                left, right = sorted((x0, x1))
                top, bottom = sorted((y0, y1))
                selected = []
                for idx, (rx0, ry0, rx1, ry1) in enumerate(self._cell_lookup_rects):
                    if rx1 >= left and rx0 <= right and ry1 >= top and ry0 <= bottom:
                        selected.append(idx)
                self._selected_indexes.update(selected)
                self._selected_idx = min(self._selected_indexes) if self._selected_indexes else None
            self._redraw_overlays()
            return

        if not self._drag_active:
            self._press_xy = None
            self._press_on_selected_idx = None
            return

        src = self._drag_source_idx
        dst = self._drag_target_idx
        self._drag_active = False
        self._drag_source_idx = None
        self._drag_target_idx = None

        if not self._drag_moved and src is not None and src == dst and self._press_on_selected_idx == src:
            self._selected_indexes.discard(src)
            if self._selected_idx == src:
                self._selected_idx = next(iter(self._selected_indexes), None)
            self._press_xy = None
            self._press_on_selected_idx = None
            self._drag_moved = False
            self._redraw_overlays()
            return

        self._press_xy = None
        self._press_on_selected_idx = None
        self._drag_moved = False

        if src is None or dst is None or src == dst:
            self._redraw_overlays()
            return

        moving = self.items.pop(src)
        # 按目标格插入，前往后拖动更符合视觉预期。
        self.items.insert(dst, moving)
        self._selected_idx = dst
        self._selected_indexes = {dst}
        self.app.mark_dirty()
        self.render(force=True)

    def _on_right_click(self, evt: tk.Event) -> None:
        self.app.set_active_group(self.group_id)
        self.app.pause_heavy_work(1.2)
        idx = self._index_from_xy(evt.x, evt.y)
        self._context_idx = idx
        if idx is not None:
            self._selected_idx = idx
            if idx not in self._selected_indexes:
                self._selected_indexes = {idx}
        remove_count = len(self._selected_indexes) if self._selected_indexes else (1 if idx is not None else 0)
        self._redraw_overlays()
        remove_label = self.app.tr("menu.remove_selected_images", "从窗口组移除所选图片") if remove_count > 1 else self.app.tr("menu.remove_image", "从窗口组移除图片")
        self._menu.entryconfigure(0, label=remove_label, state=("normal" if remove_count > 0 else "disabled"))
        has_gif = any(item.is_gif and item.gif_frames for item in self.items)
        self._menu.entryconfigure(1, state=("normal" if has_gif else "disabled"))
        has_template = self.template_path is not None and self.template_path.exists()
        self._menu.entryconfigure(4, state=("normal" if has_template else "disabled"))
        self._menu.entryconfigure(5, state=("normal" if has_template else "disabled"))
        try:
            self._menu.tk_popup(evt.x_root, evt.y_root)
        finally:
            self._menu.grab_release()

    def _remove_context_item(self) -> None:
        if self._selected_indexes:
            self.remove_items_at(list(self._selected_indexes))
            return
        if self._context_idx is None:
            return
        self.remove_item_at(self._context_idx)

    def _on_delete_key(self, _evt: tk.Event) -> None:
        if self._selected_indexes:
            self.remove_items_at(list(self._selected_indexes))
            return
        if self._selected_idx is None:
            return
        self.remove_item_at(self._selected_idx)

    def _clear_overlay_items(self) -> None:
        self.canvas.delete("selection_overlay")
        self.canvas.delete("drag_overlay")
        self.canvas.delete("select_overlay")

    def _redraw_overlays(self) -> None:
        self._clear_overlay_items()
        for idx, (x0, y0, x1, y1) in enumerate(self._layout_rects):
            if idx in self._selected_indexes:
                self.canvas.create_rectangle(
                    x0 + 2,
                    y0 + 2,
                    x1 - 2,
                    y1 - 2,
                    outline="#f7c948",
                    width=3,
                    tags=("selection_overlay",),
                )
            elif self._selected_idx == idx:
                self.canvas.create_rectangle(
                    x0 + 2,
                    y0 + 2,
                    x1 - 2,
                    y1 - 2,
                    outline="#4cc9f0",
                    width=2,
                    tags=("selection_overlay",),
                )

        if self._drag_active and self._drag_target_idx is not None:
            tidx = self._drag_target_idx
            if 0 <= tidx < len(self._layout_rects):
                x0, y0, x1, y1 = self._layout_rects[tidx]
                self.canvas.create_rectangle(
                    x0 + 2, y0 + 2, x1 - 2, y1 - 2, outline="#4cc9f0", width=3, tags=("drag_overlay",)
                )
        if self._select_box_active and self._select_box_start and self._select_box_current:
            x0, y0 = self._select_box_start
            x1, y1 = self._select_box_current
            self.canvas.create_rectangle(
                x0,
                y0,
                x1,
                y1,
                outline="#f7c948",
                width=2,
                dash=(6, 4),
                tags=("select_overlay",),
            )

    def _render_static_batch(self, rects: list[tuple[int, int, int, int]], token: int, start: int, batch: int = 8) -> None:
        if token != self._static_render_token:
            return
        slice_start = time.perf_counter()
        slice_budget_ms = self._render_slice_budget_ms()
        effective_batch = max(1, self._render_slice_batch(batch))
        end = start
        for idx in range(start, len(self.items)):
            if idx >= len(rects):
                break
            item = self.items[idx]
            x0, y0, x1, y1 = rects[idx]
            cell_w = max(1, x1 - x0)
            cell_h = max(1, y1 - y0)

            frame_idx = -1
            frame = item.pil_image
            if item.is_gif and item.gif_frames:
                frame_idx = item.gif_index
                frame = item.gif_frames[item.gif_index]

            scale = min(cell_w / item.width, cell_h / item.height)
            draw_w = max(1, int(item.width * scale))
            draw_h = max(1, int(item.height * scale))
            self._slot_draw_sizes[idx] = (draw_w, draw_h)

            tk_img = self._photo_for(item, frame_idx, frame, draw_w, draw_h)
            self._image_refs[idx] = tk_img

            cx = x0 + cell_w // 2
            cy = y0 + cell_h // 2
            image_id = self.canvas.create_image(cx, cy, image=tk_img)
            self._slot_image_ids[idx] = image_id
            end = idx + 1

            elapsed_ms = (time.perf_counter() - slice_start) * 1000
            if end - start >= effective_batch or elapsed_ms >= slice_budget_ms:
                break

        self._redraw_overlays()
        if end < len(self.items):
            delay_ms = self._render_slice_delay_ms()
            self._render_batch_after_id = self.top.after(delay_ms, lambda: self._render_static_batch(rects, token, end, batch))
        else:
            self._render_batch_after_id = None

    def _compute_layout_rects(self, total_w: int, total_h: int) -> list[tuple[int, int, int, int]]:
        if self.smart_layout:
            if self.layout_algorithm == "balanced":
                rects = self._balanced_layout_rects(total_w, total_h)
            elif self.layout_algorithm == "justified":
                rects = self._justified_layout_rects(total_w, total_h)
            else:
                rects = self._smart_layout_rects(total_w, total_h)
            self._layout_rows = max(1, self.rows)
            self._layout_cols = max(1, math.ceil(len(self.items) / max(1, self.rows)))
            self._cell_w = max(1, total_w // max(1, self._layout_cols))
            self._cell_h = max(1, total_h // max(1, self._layout_rows))
            return rects

        rows, cols, cell_w, cell_h = self._compute_grid(total_w, total_h)
        self._layout_rows = rows
        self._layout_cols = cols
        self._cell_w = cell_w
        self._cell_h = cell_h
        rects = []
        for idx in range(len(self.items)):
            row = idx // cols
            col = idx % cols
            x0 = col * cell_w
            y0 = row * cell_h
            x1 = x0 + cell_w
            y1 = y0 + cell_h
            rects.append((x0, y0, x1, y1))
        return rects

    def _draw_static_layout_in_place(self, total_w: int, total_h: int) -> None:
        if self._render_batch_after_id:
            try:
                self.top.after_cancel(self._render_batch_after_id)
            except Exception:
                pass
            self._render_batch_after_id = None
        self._static_render_token += 1
        token = self._static_render_token

        rects = self._compute_layout_rects(total_w, total_h)
        if len(rects) != len(self.items):
            self._draw_static_layout(total_w, total_h)
            return

        self._layout_rects = list(rects)
        self._cell_lookup_rects = list(rects)
        self._slot_draw_sizes = [(0, 0)] * len(self.items)
        self._image_refs = [None] * len(self.items)

        for idx, (x0, y0, x1, y1) in enumerate(rects):
            frame_id = self._slot_frame_ids[idx] if idx < len(self._slot_frame_ids) else 0
            if frame_id:
                self.canvas.coords(frame_id, x0, y0, x1, y1)

        self._redraw_overlays()
        self._render_static_batch(rects, token, 0, batch=12)

    def _draw_static_layout(self, total_w: int, total_h: int) -> None:
        if self._render_batch_after_id:
            try:
                self.top.after_cancel(self._render_batch_after_id)
            except Exception:
                pass
            self._render_batch_after_id = None
        self._static_render_token += 1
        token = self._static_render_token

        self.canvas.delete("all")
        self._image_refs.clear()
        self._layout_rects.clear()
        self._cell_lookup_rects.clear()
        self._slot_image_ids.clear()
        self._slot_frame_ids.clear()
        self._slot_draw_sizes.clear()

        if not self.items:
            self.canvas.create_text(
                total_w // 2,
                total_h // 2,
                fill="#aaaaaa",
                text=self.app.tr("group.empty_hint", "该窗口组还没有图片\n可直接拖拽到此窗口"),
                font=("Microsoft YaHei UI", 14),
                justify=tk.CENTER,
            )
            return

        rects = self._compute_layout_rects(total_w, total_h)

        self._image_refs = [None] * len(self.items)
        self._slot_image_ids = [0] * len(self.items)
        self._slot_frame_ids = [0] * len(self.items)
        self._slot_draw_sizes = [(0, 0)] * len(self.items)

        for idx, (x0, y0, x1, y1) in enumerate(rects):
            self._layout_rects.append((x0, y0, x1, y1))
            self._cell_lookup_rects.append((x0, y0, x1, y1))
            self._slot_frame_ids[idx] = self.canvas.create_rectangle(x0, y0, x1, y1, outline="#1f1f1f")

        self._redraw_overlays()
        self._render_static_batch(rects, token, 0, batch=10)

    def _refresh_gif_slot(self, idx: int) -> bool:
        if len(self._slot_image_ids) != len(self.items):
            return False
        if idx < 0 or idx >= len(self.items):
            return False
        item = self.items[idx]
        if not item.is_gif or not item.gif_frames:
            return False

        draw_w, draw_h = self._slot_draw_sizes[idx]
        image_id = self._slot_image_ids[idx]
        if draw_w <= 0 or draw_h <= 0 or not image_id:
            return False
        frame_idx = item.gif_index
        frame = item.gif_frames[frame_idx]
        tk_img = self._photo_for(item, frame_idx, frame, draw_w, draw_h)
        self._image_refs[idx] = tk_img
        self.canvas.itemconfigure(image_id, image=tk_img)
        return True

    def _refresh_gif_slots(self, changed_indexes: list[int]) -> None:
        if not changed_indexes:
            return

        for idx in changed_indexes:
            self._refresh_gif_slot(idx)

    def render(self, force: bool = False) -> None:
        total_w = self.canvas.winfo_width()
        total_h = self.canvas.winfo_height()
        if total_w <= 1 or total_h <= 1:
            return
        if time.time() < self._resizing_until and not force:
            return

        size_changed = (total_w, total_h) != self._last_layout_size
        if not force and not size_changed:
            return

        same_count = len(self._slot_image_ids) == len(self.items) == len(self._slot_frame_ids) and bool(self.items)
        self._last_layout_size = (total_w, total_h)
        if force and not size_changed and same_count:
            self._draw_static_layout_in_place(total_w, total_h)
            return
        self._draw_static_layout(total_w, total_h)

    def _advance_gif_to_now(self, item: ImageItem, now: float) -> bool:
        if item.next_due == 0.0:
            item.next_due = now + item.gif_durations[item.gif_index] / 1000
            return False
        if now < item.next_due:
            return False

        changed = False
        step_guard = 0
        while now >= item.next_due and step_guard < 240:
            item.gif_index = (item.gif_index + 1) % len(item.gif_frames)
            item.next_due += item.gif_durations[item.gif_index] / 1000
            changed = True
            step_guard += 1

        if step_guard >= 240:
            item.next_due = now + item.gif_durations[item.gif_index] / 1000
        return changed

    def tick_gif(self, now: float, frame_budget: int = 18, time_budget_ms: Optional[float] = None) -> int:
        if not self.items or frame_budget <= 0 or now < self._resizing_until:
            return 0

        gif_indexes = [i for i, it in enumerate(self.items) if it.is_gif and it.gif_frames]
        if not gif_indexes:
            return 0

        start = self._gif_round_robin_start % len(gif_indexes)
        ordered = gif_indexes[start:] + gif_indexes[:start]

        slice_start = time.perf_counter()
        updated = 0
        scanned = 0
        for idx in ordered:
            if updated >= frame_budget or time.time() < self._resizing_until:
                break
            scanned += 1
            item = self.items[idx]
            if self._advance_gif_to_now(item, now):
                if self._refresh_gif_slot(idx):
                    updated += 1
                if time_budget_ms is not None and updated > 0:
                    elapsed_ms = (time.perf_counter() - slice_start) * 1000
                    if elapsed_ms >= time_budget_ms:
                        break

        self._gif_round_robin_start = (start + max(1, scanned)) % len(gif_indexes)
        return updated


class PicReadApp:
    def __init__(self) -> None:
        self._enable_dpi_awareness()
        self.root = tk.Tk()
        self.root.title(f"PicRead v{APP_VERSION} - 多窗口组平铺看图")
        self._icon_ref: Optional[ImageTk.PhotoImage] = None
        self._init_app_icon()
        self.root.protocol("WM_DELETE_WINDOW", self._on_app_close)

        self.groups: dict[int, GroupWindow] = {}
        self._next_group_id = 1
        self._free_group_ids: set[int] = set()
        self._drop_queue: queue.SimpleQueue[tuple[Optional[int], list]] = queue.SimpleQueue()
        self._group_order: list[int] = []
        self._pinned_groups: set[int] = set()
        self._active_group_id: Optional[int] = None
        self._drag_group_index: Optional[int] = None

        self._dirty = False
        self._last_save_ts = 0.0
        self._suspend_dirty = False
        self._interaction_pause_until = 0.0
        self._modal_dialog_depth = 0
        self._ui_state = self._load_ui_state()
        self.language_code = str(self._ui_state.get("language", "zh_CN"))
        if self.language_code not in LANGUAGE_OPTIONS:
            self.language_code = "zh_CN"
        self._i18n = self._load_i18n(self.language_code)
        self.root.title(self.tr("app.title", f"PicRead v{APP_VERSION} - 多窗口组平铺看图"))
        self._last_tick_updated = 0
        self._last_status_refresh = 0.0
        self.drag_drop_enabled = False
        self.drag_drop_backend = "none"
        self._native_drop: Optional[Win32DropManager] = None

        STATE_DIR.mkdir(parents=True, exist_ok=True)
        TEMPLATE_DIR.mkdir(parents=True, exist_ok=True)
        HISTORY_DIR.mkdir(parents=True, exist_ok=True)
        THUMB_CACHE_DIR.mkdir(parents=True, exist_ok=True)
        self._template_geometry_map: dict[str, str] = dict(self._ui_state.get("template_geometry_map", {}))
        self._thumb_photo_cache: OrderedDict[str, ImageTk.PhotoImage] = OrderedDict()
        self._thumb_render_token = 0

        self._set_initial_window_geometry()
        self._build_ui()
        self._setup_drag_drop()
        self.load_session(silent=True)
        self._schedule_tick()

    def _enable_dpi_awareness(self) -> None:
        try:
            import ctypes

            try:
                ctypes.windll.shcore.SetProcessDpiAwareness(2)
            except Exception:
                ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

    def _init_app_icon(self) -> None:
        # 打包 EXE 会使用嵌入图标；源码运行时尽量复用同一套图标资源。
        try:
            if ICON_ICO_PATH.exists():
                self.root.iconbitmap(default=str(ICON_ICO_PATH))
        except Exception:
            pass
        try:
            if ICON_PNG_PATH.exists():
                self._icon_ref = ImageTk.PhotoImage(file=str(ICON_PNG_PATH))
                self.root.iconphoto(True, self._icon_ref)
        except Exception:
            pass

    def apply_window_icon(self, win: tk.Toplevel) -> None:
        try:
            if ICON_ICO_PATH.exists():
                win.iconbitmap(default=str(ICON_ICO_PATH))
        except Exception:
            pass
        if self._icon_ref is not None:
            try:
                win.iconphoto(True, self._icon_ref)
            except Exception:
                pass

    def _default_group_name(self) -> str:
        return self.tr("group.default_name", "窗口组")

    def _set_initial_window_geometry(self) -> None:
        sw = max(1024, self.root.winfo_screenwidth())
        sh = max(720, self.root.winfo_screenheight())

        # 给任务栏/缩放留安全边距，避免首屏 UI 被裁切。
        width = min(1960, max(1520, int(sw * 0.975)))
        height = min(1120, max(820, int(sh * 0.90)))
        x = max(0, (sw - width) // 2)
        y = max(0, (sh - height) // 2)
        self.root.geometry(f"{width}x{height}+{x}+{y}")

        min_w = min(width, max(1460, int(sw * 0.90)))
        min_h = min(height, max(760, int(sh * 0.76)))
        self.root.minsize(min_w, min_h)

    def apply_safe_layout(self) -> None:
        self._set_initial_window_geometry()
        if hasattr(self, "notebook"):
            self.notebook.select(0)

    def _center_window(self, win: tk.Toplevel, width: int, height: int) -> None:
        sw = max(1024, win.winfo_screenwidth())
        sh = max(720, win.winfo_screenheight())
        w = min(width, max(380, int(sw * 0.9)))
        h = min(height, max(280, int(sh * 0.9)))
        x = max(0, (sw - w) // 2)
        y = max(0, (sh - h) // 2)
        win.geometry(f"{w}x{h}+{x}+{y}")

    def _bind_vertical_mousewheel(self, widget: tk.Misc, target) -> None:
        def _scroll_units(delta: int) -> None:
            if delta == 0:
                return
            try:
                target.yview_scroll(delta, "units")
            except Exception:
                pass

        def _on_mousewheel(evt: tk.Event) -> None:
            steps = max(1, abs(int(evt.delta)) // 120) if getattr(evt, "delta", 0) else 0
            if evt.delta > 0:
                _scroll_units(-steps)
            elif evt.delta < 0:
                _scroll_units(steps)

        widget.bind("<MouseWheel>", _on_mousewheel, add="+")
        widget.bind("<Button-4>", lambda _e: _scroll_units(-3), add="+")
        widget.bind("<Button-5>", lambda _e: _scroll_units(3), add="+")

    def _load_ui_state(self) -> dict:
        if not UI_STATE_FILE.exists():
            return {}
        try:
            data = json.loads(UI_STATE_FILE.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return data
        except Exception:
            pass
        return {}

    def _load_i18n(self, code: str) -> dict[str, str]:
        lang_file = I18N_DIR / f"{code}.json"
        try:
            data = json.loads(lang_file.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return {str(k): str(v) for k, v in data.items()}
        except Exception:
            pass
        return {}

    def tr(self, key: str, default: Optional[str] = None, **kwargs) -> str:
        text = self._i18n.get(key, default if default is not None else key)
        if kwargs:
            try:
                return text.format(**kwargs)
            except Exception:
                return text
        return text

    def perf_mode_label(self, key: str) -> str:
        return self.tr(f"perf_mode.{key}", key)

    def load_profile_label(self, key: str) -> str:
        return self.tr(f"load_profile.{key}", key)

    def language_label(self, code: str) -> str:
        return LANGUAGE_OPTIONS.get(code, code)

    def batch_order_label(self, key: str) -> str:
        safe_key = key if key in BATCH_ORDER_OPTIONS else "normal"
        return self.tr(f"batch_order.{safe_key}", BATCH_ORDER_OPTIONS[safe_key])

    def _save_ui_state(self) -> None:
        geom_items = list(self._template_geometry_map.items())[:300]
        data = {
            "template_view_mode": self.template_view_var.get() if hasattr(self, "template_view_var") else "list",
            "perf_mode": self.perf_mode_var.get() if hasattr(self, "perf_mode_var") else "平衡",
            "load_profile": self.load_profile_var.get() if hasattr(self, "load_profile_var") else "低负载",
            "language": self.language_code,
            "batch_import_order": self.batch_order_var.get() if hasattr(self, "batch_order_var") else "normal",
            "template_geometry_map": dict(geom_items),
        }
        try:
            UI_STATE_FILE.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _build_ui(self) -> None:
        self._setup_style()
        root_frame = ttk.Frame(self.root, padding=12)
        root_frame.pack(fill=tk.BOTH, expand=True)

        self.head_label = ttk.Label(
            root_frame,
            text=self.tr("app.header", f"PicRead v{APP_VERSION} | 多窗口组平铺看图"),
            font=("Microsoft YaHei UI", 14, "bold"),
        )
        self.head_label.pack(anchor="w")
        ttk.Separator(root_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=(8, 10))

        self.notebook = ttk.Notebook(root_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        groups_tab = ttk.Frame(self.notebook, padding=10)
        templates_tab = ttk.Frame(self.notebook, padding=10)
        history_tab = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(groups_tab, text=self.tr("tab.groups", "窗口组"))
        self.notebook.add(templates_tab, text=self.tr("tab.templates", "模板库"))
        self.notebook.add(history_tab, text=self.tr("tab.history", "历史记录"))

        control = ttk.Frame(groups_tab)
        control.pack(fill=tk.X)

        group_row1 = ttk.Frame(control)
        group_row1.pack(fill=tk.X, anchor="w")
        group_row2 = ttk.Frame(control)
        group_row2.pack(fill=tk.X, anchor="w", pady=(12, 0))
        group_row3 = ttk.Frame(control)
        group_row3.pack(fill=tk.X, anchor="w", pady=(12, 0))

        self.lbl_group_name = ttk.Label(group_row1, text=self.tr("control.group_name", "窗口组名:"))
        self.lbl_group_name.pack(side=tk.LEFT)
        self.group_name_var = tk.StringVar(value=self._default_group_name())
        self.group_name_entry = ttk.Entry(group_row1, textvariable=self.group_name_var, width=15)
        self.group_name_entry.pack(side=tk.LEFT, padx=(6, 22))

        self.lbl_rows = ttk.Label(group_row1, text=self.tr("control.rows", "行数:"))
        self.lbl_rows.pack(side=tk.LEFT)
        self.rows_var = tk.IntVar(value=2)
        self.rows_spin = ttk.Spinbox(group_row1, from_=1, to=12, textvariable=self.rows_var, width=5)
        self.rows_spin.pack(side=tk.LEFT, padx=(6, 22))

        self.smart_layout_var = tk.BooleanVar(value=True)
        self._control_label_font = ("Microsoft YaHei UI", 11)
        self.smart_layout_check = BoxToggle(
            group_row1,
            self.tr("control.smart_layout", "智能排版"),
            self.smart_layout_var,
            bg=self._theme_bg,
            fg=self._theme_fg,
            accent=self._theme_accent,
            box_size=18,
            font=self._control_label_font,
        )
        self.smart_layout_check.pack(side=tk.LEFT, padx=(0, 22))
        self.lbl_algorithm = ttk.Label(group_row1, text=self.tr("control.algorithm", "算法:"))
        self.lbl_algorithm.pack(side=tk.LEFT)
        self.layout_algo_var = tk.StringVar(value="balanced")
        self.layout_algo_combo = ttk.Combobox(
            group_row1,
            textvariable=self.layout_algo_var,
            values=[f"{LAYOUT_ALGORITHMS[key]} ({key})" for key in LAYOUT_ALGORITHMS],
            state="readonly",
            width=17,
        )
        self.layout_algo_combo.pack(side=tk.LEFT, padx=(6, 0))
        self.layout_algo_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_layout_algo_change())
        self._sync_layout_algo_value("balanced")

        self.lbl_perf_mode = ttk.Label(group_row2, text=self.tr("control.perf_mode", "性能模式:"))
        self.lbl_perf_mode.pack(side=tk.LEFT)
        default_mode = str(self._ui_state.get("perf_mode", "平衡"))
        if default_mode not in PERF_MODES:
            default_mode = "平衡"
        self.perf_mode_var = tk.StringVar(value=default_mode)
        self.perf_mode_display_var = tk.StringVar()
        self.perf_mode_combo = ttk.Combobox(
            group_row2, textvariable=self.perf_mode_display_var, values=[], state="readonly", width=12
        )
        self.perf_mode_combo.pack(side=tk.LEFT, padx=(6, 20))
        self.perf_mode_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_perf_mode_change())
        self.lbl_load = ttk.Label(group_row2, text=self.tr("control.load_profile", "负载:"))
        self.lbl_load.pack(side=tk.LEFT)
        default_load = str(self._ui_state.get("load_profile", "低负载"))
        if default_load not in LOAD_PROFILES:
            default_load = "低负载"
        self.load_profile_var = tk.StringVar(value=default_load)
        self.load_profile_display_var = tk.StringVar()
        self.load_profile_combo = ttk.Combobox(
            group_row2, textvariable=self.load_profile_display_var, values=[], state="readonly", width=12
        )
        self.load_profile_combo.pack(side=tk.LEFT, padx=(6, 20))
        self.load_profile_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_load_profile_change())
        self.lbl_language = ttk.Label(group_row2, text=self.tr("control.language", "语言:"))
        self.lbl_language.pack(side=tk.LEFT)
        self.language_display_var = tk.StringVar(value=self.language_label(self.language_code))
        self.language_combo = ttk.Combobox(
            group_row2,
            textvariable=self.language_display_var,
            values=[self.language_label(code) for code in LANGUAGE_OPTIONS],
            state="readonly",
            width=11,
        )
        self.language_combo.pack(side=tk.LEFT, padx=(6, 20))
        self.language_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_language_change())

        self.lbl_batch_order = ttk.Label(group_row3, text=self.tr("control.batch_order", "批量导入顺序:"))
        self.lbl_batch_order.pack(side=tk.LEFT)
        default_batch_order = str(self._ui_state.get("batch_import_order", "normal"))
        if default_batch_order not in BATCH_ORDER_OPTIONS:
            default_batch_order = "normal"
        self.batch_order_var = tk.StringVar(value=default_batch_order)
        self.batch_order_display_var = tk.StringVar()
        self.batch_order_combo = ttk.Combobox(
            group_row3,
            textvariable=self.batch_order_display_var,
            values=[],
            state="readonly",
            width=10,
        )
        self.batch_order_combo.pack(side=tk.LEFT, padx=(6, 20))
        self.batch_order_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_batch_order_change())

        group_actions = ttk.Frame(group_row2)
        group_actions.pack(side=tk.LEFT, padx=(8, 0))
        self.tuning_btn = ttk.Button(
            group_actions, text=self.tr("control.tuning_panel", "调参面板"), command=self.open_tuning_panel
        )
        self.tuning_btn.pack(side=tk.LEFT)
        self.create_group_btn = ttk.Button(
            group_actions, text=self.tr("control.create_group", "创建窗口组"), command=self.create_group, width=12
        )
        self.create_group_btn.pack(side=tk.LEFT, padx=(10, 0))

        list_frame = ttk.Frame(groups_tab)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        self.group_list = tk.Listbox(list_frame, height=10)
        self.group_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.group_list.bind("<<ListboxSelect>>", self._on_group_selected)
        self.group_list.bind("<ButtonPress-1>", self._on_group_list_press)
        self.group_list.bind("<B1-Motion>", self._on_group_list_drag)
        self.group_list.bind("<ButtonRelease-1>", self._on_group_list_release)
        self.group_list.bind("<Button-3>", self._on_group_list_right_click)
        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL, command=self.group_list.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.group_list.configure(yscrollcommand=scrollbar.set)
        self.group_list_menu = tk.Menu(self.root, tearoff=0)
        self.group_list_menu.add_command(label=self.tr("menu.pin_toggle", "置顶/取消置顶"), command=self._toggle_pin_selected_group)

        btns1 = ttk.Frame(groups_tab)
        btns1.pack(fill=tk.X)
        self.apply_layout_btn = ttk.Button(btns1, text=self.tr("button.apply_layout", "应用布局"), command=self.update_layout)
        self.apply_layout_btn.pack(side=tk.LEFT)
        self.merge_btn = ttk.Button(btns1, text=self.tr("button.merge_to_current", "合并到当前组"), command=self.merge_groups)
        self.merge_btn.pack(side=tk.LEFT, padx=8)
        self.close_group_btn = ttk.Button(btns1, text=self.tr("button.close_group", "关闭窗口组"), command=self.close_group)
        self.close_group_btn.pack(side=tk.RIGHT)

        btns2 = ttk.Frame(groups_tab)
        btns2.pack(fill=tk.X, pady=(8, 0))
        self.safe_layout_btn = ttk.Button(btns2, text=self.tr("button.safe_layout", "启动安全布局"), command=self.apply_safe_layout)
        self.safe_layout_btn.pack(side=tk.LEFT)
        self.save_template_btn = ttk.Button(btns2, text=self.tr("button.save_template", "保存为模板"), command=self.save_group_template)
        self.save_template_btn.pack(side=tk.LEFT)
        self.save_session_btn = ttk.Button(btns2, text=self.tr("button.save_session", "保存会话"), command=self.save_session_snapshot)
        self.save_session_btn.pack(side=tk.LEFT, padx=8)

        tpl_top = ttk.Frame(templates_tab)
        tpl_top.pack(fill=tk.X)

        tpl_actions = ttk.Frame(tpl_top)
        tpl_actions.pack(anchor="w")
        tpl_filters = ttk.Frame(tpl_top)
        tpl_filters.pack(fill=tk.X, anchor="w", pady=(12, 0))

        self.tpl_refresh_btn = ttk.Button(tpl_actions, text=self.tr("button.refresh_templates", "刷新模板库"), command=self.refresh_template_library)
        self.tpl_refresh_btn.pack(side=tk.LEFT)
        self.tpl_open_btn = ttk.Button(tpl_actions, text=self.tr("button.open_template", "打开模板"), command=self.load_group_template)
        self.tpl_open_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.tpl_update_btn = ttk.Button(tpl_actions, text=self.tr("button.update_template", "更新该模板"), command=self.update_linked_template)
        self.tpl_update_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.tpl_reload_btn = ttk.Button(tpl_actions, text=self.tr("button.reload_template", "重新加载模板"), command=self.reload_linked_template)
        self.tpl_reload_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.tpl_rename_btn = ttk.Button(tpl_actions, text=self.tr("button.rename_template", "重命名模板"), command=self.rename_selected_template)
        self.tpl_rename_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.tpl_tags_btn = ttk.Button(tpl_actions, text=self.tr("button.edit_tags", "编辑标签"), command=self.edit_selected_template_tags)
        self.tpl_tags_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.tpl_delete_btn = ttk.Button(tpl_actions, text=self.tr("button.delete_template", "删除模板"), command=self.delete_selected_template)
        self.tpl_delete_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.template_view_var = tk.StringVar(value=str(self._ui_state.get("template_view_mode", "list")))
        self.tpl_search_label = ttk.Label(tpl_filters, text=self.tr("template.search", "搜索:"))
        self.tpl_search_label.pack(side=tk.LEFT)
        self.template_search_var = tk.StringVar(value="")
        self.template_search_entry = ttk.Entry(tpl_filters, textvariable=self.template_search_var, width=26)
        self.template_search_entry.pack(side=tk.LEFT, padx=(6, 18))
        self.template_search_var.trace_add("write", lambda *_: self.refresh_template_library())
        self.tpl_tag_label = ttk.Label(tpl_filters, text=self.tr("template.tag", "标签:"))
        self.tpl_tag_label.pack(side=tk.LEFT)
        self.template_tag_var = tk.StringVar(value=self.tr("template.all", "全部"))
        self.template_tag_combo = ttk.Combobox(
            tpl_filters, textvariable=self.template_tag_var, values=[self.tr("template.all", "全部")], state="readonly", width=12
        )
        self.template_tag_combo.pack(side=tk.LEFT, padx=(6, 18))
        self.template_tag_combo.bind("<<ComboboxSelected>>", lambda _e: self.refresh_template_library())
        tpl_view_wrap = ttk.Frame(tpl_filters)
        tpl_view_wrap.pack(side=tk.LEFT, padx=(4, 0))
        self.tpl_view_icon_radio = DotRadio(
            tpl_view_wrap,
            self.tr("template.view_icon", "图标"),
            self.template_view_var,
            "icon",
            command=self._switch_template_view,
            bg=self._theme_bg,
            fg=self._theme_fg,
            accent=self._theme_accent,
            box_size=18,
            font=self._control_label_font,
        )
        self.tpl_view_icon_radio.pack(side=tk.LEFT)
        self.tpl_view_list_radio = DotRadio(
            tpl_view_wrap,
            self.tr("template.view_list", "列表"),
            self.template_view_var,
            "list",
            command=self._switch_template_view,
            bg=self._theme_bg,
            fg=self._theme_fg,
            accent=self._theme_accent,
            box_size=18,
            font=self._control_label_font,
        )
        self.tpl_view_list_radio.pack(side=tk.LEFT, padx=(10, 0))

        self.template_entries: list[dict] = []
        self.template_selected_idx: Optional[int] = None
        self.template_thumbs: list[ImageTk.PhotoImage] = []
        self.template_icon_cells: list[tuple[int, int, int, int]] = []
        self.template_icon_outline_ids: list[int] = []
        self._template_render_after_id: Optional[str] = None
        self.template_context_var = tk.StringVar(value=self.tr("template.context_none", "当前目标组：未选择"))
        ttk.Label(templates_tab, textvariable=self.template_context_var).pack(anchor="w", pady=(8, 2))

        self.tpl_stack = ttk.Frame(templates_tab)
        self.tpl_stack.pack(fill=tk.BOTH, expand=True, pady=(8, 0))

        self.tpl_list_frame = ttk.Frame(self.tpl_stack)
        self.template_list = tk.Listbox(self.tpl_list_frame)
        self.template_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.template_list.bind("<<ListboxSelect>>", self._on_template_list_selected)
        self.template_list.bind("<Double-Button-1>", lambda _e: self.load_group_template())
        self._bind_vertical_mousewheel(self.template_list, self.template_list)
        self.tpl_list_scroll = ttk.Scrollbar(self.tpl_list_frame, orient=tk.VERTICAL, command=self.template_list.yview)
        self.tpl_list_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.template_list.configure(yscrollcommand=self.tpl_list_scroll.set)

        self.tpl_icon_frame = ttk.Frame(self.tpl_stack)
        self.template_canvas = tk.Canvas(self.tpl_icon_frame, bg="#121212", highlightthickness=0)
        self.template_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.template_canvas.bind("<Button-1>", self._on_template_icon_click)
        self.template_canvas.bind("<Double-Button-1>", lambda _e: self.load_group_template())
        self.template_canvas.bind("<Configure>", lambda _e: self._schedule_template_icon_render())
        self._bind_vertical_mousewheel(self.template_canvas, self.template_canvas)
        self.tpl_icon_scroll = ttk.Scrollbar(self.tpl_icon_frame, orient=tk.VERTICAL, command=self.template_canvas.yview)
        self.tpl_icon_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.template_canvas.configure(yscrollcommand=self.tpl_icon_scroll.set)

        self._switch_template_view()
        self.refresh_template_library()
        self._build_history_tab(history_tab)
        self.refresh_history_library()

        self.status_var = tk.StringVar(value=self.tr("status.ready", "就绪"))
        status = ttk.Label(root_frame, textvariable=self.status_var, anchor="w", justify=tk.LEFT)
        status.pack(fill=tk.X, pady=(8, 0))
        root_frame.bind(
            "<Configure>",
            lambda e: status.configure(wraplength=max(280, int(e.width) - 24)),
        )
        self._refresh_perf_mode_options()
        self._refresh_load_profile_options()
        self._refresh_batch_order_options()
        self._apply_dark_widget_styles()
        self._refresh_window_texts()

    def _setup_style(self) -> None:
        self.root.option_add("*Font", "{Microsoft YaHei UI} 11")
        style = ttk.Style(self.root)
        for candidate in ("clam", "vista", "xpnative"):
            if candidate in style.theme_names():
                style.theme_use(candidate)
                break
        # VSCode-like dark style
        bg = "#1e1e1e"
        panel = "#252526"
        fg = "#d4d4d4"
        accent = "#007acc"
        muted = "#9da5b4"
        border = "#3c3c3c"
        self._theme_bg = bg
        self._theme_panel = panel
        self._theme_fg = fg
        self._theme_accent = accent
        self._theme_muted = muted
        self._theme_border = border

        self.root.configure(bg=bg)
        style.configure(".", background=bg, foreground=fg)
        style.configure("TFrame", background=bg)
        style.configure("TLabel", background=bg, foreground=fg, padding=(2, 2))
        style.configure("TButton", background=panel, foreground=fg, bordercolor="#747474", padding=(16, 9))
        style.map(
            "TButton",
            background=[("active", "#2f3335"), ("pressed", "#3a4046")],
            foreground=[("disabled", muted)],
        )
        style.configure("TEntry", fieldbackground=panel, foreground=fg, bordercolor="#747474", padding=(6, 5))
        style.configure(
            "TCombobox",
            fieldbackground=panel,
            foreground=fg,
            background=panel,
            bordercolor="#747474",
            darkcolor=panel,
            lightcolor=panel,
            arrowcolor="#ffffff",
            arrowsize=18,
            padding=(6, 5),
        )
        style.map(
            "TCombobox",
            fieldbackground=[("readonly", panel), ("disabled", "#2a2a2a")],
            foreground=[("readonly", fg), ("disabled", "#7f848e")],
            selectbackground=[("readonly", panel)],
            selectforeground=[("readonly", fg)],
        )
        style.configure(
            "TSpinbox",
            fieldbackground=panel,
            foreground=fg,
            bordercolor="#747474",
            darkcolor=panel,
            lightcolor=panel,
            arrowcolor="#ffffff",
            arrowsize=18,
            padding=(4, 4),
        )
        style.map(
            "TSpinbox",
            fieldbackground=[("readonly", panel), ("disabled", "#2a2a2a")],
            foreground=[("readonly", fg), ("disabled", "#7f848e")],
        )
        style.configure(
            "TCheckbutton",
            background=bg,
            foreground=fg,
            indicatorcolor=panel,
            indicatorbackground=panel,
            indicatormargin=4,
            padding=(4, 3),
        )
        style.map(
            "TCheckbutton",
            indicatorcolor=[("selected", "#dcdcdc"), ("!selected", panel)],
            indicatorbackground=[("selected", panel), ("!selected", panel)],
            foreground=[("disabled", muted)],
        )
        style.configure("TRadiobutton", background=bg, foreground=fg)
        style.configure("TNotebook", background=bg, borderwidth=0)
        style.configure("TNotebook.Tab", background=panel, foreground=fg, padding=(14, 8))
        style.map("TNotebook.Tab", background=[("selected", "#333333")], foreground=[("selected", "#ffffff")])
        style.configure("TSeparator", background=border)
        style.configure("Vertical.TScrollbar", background=panel, troughcolor=bg, bordercolor=border)
        self.root.option_add("*Menu.background", panel)
        self.root.option_add("*Menu.foreground", fg)
        self.root.option_add("*Menu.activeBackground", accent)
        self.root.option_add("*Menu.activeForeground", "#ffffff")

    def _apply_dark_widget_styles(self) -> None:
        list_bg = "#1b1b1b"
        list_fg = "#d4d4d4"
        sel_bg = "#264f78"
        sel_fg = "#ffffff"
        for lb in (self.group_list, self.template_list, self.history_list):
            lb.configure(
                bg=list_bg,
                fg=list_fg,
                selectbackground=sel_bg,
                selectforeground=sel_fg,
                highlightthickness=1,
                highlightbackground="#3c3c3c",
                highlightcolor="#3c3c3c",
                bd=0,
            )
        self.template_canvas.configure(bg="#1b1b1b")

    def _layout_algo_label(self, key: str) -> str:
        safe_key = key if key in LAYOUT_ALGORITHMS else "legacy"
        lang = getattr(self, "language_code", "zh_CN")
        suffix = safe_key if lang == "zh_CN" else safe_key.upper()
        return f"{self.tr(f'layout.{safe_key}', LAYOUT_ALGORITHMS[safe_key])} ({suffix})"

    def _layout_algo_key_from_var(self) -> str:
        raw = self.layout_algo_var.get().strip() if hasattr(self, "layout_algo_var") else "legacy"
        match = re.search(r"\(([^()]+)\)\s*$", raw)
        key = (match.group(1).strip() if match else raw).lower()
        return key if key in LAYOUT_ALGORITHMS else "legacy"

    def _sync_layout_algo_value(self, key: Optional[str] = None) -> None:
        safe_key = key or self._layout_algo_key_from_var()
        if hasattr(self, "layout_algo_var"):
            self.layout_algo_var.set(self._layout_algo_label(safe_key))

    def _on_layout_algo_change(self) -> None:
        self._sync_layout_algo_value()
        if hasattr(self, "smart_layout_var"):
            self.smart_layout_var.set(True)
        g = self._selected_group()
        if g is None:
            return
        self._apply_layout_to_group(g)

    def _refresh_perf_mode_options(self) -> None:
        values = [self.perf_mode_label(key) for key in PERF_MODES]
        self.perf_mode_combo.configure(values=values)
        current = self.perf_mode_var.get() if hasattr(self, "perf_mode_var") else "平衡"
        self.perf_mode_display_var.set(self.perf_mode_label(current))

    def _refresh_load_profile_options(self) -> None:
        values = [self.load_profile_label(key) for key in LOAD_PROFILES]
        self.load_profile_combo.configure(values=values)
        current = self.load_profile_var.get() if hasattr(self, "load_profile_var") else "低负载"
        self.load_profile_display_var.set(self.load_profile_label(current))

    def _refresh_batch_order_options(self) -> None:
        values = [self.batch_order_label(key) for key in BATCH_ORDER_OPTIONS]
        self.batch_order_combo.configure(values=values)
        current = self.batch_order_var.get() if hasattr(self, "batch_order_var") else "normal"
        if current not in BATCH_ORDER_OPTIONS:
            current = "normal"
            self.batch_order_var.set(current)
        self.batch_order_display_var.set(self.batch_order_label(current))

    def _perf_mode_key_from_display(self) -> str:
        raw = self.perf_mode_display_var.get().strip()
        for key in PERF_MODES:
            if raw == self.perf_mode_label(key):
                return key
        return self.perf_mode_var.get() if hasattr(self, "perf_mode_var") else "平衡"

    def _load_profile_key_from_display(self) -> str:
        raw = self.load_profile_display_var.get().strip()
        for key in LOAD_PROFILES:
            if raw == self.load_profile_label(key):
                return key
        return self.load_profile_var.get() if hasattr(self, "load_profile_var") else "低负载"

    def _batch_order_key_from_display(self) -> str:
        raw = self.batch_order_display_var.get().strip()
        for key in BATCH_ORDER_OPTIONS:
            if raw == self.batch_order_label(key):
                return key
        return self.batch_order_var.get() if hasattr(self, "batch_order_var") else "normal"

    def _on_batch_order_change(self) -> None:
        self.batch_order_var.set(self._batch_order_key_from_display())
        self._save_ui_state()

    def _on_language_change(self) -> None:
        selected = self.language_display_var.get().strip()
        for code in LANGUAGE_OPTIONS:
            if selected == self.language_label(code):
                self.language_code = code
                self._i18n = self._load_i18n(code)
                self.mark_dirty()
                self._refresh_window_texts()
                self._update_status(self._last_tick_updated, time.time())
                return

    def _refresh_window_texts(self) -> None:
        old_default_names = {"窗口组", "Window Group"}
        if self.group_name_var.get().strip() in old_default_names:
            self.group_name_var.set(self._default_group_name())
        self.root.title(self.tr("app.title", f"PicRead v{APP_VERSION} - 多窗口组平铺看图"))
        self.head_label.configure(text=self.tr("app.header", f"PicRead v{APP_VERSION} | 多窗口组平铺看图"))
        self.notebook.tab(0, text=self.tr("tab.groups", "窗口组"))
        self.notebook.tab(1, text=self.tr("tab.templates", "模板库"))
        self.notebook.tab(2, text=self.tr("tab.history", "历史记录"))
        self.lbl_group_name.configure(text=self.tr("control.group_name", "窗口组名:"))
        self.lbl_rows.configure(text=self.tr("control.rows", "行数:"))
        self.smart_layout_check.set_text(self.tr("control.smart_layout", "智能排版"))
        self.lbl_algorithm.configure(text=self.tr("control.algorithm", "算法:"))
        self.create_group_btn.configure(text=self.tr("control.create_group", "创建窗口组"))
        self.lbl_perf_mode.configure(text=self.tr("control.perf_mode", "性能模式:"))
        self.lbl_load.configure(text=self.tr("control.load_profile", "负载:"))
        self.lbl_language.configure(text=self.tr("control.language", "语言:"))
        self.lbl_batch_order.configure(text=self.tr("control.batch_order", "批量导入顺序:"))
        self.tuning_btn.configure(text=self.tr("control.tuning_panel", "调参面板"))
        self.group_list_menu.entryconfigure(0, label=self.tr("menu.pin_toggle", "置顶/取消置顶"))
        self.apply_layout_btn.configure(text=self.tr("button.apply_layout", "应用布局"))
        self.merge_btn.configure(text=self.tr("button.merge_to_current", "合并到当前组"))
        self.close_group_btn.configure(text=self.tr("button.close_group", "关闭窗口组"))
        self.safe_layout_btn.configure(text=self.tr("button.safe_layout", "启动安全布局"))
        self.save_template_btn.configure(text=self.tr("button.save_template", "保存为模板"))
        self.save_session_btn.configure(text=self.tr("button.save_session", "保存会话"))
        self.tpl_refresh_btn.configure(text=self.tr("button.refresh_templates", "刷新模板库"))
        self.tpl_open_btn.configure(text=self.tr("button.open_template", "打开模板"))
        self.tpl_rename_btn.configure(text=self.tr("button.rename_template", "重命名模板"))
        self.tpl_tags_btn.configure(text=self.tr("button.edit_tags", "编辑标签"))
        self.tpl_delete_btn.configure(text=self.tr("button.delete_template", "删除模板"))
        self.tpl_update_btn.configure(text=self.tr("button.update_template", "更新该模板"))
        self.tpl_reload_btn.configure(text=self.tr("button.reload_template", "重新加载模板"))
        self.tpl_view_list_radio.set_text(self.tr("template.view_list", "列表"))
        self.tpl_view_icon_radio.set_text(self.tr("template.view_icon", "图标"))
        self.tpl_tag_label.configure(text=self.tr("template.tag", "标签:"))
        self.tpl_search_label.configure(text=self.tr("template.search", "搜索:"))
        if hasattr(self, "history_refresh_btn"):
            self.history_refresh_btn.configure(text=self.tr("button.refresh_history", "刷新历史"))
            self.history_open_btn.configure(text=self.tr("button.open_selected_history", "打开所选历史"))
        self.language_combo.configure(values=[self.language_label(code) for code in LANGUAGE_OPTIONS])
        self.language_display_var.set(self.language_label(self.language_code))
        self._refresh_perf_mode_options()
        self._refresh_load_profile_options()
        self._refresh_batch_order_options()
        self._sync_layout_algo_value(self._layout_algo_key_from_var())
        self._update_template_context_label()
        self.refresh_template_library()
        self.refresh_history_library()
        for g in self.groups.values():
            g.refresh_localized_texts()

    def mark_dirty(self) -> None:
        if self._suspend_dirty:
            return
        self._dirty = True

    def set_active_group(self, gid: int) -> None:
        if gid not in self.groups:
            return
        self._active_group_id = gid
        if gid in self._group_order:
            idx = self._group_order.index(gid)
            self.group_list.selection_clear(0, tk.END)
            self.group_list.selection_set(idx)
        self._update_template_context_label()

    def _setup_drag_drop(self) -> None:
        if windnd is not None:
            self.drag_drop_backend = "windnd"
            self.drag_drop_enabled = True
        elif sys.platform.startswith("win"):
            try:
                self._native_drop = Win32DropManager()
                self.drag_drop_backend = "win32"
                self.drag_drop_enabled = True
            except Exception:
                self._native_drop = None
                self.drag_drop_backend = "none"
                self.drag_drop_enabled = False
        else:
            self.drag_drop_backend = "none"
            self.drag_drop_enabled = False
        self.bind_drop_target(self.root, self.make_drop_handler(None))

    def bind_drop_target(self, widget: tk.Misc, callback) -> None:
        if self.drag_drop_backend == "windnd" and windnd is not None:
            try:
                windnd.hook_dropfiles(widget, func=callback)
                return
            except Exception:
                self.drag_drop_enabled = False
                self.drag_drop_backend = "none"
        if self.drag_drop_backend == "win32" and self._native_drop is not None:
            try:
                self._native_drop.bind(widget, callback)
            except Exception:
                self.drag_drop_enabled = False
                self.drag_drop_backend = "none"

    def make_drop_handler(self, group_id: Optional[int]):
        def _handler(files):
            try:
                payload = list(files)
            except Exception:
                payload = []
            self._drop_queue.put((group_id, payload))

        return _handler

    def _decode_drop_item(self, item) -> str:
        if isinstance(item, (bytes, bytearray)):
            raw = bytes(item)
            if not raw:
                return ""
            candidates: list[str] = []
            if b"\x00" in raw:
                candidates.extend(["utf-16-le", "utf-16-be"])
            fsenc = sys.getfilesystemencoding() or "utf-8"
            preferred = locale.getpreferredencoding(False) or ""
            for enc in (fsenc, preferred, "utf-8-sig", "utf-8", "gb18030", "gbk", "cp932", "shift_jis", "mbcs"):
                if not enc or enc in candidates:
                    continue
                candidates.append(enc)
            for enc in candidates:
                try:
                    return raw.decode(enc).replace("\x00", "")
                except Exception:
                    continue
            try:
                return os.fsdecode(raw).replace("\x00", "")
            except Exception:
                return raw.decode(fsenc, errors="surrogateescape").replace("\x00", "")
        return str(item)

    def _normalize_drop_text(self, text: str) -> str:
        raw = text.strip()
        if not raw:
            return ""

        if raw.startswith("{") and raw.endswith("}"):
            raw = raw[1:-1].strip()
        raw = raw.strip('"')

        if (raw.startswith("b'") and raw.endswith("'")) or (
            raw.startswith('b"') and raw.endswith('"')
        ):
            try:
                maybe_bytes = ast.literal_eval(raw)
                if isinstance(maybe_bytes, (bytes, bytearray)):
                    raw = self._decode_drop_item(maybe_bytes)
            except Exception:
                pass

        return raw.strip()

    def _collect_supported_paths(self, items) -> list[Path]:
        paths: list[Path] = []
        seen: set[str] = set()

        for raw in items:
            if isinstance(raw, Path):
                p = raw
            else:
                text = self._normalize_drop_text(self._decode_drop_item(raw))
                if not text:
                    continue
                p = Path(text)

            if p.suffix.lower() not in SUPPORTED_EXTS or not p.is_file():
                continue

            key = str(p.resolve())
            if key in seen:
                continue
            seen.add(key)
            paths.append(p)

        return paths

    def _order_batch_paths(self, paths: list[Path]) -> list[Path]:
        order = self.batch_order_var.get() if hasattr(self, "batch_order_var") else "normal"
        ordered = list(paths)
        if order == "reverse":
            ordered.reverse()
        return ordered

    def add_paths_to_group(
        self,
        group: GroupWindow,
        paths: list[Path],
        show_errors: bool = True,
        apply_batch_order: bool = False,
    ) -> None:
        if not paths:
            return
        group.add_paths(self._order_batch_paths(paths) if apply_batch_order else paths, show_errors=show_errors)
        self._refresh_list(select_gid=group.group_id)

    def _on_drop_to_main(self, files) -> None:
        paths = self._collect_supported_paths(files)
        if not paths:
            messagebox.showwarning(self.tr("msg.notice", "提示"), self.tr("msg.no_supported_images_dropped", "拖入的文件里没有受支持的图片格式。"))
            return

        group = self._selected_group()
        if group is None and len(self.groups) == 1:
            group = next(iter(self.groups.values()))

        if group is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_group_before_drop", "请先创建并选中一个窗口组，再拖入图片。"))
            return

        self.add_paths_to_group(group, paths, apply_batch_order=True)

    def _on_drop_to_group(self, group: GroupWindow, files) -> None:
        paths = self._collect_supported_paths(files)
        if not paths:
            messagebox.showwarning(self.tr("msg.notice", "提示"), self.tr("msg.no_supported_images_dropped", "拖入的文件里没有受支持的图片格式。"))
            return
        self.add_paths_to_group(group, paths, apply_batch_order=True)

    def _dispatch_drop_event(self, group_id: Optional[int], files) -> None:
        if group_id is None:
            self._on_drop_to_main(files)
            return

        group = self.groups.get(group_id)
        if group is None:
            return
        self._on_drop_to_group(group, files)

    def _drain_drop_queue(self) -> None:
        while True:
            try:
                group_id, files = self._drop_queue.get_nowait()
            except queue.Empty:
                break
            self._dispatch_drop_event(group_id, files)

    def _selected_group(self) -> Optional[GroupWindow]:
        idx = self.group_list.curselection()
        if not idx:
            if self._active_group_id is not None:
                return self.groups.get(self._active_group_id)
            return None
        list_idx = idx[0]
        if list_idx < 0 or list_idx >= len(self._group_order):
            if self._active_group_id is not None:
                return self.groups.get(self._active_group_id)
            return None
        gid = self._group_order[list_idx]
        return self.groups.get(gid)

    def pause_heavy_work(self, seconds: float = 0.6) -> None:
        self._interaction_pause_until = max(self._interaction_pause_until, time.time() + max(0.0, seconds))

    def _begin_modal_block(self) -> None:
        self._modal_dialog_depth += 1
        self.pause_heavy_work(10.0)

    def _end_modal_block(self) -> None:
        if self._modal_dialog_depth > 0:
            self._modal_dialog_depth -= 1
        if self._modal_dialog_depth <= 0:
            self._modal_dialog_depth = 0
            self.pause_heavy_work(0.8)

    def heavy_work_paused(self) -> bool:
        return self._modal_dialog_depth > 0 or time.time() < self._interaction_pause_until

    def _safe_template_filename(self, name: str) -> str:
        clean = re.sub(r"[^\w\-\u4e00-\u9fff]+", "_", name.strip())
        return (clean or "template") + ".json"

    def _dialog_parent(self, group: Optional[GroupWindow] = None) -> tk.Misc:
        if group is not None:
            try:
                if group.top.winfo_exists():
                    return group.top
            except Exception:
                pass
        return self.root

    def _show_dialog_window(self, win: tk.Toplevel, parent: tk.Misc) -> None:
        win.transient(parent)
        win.update_idletasks()
        win.lift()
        try:
            win.attributes("-topmost", True)
            win.after(120, lambda: win.winfo_exists() and win.attributes("-topmost", False))
        except Exception:
            pass
        try:
            win.focus_force()
        except Exception:
            pass

    def _template_display_name(self, data: dict, fallback_stem: str) -> str:
        raw = str(data.get("template_name", data.get("name", fallback_stem))).strip()
        if raw in {"", "窗口组", "模板组", "Window Group", "Template Group"}:
            return fallback_stem
        return raw

    def _switch_template_view(self) -> None:
        mode = self.template_view_var.get()
        if mode not in ("list", "icon"):
            mode = "list"
            self.template_view_var.set(mode)
        self._ui_state["template_view_mode"] = mode
        self.tpl_list_frame.pack_forget()
        self.tpl_icon_frame.pack_forget()
        if mode == "icon":
            self.tpl_icon_frame.pack(fill=tk.BOTH, expand=True)
            self._schedule_template_icon_render()
        else:
            self.tpl_list_frame.pack(fill=tk.BOTH, expand=True)

    def _schedule_template_icon_render(self) -> None:
        if not hasattr(self, "template_canvas"):
            return
        if self._template_render_after_id:
            try:
                self.root.after_cancel(self._template_render_after_id)
            except Exception:
                pass
        self._template_render_after_id = self.root.after(80, self._flush_template_icon_render)

    def _flush_template_icon_render(self) -> None:
        self._template_render_after_id = None
        self._render_template_icons()

    def current_load_profile(self) -> dict:
        name = self.load_profile_var.get() if hasattr(self, "load_profile_var") else "低负载"
        return LOAD_PROFILES.get(name, LOAD_PROFILES["低负载"])

    def current_cache_limit(self) -> int:
        return int(self.current_load_profile()["cache_limit"])

    def current_profile(self) -> dict:
        mode = self.perf_mode_var.get() if hasattr(self, "perf_mode_var") else "平衡"
        base = deepcopy(PERF_MODES.get(mode, PERF_MODES["平衡"]))
        load_profile = self.current_load_profile()
        base_budget = int(base["frame_budget"])
        effective_budget = max(8, int(round(base_budget * float(load_profile["budget_scale"]))))
        base["base_frame_budget"] = base_budget
        base["frame_budget"] = effective_budget
        base["cache_limit"] = int(load_profile["cache_limit"])
        base["load_name"] = self.load_profile_var.get() if hasattr(self, "load_profile_var") else "低负载"
        base["memory_hint_gb"] = int(load_profile["memory_hint_gb"])
        return base

    def _on_perf_mode_change(self) -> None:
        self.perf_mode_var.set(self._perf_mode_key_from_display())
        self.mark_dirty()
        for g in self.groups.values():
            g._photo_cache.clear()
            g.render(force=True)
        self._sync_tuning_panel_from_mode()

    def _on_load_profile_change(self) -> None:
        self.load_profile_var.set(self._load_profile_key_from_display())
        self.mark_dirty()
        for g in self.groups.values():
            g._trim_photo_cache()
        self._update_status(self._last_tick_updated, time.time())

    def _sync_tuning_panel_from_mode(self) -> None:
        if not hasattr(self, "_tune_win") or self._tune_win is None or not self._tune_win.winfo_exists():
            return
        mode = self.perf_mode_var.get()
        p = PERF_MODES.get(mode, PERF_MODES["平衡"])
        self._tune_tick_var.set(int(p["tick_ms"]))
        self._tune_budget_var.set(int(p["frame_budget"]))
        self._tune_multi_var.set(bool(p["multi_step"]))
        self._tune_two_pass_var.set(bool(p["two_pass"]))
        self._tune_blur_var.set(float(p["pre_blur"]))
        self._tune_sharpen_var.set(bool(p["sharpen"]))
        self._tune_resample_var.set(RESAMPLE_VALUE_TO_NAME.get(p["resample"], "LANCZOS"))

    def open_tuning_panel(self) -> None:
        if hasattr(self, "_tune_win") and self._tune_win is not None and self._tune_win.winfo_exists():
            self._tune_win.deiconify()
            self._tune_win.lift()
            self._sync_tuning_panel_from_mode()
            return

        win = tk.Toplevel(self.root)
        win.title(self.tr("tuning.title", "画质/性能调参"))
        self._center_window(win, 620, 470)
        win.minsize(560, 420)
        win.transient(self.root)
        self._tune_win = win

        frame = ttk.Frame(win, padding=12)
        frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(frame, text=self.tr("tuning.current_mode_hint", "当前模式参数（修改后立即生效）")).pack(anchor="w")
        ttk.Label(frame, text=self.tr("tuning.checkbox_hint", "说明：复选框勾选=开启，取消=关闭")).pack(anchor="w", pady=(2, 8))

        self._tune_tick_var = tk.IntVar()
        self._tune_budget_var = tk.IntVar()
        self._tune_multi_var = tk.BooleanVar()
        self._tune_two_pass_var = tk.BooleanVar()
        self._tune_blur_var = tk.DoubleVar()
        self._tune_sharpen_var = tk.BooleanVar()
        self._tune_resample_var = tk.StringVar(value="LANCZOS")

        grid = ttk.Frame(frame)
        grid.pack(fill=tk.BOTH, expand=True, pady=(10, 0))

        ttk.Label(grid, text=self.tr("tuning.tick_ms", "刷新间隔 ms")).grid(row=0, column=0, sticky="w")
        ttk.Scale(grid, from_=12, to=45, variable=self._tune_tick_var, orient=tk.HORIZONTAL).grid(row=0, column=1, sticky="ew", padx=8)
        ttk.Label(grid, textvariable=self._tune_tick_var).grid(row=0, column=2, sticky="e")

        ttk.Label(grid, text=self.tr("tuning.frame_budget", "每轮帧预算")).grid(row=1, column=0, sticky="w")
        ttk.Scale(grid, from_=8, to=80, variable=self._tune_budget_var, orient=tk.HORIZONTAL).grid(row=1, column=1, sticky="ew", padx=8)
        ttk.Label(grid, textvariable=self._tune_budget_var).grid(row=1, column=2, sticky="e")

        ttk.Label(grid, text=self.tr("tuning.resample", "重采样")).grid(row=2, column=0, sticky="w")
        ttk.Combobox(
            grid,
            textvariable=self._tune_resample_var,
            values=list(RESAMPLE_NAME_TO_VALUE.keys()),
            state="readonly",
            width=14,
        ).grid(row=2, column=1, sticky="w", padx=8)

        ttk.Label(grid, text=self.tr("tuning.pre_blur", "预模糊")).grid(row=3, column=0, sticky="w")
        ttk.Scale(grid, from_=0.0, to=0.5, variable=self._tune_blur_var, orient=tk.HORIZONTAL).grid(row=3, column=1, sticky="ew", padx=8)
        ttk.Label(grid, textvariable=self._tune_blur_var).grid(row=3, column=2, sticky="e")

        self._tune_multi_check = BoxToggle(
            grid,
            self.tr("tuning.multi_step", "开启多段缩放"),
            self._tune_multi_var,
            bg=self._theme_bg,
            fg=self._theme_fg,
            accent=self._theme_accent,
            box_size=18,
            font=self._control_label_font,
        )
        self._tune_multi_check.grid(row=4, column=0, sticky="w", pady=(4, 0))
        self._tune_two_pass_check = BoxToggle(
            grid,
            self.tr("tuning.two_pass", "开启双通道缩放"),
            self._tune_two_pass_var,
            bg=self._theme_bg,
            fg=self._theme_fg,
            accent=self._theme_accent,
            box_size=18,
            font=self._control_label_font,
        )
        self._tune_two_pass_check.grid(row=4, column=1, sticky="w", padx=8, pady=(4, 0))
        self._tune_sharpen_check = BoxToggle(
            grid,
            self.tr("tuning.sharpen", "开启锐化"),
            self._tune_sharpen_var,
            bg=self._theme_bg,
            fg=self._theme_fg,
            accent=self._theme_accent,
            box_size=18,
            font=self._control_label_font,
        )
        self._tune_sharpen_check.grid(row=5, column=0, sticky="w", pady=(4, 0))
        grid.columnconfigure(1, weight=1)

        def _apply() -> None:
            mode = self.perf_mode_var.get()
            p = PERF_MODES.get(mode, PERF_MODES["平衡"])
            p["tick_ms"] = int(self._tune_tick_var.get())
            p["frame_budget"] = int(self._tune_budget_var.get())
            p["multi_step"] = bool(self._tune_multi_var.get())
            p["two_pass"] = bool(self._tune_two_pass_var.get())
            p["pre_blur"] = float(self._tune_blur_var.get())
            p["sharpen"] = bool(self._tune_sharpen_var.get())
            p["resample"] = RESAMPLE_NAME_TO_VALUE.get(self._tune_resample_var.get(), Image.Resampling.LANCZOS)
            self._on_perf_mode_change()

        def _reset_mode() -> None:
            mode = self.perf_mode_var.get()
            if mode in DEFAULT_PERF_MODES:
                PERF_MODES[mode] = deepcopy(DEFAULT_PERF_MODES[mode])
            self._sync_tuning_panel_from_mode()
            self._on_perf_mode_change()

        btns = ttk.Frame(frame)
        btns.pack(fill=tk.X, pady=(10, 0))
        ttk.Button(btns, text=self.tr("button.apply", "应用"), command=_apply).pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(btns, text=self.tr("button.reset_current_mode", "重置当前模式"), command=_reset_mode).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=8)

        self._sync_tuning_panel_from_mode()

    def _update_status(self, updated_frames: int, now: float) -> None:
        if now - self._last_status_refresh < 0.25:
            return
        self._last_status_refresh = now

        gif_count = 0
        hits = 0
        misses = 0
        photo_cache_entries = 0
        for g in self.groups.values():
            gif_count += sum(1 for it in g.items if it.is_gif and it.gif_frames)
            hits += g.cache_hits
            misses += g.cache_misses
            photo_cache_entries += len(g._photo_cache)
        ratio = (hits / (hits + misses) * 100) if (hits + misses) else 0.0
        profile = self.current_profile()
        mem_mb = self._process_mem_mb()
        mem_text = f"{mem_mb:.0f}MB" if mem_mb > 0 else "N/A"
        if not getattr(self, "drag_drop_enabled", False):
            drag_text = self.tr("status.drag_off", "拖拽:关")
        else:
            backend = getattr(self, "drag_drop_backend", "none")
            if backend == "windnd":
                drag_text = self.tr("status.drag_windnd", "拖拽:开(windnd)")
            elif backend == "win32":
                drag_text = self.tr("status.drag_system", "拖拽:开(系统)")
            else:
                drag_text = self.tr("status.drag_on", "拖拽:开")
        self.status_var.set(
            self.tr(
                "status.summary",
                "模式: {mode} | 负载: {load} | 策略: {strategy} | 预算: {budget}帧/轮 | 缓存上限: {cache_limit} | GIF数: {gif_count} | 本轮更新: {updated} | 命中: {ratio:.1f}% | 图像缓存: {photo_cache} | 缩略图缓存: {thumb_cache} | 内存: {mem} | {drag}",
                mode=self.perf_mode_label(self.perf_mode_var.get()),
                load=self.load_profile_label(profile["load_name"]),
                strategy=self.tr(f"strategy.{profile['strategy']}", profile["strategy"]),
                budget=profile["frame_budget"],
                cache_limit=profile["cache_limit"],
                gif_count=gif_count,
                updated=updated_frames,
                ratio=ratio,
                photo_cache=photo_cache_entries,
                thumb_cache=len(self._thumb_photo_cache),
                mem=mem_text,
                drag=drag_text,
            )
        )

    def _process_mem_mb(self) -> float:
        try:
            import ctypes
            from ctypes import wintypes

            class PROCESS_MEMORY_COUNTERS(ctypes.Structure):
                _fields_ = [
                    ("cb", wintypes.DWORD),
                    ("PageFaultCount", wintypes.DWORD),
                    ("PeakWorkingSetSize", ctypes.c_size_t),
                    ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t),
                    ("PeakPagefileUsage", ctypes.c_size_t),
                ]

            counters = PROCESS_MEMORY_COUNTERS()
            counters.cb = ctypes.sizeof(counters)
            kernel32 = ctypes.windll.kernel32
            psapi = ctypes.windll.psapi
            handle = kernel32.GetCurrentProcess()
            ok = psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb)
            if ok:
                return float(counters.WorkingSetSize) / (1024 * 1024)
        except Exception:
            pass
        return -1.0

    def _on_group_list_press(self, evt: tk.Event) -> None:
        idx = self.group_list.nearest(evt.y)
        if 0 <= idx < len(self._group_order):
            self._drag_group_index = idx

    def _on_group_list_drag(self, evt: tk.Event) -> None:
        if self._drag_group_index is None:
            return
        src = self._drag_group_index
        dst = self.group_list.nearest(evt.y)
        if dst < 0 or dst >= len(self._group_order) or src == dst:
            return
        gid = self._group_order[src]
        target_gid = self._group_order[dst]
        if (gid in self._pinned_groups) != (target_gid in self._pinned_groups):
            return
        self._group_order.pop(src)
        self._group_order.insert(dst, gid)
        self._drag_group_index = dst
        self._refresh_list(select_gid=gid)
        self.mark_dirty()

    def _on_group_list_release(self, _evt: tk.Event) -> None:
        self._drag_group_index = None

    def _on_group_list_right_click(self, evt: tk.Event) -> None:
        idx = self.group_list.nearest(evt.y)
        if 0 <= idx < len(self._group_order):
            self.group_list.selection_clear(0, tk.END)
            self.group_list.selection_set(idx)
            self._active_group_id = self._group_order[idx]
            self._update_template_context_label()
        try:
            self.group_list_menu.tk_popup(evt.x_root, evt.y_root)
        finally:
            self.group_list_menu.grab_release()

    def _toggle_pin_selected_group(self) -> None:
        g = self._selected_group()
        if g is None:
            return
        if g.group_id in self._pinned_groups:
            self._pinned_groups.remove(g.group_id)
        else:
            self._pinned_groups.add(g.group_id)
        self._normalize_group_order()
        self._refresh_list(select_gid=g.group_id)
        self.mark_dirty()

    def _normalize_group_order(self) -> None:
        known = [gid for gid in self._group_order if gid in self.groups]
        for gid in self.groups:
            if gid not in known:
                known.append(gid)
        pinned = [gid for gid in known if gid in self._pinned_groups]
        normal = [gid for gid in known if gid not in self._pinned_groups]
        self._group_order = pinned + normal

    def _update_template_context_label(self) -> None:
        g = self._selected_group()
        if g is None:
            self.template_context_var.set(self.tr("template.context_none", "当前目标组：未选择"))
            return
        if g.template_path:
            self.template_context_var.set(self.tr("template.context_linked", "当前目标组：{name}（关联模板：{template}）", name=g.name, template=g.template_path.stem))
        else:
            self.template_context_var.set(self.tr("template.context_unlinked", "当前目标组：{name}（未关联模板）", name=g.name))

    def refresh_template_library(self) -> None:
        prev_selected_path: Optional[Path] = None
        if self.template_selected_idx is not None and 0 <= self.template_selected_idx < len(self.template_entries):
            prev_selected_path = self.template_entries[self.template_selected_idx]["path"]

        all_entries: list[dict] = []
        all_tags: set[str] = set()
        for p in sorted(TEMPLATE_DIR.glob("*.json"), key=lambda x: x.stat().st_mtime, reverse=True):
            try:
                data = json.loads(p.read_text(encoding="utf-8"))
            except Exception:
                continue
            raw_name = self._template_display_name(data, p.stem)
            preview = ""
            for img in data.get("images", []):
                if Path(img).is_file():
                    preview = img
                    break
            tags = [str(t).strip() for t in data.get("tags", []) if str(t).strip()]
            for t in tags:
                all_tags.add(t)
            all_entries.append(
                {
                    "path": p,
                    "name": raw_name,
                    "rows": int(data.get("rows", 2)),
                    "smart": bool(data.get("smart_layout", True)),
                    "count": len(data.get("images", [])),
                    "preview": preview,
                    "tags": tags,
                    "data": data,
                }
            )

        all_tag_label = self.tr("template.all", "全部")
        selected_tag = self.template_tag_var.get() if hasattr(self, "template_tag_var") else all_tag_label
        search = self.template_search_var.get().strip().lower() if hasattr(self, "template_search_var") else ""
        if hasattr(self, "template_tag_combo"):
            values = [all_tag_label] + sorted(all_tags)
            self.template_tag_combo.configure(values=values)
            if selected_tag not in values:
                selected_tag = all_tag_label
                self.template_tag_var.set(all_tag_label)

        self.template_entries = []
        for ent in all_entries:
            if selected_tag != all_tag_label and selected_tag not in ent["tags"]:
                continue
            if search:
                hay = f"{ent['name']} {' '.join(ent['tags'])} {ent['path'].stem}".lower()
                if search not in hay:
                    continue
            self.template_entries.append(ent)

        self.template_list.delete(0, tk.END)
        for ent in self.template_entries:
            mode = self.tr("template.mode_smart", "smart") if ent["smart"] else self.tr("template.mode_fixed", "fixed")
            tag_text = f" | tags={','.join(ent['tags'])}" if ent["tags"] else ""
            self.template_list.insert(
                tk.END, f"{ent['name']} | {mode} rows={ent['rows']} | {self.tr('template.images_short', 'images')}={ent['count']}{tag_text}"
            )
        if self.template_entries:
            pick_idx = 0
            if prev_selected_path is not None:
                for i, ent in enumerate(self.template_entries):
                    if ent["path"] == prev_selected_path:
                        pick_idx = i
                        break
            self.template_list.selection_set(pick_idx)
            self.template_selected_idx = pick_idx
        else:
            self.template_selected_idx = None
        self._render_template_icons()

    def _on_template_list_selected(self, _evt: tk.Event) -> None:
        sel = self.template_list.curselection()
        if not sel:
            return
        self.pause_heavy_work(0.8)
        self.template_selected_idx = sel[0]
        self._update_template_icon_selection_visuals()

    def _render_template_icons(self) -> None:
        if not hasattr(self, "template_canvas"):
            return
        c = self.template_canvas
        c.delete("all")
        self.template_icon_cells.clear()
        self.template_icon_outline_ids.clear()
        self.template_thumbs.clear()
        self._thumb_render_token += 1
        token = self._thumb_render_token

        width = max(320, c.winfo_width() if c.winfo_width() > 1 else 640)
        card_w = 170
        card_h = 206
        pad = 12
        cols = max(1, width // (card_w + pad))
        thumb_tasks: list[tuple[int, str, int, int]] = []

        for idx, ent in enumerate(self.template_entries):
            row = idx // cols
            col = idx % cols
            x0 = pad + col * (card_w + pad)
            y0 = pad + row * (card_h + pad)
            x1 = x0 + card_w
            y1 = y0 + card_h
            self.template_icon_cells.append((x0, y0, x1, y1))

            outline = "#4cc9f0" if idx == self.template_selected_idx else "#2c2c2c"
            outline_id = c.create_rectangle(x0, y0, x1, y1, outline=outline, width=2)
            self.template_icon_outline_ids.append(outline_id)

            preview = ent["preview"]
            if preview and Path(preview).is_file():
                image_id = c.create_text(x0 + card_w // 2, y0 + 54, text=self.tr("template.loading_preview", "加载中..."), fill="#9a9a9a")
                thumb_tasks.append((idx, preview, image_id, x0 + card_w // 2))
            else:
                c.create_text(x0 + card_w // 2, y0 + 54, text=self.tr("template.no_preview", "No Preview"), fill="#9a9a9a")

            c.create_text(
                x0 + 8,
                y0 + 116,
                text=ent["name"],
                fill="#dddddd",
                anchor="nw",
                width=card_w - 16,
            )
            mode = self.tr("template.mode_smart", "smart") if ent["smart"] else self.tr("template.mode_fixed", "fixed")
            c.create_text(
                x0 + 8,
                y0 + 156,
                text=f"{mode} rows={ent['rows']}\n{ent['count']} {self.tr('template.imgs_short', 'imgs')}",
                fill="#9a9a9a",
                anchor="nw",
                width=card_w - 16,
            )

        total_rows = math.ceil(len(self.template_entries) / cols) if cols else 0
        total_h = pad + total_rows * (card_h + pad)
        c.configure(scrollregion=(0, 0, width, total_h))
        self._render_thumb_batch(thumb_tasks, token, 0)

    def _thumb_cache_file(self, preview_path: str, w: int, h: int) -> Path:
        p = Path(preview_path)
        stat = p.stat()
        key = f"{p.resolve()}|{stat.st_mtime_ns}|{stat.st_size}|{w}x{h}"
        digest = hashlib.md5(key.encode("utf-8", errors="ignore")).hexdigest()
        return THUMB_CACHE_DIR / f"{digest}.jpg"

    def _get_or_build_thumb(self, preview_path: str, w: int, h: int) -> Optional[ImageTk.PhotoImage]:
        cache_file = self._thumb_cache_file(preview_path, w, h)
        cache_key = str(cache_file)
        cached = self._thumb_photo_cache.get(cache_key)
        if cached is not None:
            self._thumb_photo_cache.move_to_end(cache_key)
            return cached

        try:
            if not cache_file.exists():
                src = Image.open(preview_path).convert("RGB")
                src.thumbnail((w, h), Image.Resampling.LANCZOS)
                cache_file.parent.mkdir(parents=True, exist_ok=True)
                src.save(cache_file, format="JPEG", quality=88, optimize=True)

            img = Image.open(cache_file).convert("RGB")
            tk_img = ImageTk.PhotoImage(img)
            self._thumb_photo_cache[cache_key] = tk_img
            while len(self._thumb_photo_cache) > THUMB_CACHE_LIMIT:
                self._thumb_photo_cache.popitem(last=False)
            return tk_img
        except Exception:
            return None

    def _render_thumb_batch(
        self,
        tasks: list[tuple[int, str, int, int]],
        token: int,
        start: int,
        batch: int = 12,
    ) -> None:
        if token != self._thumb_render_token:
            return
        if not hasattr(self, "template_canvas"):
            return
        c = self.template_canvas
        end = min(len(tasks), start + batch)
        for i in range(start, end):
            _idx, preview, text_item_id, center_x = tasks[i]
            tk_img = self._get_or_build_thumb(preview, 156, 96)
            if tk_img is None:
                c.itemconfigure(text_item_id, text=self.tr("template.no_preview", "No Preview"))
                continue
            self.template_thumbs.append(tk_img)
            x, y = c.coords(text_item_id)
            c.delete(text_item_id)
            c.create_image(center_x, y, image=tk_img)

        if end < len(tasks):
            self.root.after(1, lambda: self._render_thumb_batch(tasks, token, end, batch))

    def _update_template_icon_selection_visuals(self) -> None:
        if not hasattr(self, "template_canvas"):
            return
        if len(self.template_icon_outline_ids) != len(self.template_entries):
            return
        for idx, item_id in enumerate(self.template_icon_outline_ids):
            outline = "#4cc9f0" if idx == self.template_selected_idx else "#2c2c2c"
            try:
                self.template_canvas.itemconfigure(item_id, outline=outline)
            except Exception:
                pass

    def _on_template_icon_click(self, evt: tk.Event) -> None:
        x = self.template_canvas.canvasx(evt.x)
        y = self.template_canvas.canvasy(evt.y)
        for idx, (x0, y0, x1, y1) in enumerate(self.template_icon_cells):
            if x0 <= x <= x1 and y0 <= y <= y1:
                self.pause_heavy_work(0.8)
                self.template_selected_idx = idx
                self.template_list.selection_clear(0, tk.END)
                self.template_list.selection_set(idx)
                self.template_list.see(idx)
                self._update_template_icon_selection_visuals()
                return

    def _selected_template_entry(self) -> Optional[dict]:
        if self.template_selected_idx is None:
            return None
        if 0 <= self.template_selected_idx < len(self.template_entries):
            return self.template_entries[self.template_selected_idx]
        return None

    def _build_history_tab(self, history_tab: ttk.Frame) -> None:
        top = ttk.Frame(history_tab)
        top.pack(fill=tk.X)
        self.history_refresh_btn = ttk.Button(top, text=self.tr("button.refresh_history", "刷新历史"), command=self.refresh_history_library)
        self.history_refresh_btn.pack(side=tk.LEFT)
        self.history_open_btn = ttk.Button(top, text=self.tr("button.open_selected_history", "打开所选历史"), command=self.open_selected_history)
        self.history_open_btn.pack(side=tk.LEFT, padx=8)

        body = ttk.Frame(history_tab)
        body.pack(fill=tk.BOTH, expand=True, pady=(8, 0))
        self.history_list = tk.Listbox(body)
        self.history_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.history_list.bind("<Double-Button-1>", lambda _e: self.open_selected_history())
        scr = ttk.Scrollbar(body, orient=tk.VERTICAL, command=self.history_list.yview)
        scr.pack(side=tk.RIGHT, fill=tk.Y)
        self.history_list.configure(yscrollcommand=scr.set)
        self.history_entries: list[Path] = []

    def refresh_history_library(self) -> None:
        if not hasattr(self, "history_list"):
            return
        self.history_list.delete(0, tk.END)
        self.history_entries = []

        if SESSION_FILE.exists():
            ts = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(SESSION_FILE.stat().st_mtime))
            self.history_list.insert(tk.END, self.tr("history.latest_session", "[最新自动会话] session.json ({ts})", ts=ts))
            self.history_entries.append(SESSION_FILE)

        for p in sorted(HISTORY_DIR.glob("session_*.json"), key=lambda x: x.stat().st_mtime, reverse=True):
            ts = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(p.stat().st_mtime))
            self.history_list.insert(tk.END, f"{p.name} ({ts})")
            self.history_entries.append(p)

        if self.history_entries:
            self.history_list.selection_set(0)

    def open_selected_history(self) -> None:
        if not hasattr(self, "history_list"):
            return
        sel = self.history_list.curselection()
        if not sel:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_history_first", "请先选择一条历史记录。"))
            return
        p = self.history_entries[sel[0]]
        if self.groups:
            ok = messagebox.askyesno(self.tr("msg.restore_session", "恢复会话"), self.tr("msg.restore_session_confirm", "恢复会话会替换当前窗口组，是否继续？"))
            if not ok:
                return
        self.load_session(path=p, silent=False, replace_existing=True)

    def _choose_from_entries(self, title: str, entries: list[tuple[str, Path]]) -> Optional[Path]:
        if not entries:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.no_records", "当前没有可用记录。"))
            return None

        result: dict[str, Optional[Path]] = {"path": None}
        win = tk.Toplevel(self.root)
        win.title(title)
        win.geometry("560x420")
        win.transient(self.root)
        win.grab_set()

        ttk.Label(win, text=title, font=("Microsoft YaHei UI", 11, "bold")).pack(
            anchor="w", padx=12, pady=(12, 8)
        )

        frame = ttk.Frame(win)
        frame.pack(fill=tk.BOTH, expand=True, padx=12)

        lb = tk.Listbox(frame)
        lb.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sc = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=lb.yview)
        sc.pack(side=tk.RIGHT, fill=tk.Y)
        lb.configure(yscrollcommand=sc.set)

        for label, _ in entries:
            lb.insert(tk.END, label)
        lb.selection_set(0)

        def _open_selected() -> None:
            sel = lb.curselection()
            if not sel:
                return
            result["path"] = entries[sel[0]][1]
            win.destroy()

        lb.bind("<Double-Button-1>", lambda _e: _open_selected())

        btns = ttk.Frame(win)
        btns.pack(fill=tk.X, padx=12, pady=12)
        ttk.Button(btns, text=self.tr("button.open", "打开"), command=_open_selected).pack(side=tk.LEFT)
        ttk.Button(btns, text=self.tr("button.cancel", "取消"), command=win.destroy).pack(side=tk.RIGHT)

        self.root.wait_window(win)
        return result["path"]

    def _prompt_template_meta(
        self,
        title: str,
        default_name: str,
        default_tags: Optional[list[str]] = None,
        parent: Optional[tk.Misc] = None,
    ) -> Optional[tuple[str, list[str]]]:
        result: dict[str, Optional[tuple[str, list[str]]]] = {"value": None}
        self._begin_modal_block()
        self.root.update_idletasks()
        dialog_parent = parent or self.root
        win = tk.Toplevel(dialog_parent)
        self.apply_window_icon(win)
        win.title(title)
        self._show_dialog_window(win, dialog_parent)
        win.grab_set()

        body = ttk.Frame(win, padding=16)
        body.pack(fill=tk.BOTH, expand=True)
        ttk.Label(body, text=title, font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w", pady=(0, 10))

        ttk.Label(body, text=self.tr("template.name", "模板名称")).pack(anchor="w")
        name_var = tk.StringVar(value=default_name)
        name_entry = ttk.Entry(body, textvariable=name_var, width=40)
        name_entry.pack(fill=tk.X, pady=(4, 10))

        ttk.Label(body, text=self.tr("template.tags_hint", "分类 / 标签（逗号分隔，可留空）")).pack(anchor="w")
        tags_var = tk.StringVar(value=",".join(default_tags or []))
        tags_entry = ttk.Entry(body, textvariable=tags_var, width=40)
        tags_entry.pack(fill=tk.X, pady=(4, 0))

        def _confirm() -> None:
            name = name_var.get().strip()
            if not name:
                messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.template_name_required", "模板名称不能为空。"), parent=win)
                return
            result["value"] = (name, self._parse_tags(tags_var.get()))
            win.destroy()

        ttk.Label(body, text=self.tr("template.tags_empty_hint", "留空表示不分类。"), foreground="#9da5b4").pack(anchor="w", pady=(10, 0))

        btns = ttk.Frame(win, padding=(16, 0, 16, 16))
        btns.pack(fill=tk.X, side=tk.BOTTOM)
        ttk.Button(btns, text=self.tr("button.confirm", "确定"), command=_confirm).pack(side=tk.LEFT)
        ttk.Button(btns, text=self.tr("button.cancel", "取消"), command=win.destroy).pack(side=tk.RIGHT)

        win.update_idletasks()
        req_w = max(560, win.winfo_reqwidth() + 24)
        req_h = max(340, win.winfo_reqheight() + 24)
        self._center_window(win, req_w, req_h)
        win.minsize(req_w, req_h)

        name_entry.focus_set()
        name_entry.selection_range(0, tk.END)
        win.bind("<Return>", lambda _e: _confirm())
        try:
            self.root.wait_window(win)
        finally:
            self._end_modal_block()
        return result["value"]

    def _create_group(
        self,
        name: str,
        rows: int,
        smart_layout: bool,
        layout_algorithm: str = "legacy",
        image_paths: Optional[list[Path]] = None,
        geometry: Optional[str] = None,
        template_path: Optional[Path] = None,
        mark_dirty: bool = True,
    ) -> GroupWindow:
        if self._free_group_ids:
            gid = min(self._free_group_ids)
            self._free_group_ids.remove(gid)
        else:
            gid = self._next_group_id
            self._next_group_id += 1

        group = GroupWindow(
            self,
            gid,
            name,
            rows,
            smart_layout,
            layout_algorithm=layout_algorithm,
            template_path=template_path,
        )
        self.groups[gid] = group
        if gid not in self._group_order:
            self._group_order.append(gid)
        self._normalize_group_order()

        if geometry:
            try:
                group.top.geometry(geometry)
            except Exception:
                pass

        if image_paths:
            self.add_paths_to_group(group, image_paths, show_errors=False)

        self._refresh_list(select_gid=gid)
        if mark_dirty:
            self.mark_dirty()
        return group

    def create_group(self) -> None:
        name = self.group_name_var.get().strip() or self._default_group_name()
        rows = max(1, int(self.rows_var.get() or 1))
        smart_layout = bool(self.smart_layout_var.get())
        layout_algorithm = self._layout_algo_key_from_var()
        self._create_group(name, rows, smart_layout, layout_algorithm=layout_algorithm)

    def _refresh_list(self, select_gid: Optional[int] = None) -> None:
        current = self._selected_group()
        target_gid = select_gid if select_gid is not None else (current.group_id if current else None)

        self._normalize_group_order()
        self.group_list.delete(0, tk.END)
        for gid in self._group_order:
            if gid not in self.groups:
                continue
            g = self.groups[gid]
            mode = self.tr("list.layout_smart", "smart") if g.smart_layout else self.tr("list.layout_fixed", "fixed")
            algo = f" | {self.tr('list.algorithm', 'algo')}={self.tr(f'layout.{g.layout_algorithm}', LAYOUT_ALGORITHMS.get(g.layout_algorithm, '算法1'))}" if g.smart_layout else ""
            tpl = " | tpl" if g.template_path else ""
            pin = " [PIN]" if gid in self._pinned_groups else ""
            self.group_list.insert(
                tk.END,
                f"{gid}# {g.name}{pin} | {self.tr('list.layout', 'layout')}={mode} rows={g.rows}{algo} | {self.tr('list.images', 'images')}={len(g.items)}{tpl}",
            )

        if target_gid is not None and target_gid in self._group_order:
            idx = self._group_order.index(target_gid)
            self.group_list.selection_clear(0, tk.END)
            self.group_list.selection_set(idx)
            self._active_group_id = target_gid
        self._update_template_context_label()

    def _on_group_selected(self, _evt: tk.Event) -> None:
        g = self._selected_group()
        if not g:
            self._update_template_context_label()
            return
        self._active_group_id = g.group_id
        self.rows_var.set(g.rows)
        self.smart_layout_var.set(g.smart_layout)
        self._sync_layout_algo_value(g.layout_algorithm)
        self.group_name_var.set(g.name)
        if g.template_path:
            for i, ent in enumerate(self.template_entries):
                if ent["path"] == g.template_path:
                    self.template_selected_idx = i
                    self.template_list.selection_clear(0, tk.END)
                    self.template_list.selection_set(i)
                    self.template_list.see(i)
                    self._render_template_icons()
                    break
        self._update_template_context_label()

    def add_images(self) -> None:
        g = self._selected_group()
        if not g:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_group_in_list", "请先在列表里选择一个窗口组。"))
            return

        paths = filedialog.askopenfilenames(
            title=self.tr("dialog.choose_images", "选择图片"),
            filetypes=[
                (self.tr("dialog.image_files", "图片"), "*.png *.jpg *.jpeg *.gif *.bmp *.webp"),
                (self.tr("dialog.all_files", "所有文件"), "*.*"),
            ],
        )
        if not paths:
            return

        normalized = self._collect_supported_paths(paths)
        if not normalized:
            messagebox.showwarning(self.tr("msg.notice", "提示"), self.tr("msg.no_supported_images_selected", "没有选中受支持的图片类型。"))
            return

        self.add_paths_to_group(g, normalized, apply_batch_order=True)

    def _apply_layout_to_group(self, g: GroupWindow) -> None:
        rows = max(1, int(self.rows_var.get() or 1))
        smart = bool(self.smart_layout_var.get())
        layout_algorithm = self._layout_algo_key_from_var()
        new_name = self.group_name_var.get().strip() or g.name
        g.name = new_name
        g._update_title()
        g.set_layout(rows, smart, layout_algorithm=layout_algorithm)
        self._refresh_list(select_gid=g.group_id)

    def update_layout(self) -> None:
        g = self._selected_group()
        if not g:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_group_in_list", "请先在列表里选择一个窗口组。"))
            return

        self._apply_layout_to_group(g)

    def focus_group(self) -> None:
        g = self._selected_group()
        if not g:
            return
        g.top.deiconify()
        g.top.lift()
        g.top.focus_force()

    def close_group(self) -> None:
        g = self._selected_group()
        if not g:
            return
        gid = g.group_id
        self.persist_template_geometry(g)
        g.top.destroy()
        self.unregister_group(gid)

    def unregister_group(self, gid: int) -> None:
        if gid in self.groups:
            self.groups.pop(gid, None)
            self._free_group_ids.add(gid)
            if gid in self._group_order:
                self._group_order.remove(gid)
            self._pinned_groups.discard(gid)
            if self._active_group_id == gid:
                self._active_group_id = None
            self.mark_dirty()
            self._refresh_list()

    def save_group_template(self, group: Optional[GroupWindow] = None) -> None:
        self.pause_heavy_work(1.5)
        g = group or self._selected_group()
        dialog_parent = self._dialog_parent(g)
        if not g:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_group_first", "请先选择一个窗口组。"), parent=dialog_parent)
            return

        default_name = g.name
        existing_tags: list[str] = []
        if g.template_path and g.template_path.exists():
            try:
                existing = json.loads(g.template_path.read_text(encoding="utf-8"))
                existing_tags = list(existing.get("tags", []))
            except Exception:
                existing_tags = []

        meta = self._prompt_template_meta(self.tr("dialog.save_template", "保存模板"), default_name, existing_tags, parent=dialog_parent)
        if not meta:
            return
        name, tags = meta

        data = g.to_state()
        data["template_name"] = name
        data["tags"] = tags
        file_path = TEMPLATE_DIR / self._safe_template_filename(name)
        current_path = g.template_path.resolve() if g.template_path and g.template_path.exists() else None
        if file_path.exists() and file_path.resolve() != current_path:
            messagebox.showwarning(self.tr("msg.notice", "提示"), self.tr("msg.template_name_exists", "同名模板已存在，请换一个模板名称。"), parent=dialog_parent)
            return
        try:
            file_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            g.template_path = file_path
            self.refresh_template_library()
            messagebox.showinfo(self.tr("msg.done", "完成"), self.tr("msg.template_saved", "模板已保存:\n{name}", name=file_path.name), parent=dialog_parent)
        except Exception as exc:
            messagebox.showerror(self.tr("msg.save_failed", "保存失败"), str(exc), parent=dialog_parent)

    def persist_template_geometry(self, g: GroupWindow) -> None:
        if g.suppress_template_geometry_persist:
            return
        if not g.template_path or not g.template_path.exists():
            return
        key = str(g.template_path.resolve())
        self._template_geometry_map[key] = g.top.geometry()

    def load_group_template(self) -> None:
        self.pause_heavy_work(1.2)
        ent = self._selected_template_entry()
        if ent is None:
            self.refresh_template_library()
            ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_template_first", "请先在模板库中选择一个模板。"))
            return

        data = ent["data"]
        picked = ent["path"]
        name = self._template_display_name(data, ent["name"])
        rows = max(1, int(data.get("rows", 2)))
        smart = bool(data.get("smart_layout", True))
        layout_algorithm = str(data.get("layout_algorithm", "legacy")).strip() or "legacy"
        geometry = data.get("geometry")
        key = str(picked.resolve())
        if key in self._template_geometry_map:
            geometry = self._template_geometry_map[key]
        image_paths = [Path(p) for p in data.get("images", []) if Path(p).is_file()]
        self._create_group(
            name,
            rows,
            smart,
            layout_algorithm=layout_algorithm,
            image_paths=image_paths,
            geometry=geometry,
            template_path=picked,
        )

    def update_linked_template(self, group: Optional[GroupWindow] = None) -> None:
        self.pause_heavy_work(1.2)
        g = group or self._selected_group()
        dialog_parent = self._dialog_parent(g)
        if g is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_target_group_first", "请先选择一个目标窗口组。"), parent=dialog_parent)
            return
        if not g.template_path:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.group_not_linked_template", "当前组没有关联模板，请先“保存为模板”。"), parent=dialog_parent)
            return

        current_template_name = g.template_path.stem
        ent = next((e for e in self.template_entries if e["path"] == g.template_path), None)
        if ent:
            current_template_name = ent["name"]
            tags = ent.get("tags", [])
        else:
            tags = []

        data = g.to_state()
        data["template_name"] = current_template_name
        data["tags"] = tags
        try:
            g.template_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            self.refresh_template_library()
            messagebox.showinfo(self.tr("msg.done", "完成"), self.tr("msg.template_updated", "已更新模板: {name}", name=g.template_path.name), parent=dialog_parent)
        except Exception as exc:
            messagebox.showerror(self.tr("msg.update_failed", "更新失败"), str(exc), parent=dialog_parent)

    def reload_linked_template(self, group: Optional[GroupWindow] = None) -> None:
        self.pause_heavy_work(1.2)
        g = group or self._selected_group()
        if g is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_target_group_first", "请先选择一个目标窗口组。"))
            return
        if not g.template_path or not g.template_path.exists():
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.group_no_available_template", "当前组没有可用的关联模板。"))
            return

        try:
            data = json.loads(g.template_path.read_text(encoding="utf-8"))
        except Exception as exc:
            messagebox.showerror(self.tr("msg.read_failed", "读取失败"), str(exc))
            return

        g.name = self._template_display_name(data, g.template_path.stem)
        g._update_title()
        rows = max(1, int(data.get("rows", g.rows)))
        smart = bool(data.get("smart_layout", g.smart_layout))
        layout_algorithm = str(data.get("layout_algorithm", g.layout_algorithm)).strip() or "legacy"
        g.rows = rows
        g.smart_layout = smart
        g.layout_algorithm = layout_algorithm if layout_algorithm in LAYOUT_ALGORITHMS else "legacy"
        g.items = []
        image_paths = [Path(p) for p in data.get("images", []) if Path(p).is_file()]
        g.add_paths(image_paths, show_errors=False)
        g.render(force=True)
        self._refresh_list(select_gid=g.group_id)

    def rename_selected_template(self) -> None:
        self.pause_heavy_work(1.2)
        ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_template_first", "请先在模板库中选择一个模板。"))
            return

        old_name = ent["name"]
        new_name = simpledialog.askstring(self.tr("dialog.rename_template", "重命名模板"), self.tr("dialog.new_template_name", "新模板名称:"), initialvalue=old_name)
        if not new_name:
            return
        new_name = new_name.strip()
        if not new_name:
            return

        old_path: Path = ent["path"]
        new_path = TEMPLATE_DIR / self._safe_template_filename(new_name)
        if new_path.exists() and new_path != old_path:
            messagebox.showwarning(self.tr("msg.notice", "提示"), self.tr("msg.template_name_exists_rename", "同名模板已存在，请换一个名称。"))
            return

        try:
            data = json.loads(old_path.read_text(encoding="utf-8"))
        except Exception as exc:
            messagebox.showerror(self.tr("msg.read_failed", "读取失败"), str(exc))
            return

        data["template_name"] = new_name
        try:
            new_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            if new_path != old_path:
                old_path.unlink(missing_ok=True)
            old_key = str(old_path.resolve())
            new_key = str(new_path.resolve())
            if old_key in self._template_geometry_map:
                self._template_geometry_map[new_key] = self._template_geometry_map.pop(old_key)
            for g in self.groups.values():
                if g.template_path == old_path:
                    g.template_path = new_path
            self.refresh_template_library()
            messagebox.showinfo(self.tr("msg.done", "完成"), self.tr("msg.template_renamed", "模板已重命名为: {name}", name=new_name))
        except Exception as exc:
            messagebox.showerror(self.tr("msg.rename_failed", "重命名失败"), str(exc))

    def _parse_tags(self, text: str) -> list[str]:
        out: list[str] = []
        for token in text.replace("，", ",").split(","):
            t = token.strip()
            if t and t not in out:
                out.append(t)
        return out

    def edit_selected_template_tags(self) -> None:
        self.pause_heavy_work(1.2)
        ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_template_first", "请先在模板库中选择一个模板。"))
            return
        old_tags = ent.get("tags", [])
        text = simpledialog.askstring(
            self.tr("dialog.edit_tags", "编辑标签"),
            self.tr("dialog.tags_prompt", "标签（逗号分隔）:"),
            initialvalue=",".join(old_tags),
        )
        if text is None:
            return
        tags = self._parse_tags(text)
        p: Path = ent["path"]
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
            data["tags"] = tags
            p.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            self.refresh_template_library()
        except Exception as exc:
            messagebox.showerror(self.tr("msg.tag_update_failed", "标签更新失败"), str(exc))

    def delete_selected_template(self) -> None:
        self.pause_heavy_work(1.2)
        ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_template_first", "请先在模板库中选择一个模板。"))
            return

        p: Path = ent["path"]
        display_name = ent["name"]
        ok = messagebox.askyesno(self.tr("dialog.delete_template", "删除模板"), self.tr("msg.delete_template_confirm", "确定删除模板“{name}”吗？\n\n此操作不会删除原始图片文件。", name=display_name))
        if not ok:
            return

        try:
            p.unlink(missing_ok=True)
            key = str(p.resolve())
            self._template_geometry_map.pop(key, None)
            for g in self.groups.values():
                if g.template_path == p:
                    g.template_path = None
            self.template_selected_idx = None
            self.refresh_template_library()
        except Exception as exc:
            messagebox.showerror(self.tr("msg.delete_failed", "删除失败"), str(exc))

    def _session_payload(self) -> dict:
        ordered_existing = [gid for gid in self._group_order if gid in self.groups]
        return {
            "version": 1,
            "saved_at": int(time.time()),
            "groups": [self.groups[gid].to_state() for gid in ordered_existing],
        }

    def _write_history_snapshot(self, payload: dict) -> None:
        groups = payload.get("groups", [])
        if not groups:
            return
        stamp = time.strftime("%Y%m%d_%H%M%S", time.localtime())
        snap = HISTORY_DIR / f"session_{stamp}.json"
        snap.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")

        snaps = sorted(HISTORY_DIR.glob("session_*.json"), key=lambda p: p.stat().st_mtime, reverse=True)
        for old in snaps[50:]:
            try:
                old.unlink()
            except Exception:
                pass

    def save_session(self, silent: bool = False, snapshot: bool = False) -> None:
        try:
            payload = self._session_payload()
            SESSION_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
            if snapshot:
                self._write_history_snapshot(payload)
            self.refresh_history_library()
            self._dirty = False
            self._last_save_ts = time.time()
            if not silent:
                messagebox.showinfo(self.tr("msg.done", "完成"), self.tr("msg.session_saved", "会话已保存。"))
        except Exception as exc:
            if not silent:
                messagebox.showerror(self.tr("msg.save_failed", "保存失败"), str(exc))

    def save_session_snapshot(self) -> None:
        self.save_session(silent=False, snapshot=True)

    def _close_all_groups(self) -> None:
        for gid in list(self.groups.keys()):
            g = self.groups.get(gid)
            if g is None:
                continue
            g.suppress_template_geometry_persist = True
            try:
                g.top.destroy()
            except Exception:
                pass
            self.groups.pop(gid, None)
        self._group_order = []
        self._pinned_groups.clear()
        self._active_group_id = None
        self._free_group_ids.clear()
        self._next_group_id = 1
        self._refresh_list()

    def load_session_button(self) -> None:
        # 兼容旧入口：直接跳转到历史记录页签。
        self.notebook.select(2)
        self.refresh_history_library()

    def load_session(
        self, path: Optional[Path] = None, silent: bool = True, replace_existing: bool = False
    ) -> None:
        src = path or SESSION_FILE
        if not src.exists():
            if not silent:
                messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.no_session_file", "当前没有可恢复的会话文件。"))
            return

        try:
            payload = json.loads(src.read_text(encoding="utf-8"))
        except Exception as exc:
            if not silent:
                messagebox.showerror(self.tr("msg.read_failed", "读取失败"), str(exc))
            return

        groups = payload.get("groups", [])
        if not isinstance(groups, list):
            if not silent:
                messagebox.showerror(self.tr("msg.read_failed", "读取失败"), self.tr("msg.invalid_session_format", "会话格式不正确。"))
            return
        if not groups:
            if not silent:
                messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.empty_history_session", "这条记录里没有窗口组可恢复。"))
            return

        self._suspend_dirty = True
        try:
            if replace_existing and self.groups:
                self._close_all_groups()

            for item in groups:
                name = str(item.get("name", self._default_group_name())).strip() or self._default_group_name()
                rows = max(1, int(item.get("rows", 2)))
                smart = bool(item.get("smart_layout", True))
                layout_algorithm = str(item.get("layout_algorithm", "legacy")).strip() or "legacy"
                geometry = item.get("geometry")
                template_path_raw = str(item.get("template_path", "")).strip()
                template_path = Path(template_path_raw) if template_path_raw else None
                if template_path and not template_path.exists():
                    template_path = None
                image_paths = [Path(p) for p in item.get("images", []) if Path(p).is_file()]
                created = self._create_group(
                    name,
                    rows,
                    smart,
                    layout_algorithm=layout_algorithm,
                    image_paths=image_paths,
                    geometry=geometry,
                    template_path=template_path,
                    mark_dirty=False,
                )
                if bool(item.get("pinned", False)):
                    self._pinned_groups.add(created.group_id)
            self._normalize_group_order()
        finally:
            self._suspend_dirty = False

        self._dirty = False
        if not silent:
            messagebox.showinfo(self.tr("msg.done", "完成"), self.tr("msg.session_restored", "会话恢复完成。"))

    def _choose_merge_sources(self, target_gid: int) -> list[int]:
        others = [gid for gid in self._group_order if gid != target_gid and gid in self.groups]
        if not others:
            return []

        result: dict[str, list[int]] = {"gids": []}
        win = tk.Toplevel(self.root)
        self.apply_window_icon(win)
        win.title(self.tr("dialog.choose_merge_groups", "选择要合并的窗口组"))
        self._center_window(win, 520, 400)
        win.transient(self.root)
        win.grab_set()

        ttk.Label(win, text=self.tr("merge.choose_title", "选择要并入当前目标组的窗口组"), font=("Microsoft YaHei UI", 11, "bold")).pack(
            anchor="w", padx=12, pady=(12, 4)
        )
        ttk.Label(win, text=self.tr("merge.choose_hint", "按列表顺序合并，源窗口会被关闭，组内图片顺序会保持不变。")).pack(
            anchor="w", padx=12, pady=(0, 8)
        )

        frame = ttk.Frame(win)
        frame.pack(fill=tk.BOTH, expand=True, padx=12)
        lb = tk.Listbox(frame, selectmode=tk.EXTENDED, activestyle="dotbox")
        lb.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sc = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=lb.yview)
        sc.pack(side=tk.RIGHT, fill=tk.Y)
        lb.configure(yscrollcommand=sc.set)
        for gid in others:
            g = self.groups[gid]
            lb.insert(tk.END, f"{gid}# {g.name} | images={len(g.items)}")
        if others:
            lb.selection_set(0)

        def _ok() -> None:
            sel = lb.curselection()
            result["gids"] = [others[i] for i in sel]
            win.destroy()

        lb.bind("<Double-Button-1>", lambda _e: _ok())
        lb.bind("<Return>", lambda _e: _ok())
        btns = ttk.Frame(win)
        btns.pack(fill=tk.X, padx=12, pady=12)
        ttk.Button(btns, text=self.tr("button.merge", "合并"), command=_ok).pack(side=tk.LEFT)
        ttk.Button(btns, text=self.tr("button.cancel", "取消"), command=win.destroy).pack(side=tk.RIGHT)

        lb.focus_set()
        self.root.wait_window(win)
        return result["gids"]

    def merge_groups(self) -> None:
        target = self._selected_group()
        if target is None:
            messagebox.showinfo(self.tr("msg.notice", "提示"), self.tr("msg.select_target_group_in_list", "请先在列表中选择目标窗口组。"))
            return

        source_gids = self._choose_merge_sources(target.group_id)
        if not source_gids:
            return

        for gid in source_gids:
            src = self.groups.get(gid)
            if src is None:
                continue
            target.items.extend(src.items)
            src.items = []
            src.suppress_template_geometry_persist = True
            try:
                src.top.destroy()
            except Exception:
                pass
            self.groups.pop(gid, None)
            if gid in self._group_order:
                self._group_order.remove(gid)
            self._pinned_groups.discard(gid)
            self._free_group_ids.add(gid)

        target.render(force=True)
        self.mark_dirty()
        self._refresh_list(select_gid=target.group_id)

    def _on_app_close(self) -> None:
        for g in list(self.groups.values()):
            self.persist_template_geometry(g)
        if self._dirty:
            self.save_session(silent=True, snapshot=True)
        self._save_ui_state()
        self.root.destroy()

    def _schedule_tick(self) -> None:
        self._drain_drop_queue()

        now = time.time()
        profile = self.current_profile()
        updated_total = 0
        if not self.heavy_work_paused():
            groups_with_gifs = [(g, g.gif_item_count()) for g in list(self.groups.values())]
            groups_with_gifs = [(g, gif_count) for g, gif_count in groups_with_gifs if gif_count > 0]
            remaining_budget = int(profile["frame_budget"])
            remaining_weight = sum(gif_count for _, gif_count in groups_with_gifs)
            tick_start = time.perf_counter()
            max_gif_count = max((gif_count for _, gif_count in groups_with_gifs), default=0)
            global_time_budget_ms = 8.0 if max_gif_count >= 45 else 12.0
            for idx, (g, gif_count) in enumerate(groups_with_gifs):
                if remaining_budget <= 0 or remaining_weight <= 0:
                    break
                if (time.perf_counter() - tick_start) * 1000 >= global_time_budget_ms:
                    break
                if idx == len(groups_with_gifs) - 1:
                    allocation = remaining_budget
                else:
                    allocation = max(1, int(round(remaining_budget * gif_count / remaining_weight)))
                group_time_budget_ms = 3.5 if gif_count >= 45 else 5.0 if gif_count >= 25 else 7.0
                used = g.tick_gif(now, frame_budget=allocation, time_budget_ms=group_time_budget_ms)
                updated_total += used
                remaining_budget -= used
                remaining_weight -= gif_count
        self._last_tick_updated = updated_total
        self._update_status(updated_total, now)

        if self._dirty and now - self._last_save_ts > 3.0:
            self.save_session(silent=True, snapshot=False)

        self.root.after(int(profile["tick_ms"]), self._schedule_tick)

    def run(self) -> None:
        self.root.mainloop()


if __name__ == "__main__":
    app = PicReadApp()
    app.run()
