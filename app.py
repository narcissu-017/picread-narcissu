from __future__ import annotations

import ast
import ctypes
import hashlib
import json
import math
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

SUPPORTED_EXTS = {".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp"}
if getattr(sys, "frozen", False):
    APP_DIR = Path(sys.executable).resolve().parent
else:
    APP_DIR = Path(__file__).resolve().parent
STATE_DIR = APP_DIR / "state"
TEMPLATE_DIR = STATE_DIR / "templates"
HISTORY_DIR = STATE_DIR / "history"
THUMB_CACHE_DIR = STATE_DIR / "thumbs"
SESSION_FILE = STATE_DIR / "session.json"
UI_STATE_FILE = STATE_DIR / "ui_state.json"
CACHE_LIMIT = 2200
THUMB_CACHE_LIMIT = 280
ICON_ICO_PATH = APP_DIR / "assets" / "picread_icon.ico"
ICON_PNG_PATH = APP_DIR / "assets" / "picread_icon.png"
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
}
RESAMPLE_NAME_TO_VALUE = {
    "LANCZOS": Image.Resampling.LANCZOS,
    "BICUBIC": Image.Resampling.BICUBIC,
    "BILINEAR": Image.Resampling.BILINEAR,
}
RESAMPLE_VALUE_TO_NAME = {v: k for k, v in RESAMPLE_NAME_TO_VALUE.items()}


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
        self._slot_draw_sizes: list[tuple[int, int]] = []
        self._cell_lookup_rects: list[tuple[int, int, int, int]] = []

        self._drag_source_idx: Optional[int] = None
        self._drag_target_idx: Optional[int] = None
        self._drag_active = False
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

        self._menu = tk.Menu(self.top, tearoff=0)
        self._menu.add_command(label="从窗口组移除图片", command=self._remove_context_item)
        self._menu.add_separator()
        self._menu.add_command(label="保存为模板", command=self._save_as_template_here)
        self._menu.add_command(label="更新该模板", command=self._update_template_here)
        self._menu.add_command(label="重新加载模板", command=self._reload_template_here)

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

    def _update_title(self) -> None:
        self.top.title(self.name)

    def set_layout(self, rows: int, smart_layout: bool, layout_algorithm: Optional[str] = None) -> None:
        self.rows = max(1, rows)
        self.smart_layout = smart_layout
        if layout_algorithm:
            self.layout_algorithm = layout_algorithm if layout_algorithm in LAYOUT_ALGORITHMS else "legacy"
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
                    messagebox.showwarning("读取失败", f"无法读取图片:\n{p}\n\n{exc}")
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

    def _on_resize(self, _evt: tk.Event) -> None:
        current_geo = self.top.geometry()
        if current_geo != self._last_geometry:
            self._last_geometry = current_geo
            self.app.mark_dirty()

        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        if w <= 1 or h <= 1:
            return
        if (w, h) != self._last_layout_size:
            self._resizing_until = time.time() + 0.28
            if self._resize_after_id:
                try:
                    self.top.after_cancel(self._resize_after_id)
                except Exception:
                    pass
            self._resize_after_id = self.top.after(140, self._flush_resize_render)

    def _flush_resize_render(self) -> None:
        self._resize_after_id = None
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
        while len(self._photo_cache) > CACHE_LIMIT:
            self._photo_cache.popitem(last=False)
        return tk_img

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
        self.canvas.focus_set()
        idx = self._index_from_xy(evt.x, evt.y)
        ctrl_down = bool(evt.state & 0x0004)
        shift_down = bool(evt.state & 0x0001)

        if shift_down:
            self._drag_active = False
            self._select_box_active = True
            self._select_box_start = (evt.x, evt.y)
            self._select_box_current = (evt.x, evt.y)
            if not ctrl_down:
                self._selected_indexes.clear()
            self.render(force=True)
            return

        self._selected_idx = idx
        if idx is None:
            self._drag_active = False
            if not ctrl_down:
                self._selected_indexes.clear()
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
            self.render(force=True)
            return

        self._selected_indexes = {idx}
        self._drag_active = True
        self._drag_source_idx = idx
        self._drag_target_idx = idx

    def _on_drag(self, evt: tk.Event) -> None:
        if self._select_box_active:
            self._select_box_current = (evt.x, evt.y)
            self.render(force=True)
            return
        if not self._drag_active:
            return
        idx = self._index_from_xy(evt.x, evt.y)
        if idx is None:
            return
        if idx != self._drag_target_idx:
            self._drag_target_idx = idx
            self.render(force=True)

    def _on_release(self, _evt: tk.Event) -> None:
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
            self.render(force=True)
            return

        if not self._drag_active:
            return

        src = self._drag_source_idx
        dst = self._drag_target_idx
        self._drag_active = False
        self._drag_source_idx = None
        self._drag_target_idx = None

        if src is None or dst is None or src == dst:
            self.render(force=True)
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
        idx = self._index_from_xy(evt.x, evt.y)
        self._context_idx = idx
        if idx is not None:
            self._selected_idx = idx
            if idx not in self._selected_indexes:
                self._selected_indexes = {idx}
        remove_count = len(self._selected_indexes) if self._selected_indexes else (1 if idx is not None else 0)
        remove_label = "从窗口组移除所选图片" if remove_count > 1 else "从窗口组移除图片"
        self._menu.entryconfigure(0, label=remove_label, state=("normal" if remove_count > 0 else "disabled"))
        has_template = self.template_path is not None and self.template_path.exists()
        self._menu.entryconfigure(3, state=("normal" if has_template else "disabled"))
        self._menu.entryconfigure(4, state=("normal" if has_template else "disabled"))
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

    def _draw_static_layout(self, total_w: int, total_h: int) -> None:
        self.canvas.delete("all")
        self._image_refs.clear()
        self._layout_rects.clear()
        self._cell_lookup_rects.clear()
        self._slot_image_ids.clear()
        self._slot_draw_sizes.clear()

        if not self.items:
            self.canvas.create_text(
                total_w // 2,
                total_h // 2,
                fill="#aaaaaa",
                text="该窗口组还没有图片\n可直接拖拽到此窗口",
                font=("Microsoft YaHei UI", 14),
                justify=tk.CENTER,
            )
            return

        if self.smart_layout:
            if self.layout_algorithm == "justified":
                rects = self._justified_layout_rects(total_w, total_h)
            else:
                rects = self._smart_layout_rects(total_w, total_h)
            self._layout_rows = max(1, self.rows)
            self._layout_cols = max(1, math.ceil(len(self.items) / max(1, self.rows)))
            self._cell_w = max(1, total_w // max(1, self._layout_cols))
            self._cell_h = max(1, total_h // max(1, self._layout_rows))
        else:
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

        for idx, item in enumerate(self.items):
            x0, y0, x1, y1 = rects[idx]
            cell_w = max(1, x1 - x0)
            cell_h = max(1, y1 - y0)
            self._layout_rects.append((x0, y0, x1, y1))
            self._cell_lookup_rects.append((x0, y0, x1, y1))

            frame_idx = -1
            frame = item.pil_image
            if item.is_gif and item.gif_frames:
                frame_idx = item.gif_index
                frame = item.gif_frames[item.gif_index]

            scale = min(cell_w / item.width, cell_h / item.height)
            draw_w = max(1, int(item.width * scale))
            draw_h = max(1, int(item.height * scale))

            tk_img = self._photo_for(item, frame_idx, frame, draw_w, draw_h)
            self._image_refs.append(tk_img)
            self._slot_draw_sizes.append((draw_w, draw_h))

            cx = x0 + cell_w // 2
            cy = y0 + cell_h // 2
            self.canvas.create_rectangle(x0, y0, x1, y1, outline="#1f1f1f")
            image_id = self.canvas.create_image(cx, cy, image=tk_img)
            self._slot_image_ids.append(image_id)

            if idx in self._selected_indexes:
                self.canvas.create_rectangle(
                    x0 + 2,
                    y0 + 2,
                    x1 - 2,
                    y1 - 2,
                    outline="#f7c948",
                    width=3,
                )
            elif self._selected_idx == idx:
                self.canvas.create_rectangle(
                    x0 + 2,
                    y0 + 2,
                    x1 - 2,
                    y1 - 2,
                    outline="#4cc9f0",
                    width=2,
                )

        if self._drag_active and self._drag_target_idx is not None:
            tidx = self._drag_target_idx
            if 0 <= tidx < len(self._layout_rects):
                x0, y0, x1, y1 = self._layout_rects[tidx]
                self.canvas.create_rectangle(
                    x0 + 2, y0 + 2, x1 - 2, y1 - 2, outline="#4cc9f0", width=3
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
            )

    def _refresh_gif_slots(self, changed_indexes: list[int]) -> None:
        if not changed_indexes:
            return
        if len(self._slot_image_ids) != len(self.items):
            self.render(force=True)
            return

        for idx in changed_indexes:
            if idx < 0 or idx >= len(self.items):
                continue
            item = self.items[idx]
            if not item.is_gif or not item.gif_frames:
                continue

            draw_w, draw_h = self._slot_draw_sizes[idx]
            frame_idx = item.gif_index
            frame = item.gif_frames[frame_idx]
            tk_img = self._photo_for(item, frame_idx, frame, draw_w, draw_h)
            self._image_refs[idx] = tk_img
            self.canvas.itemconfigure(self._slot_image_ids[idx], image=tk_img)

    def render(self, force: bool = False) -> None:
        total_w = self.canvas.winfo_width()
        total_h = self.canvas.winfo_height()
        if total_w <= 1 or total_h <= 1:
            return

        size_changed = (total_w, total_h) != self._last_layout_size
        if not force and not size_changed:
            return

        self._last_layout_size = (total_w, total_h)
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

    def tick_gif(self, now: float, frame_budget: int = 18) -> int:
        if not self.items or frame_budget <= 0 or now < self._resizing_until:
            return 0

        gif_indexes = [i for i, it in enumerate(self.items) if it.is_gif and it.gif_frames]
        if not gif_indexes:
            return 0

        start = self._gif_round_robin_start % len(gif_indexes)
        ordered = gif_indexes[start:] + gif_indexes[:start]

        changed_indexes: list[int] = []
        for idx in ordered:
            if len(changed_indexes) >= frame_budget:
                break
            item = self.items[idx]
            if self._advance_gif_to_now(item, now):
                changed_indexes.append(idx)

        self._gif_round_robin_start = (start + max(1, len(changed_indexes))) % len(gif_indexes)
        self._refresh_gif_slots(changed_indexes)
        return len(changed_indexes)


class PicReadApp:
    def __init__(self) -> None:
        self._enable_dpi_awareness()
        self.root = tk.Tk()
        self.root.title("PicRead - 多窗口组平铺看图")
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
        self._ui_state = self._load_ui_state()
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

    def _set_initial_window_geometry(self) -> None:
        sw = max(1024, self.root.winfo_screenwidth())
        sh = max(720, self.root.winfo_screenheight())

        # 给任务栏/缩放留安全边距，避免首屏 UI 被裁切。
        width = min(1680, max(1180, int(sw * 0.94)))
        height = min(1060, max(760, int(sh * 0.88)))
        x = max(0, (sw - width) // 2)
        y = max(0, (sh - height) // 2)
        self.root.geometry(f"{width}x{height}+{x}+{y}")

        min_w = min(width, max(1120, int(sw * 0.8)))
        min_h = min(height, max(700, int(sh * 0.72)))
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

    def _save_ui_state(self) -> None:
        geom_items = list(self._template_geometry_map.items())[:300]
        data = {
            "template_view_mode": self.template_view_var.get() if hasattr(self, "template_view_var") else "list",
            "perf_mode": self.perf_mode_var.get() if hasattr(self, "perf_mode_var") else "平衡",
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

        head = ttk.Label(
            root_frame,
            text="PicRead | 多窗口组平铺看图",
            font=("Microsoft YaHei UI", 14, "bold"),
        )
        head.pack(anchor="w")
        ttk.Separator(root_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=(8, 10))

        self.notebook = ttk.Notebook(root_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        groups_tab = ttk.Frame(self.notebook, padding=10)
        templates_tab = ttk.Frame(self.notebook, padding=10)
        history_tab = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(groups_tab, text="窗口组")
        self.notebook.add(templates_tab, text="模板库")
        self.notebook.add(history_tab, text="历史记录")

        control = ttk.Frame(groups_tab)
        control.pack(fill=tk.X)

        ttk.Label(control, text="窗口组名:").grid(row=0, column=0, sticky="w")
        self.group_name_var = tk.StringVar(value="窗口组")
        ttk.Entry(control, textvariable=self.group_name_var, width=18).grid(row=0, column=1, padx=6)

        ttk.Label(control, text="行数:").grid(row=0, column=2, sticky="e")
        self.rows_var = tk.IntVar(value=2)
        ttk.Spinbox(control, from_=1, to=12, textvariable=self.rows_var, width=6).grid(
            row=0, column=3, padx=6
        )

        self.smart_layout_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(control, text="智能排版", variable=self.smart_layout_var).grid(row=0, column=4, padx=6)
        ttk.Label(control, text="算法:").grid(row=0, column=5, sticky="e", padx=(8, 4))
        self.layout_algo_var = tk.StringVar(value="legacy")
        self.layout_algo_combo = ttk.Combobox(
            control,
            textvariable=self.layout_algo_var,
            values=[f"{LAYOUT_ALGORITHMS[key]} ({key})" for key in LAYOUT_ALGORITHMS],
            state="readonly",
            width=14,
        )
        self.layout_algo_combo.grid(row=0, column=6, sticky="w")
        self.layout_algo_combo.bind("<<ComboboxSelected>>", lambda _e: self._sync_layout_algo_value())
        self._sync_layout_algo_value("legacy")

        ttk.Button(control, text="创建窗口组", command=self.create_group).grid(row=0, column=7, padx=(10, 0))
        ttk.Label(control, text="性能模式:").grid(row=0, column=8, sticky="e", padx=(16, 4))
        default_mode = str(self._ui_state.get("perf_mode", "平衡"))
        if default_mode not in PERF_MODES:
            default_mode = "平衡"
        self.perf_mode_var = tk.StringVar(value=default_mode)
        self.perf_mode_combo = ttk.Combobox(
            control, textvariable=self.perf_mode_var, values=list(PERF_MODES.keys()), state="readonly", width=8
        )
        self.perf_mode_combo.grid(row=0, column=9, sticky="w")
        self.perf_mode_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_perf_mode_change())
        ttk.Button(control, text="调参面板", command=self.open_tuning_panel).grid(row=0, column=10, padx=(8, 0))

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
        self.group_list_menu.add_command(label="置顶/取消置顶", command=self._toggle_pin_selected_group)

        btns1 = ttk.Frame(groups_tab)
        btns1.pack(fill=tk.X)
        ttk.Button(btns1, text="应用布局", command=self.update_layout).pack(side=tk.LEFT)
        ttk.Button(btns1, text="合并到当前组", command=self.merge_groups).pack(side=tk.LEFT, padx=8)
        ttk.Button(btns1, text="关闭窗口组", command=self.close_group).pack(side=tk.RIGHT)

        btns2 = ttk.Frame(groups_tab)
        btns2.pack(fill=tk.X, pady=(8, 0))
        ttk.Button(btns2, text="启动安全布局", command=self.apply_safe_layout).pack(side=tk.LEFT)
        ttk.Button(btns2, text="保存为模板", command=self.save_group_template).pack(side=tk.LEFT)
        ttk.Button(btns2, text="保存会话", command=self.save_session_snapshot).pack(side=tk.LEFT, padx=8)

        tpl_top = ttk.Frame(templates_tab)
        tpl_top.pack(fill=tk.X)
        ttk.Button(tpl_top, text="刷新模板库", command=self.refresh_template_library).pack(side=tk.LEFT)
        ttk.Button(tpl_top, text="打开模板", command=self.load_group_template).pack(side=tk.LEFT, padx=8)
        ttk.Button(tpl_top, text="重命名模板", command=self.rename_selected_template).pack(side=tk.LEFT)
        ttk.Button(tpl_top, text="编辑标签", command=self.edit_selected_template_tags).pack(side=tk.LEFT, padx=8)
        ttk.Button(tpl_top, text="删除模板", command=self.delete_selected_template).pack(side=tk.LEFT)
        ttk.Button(tpl_top, text="更新该模板", command=self.update_linked_template).pack(side=tk.LEFT, padx=8)
        ttk.Button(tpl_top, text="重新加载模板", command=self.reload_linked_template).pack(side=tk.LEFT)
        self.template_view_var = tk.StringVar(value=str(self._ui_state.get("template_view_mode", "list")))
        ttk.Radiobutton(
            tpl_top, text="列表", variable=self.template_view_var, value="list", command=self._switch_template_view
        ).pack(side=tk.RIGHT)
        ttk.Radiobutton(
            tpl_top, text="图标", variable=self.template_view_var, value="icon", command=self._switch_template_view
        ).pack(side=tk.RIGHT, padx=8)
        ttk.Label(tpl_top, text="标签:").pack(side=tk.RIGHT)
        self.template_tag_var = tk.StringVar(value="全部")
        self.template_tag_combo = ttk.Combobox(
            tpl_top, textvariable=self.template_tag_var, values=["全部"], state="readonly", width=12
        )
        self.template_tag_combo.pack(side=tk.RIGHT, padx=(4, 8))
        self.template_tag_combo.bind("<<ComboboxSelected>>", lambda _e: self.refresh_template_library())
        ttk.Label(tpl_top, text="搜索:").pack(side=tk.RIGHT)
        self.template_search_var = tk.StringVar(value="")
        search_entry = ttk.Entry(tpl_top, textvariable=self.template_search_var, width=18)
        search_entry.pack(side=tk.RIGHT, padx=(4, 12))
        self.template_search_var.trace_add("write", lambda *_: self.refresh_template_library())

        self.template_entries: list[dict] = []
        self.template_selected_idx: Optional[int] = None
        self.template_thumbs: list[ImageTk.PhotoImage] = []
        self.template_icon_cells: list[tuple[int, int, int, int]] = []
        self.template_context_var = tk.StringVar(value="当前目标组：未选择")
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
        self.template_canvas.bind("<Configure>", lambda _e: self._render_template_icons())
        self._bind_vertical_mousewheel(self.template_canvas, self.template_canvas)
        self.tpl_icon_scroll = ttk.Scrollbar(self.tpl_icon_frame, orient=tk.VERTICAL, command=self.template_canvas.yview)
        self.tpl_icon_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.template_canvas.configure(yscrollcommand=self.tpl_icon_scroll.set)

        self._switch_template_view()
        self.refresh_template_library()
        self._build_history_tab(history_tab)
        self.refresh_history_library()

        self.status_var = tk.StringVar(value="就绪")
        status = ttk.Label(root_frame, textvariable=self.status_var, anchor="w", justify=tk.LEFT)
        status.pack(fill=tk.X, pady=(8, 0))
        root_frame.bind(
            "<Configure>",
            lambda e: status.configure(wraplength=max(280, int(e.width) - 24)),
        )
        self._apply_dark_widget_styles()

    def _setup_style(self) -> None:
        self.root.option_add("*Font", "{Microsoft YaHei UI} 10")
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

        self.root.configure(bg=bg)
        style.configure(".", background=bg, foreground=fg)
        style.configure("TFrame", background=bg)
        style.configure("TLabel", background=bg, foreground=fg, padding=(1, 1))
        style.configure("TButton", background=panel, foreground=fg, bordercolor=border, padding=(10, 6))
        style.map(
            "TButton",
            background=[("active", "#2a2d2e"), ("pressed", "#31363b")],
            foreground=[("disabled", muted)],
        )
        style.configure("TEntry", fieldbackground=panel, foreground=fg, bordercolor=border)
        style.configure("TCombobox", fieldbackground=panel, foreground=fg, background=panel)
        style.map(
            "TCombobox",
            fieldbackground=[("readonly", panel), ("disabled", "#2a2a2a")],
            foreground=[("readonly", fg), ("disabled", "#7f848e")],
            selectbackground=[("readonly", panel)],
            selectforeground=[("readonly", fg)],
        )
        style.configure("TSpinbox", fieldbackground=panel, foreground=fg, arrowcolor=fg)
        style.map(
            "TSpinbox",
            fieldbackground=[("readonly", panel), ("disabled", "#2a2a2a")],
            foreground=[("readonly", fg), ("disabled", "#7f848e")],
        )
        style.configure("TCheckbutton", background=bg, foreground=fg)
        style.configure("TRadiobutton", background=bg, foreground=fg)
        style.configure("TNotebook", background=bg, borderwidth=0)
        style.configure("TNotebook.Tab", background=panel, foreground=fg, padding=(10, 6))
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
        return f"{LAYOUT_ALGORITHMS[safe_key]} ({safe_key})"

    def _layout_algo_key_from_var(self) -> str:
        raw = self.layout_algo_var.get().strip() if hasattr(self, "layout_algo_var") else "legacy"
        match = re.search(r"\(([^()]+)\)\s*$", raw)
        key = match.group(1).strip() if match else raw
        return key if key in LAYOUT_ALGORITHMS else "legacy"

    def _sync_layout_algo_value(self, key: Optional[str] = None) -> None:
        safe_key = key or self._layout_algo_key_from_var()
        if hasattr(self, "layout_algo_var"):
            self.layout_algo_var.set(self._layout_algo_label(safe_key))

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
            for enc in ("utf-8", "gb18030", "gbk", "mbcs"):
                try:
                    return raw.decode(enc)
                except Exception:
                    continue
            return raw.decode(errors="ignore")
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

    def add_paths_to_group(self, group: GroupWindow, paths: list[Path], show_errors: bool = True) -> None:
        if not paths:
            return
        group.add_paths(paths, show_errors=show_errors)
        self._refresh_list(select_gid=group.group_id)

    def _on_drop_to_main(self, files) -> None:
        paths = self._collect_supported_paths(files)
        if not paths:
            messagebox.showwarning("提示", "拖入的文件里没有受支持的图片格式。")
            return

        group = self._selected_group()
        if group is None and len(self.groups) == 1:
            group = next(iter(self.groups.values()))

        if group is None:
            messagebox.showinfo("提示", "请先创建并选中一个窗口组，再拖入图片。")
            return

        self.add_paths_to_group(group, paths)

    def _on_drop_to_group(self, group: GroupWindow, files) -> None:
        paths = self._collect_supported_paths(files)
        if not paths:
            messagebox.showwarning("提示", "拖入的文件里没有受支持的图片格式。")
            return
        self.add_paths_to_group(group, paths)

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

    def _safe_template_filename(self, name: str) -> str:
        clean = re.sub(r"[^\w\-\u4e00-\u9fff]+", "_", name.strip())
        return (clean or "template") + ".json"

    def _template_display_name(self, data: dict, fallback_stem: str) -> str:
        raw = str(data.get("template_name", data.get("name", fallback_stem))).strip()
        if raw in {"", "窗口组", "模板组"}:
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
            self._render_template_icons()
        else:
            self.tpl_list_frame.pack(fill=tk.BOTH, expand=True)

    def current_profile(self) -> dict:
        mode = self.perf_mode_var.get() if hasattr(self, "perf_mode_var") else "平衡"
        return PERF_MODES.get(mode, PERF_MODES["平衡"])

    def _on_perf_mode_change(self) -> None:
        self.mark_dirty()
        for g in self.groups.values():
            g._photo_cache.clear()
            g.render(force=True)
        self._sync_tuning_panel_from_mode()

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
        win.title("画质/性能调参")
        self._center_window(win, 520, 420)
        win.minsize(480, 360)
        win.transient(self.root)
        self._tune_win = win

        frame = ttk.Frame(win, padding=12)
        frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(frame, text="当前模式参数（修改后立即生效）").pack(anchor="w")
        ttk.Label(frame, text="说明：复选框勾选=开启，取消=关闭").pack(anchor="w", pady=(2, 8))

        self._tune_tick_var = tk.IntVar()
        self._tune_budget_var = tk.IntVar()
        self._tune_multi_var = tk.BooleanVar()
        self._tune_two_pass_var = tk.BooleanVar()
        self._tune_blur_var = tk.DoubleVar()
        self._tune_sharpen_var = tk.BooleanVar()
        self._tune_resample_var = tk.StringVar(value="LANCZOS")

        grid = ttk.Frame(frame)
        grid.pack(fill=tk.BOTH, expand=True, pady=(10, 0))

        ttk.Label(grid, text="刷新间隔 ms").grid(row=0, column=0, sticky="w")
        ttk.Scale(grid, from_=12, to=45, variable=self._tune_tick_var, orient=tk.HORIZONTAL).grid(row=0, column=1, sticky="ew", padx=8)
        ttk.Label(grid, textvariable=self._tune_tick_var).grid(row=0, column=2, sticky="e")

        ttk.Label(grid, text="每轮帧预算").grid(row=1, column=0, sticky="w")
        ttk.Scale(grid, from_=8, to=80, variable=self._tune_budget_var, orient=tk.HORIZONTAL).grid(row=1, column=1, sticky="ew", padx=8)
        ttk.Label(grid, textvariable=self._tune_budget_var).grid(row=1, column=2, sticky="e")

        ttk.Label(grid, text="重采样").grid(row=2, column=0, sticky="w")
        ttk.Combobox(
            grid,
            textvariable=self._tune_resample_var,
            values=list(RESAMPLE_NAME_TO_VALUE.keys()),
            state="readonly",
            width=12,
        ).grid(row=2, column=1, sticky="w", padx=8)

        ttk.Label(grid, text="预模糊").grid(row=3, column=0, sticky="w")
        ttk.Scale(grid, from_=0.0, to=0.5, variable=self._tune_blur_var, orient=tk.HORIZONTAL).grid(row=3, column=1, sticky="ew", padx=8)
        ttk.Label(grid, textvariable=self._tune_blur_var).grid(row=3, column=2, sticky="e")

        ttk.Checkbutton(grid, text="开启多段缩放", variable=self._tune_multi_var).grid(row=4, column=0, sticky="w")
        ttk.Checkbutton(grid, text="开启双通道缩放", variable=self._tune_two_pass_var).grid(row=4, column=1, sticky="w", padx=8)
        ttk.Checkbutton(grid, text="开启锐化", variable=self._tune_sharpen_var).grid(row=5, column=0, sticky="w")
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
        ttk.Button(btns, text="应用", command=_apply).pack(side=tk.LEFT)
        ttk.Button(btns, text="重置当前模式", command=_reset_mode).pack(side=tk.LEFT, padx=8)

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
            drag_text = "拖拽:关"
        else:
            backend = getattr(self, "drag_drop_backend", "none")
            if backend == "windnd":
                drag_text = "拖拽:开(windnd)"
            elif backend == "win32":
                drag_text = "拖拽:开(系统)"
            else:
                drag_text = "拖拽:开"
        self.status_var.set(
            f"模式: {self.perf_mode_var.get()} | 策略: {profile['strategy']} | 预算: {profile['frame_budget']}帧/轮 | GIF数: {gif_count} | 本轮更新: {updated_frames} | 命中: {ratio:.1f}% | 图像缓存: {photo_cache_entries} | 缩略图缓存: {len(self._thumb_photo_cache)} | 内存: {mem_text} | {drag_text}"
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
            self.template_context_var.set("当前目标组：未选择")
            return
        if g.template_path:
            self.template_context_var.set(f"当前目标组：{g.name}（关联模板：{g.template_path.stem}）")
        else:
            self.template_context_var.set(f"当前目标组：{g.name}（未关联模板）")

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

        selected_tag = self.template_tag_var.get() if hasattr(self, "template_tag_var") else "全部"
        search = self.template_search_var.get().strip().lower() if hasattr(self, "template_search_var") else ""
        if hasattr(self, "template_tag_combo"):
            values = ["全部"] + sorted(all_tags)
            self.template_tag_combo.configure(values=values)
            if selected_tag not in values:
                selected_tag = "全部"
                self.template_tag_var.set("全部")

        self.template_entries = []
        for ent in all_entries:
            if selected_tag != "全部" and selected_tag not in ent["tags"]:
                continue
            if search:
                hay = f"{ent['name']} {' '.join(ent['tags'])} {ent['path'].stem}".lower()
                if search not in hay:
                    continue
            self.template_entries.append(ent)

        self.template_list.delete(0, tk.END)
        for ent in self.template_entries:
            mode = "smart" if ent["smart"] else "fixed"
            tag_text = f" | tags={','.join(ent['tags'])}" if ent["tags"] else ""
            self.template_list.insert(
                tk.END, f"{ent['name']} | {mode} rows={ent['rows']} | images={ent['count']}{tag_text}"
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
        self.template_selected_idx = sel[0]
        self._render_template_icons()

    def _render_template_icons(self) -> None:
        if not hasattr(self, "template_canvas"):
            return
        c = self.template_canvas
        c.delete("all")
        self.template_icon_cells.clear()
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
            c.create_rectangle(x0, y0, x1, y1, outline=outline, width=2)

            preview = ent["preview"]
            if preview and Path(preview).is_file():
                image_id = c.create_text(x0 + card_w // 2, y0 + 54, text="加载中...", fill="#9a9a9a")
                thumb_tasks.append((idx, preview, image_id, x0 + card_w // 2))
            else:
                c.create_text(x0 + card_w // 2, y0 + 54, text="No Preview", fill="#9a9a9a")

            c.create_text(
                x0 + 8,
                y0 + 116,
                text=ent["name"],
                fill="#dddddd",
                anchor="nw",
                width=card_w - 16,
            )
            mode = "smart" if ent["smart"] else "fixed"
            c.create_text(
                x0 + 8,
                y0 + 156,
                text=f"{mode} rows={ent['rows']}\n{ent['count']} imgs",
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
                c.itemconfigure(text_item_id, text="No Preview")
                continue
            self.template_thumbs.append(tk_img)
            x, y = c.coords(text_item_id)
            c.delete(text_item_id)
            c.create_image(center_x, y, image=tk_img)

        if end < len(tasks):
            self.root.after(1, lambda: self._render_thumb_batch(tasks, token, end, batch))

    def _on_template_icon_click(self, evt: tk.Event) -> None:
        x = self.template_canvas.canvasx(evt.x)
        y = self.template_canvas.canvasy(evt.y)
        for idx, (x0, y0, x1, y1) in enumerate(self.template_icon_cells):
            if x0 <= x <= x1 and y0 <= y <= y1:
                self.template_selected_idx = idx
                self.template_list.selection_clear(0, tk.END)
                self.template_list.selection_set(idx)
                self.template_list.see(idx)
                self._render_template_icons()
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
        ttk.Button(top, text="刷新历史", command=self.refresh_history_library).pack(side=tk.LEFT)
        ttk.Button(top, text="打开所选历史", command=self.open_selected_history).pack(side=tk.LEFT, padx=8)

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
            self.history_list.insert(tk.END, f"[最新自动会话] session.json ({ts})")
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
            messagebox.showinfo("提示", "请先选择一条历史记录。")
            return
        p = self.history_entries[sel[0]]
        if self.groups:
            ok = messagebox.askyesno("恢复会话", "恢复会话会替换当前窗口组，是否继续？")
            if not ok:
                return
        self.load_session(path=p, silent=False, replace_existing=True)

    def _choose_from_entries(self, title: str, entries: list[tuple[str, Path]]) -> Optional[Path]:
        if not entries:
            messagebox.showinfo("提示", "当前没有可用记录。")
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
        ttk.Button(btns, text="打开", command=_open_selected).pack(side=tk.LEFT)
        ttk.Button(btns, text="取消", command=win.destroy).pack(side=tk.RIGHT)

        self.root.wait_window(win)
        return result["path"]

    def _prompt_template_meta(
        self,
        title: str,
        default_name: str,
        default_tags: Optional[list[str]] = None,
    ) -> Optional[tuple[str, list[str]]]:
        result: dict[str, Optional[tuple[str, list[str]]]] = {"value": None}
        win = tk.Toplevel(self.root)
        self.apply_window_icon(win)
        win.title(title)
        win.transient(self.root)
        win.grab_set()

        body = ttk.Frame(win, padding=16)
        body.pack(fill=tk.BOTH, expand=True)
        ttk.Label(body, text=title, font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w", pady=(0, 10))

        ttk.Label(body, text="模板名称").pack(anchor="w")
        name_var = tk.StringVar(value=default_name)
        name_entry = ttk.Entry(body, textvariable=name_var, width=40)
        name_entry.pack(fill=tk.X, pady=(4, 10))

        ttk.Label(body, text="分类 / 标签（逗号分隔，可留空）").pack(anchor="w")
        tags_var = tk.StringVar(value=",".join(default_tags or []))
        tags_entry = ttk.Entry(body, textvariable=tags_var, width=40)
        tags_entry.pack(fill=tk.X, pady=(4, 0))

        def _confirm() -> None:
            name = name_var.get().strip()
            if not name:
                messagebox.showinfo("提示", "模板名称不能为空。", parent=win)
                return
            result["value"] = (name, self._parse_tags(tags_var.get()))
            win.destroy()

        ttk.Label(body, text="留空表示不分类。", foreground="#9da5b4").pack(anchor="w", pady=(10, 0))

        btns = ttk.Frame(win, padding=(16, 0, 16, 16))
        btns.pack(fill=tk.X, side=tk.BOTTOM)
        ttk.Button(btns, text="确定", command=_confirm).pack(side=tk.LEFT)
        ttk.Button(btns, text="取消", command=win.destroy).pack(side=tk.RIGHT)

        win.update_idletasks()
        req_w = max(560, win.winfo_reqwidth() + 24)
        req_h = max(340, win.winfo_reqheight() + 24)
        self._center_window(win, req_w, req_h)
        win.minsize(req_w, req_h)

        name_entry.focus_set()
        name_entry.selection_range(0, tk.END)
        win.bind("<Return>", lambda _e: _confirm())
        self.root.wait_window(win)
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
        name = self.group_name_var.get().strip() or "窗口组"
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
            mode = "smart" if g.smart_layout else "fixed"
            algo = f" | algo={LAYOUT_ALGORITHMS.get(g.layout_algorithm, '算法1')}" if g.smart_layout else ""
            tpl = " | tpl" if g.template_path else ""
            pin = " [PIN]" if gid in self._pinned_groups else ""
            self.group_list.insert(
                tk.END,
                f"{gid}# {g.name}{pin} | layout={mode} rows={g.rows}{algo} | images={len(g.items)}{tpl}",
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
            messagebox.showinfo("提示", "请先在列表里选择一个窗口组。")
            return

        paths = filedialog.askopenfilenames(
            title="选择图片",
            filetypes=[
                ("图片", "*.png *.jpg *.jpeg *.gif *.bmp *.webp"),
                ("所有文件", "*.*"),
            ],
        )
        if not paths:
            return

        normalized = self._collect_supported_paths(paths)
        if not normalized:
            messagebox.showwarning("提示", "没有选中受支持的图片类型。")
            return

        self.add_paths_to_group(g, normalized)

    def update_layout(self) -> None:
        g = self._selected_group()
        if not g:
            messagebox.showinfo("提示", "请先在列表里选择一个窗口组。")
            return

        rows = max(1, int(self.rows_var.get() or 1))
        smart = bool(self.smart_layout_var.get())
        layout_algorithm = self._layout_algo_key_from_var()
        new_name = self.group_name_var.get().strip() or g.name
        g.name = new_name
        g._update_title()
        g.set_layout(rows, smart, layout_algorithm=layout_algorithm)
        self._refresh_list(select_gid=g.group_id)

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
        g = group or self._selected_group()
        if not g:
            messagebox.showinfo("提示", "请先选择一个窗口组。")
            return

        default_name = g.name
        existing_tags: list[str] = []
        if g.template_path and g.template_path.exists():
            try:
                existing = json.loads(g.template_path.read_text(encoding="utf-8"))
                existing_tags = list(existing.get("tags", []))
            except Exception:
                existing_tags = []

        meta = self._prompt_template_meta("保存模板", default_name, existing_tags)
        if not meta:
            return
        name, tags = meta

        data = g.to_state()
        data["template_name"] = name
        data["tags"] = tags
        file_path = TEMPLATE_DIR / self._safe_template_filename(name)
        current_path = g.template_path.resolve() if g.template_path and g.template_path.exists() else None
        if file_path.exists() and file_path.resolve() != current_path:
            messagebox.showwarning("提示", "同名模板已存在，请换一个模板名称。")
            return
        try:
            file_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            g.template_path = file_path
            self.refresh_template_library()
            messagebox.showinfo("完成", f"模板已保存:\n{file_path.name}")
        except Exception as exc:
            messagebox.showerror("保存失败", str(exc))

    def persist_template_geometry(self, g: GroupWindow) -> None:
        if g.suppress_template_geometry_persist:
            return
        if not g.template_path or not g.template_path.exists():
            return
        key = str(g.template_path.resolve())
        self._template_geometry_map[key] = g.top.geometry()

    def load_group_template(self) -> None:
        ent = self._selected_template_entry()
        if ent is None:
            self.refresh_template_library()
            ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo("提示", "请先在模板库中选择一个模板。")
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
        g = group or self._selected_group()
        if g is None:
            messagebox.showinfo("提示", "请先选择一个目标窗口组。")
            return
        if not g.template_path:
            messagebox.showinfo("提示", "当前组没有关联模板，请先“保存为模板”。")
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
            messagebox.showinfo("完成", f"已更新模板: {g.template_path.name}")
        except Exception as exc:
            messagebox.showerror("更新失败", str(exc))

    def reload_linked_template(self, group: Optional[GroupWindow] = None) -> None:
        g = group or self._selected_group()
        if g is None:
            messagebox.showinfo("提示", "请先选择一个目标窗口组。")
            return
        if not g.template_path or not g.template_path.exists():
            messagebox.showinfo("提示", "当前组没有可用的关联模板。")
            return

        try:
            data = json.loads(g.template_path.read_text(encoding="utf-8"))
        except Exception as exc:
            messagebox.showerror("读取失败", str(exc))
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
        ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo("提示", "请先在模板库中选择一个模板。")
            return

        old_name = ent["name"]
        new_name = simpledialog.askstring("重命名模板", "新模板名称:", initialvalue=old_name)
        if not new_name:
            return
        new_name = new_name.strip()
        if not new_name:
            return

        old_path: Path = ent["path"]
        new_path = TEMPLATE_DIR / self._safe_template_filename(new_name)
        if new_path.exists() and new_path != old_path:
            messagebox.showwarning("提示", "同名模板已存在，请换一个名称。")
            return

        try:
            data = json.loads(old_path.read_text(encoding="utf-8"))
        except Exception as exc:
            messagebox.showerror("读取失败", str(exc))
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
            messagebox.showinfo("完成", f"模板已重命名为: {new_name}")
        except Exception as exc:
            messagebox.showerror("重命名失败", str(exc))

    def _parse_tags(self, text: str) -> list[str]:
        out: list[str] = []
        for token in text.replace("，", ",").split(","):
            t = token.strip()
            if t and t not in out:
                out.append(t)
        return out

    def edit_selected_template_tags(self) -> None:
        ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo("提示", "请先在模板库中选择一个模板。")
            return
        old_tags = ent.get("tags", [])
        text = simpledialog.askstring(
            "编辑标签",
            "标签（逗号分隔）:",
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
            messagebox.showerror("标签更新失败", str(exc))

    def delete_selected_template(self) -> None:
        ent = self._selected_template_entry()
        if ent is None:
            messagebox.showinfo("提示", "请先在模板库中选择一个模板。")
            return

        p: Path = ent["path"]
        display_name = ent["name"]
        ok = messagebox.askyesno("删除模板", f"确定删除模板“{display_name}”吗？\n\n此操作不会删除原始图片文件。")
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
            messagebox.showerror("删除失败", str(exc))

    def _session_payload(self) -> dict:
        ordered_existing = [gid for gid in self._group_order if gid in self.groups]
        return {
            "version": 1,
            "saved_at": int(time.time()),
            "groups": [self.groups[gid].to_state() for gid in ordered_existing],
        }

    def _write_history_snapshot(self, payload: dict) -> None:
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
                messagebox.showinfo("完成", "会话已保存。")
        except Exception as exc:
            if not silent:
                messagebox.showerror("保存失败", str(exc))

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
                messagebox.showinfo("提示", "当前没有可恢复的会话文件。")
            return

        try:
            payload = json.loads(src.read_text(encoding="utf-8"))
        except Exception as exc:
            if not silent:
                messagebox.showerror("读取失败", str(exc))
            return

        groups = payload.get("groups", [])
        if not isinstance(groups, list):
            if not silent:
                messagebox.showerror("读取失败", "会话格式不正确。")
            return

        self._suspend_dirty = True
        try:
            if replace_existing and self.groups:
                self._close_all_groups()

            for item in groups:
                name = str(item.get("name", "窗口组")).strip() or "窗口组"
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
            messagebox.showinfo("完成", "会话恢复完成。")

    def _choose_merge_sources(self, target_gid: int) -> list[int]:
        others = [gid for gid in self._group_order if gid != target_gid and gid in self.groups]
        if not others:
            return []

        result: dict[str, list[int]] = {"gids": []}
        win = tk.Toplevel(self.root)
        self.apply_window_icon(win)
        win.title("选择要合并的窗口组")
        self._center_window(win, 520, 400)
        win.transient(self.root)
        win.grab_set()

        ttk.Label(win, text="选择要并入当前目标组的窗口组", font=("Microsoft YaHei UI", 11, "bold")).pack(
            anchor="w", padx=12, pady=(12, 4)
        )
        ttk.Label(win, text="按列表顺序合并，源窗口会被关闭，组内图片顺序会保持不变。").pack(
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
        ttk.Button(btns, text="合并", command=_ok).pack(side=tk.LEFT)
        ttk.Button(btns, text="取消", command=win.destroy).pack(side=tk.RIGHT)

        lb.focus_set()
        self.root.wait_window(win)
        return result["gids"]

    def merge_groups(self) -> None:
        target = self._selected_group()
        if target is None:
            messagebox.showinfo("提示", "请先在列表中选择目标窗口组。")
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
        remaining_budget = int(profile["frame_budget"])
        updated_total = 0
        for g in list(self.groups.values()):
            if remaining_budget <= 0:
                break
            used = g.tick_gif(now, frame_budget=max(4, remaining_budget // max(1, len(self.groups))))
            remaining_budget -= used
            updated_total += used
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
