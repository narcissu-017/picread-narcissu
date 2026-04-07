# PicRead

[![English](https://img.shields.io/badge/README-English-2d6cdf?style=for-the-badge)](README.md) [![简体中文](https://img.shields.io/badge/%E8%AF%B4%E6%98%8E-%E7%AE%80%E4%BD%93%E4%B8%AD%E6%96%87-2d6cdf?style=for-the-badge)](README.zh-CN.md)

PicRead is a multi-window tiling viewer for reviewing large numbers of images and GIFs.

It works especially well when you want to:
- compare many images or GIFs at once
- make better use of a large monitor without wasting too much desktop space
- keep the original order and aspect ratio of your images while reviewing
- save reusable templates for different projects, themes, or batches
- and, honestly, use your giant screen to tile your hand-picked images and animated clips so you can get going right away

## Features
- Multiple window groups at the same time
- Supports PNG, JPG, JPEG, BMP, WEBP, and GIF
- Mixed viewing of still images and animated GIFs
- Automatic tiling while preserving aspect ratio
- Fixed-row layout and smart layout
- Drag to reorder items inside a group
- Multi-select and batch remove
- Template library, history, and session saving
- Open, update, reload, and delete templates
- Merge window groups
- Drag and drop image import
- Performance modes and tuning panel

## Download and Use
A ready-to-run build is included in this repository:
- `dist/PicRead.exe`

Usage notes:
- Running the EXE does not require Python to be installed.
- On first launch, the app creates its own local state folder under `dist/state/`.
- If you move the EXE, it is best to move the entire `dist` folder together.

## Run from Source
Environment:
- Windows 10/11
- Python 3.12 or a nearby version

Install dependencies:
```powershell
python -m pip install -r requirements.txt
```

Run:
```powershell
python app.py
```

Or double-click:
- `start_picread.bat`

## Basic Usage
1. Start the app and create a window group.
2. Drag images or GIFs into the window group, or import them through the UI.
3. Switch between fixed layout and smart layout as needed.
4. Drag items inside a group to reorder them.
5. Right-click or press `Delete` to remove selected items from the current group.
6. Use the template library to save and reopen common image sets.
7. Use history to restore recent viewing states.

## Templates and History
- Templates are useful for saving common image combinations, order, and layout settings.
- History is useful for restoring recent working states.
- These are stored locally in the `state/` folder and do not modify the original files.

## Layout Algorithm Notes
This repository includes a separate layout algorithm document:
- `docs/layout_algorithms.md`

It explains the current layout strategies, their goals, and the core implementation ideas with code snippets.

## Feedback and Algorithm Improvements
The current smart layout is already practical for daily use, but there is still room for improvement, especially around:
- space utilization
- mixed horizontal and vertical image layouts
- stability with large batches of images and GIFs
- more natural behavior across different window sizes

If anyone would like to help improve the layout algorithms even further, suggestions and contributions are very welcome.
