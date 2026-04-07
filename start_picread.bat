@echo off
setlocal
cd /d "%~dp0"

where python >nul 2>nul
if errorlevel 1 (
  echo [PicRead] Python not found in PATH.
  echo Please install Python 3 and ensure "python" command is available.
  pause
  exit /b 1
)

python app.py
if errorlevel 1 (
  echo.
  echo [PicRead] Launch failed. Installing dependencies and retrying...
  python -m pip install -r requirements.txt
  python app.py
)

endlocal
