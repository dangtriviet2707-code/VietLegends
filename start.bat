@echo off
chcp 65001 >nul
cd /d "%~dp0"
if not exist node_modules (
  echo Dang cai thu vien lan dau, vui long cho...
  call npm install
)
call npm start
pause
