@echo off

set target="regular_expression"

g++ %target%.cpp -o %target%.exe -Og -g -I"D:/raiscies/repo/c++/libraries/fmt/include/" -L"D:/Raiscies/repo/C++/libraries/fmt/build/" -l:"libfmt.a" -Wl,-Bstatic -lpthread -Wl,-Bdynamic

rem strip %target%.exe

if "%1" == "run" (
	%target%.exe
)else (
	echo built, press any key to strip and run
	pause > nul
	%target%.exe
)
