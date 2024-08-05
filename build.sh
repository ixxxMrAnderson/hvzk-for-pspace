#!/bin/bash
set -eu
shopt -s nullglob
cd "$(dirname "$0")"

CXXFLAGS="-std=c++14 -fno-exceptions -fno-rtti"
CXXFLAGS_WARN="-fmax-errors=2 -Wall -Wextra -Wno-class-memaccess -Wno-sign-conversion -Wno-unused-variable -Wno-sign-compare -Wno-write-strings -Wno-unused-parameter -Wno-comment"
CXXFLAGS_COMPAT="-static-libgcc -static-libstdc++"
LDFLAGS="-I/opt/homebrew/opt/openssl@3 -lcrypto -lssl"
LIBPROFILER=/usr/local/lib/libprofiler.so

NAME=solver

# Default to g++ as we are using GCC extensions (clang works fine as well, though)
GXX=$(find /usr/bin -name 'g++*' | sort -t- -k2n | tail -n1)
CLANGXX=$(find /usr/bin -name 'clang++*' | sort -t- -k2n | tail -n1)
CXX=${CXX:-$GXX}
if [[ -z "$CXX" ]]; then
    echo "Error: no compiler found. Please specify a compiler by setting the CXX environment variable, i.e.:"
    echo "    CXX=clang++ $0 $@"
    exit 1
fi

if [[ "$#" > 0 && ( "$1" = "-h" || "$1" = "--help" ) ]]; then
    echo "Usage:"
    echo "  $0 [default|debug|release]"
    echo "  $0 [debug_compat|clang_sanitize|demo|release_compat|fuzz|profile]"
    echo
    echo "Compile blic in the specified mode. default is an optimised build without warnings. If you just want to use blic, use that one."
    exit 1
fi;


if [[ "$#" < 1 || "$1" = "default" ]]; then
    "$CXX" $CXXFLAGS -O3 -mcpu=native -DNDEBUG -ggdb solver.cpp -o "$NAME" $LDFLAGS
elif [[ "$1" = "debug" ]]; then
    "$CXX" $CXXFLAGS $CXXFLAGS_WARN -O0 -ggdb -Werror solver.cpp -o "$NAME" $LDFLAGS
elif [[ "$1" = "debug_compat" ]]; then
    "$CXX" $CXXFLAGS $CXXFLAGS_WARN $CXXFLAGS_COMPAT -O0 -ggdb -Werror solver.cpp -o "$NAME" $LDFLAGS
elif [[ "$1" = "clang_sanitize" ]]; then
    "$CLANGXX" $CXXFLAGS -O0 -ggdb -Werror solver.cpp -o "$NAME" -fsanitize=address -fsanitize=undefined $LDFLAGS
elif [[ "$1" = "demo" ]]; then
    "$CXX" $CXXFLAGS $CXXFLAGS_WARN -DFFE_SIMPLE -O0 -ggdb solver.cpp -o "$NAME" $LDFLAGS
elif [[ "$1" = "release" ]]; then
    "$CXX" $CXXFLAGS $CXXFLAGS_WARN -O3 -mcpu=native -DNDEBUG -ggdb solver.cpp -o "$NAME" $LDFLAGS
elif [[ "$1" = "release_compat" ]]; then
    "$CXX" $CXXFLAGS $CXXFLAGS_WARN $CXXFLAGS_COMPAT -O3 -mcpu=native -DNDEBUG -ggdb solver.cpp -o "$NAME" $LDFLAGS
elif [[ "$1" = "fuzz" ]]; then
    "afl-clang-fast" $CXXFLAGS -O0 -ggdb solver.cpp -o "$NAME" $LDFLAGS
    AFL_SKIP_CPUFREQ=1 afl-fuzz -i test/ -o fuzz ./solver --fuzz
elif [ "$1" = "profile" ]; then
    mkdir -p profdata
    echo '# Execute:'
    echo LD_PRELOAD="$LIBPROFILER" CPUPROFILE=./profdata/"$NAME".prof CPUPROFILE_FREQUENCY=1000 ./"$NAME" '<args>'
    echo pprof -http ":" "$NAME" profdata/"$NAME".prof
else
    echo "Error: Unknown argument"
    exit 1
fi;
