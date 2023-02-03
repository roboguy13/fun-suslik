#!/bin/sh

if [ -d ".stack-work/dist" ]; then
  # Use a stack executable, if it exists
  stack exec fun-suslik $1
else
  echo Executable not compiled by stack. Run stack build.
  echo If you want to use cabal, run \'cabal exec fun-suslik \<file\>.fsus\'
fi
