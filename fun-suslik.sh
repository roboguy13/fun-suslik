#!/bin/sh

if [ -d ".stack-work/dist" ]; then
  # Prefer a stack executable, if it exists
  stack exec fun-suslik $1
else
  # Otherwise, use cabal
  cabal exec fun-suslik $1
fi
