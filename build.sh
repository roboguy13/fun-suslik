#!/bin/sh
(cd suslik; sbt assembly)
cabal build --enable-tests

