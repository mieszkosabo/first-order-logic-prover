#!/bin/bash

cabal build
exe_location=$(cabal exec which Fo-prover)
cp $exe_location .