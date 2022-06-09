#!/bin/bash

cabal build
exe_location=$(cabal exec which FO-prover)
cp $exe_location .