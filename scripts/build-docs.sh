#!/bin/sh
# Refresh the browser version in docs/: the widget's JavaScript and the numbers Lean computes.
set -e
cd "$(dirname "$0")/.."
lake build
cp widget/Penrose.js docs/Penrose.js
lake env lean --run scripts/Props.lean
