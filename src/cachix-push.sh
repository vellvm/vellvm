#!/bin/bash

nix build -L ".?submodules=1" -o vellvm-build
cachix push vellvm vellvm-build

nix develop --profile dev-shell -c echo "Done building dev shell"
cachix push vellvm dev-shell
