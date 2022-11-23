coq-file:

# Copy dependencies and call recursive nix build
# Eventually this should be the wrapped coqc
runCommand "compile-coq-preparing-dependencies"
  {
    buildInputs = [ rsync nix coq jq ]; # Copy environment?
    src = .;
    requiredSystemFeatures = [ "recursive-nix" ];
    # Do I need NIX_PATH?
  }
''
  mkdir deps
  # Fetch dependencies
  DEPS=$(coqdep -R $src/coq Vellvm $src/${coq-file} -sort)

  # Copy dependencies
  for i in $DEPS; do rsync --quiet -Ravz "${i}o" deps; done
  # Make sure we remove the vo file we want to create, if an old version got copied.
  rm -f deps/${coq-file}o

  # Use source file and `deps` directory in a recursive nix build
  BUILD=$( nix-build -E 'import ${ ./compile-coq.nix } ./deps "$src/${coq-file}"' )
  BUILD_CA=$( nix --experimental-features nix-command store make-content-addressable --json "$BUILD" | jq -r '.rewrites."'"$BUILD"'"' )

  # Clean up dependencies
  rm -r deps

  # Copy output from building coq file
  mkdir $out
  cp -r "$BUILD_CA"/* $out/
''
