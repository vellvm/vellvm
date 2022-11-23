coq: deps: coq-file: reqsString: incsString:

with import <nixpkgs> {};

runCommand "compile-coq" { buildInputs = [ coq ]; }
''
  cd "${ deps }"
  ${coq} ${reqsString} ${incsString} ${ coq-file }
  mkdir $out
  cp *\.vo $out
  cp *\.vos $out
  cp *\.vok $out
  cp *\.vio $out
  cp *\.glob $out
''
