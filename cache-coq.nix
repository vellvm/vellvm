{ pkgs, coq, src, vofile }:

derivation {
  name = "cache-coq";
  builder = "${pkgs.bash}/bin/bash" ;
  args = [ ./cache-builder.sh ];
  inherit src vofile;
  coreutils = pkgs.coreutils;
  coqc = "${coq}/bin/coqc";
  system = builtins.currentSystem;
}
