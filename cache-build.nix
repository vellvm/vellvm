{
  cache-coq-overlay = final: prev: {
    cache-coq = final.runCommand "cache-coq"
      { next = final.coq_8_15;
        nix = final.nix;
        coreutils = final.coreutils;
        jq = final.jq;
        requiredSystemFeatures = [ "recursive-nix" ];
      }
      ''
      mkdir -p $out/bin

      substitute ${./coqc-cache.sh} $out/bin/coqc-cache \
        --subst-var-by next $next \
        --subst-var-by program coqc \
        --subst-var shell \
        --subst-var nix \
        --subst-var system \
        --subst-var coreutils \
        --subst-var jq \
        --subst-var-by compile_coq ${./build-coq.sh}

      chmod +x $out/bin/coqc-cache
      '';
  };
}
