export PATH="$coreutils/bin"
# Copy dependencies...
cp --reflink=auto -r $src/deps/* .
chmod -R +w .
$coqc $incsString $reqsString $inputFile
if [[ -f "${inputFile%.v}.vo" ]]; then
    mkdir -p $out/$(dirname $inputFile)
    install -m 644 "${inputFile%.v}.vo" $out
    install -m 644 "${inputFile%.v}.vos" $out
    install -m 644 "${inputFile%.v}.vok" $out
    install -m 644 "${inputFile%.v}.glob" $out
fi
