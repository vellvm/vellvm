export PATH="$coreutils/bin"
# Copy dependencies...
cp --reflink=auto -r $src/deps/* .
chmod -R +w .
$coqc $incsString $reqsString $inputFile
if [[ -f "${inputFile%.v}.vo" ]]; then
    mkdir -p $out/$(dirname $inputFile)
    cp "${inputFile%.v}.vo" $out
    cp "${inputFile%.v}.vos" $out
    cp "${inputFile%.v}.vok" $out
    cp "${inputFile%.v}.glob" $out
fi
