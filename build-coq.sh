set -o xtrace
export PATH="$coreutils/bin"
# Copy dependencies...
cp -r $src/deps/* .
chmod -R +w .
$findutils/bin/find .
echo "compiling using $coqc... output is $out in $PWD"
echo -e "\e[32mCOQPATH: $COQPATH\e[0m"
$coqc $incsString $reqsString $inputFile
if [[ -f "${inputFile%.v}.vo" ]]; then
    mkdir -p $out/$(dirname $inputFile)
    cp "${inputFile%.v}.vo" $out
    cp "${inputFile%.v}.vos" $out
    cp "${inputFile%.v}.vok" $out
    cp "${inputFile%.v}.glob" $out
fi
