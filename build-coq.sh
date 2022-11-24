set -o xtrace
export PATH="$coreutils/bin"
mkdir $out
echo "compiling using $coqc... output is $out"
echo -e "\e[32mCOQPATH: $COQPATH\e[0m"
$coqc $reqsString $incsString $inputFile -o $out/$outputFile
