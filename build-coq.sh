set -o xtrace
export PATH="$coreutils/bin"
mkdir $out
echo "compiling using $coqc... output is $out"
$coqc $reqsString $incsString $inputFile -o $out/$outputFile
