declare -xp
export PATH="$coreutils/bin"
mkdir $out
$coqc $src -o ${out}/${src%.v}.vo
