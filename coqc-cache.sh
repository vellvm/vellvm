#! @shell@
set -eu

COQC_ORIG=@next@/bin/@program@

# if [[ ! -v NIX_REMOTE ]]; then
#     echo -e "\e[31m!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\e[0m"
#     echo -e "\e[31m$0: warning: recursive Nix is disabled\e[0m" >&2
#     echo -e "\e[31m!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\e[0m"

#     exec $COQC_ORIG "$@"
# fi

# I believe the final argument to coqc will be the file we want to
# compile... May also just be able to look for the .v extension.

# coqc -q -w -deprecated-native-compiler-option -native-compiler ondemand -I ../lib/QuickChick/src -I ../lib/QuickChick/plugin -R coq Vellvm -R ../lib/QuickChick/src QuickChick -R ../lib/flocq-quickchick FlocqQuickChick coq/Utils/PropT.v

dest=
inputFile=
compileFlags=()
export includes=()
export requiresPaths=()
export requiresNames=()
reqArgs=""
includeArgs=""
unknownArg=0

args=("$@")

# Collect all of the arguments. Some of these are handled specially,
# and also if we don't recognize any arguments we can default to the
# normal coq compiler.
for ((n = 0; n < $#; n++)); do
    arg="${args[$n]}"

    if [[ $arg = -q || $arg = -w || $arg = -deprecated-native-compiler-option || $arg = -vos || $arg = -vok || $arg = -vio || $arg = -noglob ]]; then
        compileFlags+=("$arg")
    elif [[ $arg = -o ]]; then
        : $((n++))
        dest="${args[$n]}"
    elif [[ $arg = -native-compiler ]]; then
        : $((n++))
        compileFlags+=("$arg" "${args[$n]}")
    elif [[ $arg = -I ]]; then
        : $((n++))
        includes+=("${args[$n]}")
        includeArgs+="-I ${args[$n]} "
    elif [[ $arg = -R ]]; then
        : $((n+=2))
        if [[ ${args[$n]} != "QuickChick" && ${args[$n]} != "FlocqQuickChick" ]]; then
            requiresPaths+=("${args[$n-1]}")
            requiresNames+=("${args[$n]}")
            reqArgs+="-R ${args[$n-1]} ${args[$n]} "
        fi
    elif [[ $arg =~ ^.*\.v ]]; then
        inputFile="$arg"
    elif [[ ! $arg =~ ^- ]]; then
        sources+=("$arg")
    else
        unknownArg=1
    fi
done

if [[ $unknownArg == 1 ]]; then
    echo -e "\e[31m$0: Unknown argument to coqc\e[0m" >&2
    exec $COQC_ORIG "$@"
    exit 0
fi

# TODO / NOTE:
#
# I *think* I need to do a nested nix build here...
#
# I want one nix build to pull this entire source directory into the nix store.
# Then when I'm building from there I can produce my limited directory structure
# (I.e., my dependencies, and list of required / included directories from the
# -R and -I flags...) and do another nix build with those...
#
# This may be somewhat wasteful... Files will get put into the nix
# store multiple times.
#
# Maybe let's just worry about this getting called within the nix
# build itself right now.
#
# NOTE: Actually, maybe we can just use mktemp

# Need to find all required and included directories and put them in the nix store...
# In such a way that they can be referenced later in the args.

# Need to collect all of the dependencies of the coq file and put them
# in the nix store as well...

# TODO: I don't actually want to make this directory whenever this script is called...
# ideally I would be able to use this wrapped coqc when I'm just in a nix shell to get
# cached incremental builds as well, and I don't want this polluting my current directory...
TMP_DIR=$(mktemp -d -p `pwd`)

# check if tmp dir was created
if [[ ! "$TMP_DIR" || ! -d "$TMP_DIR" ]]; then
  echo "Could not create temp dir"
  exit 1
fi

# deletes the temp directory
function cleanup_tmp_dir {
  rm -rf "$TMP_DIR"
  echo "Deleted temp working directory $TMP_DIR"
}

# register the cleanup function to be called on the EXIT signal
trap cleanup_tmp_dir EXIT

find-up () {
  path=$(pwd)
  while [[ "$path" != "" && ! -e "$path/$1" ]]; do
    path=${path%/*}
  done
  echo "$path"
}

mkdir ${TMP_DIR}/deps
DEPS=$(coqdep $reqArgs "$inputFile" -sort)
echo -e "\e[32mDEPS: $DEPS\e[0m"

# Copy dependencies
# rsync takes a long time...
for i in $DEPS; do rsync --ignore-missing-args --quiet -Ravz --no-owner --no-perms "${i}o" ${TMP_DIR}/deps; done
# Make sure we remove the vo file we want to create, if an old version got copied.
rm -f ${TMP_DIR}/deps/${coq-file}o

rsync --quiet -Ravz "$inputFile" ${TMP_DIR}/deps
outputFile=${inputFile%.v}.vo

# Use source file and `deps` directory in a recursive nix build
BUILD=$(@nix@/bin/nix-build -o "$dest.link" -E '(
  derivation rec {
    name = "coqc";
    system = "@system@";
    coqc = builtins.storePath "@next@/bin/@program@";
    builder = builtins.storePath "@shell@";
    coreutils = builtins.storePath "@coreutils@";
    findutils = builtins.storePath "@findutils@";
    src = builtins.path {path='"${TMP_DIR}"'; name = name;};
    quickChick = ../lib/QuickChick/src;
    quickChickPlugin = ../lib/QuickChick/plugin;
    flocqQuickChick = ../lib/flocq-quickchick;
    reqsString = "-R coq Vellvm -R ${quickChick} QuickChick -R ${flocqQuickChick} FlocqQuickChick";
    incsString = "-I ${quickChick} -I ${quickChickPlugin}";
    inputFile = "'"$inputFile"'";
    outputFile = "'"$outputFile"'";
    coqPkgs = builtins.map builtins.storePath [ @coqPkgs@ ];
    COQPATH = builtins.foldl'"'"' (a: b: a + (if a == "" then "" else ":") + b + "/lib/coq/8.15/user-contrib/") "" coqPkgs;
    args = [ @compile_coq@ ];
  }
)')

BUILD_CA=$( @nix@/bin/nix --experimental-features nix-command store make-content-addressed --json "$BUILD" | @jq@/bin/jq -r '.rewrites."'"$BUILD"'"' )

echo "$BUILD"
echo "$BUILD_CA"

cp $BUILD_CA/*\.vo $(dirname $inputFile)
cp $BUILD_CA/*\.vos $(dirname $inputFile)
cp $BUILD_CA/*\.vok $(dirname $inputFile)
cp $BUILD_CA/*\.glob $(dirname $inputFile)
