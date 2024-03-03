QCTEMPDIR=$(cat temp_dir)
echo "$QCTEMPDIR"
MRDIR=$(find $QCTEMPDIR -maxdepth 1 -mindepth 1 -type d -exec stat -f '%m %N' {} \; | sort -nr | head -n 1 | awk '{print $2}')
echo "$MRDIR"
QCTESTFILE=$(find $MRDIR -maxdepth 1 -mindepth 1 -type f -name "QuickChick*.ml"| head -n 1)
QCTEST="${QCTESTFILE%.ml}"
echo "$QCTESTFILE"
echo "$QCTEST"
ocamlfind opt -linkpkg -package bisect_ppx -linkpkg -package zarith -I $MRDIR/extracted -I $MRDIR/libvellvm -I $MRDIR/_build $QCTESTFILE -w - -linkall -o $MRDIR/test
$MRDIR/test
COVERAGEFILE=$(find ./ -maxdepth 1 -mindepth 1 -type f -name "*.coverage" | head -n 1)
mv $COVERAGEFILE $MRDIR
bisect-ppx-report summary --coverage-path=$MRDIR
bisect-ppx-report html --coverage-path=$MRDIR
LOCALCOVERAGE=$(find ./ -maxdepth 1 -mindepth 1 -type d -name "_coverage" | head -n 1)
mv -r $LOCALCOVERAGE $MRDIR
open $MRDIR/_coverage/index.html
# bisect-ppx-report html "$QCTEST.coverage"
# open -a “Google Chrome” $MRDIR/_coverage/index.html
