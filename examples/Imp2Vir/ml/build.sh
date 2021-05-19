#!/usr/bin/env bash
coqtop -q -w none -batch -load-vernac-source extracted/Extract.v -R ../../../src/coq Vellvm -R ../../../lib/InteractionTrees/theories ITree -R ../../../lib/QuickChick/src/ QuickChick -R ../ Imp2Vir -R ../../../lib/InteractionTrees/tutorial tutorial
patch -p1 < ../../../src/CRelationClasses.mli.patch
dune build impinterp.exe
