define i64 @main(i64 %argc, i8** %arcv) {
  %1 = icmp eq i64 2, %argc
  br i1 %1, label %left, label %right

left:
  br label %merge

right:
  br label %merge

merge:
  %z = phi i64 [ 100, %left ], [ 200, %left ]
  ret i64 %z
}

; warning: overriding the module target triple with x86_64-apple-macosx10.11.0 [-Woverride-module]
; clang: error: unable to execute command: Segmentation fault: 11
; clang: error: clang frontend command failed due to signal (use -v to see invocation)
; Apple LLVM version 7.3.0 (clang-703.0.31)
; Target: x86_64-apple-darwin15.6.0
; Thread model: posix
; InstalledDir: /Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin
; clang: note: diagnostic msg: PLEASE submit a bug report to http://developer.apple.com/bugreporter/ and include the crash backtrace, preprocessed source, and associated run script.
; clang: note: diagnostic msg: Error generating preprocessed source(s) - no preprocessable inputs.
