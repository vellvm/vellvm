(lang dune 2.8)
(using coq 0.2)
(using menhir 2.0)

(name coq-vellvm)

(license "GPLv3")
(authors "Calvin Beck" "Irene Yoon" "Yannick Zakowski" "Steve Zdancewic")
(maintainers "Calvin Beck" "Irene Yoon" "Yannick Zakowski" "Steve Zdancewic")
(source (uri "vellvm.org"))
(bug_reports "https://github.com/vellvm/vellvm/issues")

(generate_opam_files true)

(package
 (name coq-vellvm)
 (synopsis "Formalization of the LLVM intermediate representation")
 (version 1.0)
 (depends
  (coq (>= 8.15))
  (coq-itree (>= 4.0.0))
  (coq-paco (>= 4.1.2))
  (coq-ceres (>= 0.4.0))
  (coq-extlib (>= 0.11.6))
  (coq-flocq (>= 4.0.0))
  (dune (>= 2.0))
  (menhir  (>= 20211230))
  (qcheck (>= 0.18.1))
 )
)

