(lang dune 3.14)
(using coq 0.8)

(name coq-completion)

(generate_opam_files true)

(maintainers "Soichi Yajima <yajima@fos.kuis.kyoto-u.ac.jp")

(package
 (name coq-completion)
 (depends
  (dune (>= 3.6.1))
  (ocaml (>= 4.12.0))
  (coq-stdlib (>= 8.20.0))))
