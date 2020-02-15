(lang dune 2.0)
(name tt)
(source (github mjustus/tt))
(license BSD-3-clause)

(generate_opam_files true)

(package
 (name tt)
 (synopsis "Pure MLTT type checker using well-scoped de Bruijn indices")
 (depends
  (ocaml (>= 4.08.0))
  (sedlex (>= 2.2))
  (menhir (>= 20181026))
  pprint
  cmdliner
  prelude)
)
(using menhir 2.0)

