(lang dune 3.24)

(name mmlp)

(generate_opam_files true)

(source
 (github kenjitokuo/mmlp))

(authors "Kenji Tokuo <tokuo@oita-ct.ac.jp>")

(maintainers "Kenji Tokuo <tokuo@oita-ct.ac.jp>")

(license MIT)

(documentation https://github.com/kenjitokuo/mmlp)

(package
 (name mmlp)
 (synopsis "Multimodal logic programming with full formulas")
 (description "An OCaml implementation of multimodal logic programming with full first-order formulas")
 (depends ocaml)
 (tags
  ("logic-programming" "modal-logic" "proof-search" "ocaml")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
