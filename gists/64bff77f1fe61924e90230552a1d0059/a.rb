CAMLDEP -pp src/g_equations.ml4
File "src/g_equations.ml4", line 498, characters 8-15:
Parse error: 'COMMAND' 'EXTEND' uppercase identifier expected after 'VERNAC'
  (in [str_item])
File "src/g_equations.ml4", line 1:
Error: Error while running external preprocessor
Command line: /nix/store/5yzdsj1b2sn9xsljcmk7jsrbynb3rp3i-camlp5-7.05/bin/camlp5o -I /nix/store/mkfpkyp714mjk62ha2sjs5a93byy80xs-ocaml-4.04.2/lib/ocaml -I "/nix/store/msgj0vkw78ng5nbs74y2g682x3h5d05j-coq-8.7.2/lib/coq//grammar" pa_extend.cmo q_MLast.cmo pa_macro.cmo grammar.cma -loc loc -impl 'src/g_equations.ml4' > /private/tmp/nix-build-coq8.7-equations-8.8+alpha.drv-0/ocamlpp14ae5c

CAMLC -c src/equations_common.mli
CAMLOPT -c  src/equations_common.ml
File "src/equations_common.ml", line 177, characters 13-40:
Error: This function has type Term.constr -> Univ.universe_set
       It is applied to too many arguments; maybe you forgot a `;'.
make[1]: *** [Makefile:594: src/equations_common.cmx] Error 2
make: *** [Makefile:319: all] Error 2
builder for '/nix/store/2hfkkxic4qd400sm5csfdhpf3yq8z9sy-coq8.7-equations-8.8+alpha.drv' failed with exit code 2
cannot build derivation '/nix/store/nz6brafp73ydwrn0hq1682y7m30zg26z-env-coqHEAD.drv': 1 dependencies couldn't be built
error: build of '/nix/store/nz6brafp73ydwrn0hq1682y7m30zg26z-env-coqHEAD.drv' failed
