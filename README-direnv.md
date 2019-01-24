# Using direnv with Nix

[direnv](https://direnv.net/) makes it easier to swap between Nix projects
without having to use `nix-shell`. It changes your environment automatically
whenever you use `cd`. Paired with
[emacs-direnv](https://github.com/wbolster/emacs-direnv), the same occurs
whenever you switch buffers in Emacs, ensuring that the right dependencies are
in scope depending on the project you're working on.

To use it, you'll first need to put [this
script](https://github.com/jwiegley/nix-config/blob/master/bin/use_nix.sh)
somewhere on your `PATH`. Then, create a file name `.envrc` file in your
project's top directory:

    . $(which use_nix.sh)
    export NIXARGS=(-Q)
    use_nix

Now when you change directory anywhere into your project, you'll have all its
dependencies in scope. You can then use cabal as you normally would to do your
building and testing.

## Rebuilding dependencies

If you change a dependency, you'll need to force a rebuild of the cached
`direnv` environment by simply removing the `.direnv` directory:

    rm -fr <path to your project>/.direnv

It will rebuild and recache the next time you need it -- immediately if you're
current in that directory. Note also that this environment is registered as a
GC root, to protect it from garbage collection.

## Emacs

To setup `emacs-direnv`, you can use something like this in your `init.el`
file, asuming you use the `use-package` macro. This version assumes you aren't
using `flycheck` with `haskell-mode`:

``` lisp
(use-package direnv
  :demand t
  :config
  (direnv-mode)
  :hook
  ((haskell-mode coq-mode) . direnv-update-environment))
```

While this version delays setting up the environment until `flycheck` is
ready:

``` lisp
(use-package direnv
  :demand t
  :config
  (direnv-mode)
  (eval-after-load 'flycheck
    '(setq flycheck-executable-find
           (lambda (cmd)
             (direnv-update-environment default-directory)
             (executable-find cmd))))
  :hook
  (coq-mode . direnv-update-environment))
```
