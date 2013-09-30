#!/bin/bash -x

do_pull () {
    if which git-smart-pull; then
        git smart-pull
    else
        git pull
    fi
}

if [[ "$1" == -u || "$1" == --update ]]; then
    do_pull
    if [ -d learning-site/content ]; then
        (cd learning-site/content; do_pull)
    fi

    ./dev-scripts/update-repo.sh

    find . -name config -type f                 \
        | xargs perl -i -pe                     \
            's%(git|https?)://github.com/(fpco|jwiegley)/%git\@github.com:\2/%;'
    find . -name branches -prune -o -name '*.hs' | xargs hasktags -e -o - > TAGS
fi

set -e

if [[ "$1" == --reset ]]; then
    git clean -dfx
    (cd gitlib; git clean -dfx)

    ./dev-scripts/build-all.sh || echo expected failure
    # echo "documentation: True" >> .hsenvs/ghc-7.4.2.9/.hsenv/cabal/config

    (source .hsenvs/ghc-7.4.2.9/.hsenv/bin/activate; \
        cd dev-scripts/fpbuild; cabal install)

    git annex enableremote s3
    (cd learning-site/tests/selenium; \
     git annex get selenium-server-standalone-2.33.0.jar)

    ./dev-scripts/clean-all.sh
    find . -name dist -print0 | xargs -0 /bin/rm -fr

    dropdb learning_site_test
    createdb learning_site_test -O learning_site

    build-and-test --update || echo expected failure
    (source .hsenvs/ghc-7.4.2.9/.hsenv/bin/activate; \
        DYLD_LIBRARY_PATH=/usr/local/opt/icu4c/lib cabal install -j1 text-icu --extra-include-dirs=/usr/local/opt/icu4c/include --extra-lib-dirs=/usr/local/opt/icu4c/lib --reinstall doctest doctest-prop simple-reflect hdevtools MonadCatchIO-mtl)
    build-and-test --update
fi

./dev-scripts/build-all.sh
(source dev-scripts/activate-hsenv.sh && fptest)
