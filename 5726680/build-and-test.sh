#!/bin/bash -x

cd ~/fpco

do_pull () {
    if which git-smart-pull; then
        git smart-pull
    else
        git pull || (git fetch && tg update)
    fi
}

if [[ "$1" == -u || "$1" == --update ]]; then
    do_pull
    if [ -d learning-site/content ]; then
        (cd learning-site/content; do_pull)
    fi

    git clean -dfx
    ./dev-scripts/update-repo.sh

    find . -name config -type f                 \
        | xargs perl -i -pe                     \
            's%(git|https?)://github.com/(fpco|jwiegley)/%git\@github.com:\2/%;'
    find . -name '*.hs' | xargs hasktags -e -o - > TAGS
fi

set -e

cd ~/build/fpco

if [[ "$1" == -u || "$1" == --update ]]; then
    lndir -silent ~/fpco

    for gitDir in $(cd ~/fpco ; find . -name .git); do
        test -L ~/build/fpco/$gitDir \
            || (rm -fr ~/build/fpco/$gitDir; ln -s ~/fpco/$gitDir ~/build/fpco/$(dirname $gitDir))
    done
fi

./dev-scripts/test-all.sh --ghc-option='-Wall'

(source dev-scripts/activate-hsenv.sh &&                \
 fptest &&                                              \
 cd learning-site &&                                    \
 cabal install -fdev --force-reinstalls --enable-tests)

# dropdb learning_site_production
# createdb learning_site_production -O learning_site

#run-yesod-production.sh
