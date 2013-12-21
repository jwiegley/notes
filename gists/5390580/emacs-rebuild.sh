#!/bin/bash -xe

brew link libxml2

if [[ "$1" == "alt" ]]; then
    STOW_NAME=emacs-mac-alt
    APP_INSTALL_DIR=/Applications
    shift 1
else
    STOW_NAME=emacs-mac
    APP_INSTALL_DIR=/Applications/Misc
fi

INSTALL_DIR=/usr/local/Cellar/$STOW_NAME/HEAD

git clean -dfx
git reset --hard HEAD

if [[ $STOW_NAME == emacs-mac ]]; then
    rm -fr /Applications/Emacs.app
else
    rm -fr /Applications/EmacsAlt.app
fi

test -d $INSTALL_DIR && brew rm $STOW_NAME

INCLUDES=""
INCLUDES="$INCLUDES -I/usr/local/include"
INCLUDES="$INCLUDES -I/usr/local/opt/gnutls/include"
INCLUDES="$INCLUDES -I/usr/local/opt/libxml2/include"
INCLUDES="$INCLUDES -I/usr/local/opt/freetype/include"
INCLUDES="$INCLUDES -I/usr/local/opt/jpeg/include"
INCLUDES="$INCLUDES -I/usr/local/opt/libtiff/include"
INCLUDES="$INCLUDES -I/usr/local/opt/giflib/include"
INCLUDES="$INCLUDES -I/usr/local/opt/libpng/include"
INCLUDES="$INCLUDES -I/usr/local/opt/librsvg/include"
INCLUDES="$INCLUDES -I/usr/local/opt/imagemagick/include"

LIBS=""
LIBS="$LIBS -L/usr/local/lib"
LIBS="$LIBS -L/usr/local/opt/gnutls/lib"
LIBS="$LIBS -L/usr/local/opt/libxml2/lib"
LIBS="$LIBS -L/usr/local/opt/freetype/lib"
LIBS="$LIBS -L/usr/local/opt/jpeg/lib"
LIBS="$LIBS -L/usr/local/opt/libtiff/lib"
LIBS="$LIBS -L/usr/local/opt/giflib/lib"
LIBS="$LIBS -L/usr/local/opt/libpng/lib"
LIBS="$LIBS -L/usr/local/opt/librsvg/lib"
LIBS="$LIBS -L/usr/local/opt/imagemagick/lib"

export PKG_CONFIG_PATH=/usr/local/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/gnutls/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/libxml2/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/freetype/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/jpeg/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/libtiff/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/giflib/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/libpng/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/librsvg/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/usr/local/opt/imagemagick/lib/pkgconfig
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:/opt/X11/lib/pkgconfig

./configure --prefix=$INSTALL_DIR \
    --with-mac --enable-mac-app=$APP_INSTALL_DIR \
    CC=/usr/local/bin/clang CFLAGS=-O3 \
    CPPFLAGS="$INCLUDES" LDFLAGS="-O3 $LIBS"

JOBS=-j$(sysctl hw.ncpu | awk '{print $2}')

nice -n 20 make $JOBS "$@"
make install

if [[ -d $INSTALL_DIR ]]; then
    rm -f $INSTALL_DIR/share/info/dir

    if [[ $STOW_NAME == emacs-mac ]]; then
        brew ln $STOW_NAME
        mv /Applications/Misc/Emacs.app /Applications/Emacs.app
    else
        mv /Applications/Emacs.app /Applications/EmacsAlt.app
    fi
fi

brew unlink libxml2

exit 0
