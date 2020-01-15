Firefox = self.installApplication rec {
  name = "Firefox";
  version = "71.0";
  sourceRoot = "Firefox.app";
  src = super.fetchurl {
    name = "Firefox-${version}.dmg";
    url = "https://download-installer.cdn.mozilla.net/pub/firefox/releases/${version}/mac/en-US/Firefox%20${version}.dmg";
    sha256 = "1227vh040a24g335df5zz23s2wql9n57hi5kp8snk1y3rdnx5v2b";
  };
  postInstall = ''
    for file in  \
        $out/Applications/Firefox.app/Contents/MacOS/firefox \
        $out/Applications/Firefox.app/Contents/MacOS/firefox-bin
    do
        dir=$(dirname "$file")
        base=$(basename "$file")
        mv $file $dir/.$base

        cat > $file <<'EOF'
#!/bin/bash
export PATH=${self.gnupg}/bin:${self.pass}/bin:$PATH
export PASSWORD_STORE_ENABLE_EXTENSIONS="true"
export PASSWORD_STORE_EXTENSIONS_DIR="/run/current-system/sw/lib/password-store/extensions";
export PASSWORD_STORE_DIR="$HOME/Documents/.passwords";
export GNUPGHOME="$HOME/.config/gnupg"
export GPG_TTY=$(tty)
if ! pgrep -x "gpg-agent" > /dev/null; then
${self.gnupg}/gpgconf --launch gpg-agent
fi
dir=$(dirname "$0")
name=$(basename "$0")
exec "$dir"/."$name" "$@"
EOF
        chmod +x $file
    done
  '';
  description = "The Firefox web browser";
  homepage = https://www.mozilla.org/en-US/firefox/;
};
