{ fetchgit, stdenv, pkgconfig, check, python, autoconf, automake, libtool
, fetchurl, gcc }:

with stdenv.lib;
stdenv.mkDerivation rec {
  name = "bitlbee-facebook-3.4.1";

  src = fetchgit {
    url = git://github.com/jgeboski/bitlbee-facebook.git;
    rev = "c87650c3bd04a16b125cceb1d7fd8aa9c729143f";
    sha256 = "0lhxc6bdv7xz90436h0amdvjhic3lyxkxbd9601mklmqziag2w40";
  };

  bitlbee_src = fetchurl {
    url = "mirror://bitlbee/src/bitlbee-3.2.2.tar.gz";
    sha256 = "13jmcxxgli82wb2n4hs091159xk8rgh7nb02f478lgpjh6996f5s";
  };

  buildInputs = [ pkgconfig python autoconf automake libtool gcc ]
    ++ optional doCheck check;

  configurePhase = ''
    set -x
    export BITLBEE_CFLAGS="-I${bitlbee_src}/include/bitlbee"
    export BITLBEE_LIBS=""
    export PKG_CONFIG_PATH="$PKG_CONFIG_PATH:${bitlbee_src}"
    ./autogen.sh --with-plugindir=$out/lib/bitlbee/plugins
  '';

  doCheck = true;

  meta = {
    description = "Facebook plugin for Bitlbee";

    longDescription = ''
      BitlBee brings IM (instant messaging) to IRC clients.  It's a
      great solution for people who have an IRC client running all the
      time and don't want to run an additional MSN/AIM/whatever
      client.

      BitlBee currently supports the following IM networks/protocols:
      XMPP/Jabber (including Google Talk), MSN Messenger, Yahoo!
      Messenger, AIM and ICQ.
    '';

    homepage = http://www.bitlbee.org/;
    license = licenses.gpl2Plus;

    maintainers = with maintainers; [ wkennington pSub ];
    platforms = platforms.gnu;  # arbitrary choice
  };
}
