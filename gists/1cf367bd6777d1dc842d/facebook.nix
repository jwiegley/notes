{ fetchgit, stdenv, pkgconfig, check, python }:

with stdenv.lib;
stdenv.mkDerivation rec {
  name = "bitlbee-facebook-3.4.1";

  src = fetchgit {
    url = git://github.com/jgeboski/bitlbee-facebook.git;
    rev = "c87650c3bd04a16b125cceb1d7fd8aa9c729143f";
    sha256 = "ede3730455c3c91b2fd612871fa7262bdacd3dff4ba77c5dfbc3c1f0de9b8a34";
  };

  buildInputs = [ pkgconfig python ]
    ++ optional doCheck check;

  configurePhase = "./autogen.sh";

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
