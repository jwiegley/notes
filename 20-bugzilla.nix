self: super: with super; with super.perlPackages; rec {

  dbdModule = DBDmysql;

  ApacheSizeLimit = buildPerlPackage rec {
    name = "Apache-SizeLimit-0.97";
    src = fetchurl {
      url = "mirror://cpan/authors/id/P/PH/PHRED/${name}.tar.gz";
      sha256 = "0dnncki6qy7vxwcrjpd0lfskkcb1zvyc9zs70g1ihfc3hayxyks8";
    };
    buildInputs = [apacheHttpdPackages.mod_perl];
  };

  LinuxPid = buildPerlPackage rec {
    name = "Linux-Pid-0.04";
    src = fetchurl {
      url = "mirror://cpan/authors/id/R/RG/RGARCIA/${name}.tar.gz";
      sha256 = "f2ac2444a74e762783bbd36c486352f96340434d34ae7926d6ab234966540f49";
    };
  };

  DaemonGeneric = buildPerlPackage rec {
    name = "Daemon-Generic-0.85";
    src = fetchurl {
      url = "mirror://cpan/authors/id/M/MU/MUIR/modules/${name}.tar.gz";
      sha256 = "03whvw00w7a1lh5agpjqdsycmfy753gpl5741vs4wjfwdf7gzhrs";
    };
    buildInputs = [FileFlock FileSlurp];
    doCheck = false;
  };

  FileFlock = buildPerlPackage rec {
    name = "File-Flock-2014.01";
    src = fetchurl {
      url = "mirror://cpan/authors/id/M/MU/MUIR/modules/${name}.tar.gz";
      sha256 = "1lj1ybviarfhafsai4y771pzaf52j8284iqy3wkgid5y1n4xgiax";
    };
    buildInputs = [AnyEvent DataStructureUtil FileSlurp IOEvent TestSharedFork];
    doCheck = false;
  };

  IOEvent = buildPerlPackage rec {
    name = "IO-Event-0.813";
    src = fetchurl {
      url = "mirror://cpan/authors/id/M/MU/MUIR/modules/${name}.tar.gz";
      sha256 = "1dvk7wsmpj32f9bpw6150426lgjr41m47q5nvy5p0v8mg786bgj3";
    };
    buildInputs = [ ListMoreUtils ];
  };

  JSONRPC = buildPerlModule rec {
    name = "JSON-RPC-1.06";
    src = fetchurl {
      url = "mirror://cpan/authors/id/D/DM/DMAKI/${name}.tar.gz";
      sha256 = "0mw75f5gh7vhyfzhidvkmbway6hgbyjn5zqjzbgkz2wqb2sshnyp";
    };
    buildInputs = [CGI ClassAccessorLite HTTPMessage HTTPMessage JSON libwwwperl Plack RouterSimple];
  };

  RouterSimple = buildPerlModule rec {
    name = "Router-Simple-0.17";
    src = fetchurl {
      url = "mirror://cpan/authors/id/T/TO/TOKUHIROM/${name}.tar.gz";
      sha256 = "17f8n07qnzbka5yv5r8h2sx0795hv3dz5nyc41bf3viq1xi1aiik";
    };
    buildInputs = [ ClassAccessorLite ];
  };

  TestTaint = buildPerlPackage rec {
    name = "Test-Taint-1.06";
    src = fetchurl {
      url = "mirror://cpan/authors/id/P/PE/PETDANCE/${name}.tar.gz";
      sha256 = "01rip5d7gdr1c7lq6yczzkqfd0500nfa977ryigylj6jj75526vj";
    };
  };

  XMLRPCLite = buildPerlPackage rec {
    name = "XMLRPC-Lite-0.717";
    src = fetchurl {
      url = "mirror://cpan/authors/id/P/PH/PHRED/${name}.tar.gz";
      sha256 = "0925md6jhzgpsibwgny4my461b2wngm8dhxlcry8pbqzrgrab7rs";
    };
    buildInputs = [SOAPLite];
  };

  libwwwperl = buildPerlPackage rec {
    name = "libwww-perl-6.31";
    src = fetchurl {
      url = "mirror://cpan/authors/id/E/ET/ETHER/${name}.tar.gz";
      sha256 = "1qyaxvj9px2pna1rpzgw9cmblp5rp86dvsd0m1yis74xsf356paj";
    };
    buildInputs = [EncodeLocale FileListing HTMLParser HTMLParser HTTPCookies HTTPDaemon HTTPDate HTTPNegotiate HTTPMessage HTTPMessage HTTPMessage HTTPMessage LWPMediaTypes NetHTTP TryTiny URI URI WWWRobotRules];
    doCheck = false;
  };

  TextMultiMarkdown = buildPerlPackage rec {
    name = "Text-MultiMarkdown-1.000035";
    src = fetchurl {
      url = "mirror://cpan/authors/id/B/BO/BOBTFISH/${name}.tar.gz";
      sha256 = "0sk4a95jvxzx0kpd67iaykyk08cmcbkj82w8gjfrghhxfl9xsrr4";
    };
    buildInputs = [HTMLParser TextMarkdown TestException ListMoreUtils TextDiff];
  };

  ClassTrigger = buildPerlPackage rec {
    name = "Class-Trigger-0.14";
    src = fetchurl {
      url = "mirror://cpan/authors/id/M/MI/MIYAGAWA/${name}.tar.gz";
      sha256 = "1i7biadq1pbpdxr77gyicf4qpbbw2mpg3z5202771q31qnn4a7kb";
    };
  };

  DataObjectDriver = buildPerlModule rec {
    name = "Data-ObjectDriver-0.15";
    src = fetchurl {
      url = "mirror://cpan/authors/id/S/SI/SIXAPART/${name}.tar.gz";
      sha256 = "1mj8jrjbqzdrsk78xar1kkg0nbcyd3c99spb36fds50rmlwycp7a";
    };
    buildInputs = [ ModuleBuildTiny TestException];
    propagatedBuildInputs = [ClassAccessor ClassDataInheritable ClassTrigger DBI];
  };

  TheSchwartz = buildPerlModule rec {
    name = "TheSchwartz-1.12";
    src = fetchurl {
      url = "mirror://cpan/authors/id/J/JF/JFEARN/${name}.tar.gz";
      sha256 = "1yl5j864xyd106dacx2j0a6a7nggdbprczh1b46kzvc8lz6x8aad";
    };
    propagatedBuildInputs = [DataObjectDriver];
  };

  BSDResource = buildPerlPackage rec {
    name = "BSD-Resource-1.2911";
    src = fetchurl {
      url = "mirror://cpan/authors/id/J/JH/JHI/${name}.tar.gz";
      sha256 = "0g8c7825ng2m0yz5sy6838rvfdl8j3vm29524wjgf66ccfhgn74x";
    };
  };

  FCGI = buildPerlPackage rec {
    name = "FCGI-0.78";
    src = fetchurl {
      url = "mirror://cpan/authors/id/E/ET/ETHER/${name}.tar.gz";
      sha256 = "1cxavhzg4gyw4gl9kirpbdimjr8gk1rjc3pqs3xrnh1gjybld5xa";
    };
  };

  FCGIDaemon = buildPerlPackage rec {
    name = "FCGI-Daemon-0.20151226";
    src = fetchurl {
      url = "mirror://cpan/authors/id/O/ON/ONLYJOB/${name}.tar.gz";
      sha256 = "0352xs3dlkabrdyfscilb2gn7nwihs83p5i9f9r5sp2bjklbh2s9";
    };
    propagatedBuildInputs = [BSDResource FCGI FCGIProcManager];
  };

  FCGIProcManager = buildPerlPackage rec {
    name = "FCGI-ProcManager-0.28";
    src = fetchurl {
      url = "mirror://cpan/authors/id/A/AR/ARODLAND/${name}.tar.gz";
      sha256 = "03j20jdm53mzjw2pbiyk2c3ci3jy0br0h00y0mg1fyj28b05ijg1";
    };
  };

bugzilla_5_0_3 = stdenv.mkDerivation rec {
  name = "bugzilla-${version}";
  version = "5.0.3";

  src = ./bugzilla/bugzilla.tar.xz;

  buildInputs = [ perl mysql patchutils ]
    ++ (with perlPackages; [
    ExtUtilsMakeMaker
    PodChecker
    TestPodCoverage
    Test2Suite
    TestMore
    TimeDate
    PerlCritic
  ]);

  propagatedBuildInputs = with perlPackages; [
    # Required modules
    CGI
    CPANMetaRequirements
    DBI
    dbdModule
    EmailDateFormat
    DateTime
    DateTimeTimeZone
    DigestSHA
    EmailMIME
    EmailSender
    FileSlurp
    HTMLElementExtended
    HTMLFormatTextWithLinks
    HTMLFormatter
    JSONXS
    ListMoreUtils
    MathRandomISAAC
    ModuleMetadata
    ModuleRuntime
    Safe
    TemplateToolkit
    URI
  ] ++ [
    AuthenRadius
    AuthenSASL
    CGIEmulatePSGI
    CPANMetaRequirements
    CacheMemcached
    Chart
    DaemonGeneric
    EmailReply
    # EncodeDetect
    FileCopyRecursive
    FileMimeInfo
    FileWhich
    GDGraph
    GDText
    HTMLFormatTextWithLinks
    HTMLParser
    HTMLScrubber
    HTTPMessage
    IOstringy
    JSON
    JSONRPC
    LinuxPid
    LWPUserAgent
    MIMETools
    ModuleMetadata
    ModuleRuntime
    NetLDAP
    NetSMTPSSL
    PatchReader
    SOAPLite
    TemplateGD
    TestTaint
    TextMultiMarkdown
    TheSchwartz
    XMLRPCLite
    XMLTwig
    ApacheSizeLimit
    #apacheHttpdPackages.mod_expires
    apacheHttpdPackages.mod_perl
    #apacheHttpdPackages.mod_rewrite
  ];

  buildPhase = ''
    mkdir db
    mkdir -p local/lib/perl5

    mysql_install_db --basedir=${pkgs.mysql} --datadir=$PWD/db
    mysqld --port=17394 --skip-grant-tables \
        --basedir=${pkgs.mysql} \
        --datadir=$PWD/db --pid-file=$PWD/mysqld.pid \
        --socket=$PWD/mysqld.sock &
    sleep 10

    perl checksetup.pl --verbose
    perl -i -pe "s%db_sock = \'\'%db_sock = 'mysqld.sock'%;" localconfig
    perl -i -pe "s%db_user = \'\'%db_user = 'bugs'%;" localconfig
    substituteInPlace localconfig --replace "apache" "users"

    echo "\$answer{'ADMIN_EMAIL'} = 'root@localhost.com';" > install_options
    echo "\$answer{'ADMIN_PASSWORD'} = 'bugsbugsbugs';" >> install_options
    echo "\$answer{'ADMIN_REALNAME'} = 'Bugs';" >> install_options

    perl checksetup.pl --verbose install_options

    # kill $(< $out/mysqld.pid)

    substituteInPlace localconfig \
      --replace "\$db_driver = '.*'" "\$db_driver = 'mysql'" \
      --replace "\$db_host = '.*'" "\$db_host = 'localhost'" \
      --replace "\$db_name = '.*'" "\$db_name = 'bugs'" \
      --replace "\$db_user = '.*'" "\$db_user = 'bugs'" \
      --replace "\$db_sock = '.*'" "\$db_sock = '/run/mysqld/mysqld.sock'" \
      --replace "apache" "users"

    echo "use lib qw($(echo $PERL5LIB | sed 's/:/ /g')); 1;" > perl5lib.pl
  '';

  installPhase = ''
    rm -fr data
    ln -sf /run/bugzilla data

    mkdir -p $out
    cp -pR * $out
  '';

  meta = with stdenv.lib; {
    description = "Bugzilla is server software designed to help you manage software development";
    homepage = https://www.bugzilla.org;
    license = licenses.mpl20;
    maintainers = with maintainers; [ jwiegley ];
    platforms = platforms.unix;
  };
};

bugzilla_conf = ''
server {
    listen       208.82.99.78:80;
    listen       [2607:f2e0:f:712::4]:80;

    server_name  bugs.ledger-cli.org;

    access_log   /var/log/httpd/bugzilla.access_log;
    error_log    /var/log/httpd/bugzilla.error_log;

    index index.cgi;

    ## Compression
    gzip              on;
    gzip_buffers      16 8k;
    gzip_comp_level   4;
    gzip_http_version 1.0;
    gzip_min_length   1280;
    gzip_types        text/plain text/css application/x-javascript text/xml application/xml application/xml+rss text/javascript image/x-icon image/bmp;
    gzip_vary         on;

    location ~ ^/(apple-touch-icon(-120x120|-152x152)?(-precomposed)?\.png|atom\.xml|favicon\.ico|robots\.txt|wp-login\.php)$ {
        allow all;
        log_not_found off;
        access_log off;
    }

    location / {
        proxy_pass         http://127.0.0.1:8080;
        proxy_redirect     off;

        proxy_set_header   Host             $host;
        proxy_set_header   X-Real-IP        $remote_addr;
        proxy_set_header   X-Forwarded-For  $proxy_add_x_forwarded_for;

        proxy_max_temp_file_size 0;

        client_max_body_size       10m;
        client_body_buffer_size    128k;

        proxy_connect_timeout      90;
        proxy_send_timeout         90;
        proxy_read_timeout         90;

        proxy_buffer_size          4k;
        proxy_buffers              4 32k;
        proxy_busy_buffers_size    64k;
        proxy_temp_file_write_size 64k;
    }
}
'';

bugzillaEnv = pkgs.buildEnv {
  name = "bugzilla-web";
  paths = [ bugzilla_5_0_3 mysql apacheHttpd apacheHttpdPackages.mod_perl ] ++ (with perlPackages; [
    AuthenRadius
    AuthenSASL
    CacheMemcached
    Carp
    CGI
    CGIEmulatePSGI
    Chart
    CPANMetaRequirements
    DaemonGeneric
    DateTime
    DateTimeTimeZone
    DBDmysql
    DBI
    EmailDateFormat
    EmailMIME
    EmailReply
    EmailSender
    EncodeDetect
    FCGIDaemon
    FileCopyRecursive
    FileMimeInfo
    FileSlurp
    FileWhich
    GDGraph
    GDText
    HTMLElementExtended
    HTMLFormatter
    HTMLFormatTextWithLinks
    HTMLParser
    HTMLScrubber
    HTTPMessage
    IOstringy
    JSON
    JSONRPC
    JSONXS
    ListMoreUtils
    LWPUserAgent
    MathRandomISAAC
    MIMEtools
    ModuleMetadata
    ModuleRuntime
    NetLDAP
    NetSMTPSSL
    PatchReader
    Plack
    Safe
    SOAPLite
    TemplateGD
    TemplateToolkit
    TestTaint
    TextMultiMarkdown
    TheSchwartz
    URI
    XMLTwig
    XMLRPCLite
  ]);
};

}
