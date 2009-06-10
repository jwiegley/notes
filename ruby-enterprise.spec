# Package Maintainer: Increment phusion_release to match latest release available
%define phusion_release	20090610

Summary: Ruby Enterprise Edition (Release %{phusion_release})
Name: ruby-enterprise
Vendor: Phusion.nl
Packager: Adam Vollrath <adam@endpoint.com>
Version: 1.8.6
Release: 5%{dist}
License: GPL 
Group: Development/Languages 
URL: http://www.rubyenterpriseedition.com/
Source0: http://www.rubyenterpriseedition.com/ruby-enterprise-%{version}-%{phusion_release}.tar.gz
BuildRoot: %{_tmppath}/%{name}-%{version}-%{phusion_release}-root-%(%{__id_u} -n)
BuildRequires:	readline readline-devel ncurses ncurses-devel gdbm gdbm-devel glibc-devel autoconf gcc unzip openssl-devel db4-devel byacc
BuildRequires: ruby
%description 
Ruby Enterprise Edition is a server-oriented friendly branch of Ruby which includes various enhancements:
* A copy-on-write friendly garbage collector. Phusion Passenger uses this, in combination with a technique called preforking, to reduce Ruby on Rails applications' memory usage by 33% on average.
* An improved memory allocator called tcmalloc, which improves performance quite a bit.
* The ability to tweak garbage collector settings for maximum server performance, and the ability to inspect the garbage collector's state. (RailsBench GC patch)
* The ability to dump stack traces for all running threads (caller_for_all_threads), making it easier for one to debug multithreaded Ruby web applications.

%prep 
%setup -q -n ruby-enterprise-%{version}-%{phusion_release}

%package rubygems
Summary: The Ruby standard for packaging ruby libraries
Version: 1.3.2
License: Ruby or GPL+
Group: Development/Libraries
Requires: ruby-enterprise >= 1.8
Provides: ruby-enterprise(rubygems) = %{version}

%description rubygems
RubyGems is the Ruby standard for publishing and managing third party
libraries.  This rubygems package is for ruby-enterprise.

%build 
./installer --auto /usr/local --dont-install-useful-gems --destdir $RPM_BUILD_ROOT

%install
# no-op

%clean
rm -rf $RPM_BUILD_ROOT

%files 
%defattr(-,root,root)
%{_prefix}/local/bin/*
%{_prefix}/local/lib/*
%{_prefix}/local/share/man/man1/ruby.1
%doc source/ChangeLog
%doc source/COPYING
%doc source/LEGAL
%doc source/LGPL
%doc source/NEWS
%doc source/README
%doc source/README.EXT
%doc source/ToDo

# rubygems
%exclude %{_prefix}/local/bin/gem
%exclude %{_prefix}/local/lib/ruby/gems
%exclude %{_prefix}/local/lib/ruby/site_ruby/1.8/rubygems*
%exclude %{_prefix}/local/lib/ruby/site_ruby/1.8/ubygems.rb
%exclude %{_prefix}/local/lib/ruby/site_ruby/1.8/rbconfig

%files rubygems
%{_prefix}/local/bin/gem
%{_prefix}/local/lib/ruby/gems
%{_prefix}/local/lib/ruby/site_ruby/1.8/rubygems*
%{_prefix}/local/lib/ruby/site_ruby/1.8/ubygems.rb
%{_prefix}/local/lib/ruby/site_ruby/1.8/rbconfig
%doc rubygems/LICENSE.txt
%doc rubygems/README
%doc rubygems/GPL.txt
%doc rubygems/ChangeLog

%pre
# Do not install if /usr/local/bin/ruby exists and is not provided by an RPM
if ([ -e /usr/local/bin/ruby ] && !(rpm -q --whatprovides /usr/local/bin/ruby >/dev/null)); then
    exit 1
else
    exit 0
fi

%pre rubygems
# Do not install if /usr/local/bin/gem exists and is not provided by an RPM
if ([ -e /usr/local/bin/gem ] && !(rpm -q --whatprovides /usr/local/bin/gem >/dev/null)); then
    exit 1
else
    exit 0
fi

%changelog 
* Tue Jun 10 2009 Adam Vollrath <adam@endpoint.com>
- Updated for release 20090610

* Tue Jun 02 2009 Adam Vollrath <adam@endpoint.com>
- Added check for existing /usr/local/bin/gem
- Added LICENSE and other important document files

* Mon Jun 01 2009 Adam Vollrath <adam@endpoint.com>
- Refactored to use Phusion's installer instead of building from source
- Changed prefix to just /usr/local
- Added check for existing /usr/local/bin/ruby
- Split rubygems into a subpackage

* Sat May 30 2009 Adam Vollrath <adam@endpoint.com>
- Changed Release number convention
- Added tcmalloc support and `make test`

* Tue May 26 2009 Adam Vollrath <adam@endpoint.com>
- Updated for 1.8.6-20090520
- Several small improvements to spec file

* Fri Dec 13 2008 Tim C. Harper <tim.harper@leadmediapartners.com>
- first build of REE package
