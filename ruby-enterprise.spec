# Package Maintainer: Increment phusion_release to match latest release available
%define phusion_release	20090520

Summary: Ruby Enterprise Edition
Name: ruby-enterprise
Vendor: Phusion.nl
Packager: Adam Vollrath <adam@endpoint.com>
Version: 1.8.6
# Our release convention is based on Phusion's
Release: 2009060101%{dist}
License: GPL 
Group: Applications/System 
URL: http://www.rubyenterpriseedition.com/
Source0: http://rubyforge.org/frs/download.php/57097/ruby-enterprise-%{version}-%{phusion_release}.tar.gz
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

%changelog 
* Mon Jun 01 2009 Adam Vollrath <adam@endpoint.com>
- Refactored to use Phusion's installer instead of building from source
- Changed prefix to just /usr/local

* Sat May 30 2009 Adam Vollrath <adam@endpoint.com>
- Changed Release number convention
- Added tcmalloc support and `make test`

* Tue May 26 2009 Adam Vollrath <adam@endpoint.com>
- Updated for 1.8.6-20090520
- Several small improvements to spec file

* Fri Dec 13 2008 Tim C. Harper <tim.harper@leadmediapartners.com>
- first build of REE package
