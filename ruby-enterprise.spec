Summary: Ruby Enterprise Edition
Name: ruby-enterprise
Vendor: Phusion.nl
Packager: Adam Vollrath <adam@endpoint.com>
Version: 1.8.6
Release: 20090520A
License: GPL 
Group: Applications/System 
URL: http://www.rubyenterpriseedition.com/
Source0: http://rubyforge.org/frs/download.php/57097/ruby-enterprise-%{version}-%{release}.tar.gz
BuildRoot: %{_tmppath}/%{name}-%{version}-%{release}-root-%(%{__id_u} -n)
%description 
Ruby Enterprise Edition is a server-oriented friendly branch of Ruby which includes various enhancements:
* A copy-on-write friendly garbage collector. Phusion Passenger uses this, in combination with a technique called preforking, to reduce Ruby on Rails applications' memory usage by 33% on average.
* An improved memory allocator called tcmalloc, which improves performance quite a bit.
* The ability to tweak garbage collector settings for maximum server performance, and the ability to inspect the garbage collector's state. (RailsBench GC patch)
* The ability to dump stack traces for all running threads (caller_for_all_threads), making it easier for one to debug multithreaded Ruby web applications.

%prep 
%setup -q -n ruby-enterprise-%{version}-%{release}/source

%build 
PREFIX=$RPM_BUILD_ROOT/%{_prefix}/local/ruby-enterprise
./configure --prefix=%{_prefix}/local/ruby-enterprise
make

%install
make DESTDIR=$RPM_BUILD_ROOT install

%clean
rm -rf $RPM_BUILD_ROOT

%files 
%defattr(-,root,root)
%{_prefix}/local/ruby-enterprise

%changelog 
* Tue May 26 2009 Adam Vollrath <adam@endpoint.com>
- Updated for 1.8.6-20090520
- Several small improvements to spec file

* Fri Dec 13 2008 Tim C. Harper <tim.harper@leadmediapartners.com>
- first build of REE package
