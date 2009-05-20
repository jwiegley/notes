Summary: Ruby Enterprise Edition
Name: ruby-enterprise
Version: 1.8.6
Release: 20090421
License: GPL 
Group: Applications/System 
URL: http://www.rubyenterpriseedition.com/
Source0: http://rubyforge.org/frs/download.php/55511/ruby-enterprise-%{version}-%{release}.tar.gz
BuildRoot: /var/tmp/%{name}-%{version}-%{release} 
%description 
Ruby Enterprise Edition is a server-oriented friendly branch of Ruby which includes various enhancements:
* A copy-on-write friendly garbage collector. Phusion Passenger uses this, in combination with a technique called preforking, to reduce Ruby on Rails applications' memory usage by 33% on average.
* An improved memory allocator called tcmalloc, which improves performance quite a bit.
* The ability to tweak garbage collector settings for maximum server performance, and the ability to inspect the garbage collector's state. (RailsBench GC patch)
* The ability to dump stack traces for all running threads (caller_for_all_threads), making it easier for one to debug multithreaded Ruby web applications.

%prep 
%setup -q -n ruby-enterprise-%{version}-%{release}/source

%build 
./configure --prefix=/usr/local/ruby-enterprise
make

%install 
make DESTDIR=$RPM_BUILD_ROOT install

%files 
%defattr(-,root,root)
/usr/local/ruby-enterprise

%changelog 
* Fri Dec 13 2008 Tim C. Harper <tim.harper@leadmediapartners.com>
- first build of REE package
