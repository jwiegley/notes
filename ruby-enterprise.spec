Summary: Ruby Enterprise Edition
Name: ruby-enterprise
Version: 1.8.6
Release: 20090421
License: GPL 
Group: Applications/System 
Source: ruby-enterprise-%{version}-%{release}.tar.gz
BuildRoot: /var/tmp/%{name}-%{version}-%{release} 
%description 
Ruby Enterprise Edition is a copy-on-wright friendly version of ruby that also 
includes several performance patches.

%prep 
%setup -q -n ruby-enterprise-%{version}-%{release}/source

%build 
./configure --prefix=/opt/ree

%install 
make
make DESTDIR=$RPM_BUILD_ROOT install

%files 
%defattr(-,root,root)
/opt/ree

%changelog 
* Fri Dec 13 2008 Tim C. Harper <tim.harper@leadmediapartners.com>
- first build of REE package
