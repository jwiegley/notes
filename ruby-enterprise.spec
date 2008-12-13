Summary: Ruby Enterprise Edition
Name: ruby-enterprise
Version: 1.8.6
Release: 20081205
License: GPL 
Group: Applications/System 
Source: ruby-enterprise-%{version}-%{release}.tar.gz
BuildRoot: /var/tmp/%{name}-root 
%description 
%prep 
%setup -q 
%build 
%configure 
make 
%install 
rm -rf %{buildroot} 
%makeinstall 
%clean 
rm -rf %{buildroot} 
%files 
%defattr(-,root,root) 
# /etc/init.d/foo 
# %{_sbindir}/foo 
# /usr/share/man/man8/foo.8 
%defattr(-,root,root) 
# /usr/include/foo.h 
# /usr/lib/foo.a 
%changelog 

