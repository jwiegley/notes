# Here's the typical Perl solution to editing sshd_config

exec { "permit root logins":
  user    => root,
  command => "perl -i -pe 's/^#?PermitRoot.*/PermitRootLogin without-password/;' $sshd_config",
  unless  => "grep '^PermitRootLogin without-password' $sshd_config";
}

# Here is the exact same thing with Augeas

augeas { 'permit public-key root logins':
  context => '/files/etc/ssh/sshd_config',
  changes => [
    # permit root logins only using publickey
    'set PermitRootLogin without-password',
  ],
  notify  => Service['sshd'];
}
