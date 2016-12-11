In your `nixpkgs` checkout:

    git reset --hard $(curl -s http://ftp.newartisans.com/pub/nix-binary-cache/commit.txt)

In ~/.nix/nix.conf:

    binary-caches = http://ftp.newartisans.com/pub/nix-binary-cache
    signed-binary-caches = *
    binary-cache-public-keys = cache.newartisans.com:Vj2SR5/NwnD4NKUoNaZGRrwam7zAA0/XEVYLON9KcWY=
    
I have 7000+ packages built, although a few of them have custom modifications as given in my [`config.nix`](https://github.com/jwiegley/nix-config/blob/master/config.nix) file.