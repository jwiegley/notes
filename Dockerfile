FROM lnl7/nix:2.0

WORKDIR /tmp/build
COPY . /tmp/build

RUN nix-env --arg nixpkgs 'import <nixpkgs> {}' -f . -i tar

# Install all dependencies into its own layer, which doesn't change. Make sure
# to use the nixpkgs provided by nix-docker, rather than what the project is
# otherwise pinned to.
RUN nix-shell -Q -j2 --run true

RUN nix-env -f . -i hnix

CMD ["hnix"]
