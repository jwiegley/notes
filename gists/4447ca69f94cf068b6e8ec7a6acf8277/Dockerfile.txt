# Dockerfile

FROM debian:wheezy

# Install packages required to add users and install Nix
RUN apt-get update
RUN apt-get install -y curl bzip2 adduser perl python git

# Add the user rings for security reasons and for Nix
RUN adduser --disabled-password --gecos '' rings

# Nix requires ownership of /nix.
RUN mkdir -m 0755 /nix && chown rings /nix

# Copy in the RINGS repository, working around a possible AUFS bug
# (see https://github.com/docker/docker/issues/7511)
COPY . /tmp/rings
WORKDIR /tmp/rings
RUN find lib vignettes \( -name '*.glob' \
           -o -name '*.v.d' \
           -o -name '*.vo' \
           -o -name '*.hi' \
           -o -name '*.o' \
           -o -name '*.hp' \
           -o -name '.*.aux' \) -type f -delete
RUN for i in coq-haskell bedrock fiat ; do (cd $i ; git clean -dfx); done

WORKDIR /home/rings
RUN cp -pR /tmp/rings . && chown -R rings rings && rm -fr /tmp/rings

# Change docker user to rings
USER rings
ENV USER rings

# install Nix
RUN curl https://nixos.org/nix/install | sh
RUN . ~/.nix-profile/etc/profile.d/nix.sh && nix-channel --update

# Build the RINGS environment within the container

WORKDIR /home/rings/rings
RUN . ~/.nix-profile/etc/profile.d/nix.sh && \
    nix-build --no-build-output \
              --max-jobs 2 \
              --cores 2 \
              --fallback \
              --attr ringsEnv

WORKDIR /home/rings/rings/fiat
RUN . ~/.nix-profile/etc/profile.d/nix.sh && \
    ~/rings/result/bin/load-env-rings make -j2

WORKDIR /home/rings/rings/coq-haskell
RUN . ~/.nix-profile/etc/profile.d/nix.sh && \
    ~/rings/result/bin/load-env-rings make

# WORKDIR /home/rings/rings/vignettes/simple_parser_fiat
# RUN . ~/.nix-profile/etc/profile.d/nix.sh && \
#     ~/rings/result/bin/load-env-rings make

# CMD ["./rings/vignettes/simple_parser_fiat/result/bin/spv",
#      "./rings/vignettes/simple_parser_fiat/input.txt" ]
