# Introduction

Nix is: a language, a package manager (able to work under any OS), an OS
distribution based on the Linux kernel, and a cloud deployment tool: all using
the paradigm of a simple, purely functional language, combined with an
immutable object store, to offer versioned, reliable installations.

The Nix project comprises a technology stack, and this document will examine
each layer of the stack in turn, to show how this complexity all emerges from
a relatively small and compelling simplicity.

[Change this to a diagram]

    Nix Language -> Nixpkgs -> NixOS -> NixOps

# Quickstart

To make the most of this document, it will help to follow along on your own
machine.  Nix can run alongside most of the major operating systems without
affecting any other package manager you might use (for example, yum, apt,
homebrew, macports, etc).  Or you could install NixOS in a VM and play along
that way.  The author uses Nix under OS X, and so most of the early sections
will not focus on just NixOS.

To begin, simply execute the installer as a regular user on your machine:

    curl https://nixos.org/nix/install | sh

The user you install as will "own" the local Nix repository, and so will be
able to install and remove software from that user's environment without
requiring root permissions.

Every Nix operation affects only files kept in its own store, which is located
in `/nix`.  So if you ever want to completely uninstall Nix from your machine,
simply execute:

    rm -fr /nix ~/.nix*
    
Once you have finished installing Nix, the first operation to test things out
should be to install your favorite editor:

    nix-env -i emacs [or vim]
    
If pre-compiled binaries are available, they will be installed directly.  If
not, the packages will be built, along with any dependencies need to build,
such as a suitable compiler.  This can take some time in the latter case, so
you may need to leave it running as you read along.

# The Nix Language

Nix is a lazily evaluated, purely functional language.  "Lazy" in this setting
means that evaluation only occurs when results are demanded.  For example, if
you don't try to install a package named "foo", the build recipe for foo is
not computed; "purely" means that every function must return the same output
for the same inputs; and "functional" means that computations are performed
primarily by the evaluation of function calls, rather than by looping or state
mutation constructs.

This is not to say that "everything is a function".  Nix also adds certain
atomic data types:

  - booleans
  - integers
  - strings
  - paths
  - "sets" of key/value pairs
  - the null value

Most of what the Nix language is, is syntax for describing these atomic
values.  The rest of it deals with defining, and calling, functions.

## Hello world

Being a pure language, Nix has no way to state "effects", such as printing
`Hello, world!` to the screen.  However, what we can do is build a function
that describes how to say hello in the form of a bash script, and then use the
Nix evaluator to execute this script after evaluating it.  The file we are
editing will be called `hello.nix`:

    

# Object Store

# Nixpkgs

# Common commands

# Local configuration

# NixOS

# NixOps
