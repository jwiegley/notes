There are three widely used ways to install the Haskell toolchain on supported
platforms: Linux, Mac OS X, and Windows. For information on other platforms
and methods, please see the link at the bottom of the page.

# Haskell Platform

## What it is

The Haskell Platform is an all-in-one installer, designed for users who want
to get started with Haskell quickly and easily. It does not require Internet
access beyond downloading the installer, and so is ideal for academic and
learning situations where only the standard libraries will be used.

Note that future versions of the platform will include the [Stack](#stack)
tool, mentioned below, which offers additional features for advanced users.

## How to get it

The Platform is provided as a single installer, and can be downloaded at the
links below. Note that it is only available on these supported platforms.

- [Linux](http://www.haskell.org/platform/linux.html)
- [OS X](http://www.haskell.org/platform/mac.html)
- [Windows](http://www.haskell.org/platform/windows.html)

## Where to get help

- <a name="help" />For help learning Haskell itself, start with the
  [Documentation](https://www.haskell.org/documentation) page on the
  [Haskell Wiki](https://www.haskell.org/).
- If you need help with [GHC](https://www.haskell.org/ghc)---the Haskell
  compiler included with the Platform---there is a comprehensive
  [GHC User Manual](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/index.html).
- For help using Cabal to download or create additional packages (see
  [below](#thirdparty)), there is the
  [Cabal User Guide](https://www.haskell.org/cabal/users-guide/).
- Finally, you can ask questions of other Haskell users and experts on the
  [\#haskell IRC channel](irc://irc.freenode.net/haskell) on the Freenode IRC
  network.

# Stack

## What it is

<a name="stack"></a>Stack is a cross-platform build tool for Haskell that is
aimed at both new and experienced users of Haskell. Once downloaded, it will
download and install GHC and several other core packages. Some of Stack's
features are:

- Project development is isolated within sandboxes, including automatic
  download of the right version of GHC for a given project.
- It manages all Haskell-related dependencies, ensuring reproducible builds.
- It uses a curated set of packages by default, that are known to be mutually
  compatible.
- It can optionally use Docker to produce standalone deployments.

If you wish to to deploy Haskell in environments that know little about the
Haskell ecosystem, Stack can help to reduce unwanted inertia.

## How to get it

There is a [GitHub Wiki page](https://github.com/commercialhaskell/stack/wiki/Downloads)
that describes how to download Stack on various platforms, though the main
three are repeated here:

- [Linux](https://github.com/commercialhaskell/stack/wiki/Downloads#linux)
- [OS X](https://github.com/commercialhaskell/stack/releases/latest)
- [Windows](https://github.com/commercialhaskell/stack/releases/latest)

## Where to get help

For help with Haskell and GHC in general, see the links mentioned
[above](#help). For Stack itself there are also the following resources:

- The [README](https://github.com/commercialhaskell/stack/#readme) offers a
  general overview, and help with installation.
- There is an
  [in-depth guide](https://github.com/commercialhaskell/stack/blob/master/doc/GUIDE.md)
  to using Stack.
- [Getting started with Stack](http://seanhess.github.io/2015/08/04/practical-haskell-getting-started.html)
  introduces how to build new projects using Stack.
- You may post issues and feature requests on its
  [GitHub issue tracker](https://github.com/commercialhaskell/stack).
- There is a dedicated
  [\#haskell-stack IRC channel](irc://irc.freenode.net/haskell-stack) on the
  Freenode IRC network.

<!--
- Stack is supported by the consulting company, FP Complete, who may be
  [contacted directly](https://www.fpcomplete.com/business/about/contact-us/)
  if you have specific or custom needs.
-->

# Minimal installers

## What it is

Other advanced users may want only [GHC](https://www.haskell.org/ghc) and the
standard package installer, [Cabal](https://www.haskell.org/cabal/). This is
not the recommended path for those completely new to Haskell.

## How to get it

- [Linux](https://www.haskell.org/downloads/linux)
- [OS X](https://www.haskell.org/downloads/osx)
- [Windows](https://www.haskell.org/downloads/windows)

Packages are managed with the Cabal package system built into GHC (and other
compilers). For specific details, see the
[Cabal User Guide](https://www.haskell.org/cabal/users-guide/), and the
section below on [Third Party Libraries](#thirdparty).

## Where to get help

See the general help mentioned [above](#help), and also the
  [\#hackage IRC channel](irc://irc.freenode.net/hackage) on the Freenode IRC
  network, which is the default package server used by Cabal.

# Third party libraries

<a name="thirdparty"></a>The Haskell community offers far more functionality
than comes with the standard installation methods mentioned above. For
information on how to get these libraries depending on what you chose to
install, please learn more at ____.

<!--- The following would be described in a separate page on the Wiki, and not
on the downloads page. -->

# Third party installers

<!--- This should be in smaller text at the bottom of the page. The page it
jumps to could be on the Wiki to make editing and updates easier for others.
-->

For other platforms, or building from source, or using distribution package
managers such as on Debian or Nix, there are even more ways to get GHC...
