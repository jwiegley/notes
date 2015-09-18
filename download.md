There are three widely used ways to install the Haskell toolchain (the GHC
compiler and related tools) on supported platforms (currently Linux, Mac OS X,
and Windows). Supported offerings are:

- [Haskell Platform](#platform)
- [Stack](#stack)
- [GHC+Cabal minimal installers](#minimal)

For information on other platforms and methods, please see the section on
[third party installers](#other).

# Haskell Platform

## What it is

<a name="platform"></a>The Haskell Platform is a self-contained, all-in-one
installer. It provides binaries for the GHC Haskell compiler, as well as some
important, related tools and several widely used libraries.

## How to get it

The Platform is provided as a single installer, and can be downloaded at the
links below.

- [Linux](http://www.haskell.org/platform/linux.html)
- [OS X](http://www.haskell.org/platform/mac.html)
- [Windows](http://www.haskell.org/platform/windows.html)

## Where to get help

- You can find a comprehensive list of
  [what the Platform offers](https://www.haskell.org/platform/contents.html).
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

<a name="stack"></a>Stack is a cross-platform build tool for Haskell that
handles the management of the toolchain (including the GHC compiler and MSYS2
on Windows), building and registering libraries, and more. Once downloaded, it
has the capacity to download and install GHC and other core tools. Some of
Stack's features are:

- Project development is isolated within sandboxes, including automatic
  download of the right version of GHC for a given project.
- It manages all Haskell-related dependencies, ensuring reproducible builds.
- It uses a curated set of packages by default, that are known to be mutually
  compatible.
- It can optionally use Docker to produce standalone deployments.

## How to get it

There is a [GitHub Wiki page](https://github.com/commercialhaskell/stack/wiki/Downloads)
that describes how to download Stack on various platforms, though the main
three are repeated here:

- [Linux](https://github.com/commercialhaskell/stack/wiki/Downloads#ubuntu)
- [OS X](https://github.com/commercialhaskell/stack/wiki/Downloads#os-x)
- [Windows](https://github.com/commercialhaskell/stack/wiki/Downloads#windows)

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

# Minimal installers

## What it is

<a name="minimal"></a>Minimal installers provide only
[GHC](https://www.haskell.org/ghc), [Cabal](https://www.haskell.org/cabal/),
and for OS X and Windows, [Stack](https://github.com/commercialhaskell/stack).
The libraries included are only those core libraries necessarily tied to the
compiler.

## How to get it

- [Linux](https://www.haskell.org/downloads/linux)
- [OS X](https://www.haskell.org/downloads/osx)
- [Windows](https://www.haskell.org/downloads/windows)

## Where to get help

See the general help mentioned [above](#help), which covers the usage of GHC,
as well as the Cabal and Stack tools.

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

<a name="other"></a>For other platforms, or building from source, or using
distribution package managers such as on Debian or Nix, there are even more
ways to get GHC...
