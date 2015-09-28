There are three widely used ways to install the Haskell toolchain on supported
platforms. Currently these are:

- [Minimal installers](#minimal): Just GHC (the compiler) and Cabal (a package
  install and build tool) are installed globally on your system, using your
  system's package manager.

- [Stack](#stack): Installs the `stack` command globally: a project-centric
  build tool to automatically download and manage Haskell dependencies on a
  project-by-project basis.

- [Haskell Platform](#platform): Installs GHC, Cabal, and some other tools,
  along with a starter set of libraries in a global location on your system.

These options make different choices as to what elements are installed
*globally* across your system and which ones are maintained in
project-specific environments. Global installations allow sharing across users
and projects, but at the cost of potentially inflexible dependency coupling
between separate projects. Sandboxes are usually suggested to avoid this
coupling. This is possible with both Minimal and the Platform -- although the
latter can run into trouble with conflicts against the globally installed
platform packages -- while it is the fundamental operating mode for Stack.

For information on other platforms and methods, please see the section on
[third party installers](#other).

# Haskell Platform

## What it is

<a name="platform"></a>The Haskell Platform is a self-contained, all-in-one
installer. After download, you will have everything necessary to build Haskell
programs against a core set of useful libraries.

## What you get

- The [Glasgow Haskell Compiler](https://www.haskell.org/ghc) 
- The [Cabal build system](https://www.haskell.org/cabal/), which can install
  new packages, and by default fetches from
  [Hackage](https://hackage.haskell.org/), the central Haskell package
  repository.
- Support for profiling and code coverage analysis
- 35 core & widely-used [packages](https://www.haskell.org/platform/contents.html)

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
handles management of the toolchain (including the GHC compiler and MSYS2 on
Windows), building and registering libraries, and more.

## What you get

- Once downloaded, it has the capacity to download and install GHC and other
  core tools.
- Project development is isolated within sandboxes, including automatic
  download of the right version of GHC for a given project.
- It manages all Haskell-related dependencies, ensuring reproducible builds.
- It fetches from a curated repository of over a thousand packages by default,
  known to be mutually compatible.
- It can optionally use Docker to produce standalone deployments.

## How to get it

The [install and upgrade page](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md)
describes how to download Stack on various platforms, although the main
three are repeated here:

- [Ubuntu Linux](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md#ubuntu)
- [OS X](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md#os-x)
- [Windows](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md#windows)

Instructions for other Linux distributions, including Debian, Fedora, Red Hat,
Nix OS, and Arch Linux, are also available.

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
- There is a [mailing list for Stack](https://groups.google.com/d/forum/haskell-stack)
- There is a dedicated
  [\#haskell-stack IRC channel](irc://irc.freenode.net/haskell-stack) on the
  Freenode IRC network.
- The [StackOverflow haskell-stack tag](http://stackoverflow.com/questions/tagged/haskell-stack)
  has many stack-specific questions and answers.

# Minimal installers

## What it is

<a name="minimal"></a> Minimal installers provide only
[GHC](https://www.haskell.org/ghc) and [Cabal](https://www.haskell.org/cabal/)
on Linux, and on Windows and OS X provide GHC, Cabal, and
[Stack](https://github.com/commercialhaskell/stack).

## What you get

- Only the core libraries necessary for each platform are included.
- Cabal or Stack must be used to download packages after installation.

## How to get it

- [Linux](https://www.haskell.org/downloads/linux)
- [OS X](https://ghcformacosx.github.io/) (via GHC for Mac OS X)
- [Windows](https://github.com/fpco/minghc) (via MinGHC)

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
