{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Pathname where

import Control.Category
import System.Posix.ByteString
import Prelude hiding ((.))

data PathKind = EmptyPath
              | RootDir
              | AbsoluteDir
              | AbsoluteFile
              | RelativeDir
              | RelativeFile

{-
One reason pathnames have always been unreasonably tricky, is that in
representing them as string-like entities, we falsely imagine them to be
monoids.  However, they are not monoids, but categories: which does give them
somewhat of a monoidal structure, but with less freedom.

In the Category 'Path', whose objects are kinded paths, and whose morphisms
are transformations between such paths, only a fixed number of morphisms
exist:

    1. The identity morphism, which takes any kinded path to itself; this
       is represented as 'pathId'
    2. Morphisms from the root to any other kinded path
    3. Morphisms from absolute directories to absolute directories and files
    4. Morphisms from relative directories to relative directories and files

Thus you cannot, using the structure of this category, turn an absolute path
into a relative one, or combine two absolute directories (for no such endo-
morphism exists).  Such operations require deconstructing the paths into their
components and working in the freer category of those components (which, for
the underyling path segments, could be the free monoid category of lists of
bytestrings, for example).

There is also a forgetful functor from the category of paths into Hask, by
mapping each kinded path to the type 'Either [RawFilePath] [RawFilePath]',
indicating either absolute or relative filepaths (with root represented as
'Left []', and the empty path as 'Right []').  This allows functions on paths
to be fmap'd to functions on such sums of lists, but only for valid
combinations of arguments as required by the structure of the Path category.

Finally, we can easly render 'Either [RawFilePath] [RawFilePath]' paths by
interpolating separators between segments, and additionally by prefixing a
separator in the 'Left' case.
-}

data Pathname (k :: PathKind) where
    Empty   :: Pathname 'EmptyPath
    Root    :: Pathname 'RootDir
    AbsDir  :: Maybe (Pathname 'AbsoluteDir) -> RawFilePath
                  -> Pathname 'AbsoluteDir
    AbsFile :: Maybe (Pathname 'AbsoluteDir) -> RawFilePath
                  -> Pathname 'AbsoluteFile
    RelDir  :: Maybe (Pathname 'RelativeDir) -> RawFilePath
                  -> Pathname 'RelativeDir
    RelFile :: Maybe (Pathname 'RelativeDir) -> RawFilePath
                  -> Pathname 'RelativeFile

pathId :: Pathname a -> Pathname a
pathId = (</> Empty)

type family CombinedPath a b where
    CombinedPath a           EmptyPath    = a
    CombinedPath EmptyPath   b            = b
    CombinedPath RootDir     RootDir      = RootDir
    CombinedPath RootDir     AbsoluteDir  = AbsoluteDir
    CombinedPath RootDir     AbsoluteFile = AbsoluteFile
    CombinedPath RootDir     RelativeDir  = AbsoluteDir
    CombinedPath RootDir     RelativeFile = AbsoluteFile
    CombinedPath AbsoluteDir RelativeDir  = AbsoluteDir
    CombinedPath AbsoluteDir RelativeFile = AbsoluteFile
    CombinedPath RelativeDir RelativeDir  = RelativeDir
    CombinedPath RelativeDir RelativeFile = RelativeFile

(</>) :: Pathname a -> Pathname b -> Pathname (CombinedPath a b)

(</>) Empty p                                = p
(</>) p Empty                                = p

(</>) Root Root                              = Root

(</>) Root p@(AbsDir {})                     = p
(</>) Root p@(AbsFile {})                    = p

(</>) Root (RelDir Nothing dir)              = AbsDir Nothing dir
(</>) Root (RelDir (Just t) dir)             = AbsDir (Just (Root </> t)) dir

(</>) Root (RelFile Nothing file)            = AbsFile Nothing file
(</>) Root (RelFile (Just t) file)           = AbsFile (Just (Root </> t)) file

(</>) p@(AbsDir {}) (RelDir Nothing d2)      = AbsDir (Just p) d2
(</>) p@(AbsDir {}) (RelDir (Just par2) d2)  = AbsDir (Just (p </> par2)) d2

(</>) p@(AbsDir {}) (RelFile Nothing f2)     = AbsFile (Just p) f2
(</>) p@(AbsDir {}) (RelFile (Just par2) f2) = AbsFile (Just (p </> par2)) f2

(</>) p@(RelDir {}) (RelDir Nothing d2)      = RelDir (Just p) d2
(</>) p@(RelDir {}) (RelDir (Just par2) d2)  = RelDir (Just (p </> par2)) d2

(</>) p@(RelDir {}) (RelFile Nothing f2)     = RelFile (Just p) f2
(</>) p@(RelDir {}) (RelFile (Just par2) f2) = RelFile (Just (p </> par2)) f2

-- These cannot be called, and the type checker prevents it by the closed type
-- synonym up above.  However, GHC still gives warning in -Wall about these
-- "definitions" not being present.
(</>) (AbsDir  {}) _ = error "Impossible"
(</>) (AbsFile {}) _ = error "Impossible"
(</>) (RelDir  {}) _ = error "Impossible"
(</>) (RelFile {}) _ = error "Impossible"

newtype PathMor a b = PathMor { getPathMor :: Pathname a -> Pathname b }

instance Category PathMor where
    id    = PathMor pathId
    f . g = PathMor (getPathMor f . getPathMor g)
