
(</>) Root (AbsDir parent dir)       = AbsDir parent dir
(</>) Root (AbsFile parent file)     = AbsFile parent file

(</>) Root (RelDir Nothing dir)      = AbsDir Nothing dir
(</>) Root (RelDir (Just top) dir)   = AbsDir (Just (Root </> top)) dir

(</>) Root (RelFile Nothing file)    = AbsFile Nothing file
(</>) Root (RelFile (Just top) file) = AbsFile (Just (Root </> top)) file

(</>) p@(AbsDir {}) (RelDir Nothing dir2)        = AbsDir (Just p) dir2
(</>) p@(AbsDir {}) (RelDir (Just parent2) dir2) = AbsDir (Just (p </> parent2)) dir2

(</>) p@(AbsDir {}) (RelFile Nothing file2)        = AbsFile (Just p) file2
(</>) p@(AbsDir {}) (RelFile (Just parent2) file2) = AbsFile (Just (p </> parent2)) file2

(</>) p@(RelDir Nothing _) (RelDir Nothing dir2)        = RelDir (Just p) dir2
(</>) p@(RelDir Nothing _) (RelDir (Just parent2) dir2) = RelDir (Just (p </> parent2)) dir2

(</>) p@(RelDir Nothing _) (RelFile Nothing file2)        = RelFile (Just p) file2
(</>) p@(RelDir Nothing _) (RelFile (Just parent2) file2) = RelFile (Just (p </> parent2)) file2

{-