{- | Return e (Euler's constant) -}
foreign import ccall "Z3_rcf_mk_e" c'Z3_rcf_mk_e
  :: C'Z3_context -> IO C'Z3_rcf_num
foreign import ccall "&Z3_rcf_mk_e" p'Z3_rcf_mk_e
  :: FunPtr (C'Z3_context -> IO C'Z3_rcf_num)

{-# LINE 25 "Z3/Base/C/Rcf.hsc" #-}

{- | Return a new infinitesimal that is smaller than all elements in the Z3 field. -}
foreign import ccall "Z3_rcf_mk_infinitesimal" c'Z3_rcf_mk_infinitesimal
  :: C'Z3_context -> IO C'Z3_rcf_num
foreign import ccall "&Z3_rcf_mk_infinitesimal" p'Z3_rcf_mk_infinitesimal
  :: FunPtr (C'Z3_context -> IO C'Z3_rcf_num)

{-# LINE 28 "Z3/Base/C/Rcf.hsc" #-}

{- | Store in roots the roots of the polynomial
       The output vector \c roots must have size \c n.
       It returns the number of roots of the polynomial.

       \pre The input polynomial is not the zero polynomial. -}
foreign import ccall "Z3_rcf_mk_roots" c'Z3_rcf_mk_roots
  :: C'Z3_context -> CUInt -> Ptr C'Z3_rcf_num -> Ptr C'Z3_rcf_num -> IO ()
foreign import ccall "&Z3_rcf_mk_roots" p'Z3_rcf_mk_roots
  :: FunPtr (C'Z3_context -> CUInt -> Ptr C'Z3_rcf_num -> Ptr C'Z3_rcf_num -> IO ())
