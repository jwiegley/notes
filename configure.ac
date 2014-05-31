# Use custom echo test for newline option
# Current autoconf (2.65) gives incorrect echo newline option
# for icu-config
# This may be removed later - mow (June 17, 2010)
ICU_ECHO_C= ICU_ECHO_N= ICU_ECHO_T=
case `/bin/sh -c "echo -n x"` in
-n*)
  case `/bin/sh -c "echo 'x\c'"` in
  *c*) ICU_ECHO_T=' ';;     # ECHO_T is single tab character.
  *)   ICU_ECHO_C='\c';;
  esac;;
*)
  ICU_ECHO_N='-n';;
esac
AC_SUBST(ICU_ECHO_N)
AC_SUBST(ICU_ECHO_C)
AC_SUBST(ICU_ECHO_T)
