# check for Boost.Test
AC_CACHE_CHECK(
  [if boost_test is available],
  [boost_test_avail_cv_],
  [boost_test_save_libs=$LIBS
   LIBS="-lboost_unit_test_framework$BOOST_SUFFIX -lboost_test_exec_monitor$BOOST_SUFFIX $LIBS"
   AC_LANG_PUSH(C++)
   AC_LINK_IFELSE(
     [AC_LANG_SOURCE(
        [[#define BOOST_TEST_MODULE sample
          #include <boost/test/unit_test.hpp>
          BOOST_AUTO_TEST_CASE(test_test) {}]])],
     [boost_test_avail_cv_=true],
     [boost_test_avail_cv_=false])
   AC_LANG_POP
   LIBS=$boost_test_save_libs])

AM_CONDITIONAL(HAVE_BOOST_TEST, test x$boost_test_avail_cv_ = xtrue)
