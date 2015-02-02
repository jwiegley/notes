TESTS = RegressTests BaselineTests ManualTests ConfirmTests \
        GenerateTests

if HAVE_BOOST_TEST
TESTS +=            \
        UtilTests   \
        MathTests   \
        ExprTests
#       DataTests   \
#       ReportTests
endif

check_PROGRAMS = $(TESTS)

TESTLIBS = -lboost_unit_test_framework$(BOOST_SUFFIX) \
           -lboost_test_exec_monitor$(BOOST_SUFFIX)

UtilTests_SOURCES =              \
        test/unit/t_times.cc

UtilTests_CPPFLAGS = -I$(srcdir)/test $(lib_cppflags)
UtilTests_LDADD    = libledger_util.la $(TESTLIBS)