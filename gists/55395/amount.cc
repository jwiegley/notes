      // Convert the rational number to a floating-point, extending the
      // floating-point to a large enough size to get a precise answer.
      const std::size_t bits = (mpz_sizeinbase (mpq_numref(quant), 2) +
				mpz_sizeinbase (mpq_denref(quant), 2));
      mpfr_set_prec(tempfb, bits + amount_t::extend_by_digits*8);
      mpfr_set_q(tempfb, quant, GMP_RNDN);
