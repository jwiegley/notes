  OPTION_(report_t, gain, DO() { // -G
      parent->HANDLER(revalued).on_only();
      parent->HANDLER(amount_).set_expr("(amount, cost)");
      // Since we are displaying the amounts of revalued transactions, they
      // will end up being composite totals, and hence a pair of pairs.
      parent->HANDLER(display_amount_)
	.set_expr("is_seq(get_at(amount_expr, 0)) ?"
		  " get_at(get_at(amount_expr, 0), 0) :"
		  " market(get_at(amount_expr, 0), date, exchange) -"
		  "   get_at(amount_expr, 1)");
      parent->HANDLER(revalued_total_)
	.set_expr("(market(get_at(total_expr, 0), date, exchange), "
		  "get_at(total_expr, 1))");
      parent->HANDLER(display_total_)
	.set_expr("market(get_at(total_expr, 0), date, exchange)"
		  " - get_at(total_expr, 1)");
    });
