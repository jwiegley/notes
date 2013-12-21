      parent->HANDLER(revalued).on_only(string("--gain"));
      parent->HANDLER(amount_).set_expr(string("--gain"), "(amount, cost)");
      // Since we are displaying the amounts of revalued postings, they
      // will end up being composite totals, and hence a pair of pairs.
      parent->HANDLER(display_amount_)
        .set_expr(string("--gain"),
                  "use_direct_amount ? amount :"
                  " (is_seq(get_at(amount_expr, 0)) ?"
                  "  get_at(get_at(amount_expr, 0), 0) :"
                  "  market(get_at(amount_expr, 0), date, exchange)"
                  "  - get_at(amount_expr, 1))");
      parent->HANDLER(revalued_total_)
        .set_expr(string("--gain"),
                  "(market(get_at(total_expr, 0), date, exchange), "
                  "get_at(total_expr, 1))");
      parent->HANDLER(display_total_)
        .set_expr(string("--gain"),
                  "use_direct_amount ? total_expr :"
                  " market(get_at(total_expr, 0), date, exchange)"
                  " - get_at(total_expr, 1)");
