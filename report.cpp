  OPTION_(report_t, market, DO() { // -V
      OTHER(revalued).on(whence);

      OTHER(display_amount_)
        .on(whence, "market(display_amount, value_date, exchange)");
      OTHER(display_total_)
        .on(whence, "market(display_total, value_date, exchange)");
    });
