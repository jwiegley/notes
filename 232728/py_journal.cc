  shared_ptr<collect_posts>
  py_collect(journal_t& journal, const string& query)
  {
    report_t& current_report(downcast<report_t>(*scope_t::default_scope));

    std::auto_ptr<journal_t> save_journal
      (current_report.session.journal.release());
    current_report.session.journal.reset(&journal);

    shared_ptr<collect_posts> coll(new collect_posts);

    try {
      report_t local_report(current_report);
      process_arguments(split_arguments(query.c_str()), local_report);
      global_scope_t::normalize_report_options(local_report, "register");

      reporter<> collector(coll.get(), local_report, "@py_collect");
      call_scope_t scope(local_report);
      collector(scope);
    }
    catch (...) {
      current_report.session.journal.release();
      current_report.session.journal.reset(save_journal.release());
    }
    current_report.session.journal.release();
    current_report.session.journal.reset(save_journal.release());

    return coll;
  }
