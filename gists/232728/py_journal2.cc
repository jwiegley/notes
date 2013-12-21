  class_< item_handler<post_t>, shared_ptr<item_handler<post_t> >,
          boost::noncopyable >("PostHandler")
    ;

  class_< collect_posts, bases<item_handler<post_t> >,
          shared_ptr<collect_posts>, boost::noncopyable >("PostCollector")
    .def("__len__", &collect_posts::length)
    .def("__iter__", range<return_internal_reference<> >
	 (&collect_posts::begin, &collect_posts::end))
    ;

  class_< journal_t, boost::noncopyable > ("Journal")
    .def("collect", py_collect)
    ;
