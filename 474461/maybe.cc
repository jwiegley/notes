  (((positive_int(-10) >>=
     positive_int) >>=
     positive_int) >>=
     positive_int) >>=
     print_int;

  if (Maybe<int> x1 = positive_int(-10))
    if (Maybe<int> x2 = positive_int(*x1))
      if (Maybe<int> x3 = positive_int(*x2))
        if (Maybe<int> x4 = positive_int(*x3))
          print_int(*x4);
