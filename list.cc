#include <boost/optional.hpp>
#include <boost/function.hpp>
#include <boost/spirit/home/phoenix.hpp>

using namespace boost::phoenix;

#include <iostream>
#include <list>

template <typename T>
class List
{
public:
  std::list<T> value;

  List() {}
  List(const T& v) : value(v) {}

  struct binder
  {
    template <typename U>
    struct result { typedef List type; };

    boost::function<List(const T&)> f1;

    binder(boost::function<List(const T&)> const& f1)
      : f1(f1) {}

    List operator()(const T& v) const {
      return f1(v);
    }
  };

  List operator>>(function<binder> f) const;

  struct lifter
  {
    template <typename Arg>
    struct result {
      typedef T type;
    };

    template <typename Arg, typename F>
    F operator()(Arg arg1) const {
      return return_(arg1());
    }
  };

  function<lifter> lift;

  static List return_(const T& v) {
    return List(v);
  }
};

template <typename T>
List<T> List<T>::operator>>(function<binder> f) const {
  List<T> temp;
  for (typename std::list<T>::const_iterator i = value.begin();
       i != value.end();
       i++) {
    List<T> inner = f(*i);
    for (typename std::list<T>::const_iterator j = inner.value.begin();
           j != inner.value.end();
         j++)
      temp.value.push_back(*j);
  }
  return temp;
}

List<int> print(int x)
{
  std::cout << x << std::endl;
}

int main()
{
  List<int> ints;

  ints.value.push_back(10);
  ints.value.push_back(20);
  ints.value.push_back(30);

  ints >> ints.lift(arg_names::arg1 + 100) >> print;
}
