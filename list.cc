#include <boost/optional.hpp>
#include <boost/function.hpp>
#include <boost/lambda/lambda.hpp>

using namespace boost;
using namespace lambda;

#include <iostream>
#include <list>

template <typename T>
class List
{
public:
  std::list<T> value;

  List() {}
  List(const T& v) : value(v) {}

  List operator>>(function<List(const T&)> f) const;

  static function<List(const T&)> lift(function<T(const T&)> f) {
    return bind(return_, bind(f, _1));
  }

  static List return_(const T& v) {
    return List(v);
  }
};

template <typename T>
List<T> List<T>::operator>>(function<List<T>(const T&)> f) const {
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

  ints >> ints.lift(_1 + 100) >> print;
}
