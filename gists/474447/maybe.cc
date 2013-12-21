#include <boost/optional.hpp>
#include <boost/function.hpp>

#include <iostream>

template <typename T>
class Maybe
{
private:
  boost::optional<T> value;

public:
  Maybe() {}
  Maybe(const T& t) : value(t) {}
  Maybe(const Maybe& m) : value(m.value) {}

  Maybe operator>>=(boost::function<Maybe<T>(const T&)> f) const {
    if (value)
      return f(*value);
    else
      return *this;
  }

  Maybe operator>>(boost::function<Maybe<T>()> f) const {
    if (value)
      return f();
    else
      return *this;
  }

  static Maybe return_(const T& t) {
    return Maybe(t);
  }

  static Maybe Nothing() {
    return Maybe();
  }
};

Maybe<int> positive_int(const int& x)
{
  if (x >= 0) {
    std::cout << "x is positive = " << x << std::endl;
    return Maybe<int>::return_(x);
  } else {
    std::cout << "x is negative = " << x << std::endl;
    return Maybe<int>::Nothing();
  }
}

int main()
{
  ((positive_int(10)  >>= positive_int) >>= positive_int) >>= positive_int;
  ((positive_int(-10) >>= positive_int) >>= positive_int) >>= positive_int;
};
