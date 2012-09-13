#include <iostream>
#include <string>

#include <boost/optional.hpp>
#include <boost/foreach.hpp>

#define foreach BOOST_FOREACH

template <typename a = void*>
struct Monad
{
  virtual Monad operator>>(Monad (*f)(const a&)) = 0;
  virtual Monad operator>>=(Monad (*f)(const a&)) = 0;
  virtual Monad return_(const a& v) = 0;
};

template <typename a = void*>
struct Maybe : public Monad<a>
{
};

template <typename a = void*>
struct Just : public Monad<a>
{
  a value;

  Just(const a& v) : value(v) {}

  virtual Maybe<a> operator>>(Monad<a> (*f)(const a&)) {
    f(value);
    return Monad<a>();
  }

  virtual Maybe<a> operator>>=(Monad<a> (*f)(const a&)) {
    return f(value);
  }

  virtual Maybe<a> return_(const a& v) {
    return Just(v);
  }
};

template <typename a = void*>
struct Nothing : public Maybe<a>
{
  virtual Maybe<a> operator>>(Monad<a> (*f)(const a&)) {
    return Nothing();
  }

  virtual Maybe<a> operator>>=(Monad<a> (*f)(const a&)) {
    return Nothing();
  }
};

int main()
{
  Just<int> x(10);
}
