#include <boost/archive/text_oarchive.hpp>
#include <iostream>
          
struct foo {
  int a;
  foo() : a(123) {}
  template<class Archive>
  void serialize(Archive & ar, const unsigned int) {
    ar & a;
  }
};

int main() {
  boost::archive::text_oarchive oa(std::cout);
  foo x;
  oa << x;
  return 0;
}