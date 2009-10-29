#include <fstream>

#include <boost/archive/text_iarchive.hpp>
#include <boost/archive/text_oarchive.hpp>
          
#include <boost/serialization/base_object.hpp>
#include <boost/serialization/utility.hpp>
#include <boost/serialization/list.hpp>
#include <boost/serialization/assume_abstract.hpp>

struct foo {
  int a;
  template<class Archive>
  void serialize(Archive & ar, const unsigned int version) {
    ar & a;
  }
};

int main() {
  std::ofstream ofs("/tmp/bar");
  boost::archive::text_oarchive oa(ofs);
  foo x;
  oa << x;
  ofs.close();
  return 0;
}
