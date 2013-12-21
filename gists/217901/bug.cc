#include <string>
#include <sstream>

#include <boost/variant.hpp>

int main()
{
  std::ostringstream buf;
  boost::variant<bool, std::string> data;
  data = buf.str();
  data = false;
  return 0;
}
