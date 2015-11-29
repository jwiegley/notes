#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/phoenix/phoenix.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/variant.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <string>
#include <vector>
#include <iostream>

using namespace boost::spirit;
using boost::phoenix::ref;

struct reference_t
{
  unsigned long addr;
  std::string   name;
};

BOOST_FUSION_ADAPT_STRUCT(
  reference_t,
  (unsigned long, addr)
  (std::string,   name)
)

int main()
{
  qi::uint_parser<unsigned, 16, 1, 16> hex_word;
  qi::rule<std::string::iterator, reference_t(), ascii::space_type> header
    =  hex_word >> '<' >> +(qi::alnum | qi::char_('_')) >> '>' >> ':';

  while (! std::cin.eof()) {
    std::string s;
    std::getline(std::cin, s);

    reference_t hdr;
    if (qi::phrase_parse(s.begin(), s.end(), header, ascii::space, hdr)) {
      std::cout << "addr = " << hdr.addr << std::endl;
      std::cout << "name = " << hdr.name << std::endl;
    } else {
      std::cout << "Failed to parse: " << s << std::endl;
    }
  }
}
