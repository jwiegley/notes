#include <iostream>
#include <string>

int main()
{
  using namespace std;

  wstring test(L"€");

  locale utf8("en_US.UTF-8");
  wcout.imbue(utf8);

  wcout << L" test.length = " << test.length() << endl;
  wcout << L"wcslen(test) = " << wcslen(test.c_str()) << endl;
  wcout << L"     test[0] = '" << test[0] << L"'" << endl;
  wcout << L"        test = '" << test << L"'" << endl;

  wcout.width(4);
  wcout << right << test << endl;
}
