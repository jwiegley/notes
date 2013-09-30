string args_to_predicate(value_t::sequence_t::const_iterator begin,
                           value_t::sequence_t::const_iterator end)
{
  std::ostringstream expr;
  bool         append_and = false;

  while (begin != end) {
    const string& arg((*begin).as_string());

    bool parse_argument = true;

    if (arg == "not") {
        expr << " ! ";
        parse_argument = false;
        append_and = false;
    }
    else if (arg == "and") {
        expr << " & ";
        parse_argument = false;
        append_and = false;
    }
    else if (arg == "or") {
        expr << " | ";
        parse_argument = false;
        append_and = false;
    }
    else if (append_and) {
        expr << " & ";
    }
    else {
        append_and = true;
    }

    if (parse_argument) {
        const char * p = arg.c_str();

        bool in_prefix     = true;
        bool in_suffix     = false;
        bool found_specifier = false;
        bool saw_tag_char    = false;

        for (const char * c = p; *c != '\0'; c++) {
          bool consumed = false;
          if (in_prefix) {
            switch (*c) {
            case '(':
              break;
            case '@':
              expr << "(payee =~ /";
              found_specifier = true;
              consumed = true;
              break;
            case '=':
              expr << "(note =~ /";
              found_specifier = true;
              consumed = true;
              break;
            case '%':
              expr << "(note =~ /:";
              found_specifier = true;
              saw_tag_char = true;
              consumed = true;
              break;
            case '/':
            case '_':
            default:
              if (! found_specifier) {
                expr << "(account =~ /";
                found_specifier = true;
              }
              in_prefix = false;
              break;
            }
          } else {
            switch (*c) {
            case ')':
              if (! in_suffix) {
                if (found_specifier) {
                  if (saw_tag_char)
                    expr << ':';
                  expr << "/)";
                }
                in_suffix = true;
              }
              break;
            default:
              if (in_suffix)
                throw_(parse_error, "Invalid text in specification argument");
              break;
            }
          }

          if (! consumed)
            expr << *c;
        }

        if (! in_suffix) {
          if (found_specifier) {
            if (saw_tag_char)
              expr << ':';
            expr << "/)";
          }
        }
    }

    begin++;
  }

  DEBUG("report.predicate", "Regexp predicate expression = " << expr.str());

  return expr.str();
}
