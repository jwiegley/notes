/*
 * Copyright (c) 2003-2009, John Wiegley.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * - Redistributions of source code must retain the above copyright
 *   notice, this list of conditions and the following disclaimer.
 *
 * - Redistributions in binary form must reproduce the above copyright
 *   notice, this list of conditions and the following disclaimer in the
 *   documentation and/or other materials provided with the distribution.
 *
 * - Neither the name of New Artisans LLC nor the names of its
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "generate.h"

namespace ledger {

void generate_posts_iterator::generate_string(std::ostream& out, int len,
					      bool only_alpha)
{
  int last;
  int first = true;
  for (int i = 0; i < len; i++) {
    int next = only_alpha ? 3 : three_gen();
    switch (next) {
    case 1:			// colon
      if (! first && last == 3)
	out << ':';
      else
	i--;
      break;
    case 2:			// space
      if (! first && last == 3)
	out << ' ';
      else
	i--;
      break;
    case 3:			// character
      switch (three_gen()) {
      case 1:			// uppercase
	out << upchar_gen();
	break;
      case 2:			// lowercase
	out << downchar_gen();
	break;
      case 3:			// number
	if (! only_alpha && ! first)
	  out << numchar_gen();
	else
	  i--;
	break;
      }
      break;
    }
    last = next;
    first = false;
  }
}

bool generate_posts_iterator::generate_account(std::ostream& out)
{
  bool must_balance = true;
  bool is_virtual   = false;

  switch (three_gen()) {
  case 1:
    out << '[';
    is_virtual = true;
    break;
  case 2:
    out << '(';
    must_balance = false;
    is_virtual = true;
    break;
  case 3:
    break;
  }

  generate_string(out, strlen_gen());

  if (is_virtual) {
    if (must_balance)
      out << ']';
    else
      out << ')';
  }
}

void generate_posts_iterator::generate_commodity(std::ostream& out)
{
  generate_string(out, six_gen(), true);
}

string generate_posts_iterator::generate_amount(std::ostream& out)
{
  std::ostringstream buf;

  if (truth_gen()) {		// commodity goes in front
    generate_commodity(buf);
    if (truth_gen())
      buf << ' ';
    buf << number_gen();
  } else {
    buf << number_gen();
    if (truth_gen())
      buf << ' ';
    generate_commodity(buf);
  }

  out << buf.str();

  return buf.str();
}

void generate_posts_iterator::generate_post(std::ostream& out, value_t& total)
{
  out << "    ";
  generate_account(out);
  out << "  ";

  total += value_t(generate_amount(out));
  if (truth_gen())
    generate_cost(out);		// jww (2009-02-26): calc total differently if so
  if (truth_gen())
    generate_note(out);
}

void generate_posts_iterator::generate_cost(std::ostream& out)
{
}

void generate_posts_iterator::generate_date(std::ostream& out)
{
  out.width(4);
  out.fill('0');
  out << year_gen();
  
  out.width(1);
  out << '/';

  out.width(2);
  out.fill('0');
  out << mon_gen();
  
  out.width(1);
  out << '/';

  out.width(2);
  out.fill('0');
  out << day_gen();
}

void generate_posts_iterator::generate_state(std::ostream& out)
{
  switch (three_gen()) {
  case 1:
    out << "* ";
    break;
  case 2:
    out << "! ";
    break;
  case 3:
    out << "";
    break;
  }
}

void generate_posts_iterator::generate_code(std::ostream& out)
{
  out << '(';
  generate_string(out, six_gen());
  out << ')';
}

void generate_posts_iterator::generate_payee(std::ostream& out)
{
  generate_string(out, strlen_gen());
}

void generate_posts_iterator::generate_note(std::ostream& out)
{
  out << "  ; ";
  generate_string(out, strlen_gen());
}

void generate_posts_iterator::generate_xact(std::ostream& out)
{
  generate_date(out);
  if (truth_gen()) {
    out << '=';
    generate_date(out);
  }
  out << ' ';

  generate_state(out);
  generate_code(out);
  generate_payee(out);
  if (truth_gen())
    generate_note(out);

  int	  count = three_gen() * 2;
  value_t total;
  for (int i = 0; i < count; i++)
    generate_post(out, total);
}

post_t * generate_posts_iterator::operator()()
{
  post_t * post = posts();
  if (post == NULL && quantity > 0) {
    std::ostringstream buf;
    generate_xact(buf);

    DEBUG("generate.post", "The post we intend to parse:\n" << buf.str());

    std::istringstream in(buf.str());
    session.master->parse(in, session);
    posts.reset(session.master->xacts.back());
    post = posts();

    quantity--;
  }
  return post;
}

} // namespace ledger
