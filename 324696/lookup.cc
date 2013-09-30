/*
 * Copyright (c) 2003-2010, John Wiegley.  All rights reserved.
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

#include <system.hh>

#include "lookup.h"

namespace ledger {

namespace {
  typedef std::pair<xact_t *, int> score_entry_t;
  typedef std::deque<score_entry_t> scorecard_t;

  struct score_sorter {
    bool operator()(const score_entry_t& left,
                    const score_entry_t& right) const {
      return left.second > right.second;
    }
  };

  typedef std::map<account_t *, int>    account_use_map;
  typedef std::pair<account_t *, int>   account_use_pair;
  typedef std::vector<account_use_pair> account_use_vector;

  struct usage_sorter {
    bool operator()(const account_use_pair& left,
                    const account_use_pair& right) const {
      return left.second > right.second;
    }
  };
}

account_t * lookup_probable_account(const string&   ident,
                                    xacts_iterator& iter_func,
                                    account_t *     ref_account)
{
  scorecard_t scores;

  DEBUG("lookup.account", "Looking up identifier '" << ident << "'");
  DEBUG("lookup.account",
        "  with reference account: " << ref_account->fullname());

  while (xact_t * xact = iter_func()) {
    string            value_key = xact->payee;
    string::size_type len       = value_key.length();
    string::size_type index     = 0;
    int               bonus     = 0;
    int               score     = 0;
    string::size_type pos;

    // An exact match is worth a score of 1000
    if (ident == value_key) {
      scores.push_back(score_entry_t(xact, 1000));
      break;
    }

    // Walk each letter in the source identifier
    foreach (const char& ch, ident) {
      // If it occurs in the same order as the source identifier -- that is,
      // without intervening letters to break the pattern -- it's worth 10
      // points.  Plus, an extra point is added for every letter in chains of
      // 3 or more.

      int addend = 0;

      bool added_bonus = false;
      if (index < len && ch == value_key[index]) {
        addend += 10;
        if (bonus > 2)
          addend += bonus - 2;
        bonus++;
        added_bonus = true;
      }

      // If it occurs in the same general sequence as the source identifier,
      // it's worth 5 points, plus an extra point if it's within the next 3
      // characters, and an extra point if it's preceded by a non-alphabetic
      // character.

      else if (index < len &&
               (pos = value_key.find(ch, index)) != string::npos) {
        addend += 5;
        if (pos - index < 3)
          addend++;
        if (pos == 0 || (pos > 0 && !std::isalnum(value_key[pos - 1])))
          addend++;
      }

      // If the letter occurs at all in the target identifier, it's worth 1
      // point, plus an extra point if it's within 3 characters, and an extra
      // point if it's preceded by a non-alphabetic character.

      else if ((pos = value_key.find(ch)) != string::npos) {
        addend += 5;
        if (pos - index < 3)
          addend++;
        if (pos == 0 || (pos > 0 && !std::isalnum(value_key[pos - 1])))
          addend++;
      }

      // If the letter does not appear at all, decrease the score by 1

      else {
        addend--;
      }

      // Finally, decay what is to be added to the score based on its position
      // in the word.  Since credit card payees in particular often share
      // information at the end (such as the location where the purchase was
      // made), we want to give much more credence to what occurs at the
      // beginning.  Every 3 character positions from the beginning becomes a
      // divisor for the addend, so that positions 0-2 are worth 100%, but
      // positions 3-5 are only worth half as much, etc.

      if (index > 2)
        addend = int(double(addend) / int(index / 3));

      score += addend;

      if (! added_bonus)
        bonus = 0;

      index++;
    }

    scores.push_back(score_entry_t(xact, score));
  }

  // Reverse the list so that most recently used accounts are seen first;
  // then, sort the results by descending score, then look at every account
  // ever used among the top ten.  Rank these by number of times used.
  // Lastly, "decay" any latter accounts, so that we give recently used
  // accounts a slightly higher rating in case of a tie.

  std::reverse(scores.begin(), scores.end());
  std::stable_sort(scores.begin(), scores.end(), score_sorter());

  account_use_map account_usage;

  scorecard_t::iterator si = scores.begin();
  int decay = 0;
  for (int i = 0; i < 5 && si != scores.end(); i++, si++) {
    DEBUG("lookup.account",
          "Payee: " << std::setw(5) << std::right << (*si).second <<
          " - " << (*si).first->payee);

    foreach (post_t * post, (*si).first->posts) {
      if (post->account != ref_account) {
        account_use_map::iterator x = account_usage.find(post->account);
        if (x == account_usage.end())
          account_usage.insert(account_use_pair(post->account,
                                                ((*si).second - decay)));
        else
          (*x).second += ((*si).second - decay);
      }
      decay++;
    }
  }

  account_use_vector flat_account_usage(account_usage.begin(),
                                        account_usage.end());

  std::stable_sort(flat_account_usage.begin(), flat_account_usage.end(),
                   usage_sorter());

#if defined(DEBUG_ON)
  if (SHOW_DEBUG("lookup.account")) {
    foreach (account_use_pair& value, flat_account_usage) {
      DEBUG("lookup.account",
            "Account: " << value.second << " - " << value.first->fullname());
    }
  }
#endif

  return flat_account_usage.front().first;
}

} // namespace ledger
