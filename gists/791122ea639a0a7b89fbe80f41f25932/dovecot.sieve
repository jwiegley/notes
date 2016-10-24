require [ "fileinto", "imap4flags", "vacation" ];

if address :contains "from" [ "jwiegley@gmail.com", "johnw@newartisans.com", "johnw@gnu.org" ] {
  setflag "\\Seen";
}

# Keep logwatch logs out of the INBOX
if address :contains "from" [ "logwatch@", "jsgca@yahoo.com" ] {
  setflag "\\Seen";
  fileinto "list.misc";
}

# Throw away junk or useless mail
elsif allof (header :contains "From" [ "info@netflix.com", "discship@netflix.com"],
             header :contains "Subject" "How was the Picture Quality") {
  discard;
}

elsif header :contains "Subject"
    [ "Undelivered Mail Returned to Sender"
    , "Delivery Status Notification (Failure)"
    ] {
  discard;
}

# Mailing lists
elsif header :contains ["To", "From", "Cc", "Sender"] "tarikh@bahai-library.com"   { fileinto "list.bahai.tarjuman"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "tarjuman@bahai-library.com" { fileinto "list.bahai.tarjuman"; }

elsif header :contains "list-id" "<acl2-books.googlegroups.com>"                   { fileinto "list.acl2.books"; }
elsif header :contains "list-id" "<acl2-help.utlists.utexas.edu>"                  { fileinto "list.acl2.help"; }
elsif header :contains "list-id" "<acl2.utlists.utexas.edu>"                       { fileinto "list.acl2"; }
elsif header :contains "list-id" "<admin.haskell.org>"                             { fileinto "list.haskell.admin"; }
elsif header :contains "list-id" "<agda.lists.chalmers.se>"                        { fileinto "list.agda.devel"; }
elsif header :contains "list-id" "<brass-proposal.lists.brass-tacks.org>"          { fileinto "list.bae.brass.proposal"; }
elsif header :contains "list-id" "<bae-brass-commits.googlegroups.com>"            { fileinto "list.bae.brass.commits"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "rings-commit@googlegroups.com" { fileinto "list.brass.commits"; }
elsif header :contains "list-id" "<rings-commits.googlegroups.com>"                { fileinto "list.bae.brass.commits"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "rings-all@googlegroups.com" { fileinto "list.brass.rings"; }
elsif header :contains "list-id" "<rings-all.googlegroups.com>"                    { fileinto "list.bae.brass.rings"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "smedl@noreply.github.com"   { fileinto "list.brass.smedl"; }
elsif header :contains "list-id" "<smedl.brass-rings.github.com>"                  { fileinto "list.bae.brass.smedl"; }
elsif header :contains "list-id" "<beginners.haskell.org>"                         { fileinto "list.haskell.beginners"; }
elsif header :contains "list-id" "<boost-announce.lists.boost.org>"                { fileinto "list.boost.announce"; }
elsif header :contains "list-id" "<boost-users.lists.boost.org>"                   { fileinto "list.boost.users"; }
elsif header :contains "list-id" "<boost.lists.boost.org>"                         { fileinto "list.boost.devel"; }
elsif header :contains "list-id" "<boostcon-plan.googlegroups.com>"                { fileinto "list.boost.cppnow"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "help-debbugs@gnu.org"       { fileinto "list.gnu.debbugs"; }
elsif header :contains "list-id" "<help-debbugs.gnu.org>"                          { fileinto "list.gnu.debbugs"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "tracker@debbugs.gnu.org"    { fileinto "list.emacs.bugs.tracker"; }
elsif header :contains "list-id" "<emacs-bug-tracker.gnu.org>"                     { fileinto "list.emacs.bugs.tracker"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "@debbugs.gnu.org"           { fileinto "list.emacs.bugs"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "bug-gnu-emacs@gnu.org"      { fileinto "list.emacs.bugs"; }
elsif header :contains "list-id" "<bug-gnu-emacs.gnu.org>"                         { fileinto "list.emacs.bugs"; }
elsif header :contains "list-id" "<c++std-admin.accu.org>"                         { fileinto "list.wg21.admin"; }
elsif header :contains "list-id" "<c++std-all.accu.org>"                           { fileinto "list.wg21.all"; }
elsif header :contains "list-id" "<c++std-comm.accu.org>"                          { fileinto "list.wg21.comm"; }
elsif header :contains "list-id" "<c++std-compat.accu.org>"                        { fileinto "list.wg21.compat"; }
elsif header :contains "list-id" "<c++std-core.accu.org>"                          { fileinto "list.wg21.core"; }
elsif header :contains "list-id" "<c++std-date-lib.accu.org>"                      { fileinto "list.wg21.date-lib"; }
elsif header :contains "list-id" "<c++std-edit.accu.org>"                          { fileinto "list.wg21.edit"; }
elsif header :contains "list-id" "<c++std-embed.accu.org>"                         { fileinto "list.wg21.embed"; }
elsif header :contains "list-id" "<c++std-env.accu.org>"                           { fileinto "list.wg21.env"; }
elsif header :contains "list-id" "<c++std-ext.accu.org>"                           { fileinto "list.wg21.ext"; }
elsif header :contains "list-id" "<c++std-ibof.accu.org>"                          { fileinto "list.wg21.ibof"; }
elsif header :contains "list-id" "<c++std-intl.accu.org>"                          { fileinto "list.wg21.intl"; }
elsif header :contains "list-id" "<c++std-lib.accu.org>"                           { fileinto "list.wg21.lib"; }
elsif header :contains "list-id" "<c++std-migration.accu.org>"                     { fileinto "list.wg21.migration"; }
elsif header :contains "list-id" "<c++std-modules.accu.org>"                       { fileinto "list.wg21.modules"; }
elsif header :contains "list-id" "<c++std-networking.accu.org>"                    { fileinto "list.wg21.networking"; }
elsif header :contains "list-id" "<c++std-news.accu.org>"                          { fileinto "list.wg21.news"; }
elsif header :contains "list-id" "<c++std-parallel.accu.org>"                      { fileinto "list.wg21.parallel"; }
elsif header :contains "list-id" "<c++std-perf.accu.org>"                          { fileinto "list.wg21.perf"; }
elsif header :contains "list-id" "<c++std-rationale.accu.org>"                     { fileinto "list.wg21.rationale"; }
elsif header :contains "list-id" "<c++std-sci.accu.org>"                           { fileinto "list.wg21.sci"; }
elsif header :contains "list-id" "<c++std-syntax.accu.org>"                        { fileinto "list.wg21.syntax"; }
elsif header :contains "list-id" "<c++std-ustag.accu.org>"                         { fileinto "list.wg21.ustag"; }
elsif header :contains "list-id" "<cabal-devel.haskell.org>"                       { fileinto "list.haskell.cabal"; }
elsif header :contains "list-id" "<cfe-dev.cs.uiuc.edu>"                           { fileinto "list.clang.devel"; }
elsif header :contains "list-id" "<cloud-haskell-developers.googlegroups.com>"     { fileinto "list.haskell.cloud"; }
elsif header :contains "list-id" "<commercialhaskell.googlegroups.com>"            { fileinto "list.haskell.commercial"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "core-libraries-committee@haskell.org"      { fileinto "list.haskell.libraries"; }
elsif header :contains "list-id" "<core-libraries-committee.haskell.org>"                         { fileinto "list.haskell.libraries"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "committee@haskell.org"      { fileinto "list.haskell.committee"; }
elsif header :contains "list-id" "<committee.haskell.org>"                         { fileinto "list.haskell.committee"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "deepspec@lists.cs.princeton.edu" { fileinto "list.coq.deepspec"; }
elsif header :contains "list-id" "<deepspec.lists.cs.princeton.edu>"               { fileinto "list.coq"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "coq-club@inria.fr"          { fileinto "list.coq"; }
elsif header :contains "list-id" "<coq-club.inria.fr>"                             { fileinto "list.coq"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "coqdev@inria.fr"            { fileinto "list.coq.devel"; }
elsif header :contains "list-id" "<coqdev.inria.fr>"                               { fileinto "list.
coq.devel"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "fiat@lists.csail.mit.edu"   { fileinto "list.coq.fiat"; }
elsif header :contains "list-id" "<fiat.lists.csail.mit.edu>"                      { fileinto "list.
coq.fiat"; }
elsif header :contains "list-id" "<emacs-buildstatus.gnu.org>"                     { fileinto "list.emacs.buildstatus"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "emacs-devel-owner@gnu.org"  { fileinto "list.emacs.devel.owner"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "emacs-devel@gnu.org"        { fileinto "list.emacs.devel"; }
elsif header :contains "list-id" "<emacs-devel.gnu.org>"                           { fileinto "list.emacs.devel"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "emacs-tangents@gnu.org"        { fileinto "list.emacs.tangents"; }
elsif header :contains "list-id" "<emacs-tangents.gnu.org>"                           { fileinto "list.emacs.tangents"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "gnu-prog@gnu.org"           { fileinto "list.gnu.prog"; }
elsif header :contains "list-id" "<gnu-prog.gnu.org>"                              { fileinto "list.gnu.prog"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "gnu-prog-discuss@gnu.org"   { fileinto "list.gnu.prog.discuss"; }
elsif header :contains "list-id" "<gnu-prog-discuss.gnu.org>"                      { fileinto "list.gnu.prog.discuss"; }
elsif header :contains "list-id" "<emacs-diffs.gnu.org>"                           { fileinto "list.emacs.diffs"; }
elsif header :contains "list-id" "<emacs-elpa-diffs.gnu.org>"                      { fileinto "list.emacs.elpa.diffs"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "emacs-orgmode@gnu.org"      { fileinto "list.emacs.orgmode"; }
elsif header :contains "list-id" "<emacs-orgmode.gnu.org>"                         { fileinto "list.emacs.orgmode"; }
elsif header :contains "list-id" "<ext.lists.isocpp.org>"                          { fileinto "list.isocpp.ext"; }
elsif header :contains "list-id" "<google-summer-of-code-mentors-list.googlegroups.com>" { fileinto "list.gsoc.mentors"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "ghc-devs@haskell.org"       { fileinto "list.haskell.ghc.devel"; }
elsif header :contains "list-id" "<ghc-devs.haskell.org>"                          { fileinto "list.haskell.ghc.devel"; }
elsif header :contains "list-id" "<ghc-linker.googlegroups.com>"                   { fileinto "list.haskell.ghc.linker"; }
elsif header :contains "list-id" "<glasgow-haskell-users.haskell.org>"             { fileinto "list.haskell.ghc"; }
elsif header :contains "list-id" "<gnu-emacs-sources.gnu.org>"                     { fileinto "list.emacs.sources"; }
elsif header :contains "list-id" "<hackage-trustees.noreply.github.com>"           { fileinto "list.haskell.hackage-trustees"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "haskell-community@haskell.org" { fileinto "list.haskell.community"; }
elsif header :contains "list-id" "<haskell-community.haskell.org>"                 { fileinto "list.haskell.community"; }
elsif header :contains "list-id" "<haskell-infrastructure.community.galois.com>"   { fileinto "list.haskell.infrastructure"; }
elsif header :contains "list-id" "<haskell-pipes.googlegroups.com>"                { fileinto "list.haskell.pipes"; }
elsif header :contains "list-id" "<rfcs.haskell.github.com>"                       { fileinto "list.haskell.prime"; }
elsif header :contains "list-id" "<haskell-prime.haskell.org>"                     { fileinto "list.haskell.prime"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "haskell-prime@haskell.org" { fileinto "list.haskell.prime"; }
elsif header :contains "list-id" "<haskell-cafe.haskell.org>"                      { fileinto "list.haskell.cafe"; }
elsif header :contains "list-id" "<haskell.haskell.org>"                           { fileinto "list.haskell.announce"; }
elsif header :contains "list-id" "<help-emacs-windows.gnu.org>"                    { fileinto "list.emacs.windows"; }
elsif header :contains "list-id" "<help-gnu-emacs.gnu.org>"                        { fileinto "list.emacs.help"; }
elsif header :contains "list-id" "<hott-cafe.googlegroups.com>"                    { fileinto "list.hott"; }
elsif header :contains "list-id" "<idris-lang.googlegroups.com>"                   { fileinto "list.idris.devel"; }
elsif header :contains "list-id" "<info-gnu-emacs.gnu.org>"                        { fileinto "list.emacs.announce"; }
elsif header :contains "list-id" "<ledger.ledger.github.com>"                      { fileinto "list.ledger.devel"; }
elsif header :contains "list-id" "<ledger-cli.googlegroups.com>"                   { fileinto "list.ledger.devel"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "ledger-cli@googlegroups.com" { fileinto "list.ledger.devel"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "admin@haskell.org"          { fileinto "list.haskell.admin"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "libraries@haskell.org"      { fileinto "list.haskell.libraries"; }
elsif header :contains "list-id" "<libraries.haskell.org>"                         { fileinto "list.haskell.libraries"; }
elsif header :contains "list-id" "<llvmdev.cs.uiuc.edu>"                           { fileinto "list.llvm.devel"; }
elsif header :contains "list-id" "<llvm-devmeeting.lists.llvm.org>"                { fileinto "list.llvm.devel"; }
elsif header :contains "list-id" "<nix-dev.lists.science.uu.nl>"                   { fileinto "list.nix.devel"; }
elsif header :contains "list-id" "<no-reply.google-melange.appspotmail.com>"       { fileinto "list.haskell.gsoc"; }
elsif header :contains "list-id" "<proofgeneral-devel.inf.ed.ac.uk>"               { fileinto "list.emacs.proofgeneral"; }
elsif header :contains ["Subject"] "[sw-dev]"                                      { fileinto "list.riscv.devel"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "sw-dev@lists.riscv.org"     { fileinto "list.riscv.devel"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "sw-dev@groups.riscv.org"    { fileinto "list.riscv.devel"; }
elsif header :contains "list-id" "<ryppl-dev.googlegroups.com>"                    { fileinto "list.boost.ryppl"; }
elsif header :contains "list-id" "<safe-breeze.lists.crash-safe.org>"              { fileinto "list.safe.breeze"; }
elsif header :contains "list-id" "<safe-commit-watchers.lists.crash-safe.org>"     { fileinto "list.safe.commits"; }
elsif header :contains "list-id" "<safe-hw.lists.crash-safe.org>"                  { fileinto "list.safe.hw"; }
elsif header :contains "list-id" "<safe-os.lists.crash-safe.org>"                  { fileinto "list.safe.os"; }
elsif header :contains "list-id" "<safe-verif.lists.crash-safe.org>"               { fileinto "list.safe.verify"; }
elsif header :contains "list-id" "<safe.lists.crash-safe.org>"                     { fileinto "list.safe.devel"; }
elsif header :contains "list-id" "<shake-build-system.googlegroups.com>"           { fileinto "list.shake.devel"; }
elsif header :contains "list-id" "<ssreflect.msr-inria.inria.fr>"                  { fileinto "list.coq.ssreflect"; }
elsif header :contains "list-id" "<std-discussion.isocpp.org>"                     { fileinto "list.isocpp.discussion"; }
elsif header :contains "list-id" "<lib.lists.isocpp.org>"                          { fileinto "list.isocpp.lib"; }
elsif header :contains "list-id" "<core.lists.isocpp.org>"                         { fileinto "list.isocpp.core"; }
elsif header :contains "list-id" "<all.lists.isocpp.org>"                          { fileinto "list.isocpp.all"; }
elsif header :contains "list-id" "<admin.lists.isocpp.org>"                        { fileinto "list.isocpp.admin"; }
elsif header :contains "list-id" "<edit.lists.isocpp.org>"                         { fileinto "list.isocpp.edit"; }
elsif header :contains "list-id" "<std-proposals.isocpp.org>"                      { fileinto "list.isocpp.proposals"; }
elsif header :contains "list-id" "<tempest.lists.crash-safe.org>"                  { fileinto "list.safe.tempest"; }
elsif header :contains "list-id" "<types-list.lists.seas.upenn.edu>"               { fileinto "list.types"; }
elsif header :contains "list-id" "github.com"                                      { fileinto "list.github"; }

#if not header :contains "Precedence" ["bulk", "list"] {
#    vacation :days 2
#         :addresses [ "jwiegley@gmail.com"
#                    , "johnw@newartisans.com"
#                    , "johnw@gnu.org" ]
#         :subject "Out of the office until 2012-06-12"
#"I am presently out of the office on vacation, until 2012-06-12.";
#}
