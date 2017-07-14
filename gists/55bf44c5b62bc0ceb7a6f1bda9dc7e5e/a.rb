>>>>> Kidd, Steven W <kidd9@purdue.edu> writes:

> Here is a layout of what I have done so far. If I can figure out a way to
> better show my progress I will go through an write a more through account.
> Do you think using github would be helpful? I could push changes to a branch
> every so often, then github will keep track of them. I could also look into
> using Haskell's literate programming (.lhs) functionality. I am going to
> annotate "bytestring" files with B and "bytestring-fiat" files with F.

> My progress so far has fallen into two stages.

> After getting bytestring-fiat made and known to cabal. I began by working
> only through cabal, modifying the wai/warp/warp.cabal
> <https://github.com/yesodweb/wai/blob/master/warp/warp.cabal> file,

> The goal here being once dependencies where correct then it would compile.

>   *   I replaced instances of bytestring with bytestring-fiat
>      *    Several files in Warp depend on B.Data.ByteString.Internal so this rasied errors explaining that 'bytestring' was a module I needed to add to the 'build-depends' section of the warp file.

>   *   Working to solve the above by finding the correct *.cabal file syntax to exclude B.ByteString and include F.ByteString, basically wanting a version of "bytestring" with B.ByteString replaced with F.ByteString
>      *   this did not work. Older version of cabal allow hiding modules from packages but current version does not
>      *   using ghc commands in the 'Ghc-Options' section of the *.cabal file did not help, as only 'dynamic' compiler options are allowed in cabal files
>   *   I then compiled a version of "bytestring" called "altbytestring" where B.Data.ByteString is listed as a hidden module. I removed "bytestring" from the 'build-depends' section of the warp.cabal file and repleced it with 'altbytestring' and 'bytestring-fiat'. The idea being that, with B.ByteString hidden, import statements to 'Data.ByteString' in the warp source code would default to F.Data.ByteString. This allowed compiling parts of warp without getting 'Ambiguous occurrence' errors.
>      *   I was still stuck with errors of the form 'cannot match Internal.PS0 with B.ByteString' as the B.Data.Internal file used and expected B.ByteStrings while the warp files now were using F.ByteStrings.

> Using only cabal failed at this point and I began thinking that I was going
> to have to edit the source code to get B.Data.ByteString.Internal to work
> with F.ByteStrings.

>   *    I started by replacing "import Data.ByteString.Internal" statements with "import Data.ByteString.Fiat.Internal" in the warp source. The idea being that F.Data.ByteString.Fiat.Internal would contain the functions I needed, ready to work with F.ByteString.
>      *   This allowed the compilation to continue but through an error stating that F.ByteString needed to be an instance of 'Read'
>         *   I added an instance of read to F.Data.ByteString.Fiat.Internal
>      *   I began getting errors of the form "expected ByteString, given Internal.PS0"
>         *   after mucking around, I discovered that the http2 package being used in warp expects B.ByteStrings in functions where I am now passing it F.ByteStrings
>   *   I expanded my recompilation efforts to include the "http2" package. I copied the http2 package source code into a new directory "althttp2" and began making the changed necessary to make it compile against bytestring-fiat, instead of bytestring.
>      *   this has amounted to :

>                             while(1) {

>                                        -- try to compile http2 by typing 'cabal install' in the main directory

>                                        -- receive error message explaining that a B.ByteString was expected insted of an F.ByteString

>                                        -- go to file where the error is and link it against F.Data.ByteString.Fiat.Internal instead of B.Data.ByteString.Internal

>                                        -- link the file against F.Data.ByteString

>                                        -- try to compile http2 again

>                                        -- recieve error stating that functions cannot be found. These were included in B.Data.ByteString.Internal but are now not                                            found in F.Data.ByteString.Fiat.Internal

>                                        -- add the necessary functions to F.Data.ByteString.Fiat.Internal, allowing compilation to continue some more

>                             }

> Eventually I expect this process will end. I have been making progress
> adding functions to F.Data.ByteString.Fiat.Internal.

> I will send a follow up email with my versions of F.Data.ByteString and
> F.Data.ByteString.Fiat.Internal

> Regards,

> Steven
