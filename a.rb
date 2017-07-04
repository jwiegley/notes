	Tue Jul  4 12:35 2017 Time and Allocation Profiling Report  (Final)

	   ObjectsArrows +RTS -p -RTS length 1000

	total time  =        3.82 secs   (3824 ticks @ 1000 us, 1 processor)
	total alloc = 25,457,562,176 bytes  (excludes profiling overheads)

COST CENTRE            MODULE SRC                              %time %alloc

composablePairsStep.go Main   ObjectsArrows.hs:(34,5)-(38,52)   49.1   63.1
composablePairs.\      Main   ObjectsArrows.hs:41:36-70         39.8   36.8
main                   Main   ObjectsArrows.hs:(65,1)-(77,37)   10.9    0.0


                                                                                                     individual      inherited
COST CENTRE                 MODULE                SRC                             no.     entries  %time %alloc   %time %alloc

MAIN                        MAIN                  <built-in>                      107          0    0.0    0.0   100.0  100.0
 CAF                        Main                  <entire-module>                 213          0    0.0    0.0     0.0    0.0
  composablePairs           Main                  ObjectsArrows.hs:41:1-74        216          1    0.0    0.0     0.0    0.0
  main                      Main                  ObjectsArrows.hs:(65,1)-(77,37) 214          1    0.0    0.0     0.0    0.0
 CAF                        GHC.Conc.Signal       <entire-module>                 193          0    0.0    0.0     0.0    0.0
 CAF                        GHC.IO.Encoding       <entire-module>                 176          0    0.0    0.0     0.0    0.0
 CAF                        GHC.IO.Encoding.Iconv <entire-module>                 174          0    0.0    0.0     0.0    0.0
 CAF                        GHC.IO.Handle.FD      <entire-module>                 165          0    0.0    0.0     0.0    0.0
 CAF                        GHC.IO.Handle.Text    <entire-module>                 163          0    0.0    0.0     0.0    0.0
 CAF                        Text.Read.Lex         <entire-module>                 134          0    0.0    0.0     0.0    0.0
 main                       Main                  ObjectsArrows.hs:(65,1)-(77,37) 215          0   10.9    0.0   100.0  100.0
  composablePairs           Main                  ObjectsArrows.hs:41:1-74        217          0    0.0    0.0    89.1  100.0
   composablePairs.\        Main                  ObjectsArrows.hs:41:36-70       218       1000   39.8   36.8    89.1  100.0
    composablePairsStep     Main                  ObjectsArrows.hs:(30,1)-(38,52) 219       1000    0.2    0.1    49.3   63.2
     composablePairsStep.go Main                  ObjectsArrows.hs:(34,5)-(38,52) 220     500500   49.1   63.1    49.1   63.1
