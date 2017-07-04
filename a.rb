	Tue Jul  4 12:32 2017 Time and Allocation Profiling Report  (Final)

	   ObjectsArrows +RTS -p -RTS length 100

	total time  =        0.00 secs   (2 ticks @ 1000 us, 1 processor)
	total alloc =  26,648,088 bytes  (excludes profiling overheads)

COST CENTRE            MODULE SRC                              %time %alloc

composablePairs.\      Main   ObjectsArrows.hs:41:36-70         50.0   36.1
composablePairsStep.go Main   ObjectsArrows.hs:(34,5)-(38,52)   50.0   62.5
composablePairsStep    Main   ObjectsArrows.hs:(30,1)-(38,52)    0.0    1.2


                                                                                                     individual      inherited
COST CENTRE                 MODULE                SRC                             no.     entries  %time %alloc   %time %alloc

MAIN                        MAIN                  <built-in>                      107          0    0.0    0.0   100.0  100.0
 CAF                        Main                  <entire-module>                 213          0    0.0    0.0     0.0    0.0
  composablePairs           Main                  ObjectsArrows.hs:41:1-74        216          1    0.0    0.0     0.0    0.0
  main                      Main                  ObjectsArrows.hs:(65,1)-(77,37) 214          1    0.0    0.0     0.0    0.0
 CAF                        GHC.Conc.Signal       <entire-module>                 193          0    0.0    0.0     0.0    0.0
 CAF                        GHC.IO.Encoding       <entire-module>                 176          0    0.0    0.0     0.0    0.0
 CAF                        GHC.IO.Encoding.Iconv <entire-module>                 174          0    0.0    0.0     0.0    0.0
 CAF                        GHC.IO.Handle.FD      <entire-module>                 165          0    0.0    0.1     0.0    0.1
 CAF                        GHC.IO.Handle.Text    <entire-module>                 163          0    0.0    0.0     0.0    0.0
 CAF                        Text.Read.Lex         <entire-module>                 134          0    0.0    0.0     0.0    0.0
 main                       Main                  ObjectsArrows.hs:(65,1)-(77,37) 215          0    0.0    0.1   100.0   99.8
  composablePairs           Main                  ObjectsArrows.hs:41:1-74        217          0    0.0    0.0   100.0   99.8
   composablePairs.\        Main                  ObjectsArrows.hs:41:36-70       218        100   50.0   36.1   100.0   99.8
    composablePairsStep     Main                  ObjectsArrows.hs:(30,1)-(38,52) 219        100    0.0    1.2    50.0   63.7
     composablePairsStep.go Main                  ObjectsArrows.hs:(34,5)-(38,52) 220       5050   50.0   62.5    50.0   62.5
