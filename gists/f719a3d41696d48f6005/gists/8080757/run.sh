rm SpeedTest SpeedTest.o
ghc -DSPEED_BUG=1 -threaded -O2 -main-is SpeedTest SpeedTest.hs SpeedTestC.c
time ./SpeedTest

rm SpeedTest SpeedTest.o
ghc -threaded -O2 -main-is SpeedTest SpeedTest.hs SpeedTestC.c
time ./SpeedTest