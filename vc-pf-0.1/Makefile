%Code.hs : %.v
	coqc $*.v

%.o : %.hs
	ghc -O4 -c $*.hs

%Wrapper: %Code.o
	ghc -O4 $*Wrapper.hs

all: STVWrapper FPTPWrapper
test: fptp-test stv-test

stv-test: STVWrapper
	for i in 100 1000 5000 10000;  do  \
    ./stv-rand.pl $$i | ./STVWrapper; \
  done

fptp-test: FPTPWrapper
	for i in 100 1000 5000 10000;  do  \
    ./fptp-rand.pl $$i | ./FPTPWrapper ; \
  done

tests: fptp-test stv-test

clean:
	rm STVWrapper FPTPWrapper *.o *.vo *.glob *Code.hs *.hi *.tar.gz 2>/dev/null; exit 0

dist: clean
	tar czf vc-pf-0.1.tar.gz `ls | fgrep -v '.tar.gz'`
