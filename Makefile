.PHONY: all

all: FO-prover

FO-prover: app/*.hs
	./build.sh

clean:
	rm FO-prover