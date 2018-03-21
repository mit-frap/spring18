.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset7Sig
	$(COQC) Pset7
	$(COQC) Pset7Check

clean:
	rm -f *.vo *.glob
