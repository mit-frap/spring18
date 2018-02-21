.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset3Sig
	$(COQC) Pset3
	$(COQC) Pset3Check

clean:
	rm -f *.vo *.glob
