.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset1Sig
	$(COQC) Pset1
	$(COQC) Pset1Check

clean:
	rm -f *.vo *.glob
