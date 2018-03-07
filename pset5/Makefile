.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset5Sig
	$(COQC) Pset5
	$(COQC) Pset5Check

clean:
	rm -f *.vo *.glob
