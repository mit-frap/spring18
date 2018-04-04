.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset8Sig
	$(COQC) Pset8
	$(COQC) Pset8Check

clean:
	rm -f *.vo *.glob
