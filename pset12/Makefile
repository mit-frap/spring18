.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset12Sig
	$(COQC) Pset12
	$(COQC) Pset12Check

clean:
	rm -f *.vo *.glob
