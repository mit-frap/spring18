.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset11Sig
	$(COQC) Pset11
	$(COQC) Pset11Check

clean:
	rm -f *.vo *.glob
