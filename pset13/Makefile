.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset13Sig
	$(COQC) Pset13
	$(COQC) Pset13Check

clean:
	rm -f *.vo *.glob
