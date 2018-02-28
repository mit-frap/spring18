.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset4Sig
	$(COQC) Pset4
	$(COQC) Pset4Check

clean:
	rm -f *.vo *.glob
