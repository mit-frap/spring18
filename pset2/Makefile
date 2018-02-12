.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset2Sig
	$(COQC) Pset2
	$(COQC) Pset2Check

clean:
	rm -f *.vo *.glob
