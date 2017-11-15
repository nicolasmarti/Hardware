PROVER=z3

all:
	why3 prove -P $(PROVER) builtins.why
	why3 prove -P $(PROVER) -L . 01/Not.why
