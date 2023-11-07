
top: regression

quarter = ../quarter-forth

exe = .stack-work/dist/x86_64-linux/Cabal-3.6.3.0/build/main.exe/main.exe

default = x86

run: run-$(default)
tc: tc-$(default)
ti: ti-$(default)

regression: gen/infer.trace
	git diff $^

gen/infer.trace: $(exe) $(quarter)/$(default).list $(wildcard $(quarter)/f/*) Makefile
	$(exe) -unit -ti $(quarter)/$(default).list | tee $@

tc-unit-tests:
	$(exe)

# Just execute
run-%:
	$(exe) $(quarter)/$*.list

# Execute + type-checking (show errors)
tc-%:
	$(exe) -tc $(quarter)/$*.list

# Execute + type-checking (show errors + inferred types)
ti-%:
	$(exe) -ti $(quarter)/$*.list

$(exe): src/*.hs
	stack build
	touch $(exe)

