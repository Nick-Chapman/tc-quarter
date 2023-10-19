
top: infer

quarter = ../quarter-forth

exe = .stack-work/dist/x86_64-linux/Cabal-3.6.3.0/build/main.exe/main.exe

play: $(exe)
	$(exe) play.list

infer: gen/infer.trace
	git diff $^

$(exe): src/*.hs
	stack build
	touch $(exe)

gen/infer.trace: $(exe) $(quarter)/full.list $(wildcard $(quarter)/f/*)
	$(exe) $(quarter)/full.list | tee $@
