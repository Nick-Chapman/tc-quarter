
top: infer

quarter = ../quarter-forth
beeb = ../beeb-quarter

exe = .stack-work/dist/x86_64-linux/Cabal-3.6.3.0/build/main.exe/main.exe

beeb: $(exe) $(wildcard $(beeb)/f/*)
	$(exe) $(beeb)/full.list

play: $(exe)
	$(exe) play.list

infer: gen/infer.trace
	git diff $^

$(exe): src/*.hs
	stack build
	touch $(exe)

system = $(quarter)/full.list

gen/infer.trace: $(exe) $(system) $(wildcard $(quarter)/f/*)
	$(exe) $(system) | tee $@
