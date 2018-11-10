COQ_FILES := $(wildcard *.v) $(wildcard Learn/*.v)
VO_FILES := $(COQ_FILES:.v=.vo)

all: $(VO_FILES)

NoInit.vo: NoInit.v
	coqc -q -R . Top -noinit $< -o $@

# the one dependency in these examples
Learn/Example.vo: Learn/Learn.vo

%.vo: %.v
	coqc -q -R . Top $< -o $@

clean:
	rm -f *.vo
	rm -f Learn/*.vo
