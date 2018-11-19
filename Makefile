COQ_FILES := $(wildcard *.v)
VO_FILES := $(COQ_FILES:.v=.vo)

all: $(VO_FILES)

NoInit.vo: NoInit.v
	coqc -q -R . Top -noinit $< -o $@

%.vo: %.v
	coqc -q -R . Top $< -o $@

clean:
	rm -f *.vo
