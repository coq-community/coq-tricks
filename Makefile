COQ_FILES := $(wildcard *.v) $(wildcard Learn/*.v)
VO_FILES := $(COQ_FILES:.v=.vo)

all: $(VO_FILES)

NoInit.vo: NoInit.v
	coqc -q -noinit $< -o $@

%.vo: %.v
	coqc -q $< -o $@
