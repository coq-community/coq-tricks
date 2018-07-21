COQ_FILES := $(wildcard *.v) $(wildcard Learn/*.v)
VO_FILES := $(COQ_FILES:.v=.vo)

all: $(VO_FILES)

%.vo: %.v
	coqc -q $< -o $@
