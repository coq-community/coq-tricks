COQ_FILES := $(wildcard src/*.v)
VO_FILES := $(COQ_FILES:.v=.vo)

all: $(VO_FILES)

src/%.vo: src/%.v
	coqc -q -Q . Tricks $< -o $@

src/NoInit.vo: src/NoInit.v
	coqc -q -Q . Tricks -noinit $< -o $@

clean:
	rm -f src/*.vo
