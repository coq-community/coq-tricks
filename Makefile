COQ_FILES := $(wildcard src/*.v)
VO_FILES := $(COQ_FILES:.v=.vo)

all: $(VO_FILES)

src/%.vo: src/%.v
	coqc -q -R . Top $< -o $@

src/NoInit.vo: src/NoInit.v
	coqc -q -R . Top -noinit $< -o $@

clean:
	rm -f src/*.vo
