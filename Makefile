COQ_FILES := $(wildcard src/*.v)
VO_FILES := $(COQ_FILES:.v=.vo)

# this allows some customization of flags for particular files
COQ_ARGS :=

all: $(VO_FILES)

src/%.vo: src/%.v
	coqc -q -Q src Tricks $(COQ_ARGS) $< -o $@

# these rules set COQ_ARGS where needed
src/NoInit.vo: COQ_ARGS = -noinit
src/TacticNotationOptionalParams.vo: COQ_ARGS = -async-proofs-cache force

clean:
	rm -f src/*.vo
