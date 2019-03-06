.PHONY: all

LIBS=3rdparty/finmap.vo 3rdparty/bigop_aux.vo

%.vo: %.v
	coqc -R lib 3rdparty $<

lib/bigop_aux.vo: 3rdparty/finmap.vo

all: $(LIBS)
clean:
	rm -r 3rdparty/*.vo
