ifndef OSTYPE
OSTYPE=$(shell uname -s)
endif

ifeq ($(OSTYPE), Darwin)
#
#  macOS
#
CC=gcc
CXX=g++
WINBASE=win-gtk
EXE=
CFLAGS=-O3
INCLUDE=`pkg-config --cflags gtk+-3.0`
LDFLAGS=`pkg-config --libs gtk+-3.0` -lasmrun -lunix -ldl -lm

else
ifeq ($(OSTYPE), Linux)
#
#  Linux
#
CC=gcc
CXX=g++
WINBASE=win-gtk
EXE=
CFLAGS=-O3
INCLUDE=`pkg-config --cflags gtk+-3.0`
LDFLAGS=`pkg-config --libs gtk+-3.0` -lasmrun -lunix -ldl -lm

else
#
#  MS-Windows
#
CC=x86_64-w64-mingw32-gcc
CXX=x86_64-w64-mingw32-g++
WINBASE=win-d2d
EXE=.exe
CFLAGS=-D_UNICODE -DUNICODE
LDFLAGS=-lasmrun -lunix -lm -ld2d1 -ldwrite

endif
endif

CSP_PATH=../../ocaml-csp/src
GUEDRA_PATH=../../Guedra/src
DRAW_PATH=../../Guedra-draw/src
OCAML_INCLUDE=-I `ocamlc -where` -I $(CSP_PATH) -I $(GUEDRA_PATH) -I $(DRAW_PATH)
OCAMLC_OPTIONS=-bin-annot
OBJECTS=$(GUEDRA_PATH)/win.o $(GUEDRA_PATH)/$(WINBASE).o
CSP_LIB=$(CSP_PATH)/csp.cmx
GUEDRA_LIB=$(GUEDRA_PATH)/guedra.cmxa $(OBJECTS)
DRAW_LIB=$(DRAW_PATH)/draw.cmxa
LIBS=unix.cmxa

#
#  Rules
#
%.cmi:	%.mli
	ocamlc -c $(OCAMLC_OPTIONS) $(OCAML_INCLUDE) $<

%.cmi:	%.ml
	ocamlc -c $(OCAMLC_OPTIONS) $(OCAML_INCLUDE) $<

%.cmo:	%.ml
	ocamlc -c $(OCAMLC_OPTIONS) $(OCAML_INCLUDE) $<

%.cmx:	%.ml
	ocamlopt -c $(OCAMLC_OPTIONS) $(OCAML_INCLUDE) $<

OCAML_SOURCES=\
	error.ml \
	option.ml \
	db.ml \
	col.ml \
	listSet.ml \
	utils.ml \
	id.ml \
	idCol.ml \
	s.ml \
	t.ml \
	tCol.ml \
	e.ml \
	v.ml \
	vCol.ml \
	event.ml \
	eventCol.ml \
	p.ml \
	c.ml \
	cCol.ml \
	stdio.ml \
	posin.ml \
	opCsp.ml \
	tokenCsp.ml \
	lexerCsp.ml \
	parserCsp.ml \
	scc.ml \
	dependency.ml \
	spec.ml \
	mdb.ml \
	eval.ml \
	builtins.ml \
	builtinsCsp.ml \
	univ.ml \
	type.ml \
	lts.ml \
	transitions.ml \
	bfs.ml \
	unfold.ml \
	divergence.ml \
	det.ml \
	acceptances.ml \
	refinement.ml \
	viz.ml \
	report.ml \
	check.ml \
	command.ml \
	drive.ml \
	ts.ml \
	peFig.ml \
	figState.ml \
	pe.ml \
	syncstitch.ml \
	main.ml

OCAML_CMX=\
	error.cmx \
	option.cmx \
	db.cmx \
	col.cmx \
	listSet.cmx \
	utils.cmx \
	id.cmx \
	idCol.cmx \
	t.cmx \
	tCol.cmx \
	s.cmx \
	e.cmx \
	v.cmx \
	vCol.cmx \
	event.cmx \
	eventCol.cmx \
	p.cmx \
	c.cmx \
	cCol.cmx \
	scc.cmx \
	dependency.cmx \
	spec.cmx \
	mdb.cmx \
	univ.cmx \
	eval.cmx \
	builtins.cmx \
	type.cmx \
	lts.cmx \
	transitions.cmx \
	bfs.cmx \
	unfold.cmx \
	divergence.cmx \
	det.cmx \
	acceptances.cmx \
	refinement.cmx \
	viz.cmx \
	report.cmx \
	check.cmx \
	command.cmx \
	stdio.cmx \
	posin.cmx \
	opCsp.cmx \
	tokenCsp.cmx \
	lexerCsp.cmx \
	parserCsp.cmx \
	builtinsCsp.cmx \
	drive.cmx \
	ts.cmx \
	peFig.cmx \
	figState.cmx \
	pe.cmx \
	syncstitch.cmx \
	main.cmx

all:	syncstitch

syncstitch:	$(OCAML_CMX)
	ocamlopt -o $@ $(CSP_LIB) $(GUEDRA_LIB) $(DRAW_LIB) $(LIBS) $^ \
		-cclib "-L `ocamlc -where`" \
		-cclib "$(LDFLAGS)"

clean:
	rm syncstitch $(OCAML_CMX) *.cmi *.cmo *.cmx *.cmt *.o

dep:
	ocamldep $(OCAML_SOURCES) > .depend

-include .depend
