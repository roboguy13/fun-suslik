all: formal-def.pdf
formal-def.pdf: formal-def.tex defs.tex # *.bib
	pdflatex $<
	# bibtex $(patsubst %.tex,%.aux, $<)
	# pdflatex $<
	pdflatex $<


%.pdf: %.tex
	pdflatex $<

clean:
	rm -f formal-def.aux
	rm -f formal-def.bbl
	rm -f formal-def.blg
	rm -f formal-def.out
	rm -f formal-def.log
	rm -f formal-def.pdf

