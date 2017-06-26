.SUFFIXES: .tex .bib .aux .bbl .dvi .ps .pdf

all:	opsets.pdf

%.pdf:	%.bbl
	pdflatex $(@:.pdf=)
	pdflatex $(@:.pdf=)

%.bbl:	references.bib %.aux
	bibtex $(@:.bbl=)

%.aux:	*.tex
	pdflatex $(@:.aux=)

%-arxiv.tex: %.tex %.bbl
	sed -e "/\\\\bibliography{references}/ r $(@:-arxiv.tex=.bbl)" -e '/\\bibliography{references}/ d' $(@:-arxiv.tex=.tex) > $@

clean:
	rm -f *.{log,aux,out,bbl,blg,dvi,ps,pdf} *-arxiv.tex
