.SUFFIXES: .tex .bib .aux .bbl .dvi .ps .pdf .thy

all:	opsets.pdf papoc.pdf

%.pdf:	%.bbl
	pdflatex $(@:.pdf=)
	pdflatex $(@:.pdf=)

%.bbl:	references.bib %.aux
	bibtex $(@:.bbl=)

%.aux:	*.tex
	pdflatex $(@:.aux=)

%-arxiv.tex: %.tex %.bbl
	sed -e "/\\\\bibliography{references}/ r $(@:-arxiv.tex=.bbl)" -e '/\\bibliography{references}/ d' $(@:-arxiv.tex=.tex) > $@

list-insert.tex: ../isabelle/Datalog_Insert.thy
	awk -f isabelle-to-latex.awk $< > $@

assignment.tex: ../isabelle/Datalog_Assignment.thy
	awk -f isabelle-to-latex.awk $< > $@

clean:
	rm -f opsets.{log,aux,out,bbl,blg,dvi,ps,pdf} *-arxiv.tex
