LC=pdflatex
LCFLAGS=-shell-escape

all: presentation.pdf

%.pdf: %.tex
	$(LC) $(LCFLAGS) $<

clean:
	rm *.aux *.log *.pdf *.out *.snm *.toc *.nav
