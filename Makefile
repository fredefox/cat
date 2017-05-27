PROJECT = cat
PDF = $(PROJECT).pdf
NOTES = $(PROJECT).md

preview: report
	xdg-open $(PDF)

report: $(PDF)

$(PDF): $(NOTES)
	pandoc $(NOTES) \
		-o $(PDF) \
		--latex-engine=xelatex \
		--variable urlcolor=cyan \
		-V papersize:a4 \
		-V geometry:margin=1.5in \
		--filter pandoc-citeproc

github: README.md

README.md: $(NOTES)
	pandoc $(NOTES) \
		-o README.md

run:
	stack exec lab4

build:
	stack build

dist: report
	tar \
		--transform "s/^/$(PROJECT)\//" \
		-zcvf $(PROJECT).tar.gz \
		$(SOURCE) \
		LICENSE \
		stack.yaml \
		lab4.cabal \
		Makefile \
		$(PDF)
