build: src/**.agda
	agda src/Cat.agda

clean:
	find src -name "*.agdai" -type f -delete

html: src/**.agda
	agda --html src/Cat.agda

upload: html
	scp -r html/ remote11.chalmers.se:www/cat/doc/

.PHONY: upload clean
