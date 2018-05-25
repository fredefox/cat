build: src/**.agda
	agda --library-file ./libraries src/Cat.agda

clean:
	find src -name "*.agdai" -type f -delete

html:
	agda --html src/Cat.agda

upload: html
	scp -r html/ remote11.chalmers.se:www/cat/doc/
