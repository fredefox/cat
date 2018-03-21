build: src/**.agda
	agda src/Cat.agda

clean:
	find src -name "*.agdai" -type f -delete
