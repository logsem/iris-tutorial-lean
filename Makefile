.PHONY: all build out serve clean

PORT ?= 8000

all: out

build:
	lake exe textbook

out: build
	rm -rf out
	mkdir -p out
	cp -r _out/html-multi out/
	cd _out && zip -r ../out/code.zip example-code

serve: out
	cd out/html-multi && python3 -m http.server $(PORT)

clean:
	rm -rf out _out
