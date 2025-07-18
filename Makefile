all: build

build:
	cargo build --release
	mkdir -p bin
	cp -f target/release/obol bin

build-dev:
	cargo build
	mkdir -p bin
	cp -f target/debug/obol bin
