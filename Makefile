all: build

build:
	cargo build --release
	mkdir -p bin
	cp -f target/release/obol bin
	cp -f target/release/obol-driver bin

build-offline:
	cargo build --release --offline
	mkdir -p bin
	cp -f target/release/obol bin
	cp -f target/release/obol-driver bin

build-dev:
	cargo build
	mkdir -p bin
	cp -f target/debug/obol bin
	cp -f target/debug/obol-driver bin
