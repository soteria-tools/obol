all: build

build:
	cargo build --release
	mkdir -p bin
	cp -f target/release/obol bin
