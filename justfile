build:
	cargo build

clean:
	git clean -Xdf

test:
	cargo test

lint:
	cargo fmt --check
	cargo clippy --all-targets -- -Dwarnings

check: build lint test
