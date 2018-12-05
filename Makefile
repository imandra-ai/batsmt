
build: release

release:
	cargo build --release

check:
	cargo check

clean:
	cargo clean

test:
	cargo test -- --nocapture

test-release:
	cargo test --release -- --nocapture

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make check ; \
	done
