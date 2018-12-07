
build: release

release:
	cargo build --release --all

debug:
	cargo build --all

check:
	cargo check --all

clean:
	cargo clean

TEST_FLAGS ?= --test-threads=1 --nocapture

test:
	cargo test -- $(TEST_FLAGS)

test-release:
	cargo test --release -- $(TEST_FLAGS)

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make check ; \
	done
