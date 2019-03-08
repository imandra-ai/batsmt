
J ?= 3

build: release

release:
	cargo build --release --all

debug:
	cargo build --all

#release-debug:
#	RUSTFLAGS="-g" cargo build --release --all

check:
	cargo check --all

clean:
	cargo clean

doc:
	cargo doc

TEST_FLAGS ?= --test-threads=1 --nocapture

test-debug:
	cargo test -- $(TEST_FLAGS)
	#RUST_BACKTRACE=full cargo test -- $(TEST_FLAGS)

test-release:
	cargo test --release -- $(TEST_FLAGS)

LOGITEST_OPTS = -j $(J)
DATE=$(shell date +%FT%H:%M)
logitest-benchs:
	@mkdir -p snapshots
	@logitest run -c benchs/conf.toml $(LOGITEST_OPTS) \
	  --meta `git rev-parse HEAD` --summary snapshots/bench-$(DATE).txt \
	  --csv snapshots/bench-$(DATE).csv

dev: check test-release build

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make check ; \
	done
