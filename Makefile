FUTHARK_BACKEND=cuda

.PHONY: run

run: benchmark lib
	./benchmark --backend=$(FUTHARK_BACKEND)

benchmark: tooling/benchmark.mlb tooling/benchmark.sml tooling/lib
	mlkit -o $@ $<

lib: futhark.pkg
	futhark pkg sync

tooling/lib: tooling/sml.pkg
	cd tooling && smlpkg sync
