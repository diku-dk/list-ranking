FUTHARK_BACKEND=cuda

.PHONY: run

run: benchmark lib
	./benchmark --backend=$(FUTHARK_BACKEND)

# A version of the run target with much fewer workloads, for testing the tooling.
run-fast: benchmark lib
	./benchmark --backend=$(FUTHARK_BACKEND) -k 3 --min-n 100000 --max-n 1000000

benchmark: tooling/benchmark.mlb tooling/benchmark.sml tooling/lib
	mlkit -o $@ $<

lib: futhark.pkg
	futhark pkg sync

tooling/lib: tooling/sml.pkg
	cd tooling && smlpkg sync
