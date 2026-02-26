FUTHARK_BACKEND=cuda

.PHONY: run

run: benchmark
	./benchmark --backend=$(FUTHARK_BACKEND)

benchmark: tooling/benchmark.mlb tooling/benchmark.sml
	mlkit -o $@ $<
