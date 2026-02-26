.PHONY: run

run: benchmark
	./benchmark

benchmark: tooling/benchmark.sml
	mlkit -o $@ $<
