.PHONY: run

run: benchmark
	./benchmark

benchmark: benchmark.sml
	mlkit -o $@ $<
