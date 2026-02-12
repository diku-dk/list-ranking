# List ranking experiments

This repository contains implementations of various algorithms for list ranking.
The eventual goal is to construct a paper comparing list ranking algorithms on
GPUs, inspired by the prior work:

* [A Comparison of the Performance of List Ranking and Connected Components
  Algorithms on SMP and MTA Shared-Memory
  Systems](https://www.semanticscholar.org/paper/A-Comparison-of-the-Performance-of-List-Ranking-and-Bader-Cong/f95a7864e95184180a6b55357149b3712b5aa73f)

* [List ranking and list scan on the Cray
  C-90](https://dl.acm.org/doi/10.1145/181014.181049)

## Running experiments

You will need to install the [Futhark compiler](https://futhark-lang.org). Then
download the package dependencies:

```
$ futhark pkg sync
```

And run the benchmarks using a GPU backend (`hip` and `cuda` is recommended):

```
$ futhark bench --backend=cuda list_ranking.fut
```

## Acknowledgements

The hedge heroes Therese Lyngby and Alba Lili Dekens showed that fancy list
ranking algorithms might be worth using, and contributed the initial code.
