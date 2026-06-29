#!/bin/bash
#SBATCH -p gpu
#SBATCH --gres=gpu:a100
#SBATCH --mem=32G
#SBATCH --time=3:00:00
#SBATCH --output=benchmark.log

set -e

module unload cuda
module load cuda/11.8
module load mlkit
make run
# futhark bench --backend=cuda list_ranking.fut

echo "Benchmarking finished."
