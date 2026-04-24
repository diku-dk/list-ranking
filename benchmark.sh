#!/bin/bash
#SBATCH -p gpu
#SBATCH --gres=gpu:a100
#SBATCH --mem=16G
#SBATCH --exclude=hendrixgpu05fl
#SBATCH --time=0:30:00

module unload cuda
module load cuda/11.8
futhark bench --backend=cuda list-ranking.fut
