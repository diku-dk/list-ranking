set term png

unset key
set tic scale 0

set ylabel "n"
set xlabel "b"

set palette defined ( \
    0 "white", \
    1 "blue", \
    3 "red" )
set cbrange [0:3]
set cblabel "Speedup"
unset xtics
unset ytics

set view map

set title "Speedup of Random Mate over Wyllie"
set output "heatmap_random_mate.png"
splot 'random_mate.speedups' matrix with image

set title "Speedup of Cole-Vishkin over Wyllie"
set output "heatmap_cole_vishkin.png"
splot 'cole_vishkin.speedups' matrix with image
