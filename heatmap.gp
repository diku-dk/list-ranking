set term png
set output "heatmap.png"

set title "Speedup of Random Mate over Wyllie"
unset key
set tic scale 0

set ylabel "n"
set xlabel "b"

set palette rgbformula -7,-7,2
set cbrange [0:1]
set cblabel "Speedup"
unset xtics
unset ytics

set view map
splot 'random_mate.speedups' matrix with image
