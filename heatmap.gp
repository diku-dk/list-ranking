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

set cbrange [0:10]

set title "Scalability of Wyllie"
set output "scalability_wyllie.png"
splot 'wyllie.scaling' matrix with image

set title "Scalability of Random Mate"
set output "scalability_random_mate.png"
splot 'random_mate.scaling' matrix with image

set title "Scalability of Cole-Vishkin"
set output "scalability_cole_vishkin.png"
splot 'cole_vishkin.scaling' matrix with image
