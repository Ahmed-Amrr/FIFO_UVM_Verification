vlib work
vlog -f src_file.list +cover -covercells
vsim -voptargs=+acc work.FIFO_top -classdebug  -uvmcontrol=all -cover
add wave /FIFO_top/FIFO_if/*
add wave -position insertpoint  \
sim:/FIFO_scoreboard::data_out_ref
add wave -position insertpoint  \
sim:/FIFO_top/dut/mem
coverage save FIFO_tb.ucdb -onexit
run -all