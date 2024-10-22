module FIFO_sva (FIFO_interface.DUT FIFO_if);
	underflow_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.rd_en && FIFO_if.empty |=> FIFO_if.underflow));
	underflow_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.rd_en && FIFO_if.empty |=> FIFO_if.underflow));

	overflow_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && FIFO_if.full |=> FIFO_if.overflow));
	overflow_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && FIFO_if.full |=> FIFO_if.overflow));

	wrk_ack_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full |=> FIFO_if.wr_ack));
	wrk_ack_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full |=> FIFO_if.wr_ack));

endmodule