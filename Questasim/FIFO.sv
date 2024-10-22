////////////////////////////////////////////////////////////////////////////////
// Author: Kareem Waseem
// Course: Digital Verification using SV & UVM
//
// Description: FIFO Design 
// 
////////////////////////////////////////////////////////////////////////////////
module FIFO(FIFO_interface.DUT FIFO_if);
 
localparam max_fifo_addr = $clog2(FIFO_if.FIFO_DEPTH);

reg [FIFO_if.FIFO_WIDTH-1:0] mem [FIFO_if.FIFO_DEPTH-1:0];

reg [max_fifo_addr-1:0] wr_ptr, rd_ptr;
reg [max_fifo_addr:0] count;

always @(posedge FIFO_if.clk or negedge FIFO_if.rst_n) begin
	if (!FIFO_if.rst_n) begin
		wr_ptr <= 0;
		FIFO_if.overflow <= 0;
	end
	else if (FIFO_if.wr_en && count < FIFO_if.FIFO_DEPTH) begin
		mem[wr_ptr] <= FIFO_if.data_in;
		FIFO_if.wr_ack <= 1;
		wr_ptr <= wr_ptr + 1;
	end
	else begin 
		FIFO_if.wr_ack <= 0; 
		if (FIFO_if.full && FIFO_if.wr_en)
			FIFO_if.overflow <= 1;
		else
			FIFO_if.overflow <= 0;
	end
end

always @(posedge FIFO_if.clk or negedge FIFO_if.rst_n) begin
	if (!FIFO_if.rst_n) begin
		rd_ptr <= 0;
		FIFO_if.underflow <= 0;
	end
	else if (FIFO_if.rd_en && count != 0) begin
		FIFO_if.data_out <= mem[rd_ptr];
		rd_ptr <= rd_ptr + 1;
	end
	else begin
		if (FIFO_if.empty && FIFO_if.rd_en)
			FIFO_if.underflow <= 1;
		else
			FIFO_if.underflow <= 0;
	end
end

always @(posedge FIFO_if.clk or negedge FIFO_if.rst_n) begin
	if (!FIFO_if.rst_n) begin
		count <= 0;
	end
	else begin

		if (FIFO_if.wr_en && FIFO_if.rd_en) begin
			if	(FIFO_if.empty) begin
				count <= count + 1;
				mem[wr_ptr] <= FIFO_if.data_in;
			end
			else if (FIFO_if.full) begin
				count <= count - 1;
				FIFO_if.data_out <= mem[rd_ptr];
			end
			else begin
				mem[wr_ptr] <= FIFO_if.data_in;
				FIFO_if.data_out <= mem[rd_ptr];
			end
		end
		else if	(FIFO_if.wr_en && !FIFO_if.full) begin
			count <= count + 1;
			mem[wr_ptr] <= FIFO_if.data_in;
		end
		else if (FIFO_if.rd_en && !FIFO_if.empty) begin
			count <= count - 1;
			FIFO_if.data_out <= mem[rd_ptr];
		end
	end
end

assign FIFO_if.full = (count == FIFO_if.FIFO_DEPTH)? 1 : 0;
assign FIFO_if.empty = (count == 0)? 1 : 0;
assign FIFO_if.almostfull = (count == FIFO_if.FIFO_DEPTH-1)? 1 : 0; 
assign FIFO_if.almostempty = (count == 1)? 1 : 0;

underflow_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.rd_en && FIFO_if.empty |=> FIFO_if.underflow));
underflow_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.rd_en && FIFO_if.empty |=> FIFO_if.underflow));

overflow_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && FIFO_if.full |=> FIFO_if.overflow));
overflow_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && FIFO_if.full |=> FIFO_if.overflow));

wrk_ack_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full |=> FIFO_if.wr_ack));
wrk_ack_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full |=> FIFO_if.wr_ack));

mem_count_up_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full && !FIFO_if.rd_en |=> count == $past(count) + 1));
mem_count_up_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full && !FIFO_if.rd_en |=> count == $past(count) + 1));

mem_count_down_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.rd_en && !FIFO_if.empty && !FIFO_if.wr_en |=> count == $past(count) - 1));
mem_count_down_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.rd_en && !FIFO_if.empty && !FIFO_if.wr_en |=> count == $past(count) - 1));

wr_ptr_zero_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.wr_en) (FIFO_if.wr_en && !FIFO_if.full && wr_ptr == 7 |=> wr_ptr == 0));
wr_ptr_zero_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.wr_en) (FIFO_if.wr_en && !FIFO_if.full && wr_ptr == 7 |=> wr_ptr == 0));

rd_ptr_zero_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.rd_en) (FIFO_if.rd_en && !FIFO_if.empty && rd_ptr == 7 |=> rd_ptr == 0));
rd_ptr_zero_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.rd_en) (FIFO_if.rd_en && !FIFO_if.empty && rd_ptr == 7 |=> rd_ptr == 0));

wr_ptr_over_zero_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.wr_en) (FIFO_if.wr_en && !FIFO_if.full && wr_ptr < 7 |=> wr_ptr == $past(wr_ptr) + 1));
wr_pt_over_zero_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.wr_en) (FIFO_if.wr_en && !FIFO_if.full && wr_ptr < 7 |=> wr_ptr == $past(wr_ptr) + 1));

rd_ptr_over_zero_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.rd_en) (FIFO_if.rd_en && !FIFO_if.empty && rd_ptr < 7 |=> rd_ptr == $past(rd_ptr) + 1));
rd_ptr_over_zero_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n || !FIFO_if.rd_en) (FIFO_if.rd_en && !FIFO_if.empty && rd_ptr < 7 |=> rd_ptr == $past(rd_ptr) + 1));


write_in_mem_a: assert property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full |=> mem[$past(wr_ptr)] == $past(FIFO_if.data_in)));
write_in_mem_c: cover property (@(posedge FIFO_if.clk) disable iff(!FIFO_if.rst_n) (FIFO_if.wr_en && !FIFO_if.full |=> mem[$past(wr_ptr)] == $past(FIFO_if.data_in)));

always_comb begin 
	if(!FIFO_if.rst_n) begin
		a_reset: assert final(wr_ptr == 0 && rd_ptr == 0 && count == 0);
		c_reset: cover final(wr_ptr == 0 && rd_ptr == 0 && count == 0);
	end
	if (count == FIFO_if.FIFO_DEPTH) begin
		full_a: assert final (FIFO_if.full == 1);
		full_c: cover final (FIFO_if.full == 1);
	end
	if (count == FIFO_if.FIFO_DEPTH - 1) begin
		almostfull_a: assert final (FIFO_if.almostfull == 1);
		almostfull_c: cover final (FIFO_if.almostfull == 1);
	end
	if (count == 0) begin
		empty_a: assert final (FIFO_if.empty == 1);
		empty_c: cover final (FIFO_if.empty == 1);
	end
	if (count == 1) begin
		almostempty_a: assert final (FIFO_if.almostempty == 1);
		almostempty_c: cover final (FIFO_if.almostempty == 1);
	end
end
endmodule