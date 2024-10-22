import uvm_pkg::*;
import FIFO_test::*;
`include "uvm_macros.svh"

module FIFO_top ();
	bit clk;

	initial begin
		clk = 0;
		forever
			#1 clk = ~clk;
	end

	FIFO_interface FIFO_if (clk);
	FIFO dut (FIFO_if);

	initial begin
		uvm_config_db#(virtual FIFO_interface)::set(null, "uvm_test_top", "FIFO_interface", FIFO_if);
		run_test("FIFO_test");
	end
endmodule