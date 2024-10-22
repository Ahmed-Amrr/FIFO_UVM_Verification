package FIFO_sequence_item;
	import uvm_pkg::*;
	import shared_pkg::*;
	
	`include "uvm_macros.svh"

	class FIFO_sequence_item extends  uvm_sequence_item;
	
	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		
	
	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_object_utils(FIFO_sequence_item)

		rand logic [FIFO_WIDTH-1:0] data_in;
		rand logic rst_n, wr_en, rd_en;

		logic [FIFO_WIDTH-1:0] data_out;
		logic wr_ack, overflow;
		logic full, empty, almostfull, almostempty, underflow;
		
		integer RD_EN_ON_DIST;
		integer WR_EN_ON_DIST;
	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		// Constructor
		function new(string name = "FIFO_sequence_item", integer rd_en_on_dist = 30, wr_en_on_dist = 70);
			super.new(name);
			RD_EN_ON_DIST = rd_en_on_dist;
			WR_EN_ON_DIST = wr_en_on_dist;
		endfunction

		function string convert2string();
			return $sformatf("%s data_in = 0x%0h, rst_n = 0b%0b, wr_en = 0b%0b, rd_en = 0b%0b, data_out = 0x%0h, wr_ack = 0b%0b, overflow = 0b%0b, full = 0b%0b, empty = 0b%0b, almostfull = 0b%0b, almostempty = 0b%0b, underflow = 0b%0b",
				super.convert2string(), data_in, rst_n, wr_en, rd_en, data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow);
		endfunction

		function string convert2string_stimulus();
			return $sformatf("data_in = 0x%0h, rst_n = 0b%0b, wr_en = 0b%0b, rd_en = 0b%0b, data_out = 0x%0h, wr_ack = 0b%0b, overflow = 0b%0b, full = 0b%0b, empty = 0b%0b, almostfull = 0b%0b, almostempty = 0b%0b, underflow = 0b%0b",
				data_in, rst_n, wr_en, rd_en, data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow);
		endfunction

		constraint rst_n_dist {rst_n dist{1:=95, 0:=5};}
		constraint wr_en_dist {wr_en dist{1:=WR_EN_ON_DIST, 0:=100 - WR_EN_ON_DIST};}
		constraint rd_en_dist {rd_en dist{1:=RD_EN_ON_DIST, 0:=100 - RD_EN_ON_DIST};}
	endclass
endpackage