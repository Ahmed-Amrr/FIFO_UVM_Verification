package FIFO_reset_sequence;
	import uvm_pkg::*;
	import FIFO_sequence_item::*;
			
	`include "uvm_macros.svh"

	class FIFO_reset_sequence extends  uvm_sequence#(FIFO_sequence_item);
	
	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		
	
	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_object_utils(FIFO_reset_sequence)
		FIFO_sequence_item seq_item;
	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		// Constructor
		function new(string name = "FIFO_reset_sequence");
			super.new(name);
		endfunction
		
		task body();
			seq_item = FIFO_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			seq_item.data_in = 16'hFFFF;
			seq_item.rst_n = 0;
			seq_item.wr_en = 1;
			seq_item.rd_en = 1;
			finish_item(seq_item);
		endtask
	endclass
endpackage