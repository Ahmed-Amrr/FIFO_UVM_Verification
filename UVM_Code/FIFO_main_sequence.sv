package FIFO_main_sequence;
	import uvm_pkg::*;
	import FIFO_sequence_item::*;
			
	`include "uvm_macros.svh"

	class FIFO_main_sequence extends  uvm_sequence#(FIFO_sequence_item);
	
	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		
	
	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_object_utils(FIFO_main_sequence)
		FIFO_sequence_item seq_item;
	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		// Constructor
		function new(string name = "FIFO_main_sequence");
			super.new(name);
		endfunction
		
		task body();
			//write
			repeat (10) begin
				seq_item=FIFO_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.rst_n=1;
				seq_item.wr_en=1;
				seq_item.rd_en=0;
				seq_item.data_in=$random();
				finish_item(seq_item);
			end

			//read
			repeat (10) begin
				seq_item=FIFO_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.rst_n=1;
				seq_item.wr_en=0;
				seq_item.rd_en=1;
				seq_item.data_in=$random();
				finish_item(seq_item);
			end

			//write_read
			repeat (10) begin
				seq_item=FIFO_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.rst_n=1;
				seq_item.wr_en=1;
				seq_item.rd_en=1;
				seq_item.data_in=$random();
				finish_item(seq_item);
			end

			seq_item=FIFO_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			seq_item.rst_n=0;
			finish_item(seq_item);

			//random
			repeat (10000) begin
				seq_item=FIFO_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize());
				finish_item(seq_item);
			end
		endtask
	endclass
endpackage