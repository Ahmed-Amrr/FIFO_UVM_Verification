package FIFO_sequencer;
	import uvm_pkg::*;
	import FIFO_sequence_item::*;
			
	`include "uvm_macros.svh"

class FIFO_sequencer extends  uvm_sequencer#(FIFO_sequence_item);

/*-------------------------------------------------------------------------------
-- Interface, port, fields
-------------------------------------------------------------------------------*/
	

/*-------------------------------------------------------------------------------
-- UVM Factory register
-------------------------------------------------------------------------------*/
	// Provide implementations of virtual methods such as get_type_name and create
	`uvm_component_utils(FIFO_sequencer)

/*-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------*/
	// Constructor
	function new(string name = "FIFO_sequencer", uvm_component parent=null);
		super.new(name, parent);
	endfunction

endclass
endpackage