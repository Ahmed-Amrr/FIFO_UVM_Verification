package FIFO_config;
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	class FIFO_config extends  uvm_object;
	
	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		
	
	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_object_utils(FIFO_config)
		virtual FIFO_interface FIFO_vif;
	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		// Constructor
		function new(string name = "FIFO_config");
			super.new(name);
		endfunction
	
	endclass
endpackage