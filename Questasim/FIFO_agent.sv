package FIFO_agent;
	import uvm_pkg::*;
	import FIFO_sequence_item::*;
	import FIFO_sequencer::*;
	import FIFO_config::*;
	import FIFO_driver::*;
	import FIFO_monitor::*;
	
	`include "uvm_macros.svh"

	class FIFO_agent extends  uvm_agent;
	
	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		
	
	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_component_utils(FIFO_agent)
		uvm_analysis_port#(FIFO_sequence_item) agt_ap;
		FIFO_config FIFO_cfg;
		FIFO_monitor mon;
		FIFO_driver drv;
		FIFO_sequencer sqr;
	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		// Constructor
		function new(string name = "FIFO_agent", uvm_component parent=null);
			super.new(name, parent);
		endfunction
		
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);

			if (!(uvm_config_db#(FIFO_config)::get(this, "", "CFG", FIFO_cfg)))
				`uvm_fatal("build phase", "Agent - unable to get configuration object")

			sqr = FIFO_sequencer::type_id::create("sqr", this);
			drv = FIFO_driver::type_id::create("drv", this);
			mon = FIFO_monitor::type_id::create("mon", this);			
			agt_ap = new("agt_ap", this);
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			drv.FIFO_vif = FIFO_cfg.FIFO_vif;
			mon.FIFO_vif = FIFO_cfg.FIFO_vif;
			drv.seq_item_port.connect(sqr.seq_item_export);
			mon.mon_ap.connect(agt_ap);
		endfunction
	endclass
endpackage