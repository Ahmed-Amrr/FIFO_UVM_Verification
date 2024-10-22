package FIFO_test;
	import uvm_pkg::*;
	import FIFO_config::*;
	import FIFO_main_sequence::*;
	import FIFO_reset_sequence::*;
	import FIFO_env::*;
	
	`include "uvm_macros.svh"

	class FIFO_test extends  uvm_test;

	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		

	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_component_utils(FIFO_test)
		FIFO_config FIFO_cfg;
		FIFO_env env;
		FIFO_main_sequence main_seq;
		FIFO_reset_sequence reset_seq;
	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		// Constructor
		function new(string name = "FIFO_test", uvm_component parent=null);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);

			FIFO_cfg = FIFO_config::type_id::create("FIFO_cfg");
			main_seq = FIFO_main_sequence::type_id::create("main_seq");
			reset_seq = FIFO_reset_sequence::type_id::create("reset_seq");
			env = FIFO_env::type_id::create("env", this);
			
			if (!(uvm_config_db#(virtual FIFO_interface)::get(this, "", "FIFO_interface", FIFO_cfg.FIFO_vif)))
				`uvm_fatal("build_phase", "unable to get vitual interface from top module");

			uvm_config_db#(FIFO_config)::set(this, "*", "CFG", FIFO_cfg);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			phase.raise_objection(this);

			`uvm_info("run phase", "Reset Asserted", UVM_LOW);
			reset_seq.start(env.agt.sqr);
			`uvm_info("run phase", "Reset Asserted", UVM_LOW);

			`uvm_info("run phase", "Stimulus Generation Started", UVM_LOW);
			main_seq.start(env.agt.sqr);
			`uvm_info("run phase", "Stimulus Generation Ended", UVM_LOW);

			phase.drop_objection(this);
		endtask
	endclass
endpackage