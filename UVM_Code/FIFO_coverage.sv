package FIFO_coverage;
	import uvm_pkg::*;
	import FIFO_sequence_item::*;
	
	`include "uvm_macros.svh"

	class FIFO_coverage extends  uvm_component;
	
	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		
	
	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_component_utils(FIFO_coverage)
		FIFO_sequence_item cov_item;
		uvm_analysis_export#(FIFO_sequence_item) cov_export;
		uvm_tlm_analysis_fifo#(FIFO_sequence_item) cov_fifo;
	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		covergroup FIFO_cvg;
		 	wr_full: cross cov_item.wr_en, cov_item.full;
		 	wr_rd_almostfull: cross cov_item.wr_en, cov_item.rd_en, cov_item.almostfull;
		 	wr_rd_empty: cross cov_item.wr_en, cov_item.rd_en, cov_item.empty;
		 	wr_rd_almostempty: cross cov_item.wr_en, cov_item.rd_en, cov_item.almostempty;
		 	wr_rd_overflow: cross cov_item.wr_en, cov_item.rd_en, cov_item.overflow;
		 	wr_rd_underflow: cross cov_item.wr_en, cov_item.rd_en, cov_item.underflow;
		 	wr_rd_wr_ack: cross cov_item.wr_en, cov_item.rd_en, cov_item.wr_ack;
		endgroup

		// Constructor
		function new(string name = "FIFO_coverage", uvm_component parent=null);
			super.new(name, parent);
			FIFO_cvg = new();
		endfunction
	
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			cov_export = new("cov_export", this);
			cov_fifo = new("cov_fifo", this);			
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			cov_export.connect(cov_fifo.analysis_export);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				cov_fifo.get(cov_item);
				FIFO_cvg.sample();
			end
		endtask
	endclass
endpackage