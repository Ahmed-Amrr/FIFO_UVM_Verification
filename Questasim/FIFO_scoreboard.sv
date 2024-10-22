package FIFO_scoreboard;
	import uvm_pkg::*;
	import FIFO_sequence_item::*;
	import shared_pkg::*;
	
	`include "uvm_macros.svh"

	logic [FIFO_WIDTH-1:0] data_out_ref;

	logic [FIFO_WIDTH - 1 : 0] mem_ref_queue [FIFO_DEPTH];

	bit [2:0] wr_ptr = 0;
	bit [2:0] rd_ptr = 0;
	integer count = 0;

	class FIFO_scoreboard extends  uvm_scoreboard;
	
	/*-------------------------------------------------------------------------------
	-- Interface, port, fields
	-------------------------------------------------------------------------------*/
		
	
	/*-------------------------------------------------------------------------------
	-- UVM Factory register
	-------------------------------------------------------------------------------*/
		// Provide implementations of virtual methods such as get_type_name and create
		`uvm_component_utils(FIFO_scoreboard)
		uvm_analysis_export#(FIFO_sequence_item) sb_export;
		uvm_tlm_analysis_fifo#(FIFO_sequence_item) sb_fifo;
		FIFO_sequence_item sb_item;

		integer correct_count = 0;
		integer error_count = 0;

	/*-------------------------------------------------------------------------------
	-- Functions
	-------------------------------------------------------------------------------*/
		// Constructor
		function new(string name = "FIFO_scoreboard", uvm_component parent=null);
			super.new(name, parent);
		endfunction
		
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			sb_export = new("sb_export", this);
			sb_fifo = new("sb_fifo", this);			
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			sb_export.connect(sb_fifo.analysis_export);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				sb_fifo.get(sb_item);
				ref_model(sb_item);
				if (sb_item.data_out != data_out_ref) begin
					`uvm_error("run phase", $sformatf("Comparison failed Transaction Received by the DUT: %s, While the reference out: 0x%0h",
						sb_item.convert2string(), data_out_ref))
					error_count ++;
				end
				else begin
					`uvm_info("run_phase", $sformatf("Correct FIFO out: %s", sb_item.convert2string()), UVM_HIGH)
					correct_count++;
				end
			end
		endtask

		task ref_model(FIFO_sequence_item seq_item_chk);
			if (!seq_item_chk.rst_n) begin
				wr_ptr = 0;
				rd_ptr = 0;
				count = 0;
			end
			else begin
				if (seq_item_chk.wr_en && seq_item_chk.rd_en) begin
					if (count == 0) begin
						mem_ref_queue[wr_ptr] = seq_item_chk.data_in;
						wr_ptr++;
						count++;
					end
					else if (count == FIFO_DEPTH) begin
						data_out_ref = mem_ref_queue[rd_ptr];
						rd_ptr++;
						count--;
					end
					else begin
						data_out_ref = mem_ref_queue[rd_ptr];
						rd_ptr++;
						mem_ref_queue[wr_ptr] = seq_item_chk.data_in;
						wr_ptr++;
					end
				end
				else if (seq_item_chk.wr_en && !(count == FIFO_DEPTH)) begin
					mem_ref_queue[wr_ptr] = seq_item_chk.data_in;
						wr_ptr++;
						count++;
				end
				else if (seq_item_chk.rd_en && !(count == 0)) begin
						data_out_ref = mem_ref_queue[rd_ptr];
						rd_ptr++;
						count--;
				end
			end	
		endtask

		function void report_phase(uvm_phase phase);
			super.report_phase(phase);
			`uvm_info("report_phase", $sformatf("Total successful transactions: %0d", correct_count), UVM_MEDIUM)
			`uvm_info("report_phase", $sformatf("Total failed transactions: %0d", error_count), UVM_MEDIUM)
		endfunction
	endclass
endpackage