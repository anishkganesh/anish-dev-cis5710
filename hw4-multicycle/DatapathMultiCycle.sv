/* INSERT NAME AND PENNKEY HERE */
`timescale 1ns/1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2b-cla/cla.sv"
`include "DividerUnsignedPipelined.sv"

//----------------------------------------------------------------
// RegFile Module
//----------------------------------------------------------------
module RegFile (
    input  logic [4:0] rd,
    input  logic [`REG_SIZE] rd_data,
    input  logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input  logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,
    input  logic clk,
    input  logic we,
    input  logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // x0 is hardwired to 0.
  assign rs1_data = (rs1 == 5'd0) ? 32'd0 : regs[rs1];
  assign rs2_data = (rs2 == 5'd0) ? 32'd0 : regs[rs2];

  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < NumRegs; i++) begin
        regs[i] <= 32'd0;
      end
    end else if (we && (rd != 5'd0)) begin
      regs[rd] <= rd_data;
    end
  end
endmodule

//----------------------------------------------------------------
// DatapathMultiCycle Module
//
// This module is adapted from your single–cycle datapath and
// includes a two–state FSM. In STATE_NORMAL most instructions execute
// in one cycle; when a division op (DIV, DIVU, REM, or REMU) is detected,
// the datapath latches its destination register and operands and enters STATE_DIV.
// In STATE_DIV a counter (set to 8) counts down while the PC is held. When
// the division result is ready (with sign correction applied if needed),
// that result is stored (in final_reg_wdata) and the PC is updated.
// Note: All combinational logic is separated into “_comb” signals,
// and the sequential (register) outputs are updated only in the always_ff block.
//----------------------------------------------------------------
module DatapathMultiCycle (
    input  wire clk,
    input  wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input  wire [`REG_SIZE] insn_from_imem,
    // Data memory interface signals
    output logic [`REG_SIZE] addr_to_dmem,
    input  wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  // FSM state definitions.
  typedef enum logic {STATE_NORMAL, STATE_DIV} state_t;
  state_t state;

  // Program counter.
  logic [31:0] pc, next_pc;
  assign pc_to_imem = pc;

  //--------------------------------------------------------------------------
  // Instruction field extraction.
  //--------------------------------------------------------------------------
  wire [6:0]  insn_funct7;
  wire [4:0]  insn_rs2, insn_rs1, insn_rd;
  wire [2:0]  insn_funct3;
  wire [`OPCODE_SIZE] insn_opcode;
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // Immediate fields.
  wire [11:0] imm_i = insn_from_imem[31:20];
  wire [4:0]  imm_shamt = insn_from_imem[24:20];
  wire [11:0] imm_s;
  assign {imm_s[11:5], imm_s[4:0]} = {insn_funct7, insn_rd};
  wire [12:0] imm_b;
  assign imm_b = { insn_funct7[6], insn_rd[0], insn_funct7[5:0], insn_rd[4:1], 1'b0 };

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b};

  //--------------------------------------------------------------------------
  // Opcode definitions.
  //--------------------------------------------------------------------------
  localparam bit [`OPCODE_SIZE] OpLoad    = 7'b0000011;
  localparam bit [`OPCODE_SIZE] OpStore   = 7'b0100011;
  localparam bit [`OPCODE_SIZE] OpBranch  = 7'b1100011;
  localparam bit [`OPCODE_SIZE] OpRegImm  = 7'b0010011;
  localparam bit [`OPCODE_SIZE] OpRegReg  = 7'b0110011;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b1110011;
  localparam bit [`OPCODE_SIZE] OpLui     = 7'b0110111;
  localparam bit [`OPCODE_SIZE] OpAuipc   = 7'b0010111;
  localparam bit [`OPCODE_SIZE] OpJal     = 7'b1101111;
  localparam bit [`OPCODE_SIZE] OpJalr    = 7'b1100111;

  //--------------------------------------------------------------------------
  // Combinational signals computed in STATE_NORMAL.
  // These are the “candidate” values that will be written back in normal ops.
  //--------------------------------------------------------------------------
  logic [31:0] alu_result_comb;
  logic        reg_we_comb;
  logic [31:0] addr_to_dmem_comb;
  logic [3:0]  store_we_to_dmem_comb;
  logic [31:0] store_data_to_dmem_comb;
  logic        branch_taken_comb;
  logic        illegal_insn_comb;
  logic        halt_comb;
  logic [31:0] next_pc_comb;

  always_comb begin
    // Default assignments.
    alu_result_comb       = 32'd0;
    reg_we_comb           = 1'b0;
    addr_to_dmem_comb     = 32'd0;
    store_we_to_dmem_comb = 4'b0;
    store_data_to_dmem_comb = 32'd0;
    branch_taken_comb     = 1'b0;
    illegal_insn_comb     = 1'b0;
    halt_comb             = 1'b0;
    next_pc_comb          = pc + 4;  // default: next sequential PC

    if (state == STATE_NORMAL) begin
      case (insn_opcode)
        // LUI: rd = {imm[31:12], 12'b0}
        OpLui: begin
          alu_result_comb = {insn_from_imem[31:12], 12'b0};
          reg_we_comb = 1'b1;
        end

        // AUIPC: rd = PC + (imm20 << 12)
        OpAuipc: begin
          alu_result_comb = pc + {insn_from_imem[31:12], 12'b0};
          reg_we_comb = 1'b1;
        end

        // JAL: rd = PC+4; jump target computed here.
        OpJal: begin
          alu_result_comb = pc + 4;
          reg_we_comb = 1'b1;
          // Compute J-type immediate.
          {
            /* Concatenate:
               imm_j[20] = insn_from_imem[31],
               imm_j[10:1] = insn_from_imem[30:21],
               imm_j[11] = insn_from_imem[20],
               imm_j[19:12] = insn_from_imem[19:12],
               and a trailing 0.
            */
          }
          // For simplicity, we compute next_pc_comb below.
          {
            logic [20:0] imm_j;
            imm_j = { insn_from_imem[31],
                      insn_from_imem[19:12],
                      insn_from_imem[20],
                      insn_from_imem[30:21],
                      1'b0 };
            next_pc_comb = pc + {{11{imm_j[20]}}, imm_j};
          end
        end

        // JALR: rd = PC+4; jump target computed here.
        OpJalr: begin
          alu_result_comb = pc + 4;
          reg_we_comb = 1'b1;
          next_pc_comb = (rf_rs1_data + imm_i_sext) & ~32'b1;
        end

        // RegImm instructions (example: only ADDI).
        OpRegImm: begin
          if (insn_from_imem[14:12] == 3'b000) begin // ADDI
            alu_result_comb = rf_rs1_data + imm_i_sext;
            reg_we_comb = 1'b1;
          end else begin
            illegal_insn_comb = 1'b1;
          end
        end

        // RegReg instructions.
        OpRegReg: begin
          if (insn_funct7 == 7'b0000001) begin
            // For M-extension division/remainder ops we do not compute alu_result.
            if ((insn_funct3 == 3'b100) || (insn_funct3 == 3'b101) ||
                (insn_funct3 == 3'b110) || (insn_funct3 == 3'b111)) begin
              alu_result_comb = 32'd0;
              reg_we_comb = 1'b0;
            end else begin
              // For example, MUL.
              if (insn_funct3 == 3'b000) begin // MUL
                alu_result_comb = $signed(rf_rs1_data) * $signed(rf_rs2_data);
                reg_we_comb = 1'b1;
              end else begin
                illegal_insn_comb = 1'b1;
              end
            end
          end else begin
            // Standard R-type operations.
            if ((insn_from_imem[14:12] == 3'b000) && (insn_funct7 == 7'd0)) begin // ADD
              alu_result_comb = rf_rs1_data + rf_rs2_data;
              reg_we_comb = 1'b1;
            end else if ((insn_from_imem[14:12] == 3'b000) && (insn_funct7 == 7'b0100000)) begin // SUB
              alu_result_comb = rf_rs1_data - rf_rs2_data;
              reg_we_comb = 1'b1;
            end else begin
              illegal_insn_comb = 1'b1;
            end
          end
        end

        // Load instructions.
        OpLoad: begin
          addr_to_dmem_comb = rf_rs1_data + imm_i_sext;
          alu_result_comb = load_data_from_dmem;
          reg_we_comb = 1'b1;
        end

        // Store instructions.
        OpStore: begin
          addr_to_dmem_comb = rf_rs1_data + imm_s_sext;
          store_we_to_dmem_comb = 4'b1111;  // assume word store
          store_data_to_dmem_comb = rf_rs2_data;
        end

        // Branch instructions (example: BEQ).
        OpBranch: begin
          branch_taken_comb = (rf_rs1_data == rf_rs2_data);
          next_pc_comb = branch_taken_comb ? (pc + imm_b_sext) : (pc + 4);
        end

        // System instructions.
        OpEnviron: begin
          if (insn_from_imem[31:7] == 25'd0)
            halt_comb = 1'b1;
          else
            illegal_insn_comb = 1'b1;
        end

        default: illegal_insn_comb = 1'b1;
      endcase
    end
  end

  //--------------------------------------------------------------------------
  // Instantiate the Register File.
  // We now drive its rd_data input from final_reg_wdata (updated sequentially).
  //--------------------------------------------------------------------------
  reg [31:0] final_reg_wdata;
  reg        final_halt;
  RegFile rf (
      .rd(insn_rd),
      .rd_data(final_reg_wdata),
      .rs1(insn_rs1),
      .rs1_data(rf_rs1_data),
      .rs2(insn_rs2),
      .rs2_data(rf_rs2_data),
      .clk(clk),
      .we(reg_we_comb),
      .rst(rst)
  );

  //--------------------------------------------------------------------------
  // Division Operation Registers.
  // These are latched when a division instruction is detected.
  //--------------------------------------------------------------------------
  reg [4:0]  div_rd_reg;
  reg        div_signed_reg; // 1 for signed (DIV, REM); 0 for unsigned (DIVU, REMU)
  reg        div_rem_reg;    // 1 for remainder ops (REM, REMU)
  reg [31:0] div_op_rs1_reg, div_op_rs2_reg;
  reg [3:0]  div_counter;    // Counts down 8 cycles for division

  //--------------------------------------------------------------------------
  // Instantiate the Pipelined Divider.
  // For signed operations, feed the absolute values.
  //--------------------------------------------------------------------------
  wire [31:0] div_in_dividend, div_in_divisor;
  assign div_in_dividend = (div_signed_reg && div_op_rs1_reg[31]) ? (~div_op_rs1_reg + 1) : div_op_rs1_reg;
  assign div_in_divisor  = (div_signed_reg && div_op_rs2_reg[31]) ? (~div_op_rs2_reg + 1) : div_op_rs2_reg;

  wire [31:0] div_pipe_quotient, div_pipe_remainder;
  DividerUnsignedPipelined divider_inst (
      .clk(clk),
      .rst(rst),
      .stall(1'b0),
      .i_dividend(div_in_dividend),
      .i_divisor(div_in_divisor),
      .o_remainder(div_pipe_remainder),
      .o_quotient(div_pipe_quotient)
  );

  //--------------------------------------------------------------------------
  // Sequential FSM: Update PC, state, and final result signals.
  // All assignments here use nonblocking assignments.
  //--------------------------------------------------------------------------
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      pc              <= 32'd0;
      state           <= STATE_NORMAL;
      final_reg_wdata <= 32'd0;
      final_halt      <= 1'b0;
      div_counter     <= 0;
    end else begin
      case (state)
        STATE_NORMAL: begin
          // Check for a division op (M-extension: funct7==0000001 and funct3 one of 100,101,110,111)
          if ((insn_opcode == OpRegReg) && (insn_funct7 == 7'b0000001) &&
              ((insn_funct3 == 3'b100) || (insn_funct3 == 3'b101) ||
               (insn_funct3 == 3'b110) || (insn_funct3 == 3'b111))) begin
            state           <= STATE_DIV;
            div_counter     <= 8;  // Stall for 8 cycles.
            div_rd_reg      <= insn_rd;
            // For signed division (DIV and REM): funct3 100 and 110.
            div_signed_reg  <= (insn_funct3 == 3'b100) || (insn_funct3 == 3'b110);
            // For remainder ops (REM, REMU): funct3 110 and 111.
            div_rem_reg     <= (insn_funct3 == 3'b110) || (insn_funct3 == 3'b111);
            // Latch operands.
            div_op_rs1_reg  <= rf_rs1_data;
            div_op_rs2_reg  <= rf_rs2_data;
            // Hold PC.
            pc <= pc;
            // Do not update final_reg_wdata in this cycle.
          end else begin
            // Normal operation: update PC and write back ALU result.
            pc <= next_pc_comb;
            final_reg_wdata <= alu_result_comb;
          end
          // Update halt flag.
          final_halt <= halt_comb;
        end

        STATE_DIV: begin
          if (div_counter > 0) begin
            div_counter <= div_counter - 1;
            pc <= pc; // Hold PC.
          end else begin
            // Division is complete. Capture the result.
            reg [31:0] div_result;
            if (div_rem_reg)
              div_result = div_pipe_remainder;
            else
              div_result = div_pipe_quotient;
            // Apply sign correction if needed.
            if (div_signed_reg) begin
              if (!div_rem_reg) begin
                // For quotient: if dividend and divisor have opposite signs, negate.
                if (div_op_rs1_reg[31] ^ div_op_rs2_reg[31])
                  div_result = ~div_result + 1;
              end else begin
                // For remainder: if dividend was negative, negate.
                if (div_op_rs1_reg[31])
                  div_result = ~div_result + 1;
              end
            end
            final_reg_wdata <= div_result;
            pc <= pc + 4;
            state <= STATE_NORMAL;
          end
          final_halt <= 1'b0;
        end
      endcase
    end
  end

  // Drive memory interface outputs from the combinational signals.
  assign addr_to_dmem     = addr_to_dmem_comb;
  assign store_we_to_dmem = store_we_to_dmem_comb;
  assign store_data_to_dmem = store_data_to_dmem_comb;
  // Drive reg_we for the register file from the combinational signal.
  // (The register file uses final_reg_wdata which is updated sequentially.)
  // The halt output is driven from final_halt.
  assign halt = final_halt;

endmodule

//----------------------------------------------------------------
// MemorySingleCycle Module
//
// A memory model that provides instruction and data memory.
//----------------------------------------------------------------
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    input wire rst,
    input wire clock_mem,
    input wire [`REG_SIZE] pc_to_imem,
    output logic [`REG_SIZE] insn_from_imem,
    input wire [`REG_SIZE] addr_to_dmem,
    output logic [`REG_SIZE] load_data_from_dmem,
    input wire [`REG_SIZE] store_data_to_dmem,
    input wire [3:0] store_we_to_dmem
);
  logic [`REG_SIZE] mem_array[NUM_WORDS];

`ifdef SYNTHESIS
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end
`endif

  always_comb begin
    assert(pc_to_imem[1:0] == 2'b00);
    assert(addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // Instruction memory read.
  always @(posedge clock_mem) begin
    if (!rst)
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end

  // Data memory write (on negedge) with read-first behavior.
  always @(negedge clock_mem) begin
    if (!rst) begin
      if (store_we_to_dmem[0])
        mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}][7:0] <= store_data_to_dmem[7:0];
      if (store_we_to_dmem[1])
        mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}][15:8] <= store_data_to_dmem[15:8];
      if (store_we_to_dmem[2])
        mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}][23:16] <= store_data_to_dmem[23:16];
      if (store_we_to_dmem[3])
        mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}][31:24] <= store_data_to_dmem[31:24];
      load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

//----------------------------------------------------------------
// Processor Top-Level Module
//
// This module instantiates memory and the multi–cycle datapath,
// providing the top-level module "Processor" expected by the testbench.
//----------------------------------------------------------------
module Processor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem;
  wire [`REG_SIZE] mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
      .rst(rst),
      .clock_mem(clock_mem),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we)
  );

  DatapathMultiCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );
endmodule
