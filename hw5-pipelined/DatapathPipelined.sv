`timescale 1ns / 1ns

// Registers and instructions are 32 bits in RV32.
`define REG_SIZE 31:0
`define INSN_SIZE 31:0

// RISC-V opcodes are 7 bits wide.
`define OPCODE_SIZE 6:0

`ifndef DIVIDER_STAGES
  `define DIVIDER_STAGES 8
`endif

`ifndef SYNTHESIS
  `include "../hw3-singlecycle/RvDisassembler.sv"
`endif
`include "../hw2b-cla/cla.sv"
`include "../hw4-multicycle/DividerUnsignedPipelined.sv"
`include "cycle_status.sv"

///////////////////////////////////////////////////////////////////////////////
// Disassembler for simulation tracing.
///////////////////////////////////////////////////////////////////////////////
module Disasm #(
  byte PREFIX = "D"
) (
  input  wire [31:0] insn,
  output wire [(8*32)-1:0] disasm
);
`ifndef SYNTHESIS
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  genvar i;
  for(i = 3; i < 32; i = i+1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
`endif
endmodule

///////////////////////////////////////////////////////////////////////////////
// Register File with WD bypass.
///////////////////////////////////////////////////////////////////////////////
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
  logic [`REG_SIZE] regs_int[NumRegs];

  // Generate a combinational view of registers with write-data (WD) bypassing.
  logic [`REG_SIZE] regs[NumRegs];
  genvar i;
  generate
    for(i = 0; i < NumRegs; i = i+1) begin : reg_bypass
      if(i == 0) begin : assign_zero
        // Register x0 is hardwired to 0.
        assign regs[i] = 32'd0;
      end else begin : assign_val
        // If a write is pending to this register in a later stage, bypass.
        assign regs[i] = (we && (rd == i)) ? rd_data : regs_int[i];
      end
    end
  endgenerate

  // Provide register read outputs.
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  // Write back the data at the positive clock edge.
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int j = 0; j < NumRegs; j = j+1)
        regs_int[j] <= 32'd0;
    end else if (we && (rd != 5'd0)) begin
      regs_int[rd] <= rd_data;
    end
  end
endmodule

///////////////////////////////////////////////////////////////////////////////
// Pipeline Stage Structures.
///////////////////////////////////////////////////////////////////////////////
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e    cycle_status;
  logic [6:0]       insn_funct7;
  logic [4:0]       insn_rs2;
  logic [4:0]       insn_rs1;
  logic [2:0]       insn_funct3;
  logic [4:0]       insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0]      insn_imm_u;
  // For immediate arithmetic (I-type) instructions.
  logic [11:0]      insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic             we;
} stage_decode_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e    cycle_status;
  logic [6:0]       insn_funct7;
  logic [4:0]       insn_rs2;
  logic [4:0]       insn_rs1;
  logic [2:0]       insn_funct3;
  logic [4:0]       insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0]      insn_imm_u;
  logic [11:0]      insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic             we;
} stage_execute_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e    cycle_status;
  logic [6:0]       insn_funct7;
  logic [4:0]       insn_rs2;
  logic [4:0]       insn_rs1;
  logic [2:0]       insn_funct3;
  logic [4:0]       insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0]      insn_imm_u;
  logic [11:0]      insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic             we;
} stage_memory_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e    cycle_status;
  logic [6:0]       insn_funct7;
  logic [4:0]       insn_rs2;
  logic [4:0]       insn_rs1;
  logic [2:0]       insn_funct3;
  logic [4:0]       insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0]      insn_imm_u;
  logic [11:0]      insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic             we;
} stage_writeback_t;

///////////////////////////////////////////////////////////////////////////////
// DatapathPipelined
///////////////////////////////////////////////////////////////////////////////
module DatapathPipelined (
  input  wire clk,
  input  wire rst,
  output logic [`REG_SIZE] pc_to_imem,
  input  wire [`INSN_SIZE] insn_from_imem,
  output logic [`REG_SIZE] addr_to_dmem,
  input  wire [`REG_SIZE] load_data_from_dmem,
  output logic [`REG_SIZE] store_data_to_dmem,
  output logic [3:0]       store_we_to_dmem,
  output logic           halt,
  output logic [`REG_SIZE] trace_writeback_pc,
  output logic [`INSN_SIZE] trace_writeback_insn,
  output cycle_status_e    trace_writeback_cycle_status,
  output wire [(8*32)-1:0] test_case
);
  // Opcode definitions.
  localparam bit [`OPCODE_SIZE] OpcodeLui    = 7'b01_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeAuipc  = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;

  /////////////////////////////////////////////////////////////////////////////
  // Cycle Counter.
  /////////////////////////////////////////////////////////////////////////////
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if(rst)
      cycles_current <= 0;
    else
      cycles_current <= cycles_current + 1;
  end

  /////////////////////////////////////////////////////////////////////////////
  // Branch Flush signals computed in EX.
  /////////////////////////////////////////////////////////////////////////////
  logic flush_ex;
  // Compute branch target using a sign-extended 13-bit immediate.
  // The branch immediate is reassembled in decode as:
  //   {insn[31], insn[7], insn[30:25], insn[11:8], 1'b0}  (13 bits; MSB is bit 12)
  logic [`REG_SIZE] branch_target_reg;
  logic branch_cond;
  // Use the execute stage branch condition to flush.
  assign flush_ex = (execute_state.insn_opcode == OpcodeBranch) && branch_cond;
  // Sign-extend the 13-bit branch immediate.
  assign branch_target_reg = execute_state.pc +
         ({{19{execute_state.insn_imm_i[12]}}, execute_state.insn_imm_i});
  
  // Latch flush signal for branch delay.
  logic flush_pending;
  always_ff @(posedge clk) begin
    if(rst)
      flush_pending <= 1'b0;
    else
      flush_pending <= flush_ex;
  end

  /////////////////////////////////////////////////////////////////////////////
  // FETCH Stage.
  /////////////////////////////////////////////////////////////////////////////
  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e   f_cycle_status;
  always_ff @(posedge clk) begin
    if(rst) begin
      f_pc_current <= 32'd0;
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      if(flush_ex) begin
        f_pc_current <= branch_target_reg;
        f_cycle_status <= CYCLE_TAKEN_BRANCH;
      end else begin
        f_pc_current <= f_pc_current + 4;
        f_cycle_status <= CYCLE_NO_STALL;
      end
    end
  end
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;
  wire [255:0] f_disasm;
  Disasm #(.PREFIX("F"))
    disasm_0fetch (.insn(f_insn), .disasm(f_disasm));

  /////////////////////////////////////////////////////////////////////////////
  // DECODE Stage.
  /////////////////////////////////////////////////////////////////////////////
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if(rst)
      decode_state <= '{
        pc: 0, insn: 0, cycle_status: CYCLE_RESET,
        insn_funct7: 0, insn_rs2: 0, insn_rs1: 0,
        insn_funct3: 0, insn_rd: 0, insn_opcode: 0,
        insn_imm_u: 0, insn_imm_i: 0, rd_data: 32'd0, we: 0
      };
    else begin
      if(flush_pending)
        decode_state <= '{
          pc: f_pc_current, insn: 32'd0, cycle_status: CYCLE_TAKEN_BRANCH,
          insn_funct7: 0, insn_rs2: 0, insn_rs1: 0,
          insn_funct3: 0, insn_rd: 0, insn_opcode: 0,
          insn_imm_u: 0, insn_imm_i: 0, rd_data: 32'd0, we: 0
        };
      else
        decode_state <= '{
          pc: f_pc_current, insn: f_insn, cycle_status: f_cycle_status,
          insn_funct7: 7'd0, insn_rs2: 5'd0, insn_rs1: 5'd0,
          insn_funct3: 3'd0, insn_rd: 5'd0, insn_opcode: 7'd0,
          insn_imm_u: 20'd0, insn_imm_i: 12'd0, rd_data: 32'd0, we: 0
        };
    end
  end
  wire [255:0] d_disasm;
  Disasm #(.PREFIX("D"))
    disasm_1decode (.insn(decode_state.insn), .disasm(d_disasm));

  // Instruction field extraction.
  logic [19:0] d_insn_imm_u;
  // For branch instructions we now extract a 13-bit immediate.
  logic [12:0] d_insn_imm_i;
  logic [4:0]  d_insn_rd, d_insn_rs1, d_insn_rs2;
  logic [2:0]  d_funct3;
  logic [`OPCODE_SIZE] d_insn_opcode;
  logic [6:0]  d_insn_funct7;
  logic         d_we;
  logic         d_illegal_insn;
  always_comb begin
    d_illegal_insn = 1'b0;
    d_we           = 1'b0;
    d_insn_imm_u   = 20'd0;
    d_insn_imm_i   = 13'd0;
    d_insn_rd      = 5'd0;
    d_insn_rs1     = 5'd0;
    d_insn_rs2     = 5'd0;
    d_funct3       = 3'd0;
    d_insn_opcode  = 7'd0;
    d_insn_funct7  = 7'd0;
    case (decode_state.insn[6:0])
      OpcodeLui: begin
        d_insn_imm_u  = decode_state.insn[31:12];
        d_insn_rd     = decode_state.insn[11:7];
        d_insn_opcode = decode_state.insn[6:0];
        d_we          = 1;
      end
      OpcodeAuipc: begin
        d_insn_imm_u  = decode_state.insn[31:12];
        d_insn_rd     = decode_state.insn[11:7];
        d_insn_opcode = decode_state.insn[6:0];
        d_we          = 1;
      end
      OpcodeRegImm: begin
        d_insn_imm_i  = decode_state.insn[31:20]; // 12-bit immediate from I-type
        d_insn_rs1    = decode_state.insn[19:15];
        d_funct3      = decode_state.insn[14:12];
        d_insn_rd     = decode_state.insn[11:7];
        d_insn_opcode = decode_state.insn[6:0];
        d_we          = 1;
      end
      OpcodeRegReg: begin
        d_insn_funct7 = decode_state.insn[31:25];
        d_insn_rs2    = decode_state.insn[24:20];
        d_insn_rs1    = decode_state.insn[19:15];
        d_funct3      = decode_state.insn[14:12];
        d_insn_rd     = decode_state.insn[11:7];
        d_insn_opcode = decode_state.insn[6:0];
        d_we          = 1;
      end
      OpcodeBranch: begin
        // Assemble branch immediate as: {insn[31], insn[7], insn[30:25], insn[11:8], 1'b0} => 13 bits.
        d_insn_imm_i = {decode_state.insn[31],
                        decode_state.insn[7],
                        decode_state.insn[30:25],
                        decode_state.insn[11:8],
                        1'b0};
        d_insn_rs1   = decode_state.insn[19:15];
        d_insn_rs2   = decode_state.insn[24:20];
        d_funct3     = decode_state.insn[14:12];
        d_insn_opcode= decode_state.insn[6:0];
        d_we         = 0;
      end
      default: d_illegal_insn = 1'b1;
    endcase
  end

  /////////////////////////////////////////////////////////////////////////////
  // Register File Instantiation.
  /////////////////////////////////////////////////////////////////////////////
  wire [`REG_SIZE] reg_rs1_data;
  wire [`REG_SIZE] reg_rs2_data;
  RegFile rf (
    .clk(clk),
    .rst(rst),
    .we(writeback_state.we),
    .rd(writeback_state.insn_rd),
    .rd_data(writeback_state.rd_data),
    .rs1(decode_state.insn[19:15]),
    .rs2(decode_state.insn[24:20]),
    .rs1_data(reg_rs1_data),
    .rs2_data(reg_rs2_data)
  );

  /////////////////////////////////////////////////////////////////////////////
  // EXECUTE Stage.
  /////////////////////////////////////////////////////////////////////////////
  stage_execute_t execute_state;
  logic [`REG_SIZE] e_rd_data;
  logic            e_illegal_insn;
  logic [`REG_SIZE] e_cla_addi_a;
  logic [`REG_SIZE] e_imm_i_sext;
  logic [4:0]      e_imm_shamt;
  // For R-type operations.
  logic [`REG_SIZE] alu_op1, alu_op2;
  // For branch comparisons.
  logic [`REG_SIZE] branch_op1, branch_op2;
  wire [`REG_SIZE] e_addi_result;
  // Compute ADDI result using a CLA module.
  cla cla_addi (
    .a(e_cla_addi_a),
    .b({{20{execute_state.insn_imm_i[11]}}, execute_state.insn_imm_i[11:0]}),
    .cin(1'b0),
    .sum(e_addi_result)
  );
  always_comb begin
    e_illegal_insn      = 1'b0;
    e_rd_data           = 32'd0;
    e_imm_i_sext        = {{20{execute_state.insn_imm_i[11]}}, execute_state.insn_imm_i};
    e_imm_shamt         = execute_state.insn_imm_i[4:0]; // For immediate shifts.
    e_cla_addi_a        = 32'd0;
    alu_op1             = 32'd0;
    alu_op2             = 32'd0;
    branch_op1          = 32'd0;
    branch_op2          = 32'd0;
    branch_cond         = 1'b0;
    case(execute_state.insn_opcode)
      OpcodeLui: begin
        e_rd_data = execute_state.insn_imm_u << 12;
      end
      OpcodeAuipc: begin
        e_rd_data = execute_state.pc + (execute_state.insn_imm_u << 12);
      end
      OpcodeRegImm: begin
        case(d_funct3)
          3'b000: begin // ADDI
            if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_cla_addi_a = memory_state.rd_data;
            else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_cla_addi_a = writeback_state.rd_data;
            else
              e_cla_addi_a = reg_rs1_data;
            e_rd_data = e_addi_result;
          end
          3'b010: begin // SLTI (signed)
            if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = ($signed(memory_state.rd_data) < $signed(e_imm_i_sext)) ? 32'd1 : 32'd0;
            else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = ($signed(writeback_state.rd_data) < $signed(e_imm_i_sext)) ? 32'd1 : 32'd0;
            else
              e_rd_data = ($signed(reg_rs1_data) < $signed(e_imm_i_sext)) ? 32'd1 : 32'd0;
          end
          3'b011: begin // SLTIU (unsigned)
            if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = (memory_state.rd_data < e_imm_i_sext) ? 32'd1 : 32'd0;
            else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = (writeback_state.rd_data < e_imm_i_sext) ? 32'd1 : 32'd0;
            else
              e_rd_data = (reg_rs1_data < e_imm_i_sext) ? 32'd1 : 32'd0;
          end
          3'b100: begin // XORI
            if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = memory_state.rd_data ^ e_imm_i_sext;
            else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = writeback_state.rd_data ^ e_imm_i_sext;
            else
              e_rd_data = reg_rs1_data ^ e_imm_i_sext;
          end
          3'b110: begin // ORI
            if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = memory_state.rd_data | e_imm_i_sext;
            else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = writeback_state.rd_data | e_imm_i_sext;
            else
              e_rd_data = reg_rs1_data | e_imm_i_sext;
          end
          3'b111: begin // ANDI
            if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = memory_state.rd_data & e_imm_i_sext;
            else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
              e_rd_data = writeback_state.rd_data & e_imm_i_sext;
            else
              e_rd_data = reg_rs1_data & e_imm_i_sext;
          end
          3'b001: begin // SLLI (Immediate shift left)
            if(execute_state.insn[31:25] == 7'b0000000) begin
              if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
                e_rd_data = memory_state.rd_data << e_imm_shamt;
              else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
                e_rd_data = writeback_state.rd_data << e_imm_shamt;
              else
                e_rd_data = reg_rs1_data << e_imm_shamt;
            end else begin
              e_illegal_insn = 1'b1;
            end
          end
          3'b101: begin // SRLI/SRAI (Immediate shift right)
            if(execute_state.insn[31:25] == 7'b0000000) begin // SRLI
              if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
                e_rd_data = memory_state.rd_data >> e_imm_shamt;
              else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
                e_rd_data = writeback_state.rd_data >> e_imm_shamt;
              else
                e_rd_data = reg_rs1_data >> e_imm_shamt;
            end else if(execute_state.insn[31:25] == 7'b0100000) begin // SRAI
              if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
                e_rd_data = $signed(memory_state.rd_data) >>> e_imm_shamt;
              else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
                e_rd_data = $signed(writeback_state.rd_data) >>> e_imm_shamt;
              else
                e_rd_data = $signed(reg_rs1_data) >>> e_imm_shamt;
            end else begin
              e_illegal_insn = 1'b1;
            end
          end
          default: e_illegal_insn = 1'b1;
        endcase
      end
      OpcodeRegReg: begin
        // For R-type instructions, use bypass logic for operands.
        if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
          alu_op1 = memory_state.rd_data;
        else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
          alu_op1 = writeback_state.rd_data;
        else
          alu_op1 = reg_rs1_data;
        if((memory_state.insn_rd == execute_state.insn_rs2) && (execute_state.insn_rs2 != 0))
          alu_op2 = memory_state.rd_data;
        else if((writeback_state.insn_rd == execute_state.insn_rs2) && (execute_state.insn_rs2 != 0))
          alu_op2 = writeback_state.rd_data;
        else
          alu_op2 = reg_rs2_data;
        // For R-type shift instructions, extract a 5-bit shift amount.
        logic [4:0] rtype_shamt;
        rtype_shamt = alu_op2[4:0];
        case(execute_state.insn_funct3)
          3'b000: begin
            if(execute_state.insn_funct7 == 7'b0100000)
              e_rd_data = alu_op1 - alu_op2; // SUB
            else
              e_rd_data = alu_op1 + alu_op2; // ADD
          end
          3'b001: begin // SLL (Shift Left Logical)
            if(execute_state.insn_funct7 == 7'b0000000)
              e_rd_data = alu_op1 << rtype_shamt;
            else
              e_illegal_insn = 1'b1;
          end
          3'b010: begin // SLT (signed)
            e_rd_data = ($signed(alu_op1) < $signed(alu_op2)) ? 32'd1 : 32'd0;
          end
          3'b011: begin // SLTU (unsigned)
            if(execute_state.insn_funct7 == 7'b0000000)
              e_rd_data = (alu_op1 < alu_op2) ? 32'd1 : 32'd0;
            else
              e_illegal_insn = 1'b1;
          end
          3'b100: e_rd_data = alu_op1 ^ alu_op2; // XOR
          3'b101: begin // SRL/SRA (Shift Right Logical/Arithmetic)
            if(execute_state.insn_funct7 == 7'b0100000)
              e_rd_data = $signed(alu_op1) >>> rtype_shamt; // SRA
            else if(execute_state.insn_funct7 == 7'b0000000)
              e_rd_data = alu_op1 >> rtype_shamt; // SRL
            else
              e_illegal_insn = 1'b1;
          end
          3'b110: e_rd_data = alu_op1 | alu_op2; // OR
          3'b111: e_rd_data = alu_op1 & alu_op2; // AND
          default: e_illegal_insn = 1'b1;
        endcase
      end
      OpcodeBranch: begin
        // For branch instructions, compare registers using bypass logic.
        if((memory_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
          branch_op1 = memory_state.rd_data;
        else if((writeback_state.insn_rd == execute_state.insn_rs1) && (execute_state.insn_rs1 != 0))
          branch_op1 = writeback_state.rd_data;
        else
          branch_op1 = reg_rs1_data;
        if((memory_state.insn_rd == execute_state.insn_rs2) && (execute_state.insn_rs2 != 0))
          branch_op2 = memory_state.rd_data;
        else if((writeback_state.insn_rd == execute_state.insn_rs2) && (execute_state.insn_rs2 != 0))
          branch_op2 = writeback_state.rd_data;
        else
          branch_op2 = reg_rs2_data;
        case(execute_state.insn_funct3)
          3'b000: branch_cond = (branch_op1 == branch_op2); // BEQ
          3'b001: branch_cond = (branch_op1 != branch_op2); // BNE
          3'b100: branch_cond = ($signed(branch_op1) < $signed(branch_op2)); // BLT
          3'b101: branch_cond = ($signed(branch_op1) >= $signed(branch_op2)); // BGE
          3'b110: branch_cond = (branch_op1 < branch_op2);  // BLTU
          3'b111: branch_cond = (branch_op1 >= branch_op2); // BGEU
          default: branch_cond = 1'b0;
        endcase
        e_rd_data = branch_cond ? branch_target_reg : 32'd0;
      end
      default: e_illegal_insn = 1'b1;
    endcase
  end

  // Latch Execute Stage.
  always_ff @(posedge clk) begin
    if(rst)
      execute_state <= '{
        pc: 0, insn: 0, cycle_status: CYCLE_RESET,
        insn_funct7: 0, insn_rs2: 0, insn_rs1: 0,
        insn_funct3: 0, insn_rd: 0, insn_opcode: 0,
        insn_imm_u: 0, insn_imm_i: 0, rd_data: 0, we: 0
      };
    else begin
      execute_state <= '{
        pc: decode_state.pc,
        insn: decode_state.insn,
        cycle_status: ((d_insn_opcode == OpcodeBranch) && branch_cond) ? CYCLE_TAKEN_BRANCH : decode_state.cycle_status,
        insn_funct7: d_insn_funct7,
        insn_rs2: d_insn_rs2,
        insn_rs1: d_insn_rs1,
        insn_funct3: d_funct3,
        insn_rd: d_insn_rd,
        insn_opcode: d_insn_opcode,
        insn_imm_u: d_insn_imm_u,
        insn_imm_i: d_insn_imm_i,
        rd_data: decode_state.rd_data,
        we: d_we
      };
    end
  end
  wire [255:0] e_disasm;
  Disasm #(.PREFIX("E"))
    disasm_1execute (.insn(execute_state.insn), .disasm(e_disasm));

  /////////////////////////////////////////////////////////////////////////////
  // MEMORY Stage.
  /////////////////////////////////////////////////////////////////////////////
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if(rst)
      memory_state <= '{
        pc: 0, insn: 0, cycle_status: CYCLE_RESET,
        insn_funct7: 0, insn_rs2: 0, insn_rs1: 0,
        insn_funct3: 0, insn_rd: 0, insn_opcode: 0,
        insn_imm_u: 0, insn_imm_i: 0, rd_data: 0, we: 0
      };
    else begin
      memory_state <= '{
        pc: execute_state.pc,
        insn: execute_state.insn,
        cycle_status: execute_state.cycle_status,
        insn_funct7: execute_state.insn_funct7,
        insn_rs2: execute_state.insn_rs2,
        insn_rs1: execute_state.insn_rs1,
        insn_funct3: execute_state.insn_funct3,
        insn_rd: execute_state.insn_rd,
        insn_opcode: execute_state.insn_opcode,
        insn_imm_u: execute_state.insn_imm_u,
        insn_imm_i: execute_state.insn_imm_i,
        rd_data: e_rd_data,
        we: execute_state.we
      };
    end
  end
  wire [255:0] m_disasm;
  Disasm #(.PREFIX("M"))
    disasm_1memory (.insn(memory_state.insn), .disasm(m_disasm));

  /////////////////////////////////////////////////////////////////////////////
  // WRITEBACK Stage.
  /////////////////////////////////////////////////////////////////////////////
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if(rst)
      writeback_state <= '{
        pc: 0, insn: 0, cycle_status: CYCLE_RESET,
        insn_funct7: 0, insn_rs2: 0, insn_rs1: 0,
        insn_funct3: 0, insn_rd: 0, insn_opcode: 0,
        insn_imm_u: 0, insn_imm_i: 0, rd_data: 0, we: 0
      };
    else begin
      writeback_state <= '{
        pc: memory_state.pc,
        insn: memory_state.insn,
        cycle_status: memory_state.cycle_status,
        insn_funct7: memory_state.insn_funct7,
        insn_rs2: memory_state.insn_rs2,
        insn_rs1: memory_state.insn_rs1,
        insn_funct3: memory_state.insn_funct3,
        insn_rd: memory_state.insn_rd,
        insn_opcode: memory_state.insn_opcode,
        insn_imm_u: memory_state.insn_imm_u,
        insn_imm_i: memory_state.insn_imm_i,
        rd_data: memory_state.rd_data,
        we: memory_state.we
      };
    end
  end
  wire [255:0] w_disasm;
  Disasm #(.PREFIX("W"))
    disasm_1writeback (.insn(writeback_state.insn), .disasm(w_disasm));

  /////////////////////////////////////////////////////////////////////////////
  // dmem interface (unused in Milestone 1)
  /////////////////////////////////////////////////////////////////////////////
  assign addr_to_dmem      = 32'd0;
  assign store_data_to_dmem  = 32'd0;
  assign store_we_to_dmem    = 4'd0;
  assign halt              = 1'b0;

  /////////////////////////////////////////////////////////////////////////////
  // Trace outputs from Writeback stage.
  /////////////////////////////////////////////////////////////////////////////
  assign trace_writeback_pc         = writeback_state.pc;
  assign trace_writeback_insn       = writeback_state.insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;
endmodule

///////////////////////////////////////////////////////////////////////////////
// MemorySingleCycle
///////////////////////////////////////////////////////////////////////////////
module MemorySingleCycle #(
  parameter int NUM_WORDS = 512
) (
  input  wire rst,
  input  wire clk,
  input  wire [`REG_SIZE] pc_to_imem,
  output logic [`REG_SIZE] insn_from_imem,
  input  wire [`REG_SIZE] addr_to_dmem,
  output logic [`REG_SIZE] load_data_from_dmem,
  input  wire [`REG_SIZE] store_data_to_dmem,
  input  wire [3:0] store_we_to_dmem
);
  logic [`REG_SIZE] mem_array[NUM_WORDS];
`ifdef SYNTHESIS
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end
`endif
  always_comb begin
    assert(pc_to_imem[1:0]==2'b00);
    assert(addr_to_dmem[1:0]==2'b00);
  end
  localparam int AddrMsb = $clog2(NUM_WORDS)+1;
  localparam int AddrLsb = 2;
  always @(negedge clk) begin
    if(!rst)
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end
  always @(negedge clk) begin
    if(!rst) begin
      if(store_we_to_dmem[0])
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0]   <= store_data_to_dmem[7:0];
      if(store_we_to_dmem[1])
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8]  <= store_data_to_dmem[15:8];
      if(store_we_to_dmem[2])
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      if(store_we_to_dmem[3])
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

///////////////////////////////////////////////////////////////////////////////
// Processor
///////////////////////////////////////////////////////////////////////////////
module Processor (
  input  wire clk,
  input  wire rst,
  output logic halt,
  output wire [`REG_SIZE] trace_writeback_pc,
  output wire [`INSN_SIZE] trace_writeback_insn,
  output cycle_status_e trace_writeback_cycle_status,
  output wire [(8*32)-1:0] test_case
);
  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;
  wire [(8*32)-1:0] test_case_internal;
  MemorySingleCycle #(.NUM_WORDS(8192)) memory (
    .rst(rst),
    .clk(clk),
    .pc_to_imem(pc_to_imem),
    .insn_from_imem(insn_from_imem),
    .addr_to_dmem(mem_data_addr),
    .load_data_from_dmem(mem_data_loaded_value),
    .store_data_to_dmem(mem_data_to_write),
    .store_we_to_dmem(mem_data_we)
  );
  DatapathPipelined datapath (
    .clk(clk),
    .rst(rst),
    .pc_to_imem(pc_to_imem),
    .insn_from_imem(insn_from_imem),
    .addr_to_dmem(mem_data_addr),
    .store_data_to_dmem(mem_data_to_write),
    .store_we_to_dmem(mem_data_we),
    .load_data_from_dmem(mem_data_loaded_value),
    .halt(halt),
    .trace_writeback_pc(trace_writeback_pc),
    .trace_writeback_insn(trace_writeback_insn),
    .trace_writeback_cycle_status(trace_writeback_cycle_status),
    .test_case(test_case_internal)
  );
  assign test_case = test_case_internal;
endmodule
