`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
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

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
`ifndef SYNTHESIS
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
`endif
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // x0 is always 0.
  assign rs1_data = (rs1 == 5'd0) ? 32'd0 : regs[rs1];
  assign rs2_data = (rs2 == 5'd0) ? 32'd0 : regs[rs2];

  always @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < NumRegs; i++) begin
        regs[i] <= 32'd0;
      end
    end else if (we && (rd != 5'd0)) begin
      regs[rd] <= rd_data;
    end
  end

endmodule

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [6:0] insn_funct7;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rs1;
  logic [2:0] insn_funct3;
  logic [4:0] insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0] insn_imm_u;
  logic [11:0] insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic we;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [6:0] insn_funct7;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rs1;
  logic [2:0] insn_funct3;
  logic [4:0] insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0] insn_imm_u;
  logic [11:0] insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic we;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [6:0] insn_funct7;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rs1;
  logic [2:0] insn_funct3;
  logic [4:0] insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0] insn_imm_u;
  logic [11:0] insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic we;
} stage_memory_t;

/** state at the start of Writeback stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [6:0] insn_funct7;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rs1;
  logic [2:0] insn_funct3;
  logic [4:0] insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [19:0] insn_imm_u;
  logic [11:0] insn_imm_i;
  logic [`REG_SIZE] rd_data;
  logic we;
} stage_writeback_t;

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See the cycle_status.sv file for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  // localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  // localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  // localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  // localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  // localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  // localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_funct7: 0,
        insn_rs2: 0,
        insn_rs1: 0,
        insn_funct3: 0,
        insn_rd: 0,
        insn_opcode: 0,
        insn_imm_u: 0,
        insn_imm_i: 0, 
        rd_data: 0,
        we: 0
      };
    end else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status, 
          insn_funct7: 7'd0,
          insn_rs2: 5'd0,
          insn_rs1: 5'd0,
          insn_funct3: 3'd0,
          insn_rd: 5'd0,
          insn_opcode:  7'd0,
          insn_imm_u: 20'd0,
          insn_imm_i: 12'd0,
          rd_data: 32'd0,
          we: 0
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  logic [19:0] d_insn_imm_u;
  logic [11:0] d_insn_imm_i;
  logic [4:0] d_insn_rd;
  logic [4:0] d_insn_rs1;
  logic [2:0] d_funct3;
  logic [`OPCODE_SIZE] d_insn_opcode;
  logic d_we;
  logic d_illegal_insn;

  always_comb begin
    case (decode_state.insn[`OPCODE_SIZE]) 
      OpcodeLui: begin
        {d_insn_imm_u, d_insn_rd, d_insn_opcode} = decode_state.insn;
        d_we = 1;
      end

      OpcodeRegImm: begin
            {d_insn_imm_i, d_insn_rs1, d_funct3, d_insn_rd, d_insn_opcode} = decode_state.insn;
            d_we = 1;
      end

      default: begin
        d_illegal_insn = 1'b1;
        d_we = 0;
      end
    endcase
  end

  /*****************/
  /* EXECUTE STAGE */
  /*****************/

  stage_execute_t execute_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_funct7: 0,
        insn_rs2: 0,
        insn_rs1: 0,
        insn_funct3: 0,
        insn_rd: 0,
        insn_opcode: 0,
        insn_imm_u: 0,
        insn_imm_i: 0,
        rd_data: 0,
        we: 0
      };
    end else begin
      begin
        execute_state <= '{
          pc: decode_state.pc,
          insn: decode_state.insn,
          cycle_status: decode_state.cycle_status,
          insn_funct7: decode_state.insn_funct7,
          insn_rs2: decode_state.insn_rs2,
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
  end

  wire [255:0] e_disasm;
  Disasm #(
      .PREFIX("E")
  ) disasm_1execute (
      .insn  (execute_state.insn),
      .disasm(e_disasm)
  );

  logic [`REG_SIZE] e_rd_data;
  logic e_illegal_insn;
  logic [`REG_SIZE] e_cla_addi_a;
  logic [`REG_SIZE] e_imm_i_sext;
  logic [4:0] e_imm_shamt;
  

  // instantiate CLA for ADDI
  wire [`REG_SIZE] e_addi_result;
  cla cla_addi (
    .a(e_cla_addi_a),
    .b({{20{execute_state.insn_imm_i[11]}}, execute_state.insn_imm_i[11:0]}),
    .cin(1'b0),
    .sum(e_addi_result)
  );

  // Execute Stage Operations
  always_comb begin

    e_imm_i_sext = {{20{execute_state.insn_imm_i[11]}}, execute_state.insn_imm_i[11:0]};
    e_imm_shamt = execute_state.insn_imm_i[4:0];

    case (execute_state.insn_opcode)
      OpcodeLui: begin
        e_rd_data = execute_state.insn_imm_u << 12;
      end

      OpcodeRegImm: begin
        case (execute_state.insn_funct3)
          3'b000: begin // ADDI
            if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
              e_cla_addi_a = memory_state.rd_data;
            end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
              e_cla_addi_a = writeback_state.rd_data;
            end else begin
              e_cla_addi_a = rs1_data;
            end
            e_rd_data = e_addi_result;
          end

          3'b010: begin // STLI
            if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
              e_rd_data = ($signed(memory_state.rd_data) < $signed(e_imm_i_sext)) ? 32'd1 : 32'd0;
            end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
              e_rd_data = ($signed(writeback_state.rd_data) < $signed(e_imm_i_sext)) ? 32'd1 : 32'd0;
            end else begin
              e_rd_data = ($signed(rs1_data) < $signed(e_imm_i_sext)) ? 32'd1 : 32'd0;
            end
          end

          3'b011: begin // STLIU
            if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
              e_rd_data = (memory_state.rd_data < e_imm_i_sext) ? 32'd1 : 32'd0;
            end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
              e_rd_data = (writeback_state.rd_data < e_imm_i_sext) ? 32'd1 : 32'd0;
            end else begin
              e_rd_data = (rs1_data < e_imm_i_sext) ? 32'd1 : 32'd0;
            end
          end

          3'b100: begin // XORI
            if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
              e_rd_data = memory_state.rd_data ^ e_imm_i_sext;
            end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
              e_rd_data = writeback_state.rd_data ^ e_imm_i_sext;
            end else begin
              e_rd_data = rs1_data ^ e_imm_i_sext;
            end
          end

          3'b110: begin // ORI
            if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
              e_rd_data = memory_state.rd_data | e_imm_i_sext;
            end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
              e_rd_data = writeback_state.rd_data | e_imm_i_sext;
            end else begin
              e_rd_data = rs1_data | e_imm_i_sext;
            end
          end

          3'b111: begin // ANDI
            if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
              e_rd_data = memory_state.rd_data & e_imm_i_sext;
            end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
              e_rd_data = writeback_state.rd_data & e_imm_i_sext;
            end else begin
              e_rd_data = rs1_data & e_imm_i_sext;
            end
          end

          3'b001: begin // SLLI
            if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
              e_rd_data = memory_state.rd_data << e_imm_shamt;
            end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
              e_rd_data = writeback_state.rd_data << e_imm_shamt;
            end else begin
              e_rd_data = rs1_data << e_imm_shamt;
            end
          end

          3'b101: begin // SRLI + SRAI
            if (execute_state.insn[31:25] == 7'd0) begin // SRLI
              if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
                e_rd_data = memory_state.rd_data >> e_imm_shamt;
              end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
                e_rd_data = writeback_state.rd_data >> e_imm_shamt;
              end else begin
                e_rd_data = rs1_data >> e_imm_shamt;
              end
            end else if (execute_state.insn[31:25] == 7'b0100000) begin // SRAI
              if (memory_state.insn_rd == execute_state.insn_rs1) begin // MX
                e_rd_data = $signed(memory_state.rd_data) >>> e_imm_shamt;
              end else if (writeback_state.insn_rd == execute_state.insn_rs1) begin // WX 
                e_rd_data = $signed(writeback_state.rd_data) >>> e_imm_shamt;
              end else begin
                e_rd_data = $signed(rs1_data) >>> e_imm_shamt;
              end
            end else begin
                e_illegal_insn = 1'b1;
            end
          end

          default: begin
            e_illegal_insn = 1'b1;
          end
          
        endcase
      end

      // new Ops go here

      default: begin
        e_illegal_insn = 1'b1;
      end
    endcase
  end

  /****************/
  /* MEMORY STAGE */
  /****************/

  stage_memory_t memory_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_funct7: 0,
        insn_rs2: 0,
        insn_rs1: 0,
        insn_funct3: 0,
        insn_rd: 0,
        insn_opcode: 0,
        insn_imm_u: 0,
        insn_imm_i: 0,
        rd_data: 0,
        we: 0
      };
    end else begin
      begin
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
  end

  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );

  // Memory Stage Operations
  // always_comb begin
  //   case (memory_state.insn_opcode)
  //     
  //   endcase
  // end


  /*******************/
  /* WRITEBACK STAGE */
  /*******************/

  stage_writeback_t writeback_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_funct7: 0,
        insn_rs2: 0,
        insn_rs1: 0,
        insn_funct3: 0,
        insn_rd: 0,
        insn_opcode: 0,
        insn_imm_u: 0,
        insn_imm_i: 0,
        rd_data: 0,
        we: 0
      };
    end else begin
      begin
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
  end

  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_1writeback (
      .insn  (writeback_state.insn),
      .disasm(w_disasm)
  );

  // Writeback Stage Operations

  wire [`REG_SIZE] rs1_data;
  wire [`REG_SIZE] rs2_data;

  RegFile rf (
    .clk(clk),
    .rst(rst),
    .we(writeback_state.we),
    .rd(writeback_state.insn_rd),
    .rd_data(writeback_state.rd_data),
    .rs1(writeback_state.insn_rs1),
    .rs2(writeback_state.insn_rs2),
    .rs1_data(rs1_data),
    .rs2_data(rs2_data)
  );


endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem_array[NUM_WORDS];

`ifdef SYNTHESIS
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end
`endif

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module Processor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
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
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
