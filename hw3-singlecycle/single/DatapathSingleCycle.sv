`timescale 1ns / 1ns

//----------------------------------------------------------------
// Global definitions
//----------------------------------------------------------------
`define REG_SIZE 31:0
`define OPCODE_SIZE 6:0

//----------------------------------------------------------------
// Simple Carry Lookahead Adder (CLA)
// (Behavioral implementation.)
//----------------------------------------------------------------
module cla(
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic        cin,
    output logic [31:0] sum
);
  always_comb begin
    // Add with the 1-bit cin extended to 32 bits.
    sum = a + b + {31'd0, cin};
  end
endmodule

//----------------------------------------------------------------
// Unsigned Divider Module (Rewritten without / or % operators)
// Returns 0xFFFFFFFF for quotient if divisor is zero.
//----------------------------------------------------------------
module divider_unsigned(
    input  logic [31:0] i_dividend,
    input  logic [31:0] i_divisor,
    output logic [31:0] o_quotient,
    output logic [31:0] o_remainder
);
  // Declare quotient and remainder as internal signals so that they are always assigned.
  logic [31:0] quotient;
  logic [31:0] remainder;
  integer i;
  always_comb begin
    // Initialize all values so that every branch assigns a value.
    quotient  = 32'd0;
    remainder = 32'd0;
    
    if (i_divisor == 32'd0) begin
      quotient  = 32'hffffffff;
      remainder = i_dividend;
    end else begin
      // Process dividend from MSB to LSB.
      for (i = 0; i < 32; i = i + 1) begin
        // Shift left remainder and bring in the next MSB from dividend.
        remainder = {remainder[30:0], i_dividend[31-i]};
        // If remainder >= divisor, subtract divisor (using two's complement addition).
        if (remainder >= i_divisor) begin
          remainder = remainder + (~i_divisor + 1);
          quotient[31-i] = 1'b1;
        end else begin
          quotient[31-i] = 1'b0;
        end
      end
    end
    o_quotient  = quotient;
    o_remainder = remainder;
  end
endmodule

//----------------------------------------------------------------
// Register File
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

//----------------------------------------------------------------
// DatapathSingleCycle
//----------------------------------------------------------------
module DatapathSingleCycle (
    input  wire clk,
    input  wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input  wire [`REG_SIZE] insn_from_imem,
    // Data memory ports
    output logic [`REG_SIZE] addr_to_dmem,
    input  wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,
    // Debug counters
    output logic [`REG_SIZE] cycles_current,
    output logic [`REG_SIZE] num_insns_current
);

  //--------------------------------------------------------------------------
  // Extract instruction fields.
  //--------------------------------------------------------------------------
  wire [6:0]  insn_funct7;
  wire [4:0]  insn_rs2;
  wire [4:0]  insn_rs1;
  wire [2:0]  insn_funct3;
  wire [4:0]  insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // Immediate extraction:
  // I-type
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [4:0]  imm_shamt = insn_from_imem[24:20];

  // S-type
  wire [11:0] imm_s;
  assign {imm_s[11:5], imm_s[4:0]} = {insn_funct7, insn_rd};

  // B-type
  wire [12:0] imm_b;
  assign imm_b = { insn_funct7[6], insn_rd[0], insn_funct7[5:0], insn_rd[4:1], 1'b0 };

  // Sign-extensions.
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
  // Instruction signal definitions.
  // U-type:
  wire insn_lui = (insn_opcode == OpLui);
  // RegImm:
  wire insn_addi  = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b000);
  wire insn_slti  = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b010);
  wire insn_sltiu = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b011);
  wire insn_xori  = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b100);
  wire insn_ori   = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b110);
  wire insn_andi  = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b111);
  wire insn_slli  = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b001) && (insn_from_imem[31:25] == 7'd0);
  wire insn_srli  = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101) && (insn_from_imem[31:25] == 7'd0);
  wire insn_srai  = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101) && (insn_from_imem[31:25] == 7'b0100000);
  // RegReg:
  wire insn_add   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000) && (insn_from_imem[31:25] == 7'd0);
  wire insn_sub   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000) && (insn_from_imem[31:25] == 7'b0100000);
  wire insn_sll   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b001) && (insn_from_imem[31:25] == 7'd0);
  wire insn_slt   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b010) && (insn_from_imem[31:25] == 7'd0);
  wire insn_sltu  = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b011) && (insn_from_imem[31:25] == 7'd0);
  wire insn_xor   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b100) && (insn_from_imem[31:25] == 7'd0);
  wire insn_srl   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101) && (insn_from_imem[31:25] == 7'd0);
  wire insn_sra   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101) && (insn_from_imem[31:25] == 7'b0100000);
  wire insn_or    = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b110) && (insn_from_imem[31:25] == 7'd0);
  wire insn_and   = (insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b111) && (insn_from_imem[31:25] == 7'd0);
  // Loads and stores:
  wire insn_lw = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b010);
  wire insn_sw = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b010);
  // Branches:
  wire insn_beq  = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b000);
  wire insn_bne  = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b001);
  wire insn_blt  = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b100);
  wire insn_bge  = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b101);
  wire insn_bltu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b110);
  wire insn_bgeu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b111);
  // System:
  wire insn_ecall = (insn_opcode == OpEnviron) && (insn_from_imem[31:7] == 25'd0);
  // Extended memory (byte/halfword) loads/stores:
  wire insn_lb   = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b000);
  wire insn_lh   = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b001);
  wire insn_lbu  = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b100);
  wire insn_lhu  = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b101);
  wire insn_sb   = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b000);
  wire insn_sh   = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b001);

  //--------------------------------------------------------------------------
  // Instantiate Register File.
  //--------------------------------------------------------------------------
  wire [`REG_SIZE] rf_rs1_data, rf_rs2_data;
  logic reg_we;
  logic [`REG_SIZE] reg_wdata;
  RegFile rf (
    .rd(insn_rd),
    .rd_data(reg_wdata),
    .rs1(insn_rs1),
    .rs1_data(rf_rs1_data),
    .rs2(insn_rs2),
    .rs2_data(rf_rs2_data),
    .clk(clk),
    .we(reg_we),
    .rst(rst)
  );

  //--------------------------------------------------------------------------
  // Data memory interface signals.
  //--------------------------------------------------------------------------
  logic [`REG_SIZE] mem_addr;
  logic [3:0] mem_we;
  logic [`REG_SIZE] mem_wdata;
  assign addr_to_dmem      = mem_addr;
  assign store_data_to_dmem  = mem_wdata;
  assign store_we_to_dmem    = mem_we;

  //--------------------------------------------------------------------------
  // Instantiate the CLA for subtraction.
  //--------------------------------------------------------------------------
  wire [`REG_SIZE] sub_result;
  cla cla_sub_inst (
    .a(rf_rs1_data),
    .b(~rf_rs2_data),
    .cin(1'b1),
    .sum(sub_result)
  );

  //--------------------------------------------------------------------------
  // Instantiate Dividers for M-extension.
  //--------------------------------------------------------------------------
  logic [31:0] div_u_dividend, div_u_divisor;
  wire [31:0]  div_u_quotient, div_u_remainder;
  divider_unsigned div_u_inst (
    .i_dividend(div_u_dividend),
    .i_divisor(div_u_divisor),
    .o_quotient(div_u_quotient),
    .o_remainder(div_u_remainder)
  );

  logic [31:0] div_s_dividend, div_s_divisor;
  wire [31:0]  div_s_quotient, div_s_remainder;
  divider_unsigned div_s_inst (
    .i_dividend(div_s_dividend),
    .i_divisor(div_s_divisor),
    .o_quotient(div_s_quotient),
    .o_remainder(div_s_remainder)
  );

  // For signed division, take the absolute values.
  assign div_u_dividend = rf_rs1_data;
  assign div_u_divisor  = rf_rs2_data;
  assign div_s_dividend = (rf_rs1_data[31]) ? (~rf_rs1_data + 1) : rf_rs1_data;
  assign div_s_divisor  = (rf_rs2_data[31]) ? (~rf_rs2_data + 1) : rf_rs2_data;

  //--------------------------------------------------------------------------
  // ALU, Branch, and Control Logic.
  //--------------------------------------------------------------------------
  logic [`REG_SIZE] alu_result;
  logic branch_taken;
  logic illegal_insn;

  // We assume pcCurrent is declared in the PC update section.
  logic [`REG_SIZE] pcNext, pcCurrent;

  always_comb begin
    // Temporary variables for multiplication.
    logic signed [63:0] mult_temp_signed;
    logic [63:0]        mult_temp_unsigned;

    // Default assignments.
    alu_result   = 32'd0;
    reg_we       = 1'b0;
    mem_addr     = 32'd0;
    mem_we       = 4'b0;
    mem_wdata    = 32'd0;
    branch_taken = 1'b0;
    halt         = 1'b0;
    illegal_insn = 1'b0;

    case (insn_opcode)
      // LUI: rd = {imm[31:12], 12'b0}
      OpLui: begin
        alu_result = {insn_from_imem[31:12], 12'b0};
        reg_we = 1'b1;
      end

      // AUIPC: rd = PC + (imm20 << 12)
      OpAuipc: begin
        alu_result = pcCurrent + {insn_from_imem[31:12], 12'b0};
        reg_we = 1'b1;
      end

      // JAL: rd = PC+4; PC updated later.
      OpJal: begin
        logic [20:0] imm_j;
        logic [31:0] imm_j_sext;
        imm_j = { insn_from_imem[31],
                  insn_from_imem[19:12],
                  insn_from_imem[20],
                  insn_from_imem[30:21],
                  1'b0 };
        imm_j_sext = {{11{imm_j[20]}}, imm_j};
        alu_result = pcCurrent + 4;  // rd gets PC+4
        reg_we = 1'b1;
      end

      // JALR: rd = PC+4; PC update handled below.
      OpJalr: begin
        alu_result = pcCurrent + 4;
        reg_we = 1'b1;
      end

      // RegImm instructions.
      OpRegImm: begin
        if (insn_addi) begin
          alu_result = rf_rs1_data + imm_i_sext;
          reg_we = 1'b1;
        end else if (insn_slti) begin
          alu_result = ($signed(rf_rs1_data) < $signed(imm_i_sext)) ? 32'd1 : 32'd0;
          reg_we = 1'b1;
        end else if (insn_sltiu) begin
          alu_result = (rf_rs1_data < imm_i_sext) ? 32'd1 : 32'd0;
          reg_we = 1'b1;
        end else if (insn_xori) begin
          alu_result = rf_rs1_data ^ imm_i_sext;
          reg_we = 1'b1;
        end else if (insn_ori) begin
          alu_result = rf_rs1_data | imm_i_sext;
          reg_we = 1'b1;
        end else if (insn_andi) begin
          alu_result = rf_rs1_data & imm_i_sext;
          reg_we = 1'b1;
        end else if (insn_slli) begin
          alu_result = rf_rs1_data << imm_shamt;
          reg_we = 1'b1;
        end else if (insn_srli) begin
          alu_result = rf_rs1_data >> imm_shamt;
          reg_we = 1'b1;
        end else if (insn_srai) begin
          alu_result = $signed(rf_rs1_data) >>> imm_shamt;
          reg_we = 1'b1;
        end else begin
          illegal_insn = 1'b1;
        end
      end

      // RegReg instructions (including M-extension).
      OpRegReg: begin
        if (insn_from_imem[31:25] == 7'b0000001) begin
          case (insn_funct3)
            3'b000: begin // MUL
              mult_temp_signed = $signed(rf_rs1_data) * $signed(rf_rs2_data);
              alu_result = mult_temp_signed[31:0];
              reg_we = 1'b1;
            end
            3'b001: begin // MULH
              mult_temp_signed = $signed(rf_rs1_data) * $signed(rf_rs2_data);
              alu_result = mult_temp_signed[63:32];
              reg_we = 1'b1;
            end
            3'b010: begin // MULHSU – fixed: extend operands to 64 bits properly
              logic signed [63:0] prod;
              prod = $signed({{32{rf_rs1_data[31]}}, rf_rs1_data}) * $unsigned({32'd0, rf_rs2_data});
              alu_result = prod[63:32];
              reg_we = 1'b1;
            end
            3'b011: begin // MULHU
              mult_temp_unsigned = rf_rs1_data * rf_rs2_data;
              alu_result = mult_temp_unsigned[63:32];
              reg_we = 1'b1;
            end
            3'b100: begin // DIV (signed)
              if (rf_rs2_data == 32'd0)
                alu_result = 32'hffffffff;
              else
                alu_result = (rf_rs1_data[31] ^ rf_rs2_data[31]) ? (~div_s_quotient + 1) : div_s_quotient;
              reg_we = 1'b1;
            end
            3'b101: begin // DIVU (unsigned)
              if (rf_rs2_data == 32'd0)
                alu_result = 32'hffffffff;
              else
                alu_result = div_u_quotient;
              reg_we = 1'b1;
            end
            3'b110: begin // REM (signed)
              if (rf_rs2_data == 32'd0)
                alu_result = rf_rs1_data;
              else
                alu_result = (rf_rs1_data[31]) ? (~div_s_remainder + 1) : div_s_remainder;
              reg_we = 1'b1;
            end
            3'b111: begin // REMU (unsigned)
              if (rf_rs2_data == 32'd0)
                alu_result = rf_rs1_data;
              else
                alu_result = div_u_remainder;
              reg_we = 1'b1;
            end
            default: illegal_insn = 1'b1;
          endcase
        end else begin
          if (insn_add) begin
            alu_result = rf_rs1_data + rf_rs2_data;
            reg_we = 1'b1;
          end else if (insn_sub) begin
            alu_result = sub_result;
            reg_we = 1'b1;
          end else if (insn_sll) begin
            alu_result = rf_rs1_data << rf_rs2_data[4:0];
            reg_we = 1'b1;
          end else if (insn_slt) begin
            alu_result = ($signed(rf_rs1_data) < $signed(rf_rs2_data)) ? 32'd1 : 32'd0;
            reg_we = 1'b1;
          end else if (insn_sltu) begin
            alu_result = (rf_rs1_data < rf_rs2_data) ? 32'd1 : 32'd0;
            reg_we = 1'b1;
          end else if (insn_xor) begin
            alu_result = rf_rs1_data ^ rf_rs2_data;
            reg_we = 1'b1;
          end else if (insn_srl) begin
            alu_result = rf_rs1_data >> rf_rs2_data[4:0];
            reg_we = 1'b1;
          end else if (insn_sra) begin
            alu_result = $signed(rf_rs1_data) >>> rf_rs2_data[4:0];
            reg_we = 1'b1;
          end else if (insn_or) begin
            alu_result = rf_rs1_data | rf_rs2_data;
            reg_we = 1'b1;
          end else if (insn_and) begin
            alu_result = rf_rs1_data & rf_rs2_data;
            reg_we = 1'b1;
          end else begin
            illegal_insn = 1'b1;
          end
        end
      end

      // Load instructions.
      OpLoad: begin
        mem_addr = rf_rs1_data + imm_i_sext;
        if (insn_lb || insn_lbu) begin
          logic [7:0] byte_data;
          case (mem_addr[1:0])
            2'b00: byte_data = load_data_from_dmem[7:0];
            2'b01: byte_data = load_data_from_dmem[15:8];
            2'b10: byte_data = load_data_from_dmem[23:16];
            default: byte_data = load_data_from_dmem[31:24];
          endcase
          alu_result = (insn_lb) ? {{24{byte_data[7]}}, byte_data} : {24'd0, byte_data};
          reg_we = 1'b1;
        end else if (insn_lh || insn_lhu) begin
          logic [15:0] half_data;
          half_data = (mem_addr[1] == 1'b0) ? load_data_from_dmem[15:0] : load_data_from_dmem[31:16];
          alu_result = (insn_lh) ? {{16{half_data[15]}}, half_data} : {16'd0, half_data};
          reg_we = 1'b1;
        end else if (insn_lw) begin
          alu_result = load_data_from_dmem;
          reg_we = 1'b1;
        end else begin
          illegal_insn = 1'b1;
        end
      end

      // Store instructions.
      OpStore: begin
        mem_addr = rf_rs1_data + imm_s_sext;
        if (insn_sb) begin
          case (mem_addr[1:0])
            2'b00: begin mem_we = 4'b0001; mem_wdata = {24'd0, rf_rs2_data[7:0]}; end
            2'b01: begin mem_we = 4'b0010; mem_wdata = {16'd0, rf_rs2_data[7:0], 8'd0}; end
            2'b10: begin mem_we = 4'b0100; mem_wdata = {8'd0, rf_rs2_data[7:0], 16'd0}; end
            default: begin mem_we = 4'b1000; mem_wdata = {rf_rs2_data[7:0], 24'd0}; end
          endcase
        end else if (insn_sh) begin
          if (mem_addr[1] == 1'b0) begin
            mem_we = 4'b0011;
            mem_wdata = {16'd0, rf_rs2_data[15:0]};
          end else begin
            mem_we = 4'b1100;
            mem_wdata = {rf_rs2_data[15:0], 16'd0};
          end
        end else if (insn_sw) begin
          mem_we = 4'b1111;
          mem_wdata = rf_rs2_data;
        end else begin
          illegal_insn = 1'b1;
        end
      end

      // Branch instructions. (PC update handled separately.)
      OpBranch: begin
        case (insn_funct3)
          3'b000: branch_taken = (rf_rs1_data == rf_rs2_data); // BEQ
          3'b001: branch_taken = (rf_rs1_data != rf_rs2_data); // BNE
          3'b100: branch_taken = ($signed(rf_rs1_data) < $signed(rf_rs2_data)); // BLT
          3'b101: branch_taken = ($signed(rf_rs1_data) >= $signed(rf_rs2_data)); // BGE
          3'b110: branch_taken = (rf_rs1_data < rf_rs2_data); // BLTU
          3'b111: branch_taken = (rf_rs1_data >= rf_rs2_data); // BGEU
          default: branch_taken = 1'b0;
        endcase
      end

      // System instruction: ECALL.
      OpEnviron: begin
        if (insn_ecall)
          halt = 1'b1;
        else
          illegal_insn = 1'b1;
      end

      default: illegal_insn = 1'b1;
    endcase

    // Drive register write data with ALU result.
    reg_wdata = alu_result;
  end

  //--------------------------------------------------------------------------
  // Program Counter (PC) Update Logic.
  //--------------------------------------------------------------------------
  always_ff @(posedge clk) begin
    if (rst)
      pcCurrent <= 32'd0;
    else
      pcCurrent <= pcNext;
  end
  assign pc_to_imem = pcCurrent;

  always_comb begin
    case (insn_opcode)
      OpJal: begin
        logic [20:0] imm_j;
        logic [31:0] imm_j_sext;
        imm_j = { insn_from_imem[31],
                  insn_from_imem[19:12],
                  insn_from_imem[20],
                  insn_from_imem[30:21],
                  1'b0 };
        imm_j_sext = {{11{imm_j[20]}}, imm_j};
        pcNext = pcCurrent + imm_j_sext;
      end
      OpJalr: begin
        pcNext = (rf_rs1_data + imm_i_sext) & ~32'b1;
      end
      OpBranch: begin
        pcNext = branch_taken ? pcCurrent + imm_b_sext : pcCurrent + 4;
      end
      default: begin
        pcNext = pcCurrent + 4;
      end
    endcase
  end

  //--------------------------------------------------------------------------
  // Cycle and Instruction Counters.
  //--------------------------------------------------------------------------
  always @(posedge clk) begin
    if (rst) begin
      cycles_current   <= 32'd0;
      num_insns_current <= 32'd0;
    end else begin
      cycles_current   <= cycles_current + 1;
      num_insns_current <= num_insns_current + 1;
    end
  end

endmodule

//----------------------------------------------------------------
// MemorySingleCycle
//----------------------------------------------------------------
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    input  wire rst,
    input  wire clock_mem,
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

  // Ensure PC is word-aligned.
  always_comb begin
    assert(pc_to_imem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // Instruction memory read.
  always @(posedge clock_mem) begin
    if (!rst)
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end

  // Data memory write and read.
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
// Processor Top-Level
//----------------------------------------------------------------
module Processor (
    input  wire clock_proc,
    input  wire clock_mem,
    input  wire rst,
    input  logic [(8*32)-1:0] test_case, // For testbench use.
    output logic halt
);
  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;
  wire [`REG_SIZE] cycles_current, num_insns_current;

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

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .cycles_current(cycles_current),
      .num_insns_current(num_insns_current)
  );
endmodule
