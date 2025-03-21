module MyClockGen (
	input_clk_25MHz,
	clk_proc,
	clk_mem,
	locked
);
	input input_clk_25MHz;
	output wire clk_proc;
	output wire clk_mem;
	output wire locked;
	wire clkfb;
	(* FREQUENCY_PIN_CLKI = "25" *) (* FREQUENCY_PIN_CLKOP = "4.16667" *) (* FREQUENCY_PIN_CLKOS = "4.01003" *) (* ICP_CURRENT = "12" *) (* LPF_RESISTOR = "8" *) (* MFG_ENABLE_FILTEROPAMP = "1" *) (* MFG_GMCREF_SEL = "2" *) EHXPLLL #(
		.PLLRST_ENA("DISABLED"),
		.INTFB_WAKE("DISABLED"),
		.STDBY_ENABLE("DISABLED"),
		.DPHASE_SOURCE("DISABLED"),
		.OUTDIVIDER_MUXA("DIVA"),
		.OUTDIVIDER_MUXB("DIVB"),
		.OUTDIVIDER_MUXC("DIVC"),
		.OUTDIVIDER_MUXD("DIVD"),
		.CLKI_DIV(6),
		.CLKOP_ENABLE("ENABLED"),
		.CLKOP_DIV(128),
		.CLKOP_CPHASE(64),
		.CLKOP_FPHASE(0),
		.CLKOS_ENABLE("ENABLED"),
		.CLKOS_DIV(133),
		.CLKOS_CPHASE(97),
		.CLKOS_FPHASE(2),
		.FEEDBK_PATH("INT_OP"),
		.CLKFB_DIV(1)
	) pll_i(
		.RST(1'b0),
		.STDBY(1'b0),
		.CLKI(input_clk_25MHz),
		.CLKOP(clk_proc),
		.CLKOS(clk_mem),
		.CLKFB(clkfb),
		.CLKINTFB(clkfb),
		.PHASESEL0(1'b0),
		.PHASESEL1(1'b0),
		.PHASEDIR(1'b1),
		.PHASESTEP(1'b1),
		.PHASELOADREG(1'b1),
		.PLLWAKESYNC(1'b0),
		.ENCLKOP(1'b0),
		.LOCK(locked)
	);
endmodule
module cla (
	a,
	b,
	cin,
	sum
);
	reg _sv2v_0;
	input wire [31:0] a;
	input wire [31:0] b;
	input wire cin;
	output reg [31:0] sum;
	always @(*) begin
		if (_sv2v_0)
			;
		sum = (a + b) + {31'd0, cin};
	end
	initial _sv2v_0 = 0;
endmodule
module divider_unsigned (
	i_dividend,
	i_divisor,
	o_quotient,
	o_remainder
);
	reg _sv2v_0;
	input wire [31:0] i_dividend;
	input wire [31:0] i_divisor;
	output reg [31:0] o_quotient;
	output reg [31:0] o_remainder;
	reg [31:0] quotient;
	reg [31:0] remainder;
	integer i;
	always @(*) begin
		if (_sv2v_0)
			;
		quotient = 32'd0;
		remainder = 32'd0;
		if (i_divisor == 32'd0) begin
			quotient = 32'hffffffff;
			remainder = i_dividend;
		end
		else
			for (i = 0; i < 32; i = i + 1)
				begin
					remainder = {remainder[30:0], i_dividend[31 - i]};
					if (remainder >= i_divisor) begin
						remainder = remainder + (~i_divisor + 1);
						quotient[31 - i] = 1'b1;
					end
					else
						quotient[31 - i] = 1'b0;
				end
		o_quotient = quotient;
		o_remainder = remainder;
	end
	initial _sv2v_0 = 0;
endmodule
module RegFile (
	rd,
	rd_data,
	rs1,
	rs1_data,
	rs2,
	rs2_data,
	clk,
	we,
	rst
);
	input wire [4:0] rd;
	input wire [31:0] rd_data;
	input wire [4:0] rs1;
	output wire [31:0] rs1_data;
	input wire [4:0] rs2;
	output wire [31:0] rs2_data;
	input wire clk;
	input wire we;
	input wire rst;
	localparam signed [31:0] NumRegs = 32;
	reg [31:0] regs [0:31];
	assign rs1_data = (rs1 == 5'd0 ? 32'd0 : regs[rs1]);
	assign rs2_data = (rs2 == 5'd0 ? 32'd0 : regs[rs2]);
	always @(posedge clk)
		if (rst) begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < NumRegs; i = i + 1)
				regs[i] <= 32'd0;
		end
		else if (we && (rd != 5'd0))
			regs[rd] <= rd_data;
endmodule
module DatapathSingleCycle (
	clk,
	rst,
	halt,
	pc_to_imem,
	insn_from_imem,
	addr_to_dmem,
	load_data_from_dmem,
	store_data_to_dmem,
	store_we_to_dmem,
	cycles_current,
	num_insns_current
);
	reg _sv2v_0;
	input wire clk;
	input wire rst;
	output reg halt;
	output wire [31:0] pc_to_imem;
	input wire [31:0] insn_from_imem;
	output wire [31:0] addr_to_dmem;
	input wire [31:0] load_data_from_dmem;
	output wire [31:0] store_data_to_dmem;
	output wire [3:0] store_we_to_dmem;
	output reg [31:0] cycles_current;
	output reg [31:0] num_insns_current;
	wire [6:0] insn_funct7;
	wire [4:0] insn_rs2;
	wire [4:0] insn_rs1;
	wire [2:0] insn_funct3;
	wire [4:0] insn_rd;
	wire [6:0] insn_opcode;
	assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;
	wire [11:0] imm_i;
	assign imm_i = insn_from_imem[31:20];
	wire [4:0] imm_shamt = insn_from_imem[24:20];
	wire [11:0] imm_s;
	assign {imm_s[11:5], imm_s[4:0]} = {insn_funct7, insn_rd};
	wire [12:0] imm_b;
	assign imm_b = {insn_funct7[6], insn_rd[0], insn_funct7[5:0], insn_rd[4:1], 1'b0};
	wire [31:0] imm_i_sext = {{20 {imm_i[11]}}, imm_i};
	wire [31:0] imm_s_sext = {{20 {imm_s[11]}}, imm_s};
	wire [31:0] imm_b_sext = {{19 {imm_b[12]}}, imm_b};
	localparam [6:0] OpLoad = 7'b0000011;
	localparam [6:0] OpStore = 7'b0100011;
	localparam [6:0] OpBranch = 7'b1100011;
	localparam [6:0] OpRegImm = 7'b0010011;
	localparam [6:0] OpRegReg = 7'b0110011;
	localparam [6:0] OpEnviron = 7'b1110011;
	localparam [6:0] OpLui = 7'b0110111;
	localparam [6:0] OpAuipc = 7'b0010111;
	localparam [6:0] OpJal = 7'b1101111;
	localparam [6:0] OpJalr = 7'b1100111;
	wire insn_lui = insn_opcode == OpLui;
	wire insn_addi = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b000);
	wire insn_slti = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b010);
	wire insn_sltiu = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b011);
	wire insn_xori = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b100);
	wire insn_ori = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b110);
	wire insn_andi = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b111);
	wire insn_slli = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b001)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srli = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srai = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_add = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sub = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_sll = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b001)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_slt = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b010)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sltu = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b011)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_xor = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b100)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srl = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sra = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_or = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b110)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_and = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b111)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_lw = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b010);
	wire insn_sw = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b010);
	wire insn_beq = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b000);
	wire insn_bne = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b001);
	wire insn_blt = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b100);
	wire insn_bge = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b101);
	wire insn_bltu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b110);
	wire insn_bgeu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b111);
	wire insn_ecall = (insn_opcode == OpEnviron) && (insn_from_imem[31:7] == 25'd0);
	wire insn_lb = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b000);
	wire insn_lh = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b001);
	wire insn_lbu = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b100);
	wire insn_lhu = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b101);
	wire insn_sb = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b000);
	wire insn_sh = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b001);
	wire [31:0] rf_rs1_data;
	wire [31:0] rf_rs2_data;
	reg reg_we;
	reg [31:0] reg_wdata;
	RegFile rf(
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
	reg [31:0] mem_addr;
	reg [3:0] mem_we;
	reg [31:0] mem_wdata;
	assign addr_to_dmem = mem_addr;
	assign store_data_to_dmem = mem_wdata;
	assign store_we_to_dmem = mem_we;
	wire [31:0] sub_result;
	cla cla_sub_inst(
		.a(rf_rs1_data),
		.b(~rf_rs2_data),
		.cin(1'b1),
		.sum(sub_result)
	);
	wire [31:0] div_u_dividend;
	wire [31:0] div_u_divisor;
	wire [31:0] div_u_quotient;
	wire [31:0] div_u_remainder;
	divider_unsigned div_u_inst(
		.i_dividend(div_u_dividend),
		.i_divisor(div_u_divisor),
		.o_quotient(div_u_quotient),
		.o_remainder(div_u_remainder)
	);
	wire [31:0] div_s_dividend;
	wire [31:0] div_s_divisor;
	wire [31:0] div_s_quotient;
	wire [31:0] div_s_remainder;
	divider_unsigned div_s_inst(
		.i_dividend(div_s_dividend),
		.i_divisor(div_s_divisor),
		.o_quotient(div_s_quotient),
		.o_remainder(div_s_remainder)
	);
	assign div_u_dividend = rf_rs1_data;
	assign div_u_divisor = rf_rs2_data;
	assign div_s_dividend = (rf_rs1_data[31] ? ~rf_rs1_data + 1 : rf_rs1_data);
	assign div_s_divisor = (rf_rs2_data[31] ? ~rf_rs2_data + 1 : rf_rs2_data);
	reg [31:0] alu_result;
	reg branch_taken;
	reg illegal_insn;
	reg [31:0] pcNext;
	reg [31:0] pcCurrent;
	always @(*) begin : sv2v_autoblock_1
		reg signed [63:0] mult_temp_signed;
		reg [63:0] mult_temp_unsigned;
		if (_sv2v_0)
			;
		alu_result = 32'd0;
		reg_we = 1'b0;
		mem_addr = 32'd0;
		mem_we = 4'b0000;
		mem_wdata = 32'd0;
		branch_taken = 1'b0;
		halt = 1'b0;
		illegal_insn = 1'b0;
		case (insn_opcode)
			OpLui: begin
				alu_result = {insn_from_imem[31:12], 12'b000000000000};
				reg_we = 1'b1;
			end
			OpAuipc: begin
				alu_result = pcCurrent + {insn_from_imem[31:12], 12'b000000000000};
				reg_we = 1'b1;
			end
			OpJal: begin : sv2v_autoblock_2
				reg [20:0] imm_j;
				reg [31:0] imm_j_sext;
				imm_j = {insn_from_imem[31], insn_from_imem[19:12], insn_from_imem[20], insn_from_imem[30:21], 1'b0};
				imm_j_sext = {{11 {imm_j[20]}}, imm_j};
				alu_result = pcCurrent + 4;
				reg_we = 1'b1;
			end
			OpJalr: begin
				alu_result = pcCurrent + 4;
				reg_we = 1'b1;
			end
			OpRegImm:
				if (insn_addi) begin
					alu_result = rf_rs1_data + imm_i_sext;
					reg_we = 1'b1;
				end
				else if (insn_slti) begin
					alu_result = ($signed(rf_rs1_data) < $signed(imm_i_sext) ? 32'd1 : 32'd0);
					reg_we = 1'b1;
				end
				else if (insn_sltiu) begin
					alu_result = (rf_rs1_data < imm_i_sext ? 32'd1 : 32'd0);
					reg_we = 1'b1;
				end
				else if (insn_xori) begin
					alu_result = rf_rs1_data ^ imm_i_sext;
					reg_we = 1'b1;
				end
				else if (insn_ori) begin
					alu_result = rf_rs1_data | imm_i_sext;
					reg_we = 1'b1;
				end
				else if (insn_andi) begin
					alu_result = rf_rs1_data & imm_i_sext;
					reg_we = 1'b1;
				end
				else if (insn_slli) begin
					alu_result = rf_rs1_data << imm_shamt;
					reg_we = 1'b1;
				end
				else if (insn_srli) begin
					alu_result = rf_rs1_data >> imm_shamt;
					reg_we = 1'b1;
				end
				else if (insn_srai) begin
					alu_result = $signed(rf_rs1_data) >>> imm_shamt;
					reg_we = 1'b1;
				end
				else
					illegal_insn = 1'b1;
			OpRegReg:
				if (insn_from_imem[31:25] == 7'b0000001)
					case (insn_funct3)
						3'b000: begin
							mult_temp_signed = $signed(rf_rs1_data) * $signed(rf_rs2_data);
							alu_result = mult_temp_signed[31:0];
							reg_we = 1'b1;
						end
						3'b001: begin
							mult_temp_signed = $signed(rf_rs1_data) * $signed(rf_rs2_data);
							alu_result = mult_temp_signed[63:32];
							reg_we = 1'b1;
						end
						3'b010: begin : sv2v_autoblock_3
							reg signed [63:0] prod;
							prod = $signed({{32 {rf_rs1_data[31]}}, rf_rs1_data}) * $unsigned({32'd0, rf_rs2_data});
							alu_result = prod[63:32];
							reg_we = 1'b1;
						end
						3'b011: begin
							mult_temp_unsigned = rf_rs1_data * rf_rs2_data;
							alu_result = mult_temp_unsigned[63:32];
							reg_we = 1'b1;
						end
						3'b100: begin
							if (rf_rs2_data == 32'd0)
								alu_result = 32'hffffffff;
							else
								alu_result = (rf_rs1_data[31] ^ rf_rs2_data[31] ? ~div_s_quotient + 1 : div_s_quotient);
							reg_we = 1'b1;
						end
						3'b101: begin
							if (rf_rs2_data == 32'd0)
								alu_result = 32'hffffffff;
							else
								alu_result = div_u_quotient;
							reg_we = 1'b1;
						end
						3'b110: begin
							if (rf_rs2_data == 32'd0)
								alu_result = rf_rs1_data;
							else
								alu_result = (rf_rs1_data[31] ? ~div_s_remainder + 1 : div_s_remainder);
							reg_we = 1'b1;
						end
						3'b111: begin
							if (rf_rs2_data == 32'd0)
								alu_result = rf_rs1_data;
							else
								alu_result = div_u_remainder;
							reg_we = 1'b1;
						end
						default: illegal_insn = 1'b1;
					endcase
				else if (insn_add) begin
					alu_result = rf_rs1_data + rf_rs2_data;
					reg_we = 1'b1;
				end
				else if (insn_sub) begin
					alu_result = sub_result;
					reg_we = 1'b1;
				end
				else if (insn_sll) begin
					alu_result = rf_rs1_data << rf_rs2_data[4:0];
					reg_we = 1'b1;
				end
				else if (insn_slt) begin
					alu_result = ($signed(rf_rs1_data) < $signed(rf_rs2_data) ? 32'd1 : 32'd0);
					reg_we = 1'b1;
				end
				else if (insn_sltu) begin
					alu_result = (rf_rs1_data < rf_rs2_data ? 32'd1 : 32'd0);
					reg_we = 1'b1;
				end
				else if (insn_xor) begin
					alu_result = rf_rs1_data ^ rf_rs2_data;
					reg_we = 1'b1;
				end
				else if (insn_srl) begin
					alu_result = rf_rs1_data >> rf_rs2_data[4:0];
					reg_we = 1'b1;
				end
				else if (insn_sra) begin
					alu_result = $signed(rf_rs1_data) >>> rf_rs2_data[4:0];
					reg_we = 1'b1;
				end
				else if (insn_or) begin
					alu_result = rf_rs1_data | rf_rs2_data;
					reg_we = 1'b1;
				end
				else if (insn_and) begin
					alu_result = rf_rs1_data & rf_rs2_data;
					reg_we = 1'b1;
				end
				else
					illegal_insn = 1'b1;
			OpLoad: begin
				mem_addr = rf_rs1_data + imm_i_sext;
				if (insn_lb || insn_lbu) begin : sv2v_autoblock_4
					reg [7:0] byte_data;
					case (mem_addr[1:0])
						2'b00: byte_data = load_data_from_dmem[7:0];
						2'b01: byte_data = load_data_from_dmem[15:8];
						2'b10: byte_data = load_data_from_dmem[23:16];
						default: byte_data = load_data_from_dmem[31:24];
					endcase
					alu_result = (insn_lb ? {{24 {byte_data[7]}}, byte_data} : {24'd0, byte_data});
					reg_we = 1'b1;
				end
				else if (insn_lh || insn_lhu) begin : sv2v_autoblock_5
					reg [15:0] half_data;
					half_data = (mem_addr[1] == 1'b0 ? load_data_from_dmem[15:0] : load_data_from_dmem[31:16]);
					alu_result = (insn_lh ? {{16 {half_data[15]}}, half_data} : {16'd0, half_data});
					reg_we = 1'b1;
				end
				else if (insn_lw) begin
					alu_result = load_data_from_dmem;
					reg_we = 1'b1;
				end
				else
					illegal_insn = 1'b1;
			end
			OpStore: begin
				mem_addr = rf_rs1_data + imm_s_sext;
				if (insn_sb)
					case (mem_addr[1:0])
						2'b00: begin
							mem_we = 4'b0001;
							mem_wdata = {24'd0, rf_rs2_data[7:0]};
						end
						2'b01: begin
							mem_we = 4'b0010;
							mem_wdata = {16'd0, rf_rs2_data[7:0], 8'd0};
						end
						2'b10: begin
							mem_we = 4'b0100;
							mem_wdata = {8'd0, rf_rs2_data[7:0], 16'd0};
						end
						default: begin
							mem_we = 4'b1000;
							mem_wdata = {rf_rs2_data[7:0], 24'd0};
						end
					endcase
				else if (insn_sh) begin
					if (mem_addr[1] == 1'b0) begin
						mem_we = 4'b0011;
						mem_wdata = {16'd0, rf_rs2_data[15:0]};
					end
					else begin
						mem_we = 4'b1100;
						mem_wdata = {rf_rs2_data[15:0], 16'd0};
					end
				end
				else if (insn_sw) begin
					mem_we = 4'b1111;
					mem_wdata = rf_rs2_data;
				end
				else
					illegal_insn = 1'b1;
			end
			OpBranch:
				case (insn_funct3)
					3'b000: branch_taken = rf_rs1_data == rf_rs2_data;
					3'b001: branch_taken = rf_rs1_data != rf_rs2_data;
					3'b100: branch_taken = $signed(rf_rs1_data) < $signed(rf_rs2_data);
					3'b101: branch_taken = $signed(rf_rs1_data) >= $signed(rf_rs2_data);
					3'b110: branch_taken = rf_rs1_data < rf_rs2_data;
					3'b111: branch_taken = rf_rs1_data >= rf_rs2_data;
					default: branch_taken = 1'b0;
				endcase
			OpEnviron:
				if (insn_ecall)
					halt = 1'b1;
				else
					illegal_insn = 1'b1;
			default: illegal_insn = 1'b1;
		endcase
		reg_wdata = alu_result;
	end
	always @(posedge clk)
		if (rst)
			pcCurrent <= 32'd0;
		else
			pcCurrent <= pcNext;
	assign pc_to_imem = pcCurrent;
	always @(*) begin
		if (_sv2v_0)
			;
		case (insn_opcode)
			OpJal: begin : sv2v_autoblock_6
				reg [20:0] imm_j;
				reg [31:0] imm_j_sext;
				imm_j = {insn_from_imem[31], insn_from_imem[19:12], insn_from_imem[20], insn_from_imem[30:21], 1'b0};
				imm_j_sext = {{11 {imm_j[20]}}, imm_j};
				pcNext = pcCurrent + imm_j_sext;
			end
			OpJalr: pcNext = (rf_rs1_data + imm_i_sext) & ~32'b00000000000000000000000000000001;
			OpBranch: pcNext = (branch_taken ? pcCurrent + imm_b_sext : pcCurrent + 4);
			default: pcNext = pcCurrent + 4;
		endcase
	end
	always @(posedge clk)
		if (rst) begin
			cycles_current <= 32'd0;
			num_insns_current <= 32'd0;
		end
		else begin
			cycles_current <= cycles_current + 1;
			num_insns_current <= num_insns_current + 1;
		end
	initial _sv2v_0 = 0;
endmodule
module MemorySingleCycle (
	rst,
	clock_mem,
	pc_to_imem,
	insn_from_imem,
	addr_to_dmem,
	load_data_from_dmem,
	store_data_to_dmem,
	store_we_to_dmem
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_WORDS = 512;
	input wire rst;
	input wire clock_mem;
	input wire [31:0] pc_to_imem;
	output reg [31:0] insn_from_imem;
	input wire [31:0] addr_to_dmem;
	output reg [31:0] load_data_from_dmem;
	input wire [31:0] store_data_to_dmem;
	input wire [3:0] store_we_to_dmem;
	reg [31:0] mem_array [0:NUM_WORDS - 1];
	initial $readmemh("mem_initial_contents.hex", mem_array);
	always @(*)
		if (_sv2v_0)
			;
	localparam signed [31:0] AddrMsb = $clog2(NUM_WORDS) + 1;
	localparam signed [31:0] AddrLsb = 2;
	always @(posedge clock_mem)
		if (!rst)
			insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
	always @(negedge clock_mem)
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
	initial _sv2v_0 = 0;
endmodule
`default_nettype none
module debouncer (
	i_clk,
	i_in,
	o_debounced,
	o_debug
);
	parameter NIN = 21;
	parameter LGWAIT = 17;
	input wire i_clk;
	input wire [NIN - 1:0] i_in;
	output reg [NIN - 1:0] o_debounced;
	output wire [30:0] o_debug;
	reg different;
	reg ztimer;
	reg [NIN - 1:0] r_in;
	reg [NIN - 1:0] q_in;
	reg [NIN - 1:0] r_last;
	reg [LGWAIT - 1:0] timer;
	initial q_in = 0;
	initial r_in = 0;
	initial different = 0;
	always @(posedge i_clk) q_in <= i_in;
	always @(posedge i_clk) r_in <= q_in;
	always @(posedge i_clk) r_last <= r_in;
	initial ztimer = 1'b1;
	initial timer = 0;
	always @(posedge i_clk)
		if (ztimer && different) begin
			timer <= {LGWAIT {1'b1}};
			ztimer <= 1'b0;
		end
		else if (!ztimer) begin
			timer <= timer - 1'b1;
			ztimer <= timer[LGWAIT - 1:1] == 0;
		end
		else begin
			ztimer <= 1'b1;
			timer <= 0;
		end
	always @(posedge i_clk) different <= (different && !ztimer) || (r_in != o_debounced);
	initial o_debounced = {NIN {1'b0}};
	always @(posedge i_clk)
		if (ztimer)
			o_debounced <= r_last;
	reg trigger;
	initial trigger = 1'b0;
	always @(posedge i_clk) trigger <= (((!ztimer && !different) && !(|i_in)) && (timer[LGWAIT - 1:2] == 0)) && timer[1];
	wire [30:0] debug;
	assign debug[30] = ztimer;
	assign debug[29] = trigger;
	assign debug[28] = 1'b0;
	generate
		if (NIN >= 14) begin : genblk1
			assign debug[27:14] = o_debounced[13:0];
			assign debug[13:0] = r_in[13:0];
		end
		else begin : genblk1
			assign debug[27:14 + NIN] = 0;
			assign debug[(14 + NIN) - 1:14] = o_debounced;
			assign debug[13:NIN] = 0;
			assign debug[NIN - 1:0] = r_in;
		end
	endgenerate
	assign o_debug = debug;
endmodule
module SystemDemo (
	external_clk_25MHz,
	btn,
	led
);
	input wire external_clk_25MHz;
	input wire [6:0] btn;
	output wire [7:0] led;
	localparam signed [31:0] MmapButtons = 32'hff001000;
	localparam signed [31:0] MmapLeds = 32'hff002000;
	wire rst_button_n;
	wire [30:0] ignore;
	wire clk_proc;
	debouncer #(.NIN(1)) db(
		.i_clk(clk_proc),
		.i_in(btn[0]),
		.o_debounced(rst_button_n),
		.o_debug(ignore)
	);
	wire clk_mem;
	wire clk_locked;
	MyClockGen clock_gen(
		.input_clk_25MHz(external_clk_25MHz),
		.clk_proc(clk_proc),
		.clk_mem(clk_mem),
		.locked(clk_locked)
	);
	wire rst = !rst_button_n || !clk_locked;
	wire [31:0] pc_to_imem;
	wire [31:0] insn_from_imem;
	wire [31:0] mem_data_addr;
	wire [31:0] mem_data_loaded_value;
	wire [31:0] mem_data_to_write;
	wire [3:0] mem_data_we;
	reg [7:0] led_state;
	assign led = led_state;
	always @(posedge clk_mem)
		if (rst)
			led_state <= 0;
		else if ((mem_data_addr == MmapLeds) && (mem_data_we[0] == 1))
			led_state <= mem_data_to_write[7:0];
	MemorySingleCycle #(.NUM_WORDS(1024)) memory(
		.rst(rst),
		.clock_mem(clk_mem),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.load_data_from_dmem(mem_data_loaded_value),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem((mem_data_addr == MmapLeds ? 4'd0 : mem_data_we))
	);
	wire halt;
	DatapathSingleCycle datapath(
		.clk(clk_proc),
		.rst(rst),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem(mem_data_we),
		.load_data_from_dmem((mem_data_addr == MmapButtons ? {25'd0, btn} : mem_data_loaded_value)),
		.halt(halt)
	);
endmodule