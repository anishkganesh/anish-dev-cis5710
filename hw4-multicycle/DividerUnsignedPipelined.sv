/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module DividerUnsignedPipelined (
    input wire clk, rst, stall,
    input  wire  [31:0] i_dividend,
    input  wire  [31:0] i_divisor,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);

    reg [31:0] divisor_reg [0:6];
    reg [31:0] remainder_reg [0:6];
    reg [31:0] quotient_reg [0:6];
    reg [31:0] dividend_reg [0:6];
    
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            divisor_reg[0] <= 32'b0;
            remainder_reg[0] <= 32'b0;
            quotient_reg[0] <= 32'b0;
            dividend_reg[0] <= 32'b0;
        end else if (!stall) begin
            divisor_reg[0] <= i_divisor;
            remainder_reg[0] <= 32'b0;
            quotient_reg[0] <= 32'b0;
            dividend_reg[0] <= i_dividend;
        end
    end
    
    genvar stage;
    generate
        for (stage = 0; stage < 6; stage = stage + 1) begin: pipeline_stage
            wire [31:0] stage_remainder [0:4];
            wire [31:0] stage_quotient [0:4];
            wire [31:0] stage_dividend [0:4];
            
            assign stage_remainder[0] = remainder_reg[stage];
            assign stage_quotient[0] = quotient_reg[stage];
            assign stage_dividend[0] = dividend_reg[stage];
            
            genvar iter;
            for (iter = 0; iter < 4; iter = iter + 1) begin: division_iteration
                divu_1iter div_iter (
                    .i_dividend(stage_dividend[iter]),
                    .i_divisor(divisor_reg[stage]),
                    .i_remainder(stage_remainder[iter]),
                    .i_quotient(stage_quotient[iter]),
                    .o_dividend(stage_dividend[iter+1]),
                    .o_remainder(stage_remainder[iter+1]),
                    .o_quotient(stage_quotient[iter+1])
                );
            end
            
            always_ff @(posedge clk or posedge rst) begin
                if (rst) begin
                    divisor_reg[stage+1] <= 32'b0;
                    remainder_reg[stage+1] <= 32'b0;
                    quotient_reg[stage+1] <= 32'b0;
                    dividend_reg[stage+1] <= 32'b0;
                end else if (!stall) begin
                    divisor_reg[stage+1] <= divisor_reg[stage];
                    remainder_reg[stage+1] <= stage_remainder[4];
                    quotient_reg[stage+1] <= stage_quotient[4];
                    dividend_reg[stage+1] <= stage_dividend[4];
                end
            end
        end
    endgenerate
    
    wire [31:0] final_remainder [0:8];
    wire [31:0] final_quotient [0:8];
    wire [31:0] final_dividend [0:8];
    
    assign final_remainder[0] = remainder_reg[6];
    assign final_quotient[0] = quotient_reg[6];
    assign final_dividend[0] = dividend_reg[6];
    
    genvar final_iter;
    generate
        for (final_iter = 0; final_iter < 8; final_iter = final_iter + 1) begin: final_division_iteration
            divu_1iter final_div_iter (
                .i_dividend(final_dividend[final_iter]),
                .i_divisor(divisor_reg[6]),
                .i_remainder(final_remainder[final_iter]),
                .i_quotient(final_quotient[final_iter]),
                .o_dividend(final_dividend[final_iter+1]),
                .o_remainder(final_remainder[final_iter+1]),
                .o_quotient(final_quotient[final_iter+1])
            );
        end
    endgenerate
    
    assign o_remainder = final_remainder[8];
    assign o_quotient = final_quotient[8];

endmodule


module divu_1iter (
    input  wire  [31:0] i_dividend,
    input  wire  [31:0] i_divisor,
    input  wire  [31:0] i_remainder,
    input  wire  [31:0] i_quotient,
    output logic [31:0] o_dividend,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);

    wire [31:0] next_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'h1);
    wire condition = (next_remainder >= i_divisor) && (i_divisor != 0);
    wire [31:0] updated_remainder = condition ? (next_remainder - i_divisor) : next_remainder;
    wire [31:0] updated_quotient = (i_quotient << 1) | {31'b0, condition};

    assign o_dividend = i_dividend << 1;
    assign o_remainder = updated_remainder;
    assign o_quotient = updated_quotient;

endmodule
