// Name: Anish Krishnan Ganesh
// PennKey: anishg
`timescale 1ns / 1ns

//======================================================================
// Single iteration of the unsigned division algorithm
//======================================================================
module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // Instead of OR-ing a 1-bit signal, we are concatenating:
    wire [31:0] remainder_shifted = { i_remainder[30:0], i_dividend[31] };

    wire [31:0] quotient_shifted  = i_quotient << 1;

    // After subtracting divisor
    wire [31:0] remainder_sub = remainder_shifted - i_divisor;

    wire remainder_lt_divisor = (remainder_shifted < i_divisor);

    assign o_remainder = remainder_lt_divisor ? remainder_shifted : remainder_sub;
    assign o_quotient  = remainder_lt_divisor ? quotient_shifted 
                                              : (quotient_shifted | 32'h1);

    // Dividend is always shifted left for next iteration
    assign o_dividend = i_dividend << 1;

endmodule

//======================================================================
// Fully unrolled 32-bit unsigned divider
//======================================================================
module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // We will store intermediate values for dividend/remainder/quotient
    // values across 32 iterations of "divu_1iter"
    wire [31:0] dividend [0:32];
    wire [31:0] remainder[0:32];
    wire [31:0] quotient [0:32];

    // Initialize iteration 0
    assign dividend[0]  = i_dividend;
    assign remainder[0] = 32'b0;
    assign quotient[0]  = 32'b0;

    // Generate 32 chained divu_1iter modules
    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : DIV_ITER
            divu_1iter iter (
                .i_dividend(dividend[i]),
                .i_divisor(i_divisor),
                .i_remainder(remainder[i]),
                .i_quotient(quotient[i]),
                .o_dividend(dividend[i+1]),
                .o_remainder(remainder[i+1]),
                .o_quotient(quotient[i+1])
            );
        end
    endgenerate

    // After 32 iterations, output the final quotient and remainder
    assign o_remainder = remainder[32];
    assign o_quotient  = quotient[32];

endmodule
