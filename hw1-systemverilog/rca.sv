// Tell the simulator that we express delays at nanosecond granularity, and that
// it should track timing at nanosecond granularity as well.
`timescale 1ns / 1ns

// prevents undeclared wires from being inferred
`default_nettype none

/* A half-adder that adds two 1-bit numbers and produces a 2-bit result (as sum
 * and carry-out) */
module halfadder(input wire  a,
                 input wire  b,
                 output wire s,
                 output wire cout);
   assign s    = a ^ b;
   assign cout = a & b;
endmodule

/* A full adder adds three 1-bit numbers (a, b, carry-in) and produces a 2-bit
 * result (as sum and carry-out) */
module fulladder(input wire  cin,
                 input wire  a,
                 input wire  b,
                 output wire s,
                 output wire cout);
   wire s_tmp, cout_tmp1, cout_tmp2;

   // FIXED: The 's' output of halfadder h0 now goes to s_tmp
   // instead of wiring directly to 'cout'
   halfadder h0(
       .a(a),
       .b(b),
       .s(s_tmp),       // << CHANGED from ".s(cout)" to ".s(s_tmp)"
       .cout(cout_tmp1)
   );

   halfadder h1(
       .a(s_tmp),
       .b(cin),
       .s(s),
       .cout(cout_tmp2)
   );

   // Combine both halfadders' carry signals
   assign cout = cout_tmp1 | cout_tmp2;
endmodule

/* A full adder that adds 2-bit numbers. Builds upon the 1-bit full adder. */
module fulladder2(
    input  wire       cin,
    input  wire [1:0] a,
    input  wire [1:0] b,
    output wire [1:0] s,
    output wire       cout
);
    wire cout_tmp;

    // Low-bit adder
    // Use the carry-out here as the carry-in to the high-bit adder
    fulladder a0(
        .cin(cin),
        .a(a[0]), 
        .b(b[0]), 
        .s(s[0]), 
        .cout(cout_tmp)
    );

    // High-bit adder
    // Drive s[1] (instead of s[0] again)
    // The carry-out of this stage is the final cout
    fulladder a1(
        .cin(cout_tmp),
        .a(a[1]), 
        .b(b[1]), 
        .s(s[1]),   // FIX: changed from s[0] to s[1]
        .cout(cout) // FIX: changed from cout_tmp to cout
    );
endmodule

/**
 * Demo module that adds a constant 2 to a 4-bit input taken from the FPGA
 * board's buttons B2,B5,B4,B6. The sum is displayed on the board's LEDs.
 * Note: there are no bugs in this module.
 */
/* 4-bit ripple-carry adder that adds two 4-bit numbers */
module rca4(
    input  wire [3:0] a,
    input  wire [3:0] b,
    output wire [3:0] sum,
    output wire       carry_out
);
    wire cout_mid;

    // Add the lower 2 bits
    fulladder2 adder_lo (
        .cin(1'b0),        // Typically start with carry_in = 0
        .a(a[1:0]),
        .b(b[1:0]),
        .s(sum[1:0]),
        .cout(cout_mid)
    );

    // Add the upper 2 bits
    fulladder2 adder_hi (
        .cin(cout_mid),
        .a(a[3:2]),
        .b(b[3:2]),
        .s(sum[3:2]),
        .cout(carry_out)
    );
endmodule
