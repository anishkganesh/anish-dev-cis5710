`timescale 1ns / 1ps

module gp1(input wire a, b, output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

// gp4: 4-bit group generate/propagate
module gp4(
    input wire [3:0] gin, pin,
    input wire       cin,
    output wire      gout, pout,
    output wire [2:0] cout
);
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | (pin[1] & pin[0] & cin);
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | (pin[2] & pin[1] & gin[0]) | (pin[2] & pin[1] & pin[0] & cin);

   assign gout = gin[3] 
                 | (pin[3] & gin[2]) 
                 | (pin[3] & pin[2] & gin[1]) 
                 | (pin[3] & pin[2] & pin[1] & gin[0]);
   assign pout = &pin;
endmodule

// gp8: 8-bit group generate/propagate
module gp8(
    input wire [7:0] gin, pin,
    input wire       cin,
    output wire      gout, pout,
    output wire [6:0] cout
);
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | (pin[1] & pin[0] & cin);
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | (pin[2] & pin[1] & gin[0]) | (pin[2] & pin[1] & pin[0] & cin);
   assign cout[3] = gin[3] | (pin[3] & gin[2]) | (pin[3] & pin[2] & gin[1]) | (pin[3] & pin[2] & pin[1] & gin[0]) 
                    | (pin[3] & pin[2] & pin[1] & pin[0] & cin);
   assign cout[4] = gin[4] | (pin[4] & gin[3]) | (pin[4] & pin[3] & gin[2]) 
                    | (pin[4] & pin[3] & pin[2] & gin[1]) 
                    | (pin[4] & pin[3] & pin[2] & pin[1] & gin[0]) 
                    | (pin[4] & pin[3] & pin[2] & pin[1] & pin[0] & cin);
   assign cout[5] = gin[5] | (pin[5] & gin[4]) | (pin[5] & pin[4] & gin[3]) 
                    | (pin[5] & pin[4] & pin[3] & pin[2] & gin[1]) 
                    | (pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & gin[0]) 
                    | (pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & pin[0] & cin);
   assign cout[6] = gin[6] | (pin[6] & gin[5]) | (pin[6] & pin[5] & gin[4]) 
                    | (pin[6] & pin[5] & pin[4] & gin[3]) 
                    | (pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & gin[1]) 
                    | (pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & gin[0]) 
                    | (pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & pin[0] & cin);

   assign gout = gin[7]
                 | (pin[7] & gin[6])
                 | (pin[7] & pin[6] & gin[5])
                 | (pin[7] & pin[6] & pin[5] & gin[4])
                 | (pin[7] & pin[6] & pin[5] & pin[4] & gin[3])
                 | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & gin[2])
                 | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & gin[1])
                 | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & gin[0]);
   assign pout = &pin;
endmodule

// cla: 32-bit two-level CLA
module cla(
    input  wire [31:0] a, b,
    input  wire        cin,
    output wire [31:0] sum
);
   wire [31:0] g, p;
   genvar i;
   generate
     for (i=0; i<32; i=i+1) begin: bit_gp
       gp1 gpinst(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
     end
   endgenerate

   wire [7:0] nibG, nibP;
   wire [2:0] unused_cout[7:0];
   for (i=0; i<8; i=i+1) begin: nibble_partial
     gp4 partialGp4(
       .gin(g[4*i+3 : 4*i]),
       .pin(p[4*i+3 : 4*i]),
       .cin(1'b0),
       .gout(nibG[i]),
       .pout(nibP[i]),
       .cout(unused_cout[i])
     );
   end

   wire [6:0] nibCarry;
   wire gout_ignored, pout_ignored;
   gp8 aggregator(
     .gin(nibG),
     .pin(nibP),
     .cin(cin),
     .gout(gout_ignored),
     .pout(pout_ignored),
     .cout(nibCarry)
   );

   wire [7:0] nibble_cin;
   assign nibble_cin[0] = cin;
   for (i=1; i<8; i=i+1) begin: nibcarry_loop
     assign nibble_cin[i] = nibCarry[i-1];
   end

   for (i=0; i<8; i=i+1) begin: final_nibble
     wire [2:0] ctemp;
     wire [3:0] ginLocal = g[4*i+3 : 4*i];
     wire [3:0] pinLocal = p[4*i+3 : 4*i];
     wire gout_unused, pout_unused;

     gp4 finalGp4(
       .gin(ginLocal),
       .pin(pinLocal),
       .cin(nibble_cin[i]),
       .gout(gout_unused),
       .pout(pout_unused),
       .cout(ctemp)
     );

     assign sum[4*i]   = a[4*i]   ^ b[4*i]   ^ nibble_cin[i];
     assign sum[4*i+1] = a[4*i+1] ^ b[4*i+1] ^ ctemp[0];
     assign sum[4*i+2] = a[4*i+2] ^ b[4*i+2] ^ ctemp[1];
     assign sum[4*i+3] = a[4*i+3] ^ b[4*i+3] ^ ctemp[2];
   end
endmodule
