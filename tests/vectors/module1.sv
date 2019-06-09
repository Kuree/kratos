module module1(a, b, c, f, g);
output [3:0] f;
output [3: 0] g;
input a, b, c;
// Description goes here
endmodule

// alternatively
module module2(input a, b, c, output f);
// Description goes here
endmodule

module module3(a, b, c, f);
    output [0:3] f;
    input a, b, c;
// Description goes here
endmodule
