module example_tb();
wire out;
reg in;
example example1(in, out);
integer i;
initial begin
 in= 0;

#10 
  $display ("Value of out is %b ",out);
end
endmodule
module example(in, out);
reg [31:0] r;
output out;
reg out;
reg [2:0] mid;
input in;
always @(*)
begin
 out = 0;
 mid[0] = in;

 mid[1] = in;

 mid[2] = in;

 r = 0;
 r = (r + mid[0] );

 r = (r + mid[1] );

 r = (r + mid[2] );

if ((r < 2))
begin
 out = 0;
end
else begin
 out = 1;
end

end
endmodule

