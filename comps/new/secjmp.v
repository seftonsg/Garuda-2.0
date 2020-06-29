module secjmp_tb();
wire [63:0] o;
reg [63:0] i;
secjmp secjmp1(i, o);
integer i;
initial begin
 i= 16;

#10 
  $display ("Value of o is %d ",o);
end
endmodule
module secjmp(i, o);
output [63:0] o;
reg [63:0] o;
input [63:0] i;
reg [63:0] internal0;
reg [63:0] internal1;
always @(*)
begin
 internal1 = 0;
 internal0 = 0;
 o = 0;
if (((((((i >> 26) & (-1 >> 58)) == 0) & (((i >> 0) & (-1 >> 58)) == 9)) | ((((i >> 26) & (-1 >> 58)) == 0) & (((i >> 0) & (-1 >> 58)) == 8))) | ((((i >> 26) & (-1 >> 58)) == 2) | (((i >> 26) & (-1 >> 58)) == 3))))
begin
if ((((i >> 10) & (-1 >> 38)) == 0))
begin
 internal0 = i;
end
else begin
end
end
else begin
end
if (~((((((i >> 26) & (-1 >> 58)) == 0) & (((i >> 0) & (-1 >> 58)) == 9)) | ((((i >> 26) & (-1 >> 58)) == 0) & (((i >> 0) & (-1 >> 58)) == 8))) | ((((i >> 26) & (-1 >> 58)) == 2) | (((i >> 26) & (-1 >> 58)) == 3))))
begin
 internal1 = i;
end
else begin
end
 o = (internal0 | internal1);



end
endmodule

