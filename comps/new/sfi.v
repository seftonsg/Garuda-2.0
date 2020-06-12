module SFI_tb();
wire [63:0] ro;
reg [63:0] ri;
SFI SFI1(ri, ro);
integer i;
initial begin
 ri= 16;

#10 
  $display ("Value of ro is %d ",ro);
end
endmodule
module SFI(ri, ro);
output [63:0] ro;
reg [63:0] ro;
input [63:0] ri;
reg [63:0] internal0;
reg [63:0] internal1;
reg [63:0] internal2;
always @(*)
begin
 internal2 = 0;
 internal1 = 0;
 internal0 = 0;
 ro = 0;
if (((((ri >> 26) & (-1 >> 58)) == 40) | (((ri >> 26) & (-1 >> 58)) == 43)))
begin
 internal2 = (72057594037927935 & ri);
 internal0 = (-6773413839565225984 | internal2);

end
else begin
end
if (~((((ri >> 26) & (-1 >> 58)) == 40) | (((ri >> 26) & (-1 >> 58)) == 43)))
begin
 internal1 = ri;
end
else begin
end
 ro = (internal0 | internal1);



end
endmodule

