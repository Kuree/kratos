module mod (
);

logic a;
logic b;
logic [31:0] c;
logic [31:0] fd;
initial begin
  fd = $fopen ("test.sv", "r");
  for (int unsigned i = 0; i < 10; i += 1) begin
      c = $fscanf (fd, "%d %d", a, b);
    end
  $fclose (fd);
end
endmodule   // mod

