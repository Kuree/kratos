module gen (
);

logic a;
initial begin
  assert (a) else $hgdb_assert_fail (gen, "test.py", 32'h2A);
end
endmodule   // gen

