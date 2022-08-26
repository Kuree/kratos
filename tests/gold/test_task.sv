module TB (
);

task delay_finish;
begin
  #5;
  $finish ();
end
endtask
initial begin
  delay_finish ();
end
endmodule   // TB

