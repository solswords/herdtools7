
constant A = 1 << 10;
constant B = 1 << 10;

func myfunction(a: integer {0..A}, b: integer {0..B})
begin
  var z = a ^ b;
end;

func main () => integer
begin
  myfunction(A, 1);
  myfunction(0, 1);

  return 0;
end;
