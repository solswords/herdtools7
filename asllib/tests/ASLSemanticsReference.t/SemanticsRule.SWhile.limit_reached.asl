func main () => integer
begin
  var i: integer = 0;
  while i <= 3 looplimit 2 do
    assert i <= 3;
    i = i + 1;
   end;
  return 0;
end;
