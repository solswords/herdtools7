var g : integer = 0;

func increment() => boolean
begin
    g = g + 1;
    return g < 1000;
end;

func main() => integer
begin
    assert(increment()); // Illegal, since increment is not pure.
    assert(1); // Illegal as 1 is not boolean-typed.
    return 0;
end;
