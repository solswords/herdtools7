// A helper function which prints its argument
func p{n: integer}() => integer{n}
begin
  print(n);
  return n;
end;

// A helper function which prints its first argument and returns an array
func arr(n: integer) => array[[8]] of integer
begin
  println(n);
  var arr : array[[8]] of integer;
  return arr;
end;

// A helper accessor pair taking two arguments
accessor Foo(a: integer, b: integer) <=> integer
begin
  getter begin
    return 0;
  end;

  setter = value_in begin
    pass;
  end;
end;

// A helper record type
type Record of record {
  a: integer,
  b: integer,
};

func main() => integer
begin
  println("Function calls:");
  Foo(p{3}, p{4}) = Foo(p{1}, p{2});
  println();

  println("Tuples:");
  let - = (p{1}, p{2});
  println();

  println("Non-short-circuiting binary operations:");
  let - = p{1} + p{2} + p{3};
  println();

  println("Array-indexing:");
  let - = arr(1)[[p{2}]];
  println();

  println("Slicing:");
  var bv : bits(64);
  let - = bv[p{1}, p{2}:p{3}, p{4}+:p{5}, p{6}*:p{7}];
  println();

  println("Record construction:");
  let - = Record{ a = p{1}, b = p{2} };
  println();

  println("Print statements:");
  println(p{1}, p{2}, p{3}, p{4});

  println("For-loop start/end expressions:");
  for i = p{1} to p{2} do
    let - = p{i + 2};
  end;
  println();

  return 0;
end;
