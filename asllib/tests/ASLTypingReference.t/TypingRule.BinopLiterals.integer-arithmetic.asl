func main() => integer
begin
    println("add_int: 10 + 20 = ", 10 + 20);
    println("sub_int: 10 - 20 = ", 10 - 20);
    println("mul_int: 10 * 20 = ", 10 * 20);
    println("div_int: 20 DIV 10 = ", 20 DIV 10);
    // println("invalid", "div_int: 20 DIV 0 = ", 20 DIV 0);
    // println("invalid", "div_int: 20 DIV 3 = ", 20 DIV 3);
    println("fdiv_int: 20 DIVRM 3 = ", 20 DIVRM 3);
    println("fdiv_int: -20 DIVRM 3 = ", -20 DIVRM 3);
    // println("invalid", "fdiv_int: 20 DIVRM -3 = ", 20 DIVRM -3);
    println("frem_int: 20 MOD 3 = ", 20 MOD 3);
    println("frem_int: -20 MOD 3 = ", -20 MOD 3);
    // println("invalid", "frem_int: 20 MOD -3 = ", 20 MOD -3);
    println("exp_int: 2 ^ 10 = ", 2 ^ 10);
    println("exp_int: -2 ^ 10 = ", -2 ^ 10);
    println("exp_int: -2 ^ 11 = ", -2 ^ 11);
    println("exp_int: 0 ^ 0 = ", 0 ^ 0);
    println("exp_int: -2 ^ 0 = ", -2 ^ 0);
    // println("invalid", "exp_int: 0 ^ -2 = ", 0 ^ -2);
    println("shiftleft_int: 1 << 10 = ", 1 << 10);
    println("shiftleft_int: 1 << 0 = ", 1 << 0);
    println("shiftleft_int: -1 << 10 = ", -1 << 10);
    // println("invalid", "shiftleft_int: 1 << -10 = ", 1 << -10);
    println("shiftright_int: 1 >> 10 = ", 1 >> 10);
    println("shiftright_int: 16 >> 2 = ", 16 >> 2);
    println("shiftright_int: -16 >> 2 = ", -16 >> 2);
    println("shiftright_int: 1 >> 0 = ", 1 >> 0);
    println("shiftright_int: -1 >> 10 = ", -1 >> 10);
    // println("invalid", "shiftright_int: 1 >> -10 = ", 1 >> -10);
    return 0;
end;
