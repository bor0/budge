# Extracted by budge-tp from the checked theorem thProgram:
#   {⊤} $A = $X; $B = $Y; WHILE (¬EQ($B,0)) { $T = MOD($A,$B); $A = $B; $B = $T; } {ALL(((EX(EQ($A,MUL(V(S(0)),V(0))))=>(EX(EQ($X,MUL(V(S(0)),V(0))))∧EX(EQ($Y,MUL(V(S(0)),V(0))))))∧((EX(EQ($X,MUL(V(S(0)),V(0))))∧EX(EQ($Y,MUL(V(S(0)),V(0)))))=>EX(EQ($A,MUL(V(S(0)),V(0)))))))}
# Partial correctness: if it returns, the postcondition holds.


def gcd(X: int, Y: int):
    if X < 0:
        raise ValueError('X < 0')
    if Y < 0:
        raise ValueError('Y < 0')
    A = X
    B = Y
    while not (B == 0):
        T = A % B
        A = B
        B = T
    # postcondition (proved, not executable): ALL(((EX(EQ($A,MUL(V(S(0)),V(0))))=>(EX(EQ($X,MUL(V(S(0)),V(0))))∧EX(EQ($Y,MUL(V(S(0)),V(0))))))∧((EX(EQ($X,MUL(V(S(0)),V(0))))∧EX(EQ($Y,MUL(V(S(0)),V(0)))))=>EX(EQ($A,MUL(V(S(0)),V(0)))))))
    return A
