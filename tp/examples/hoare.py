# Extracted by budge-tp from the checked theorem thProgram:
#   {⊤} $I = 0; $S = 0; WHILE (¬EQ($I,$N)) { IF (EQ(MOD2($I),S(0))) { $S = S($S); } ELSE { ; } $I = S($I); } {EQ($S,DIV2($N))}
# Partial correctness: if it returns, the postcondition holds.


def count_odd_below(N: int):
    if N < 0:
        raise ValueError('N < 0')
    I = 0
    S = 0
    while not (I == N):
        if (I % 2) == 1:
            S = S + 1
        I = I + 1
    assert S == (N // 2)
    return S
