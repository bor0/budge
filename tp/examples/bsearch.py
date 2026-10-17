# Extracted by budge-tp from the checked theorem thProgram:
#   {⊤} $L = 0; $H = S($N); WHILE (¬EQ(S($L),$H)) { $M = DIV2(ADD($L,$H)); IF (LE(MUL($M,$M),$N)) { $L = $M; } ELSE { $H = $M; } } {(LE(MUL($L,$L),$N)∧¬LE(MUL(S($L),S($L)),$N))}
# Partial correctness: if it returns, the postcondition holds.


def isqrt(N: int):
    if N < 0:
        raise ValueError('N < 0')
    L = 0
    H = N + 1
    while not ((L + 1) == H):
        M = (L + H) // 2
        if (M * M) <= N:
            L = M
        else:
            H = M
    assert ((L * L) <= N) and (not (((L + 1) * (L + 1)) <= N))
    return L
