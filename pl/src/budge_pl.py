"""Budge-PL engine: an interpreter and a macro assembler.

The interpreter is fastEvaluate' from budge-pl.lhs. Budge-PL arithmetic is unary, so it
runs two loop shapes in one step: transfer loops (a flat body that counts its register
down once per iteration) and the digit-pop loop of `Asm.pop`. Both have closed forms;
everything else is interpreted. `build(prog, pop_shape(B))` compiles a program to a
function over a register list.
"""

# Budge-PL: a program is a list; n > 0 increments register n, -n decrements it (stopping
# at 0), and a list [x, s1, s2, ...] repeats s1, s2, ... while register x is non-zero.
# This is fastEvaluate' from budge-pl.lhs, compiled to closures over a register list.

STEPS = [0]

def canon(node, m):
    """node with registers renamed by first appearance: equal shapes up to registers."""
    if isinstance(node, int):
        i = m.setdefault(abs(node), len(m))
        return i if node > 0 else ~i
    return tuple(canon(s, m) for s in node)

def transfer(loop):
    """(c, {r: k}) when the body is flat, decrements c once, and every other register
    only goes up or only goes down: then r changes by k per iteration, c times."""
    c, body = loop[0], loop[1:]
    if not all(isinstance(s, int) for s in body) or body.count(-c) != 1 or c in body:
        return None
    delta = {}
    for s in body:
        if abs(s) != c:
            if s in body and -s in body:
                return None  # mixed signs
            delta[abs(s)] = delta.get(abs(s), 0) + (1 if s > 0 else -1)
    return c, delta

def build(stmts, pop_shape):
    ops = [build1(s, pop_shape) for s in stmts]
    def run(R):
        for op in ops:
            op(R)
    return run

def build1(s, pop_shape):
    if isinstance(s, int):
        r = abs(s)
        if s > 0:
            def inc(R):
                STEPS[0] += 1
                R[r] += 1
            return inc
        def dec(R):
            STEPS[0] += 1
            if R[r]:
                R[r] -= 1
        return dec
    t = transfer(s)
    if t:
        c, delta = t
        ups = [(r, k) for r, k in delta.items() if k > 0]
        downs = [(r, -k) for r, k in delta.items() if k < 0]
        def move(R):
            STEPS[0] += 1
            n = R[c]
            for r, k in ups:
                R[r] += k * n
            for r, k in downs:
                R[r] = max(0, R[r] - k * n)
            R[c] = 0
        return move
    slow = build(s[1:], pop_shape)
    c = s[0]
    def loop(R):
        while R[c]:
            STEPS[0] += 1
            slow(R)
    m = {}
    if canon(s, m) != pop_shape[0]:
        return loop
    # the digit-pop loop: s counts down into d, and every B steps d wraps into q
    regs = sorted(m, key=m.get)
    sr, dr, qr, cr = (regs[i] for i in pop_shape[1])
    temps = [r for r in regs if r not in (sr, dr, qr, cr)]
    B = pop_shape[2]
    def pop(R):
        if R[dr] + R[cr] != B or R[dr] >= B or any(R[t] for t in temps):
            return loop(R)  # outside the closed form's precondition
        STEPS[0] += 1
        total = R[dr] + R[sr]
        R[qr] += total // B
        R[dr] = total % B
        R[cr] = B - R[dr]
        R[sr] = 0
    return pop

def show(prog):
    return '(' + ', '.join(str(s) if isinstance(s, int) else show(s) for s in prog) + ')'

def size(prog):
    return sum(1 if isinstance(s, int) else size(s) for s in prog)

# Macro assembler. Each macro returns a list of statements. Temporaries come from a pool
# and are zero whenever they are free; macros that run a body take it as a function, so
# the body's temporaries are allocated after (and never clash with) the macro's own.

class Asm:
    def __init__(self, B):
        self.B = B
        self.top = 0
        self.pool = []

    def reg(self):
        if self.pool:
            return self.pool.pop()
        self.top += 1
        return self.top

    def free(self, *rs):
        self.pool.extend(rs)

    def zero(self, r):
        return [[r, -r]]

    def move(self, a, b):  # b += a, a := 0
        return [[a, -a, b]]

    def copy(self, a, b):  # b += a
        t = self.reg()
        code = [[a, -a, b, t], [t, -t, a]]
        self.free(t)
        return code

    def if_else(self, c, then, els):
        n, e, t = self.reg(), self.reg(), self.reg()
        code = [e] + self.copy(c, t) + [[t, [t, -t], -e, n]]  # c ≠ 0: n := 1, e := 0
        code += [[n, -n] + then()] + [[e, -e] + els()]
        self.free(n, e, t)
        return code

    def eq(self, a, b, e):  # e := 1 if a == b else 0 (e starts at 0)
        x, y, z = self.reg(), self.reg(), self.reg()
        code = self.copy(a, x) + self.copy(b, z) + [[z, -z, -x]]  # x := a ∸ b
        code += self.copy(b, y) + self.copy(a, z) + [[z, -z, -y]]  # y := b ∸ a
        code += [e, [x, [x, -x], -e], [y, [y, -y], -e]]
        self.free(x, y, z)
        return code

    def push(self, s, d):  # s := s·B + d, d := 0
        t = self.reg()
        code = [[s, -s] + [t] * self.B, [t, -t, s]] + self.move(d, s)
        self.free(t)
        return code

    def pop_loop(self, s, d, q, c):  # d + c = B: s into d, carrying into q every B
        return [s, -s, d, -c] + self.if_else(c, lambda: [],
                                             lambda: [c] * self.B + self.zero(d) + [q])

    def pop(self, s, d):  # s ≠ 0, d = 0: d := first character, s := the rest
        q, c = self.reg(), self.reg()
        code = [c] * self.B + [self.pop_loop(s, d, q, c)]
        code += self.if_else(d, lambda: [], lambda: [d] * self.B + [-q])  # digits are 1..B
        code += self.zero(c) + self.move(q, s)
        self.free(q, c)
        return code

    def subst(self, s, v, x):  # s := s.replace(v, x), v a single character
        o, d, e, y, ch = (self.reg() for _ in range(5))
        then = lambda: self.zero(d) + self.copy(x, y) + [[y] + self.pop(y, ch) + self.push(o, ch)]
        els = lambda: self.push(o, d)
        code = [[s] + self.pop(s, d) + self.eq(d, v, e) + self.if_else(e, then, els) + self.zero(e)]
        code += [[o] + self.pop(o, d) + self.push(s, d)]  # o is s reversed; reverse it back
        self.free(o, d, e, y, ch)
        return code

def pop_shape(B):
    a = Asm(B)
    a.top = 4
    m = {}
    shape = canon(a.pop_loop(1, 2, 3, 4), m)
    return shape, [m[r] for r in (1, 2, 3, 4)], B
