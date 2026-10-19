% Type inference for the simply typed lambda calculus, de Bruijn-free:
% terms var(X), lam(X, Body), app(F, A); types arrow(A, B) and base types.
lookup(X, [bind(X, T) | _], T).
lookup(X, [bind(Y, _) | G], T) :- different(X, Y), lookup(X, G, T).
different(x, y). different(y, x). different(x, z). different(z, x). different(y, z). different(z, y).

type(G, var(X), T) :- lookup(X, G, T).
type(G, lam(X, B), arrow(A, R)) :- type([bind(X, A) | G], B, R).
type(G, app(F, E), R) :- type(G, F, arrow(A, R)), type(G, E, A).

?- type([], lam(x, var(x)), T).                                   % I : a -> a
?- type([], lam(x, lam(y, var(x))), T).                           % K : a -> b -> a
?- type([], lam(x, lam(y, lam(z, app(app(var(x), var(z)), app(var(y), var(z)))))), T).  % S
?- type([], lam(x, app(var(x), var(x))), T).                      % self-application: no type
