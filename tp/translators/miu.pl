% Hofstadter's MIU system (GEB, and examples/miu.btp): strings as lists of m, i, u.
% theorem(S, N): S has a derivation of at most N steps (N in Peano notation),
% so the depth-first search can't run off down one rule forever.
append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).

theorem([m, i], _).
theorem(S, s(N)) :- theorem(X, N), append(_, [i], X), append(X, [u], S).              % xI -> xIU
theorem(S, s(N)) :- theorem([m | X], N), append([m | X], X, S).                        % Mx -> Mxx
theorem(S, s(N)) :- theorem(X, N), append(P, [i, i, i | Q], X), append(P, [u | Q], S). % III -> U
theorem(S, s(N)) :- theorem(X, N), append(P, [u, u | Q], X), append(P, Q, S).          % UU ->

?- theorem([m, u, i], s(s(s(0)))).
?- theorem([m, u, i, u], s(s(s(s(0))))).
?- theorem([m, u], s(s(s(s(0))))).          % MU is not a theorem: no proof
