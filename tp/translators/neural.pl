% A neural network learns XOR: two sigmoid neurons feed an output neuron, and
% backpropagation trains the weights.
%
% The queries check one epoch of training from the starting weights (four
% updates, each a forward pass and backpropagation), and that the weights after
% 3000 epochs compute XOR. The 3000 epochs are only the search for those weights
% (in floating point, SWI-Prolog runs train(3000, ...) in 0.1 s); what is checked
% is that they work.
%
% Arithmetic is prolog2btp's: numbers with four decimals, products and
% quotients cut to four, exp from a table (see its README).

% The starting weights, and the weights after 3000 epochs (to four decimals)
start([[0.2, 0.4, 0.1], [-0.3, -0.2, 0.2]], [0.4, 0.7, -0.3]).
trained([[-6.517, -6.5232, 9.7425], [-8.069, -8.1375, 3.5464]], [15.2375, -15.5699, -7.3163]).

data([ex(0, 0, 0), ex(0, 1, 1), ex(1, 0, 1), ex(1, 1, 0)]).

% neuron(Ws, Xs, H): H = sigmoid(W1 X1 + ... + Wn Xn)
neuron(Ws, Xs, H) :- dot(Ws, Xs, Z), H is 1 / (1 + exp(-Z)).
dot([], [], 0).
dot([W|Ws], [X|Xs], Z) :- dot(Ws, Xs, Z0), Z is W * X + Z0.

% hidden(W, Xs, Hs): one neuron per row of W, then the bias input 1
hidden([], _, [1]).
hidden([Row|Rows], Xs, [H|Hs]) :- neuron(Row, Xs, H), hidden(Rows, Xs, Hs).

% step(W0, V0, Example, W, V): predict, then adjust the weights
step(W0, V0, ex(X, Y, Target), W, V) :-
    hidden(W0, [X, Y, 1], H),
    neuron(V0, H, P), Error is Target - P,
    backprop(W0, V0, H, Error, [X, Y, 1], W),
    add_scaled(V0, Error, H, V).

% For each hidden neuron j, delta = error * v[j] * h[j] * (1 - h[j]), then
% w[j][i] += delta * inputs[i]. It reads the old output weights V0.
backprop([], _, _, _, _, []).
backprop([Row|Rows], [Vj|Vs], [Hj|Hs], Error, Inputs, [Row1|Rows1]) :-
    Delta is Error * Vj * Hj * (1 - Hj),
    add_scaled(Row, Delta, Inputs, Row1),
    backprop(Rows, Vs, Hs, Error, Inputs, Rows1).

% add_scaled(Ws, D, Xs, Ws1): Ws1 = Ws + D * Xs, element by element
add_scaled([], _, [], []).
add_scaled([W|Ws], D, [X|Xs], [W1|Ws1]) :- W1 is W + D * X, add_scaled(Ws, D, Xs, Ws1).

epoch(W, V, [], W, V).
epoch(W0, V0, [E|Es], W, V) :- step(W0, V0, E, W1, V1), epoch(W1, V1, Es, W, V).

train(0, W, V, W, V).
train(N, W0, V0, W, V) :-
    N > 0, data(D), epoch(W0, V0, D, W1, V1), M is N - 1, train(M, W1, V1, W, V).

% predict(W, V, Examples, Rs): the rounded output for each example
predict(_, _, [], []).
predict(W, V, [ex(X, Y, _)|Es], [R|Rs]) :-
    hidden(W, [X, Y, 1], H), neuron(V, H, P), rounded(P, R), predict(W, V, Es, Rs).
rounded(P, 1) :- P >= 0.5.
rounded(P, 0) :- P < 0.5.

% One epoch. In floating point (SWI-Prolog) it gives w = [[0.1321, 0.298, -0.0097],
% [-0.3946, -0.3021, 0.0687]], v = [0.2128, 0.5343, -0.5643]; this is within 0.0002
?- start(W0, V0), train(1, W0, V0, W, V).
?- trained(W, V), data(D), predict(W, V, D, [0, 1, 1, 0]).
