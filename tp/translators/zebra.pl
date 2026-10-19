% The zebra puzzle (Einstein's riddle), pure Prolog: no arithmetic.
right_of(X, Y, [Y, X | _]).
right_of(X, Y, [_ | T]) :- right_of(X, Y, T).
next_to(X, Y, L) :- right_of(X, Y, L).
next_to(X, Y, L) :- right_of(Y, X, L).
member(X, [X | _]).
member(X, [_ | T]) :- member(X, T).

% h(Nationality, Pet, Smoke, Drink, Colour)
zebra(Houses, ZebraOwner, WaterDrinker) :-
    Houses = [h(norwegian, _, _, _, _), _, h(_, _, _, milk, _), _, _],
    member(h(englishman, _, _, _, red), Houses),
    member(h(spaniard, dog, _, _, _), Houses),
    member(h(_, _, _, coffee, green), Houses),
    member(h(ukrainian, _, _, tea, _), Houses),
    right_of(h(_, _, _, _, green), h(_, _, _, _, ivory), Houses),
    member(h(_, snails, oldgold, _, _), Houses),
    member(h(_, _, kools, _, yellow), Houses),
    next_to(h(_, _, chesterfield, _, _), h(_, fox, _, _, _), Houses),
    next_to(h(_, _, kools, _, _), h(_, horse, _, _, _), Houses),
    member(h(_, _, luckystrike, orangejuice, _), Houses),
    member(h(japanese, _, parliament, _, _), Houses),
    next_to(h(norwegian, _, _, _, _), h(_, _, _, _, blue), Houses),
    member(h(ZebraOwner, zebra, _, _, _), Houses),
    member(h(WaterDrinker, _, _, water, _), Houses).

?- zebra(Houses, Owner, Water).
