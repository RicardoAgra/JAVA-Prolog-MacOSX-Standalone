
:- use_module(library(clpfd)).

benches([]).
benches([Goal|Goals]) :-
	format(user_error, 'Calling goal: ~w\n',[Goal]),
	statistics(runtime,_),
	call(Goal), !,
	statistics(runtime,[_,T]),
	format(user_error, 'Runtime: ~d\n',[T]),
	fd_statistics,
	nl(user_error),
	benches(Goals).

lips(indexical, N) :-
	M is -N,
	domain([X,Y], M, N),
	X #< Y,
	Y #< X.
lips(global, N) :-
	M is -N,
	domain([X,Y], M, N),
	clpfd:le_iff(X, Y, 0),
	clpfd:le_iff(Y, X, 0).
lips(_, _).


