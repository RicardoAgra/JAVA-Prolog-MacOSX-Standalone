%=====================================================================%
%                                                                     %
%                      Sistemas de Representação                      %
%                     de conhecimento e Raciocínio                    %
%                                                                     %
%                              Grupo 20                               %
%                            2º Exercício                             %
%                                            						  %
%					     Trabalho realizado por:					  %
%                                            						  %
%                          Ricardo Agra, 47069						  %
%						   César Cachulo, 72384						  %
%                          Luís Marques, 68691            			  %
%                           Rui Duarte, 54723 						  %
%                                            						  %
%=====================================================================%

%======================================================================
%					--	Definições Iniciais		--					  %
%======================================================================

% # NAC : Não Adicionar Caso
% # NRC : Não Remover Caso

:- set_prolog_flag( discontiguous_warnings, off ).
:- set_prolog_flag( single_var_warnings, off ).
:- set_prolog_flag( unknown, fail ).

:- op( 900, xf, '-' ).
:- op( 900, xfy, '::' ).

:- dynamic '-'/1.
:- dynamic utente/4.
:- dynamic servico/4.
:- dynamic restrito/1.
:- dynamic consulta/7.

%======================================================================
%					#	Base De Conhecimento	#					  %
%======================================================================
	% / Individualidade /
+Q :: ( findall( Q, Q, S ), tamanho( S,T ), T==0 ).
	% / Negação Forte /
not( Q ) :- nao( Q ), nao( exceto( Q )).

%==================================================================================================================
% # utente( Id, Instituição, Cidade, Descrição ).
%==================================================================================================================
	% # NRC
	% / O seu Id exista numa consulta. /
-utente( Idu, Nome, Idade, Morada ) :: ( findall( Idu, consulta( _, _, _, Idu, _, _, _ ), S ), tamanho( S, T ), T==0 ).
	% # NAC
	% / Exista uma negação quanto á idade, /
+utente( Id, Nome, Idade, Morada ) :: ( findall( Idade , -utente( Id, Nome, Idade, _ ), S ), tamanho( S, T ), T==0 ).
	% / Exista uma negação quanto á morada, ou ambas. /
+utente( Id, Nome, Idade, Morada ) :: ( findall( Morada , -utente( Id, Nome, _, Morada ), S ), tamanho( S, T ), T==0 ).
	% / O Id já se encontre em uso. /
+utente( Id, Nome, Idade, Morada ) :: ( findall( Id, utente( Id, _, _, _ ), S ), tamanho( S, T ), T==0 ).
	% / As negações fortes negam qualquer termo emparelhado /
not( utente( Id, N, I, M )) :- -utente( Id, N, I, _ ); -utente( Id, N, _, M ).

utente( 0, admin, ?, ? ).
-utente( 0, admin, 15, ? ).
-utente( 0, admin, ?, braga ).
utente( 1, ut1, 20, braga ).
utente( 2, ut2, 25, ? ).
utente( 3, ut3, ?, porto ).
-utente( 4, ut4, ?, braga ).

exceto( utente( Id, N, I, M )) :- nao( utente( Id, N, I, M )),( utente( Id, N, I, ? ); utente( Id, N, ?, M ); utente( Id, N, ?, ? )).

%==================================================================================================================
% # servico( Id, Instituição, Cidade, Descrição ).
%==================================================================================================================
	% # NRC
	% / O Id exista numa consulta. /
-servico( Ids, I, C, D ) :: ( findall( servico( Ids, _, _, _ ), consulta( _, _, _, _, Ids, _, _ ), S ), tamanho( S, T ), T==0 ). 
	% # NAC	
	% / O Id já se encontre em uso. /
+servico( Id, Instituicao, Cidade, Descricao ) :: ( findall( Id, servico( Id, _, _, _ ), S ), tamanho( S, T ), T==0 ).
+servico( Id, I, C, D ) :: ( findall( Id, restrito( servico( Id, _, _, _ )), S ), tamanho( S, T ), T==0 ).

servico( 1, hospital, braga, atendimento ).
servico( 3, test,test,test ).
restrito( servico( 2, tribunal, braga, consultadoria )).

%==================================================================================================================
% # consulta( Dia, Mês, Ano, Id-Utente, Id-Serviço, Custo, Variância ).
%==================================================================================================================
	% # NAC 
	% / O utente e o servico não se encontrem na base de conhecimento /
+consulta( D, M, A, Idu, Ids, C, V ) :- ( utente( Idu, X, Y, Z ), servico( Ids, A, B, C ) ).
	% / A variância seja maior do que o custo, ou negativa. /
+consulta( D, M, A, Idu, Ids, C, V ) :- ( C >= V ), ( V >= 0 ).
	% / Já exista um registo do utente e serviço na data em questão. /
+consulta( D, M, A, Idu, Ids, C, V ) :- ( findall( ( D, M, A, Idu, Ids ), consulta( D, M, A, Idu, Ids, _, _ ) , S ), tamanho( S, T ), T==0 ).

consulta( 1, 1, 15, 1, 1, 100, 0 ).
consulta( 2, 1, 15, 2, 1, 50, 50 ).

	% # É conhecimento perfeito se a variância for igual a 0.
consulta( D, M, A, Idu, Ids , C ) :- consulta( D, M, A, Idu, Ids, C, 0 ).
	% # É uma excecao se dado um valor X existir uma consulta com os mesmos identificadores( D,M,A,Idu,Ids ) e 
	% # o valor dado se encontrar entre o intervalo de excecao.
exceto( consulta( D, M, A, Idu, Ids, X )) :- consulta( D, M, A, Idu, Ids, C , V ), ( V \= 0 ), ( C-V =< X ), ( X =< C+V ).

%======================================================================
%					#	 Funcoes Auxiliares		#					  %
%======================================================================
%		/ Negação /
nao( Questao ) :- Questao, !, fail.
nao( Questao ).

%_________________________________________
%		/ Elemento pertence a uma lista /
pertence( E, [E|Tail] ). 
pertence( E, [Head|Tail] ) :- pertence( E, Tail ).

%_____________________________________________
%		/ Verificar uma lista de afirmacoes /
testar( [] ).
testar( [ Head|Tail] ) :- Head, testar( Tail ).

%__________________________________
%		/ Adicionar conhecimento /

adicionar( T ) :- findall( I, +T::I, L ), testar( L ), assert( T ).

%_______________________________
%		/ Apagar conhecimento /

apagar( T ) :- findall( I, -T::I, L ), testar( L ), retract( T ).

%___________________________________________
%		/ Calcular o tamanho de uma lista /
% tamanho : [elemeto], int -> { V, F }

tamanho( [], 0 ).
tamanho( [Head|Tail], X ) :- tamanho( Tail , Xx ), X is Xx + 1.

%_____________________________________
%		/ Questionar « ??( Q,R ). » /
% ?? : Q, { X } -> { V, F, D }

??( Questao, sim ) :- Questao.
%??( Questao, nao ) :- -Questao.
??( Questao, nao ) :- not( Questao ).
??( Questao, desconhecido ) :- nao( Questao ), nao( -Questao ).

