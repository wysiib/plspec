:- use_module(library(option)).
:- use_module(library(plunit)).
:- use_module(abs_int,[abs_int/2, abs_int/3]).
:- use_module(imp_int,[impl_int/1,impl_int/2]).
:- use_module(fileProcessor,[getOptions/1,set_loglevel/1,loglevel/1]).
%:- [parser,abs_int,imp_int,strength_reduction,constant_folding,fileProcessor,logger].

fileNames(Names) :-
    Names = ["APL/endless_for",
             "APL/endless_while",
             "APL/everything",
             "APL/for_print",
             "APL/int_division",
             "APL/print_add",
             "APL/print_if_less_ten",
             "APL/print_if_less_ten_else_print_ten",
             "APL/x_change",
             "APL/while",
             "APL/while_folding",
             "APL/CF/constantfolding",
             "APL/CF/if_folding",
             "APL/CF/loop_folding",
             "APL/SR/reduction_test",
             "APL/SR/shift"].
             
fileName(Name) :-
    fileNames(Names),
    member(Name,Names).
             
fileNameWithoutEndless(Name) :-
    fileNames(Names),
    member(Name,Names),
     Name \= "APL/endless_for",
    Name \= "APL/endless_while".



    
:- begin_tests(load).
% Testet einige Beispieldatein. Dauert lange und funktioniert nur, wenn alle oben genannten Datein vorhanden sind
    
test(abs_int,[forall(fileName(Name)),setup(set_loglevel(nothing)),cleanup(set_loglevel(error))]) :-
    string_concat(Name,".apl",APL),
    string_concat(Name,".bapl",BAPL),
    abs_int(APL,Res),
    abs_int(APL,Res,[cf(true)]),
    abs_int(APL,Res,[sr(true)]),
    abs_int(APL,Res,[cf(true),sr(true)]),
    abs_int(BAPL,Res).
    
test(imp_int,[forall(fileNameWithoutEndless(Name)),setup(set_loglevel(nothing)),cleanup(set_loglevel(error))]) :-
    Name \= "APL/endless_for",
    Name \= "APL/endless_while",
     string_concat(Name,".apl",APL),
    string_concat(Name,".bapl",BAPL),
    impl_int(APL),
    impl_int(APL,[cf(true)]),
    impl_int(APL,[sr(true)]),
    impl_int(APL,[cf(true),sr(true)]),
    impl_int(BAPL).
:- end_tests(load).