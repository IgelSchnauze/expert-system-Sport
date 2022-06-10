implement main

domains
    i = integer.
    s = string.
    ch = char.
    li = i*.

class facts - knowledge
    cond : (i, s). /* критерии */
    rule : (s, li).

class facts - dialog
    cond_is : (i, ch). /* номер критерии; '1' - есть, '2' - нет*/

class predicates
    choiceSport : () nondeterm.
clauses
    choiceSport() :-
        rule(X, L),
        check(L),
        stdio::write("\nНам кажется, что для вашего ребенка подойдет следующий вид спорта: ", X),
        stdio::write("\nА вы согласны с таким выбором? (1 - Да, 2 - Нет)"),
        read_true_char(C),
        C = '1',
        !.
    choiceSport() :-
        stdio::write("\nК сожалению, мы пока не знаем, какой вид спорта подходит под указанные параметры. \n"),
        stdio::write("Но можно обновить информацию в базе знаний.\n"),
        update.

class predicates
    update : () nondeterm. /* добавляет в базу информацию о новом элементе */
clauses
    update() :-
        stdio::write("\nЕсли при прохождении опроса вы подразумевали некоторый вид спорта, пожалуйста, введите его название и нажмите ENTER. "),
        stdio::write("\nВ противном случае просто нажмите ENTER"),
        stdio::write("\nВвод: "),
        S = stdio::readLine(),
        add_cond(L),
        S_len = string::length(S),
        if S_len = 0 then
            assert(rule("no_name", L)) /* добавляем вид спорта без названия*/
        else
            assert(rule(S, L)) /* добавляем вид спорта с введенным названием*/
        end if,
        file::saveUtf8(@"..\SportForKid_catalog.dba", knowledge), /* сохраняем базу знаний в файл */
        stdio::write("\nБаза знаний успешно обновлена.").

class predicates
    test_cond : (i) nondeterm.
clauses
    test_cond(H) :-
        cond_is(H, '1'),
        !. /* в базе имеется информация о наличии критерия*/
    test_cond(H) :-
        cond_is(H, '2'),
        !,
        fail. /* в базе имеется информация об отсутствии критерия */
    test_cond(H) :-
        /* в базе нет никакой информации о данном критерии, поэтому спрашиваем */
        cond(H, S),
        stdio::writef("\n%? (1 - Да, 2 - Нет)", S),
        read_true_char(A),
        assert(cond_is(H, A)),
        test_cond(H).

class predicates
    check : (li) nondeterm.
clauses
    check([H | T]) :-
        test_cond(H),
        check(T).
    check([]).

class predicates
    add_cond : (li) nondeterm anyflow. /* возвращает список критериев, имеющихся у нового элемента */
clauses
    add_cond(L) :-
        cond_is(_, '1'),
        !,
        stdio::write("\nБыли указаны следущие критерии: "),
        print_cond(1, [], L1), /* вывод имеющейся информации */
        stdio::write("\nВажно ли указать ещё что-то? (1 - Да, 2 - Нет)"),
        read_true_char(C),
        read_cond(C, L1, L).
    add_cond(L) :-
        read_cond('1', [], L).

class predicates
    print_cond : (i, li, li) nondeterm anyflow. /* добавляет в список номера критериев,
относительно которых уже были даны положит ответы */
clauses
    print_cond(H, L, L) :-
        not(cond(H, _)),
        !.
    print_cond(H, L, L1) :-
        cond_is(H, '1'),
        !,
        cond(H, T),
        H1 = H + 1,
        stdio::writef("\n%", T),
        print_cond(H1, [H | L], L1).
    print_cond(H, L, L1) :-
        H1 = H + 1,
        print_cond(H1, L, L1).

class predicates
    read_cond : (ch, li, li) anyflow. /* добавляет в список номера критериев, о которых еще не спрашивалось */
clauses
    read_cond('1', L, L2) :-
        ex_cond(1, L, L1, N),
        new_cond(N, L1, L2),
        !.
    read_cond(_, L, L) :-
        !.

class predicates
    ex_cond : (i, li, li, i) nondeterm anyflow. /* добавляет в список номера имеющихся в базе критериев*/
clauses
    ex_cond(N, L, L, N) :-
        not(cond(N, _)),
        !.
    ex_cond(N, L, L1, N2) :-
        cond_is(N, _),
        !,
        N1 = N + 1,
        ex_cond(N1, L, L1, N2).
    ex_cond(N, L, L1, N2) :-
        cond(N, S),
        stdio::writef("\n%? (1 - Да, 2 - Нет)", S),
        read_true_char(A),
        wr_cond(A, N, L, L2),
        N1 = N + 1,
        ex_cond(N1, L2, L1, N2).

class predicates
    wr_cond : (ch, i, li, li) nondeterm anyflow.
clauses
    wr_cond('1', N, L, [N | L]) :-
        !.
    wr_cond('2', _, L, L) :-
        !.

class predicates
    new_cond : (i, li, li) anyflow. /* добавляет номера и описания новых критериев в базу знаний */
clauses
    new_cond(N, L, L1) :-
        stdio::write("\nВажны ли еще какие-либо критерии? (1 - Да, 2- Нет)"),
        read_true_char(A),
        A = '1',
        !,
        stdio::write("\nТогда напишите дополнительный параметр: "),
        S = stdio::readLine(),
        assert(cond(N, S)), /* добавление нового свойства в базу знаний */
        N1 = N + 1,
        new_cond(N1, [N | L], L1).
    new_cond(_, L, L).

class predicates
    read_true_char : (ch [out]) determ. /* читает символ с консоли, пока он не равен '1' или '2'*/
clauses
    read_true_char(C) :-
        Cstr = stdio::readLine(),
        /*string::frontchar(Cstr, C1, _),*/
        C1 = string::subChar(Cstr, 0),
        test(C1, C).

class predicates
    test : (ch, ch [out]) determ.
clauses
    test(C, C) :-
        '1' <= C,
        C <= '2',
        '1' <= C,
        !.
    test(_, C) :-
        stdio::write("Ошибка ввода! Нажмите 1 или 2. \n"),
        Cstr = stdio::readLine(),
        /*string::frontchar(Cstr, C1, _),*/
        C1 = string::subChar(Cstr, 0),
        test(C1, C).

clauses
    run() :-
        console::init(stream::unicode),
        /*console::init(),*/
        file::consult(@"..\SportForKid_catalog.dba", knowledge), /*  загружаем инфу из базы знаний */
        stdio::write("\nДанная ЭС может помочь выбрать наиболее подходящий вид спорта для вашего ребенка.\n"),
        stdio::write("Для этого вам необходимо ответить на несколько вопросов о вашем ребенке и о предпочитетельных критериях спортивных занятий.\n"),
        stdio::write("После каждого ввода ответа нажмите ENTER.\n"),
        stdio::write("***Обращаем ваше внимание на то, что результаты носят чисто рекомендательный характер.\n"),
        choiceSport, /* попытка определить */
        retractFactDB(dialog), /* очищаем текущую информацию */
        retractFactDB(knowledge), /* удаляем инфу из базу данных  */
        stdio::write("\n\nПопробуем ещё раз? (1 - Да, 2 - Нет)"),
        read_true_char(C),
        C = '1',
        !,
        run.
    run() :-
        stdio::write("\nНадеемся, что смогли вам помочь!"),
        _ = stdio::readChar().

end implement main

goal
    mainExe::run(main::run).
    /*console::runUtf8(main::run).*/
