
exception NoProof

type var = string

type term =
      Var of var
    | Con of string

type prop =
      Atom of string * term list
    | Impl of prop * prop
    | Conj of prop * prop
    | Disj of prop * prop
    | Forall of var * prop
    | Exists of var * prop
    | Top
    | Bot


type context = prop list * prop list

type sequent = context * prop

let (=>) a b = Impl (a, b)
let (&.) a b = Conj (a, b)
let (|.) a b = Disj (a, b)
let (?.) a = Var a
let (??) a = Con a
let (!.) a = Atom (a, [])
let (!!) a b = Atom (a, b)
let (~.) a = Impl (a, Bot)
let forall x p = Forall (x, p)
let exists x p = Exists (x, p)
let (===>) context prop = (context, prop)

type rule =
      ConjR
    | ConjL
    | TopR
    | ImplR
    | ImplL
    | Init
    | DisjL
    | DisjR1
    | DisjR2
    | TopL
    | BotL
    | AtomImplL
    | ConjImplL
    | TopImplL
    | DisjImplL
    | BotImplL
    | ImplImplL
    | ForallL
    | ForallR
    | ExistsL
    | ExistsR
    | ForallImplL
    | ExistsImplL

type derivation =
      ZeroInf of rule * sequent
    | OneInf  of rule * derivation * sequent
    | TwoInf  of rule * derivation * derivation * sequent

let term_pp out = function
    | Var s | Con s -> output_string out s

let terms_pp out = function
    | [] -> ()
    | x :: xs ->
        Printf.fprintf out "%a" term_pp x;
        List.iter (Printf.fprintf out ", %a" term_pp) xs

let rec prop_pp out = function
    | Atom (x, []) -> output_string out x
    | Atom (x, y) -> Printf.fprintf out "%s(%a)" x terms_pp y
    | Impl (x, Bot) -> Printf.fprintf out "¬ %a" prop_pp x
    | Impl (x, y) -> Printf.fprintf out "(%a ⊃ %a)" prop_pp x prop_pp y
    | Conj (x, y) -> Printf.fprintf out "(%a ∧ %a)" prop_pp x prop_pp y
    | Disj (x, y) -> Printf.fprintf out "(%a ∨ %a)" prop_pp x prop_pp y
    | Forall (x, y) -> Printf.fprintf out "∀ %s.%a" x prop_pp y
    | Exists (x, y) -> Printf.fprintf out "∃ %s.%a" x prop_pp y
    | Top -> output_string out "⊤"
    | Bot -> output_string out "⊥"

let rule_pp out rule =
    let s = match rule with
    | ConjR      -> "∧R"
    | ConjL      -> "∧L"
    | TopR       -> "⊤R"
    | ImplR      -> "⊃R"
    | Init       -> "init"
    | DisjL      -> "∨L"
    | DisjR1     -> "∨R_1"
    | DisjR2     -> "∨R_2"
    | TopL       -> "⊤L"
    | BotL       -> "⊥L"
    | ImplL      -> "⊃L"
    | AtomImplL  -> "P⊃L"
    | ConjImplL  -> "∧⊃L"
    | TopImplL   -> "⊤⊃L"
    | DisjImplL  -> "∨⊃L"
    | BotImplL   -> "⊥⊃L"
    | ImplImplL  -> "⊃⊃L"
    | ForallL    ->  "∀L"
    | ForallR    ->  "∀R"
    | ExistsL    ->  "∃L"
    | ExistsR    ->  "∃R"
    | ForallImplL -> "∀⊃L"
    | ExistsImplL -> "∃⊃R"
    in
    output_string out s

let sequent_pp out ((g, o), prop) =
    (match g @ o with
    | [] -> ()
    | p :: ps ->
        Printf.fprintf out "%a" prop_pp p;
        List.iter (Printf.fprintf out ", %a" prop_pp) ps);
    Printf.fprintf out "  ---->  %a" prop_pp prop
 
let rec derivation_pp out deriv =
    let rec aux out (depth, deriv) = match deriv with
        | ZeroInf (rule, seq) ->
            Printf.fprintf out "%*s• %a by %a\n"
                depth " " sequent_pp seq rule_pp rule
        | OneInf (rule, deriv, seq) ->
            Printf.fprintf out "%*s• %a by %a \n%a"
                depth " " sequent_pp seq rule_pp rule aux (depth + 1, deriv)
        | TwoInf(rule, deriv1, deriv2, seq) ->
            Printf.fprintf out "%*s• %a by %a \n\n%a\n%a"
                depth " " sequent_pp seq rule_pp rule aux
                (depth + 1, deriv1) aux (depth + 1, deriv2) in
    aux out (0, deriv)


let new_var () =
    let index =
        let i = ref 0 in
        fun () -> incr i;
        !i in
    Var ("__u" ^ string_of_int (index ()))

let rec unique = function
    | [] -> []
    | x :: xs ->
        x :: unique (List.filter ((<>)x) xs)

let is_constant = function
    | Con _ -> true
    | _ -> false

let all_constants prop =
    let rec aux = function
    | Atom (_, y) -> List.filter is_constant y
    | Impl (x, y) | Conj (x, y) | Disj (x, y) -> aux x @ aux y
    | Forall (x, prop) | Exists (x, prop) ->
           List.filter (fun y -> Var x != y) (aux prop)
    | _ -> [] in
    unique (aux prop)

let rec subst var value = function
    | Atom (x, terms) ->
            let terms = List.map (fun y ->
                if y = Var var
                then value
                else y)  terms in
            Atom (x, terms)
    | Impl (x, y) -> subst var value x => subst var value y
    | Conj (x, y) -> subst var value x &. subst var value y
    | Disj (x, y) -> subst var value x |. subst var value y
    | Forall (x, y) as prop when x = var -> prop
    | Exists (x, y) as prop when x = var -> prop
    | Forall (x, y) -> forall x (subst var value y)
    | Exists (x, y) -> exists x (subst var value y)
    | Top -> Top
    | Bot -> Bot

(* insert a proposition to context. *)
let ($$) (g, o) prop = match prop with
    (* A, A ⊃ B, P ⊃ Q ⊃ R, ∀ x. P(x) ⊃ Q are inserted in g *)
    | Atom _
    | Impl (Atom _, _)
    | Impl (Impl (_, _), _)
    | Impl (Forall (_, _), _)
    | Impl (Exists (_, _), _) -> (prop :: g, o)
    | a -> (g, prop :: o)

(* forall P in Γ, make a pair (P, Γ\{P}). *)
let all_contexts =
    let rec aux hd = function
    | [] -> []
    | x :: xs ->
        (x, hd @ xs) :: aux (hd @ [x]) xs in
    aux []

(* try `f x` forall `x` in a list, until
   it does not raise NoProof.  *)
let rec fold_try f = function
    | [] -> raise NoProof
    | x :: xs ->
        try f x
        with NoProof ->
            fold_try f xs

let rec step depth cons goal =
    let step' = step depth cons in
    match goal with
    (* Γ => Top *)
    | context, Top -> ZeroInf (TopR, goal)
    (* Γ => A,  Γ => B
      ------------------(=>&)
       Γ => A & B     *)
    | context, Conj (a, b) ->
        let newgoal1 = context ===> a in
        let newgoal2 = context ===> b in
        TwoInf (ConjR, step' newgoal1, step' newgoal2, goal)
    (*  A, Γ => B
      ----------------(=>⊃)
        Γ => A ⊃ B   *)
    | context, Impl (a, b) ->
        let newgoal = context $$ a ===> b in
        OneInf (ImplR, step' newgoal, goal)
    (*     Γ => A(y) 
      -------------------(=>∀)
         Γ => ∀ x. A(x)   *)
    | context, Forall (a, b) ->
        let newvar = new_var () in
        let newgoal = context ===> subst a newvar b in
        OneInf (ForallR, step depth (newvar :: cons) newgoal, goal)
    (*  A, B, Γ => G
      ----------------(&=>)
        A & B, Γ => G  *)
    | (g, Conj (a, b) :: o), c ->
        let newgoal = ((g, o) $$ a $$ b) ===> c in
        OneInf (ConjL, step' newgoal, goal)
    (*    Γ => G
      ---------------(??)
       Top, Γ => G  *)
    | (g, Top :: o), c ->
        let newgoal = (g, o) ===> c in
        OneInf (TopL, step' newgoal, goal)
    (* ?? *)
    | (g, Bot :: o), c ->
        ZeroInf (BotL, (Bot :: g, o) ===> c)
    (*  A, Γ => G    B, Γ => G
      ---------------------------(|=>)
            A | B, Γ => G       *)
    | (g, Disj (a, b) :: o), c ->
        let newgoal1 = (g, o) $$ a ===> c in
        let newgoal2 = (g, o) $$ b ===> c in
        TwoInf (DisjL, step' newgoal1, step' newgoal2, goal)
    (*     A, Γ => G
       Top ⊃ A, Γ => G   *)
    | (g, Impl (Top, b) :: o), c ->
        let newgoal = (g, o) $$ b ===> c in
        OneInf (TopImplL, step' newgoal, goal)
    (*       Γ => G
      --------------------(⊥=>)
        Bot ⊃ A, Γ => G  *)
    | (g, Impl (Bot, b) :: o), c ->
        let newgoal = (g, o) ===> c in
        OneInf (BotImplL, step' newgoal, goal)
    (*   (D ⊃ E) ⊃ B, Γ => G
      --------------------------(&=>)
         (D & E) ⊃ B, Γ => G   *)
    | (g, Impl (Conj (d, e), b) :: o), c ->
        let newgoal =  (g, o) $$ (d => (e => b)) ===> c in
        OneInf (ConjImplL, step' newgoal, goal)
    (*   D ⊃ B, E ⊃ B, Γ => G
      --------------------------(|⊃=>)
         (D | E) ⊃ B, Γ => G   *)
    | (g, Impl (Disj (d, e), b) :: o), c ->
        let newgoal = ((g, o) $$ (d => b) $$ (e => b)) ===> c in
        OneInf (DisjImplL, step' newgoal, goal)
    | (g, Forall (a, b) :: o), c ->
    (*     Γ, ∀ x. A(x), A(t) => E
      ------------------------------(∀=>)
            Γ, ∀ x. A(x) => E        *)
        let newcontext = List.fold_left
            (fun ctx t -> ctx $$ subst a t b) (g, o) cons in
        let newgoal = newcontext ===> c in
        OneInf (ForallL, step' newgoal, goal)
    (*       Γ, A(y) => E
      -------------------------(∃=>)
         Γ, ∃ x. A(x) => E   *)
    | (g, Exists (a, b) :: o), c ->
        let newvar = new_var () in
        let newgoal = (g, o) ===> subst a newvar b in
        OneInf (ExistsL, step depth (newvar :: cons) newgoal, goal)
    (*     Γ => A                Γ => B
      --------------(=>|) or ---------------(=>|)
         Γ => A | B            Γ => A | B    *)
    | (g, []), Disj (a, b) -> begin
        try
            OneInf (DisjL, searchSync depth cons g (Disj (a, b)), goal)
        with NoProof ->
            try
                OneInf (DisjR1, step' ((g, []) ===> a), goal)
            with NoProof ->
                OneInf (DisjR2, step' ((g, []) ===> b), goal)
    end
    (*     Γ => A(t)
      -------------------(=>∃)
         Γ => ∃ x. A(x)   *)
    | (g, []), Exists (a, b) -> begin
        try
            OneInf (ExistsR, searchSync depth cons g (Exists (a, b)), goal)
        with NoProof ->
            fold_try (fun t ->
                let newgoal = (g, []) ===> subst a t b in
                OneInf (DisjR2, step' newgoal, goal)) cons
    end
    | (g, []), c -> searchSync depth cons g c
    | _ -> failwith "step case not supposed to happen"

and searchSync depth cons g c =
    let rec aux = function
    | [] -> raise NoProof
    | ctx :: cs ->
        match eliminate depth cons (c, ctx) with
        | Some d -> d
        | None -> aux cs in
    aux (all_contexts g)

and eliminate depth cons =
    let step' = step depth cons in function
    (* ----------------(axiom)
          Γ, A => A   *)
    | Atom (_, _) as x, (Atom (_, _) as y, ctx) when x = y ->
        Some (ZeroInf (Init, (x :: ctx, []) ===> y))
    (*    B, A, Γ => G
      ---------------------(Atom⊃=>)
       A ⊃ B, A, Γ => G   *)
    | c, (Impl (Atom (x, []), b), ctx) when List.mem (Atom (x, [])) ctx ->
        let goal = ((Atom (x, []) => b) :: ctx, []) ===> c in
        let newgoal = (ctx, []) $$ b ===> c in
        (try Some (OneInf (AtomImplL, step' newgoal, goal))
        with NoProof -> None)
    (*  E ⊃ B, D, Γ => E    B, Γ => G
      ---------------------------------(⊃⊃=>)
            (D ⊃ E) ⊃ B, Γ => G      *)
    | c, (Impl (Impl (d, e), b), ctx) ->
        let goal = (((d => e) => b) :: ctx, []) ===> c in
        let newgoal1 = (ctx, []) $$ (e => b) $$ d ===> e in
        let newgoal2 = (ctx, []) $$ b ===> c in
        (try Some (TwoInf (ImplImplL, step' newgoal1, step' newgoal2, goal))
        with NoProof -> None)
    (*     Γ, ∀ x. A(x) ⊃ B => ∀ x. A(x)    Γ, B => E
      -----------------------------------------------------(∀⊃=>)
                      Γ, ∀ x. A(x) ⊃ B => E              *)
    | c, (Impl (Forall (d, e), b), ctx) ->
        (if depth <= 0 then raise NoProof);
        let goal = ((forall d e => b) :: ctx, []) ===> c in
        let newgoal1 = (ctx, []) $$ (forall d e => b) ===> forall d e in
        let newgoal2 = (ctx, []) $$ b ===> c in
        (try Some (TwoInf (ForallImplL, step (depth - 1) cons newgoal1, step (depth - 1) cons newgoal2, goal))
        with NoProof -> None)
    (*     Γ, ∀ x. (A(x) ⊃ B) => ∀ x. A(x)    Γ, B => E
      -----------------------------------------------------(∃⊃=>)
                      Γ, ∃ x. A(x) ⊃ B => E              *)
    | c, (Impl (Exists (d, e), b), ctx) ->
        let goal = ((exists d e => b) :: ctx, []) ===> c in
        let newgoal1 = (ctx, []) $$ (forall d (e => b)) ===> forall d e in
        let newgoal2 = (ctx, []) $$ b ===> c in
        (try Some (TwoInf (ExistsImplL, step' newgoal1, step' newgoal2, goal))
        with NoProof -> None)
    | _ -> None

let prove c =
    let max_depth = 100 in
    let cons = match all_constants c with
        | [] -> [Con "t"] (* dummy constant *)
        | cs -> cs in
    try Some (step max_depth cons (([], []) ===> c))
    with NoProof -> None


let test name problem =
    Printf.printf "==========================\n%s\n%a\n" name prop_pp problem;
    match prove problem with
    | Some d -> Printf.printf "success!\n\n%a\n" derivation_pp d
    | None -> print_endline "fail\n"

let () =
    let example = (forall "x" ((!!"foo"[?."x"; ??"hanako"]))) => (!!"foo"[??"taro"; ??"hanako"]) in
    let example2 = (forall "x" ((!!"tea"[?."x"]) |. (!!"coffee"[?."x"])))
    => ((forall "x" ((!!"woman"[?."x"]) => (exists "y" (((!!"tea"[?."y"]) |. (!!"coffee"[?."y"])) &. (!!"order"[?."x"; ?."y"])))))
    => ((exists "x" ((!!"woman"[?."x"]) &. (~.(exists "y" ((!!"coffee"[?."y"]) &. (!!"order"[?."x"; ?."y"]))))))
    => (exists "x" ((!!"woman"[?."x"]) &. (exists "y" ((!!"tea"[?."y"]) &. (!!"order"[?."x"; ?."y"]))))))) in
    let example3 = (forall "x" ((!!"tea"[?."x"]) |. (!!"coffee"[?."x"])))
    => (forall "x" ((!!"tea"[?."x"]) |. (!!"coffee"[?."x"]))) in
    let example4 = (exists "x" (~.(!!"P"[?."x"]))) => (~.(forall "x" (!!"P"[?."x"]))) in
    test "forall" example;
    test "ccg2lambda" example2;
    test "ccg2lambda2" example3;
    test "test" example4;

(*
let a = !"A"
let b = !"B"
let c = !"C"
let d = !"D"
let e = !"E"

let () =
test "simple" (a => (b => a));
test "simple2" (((a => b) => c) => ((a => b) => c));
test "simple3" ((((a => b) => c) => d) => (c => d));
test "conjAssoc" ((a &. (b &. c)) => ((a &. b) &. c));
test "conjComm"  ((a &. b) => (b &. a));
test "implTrans" ((a => b) => ((b => c) => (a => c)));
test "disjComm"  ((a |. b) => (b |. a));
test "random1" ((a |. b => c) => ((a => c) &. (b => c)));
test "random2" (((a |. b |. c) => d) => ((a => d) &. (b => d) &. (c => d)));
test "random3" (((a => b) => c) => (d => (d |. d)));
test "curry" ((a &. b => c) => (a => (b => c)));
test "uncurry" ((a => (b => c)) => ((a &. b) => c));
test "projConjL" ((a &. b) => a);
test "projConjR" ((a &. b) => b);
test "impFst" (a => (b => a));
test "impSnd" (a => (b => a));
test "flip" ((a => (b => c)) => (b => (a => c)));
test "tripleNeg" (~.(~.(~.a)) => ~.a);
test "long" ((((a => b) => c) => d) => (((a => b) => c) => d));
test "long2" ((((((a => b) => c) => d) => e) => Bot) => (((((a => b) => c) => d) => e) => Bot));
test "verylong" ((((((a => b) => c) => d) => e) => Bot) => ((((((a => b) => c) => d) => e) => Bot) |. (((((a => b) => c) => d) => e) => Bot)));
test "glivenko" (((((a => b) => a) => a) => Bot) => Bot);
test "duality1" (((a => Bot) |. (b => Bot)) => (a &. b => Bot));
test "duality2" (((Top => Bot) => Bot) &. (Bot => (Top => Bot)));
test "exFalsoQuodlibet" (Bot => a)

*)
