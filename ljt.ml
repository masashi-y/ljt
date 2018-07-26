
exception NoProof

type prop =
      Atom of string
    | Impl of prop * prop
    | Conj of prop * prop
    | Disj of prop * prop
    | Top
    | Bot

type context = prop list * prop list

type sequent = context * prop

let (=>) a b = Impl (a, b)
let (&.) a b = Conj (a, b)
let (|.) a b = Disj (a, b)
let (!) a = Atom a
let (~.) a = Impl (a, Bot)
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

type derivation =
      ZeroInf of rule * sequent
    | OneInf  of rule * derivation * sequent
    | TwoInf  of rule * derivation * derivation * sequent

let rec prop_pp out = function
    | Atom s -> output_string out s
    | Impl (x, Bot) -> Printf.fprintf out "¬ %a" prop_pp x
    | Impl (x, y) -> Printf.fprintf out "(%a ⊃ %a)" prop_pp x prop_pp y
    | Conj (x, y) -> Printf.fprintf out "(%a ∧ %a)" prop_pp x prop_pp y
    | Disj (x, y) -> Printf.fprintf out "(%a ∨ %a)" prop_pp x prop_pp y
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
    | ImplImplL  -> "⊃⊃L" in
    output_string out s

let sequent_pp out ((g, o), prop) =
    (match g @ o with
    | [] -> ()
    | p :: ps ->
        Printf.fprintf out "%a" prop_pp p;
        List.iter (Printf.fprintf out ", %a" prop_pp) ps);
    Printf.fprintf out "  ---->  %a" prop_pp prop
 
let rec derivation_pp out = function
    | ZeroInf (rule, seq) ->
        Printf.fprintf out "• %a by %a\n"
            sequent_pp seq rule_pp rule
    | OneInf (rule, deriv, seq) ->
        Printf.fprintf out "• %a by %a \n%a"
            sequent_pp seq rule_pp rule derivation_pp deriv
    | TwoInf(rule, deriv1, deriv2, seq) ->
        Printf.fprintf out "• %a by %a \n\n%a\n\n%a"
            sequent_pp seq rule_pp rule derivation_pp deriv1 derivation_pp deriv2

(* insert a proposition to context. *)
let ($$) (g, o) prop = match prop with
    (* A, A ⊃ B, P ⊃ Q ⊃ R are inserted in g *)
    | Atom _ | Impl (Atom _, _) | Impl (Impl (_, _), _) -> (prop :: g, o)
    | a -> (g, prop :: o)

(* forall P in Γ, make a pair (P, Γ\{P}). *)
let all_contexts =
    let rec aux hd = function
    | [] -> []
    | x :: xs ->
        (x, hd @ xs) :: aux (hd @ [x]) xs in
    aux []

let rec step goal = match goal with
    (* Γ => Top *)
    | context, Top -> ZeroInf (TopR, goal)
    (* Γ => A,  Γ => B  |-  Γ => A & B *)
    | context, Conj (a, b) ->
        let newgoal1 = context ===> a in
        let newgoal2 = context ===> b in
        TwoInf (ConjR, step newgoal1, step newgoal2, goal)
    (* A, Γ => B |- Γ => A ⊃ B *)
    | context, Impl (a, b) ->
        let newgoal = context $$ a ===> b in
        OneInf (ImplR, step newgoal, goal)
    (* A, B, Γ => G |- A & B, Γ => G *)
    | (g, Conj (a, b) :: o), c ->
        let newgoal = ((g, o) $$ a $$ b) ===> c in
        OneInf (ConjL, step newgoal, goal)
    (* Γ => G |- Top, Γ => G *)
    | (g, Top :: o), c ->
        let newgoal = (g, o) ===> c in
        OneInf (TopL, step newgoal, goal)
    (* ?? *)
    | (g, Bot :: o), c ->
        ZeroInf (BotL, (Bot :: g, o) ===> c)
    (* A, Γ => G    B, Γ => G |- A | B, Γ => G *)
    | (g, Disj (a, b) :: o), c ->
        let newgoal1 = (g, o) $$ a ===> c in
        let newgoal2 = (g, o) $$ b ===> c in
        TwoInf (DisjL, step newgoal1, step newgoal2, goal)
    (* A, Γ => G |- Top ⊃ A, Γ => G *)
    | (g, Impl (Top, b) :: o), c ->
        let newgoal = (g, o) $$ b ===> c in
        OneInf (TopImplL, step newgoal, goal)
    (* ?? Γ => G |- Bot ⊃ A, Γ => G *)
    | (g, Impl (Bot, b) :: o), c ->
        let newgoal = (g, o) ===> c in
        OneInf (BotImplL, step newgoal, goal)
    (* (D ⊃ E) ⊃ B, Γ => G |- (D & E) ⊃ B, Γ => G *)
    | (g, Impl (Conj (d, e), b) :: o), c ->
        let newgoal =  (g, o) $$ (d => (e => b)) ===> c in
        OneInf (ConjImplL, step newgoal, goal)
    (* D ⊃ B, E ⊃ B, Γ => G |- (D | E) ⊃ B, Γ => G *)
    | (g, Impl (Disj (d, e), b) :: o), c ->
        let newgoal = ((g, o) $$ (d => b) $$ (e => b)) ===> c in
        OneInf (DisjImplL, step newgoal, goal)
    (* Γ => A |- Γ => A | B  _or_  Γ => B |- Γ => A | B *)
    | (g, []), Disj (a, b) -> begin
        try
            OneInf (DisjL, searchSync g (Disj (a, b)), goal)
        with NoProof ->
            try
                OneInf (DisjR1, step ((g, []) ===> a), goal)
            with NoProof ->
                OneInf (DisjR2, step ((g, []) ===> b), goal)
    end
    | (g, []), c -> searchSync g c
    | _ -> failwith "step case not supposed to happen"

and searchSync g c =
    let rec aux = function
    | [] -> raise NoProof
    | ctx :: cs ->
        match eliminate (c, ctx) with
        | Some d -> d
        | None -> aux cs in
    aux (all_contexts g)

and eliminate = function
    | Atom x, (Atom y, ctx) when x = y ->
        Some (ZeroInf (Init, (Atom x :: ctx, []) ===> Atom y))
    (* B, A, Γ => G |- A ⊃ B, A, Γ => G *)
    | c, (Impl (Atom x, b), ctx) when List.mem (Atom x) ctx ->
        let goal = ((Atom x => b) :: ctx, []) ===> c in
        let newgoal = (ctx, []) $$ b ===> c in
        (try Some (OneInf (AtomImplL, step newgoal, goal))
        with NoProof -> None)
    (* E ⊃ B, D, Γ => E    B, Γ => G |- (D ⊃ E) ⊃ B, Γ => G *)
    | c, (Impl (Impl (d, e), b), ctx) ->
        let goal = (((d => e) => b) :: ctx, []) ===> c in
        let newgoal1 = (ctx, []) $$ (e => b) $$ d ===> e in
        let newgoal2 = (ctx, []) $$ b ===> c in
        (try Some (TwoInf (ImplImplL, step newgoal1, step newgoal2, goal))
        with NoProof -> None)
    | _ -> None

let prove c =
   try Some (step (([], []) ===> c))
   with NoProof -> None

let test name problem =
    Printf.printf "==========================\n%s\n%a\n" name prop_pp problem;
    match prove problem with
    | Some d -> Printf.printf "success!\n\n%a\n" derivation_pp d
    | None -> print_endline "fail\n"

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

