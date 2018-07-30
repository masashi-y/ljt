(* 証明が行き詰まったときに投げる例外 *)
exception NoProof

(* 論理式(命題; proposition)の定義 *)
type prop =
      Atom of string
    | Impl of prop * prop
    | Conj of prop * prop
    | Disj of prop * prop
    | Bot

(* いわゆるΓ *)
type context =
    prop list (* positive: positive (synchronous) phaseに使うコンテキスト *)
  * prop list (* negative: negative (asynchronous) phaseに使うコンテキスト *)

(* シーケント context => prop *)
type sequent = context * prop

(* 簡単な記法 *)
let (=>) a b = Impl (a, b)
let (&.) a b = Conj (a, b)
let (|.) a b = Disj (a, b)
let (!) a = Atom a
let (~.) a = Impl (a, Bot)
let (===>) context prop = (context, prop)

(* 公理 & 推論規則 *)
type rule =
      ConjR      (* ∧右     *)
    | ConjL      (* ∧左     *)
    | ImplR      (* ⊃右     *)
    | ImplL      (* ⊃左     *)
    | Init       (* axiom   *)
    | DisjL      (* ∨左     *)
    | DisjR1     (* ∨右_1   *)
    | DisjR2     (* ∨右_2   *)
    | BotL       (* ⊥左     *)
    | AtomImplL  (* Atom⊃左 *)
    | ConjImplL  (* ∧⊃左    *)
    | DisjImplL  (* ∨⊃左    *)
    | BotImplL   (* ⊥⊃左    *)
    | ImplImplL  (* ⊃⊃左    *)

(* 導出 (シーケントの木) *)
type derivation =
    (* 規則(rule) を適用してsequentを導出
                (なし)
     --------------------------(rule)
               sequent                 *)
      ZeroInf of rule * sequent
    (*        derivation
     --------------------------(rule)
               sequent                 *)
    | OneInf  of rule * derivation * sequent
    (* derivation   derivation
     --------------------------(rule)
               sequent                 *)
    | TwoInf  of rule * derivation * derivation * sequent

(* propのプリント関数 *)
(* 使い方: Printf.printf "%a" prop_pp (And (Atom "x", Atom "y")) *)
let rec prop_pp out = function
    | Atom s -> output_string out s
    | Impl (x, Bot) -> Printf.fprintf out "¬ %a" prop_pp x
    | Impl (x, y) -> Printf.fprintf out "(%a ⊃ %a)" prop_pp x prop_pp y
    | Conj (x, y) -> Printf.fprintf out "(%a ∧ %a)" prop_pp x prop_pp y
    | Disj (x, y) -> Printf.fprintf out "(%a ∨ %a)" prop_pp x prop_pp y
    | Bot -> output_string out "⊥"

(* ruleのプリント関数 *)
let rule_pp out rule =
    let s = match rule with
    | ConjR      -> "∧R"
    | ConjL      -> "∧L"
    | ImplR      -> "⊃R"
    | Init       -> "init"
    | DisjL      -> "∨L"
    | DisjR1     -> "∨R_1"
    | DisjR2     -> "∨R_2"
    | BotL       -> "⊥L"
    | ImplL      -> "⊃L"
    | AtomImplL  -> "P⊃L"
    | ConjImplL  -> "∧⊃L"
    | DisjImplL  -> "∨⊃L"
    | BotImplL   -> "⊥⊃L"
    | ImplImplL  -> "⊃⊃L"
    output_string out 

(* sequentのプリント関数 *)
let sequent_pp out ((pos, neg), prop) =
    (match pos @ neg with
    | [] -> ()
    | p :: ps ->
        Printf.fprintf out "%a" prop_pp p;
        List.iter (Printf.fprintf out ", %a" prop_pp) ps);
    Printf.fprintf out "  ---->  %a" prop_pp prop
 
(* derivationのプリント関数 *)
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


(* 文脈((pos, neg))にpropを挿入 *)
let ($$) : context -> prop -> context =
    fun (pos, neg) prop -> match prop with
    (* A, A ⊃ B, P ⊃ Q ⊃ Rはposに挿入 *)
    | Atom _
    | Impl (Atom _, _)
    | Impl (Impl (_, _), _) -> (prop :: pos, neg)
    (* それ以外はnegに挿入 *)
    | a -> (pos, prop :: neg)

(* (lst : prop list) のすべてのpropについて(prop, lst\{prop}) *)
let all_contexts : prop list -> (prop * prop list) list =
    let rec aux hd = function
    | [] -> []
    | x :: xs ->
        (x, hd @ xs) :: aux (hd @ [x]) xs in
    aux []

(* メインの定理証明を行う関数
   証明木を下から再帰的に作る
   newsequent1      newsequent2
-------------------------------------(規則)
  sequent : (context ===> goal)     *)
let rec step : sequent -> derivation =
    fun sequent -> match sequent with
    (*  Γ => A,  Γ => B
      ------------------(=>&)
          Γ => A & B    *)
    | context, Conj (a, b) ->
        let newsequent1 = context ===> a in
        let newsequent2 = context ===> b in
        TwoInf (ConjR, step newsequent1, step newsequent2, sequent)
    (*   A, Γ => B
      -----------------(=>⊃)
        Γ => A ⊃ B   *)
    | context, Impl (a, b) ->
        let newsequent = (context $$ a) ===> b in
        OneInf (ImplR, step newsequent, sequent)
    (*  A, B, Γ => G
      -----------------(&=>)
        A & B, Γ => G  *)
    | (pos, Conj (a, b) :: neg), goal ->
        let newsequent = ((pos, neg) $$ a $$ b) ===> goal in
        OneInf (ConjL, step newsequent, sequent)
    (*   ⊥, Γ => G
      ---------------(??)
         ⊥, Γ => G
       ⊥をnegからposに移すだけ *)
    | (pos, Bot :: neg), goal ->
        ZeroInf (BotL, (Bot :: pos, neg) ===> goal)
    (*  A, Γ => G    B, Γ => G
      ---------------------------(|=>)
            A | B, Γ => G       *)
    | (pos, Disj (a, b) :: neg), goal ->
        let newsequent1 = (pos, neg) $$ a ===> goal in
        let newsequent2 = (pos, neg) $$ b ===> goal in
        TwoInf (DisjL, step newsequent1, step newsequent2, sequent)
    (*       Γ => G                   (テキストでは)
      --------------------(⊥=>)    ------------------(⊥=>)
        ⊥ ⊃ A, Γ => G                   ⊥, Γ => A       *)
    | (pos, Impl (Bot, a) :: neg), goal ->
        let newsequent = (pos, neg) ===> goal in
        OneInf (BotImplL, step newsequent, sequent)
    (*   (D ⊃ E) ⊃ B, Γ => G
      --------------------------(&=>)
         (D & E) ⊃ B, Γ => G   *)
    | (pos, Impl (Conj (d, e), b) :: neg), goal ->
        let newsequent =  (pos, neg) $$ (d => (e => b)) ===> goal in
        OneInf (ConjImplL, step newsequent, sequent)
    (*   D ⊃ B, E ⊃ B, Γ => G
      --------------------------(|⊃=>)
         (D | E) ⊃ B, Γ => G   *)
    | (pos, Impl (Disj (d, e), b) :: neg), goal ->
        let newsequent = ((pos, neg) $$ (d => b) $$ (e => b)) ===> goal in
        OneInf (DisjImplL, step newsequent, sequent)
    (*     Γ => A                   Γ => B
      --------------(=>|_1) or ---------------(=>|_2)
         Γ => A | B               Γ => A | B
          negが空なときだけ    *)
    | (pos, []), Disj (a, b) -> begin
        try
            (* まずはどちらの規則も使わずにsearch_syncに挑戦 *)
            OneInf (DisjL, search_sync sequent, sequent)
        with NoProof ->
            try
                (* (=>|_1)に挑戦 *)
                OneInf (DisjR1, step ((pos, []) ===> a), sequent)
            with NoProof ->
                (* (=>|_2)に挑戦 *)
                OneInf (DisjR2, step ((pos, []) ===> b), sequent)
    end
       (* negが空なときsearch_sync  *)
    | (pos, []), goal -> search_sync sequent
    | _ -> failwith "step case not supposed to happen"

(* synchronous phase *)
and search_sync : sequent -> derivation = fun ((pos, _), goal) ->
    let rec aux = function
    | [] -> raise NoProof
    | (context0, context) :: cs ->
        match eliminate goal context0 context with
        | Some d -> d
        | None -> aux cs in
    aux (all_contexts pos)

(* search_syncから呼ばれて、negを常に空にして探索 *)
and eliminate : prop -> prop -> list prop =
    fun goal context0 (* コンテキストの命題適当に1つ *) context (* それ以外 *) ->
    let sequent = (context0 :: context, []) ===> goal in
    match goal, context0 with
    (* ----------------(axiom)
          Γ, A => A   *)
    | Atom x, Atom y when x = y -> Some (ZeroInf (Init, sequent))
    (*    B, A, Γ => G
      ---------------------(Atom⊃=>)
       A ⊃ B, A, Γ => G   *)
    | goal, Impl (Atom x, b) when List.mem (Atom x) context ->
        let newsequent = (context, []) $$ b ===> goal in
        (try Some (OneInf (AtomImplL, step newsequent, sequent))
        with NoProof -> None)
    (*  E ⊃ B, D, Γ => E    B, Γ => G
      ---------------------------------(⊃⊃=>)
            (D ⊃ E) ⊃ B, Γ => G      *)
    | goal, Impl (Impl (d, e), b) ->
        let newsequent1 = (context, []) $$ (e => b) $$ d ===> e in
        let newsequent2 = (context, []) $$ b ===> goal in
        (try Some (TwoInf (ImplImplL, step newsequent1, step newsequent2, sequent))
        with NoProof -> None)
    | _ -> None

(* 定理証明 *)
let prove goal =
   try Some (step (([], []) ===> goal))
   with NoProof -> None
