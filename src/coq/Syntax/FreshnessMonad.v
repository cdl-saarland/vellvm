From Coq Require Import
     String.

From ITree Require Import
     ITree
     Events.State.
Import ITree.Basics.Basics.Monads.

From Ceres Require Import
     CeresString.

From Vellvm Require Import
     Utils.Error
     Syntax.LLVMAst.

From Tutorial Require Import
     Fin Imp.
From Coq Require Import Compare_dec.

Set Implicit Arguments.
Set Strict Implicit.

Import  Ascii. 
Require Export Coq.Strings.String.
Require Import Ceres.Ceres.
Import Monad.
Import MonadNotation.
Open Scope monad_scope.
Open Scope char_scope.
Open Scope string_scope.

Definition is_connector (c : ascii) : bool :=
  match c with
  | "095"%char => true
  | _ => false
  end.

Definition is_alpha (c : ascii) : bool :=
  if CeresString.is_upper c then true else if
      CeresString.is_lower c then true else
      if is_connector c then true else false.

Definition is_correct_prefix (s : string) : bool :=
  CeresString.string_forall is_alpha s.

(** * Freshness monad

    We define a monad used to generate fresh names for block identifiers and local variables.

    The starting point is to take inspiration from Vadim Zaliva's FSHCOL to VIR compiler as
    part of the HELIX project: natural numbers are incremented and used as suffixes with
    prefixes constrained to be purely alphabetical to generate fresh variable names.

    While this simple approach is sufficient to conveniently code the compiler, it leaves
    _heavy_ proof burden afterwards.
    We therefore aim to provide combinators for code generation that provide freshness
    guarantees for free.

 *)

Section FreshnessMonad.

  (* Record FreshState := *)
  (*   mkFreshState *)
  (*     { *)
  (*       block_count: nat ; *)
  (*       local_count: nat ; *)
  (*       (* void_count : nat ; *) *)
  (*     }. *)

  (* Definition newState: FreshState := *)
  (*   {| *)
  (*   block_count := 0 ; *)
  (*   local_count := 0 ; *)
  (*   (* void_count  := 0 ; *) *)
  (*   |}. *)

  Definition prefix := { s : string & is_correct_prefix s = true }.

  Definition var_ : Type := nat.

  (** * FreshState
      The state stores:
      - [count] is the next integer to be used to generate a fresh name
      - the last [scope] variable generated are considered to be in scope
      - we do not refer to these by name but by their position in the stack,
        [assoc_prefix] is used to retrieve the registered readable name
   *)
  Record FreshState :=
    mkFreshState
      {
        count: nat ;
        scope : nat;
        assoc_prefix: list (nat * prefix)
        (* assoc_prefix: fin scope -> prefix *)
      }.
  
  Definition FreshM := stateT FreshState err.
  Instance FreshMonad : Monad FreshM := _. 

  Definition build_pretty_var (p : prefix) (n : var_) : string :=
    (projT1 p ++ string_of_nat n).

  (* Definition extend_fin_map *)
  (*            {T : Type} {k : nat} *)
  (*            (m : fin k -> T) (t : T) : fin (S k) -> T := *)
  (*   fun x => match split_fin_sum 1 _ x with *)
  (*         | inl _ => t *)
  (*         | inr x => m x *)
  (*         end. *)

  (* Naive first attempt: [scope; count-scope-1] is in scope *)
  Definition in_scope (x : var_) : FreshM bool :=
    fun s => inr (s, andb (leb s.(scope) x) (leb (S x) (s.(count) - s.(scope)))).

End FreshnessMonad. 

Section Generators.

  (* Generator to create a local id valid to be looked up.
   Relies on [gen_rid]: it ensures to only succeed if the variable
   we are intending to lookup is indeed in scope.
   *)
  Definition gen_rid (k : nat) : FreshM raw_id :=
    b <- in_scope k;;
    if b then 
    fun s =>
          | left LT => inr (s, Name (build_pretty_var (assoc_prefix s (Fin.of_nat_lt LT)) k))
          | right _ => inl "Variable out of scope"
          end.
  (* Definition gen_rid (k : nat) : FreshM raw_id := *)
  (*   fun s => match lt_dec k (scope s) with *)
  (*         | left LT => inr (s, Name (build_pretty_var (assoc_prefix s (Fin.of_nat_lt LT)) k)) *)
  (*         | right _ => inl "Variable out of scope" *)
  (*         end. *)

  Definition gen_lid x : FreshM ident :=
    'i <- gen_rid x;;
    ret (ID_Local i).

  Definition create_lid (s : prefix) : FreshM raw_id :=
    fun st =>
      ({ scope := S st.(scope) ;
         count := S count ;
         assoc_prefix := extend_fin_map 

  Definition gen_instr (i : instr typ) : FreshM (instr_id * instr typ) :=
    

End Generators.

Section CompilerTutorial.

  Import List.ListNotations.
  Open Scope list.

  Definition var_ctx := list (Imp.var * var_).

  Fixpoint compile_expr (e: expr): FreshM (code typ) :=
    match e with
    | Var x => ret [(IId res, INSTR_Load false (IntType)
                                               (TYPE_Pointer (IntType),
                                                (EXP_Ident i))
                                               (ret 8%Z))]
    | Lit n => ret [raw]
    | Plus e1 e2 =>
      '(c1,x1) <- compile_expr e1;;
      '(c2,x2) <- compile_expr e2;;
      ret (c1 ++ c2) 
    | Minus e1 e2 =>
      c1 <- compile_expr e1;;
      c2 <- compile_expr e2;;
      ret (c1 ++ c2) 
    | Mult e1 e2 =>
      c1 <- compile_expr e1;;
      c2 <- compile_expr e2;;
      ret (c1 ++ c2) 
    end.


  Fixpoint compile_expr (e : expr) : FreshM (raw_id * code typ) :=
    match e with
    | Var x =>
      
      ret (



          (* Coercion projT1 : prefix >-> string. *)

          Definition getL : FreshM nat := fun s => (s, local_count s).
          Definition getB : FreshM nat := fun s => (s, block_count s).

          Definition incBlockNamed (s: string): 
            st <- get  ;;
            put
              {|
                block_count := S (block_count st);
                local_count := local_count st ;
                void_count := void_count st ;
                Γ := Γ st
              |} ;;
            ret (Name (prefix ++ string_of_nat (block_count st))).


          Definition mkInstr (i : instr typ) : fun (s : prefix) => FreshM (instr_id * instr typ) :=

