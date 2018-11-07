(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Programming.Eqv.
Require Import ExtLib.Structures.Monads.
Require Import ITree.
Require Import Vellvm.Util.
Require Import Vellvm.MemoryAddress.
Require Import Vellvm.DynamicValues.
Require Import Vellvm.Error.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive dtyp : Set :=
| DTYPE_I (sz:Z)
| DTYPE_Pointer
| DTYPE_Void
| DTYPE_Half
| DTYPE_Float
| DTYPE_Double
| DTYPE_X86_fp80
| DTYPE_Fp128
| DTYPE_Ppc_fp128
| DTYPE_Metadata
| DTYPE_X86_mmx
| DTYPE_Array (sz:Z) (t:dtyp)
| DTYPE_Struct (fields:list dtyp)
| DTYPE_Packed_struct (fields:list dtyp)
| DTYPE_Opaque
| DTYPE_Vector (sz:Z) (t:dtyp)     (* t must be integer, floating point, or pointer type *)
.

Module Type LLVM_INTERACTIONS (ADDR : MemoryAddress.ADDRESS).

Global Instance eq_dec_addr : RelDec (@eq ADDR.addr) := RelDec_from_dec _ ADDR.addr_dec.
Global Instance Eqv_addr : Eqv ADDR.addr := (@eq ADDR.addr).  

(* The set of dynamic types manipulated by an LLVM program.  Mostly
   isomorphic to LLVMAst.typ but
     - pointers have no further detail
     - identified types are not allowed
   Questions:
     - What to do with Opaque?
*)

Module DV := DynamicValues.DVALUE(ADDR).
Export DV.

(* IO Interactions for the LLVM IR *)
Inductive IO : Type -> Type :=
| Alloca : forall (t:dtyp), (IO dvalue)
| Load   : forall (t:dtyp) (a:dvalue), (IO dvalue)
| Store  : forall (a:dvalue) (v:dvalue), (IO unit)
| GEP    : forall (t:dtyp) (v:dvalue) (vs:list dvalue), (IO dvalue)
| ItoP   : forall (i:dvalue), (IO dvalue)
| PtoI   : forall (a:dvalue), (IO dvalue)
| Call   : forall (t:dtyp) (f:string) (args:list dvalue), (IO dvalue)
.    


(* Trace of events generated by a computation. *)
Definition Trace X := itree IO (string + X).

(* Global Instance functor_trace : Functor Trace := fun {A B} (f:A -> B) => (@ITree.map IO) _ _ (fmap f). *)

Global Instance monad_trace : (Monad Trace) :=
  { ret X x := Ret (inr x);
    bind := fun {A B} (X:Trace A) (f : A -> Trace B) => ITree.bind X
                                                                     (fun m => match m with
                                                                            | inl s => Ret (inl s)
                                                                            | inr x => f x
                                                                            end)
  }.

Global Instance exn_trace : (MonadExc string Trace) :=
  {| raise := fun _ s => Ret (inl s);
     catch := fun _ e k => match e with
                        | Ret (inl e) => k e
                        | _ => e
                        end
  |}.
(* Trace Utilities ---------------------------------------------------------- *)

(* Lift the error monad into the trace monad. *)
Definition lift_err_d {A X} (m:err A) (f: A -> Trace X) : Trace X :=
  match m with
  | inl s => raise s
  | inr b => f b
  end.

Notation "'do' x <- m ;; f" := (lift_err_d m (fun x => f))
                                (at level 100, x ident, m at next level, right associativity).

End LLVM_INTERACTIONS.

  
Module Make(ADDR : MemoryAddress.ADDRESS) <: LLVM_INTERACTIONS(ADDR).
(* The set of dynamic types manipulated by an LLVM program.  Mostly
   isomorphic to LLVMAst.typ but
     - pointers have no further detail
     - identified types are not allowed
   Questions:
     - What to do with Opaque?
*)
Include LLVM_INTERACTIONS(ADDR).
End Make.

