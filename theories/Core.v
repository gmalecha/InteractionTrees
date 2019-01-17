Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(* Move the following tactic somewhere appropriate *)
Lemma hexploit_mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.
Ltac hexploit x := eapply hexploit_mp; [eapply x|].

Ltac inv H := inversion H; clear H; subst.

Section itree.

  Context {E : Type -> Type} {R : Type}.

  Inductive itreeF {itree : Type} :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {u} (e : E u) (k : u -> itree)
  .
  Arguments itreeF _ : clear implicits.

  (** An [itree E R] is the denotation of a program as coinductive
    (possibly infinite) tree where the leaves [Ret] are labeled with
    [R] and every node is either a [Tau] node with one child, or a
    branching node [Vis] with a visible effect [E X] that branches
    on the values of [X]. *)
  CoInductive itree : Type := go
  { observe : itreeF itree }.

  Axiom itree_eta : forall s, s = go (s.(observe)).

  (** Notes about using [itree]:

     - You should simplify using [cbn] rather than [simpl] when working
       with terms of the form [observe e] where [e] is defined by
       [CoFixpoint] (as in [bind] and [map] below).  [simpl] does not
       unfold the definition properly to expose the [observe t] term.

     - Once you have [observe t] as the subject of [match], you can 
       [destruct (observe t)] to do the case split.

   [[  - TODO: add more documentation about the ways  to define functions
       by splitting them into the "_match" body and the [CoFixpoint] 

       - TODO: paco?

   ]]

   *)

End itree.

Arguments itreeF _ _ : clear implicits.
Arguments itree _ _ : clear implicits.
Arguments itree_eta {E R} s.

(** We introduce notation for the [Tau], [Ret], and [Vis] constructors. Using
    notation rather than definitions works better for extraction.  (The [spin]
    definition, given below does not extract correctly if [Tau] is a definition.)

    Using this notation means that we occasionally have to eta expand, e.g.
    writing [Vis e (fun x => Ret x)] instead of [Vis e Ret].
*)
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).

Module ITree.

Section bind.
  Context {E : Type -> Type} {T U : Type}.
  Variable k : T -> itree E U.

  (* The [match] in the definition of bind. *)
  Definition bind_match
             (bind : itree E T -> itree E U)
             (c : itree E T) : itree E U :=
    match c.(observe) with
    | RetF r => k r
    | TauF t => Tau (bind t)
    | VisF e h => Vis e (fun x => bind (h x))
    end.

  CoFixpoint bind' (t : itree E T) : itree E U :=
    bind_match bind' t.

End bind.

Arguments bind_match _ _ /.

(* Monadic [>>=]: tree substitution, sequencing of computations. *)
Definition bind {E T U}
           (c : itree E T) (k : T -> itree E U)
: itree E U :=
  bind' k c.

(* note(gmm): There needs to be generic automation for monads to simplify
 * using the monad laws up to a setoid.
 * this would be *really* useful to a lot of projects.
 *
 * this will be especially important for this project because coinductives
 * don't simplify very nicely.
 *)

(** Functorial map ([fmap] in Haskell) *)
Definition map {E R S} (f : R -> S)  (t : itree E R) : itree E S :=
  bind t (fun x => Ret (f x)).

Definition liftE {E : Type -> Type} {X : Type}
           (e : E X) : itree E X :=
  Vis e (fun x => Ret x).

(** Ignore the result of a tree. *)
Definition ignore {E R} : itree E R -> itree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E R} : itree E R := Tau spin.

(** Repeat a computation infinitely. *)
Definition forever {E R S} (t : itree E R) : itree E S :=
  cofix forever_t := bind t (fun _ => Tau forever_t).

(* this definition exists in ExtLib (or should because it is
 * generic to Monads)
 *)
Definition when {E}
           (b : bool) (body : itree E unit) : itree E unit :=
  if b then body else Ret tt.

Lemma observe_bind : forall {E T U} c (k : T -> itree E U),
    observe (bind c k) = match c.(observe) with
                         | RetF r => (k r).(observe)
                         | TauF t => TauF (bind t k)
                         | VisF e h => VisF e (fun x => bind (h x) k)
                         end.
Proof.
  unfold bind, bind', bind_match. unfold observe.
  intros.
  (* note(gmm): i wasn't able to find any way to pattern match on this goal. *)
  change (let z := observe c in
          observe match z with
                  | RetF r => k r
                  | TauF t =>
                    Tau
                      ((cofix bind' (t0 : itree E T) : itree E U :=
                          match observe t0 with
                          | RetF r => k r
                          | TauF t1 => Tau (bind' t1)
                          | @VisF _ _ _ u e h => Vis e (fun x : u => bind' (h x))
                          end) t)
                  | @VisF _ _ _ u e h =>
                    Vis e
                        (fun x : u =>
                           (cofix bind' (t : itree E T) : itree E U :=
                              match observe t with
                              | RetF r => k r
                              | TauF t0 => Tau (bind' t0)
                              | @VisF _ _ _ u0 e0 h0 => Vis e0 (fun x0 : u0 => bind' (h0 x0))
                              end) (h x))
                  end =
          match z with
          | RetF r => observe (k r)
          | TauF t =>
            TauF
              ((cofix bind' (t0 : itree E T) : itree E U :=
                  match observe t0 with
                  | RetF r => k r
                  | TauF t1 => Tau (bind' t1)
                  | @VisF _ _ _ u e h => Vis e (fun x : u => bind' (h x))
                  end) t)
          | @VisF _ _ _ u e h =>
            VisF e
                 (fun x : u =>
                    (cofix bind' (t : itree E T) : itree E U :=
                       match observe t with
                       | RetF r => k r
                       | TauF t0 => Tau (bind' t0)
                       | @VisF _ _ _ u0 e0 h0 => Vis e0 (fun x0 : u0 => bind' (h0 x0))
                       end) (h x))
          end
         ).
  destruct z; try reflexivity.
Defined.

End ITree.

(* Sometimes it's more convenient to work without the type classes
   Monad, etc. When functions using type classes are specialized,
   they simplify easily, so lemmas without classes are easier
   to apply than lemmas with.

   We can also make ExtLib's [bind] opaque, in which case it still
   doesn't hurt to have these notations around.
 *)

Notation "t1 >>= k2" := (bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Instance Functor_itree {E} : Functor (itree E) :=
{ fmap := @ITree.map E }.

(* Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
   [pure] and [ret] to make the extracted code respect OCaml's
   value restriction. *)
Instance Applicative_itree {E} : Applicative (itree E) :=
{ pure := fun _ x => Ret x
; ap := fun _ _ f x =>
          ITree.bind f (fun f => ITree.bind x (fun x => Ret (f x)))
}.

Global Instance Monad_itree {E} : Monad (itree E) :=
{| ret := fun _ x => Ret x
;  bind := @ITree.bind E
|}.

Lemma bind'_to_bind {E R U} : forall (t: itree E U) (k: U -> itree E R),
    ITree.bind' k t = ITree.bind t k.
Proof. reflexivity. Qed.

Ltac fold_bind := rewrite !bind'_to_bind in *.
