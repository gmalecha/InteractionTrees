From ITree Require Import Core.

Section terminates.
  Context {E : Type -> Type}
          (P : forall u, E u -> Prop).

  Inductive terminates' {t} (rel : itree E t -> Type)
  : itreeF E t (itree E t) -> Type :=
  | Ret_terminates x : terminates' rel (RetF x)
  | Tau_terminates {i} : rel i -> terminates' rel (TauF i)
  | Vis_terminates {u} {e : E u} {k}
                   (_ : P _ e)
                   (_ : forall v, rel (k v))
    : terminates' rel (VisF e k).

  Inductive terminates {t} (it : itree E t) : Type :=
  { tobserve : terminates' terminates it.(observe) }.
  Arguments tobserve {_ _} _.

  Definition bind_terminates {t u} c (k : t -> itree E u)
             (Tc : terminates c)
             (Tk : forall x, terminates (k x))
    : terminates (ITree.bind c k).
  Proof.
    refine (
        (fix rec c (t1 : terminates c) : terminates (ITree.bind c k) :=
           {| tobserve :=
                _ |}) _ Tc).
    refine (match t1.(tobserve) in terminates' _ i
                      return
                      (terminates' terminates
                                   (Core.observe
                                      match i with
                                      | RetF r => k r
                                      | TauF t0 =>
                                        Tau (ITree.bind t0 k)
                                      | @VisF _ _ _ u0 e h =>
                                        Vis e (fun x => ITree.bind (h x) k)
                                      end))
                with
                | Ret_terminates _ x => (Tk _).(tobserve)
                | Tau_terminates _ tk => Tau_terminates _ (rec _ tk)
                | Vis_terminates _ p tk =>
                  Vis_terminates _ p (fun y => rec _ (tk y))
                end).
  Defined.

  (* terminating interactive computations *)
  Inductive itreeT {t} : Type :=
  | TRet (_ : t)
  | TVis {u} (_ : E u) (_ : u -> @itreeT t).
  Arguments itreeT _ : clear implicits.

  (* convert a provably terminating interaction tree into an `itreeT`.
   * note: if you want the resulting value, you can use `getT` defined below
   * assuming that there are no more environment interactions.
   *)
  Fixpoint runE {t} (p : itree E t) (term : terminates p) {struct term}
  : itreeT t :=
    match term.(tobserve) with
    | Ret_terminates _ x => TRet x
    | Tau_terminates _ term => runE _ term
    | @Vis_terminates _ _ _ e _ _ t0 =>
      TVis e (fun x => runE _ (t0 x))
    end.

End terminates.
Arguments Ret_terminates {_ _ _ _} _.
Arguments Tau_terminates {_ _ _ _ _} _.
Arguments Vis_terminates {_ _ _ _ _} _ {_} _ _.
Arguments tobserve {_ _ _ _} _.
Arguments itreeT _ _ : clear implicits.

Fixpoint getT {t} (it : itreeT (fun _ => Empty_set : Type) t) : t :=
  match it with
  | TRet x => x
  | TVis e _ => match e with end
  end.