(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)

From ITree Require Import
     Core Morphisms OpenSum Termination.

Module Type FixSig.
  Section Fix.
    (* the ambient effects *)
    Context {E : Type -> Type}.

    Context {dom : Type}.
    Variable codom : dom -> Type.

    Definition fix_body : Type :=
      forall E',
        (forall t, itree E t -> itree E' t) ->
        (forall x : dom, itree E' (codom x)) ->
        forall x : dom, itree E' (codom x).

    Parameter mfix : fix_body -> forall x : dom, itree E (codom x).

    Axiom mfix_unfold : forall (body : fix_body) (x : dom),
        mfix body x = body E (fun t => id) (mfix body) x.

  End Fix.
End FixSig.

Module FixImpl <: FixSig.
  Section Fix.
    (* the ambient effects *)
    Variable E : Type -> Type.

    Variable dom : Type.
    Variable codom : dom -> Type.

    (* the fixpoint effect, used for representing recursive calls *)
    Variant fixpoint : Type -> Type :=
    | call : forall x : dom, fixpoint (codom x).

    Section mfix.
      (* this is the body of the fixpoint. *)
      Variable f : forall x : dom, itree (sum1 E fixpoint) (codom x).

      Local CoFixpoint homFix {T : Type}
            (c : itree (sum1 E fixpoint) T)
      : itree E T :=
        match c.(observe) with
        | RetF x => Ret x
        | @VisF _ _ _ u ee k =>
          match ee with
          | inrE e =>
            match e in fixpoint u return (u -> _) -> _ with
            | call x => fun k =>
              Tau (homFix (ITree.bind (f x) k))
            end k
          | inlE e' =>
            Vis e' (fun x => homFix (k x))
          end
        | TauF x => Tau (homFix x)
        end.

      Definition _mfix (x : dom) : itree E (codom x) :=
        homFix (f x).

      Definition eval_fixpoint T (X : sum1 E fixpoint T) : itree E T :=
        match X with
        | inlE e => ITree.liftE e
        | inrE f0 =>
          match f0 with
          | call x => Tau (_mfix x)
          end
        end.

      Theorem homFix_is_interp : forall {T} (c : itree _ T),
          homFix c = interp eval_fixpoint c.
      Proof.
      Admitted.

      Theorem _mfix_unroll : forall x, _mfix x = homFix (f x).
      Proof. reflexivity. Qed.

      Variable lt_dom : dom -> dom -> Prop.
      Hypothesis wf_lt_dom : well_founded lt_dom.

      Definition cond x E (P : forall u, E u -> Prop) u (e : (E +' fixpoint) u) : Prop :=
        match e return Prop with
        | inlE x => P _ x
        | inrE (call y) => lt_dom y x
        end.

      Definition mfix_terminates {P : forall u, E u -> Prop}
                 (Tbody : forall x, terminates (cond x E P) (f x))
                 (x : dom)
        : terminates P (_mfix x).
      Proof.
        refine (
           Fix wf_lt_dom (fun x => forall p : itree (E +' fixpoint) (codom x),
                               terminates (cond x E P) p ->
                               terminates P (homFix p))
                (fun (x : dom)
                   (recurse : forall y : dom, lt_dom y x ->
                                         forall p : itree (E +' fixpoint) (codom _),
                                           terminates (cond _ E P) p ->
                                           terminates P (homFix p)) =>
                   (fix rec p (t : terminates (cond _ E P) p)
                    : terminates P (homFix p) :=
                      {| tobserve :=
                           _ |})) x (f x) (Tbody _)).
        refine  (
            match t.(tobserve) in terminates' _ _ p
                  return terminates' P _ (homFix {| observe := p |}).(observe)
            with
            | Ret_terminates x =>
              Ret_terminates x
            | Tau_terminates t =>
              Tau_terminates (rec _ t)
            | @Vis_terminates _ _ _ _ _ e k pf tk =>
              match e as e
                    return
                    (cond _ E P _ e ->
                     terminates' P (terminates P)
                                 (observe (homFix (Vis e _))))
              with
              | inlE e0 => fun pf =>
                Vis_terminates e0 pf (fun y => rec _ (tk y))
              | inrE arg' => fun pf =>
                _
              end pf
            end
         ).
        clear - Tbody tk recurse rec pf.
        destruct arg'.
        compute.
        constructor.
        change (terminates P
                            (homFix (ITree.bind (f x0) k))).
        cutrewrite (homFix (ITree.bind (f x0) k) =
                    ITree.bind (homFix (f x0))
                               (fun x => homFix (k x))).
        { eapply bind_terminates.
          - eapply recurse. eapply pf.
            eapply Tbody.
          - intros. eapply rec. eapply tk. }
        { admit. }
      Admitted.

    End mfix.

    Section mfixP.
      (* The parametric representation allows us to avoid reasoning about
       * `homFix` and `eval_fixpoint`. They are (essentially) replaced by
       * beta reduction.
       *
       * The downside, is that the type of the body is a little bit more
       * complex, though one could argue that it is a more abstract encoding.
       *)
      Definition fix_body : Type :=
        forall E',
          (forall t, itree E t -> itree E' t) ->
          (forall x : dom, itree E' (codom x)) ->
          forall x : dom, itree E' (codom x).

      Variable body : fix_body.

      Definition mfix
      : forall x : dom, itree E (codom x) :=
        _mfix
          (body (E +' fixpoint)
                (fun t => @interp _ _ (fun _ e => lift e) _)
                (fun x0 : dom => ITree.liftE (inrE (call x0)))).

      Theorem mfix_unfold : forall x,
          mfix x = body E (fun t => id) mfix x.
      Proof. Admitted.
    End mfixP.
  End Fix.

  (* [mfix] with singleton domain. *)
  Section Fix0.
    Variable E : Type -> Type.
    Variable codom : Type.

    Definition fix_body0 : Type :=
      forall E',
        (forall t, itree E t -> itree E' t) ->
        itree E' codom ->
        itree E' codom.

    Definition mfix0 (body : fix_body0) : itree E codom :=
      mfix E unit (fun _ => codom)
           (fun E' lift self (_ : unit) =>
              body E' lift (self tt)) tt.
  End Fix0.

  (* [mfix] with constant codomain. *)
  Section Fix1.
    Variable E : Type -> Type.
    Variable dom : Type.
    Variable codom : Type.

    Definition fix_body1 : Type :=
      forall E',
        (forall t, itree E t -> itree E' t) ->
        (dom -> itree E' codom) ->
        (dom -> itree E' codom).

    Definition mfix1 : fix_body1 -> dom -> itree E codom :=
      mfix E dom (fun _ => codom).
  End Fix1.

End FixImpl.

Export FixImpl.
Arguments mfix {_ _} _ _ _.
Arguments mfix0 {E codom} body.
Arguments mfix1 {E dom codom} body _.
