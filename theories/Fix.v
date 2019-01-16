(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)

From ITree Require Import
     Core Morphisms OpenSum.

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

      Inductive terminates E (P : forall u, E u -> Prop) {t} : itree E t -> Type :=
      | Ret_terminates x : terminates E P {| observe := RetF x |}
      | Tau_terminates {i} : terminates E P i -> terminates E P {| observe := TauF i |}
      | Vis_terminates {u} {e : E u} {k}
                       (_ : P _ e)
                       (_ : forall v, terminates E P (k v))
        : terminates E P {| observe := VisF e k |}.
      Arguments terminates {_} _ {_} _.
      Arguments Ret_terminates {_ _ _} _.
      Arguments Tau_terminates {_ _ _ _} _.
      Arguments Vis_terminates {_ _ _ _} _ {_} _ _.

      (* temporary *)
      Lemma force : forall e t (x : itree e t), x = {| observe := x.(observe) |}.
      Admitted.
      Theorem bind_terminates
      : forall {E} (P : forall u, E u -> Prop)
          {t u} c (k : t -> itree E u),
          terminates P c ->
          (forall x, terminates P (k x)) ->
          terminates P (ITree.bind c k).
      Proof.
        intros.
        refine (
            (fix rec c (t1 : terminates P c) : terminates P (ITree.bind c k) :=
               match t1 with
               | Ret_terminates x =>
                 _
               | _ => _
               end) _ X).
        { rewrite force. compute. rewrite <- force. eapply X0. }
        { rewrite force. compute. eapply Tau_terminates.
          eapply rec. eassumption. }
        { rewrite force. compute.
          eapply Vis_terminates. eassumption.
          intros.
          eapply rec. eapply t0. }
      Defined.

      Definition cond x E (P : forall u, E u -> Prop) u (e : (E +' fixpoint) u) : Prop :=
        match e return Prop with
        | inlE x => P _ x
        | inrE (call y) => lt_dom y x
        end.

      Theorem mfix_terminates
      : forall (P : forall u, E u -> Prop),
          (forall x, @terminates
                  (E +' fixpoint)
                  (cond x E P) _ (f x)) ->
          forall x, @terminates E P _ (_mfix x).
      Proof.
        refine (fun P Term x =>
           Fix wf_lt_dom (fun x => forall p : itree (E +' fixpoint) (codom x),
                               terminates (cond x E P) p ->
                               terminates P (homFix p))
                (fun (x : dom)
                   (recurse : forall y : dom, lt_dom y x ->
                                         forall p : itree (E +' fixpoint) (codom _),
                                           terminates (cond _ E P) p ->
                                           terminates P (homFix p))
                   (p : _) (t : _) =>
                   (fix rec p (t : terminates (cond _ E P) p)
                    : @terminates E P _ (homFix p) :=
                      match t in @terminates _ _ _ p
                            return @terminates E P _ (homFix p)
                      with
                      | Ret_terminates x =>
                        _
                      | Tau_terminates t =>
                        _
                      | Vis_terminates e pf tk =>
                        _
                      end) _ t
                     ) x (f x) (Term _)).
        { rewrite force. compute. constructor. }
        { rewrite force. unfold homFix. compute.
          eapply Tau_terminates. eapply rec. eapply t. }
        { rewrite force.
          destruct e.
          { compute. eapply Vis_terminates; [ apply pf | ].
            intros. eapply rec. eapply tk. }
          { destruct f0.
            compute.
            eapply Tau_terminates.
            change (terminates P (homFix (ITree.bind (f x1) i))).
            cutrewrite (homFix (ITree.bind (f x1) i) = ITree.bind (homFix (f x1))
                                                                  (fun x => homFix (i x))).
            { eapply bind_terminates.
              eapply recurse; eauto.
              intros. eapply rec.
              eapply tk. }
            { admit. } } }
      Admitted.

      Fixpoint runE {P t} (p : itree E t) (term : terminates P p) {struct term}
      : itree E t :=
        match term with
        | Ret_terminates x => Ret x
        | Tau_terminates term => runE _ term
        | Vis_terminates e _ t0 =>
          Vis e (fun x => runE _ (t0 x))
        end.

      Fixpoint run {P t} (p : itree (fun _ => Empty_set) t)
               (term : terminates P p) {struct term}
      : t :=
        match term with
        | Ret_terminates x => x
        | Tau_terminates term => run _ term
        | Vis_terminates e _ t0 =>
          match e with end
        end.


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
