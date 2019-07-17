(** *** Translating LJD into S-Vaidity *)

Require Export DecidableEnumerable.
From Equations Require Import Equations.

Ltac resolve_existT :=
  match goal with
  | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => rewrite (inj_pair2 _ _ _ _ _ H2) in *
  | _ => idtac
  end.

Ltac inv H :=
  inversion H; subst; repeat (progress resolve_existT).

Definition ocons X (o : option X) A :=
  match o with
  | Some a => a :: A
  | None => A
  end.
Infix "o::" := ocons (at level 55).

Lemma ocons_sub X (a : option X) A B :
  A <<= B -> a o:: A <<= a o:: B.
Proof.
  intros H. destruct a; cbn.
  - intros y []; subst; intuition.
  - assumption.
Qed.

Class rule_set (f : Type) :=
  {
    atomic : f -> Type ;
    attack : f -> option f -> Type ;
    defense : forall phi adm, attack phi adm -> f -> Type ;
    dec_f : eq_dec f
  }.

Definition opred X (p : X -> Type) (o : option X) : Type :=
  forall x, o = Some x -> p x.

Section SDialogues.
  Variable f : Type.
  Variable R : rule_set f.

  Definition justified A phi := atomic phi -> phi el A.

  Lemma justified_weak A B phi :
    justified A phi -> A <<= B -> justified B phi.
  Proof.
    intros Hjust Hsub Hin. intuition.
  Qed.

  Inductive Dprv (A : list f) (T : f -> Type): Type :=
    Def phi :
      T phi ->
      justified A phi ->
      (forall adm (atk : attack phi adm), Dprv (adm o:: A) (defense atk)) ->
      Dprv A T
  | Att psi adm (atk : attack psi adm) :
      psi el A ->
      (forall chi, defense atk chi -> Dprv (chi :: A) T) ->
      opred (fun a => justified A a) adm ->
      opred (fun a => forall adm' (atk' : attack a adm'), Dprv (adm' o:: A) (defense atk')) adm ->
      Dprv A T.
  Notation "A '⊢D' T" := (Dprv A T) (at level 30).

  Inductive challenge : Type :=
    C phi adm : attack phi adm -> challenge.
  Inductive opening phi : list f -> challenge -> Type :=
    OP (H : justified nil phi) adm (atk : attack phi adm) : opening phi (adm o:: nil) (C atk).

  Definition deferred : Type := challenge * challenge.
  Definition sstate : Type := list f * list f * list deferred.

  Inductive spmove : sstate -> challenge  -> sstate -> Type :=
  | SPAtk pA oA ds c phi adm (atk : attack phi adm) :
      phi el oA -> opred (justified oA) adm -> spmove (pA, oA, ds) c (adm o:: pA, oA, (C atk, c) :: ds)
  | SPDef pA oA ds phi adm (atk : attack phi adm) psi :
      defense atk psi -> justified oA psi -> spmove (pA, oA, ds) (C atk) (psi :: pA, oA, ds).

  Inductive somove : sstate -> sstate -> challenge -> Type :=
  | SODef pA oA ds c phi adm (atk : attack phi adm) psi :
      defense atk psi -> somove (pA, oA, (C atk, c) :: ds) (pA, psi :: oA, ds) c
  | SOAtk pA phi pA' oA ds adm (atk : attack phi adm) :
      somove (pA ++ phi :: pA', oA, ds) (pA ++ pA', adm o:: oA, ds) (C atk).

  Inductive swin_strat s c : Type :=
    SWS s' : spmove s c s' -> (forall s'' c', somove s' s'' c' -> swin_strat s'' c') -> swin_strat s c.

  Definition svalid phi :=
    prod (justified nil phi) (forall A c, opening phi A c -> swin_strat (nil, A, nil) c).

  Variable ord : Type.
  Variable (olt : ord -> ord -> Type) (oplus : ord -> ord -> ord) (osuc : ord -> ord)
           (osup : (nat -> ord) -> ord) (ozero : ord).

  Variable enum_att : forall phi, nat -> option (sigT (attack phi)).
  Variable enum_def : forall phi adm (atk : attack phi adm), nat -> option (sigT (defense atk)).

  Definition subctx A (p : list f -> Type) :=
    sigT (fun B => Datatypes.prod (B <<= A) (p B)).

  Definition subctx_lift A B p : 
    A <<= B -> subctx A p -> subctx B p.
  Proof.
    intros Hsub (C & HsubC & HC). exists C. split; [| apply HC]. firstorder.
  Defined.

  Definition counter_safe A phi :=
    subctx A (fun B => (forall adm (atk : attack phi adm), (adm o:: B) ⊢D defense atk)).
  Definition continuation A (d : deferred) :=
    match d with
      (C atk, C atk') => subctx A (fun B => forall phi, defense atk phi -> (phi :: B) ⊢D defense atk')
    end.
  Definition plan A c :=
    match c with C atk => subctx A (fun B => B ⊢D defense atk) end.

  Definition counter_safe_lift A B :
    A <<= B -> forall phi, counter_safe A phi  -> counter_safe B phi.
  Proof.
    intros. apply (subctx_lift H X).
  Defined.

  Definition continuation_lift A B :
    A <<= B -> forall d, continuation A d -> continuation B d.
  Proof.
    intros H [[] []]. apply (subctx_lift H).
  Defined.

  Definition plan_lift A B :
    A <<= B -> forall c, plan A c -> plan B c.
  Proof.
    intros H []. apply (subctx_lift H).
  Defined.

  Inductive IVec X (p : X -> Type) :  list X -> Type :=
  | vNil : IVec p []
  | vCons a (H : p a) A : IVec p A -> IVec p (a :: A).

  Fixpoint osum X (p : X -> Type) A (v : IVec p A) (f : forall x, p x -> ord) : ord :=
    match v with
    | vNil _ => ozero
    | vCons Ha vA => osuc (oplus (f _ Ha) (osum vA f))
    end.

  Fixpoint vmap X (p q : X -> Type) (f : forall x, p x -> q x) A (v : IVec p A) : IVec q A :=
    match v with
    | vNil _ => vNil _
    | vCons Ha vA => vCons (f _ Ha) (vmap f vA)
    end.

  Definition vix X (p : X -> Type) A x B (v : IVec p (A ++ x :: B)) :
    p x * IVec p (A ++ B).
  Proof.
    induction A; depelim v.
    - easy.
    - destruct (IHA v). eauto using IVec.
  Qed.

  Inductive Dprv_state : Type :=
  | DS oA pA D c : IVec (counter_safe oA) pA -> IVec (continuation oA) D -> plan oA c -> Dprv_state.

  Fixpoint Dprv_size (A : list f) (T : f -> Type) (H : Dprv A T) : ord :=
    match H with
      @Def _ _ phi HT Hjust Hc =>
        osuc (osup (fun n => match @enum_att phi n with
                            Some (existT _ adm atk) => Dprv_size (Hc adm atk)
                          | None => ozero
                          end))
    | @Att _ _ psi adm atk Hin Hcont Hajust Hadef =>
      osuc (oplus (osup (fun n => match @enum_def psi adm atk n with
                                 Some (existT _ chi Hdef) => Dprv_size (Hcont chi Hdef)
                               | None => ozero
                               end))
                  (match adm with
                     Some phi => fun Hadef' => 
                        osup (fun n => match @enum_att phi n with
                                      Some (existT _ adm' atk') => Dprv_size (Hadef' phi eq_refl adm' atk')
                                    | None => ozero
                                    end)
                   | None => fun _ => ozero
                   end Hadef))
    end.

  Definition Dprv_state_size (H : Dprv_state) : ord :=
    match H with
      @DS oA pA D c cs ct pln =>
      oplus
        (osum cs (fun phi HB => match HB with | existT _ B (_, Hphi) =>
          osup (fun n => match @enum_att phi n with
                      | Some (existT _ adm atk) => Dprv_size (Hphi adm atk)
                      | None => ozero
                      end)
               end
               ))
        (oplus
          (osum ct (fun d => match d with (C atk, C _) =>
                    fun HB => match HB with existT _ B (_, Hd) =>
                    osup (fun n => match enum_def atk n with
                                | Some (existT _ phi Hdef) => Dprv_size (Hd phi Hdef)
                                | None => ozero
                                end)
                           end
                        end))
          (match c return plan oA c -> ord with 
             C atk => fun HB => match HB with existT _ B (_, pln') => Dprv_size pln' end
           end pln))
    end.

  Hypothesis ord_ind : forall X (p : X -> Type) (f : X -> ord),
      (forall x, (forall y, olt (f y) (f x) -> p y) -> p x) -> forall x, p x.

  Lemma s_sound (s : Dprv_state) :
    match s with @DS oA pA D c _ _ _ => swin_strat (pA, oA, D) c end.
  Proof.
    apply ord_ind with (f := Dprv_state_size) (x := s). clear s.
    intros [oA pA ds c cs ct pln] IH. destruct c. destruct pln as (oA' & Hsub & prv).
    inversion prv.
    - eapply SWS. 1: exact (SPDef pA ds X (justified_weak H Hsub)). intros s'' c omv.
      inversion omv; subst.
      + depelim ct. destruct c. destruct H as (oA'' & Hsub' & prv'). cbn in ct.
        assert (Hc : counter_safe (psi :: oA) phi0) by (exists oA'; intuition).
        assert (Hp : plan (psi :: oA) (C a0)).
        1: exists (psi :: oA''); split; [| apply (prv' psi X1)]; now apply incl_shift.
        assert (Hsub'' : oA <<= psi :: oA) by intuition.
        apply (IH (DS (vCons Hc (vmap (counter_safe_lift Hsub'') cs))
                      (vmap (continuation_lift Hsub'') ct)
                      Hp)).
        shelve.
      + assert (Hsub' : oA <<= adm0 o:: oA) by (destruct adm0; cbn; intuition).
        destruct pA0; cbn in H1; injection H1; intros <- ->.
        * assert (Hp : plan (adm0 o:: oA) (C atk)).
          1: exists (adm0 o:: oA'); split; [| apply (X0 adm0 atk)]; destruct adm0; now try (apply incl_shift).
          apply (IH (DS (vmap (counter_safe_lift Hsub') cs)
                        (vmap (continuation_lift Hsub') ct)
                        Hp)).
          shelve.
        * destruct (vix cs). destruct c as (oA'' & Hsub'' & Hphi1).
          assert (Hc : counter_safe (adm0 o:: oA) phi0) by (exists oA'; destruct adm0; cbn; intuition).
          assert (Hp : plan (adm0 o:: oA) (C atk)).
          1: exists (adm0 o:: oA''); split; [| apply (Hphi1 adm0 atk)]; destruct adm0; now try (apply incl_shift).
          apply (IH (DS (vCons Hc (vmap (counter_safe_lift Hsub') i))
                        (vmap (continuation_lift Hsub') ct)
                        Hp)).
          shelve.
    - assert (H' : psi el oA) by intuition. assert (X0' : opred (fun a => justified oA a) adm0).
      1: destruct adm0; unfold opred; eauto using justified_weak. eapply SWS.
      1: exact (SPAtk pA ds (C a) atk H' X0'). intros s'' c' omv. inv omv.
      + apply inj_pair2 in H5; resolve_existT.
        assert (Hp : plan (psi0 :: oA) (C a)) by (exists oA'; cbn; intuition).
        assert (Hsub'' : oA <<= psi0 :: oA) by intuition.
        destruct adm0 as [tau |].
        * assert (Hc : counter_safe (psi0 :: oA) tau) by (exists oA'; intuition). 
          apply (IH (DS (vCons Hc (vmap (counter_safe_lift Hsub'') cs))
                        (vmap (continuation_lift Hsub'') ct)
                        Hp)).
          shelve.
        * apply (IH (DS (vmap (counter_safe_lift Hsub'') cs)
                      (vmap (continuation_lift Hsub'') ct)
                      Hp)).
          shelve.
      + assert (Hc : continuation (adm1 o:: oA) (C atk, C a)) by (exists oA'; destruct adm1; cbn; intuition).
        assert (Hsub' : oA <<= adm1 o:: oA) by (destruct adm1; cbn; intuition).
        destruct adm0 as [tau |].
        * destruct pA0; cbn in H1; injection H1; intros <- ->.
          -- assert (Hp : plan (adm1 o:: oA) (C atk0)). 1: exists (adm1 o:: oA').
             1: split; [| apply (X1 tau eq_refl adm1 atk0)]; destruct adm1; now try (apply incl_shift).
             apply (IH (DS (vmap (counter_safe_lift Hsub') cs)
                          (vCons Hc (vmap (continuation_lift Hsub') ct))
                          Hp)).
             shelve.
          -- destruct (vix cs) as [(oA'' & Hsub'' & Hphi0)  cs'].
             assert (Hc' : counter_safe (adm1 o:: oA) tau) by (exists oA'; destruct adm1; cbn; intuition).
             assert (Hp : plan (adm1 o:: oA) (C atk0)).
             1: exists (adm1 o:: oA''); split; [| apply (Hphi0 adm1 atk0)]; destruct adm1; now try (apply incl_shift).
             apply (IH (DS (vCons Hc' (vmap (counter_safe_lift Hsub') cs'))
                          (vCons Hc (vmap (continuation_lift Hsub') ct))
                          Hp)).
             shelve.
        * cbn in H1; subst. destruct (vix cs) as [(oA'' & Hsub'' & Hphi0)  cs'].
          assert (Hp : plan (adm1 o:: oA) (C atk0)).
          1: exists (adm1 o:: oA''); split; [| apply (Hphi0 adm1 atk0)]; destruct adm1; now try (apply incl_shift).
          apply (IH (DS (vmap (counter_safe_lift Hsub') cs')
                        (vCons Hc (vmap (continuation_lift Hsub') ct))
                        Hp)).
          shelve.
  Admitted.

End SDialogues.