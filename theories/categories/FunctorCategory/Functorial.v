Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Pointwise Functor.Pointwise.Properties Category.Dual Category.Prod Cat.Core ExponentialLaws.Law4.Functors.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Section functor.
  Context `{fs1 : Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Definition cat := (sub_pre_cat P HF).

  Hypothesis has_functor_categories : forall C D : cat, P (C.1 -> D.1).

  Definition functor_uncurried `{fs2 : Funext, fs3 : Funext}
  : object (@functor_category fs2 (cat^op * cat) cat).
    refine (
    (* := Eval cbv zeta in *)
        let object_of := (fun CD => (((fst CD).1 -> (snd CD).1);
                                     has_functor_categories (fst CD) (snd CD)))
        in Build_Functor
             (cat^op * cat) cat
             object_of
             (fun CD C'D' FG => pointwise (fst FG) (snd FG))
             (fun _ _ _ _ _ => Functor.Pointwise.Properties.composition_of _ _ _ _)
             _).
    (** FIXME: Should just be able to use [Functor.Pointwise.Properties.identity_of]; maybe we need to use more funexts everywhere? *)
    intros.
    simpl.
    Set Printing Implicit.
    Print Functor.Pointwise.Properties.identity_of.
    Require Import Functor.Paths.
    path_functor.

    exists (identity_of_helper _ _).
    pose (Functor.Pointwise.Properties.identity_of (fst x).1 (snd x).1).
    unfold identity_of in p.
    let p' := (eval unfold p in p) in
    match p' with
      | path_functor'_sig _ _ (_; ?H) => pose proof H
    end.
    assumption.
  Defined.

  (** FIXME: Something is very wrong with the speed of the typechecker here...  If I define it directly, it shouldn't take forever. *)
  Definition functor `{fs2 : Funext, fs3 : Funext, fs4 : Funext} : object (cat^op -> (cat -> cat)).
    (* := ExponentialLaws.Law4.Functors.inverse _ _ _ (@functor_uncurried fs2 fs3). *)
  Proof.
    pose (@functor_uncurried fs2 fs3) as f0.
    lazymatch type of f0 with
    | object (?C * ?D -> ?E)%category =>
      pose (object_of (@ExponentialLaws.Law4.Functors.inverse fs4 C D E)) as f1
    end.
    apply f1.
    simpl in *.
    clear f1.
    exact f0.
  Defined.

End functor.
