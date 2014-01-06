Require Import Category.Core Category.Morphisms Category.Univalent GroupoidCategory.Core.
Require Import Trunc Equivalences HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope category_scope.

Section groupoid_category.
  Variable X : Type.
  Context `{IsTrunc 1 X}.

  Definition isotoid (s d : groupoid_category X)
  : s <~=~> d -> s = d
    := fun f => f : morphism _ _ _.

  Global Instance iscategory_groupoid_category
  : IsCategory (groupoid_category X).
  Proof.
    repeat intro.
    apply (isequiv_adjointify (@idtoiso (groupoid_category X) _ _)
                              (@isotoid _ _));
      repeat intro;
      destruct_head @Isomorphic;
      destruct_head @IsIsomorphism;
      compute in *;
      path_induction_hammer.
    (** FIXME: [path_induction_hammer] tries [assert (1%path = left_inverse) by exact (center _).], which should just work.  But it doesn't. *)
    assert (1%path = left_inverse) by apply H.
    assert (1%path = right_inverse) by apply H.
    path_induction; reflexivity.
  Qed.
End groupoid_category.
