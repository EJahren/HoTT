Require Import types.Bool Equivalences Overture Misc.

Record QInv {A B : Type} (f : A -> B) : Type := buildQInv{
  qquiv_inv : B -> A ;
  qisretr : Sect qquiv_inv f;
  qissect : Sect f qquiv_inv
}.

Definition QEquiv (A B : Type) : Type
  := {f : A -> B & QInv f}.

Definition idQEquiv {A : Type} : QEquiv A A.
  Proof.
  exists idmap.
  apply (buildQInv A A idmap idmap).
  exact (@idpath A).
  exact (@idpath A).
  Defined.

Definition idToQEquiv {A B : Type} (p:A = B) : QEquiv A B
  := match p with idpath => idQEquiv end.

Definition QInvToIsEquiv {A B : Type} (f: A -> B) (e : QInv f) : IsEquiv f
  := isequiv_adjointify f (qquiv_inv f e) (qisretr f e) (qissect f e).


Definition IsEquivToQInv {A B: Type} `(f: A -> B) (e:IsEquiv f) : QInv f
  :=
  buildQInv A B f equiv_inv (eisretr f) (eissect f).

Definition QinvUnivalence := forall (A B : Type), (QInv (@idToQEquiv A B)).

Print equiv_path_sigma_hprop.
Lemma 
