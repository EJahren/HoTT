Require Import Equivalences FunextVarieties Overture
  types.Universe types.Record types.Sigma types.Prod 
  Contractible hit.Truncations HSet HProp PathGroupoids
  types.Paths types.Forall.

Local Open Scope equiv_scope.


Record QInv {A B : Type} (f : A -> B) : Type := BuildQInv{
  quinv_inv : B -> A ;
  qisretr : Sect quinv_inv f;
  qissect : Sect f quinv_inv
}.


Definition QEquiv (A B : Type) : Type
  := {f : A -> B & QInv f}.

Definition issig_qinv' {A B : Type} (f : A -> B) :
  { g:B->A & {r:Sect g f & Sect f g}}
  <~> QInv f.
Proof.
  issig (BuildQInv A B f) (@quinv_inv A B f) (@qisretr A B f)
    (@qissect A B f) .
Defined.

Definition issig_qinv {A B : Type} (f : A -> B) :
  { g:B->A & (Sect g f * Sect f g)}
  <~> QInv f.
Proof.
  etransitivity {g : B -> A & {_ : Sect g f & Sect f g}}.
  apply (issig_equiv _ _).
  Check @exist.
  set (f0 := (fun x =>
    match x with
      exist g (r,s)
        => @exist (B->A) (fun g => exists (_:Sect g f), Sect f g) g
        (@exist (Sect g f) (fun _ => Sect f g) r s)
    end)).
  exists f0.
  set (g0 := (fun x =>
    match x with
      exist g (exist r s) =>
        @exist (B->A) (fun g => Sect g f * Sect f g) g (r,s)
    end)).
  assert (Sect f0 g0).
  unfold Sect.
  intros.
  destruct x as [g s].
  destruct s as [p q].
  reflexivity.
  assert (Sect g0 f0).
  unfold Sect.
  intros.
  destruct x as [g s].
  destruct s as [p q].
  reflexivity.
  apply (isequiv_adjointify _ _ X0 X).
  exact (issig_qinv' f).
  Defined.

Definition idQEquiv {A : Type} : QEquiv A A.
  Proof.
  exists idmap.
  apply (BuildQInv A A idmap idmap).
  exact (@idpath A).
  exact (@idpath A).
  Defined.

Definition Path_to_QEquiv {A B : Type} (p:A = B) : QEquiv A B
  := match p with idpath => idQEquiv end.

Definition QInv_to_IsEquiv {A B : Type} (f: A -> B) (e : QInv f) : IsEquiv f
  := isequiv_adjointify f (quinv_inv f e) (qisretr f e) (qissect f e).


Definition IsEquiv_To_QInv {A B: Type} `(f: A -> B) (e:IsEquiv f) : QInv f
  :=
  BuildQInv A B f equiv_inv (eisretr f) (eissect f).
 
Definition Equiv_to_QEquiv {A B:Type} (e:A <~> B) : QEquiv A B
  :=
  (equiv_fun A B e ; IsEquiv_To_QInv (equiv_fun A B e)  (equiv_isequiv A B e)).

Definition QEquiv_to_Equiv {A B:Type} (e:QEquiv A B) : A <~> B
  :=
  BuildEquiv A B (e.1) (QInv_to_IsEquiv (e.1) e.2).

Definition QinvUnivalence := forall (A B : Type), (QInv (@Path_to_QEquiv A B)).


Lemma QinvUnivalence_implies_preext : QinvUnivalence -> Preext.
  Proof.
  unfold QinvUnivalence.
  intros QU A B X e.
  pose proof (QInv_to_IsEquiv Path_to_QEquiv (QU A B)).
  pose proof (quinv_inv Path_to_QEquiv (QU A B) (Equiv_to_QEquiv e)).
  assert ({e' : (X -> A) <~> (X -> B) & (equiv_fun _ _ e') 
          = (fun f : _ => ((Equiv_to_QEquiv e).1) o f)}).
  apply (equiv_rect (Path_to_QEquiv)
    (fun e =>
     {e' : (X -> A) <~> (X -> B) & (equiv_fun _ _ e')
     = (fun f : X -> A =>(e.1 o f))})).
  path_induction.
  exists (BuildEquiv (X->A) (X->A) idmap _).
  reflexivity.
  destruct X2.
  exists x.
  assert ((Equiv_to_QEquiv e).1 = equiv_fun _ _ e).
  reflexivity.
  path_induction.
  reflexivity.
  Defined.

Definition QinvUnivalence_implies_Funext : QinvUnivalence -> Funext
  := WeakFunext_implies_Funext o 
     Preext_implies_WeakFunext o QinvUnivalence_implies_preext.

Section AssumeQinvUnivalence.
  Context (qu:QinvUnivalence).
  Instance funext : Funext | 0.
    Proof.
    exact (QinvUnivalence_implies_Funext qu).
    Defined.

  Lemma qinv_idmap_equiv {A:Type} :
    {g : A -> A & (g = idmap) * (g = idmap)} <~> (@QInv A A idmap). 
    Proof.
    pose proof (issig_qinv (fun (x:A) => x)).
    assert ({g : A -> A & (g = idmap) * (g = idmap)} <~> 
      {g : A -> A & Sect g idmap * Sect idmap g}).
    set (f:= (fun m =>
      match m with
       exist  g (r,s) =>
         @exist (A->A) (fun g=>(g = idmap) * (g = idmap))
          g (apD10^-1 r,apD10^-1 s)
       end)).
    set (g:= (fun m =>
      match m with
       exist  g (r,s) =>
         @exist (A->A) (fun g=> (g == idmap) * (g == idmap))
          g (apD10 r,apD10 s)
       end)).
    assert (Sect f g).
    unfold Sect.
    intro.
    induction x.
    induction p.
    apply (equiv_path_sigma).
    exists (idpath).
    unfold g, f, projT2.
    apply (path_prod).
    exact (eisretr apD10 a).
    exact (eisretr apD10 b).
    assert (Sect g f).
    unfold Sect.
    intro.
    induction x.
    induction p.
    apply (equiv_path_sigma).
    exists (idpath).
    unfold g, f, projT2.
    apply (path_prod).
    exact (eissect apD10 a).
    exact (eissect apD10 b).
    exact (equiv_adjointify g f X0 X1).
    exact (equiv_compose' X X0).
    Defined.
   
  
  Lemma quinv_idmap_equiv2 {A:Type} :
    {h : {g: A -> A & g = idmap} & (h.1 = idmap)} <~> (@QInv A A idmap).
    Proof.
    Check equiv_sigma_assoc.
    pose proof (equiv_sigma_assoc (fun (g:A->A) => g = idmap)
                                  (fun h => h.1 = idmap)).
    assert ({g : A -> A &
      {p : g = idmap &
      (fun h : {g : A -> A & g = idmap} => h .1 = idmap)
        (g; p)}} <~>
        {g : A -> A & (g = idmap) * (g = idmap)}).
    unfold projT1.
    Check (@exist).
    set (f:=
      fun (x:{g : A -> A & {_ : g = idmap & g = idmap}}) =>
        match x with
          (exist g (exist p1 p2)) =>
            @exist (A->A) (fun g0 => (g0 = idmap) * (g0 = idmap)) g (p1, p2)
        end).
    set (g:=
      fun (x:{g : A -> A & (g = idmap) * (g = idmap)}) =>
        match x with
          (exist g (p1, p2)) =>
            exist (fun g0 => {_:g0 = idmap & g0 = idmap}) g (exist (fun _ => g = idmap) p1 p2)
        end).
    apply (equiv_adjointify f g).
    unfold Sect.
    intro.
    induction x.
    induction p.
    exact (idpath).
    unfold Sect.
    intro.
    induction x.
    induction p.
    exact (idpath).
    pose proof (equiv_compose' X (equiv_inverse X0)).
    exact (equiv_compose' (@qinv_idmap_equiv A) (equiv_inverse X1)).
    Defined.
  
  
  Lemma qinv_idmap_equiv_catcenter {A: Type} :
    (forall (x:A), x=x) <~> @QInv A A idmap.
    Proof.
    set (X0 := @contr_basedpaths' (A->A) idmap).
    apply (equiv_compose' (@quinv_idmap_equiv2 A)).
    pose proof (equiv_sigma_contr' (fun h => h .1 = idmap)) as X.
    apply (equiv_compose' (equiv_inverse X)).
    pose proof (BuildEquiv ((fun (x:A)=>x)=idmap) ((fun (x:A) =>x)==idmap) apD10 _).
    apply (equiv_compose' (equiv_inverse X1)).
    cbv.
    exact (@equiv_idmap (forall x:A,x=x)).
    Defined.
  
  
  Lemma qinv_equiv_catcenter {A B: Type} : forall (qe: QEquiv A B),
    (forall (x:A), x=x) <~> QInv (qe.1).
    Proof.
    pose proof (QInv_to_IsEquiv Path_to_QEquiv (qu A B)).
    equiv_intro (@Path_to_QEquiv A B) qe.
    path_induction.
    exact (@qinv_idmap_equiv_catcenter A).
    Defined.
  
  Lemma isHProp_isHSet {A:Type} : IsHProp (IsHSet A).
    Proof.
    pose proof (Equiv_to_QEquiv (@equiv_hset_axiomK funext A)).
    pose proof (quinv_inv Path_to_QEquiv (qu _ _) X).
    pose proof (axiomK_isprop A).
    path_induction.
    assumption.
    Defined.

  Notation "[| A |]" := (Truncation minus_one A):truncation_scope.
  Local Open Scope truncation_scope.
  Local Open Scope path_scope.

  Lemma groupcenter_natural' {A : Type} : forall (a:A),
    (forall x, [| a = x |]) -> IsHSet (a=a) -> forall (x y:A), IsHSet (x=y). 
    intros a g s x y.
    pose proof (@isHProp_isHSet (x=y)).
    Check (@Truncation_rect_nondep).
    refine (@Truncation_rect_nondep minus_one (a=x) (IsHSet (x=y)) X
         (fun (p:a=x) => @Truncation_rect_nondep minus_one (a=y) (IsHSet (x=y)) X
         (fun (q0:a=y) => _) (g y)) (g x)).
    assert (x=y <~> a=a).
    apply (equiv_adjointify (fun r => p @ (r @ q0^)) (fun r => p^ @ (r @ q0))).
    unfold Sect.
    intro r.
    pose proof (concat_p_Vp p ((r @ q0) @ q0 ^) @ (concat_pp_V r q0)).
    pose proof (ap (fun q => p @ q) (concat_p_pp (p^) (r @ q0) (q0^))).
    cbv beta in X1.
    exact (X1^ @ X0).
    unfold Sect.
    intro r.
    pose proof ((concat_p_Vp (p^) ((r @ q0^) @ q0)) @ concat_pV_p r q0).
    pose proof (ap (fun q => p^ @ q) (concat_p_pp p (r @ q0^) q0)).
    cbv beta in X1.
    pose proof ((inv_V p)^).
    induction X2.
    exact (X1^ @ X0).
    pose proof ((quinv_inv Path_to_QEquiv (qu _ _) (Equiv_to_QEquiv X0))^).
    induction X1.
    assumption.
    Defined.
  
  Lemma groupcenter_natural {A : Type} : forall (a:A) (q:a=a),
    (forall x, [| a = x |]) -> IsHSet (a=a) -> (forall p, p @ q = q @ p)
    -> {f:forall (x:A), x=x & f a = q}.
    Proof.
    intros a q g s commutes.
    set (B := (fun x => {r:x=x & forall (s:a=x), (r = s^ @ q @ s)})).
    assert (forall x, IsHProp (B x)).
    intro.
    refine (@Truncation_rect_nondep minus_one (a=x) (IsHProp (B x))
     (HProp_HProp (B x)) (fun p => _) (g x)).
    apply hprop_allpath.
    intros.
    destruct x0 as [r h].
    destruct y as [r' h'].
    apply (equiv_path_sigma).
    exists (h p @ (h' p)^).
    unfold projT2.
    pose proof ((@transport_forall_constant (x=x) (a=x)
       (fun r0 s0 => r0 = (s0^ @ q) @ s0 ) r _ (h p @ (h' p) ^) h)).
    apply funext in X.
    apply (fun p => X @ p).
    apply path_forall.
    unfold pointwise_paths.
    intros.
    refine (@transport_paths_l (x=x) _ _ _ (h p @ (h' p) ^) (h x0) @ _).
    apply (@groupcenter_natural' A a g s x x).
    assert (forall x, B x).
    intro.
    refine (@Truncation_rect_nondep minus_one (a=x) (B x)
      (X x) (fun p => _) (g x)).
    exists (p^ @ q @ p).
    intro.
    apply (fun r => concat_pp_p (p^) q p @ r).
    apply moveR_Mp.
    induction ((inv_V p)^).
    apply (cancelR (q @ p) (p @ ((s0 ^ @ q) @ s0)) (s0^)).
    refine (_ @ concat_p_pp p (((s0 ^ @ q) @ s0)) (s0^)).
    refine ( _ @ (ap (fun q => p @ q) (concat_pp_V (s0^ @ q) s0))^).
    refine (concat_pp_p q p (s0^) @ _).
    refine (_ @ concat_pp_p p (s0^) q).
    exact ((commutes (p @ s0^))^).
    exists (fun x => (X0 x).1).
    exact (((X0 a).2 q) @ (concat_Vp q @@ (@idpath _ q)) @ concat_1p q).
    Defined.
