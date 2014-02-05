Require Import Equivalences FunextVarieties Overture
  types.Universe types.Record types.Sigma types.Prod 
  Contractible hit.Truncations HSet HProp PathGroupoids
  types.Paths types.Forall types.Bool Trunc Contractible.

Local Open Scope equiv_scope.
Local Open Scope path_scope.


Record QInv {A B: Type} (f : A -> B) := BuildQInv{
  quinv_inv : B -> A ;
  qisretr : Sect quinv_inv f;
  qissect : Sect f quinv_inv
}.

Record QEquiv A B := BuildQEquiv {
  qequiv_fun :> A -> B ;
  qequiv_qinv :> QInv qequiv_fun
}.


Definition issig_qequiv' {A B: Type} :
  {f: A -> B & QInv f} <~> QEquiv A B.
  Proof.
  issig (@BuildQEquiv A B) (@qequiv_fun A B) (@qequiv_qinv A B).
  Defined.


Definition issig_qinv' {A B: Type} (f : A -> B) :
  { g:B->A & {r:Sect g f & Sect f g}}
  <~> QInv f.
Proof.
  issig (BuildQInv A B f) (@quinv_inv A B f) (@qisretr A B f)
    (@qissect A B f) .
Defined.

Definition issig_qinv {A B} (f : A -> B) :
  { g:B->A & (Sect g f * Sect f g)}
  <~> QInv f.
Proof.
  etransitivity {g : B -> A & {_ : Sect g f & Sect f g}}.
  apply (issig_equiv _ _).
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
  apply (isequiv_adjointify f0 g0); destruct x as [g [p q]]; reflexivity.
  exact (issig_qinv' f).
  Defined.

Lemma issig_qequiv {A B: Type} :
  {f: A -> B & {g : B -> A & (Sect g f * Sect f g)}} <~> QEquiv A B.
  Proof.
    apply (equiv_adjointify (fun x => match x with
      | exist f (exist g (r,s)) => BuildQEquiv A B f (BuildQInv A B f g r s)
    end)
    (fun x => ((qequiv_fun _ _ x);
                ((quinv_inv _ (qequiv_qinv _ _ x));
                  (qisretr _ (qequiv_qinv _ _ x),
                   qissect _ (qequiv_qinv _ _ x)))))).
    destruct x as [a [b c]];simpl.
    reflexivity.
    destruct x as [a [b [c d]]];simpl.
    reflexivity.
  Defined.

Definition idQEquiv {A} : QEquiv A A :=
  (BuildQEquiv _ _ idmap (BuildQInv A A idmap idmap (@idpath A) (@idpath A))).


Check BuildQInv.
Print isequiv_path.
Print BuildQInv.
Print eisretr.
Definition qequiv_path (A B : Type) (p : A = B) : QEquiv A B
  := BuildQEquiv _ _ (transport (fun X:Type => X) p) 
  (BuildQInv _ _ _ _ (@eisretr _ _ _ (isequiv_path p)) (@eissect _ _ _ (isequiv_path p))).

Definition QInv_to_IsEquiv {A B} (f: A -> B) (e : QInv f) : IsEquiv f
  := isequiv_adjointify f (quinv_inv f e) (qisretr f e) (qissect f e).


Definition IsEquiv_To_QInv {A B} `(f: A -> B) (e:IsEquiv f) : QInv f
  :=
  BuildQInv A B f equiv_inv (eisretr f) (eissect f).
 
Definition Equiv_to_QEquiv {A B} (e:A <~> B) : QEquiv A B
  :=
  BuildQEquiv _ _
  (equiv_fun A B e) (IsEquiv_To_QInv (equiv_fun A B e)  (equiv_isequiv A B e)).

Definition QEquiv_to_Equiv {A B} (e:QEquiv A B) : A <~> B
  :=
  BuildEquiv A B
    (qequiv_fun _ _ e) (QInv_to_IsEquiv (qequiv_fun _ _ e) (qequiv_qinv _ _ e)).

Class QinvUnivalence := {
  qinv_qequiv_path :> forall (A B : Type), QInv (qequiv_path A B)
}.

Lemma QinvUnivalence_implies_preext `{QinvUnivalence} : Preext.
  Proof.
  intros A B X e.
  pose proof (QInv_to_IsEquiv (qequiv_path A B) (qinv_qequiv_path A B)).
  pose proof (quinv_inv (qequiv_path A B) (qinv_qequiv_path A B)
               (Equiv_to_QEquiv e)).
  assert ({e' : (X -> A) <~> (X -> B) & (equiv_fun _ _ e') 
          = (fun f : _ => (qequiv_fun _ _ (Equiv_to_QEquiv e)) o f)}).
  apply (equiv_rect (qequiv_path A B)
    (fun e =>
     {e' : (X -> A) <~> (X -> B) & (equiv_fun _ _ e')
     = (fun f : X -> A =>((qequiv_fun _ _ e) o f))})).
  path_induction.
  exists (BuildEquiv _ _ idmap _).
  reflexivity.
  destruct X2.
  exists x.
  assumption.
  Defined.

Definition QinvUnivalence_implies_Funext `{QinvUnivalence} : Funext
  := WeakFunext_implies_Funext (
     Preext_implies_WeakFunext QinvUnivalence_implies_preext).

Definition swapfun (x:Bool) : Bool 
  := match x with
    | true => false
    | false => true
  end.

Definition swapequiv : QEquiv (Bool:Set) (Bool:Set).
  Proof.
  refine (BuildQEquiv _ _ swapfun (BuildQInv Bool Bool swapfun swapfun _ _));
  unfold Sect, swapfun; destruct x; exact (idpath).  
  Defined.


Definition swapEq `{QinvUnivalence} : @paths Set Bool Bool
  := @quinv_inv (@paths Set Bool Bool)
    (QEquiv Bool Bool) (@qequiv_path Bool Bool) (qinv_qequiv_path Bool Bool) swapequiv.

Definition bool_lem (x:Bool): (x=true) + (x=false)
  := match x with
    | true => inl idpath
    | false => inr idpath end.

Definition bool_lem' (x:Bool): (true=x) + (false=x)
  := match x with
    | true => inl idpath
    | false => inr idpath end.

Lemma qinv_bool_false_false `{Funext} (f:Bool -> Bool) (e : QInv f) :
  (f false = false) -> (f = idmap).
  Proof.
  intro.
  apply (apD10^-1).
  intro.
  (* Double induction results in four cases. All but one case is trivial. *)
  induction (bool_lem (f x));induction x;trivial. 
  pose proof ((qissect _ e false)^ @ (ap (quinv_inv _ e) H0)).
  pose proof ((qissect _ e true)^ @ (ap (quinv_inv _ e) b)).
  induction (false_ne_true (H1 @ H2^)).
  Defined.

Lemma qinv_bool_false_true `{Funext} (f:Bool -> Bool) (e : QInv f) :
  (f false = true) -> (f = swapfun).
  Proof.
  intro.
  apply (apD10^-1).
  intro.
  (* Double induction results in four cases. All but one case is trivial. *)
  induction (bool_lem (f x));induction x;trivial. 
  pose proof ((qissect _ e false)^ @ (ap (quinv_inv _ e) H0)).
  pose proof ((qissect _ e true)^ @ (ap (quinv_inv _ e) a)).
  induction (false_ne_true (H1 @ H2^)).
  Defined.


(*
Lemma qequiv_bool_bool_qequiv_bool `{Funext} : (QEquiv Bool Bool) <~> Bool.
   Proof.
   refine (equiv_compose' _ (equiv_inverse issig_qequiv)) .
   apply (equiv_adjointify
     (fun e => e.1 false)
     (fun b : Bool => 
       if b then (issig_qequiv^-1 swapequiv) else (issig_qequiv^-1 idQEquiv))).
   destruct x;reflexivity.
   intro.
   induction (bool_lem' (x.1 false)).
   pose proof ((qinv_bool_false_true (x.1)
    (equiv_fun _ _ (issig_qinv _) (x.2)) a^)^).
   destruct x as [f [g [s r]]].
   assert (g = swapfun).
   apply (qinv_bool_false_true g (BuildQInv _ _ g f r s)).
   pose proof (s false).
   induction (g false).
   reflexivity.
   induction (true_ne_false (a @ H1)).
   induction a.
   apply (path_sigma _ (swapfun;_) (f;(g;(s,r))) H0).
   refine ((@transport_sigma' _ _ (fun f g => (Sect g f) * (Sect f g))
     swapfun f H0 (quinv_inv _ _; (qisretr _ _, qissect _ _))) @ _).
   apply (path_sigma _ (swapfun;_) (g;(s,r)) (X^)).
   unfold projT1 in H0.
   induction H0.
   refine ((transport_prod  (X^) _) @ _);  unfold fst,snd,projT2;cbv beta.
   apply path_prod'; apply apD10^-1;intro.
   exact (@set_path2 _ trunc_bool (swapfun (g x)) x _ (s x)).
   exact (@set_path2 _ trunc_bool (g (swapfun x)) x _ (r x)).
   destruct x as [f [g [s r]]].
   assert (f = idmap).
   apply (qinv_bool_false_false f (BuildQInv _ _ f g s r)).
   exact (b^).
   assert (g = idmap).
   apply (qinv_bool_false_false g (BuildQInv _ _ g f r s)).
   pose proof (ap g b).
   induction (g false).
   induction (true_ne_false (X0 @ r false)).
   reflexivity.
   induction b.
   apply (path_sigma 
     (fun f => {g : Bool -> Bool & Sect g f * Sect f g})
     (idmap;_) (f;(g;(s,r))) X^).
   refine ((@transport_sigma' _ _ (fun f g => (Sect g f) * (Sect f g))
     idQEquiv f X^ (quinv_inv _ _; (qisretr _ _, qissect _ _))) @ _).  
   apply (path_sigma _ (idmap;_) (g;(s,r)) X0^).
   unfold projT1,projT2;cbv beta.
   refine ((transport_prod  (X0^) _) @ _);  unfold fst,snd,projT2;cbv beta.
   pose proof (X^).
   induction (H0).
   apply path_prod'; apply apD10^-1;intro.
   exact (@set_path2 _ trunc_bool (idmap (g x)) x _ (s x)).
   exact (@set_path2 _ trunc_bool (g (idmap x)) x _ (r x)).
   Defined.
 *)

Lemma qinv_idmap_equiv {A} `{QinvUnivalence} :
  {g : A -> A & (g = idmap) * (g = idmap)} <~> (@QInv A A idmap). 
  Proof.
  set (funext := QinvUnivalence_implies_Funext).
  pose proof (issig_qinv (fun (x:A) => x)).
  assert ({g : A -> A & (g = idmap) * (g = idmap)} <~> 
    {g : A -> A & Sect g idmap * Sect idmap g}).
  apply (equiv_adjointify 
    (fun m =>
      match m with
       exist  g (r,s) =>
         @exist (A->A) (fun g=> (g == idmap) * (g == idmap))
          g (apD10 r,apD10 s)
      end)
    (fun m =>
      match m with
       exist  g (r,s) =>
         @exist (A->A) (fun g=>(g = idmap) * (g = idmap))
          g (apD10^-1 r,apD10^-1 s)
      end)).
  unfold Sect.
  intro.
  induction x.
  induction p.
  apply (equiv_path_sigma).
  exists (idpath).
  apply (path_prod).
  exact (eisretr apD10 a).
  exact (eisretr apD10 b).
  unfold Sect.
  intro.
  induction x.
  induction p.
  apply (equiv_path_sigma).
  exists (idpath).
  apply (path_prod).
  exact (eisretr apD10^-1 a).
  exact (eisretr apD10^-1 b).
  exact (equiv_compose' X X0).
  Defined.
 

Lemma quinv_idmap_equiv2 {A} `{QinvUnivalence} :
  {h : {g: A -> A & g = idmap} & (h.1 = idmap)} <~> (@QInv A A idmap).
  Proof.
  pose proof (equiv_sigma_assoc (fun (g:A->A) => g = idmap)
                                (fun h => h.1 = idmap)).
  unfold projT1.
  assert ({g : A -> A &
    {p : g = idmap &
    (fun h : {g : A -> A & g = idmap} => h .1 = idmap)
      (g; p)}} <~>
      {g : A -> A & (g = idmap) * (g = idmap)}).
  apply (equiv_adjointify
   (fun (x:{g : A -> A & {_ : g = idmap & g = idmap}}) =>
      match x with
        (exist g (exist p1 p2)) =>
          @exist (A->A) (fun g0 => (g0 = idmap) * (g0 = idmap)) g (p1, p2)
      end)
   (fun (x:{g : A -> A & (g = idmap) * (g = idmap)}) =>
      match x with
        (exist g (p1, p2)) =>
          exist (fun g0 => {_:g0 = idmap & g0 = idmap}) g 
            (exist (fun _ => g = idmap) p1 p2)
    end)).
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
  exact (equiv_compose' qinv_idmap_equiv (equiv_inverse X1)).
  Defined.


Lemma qinv_idmap_equiv_catcenter {A} `{QinvUnivalence}:
  (forall (x:A), x=x) <~> @QInv A A idmap.
  Proof.
  set (funext := QinvUnivalence_implies_Funext).
  set (X0 := @contr_basedpaths' (A->A) idmap).
  apply (equiv_compose' quinv_idmap_equiv2).
  pose proof (equiv_sigma_contr' (fun h => h .1 = idmap)) as X.
  apply (equiv_compose' (equiv_inverse X)).
  pose proof 
    (BuildEquiv ((fun (x:A)=>x)=idmap) ((fun (x:A) =>x)==idmap) apD10 _).
  apply (equiv_compose' (equiv_inverse X1)).
  cbv.
  exact (@equiv_idmap (forall x:A,x=x)).
  Defined.


Lemma qinv_equiv_catcenter {A B} `{QinvUnivalence} : forall (qe: QEquiv A B),
  (forall (x:A), x=x) <~> QInv (qequiv_fun _ _ qe).
  Proof.
  pose proof (QInv_to_IsEquiv (qequiv_path A B) (qinv_qequiv_path A B)).
  equiv_intro (qequiv_path A B) qe.
  path_induction.
  exact (qinv_idmap_equiv_catcenter).
  Defined.

Lemma isHProp_isHSet {A} `{QinvUnivalence} : IsHProp (IsHSet A).
  Proof.
  set (funext := QinvUnivalence_implies_Funext).
  pose proof (Equiv_to_QEquiv (@equiv_hset_axiomK funext A)).
  pose proof (quinv_inv _ (qinv_qequiv_path _ _) X).
  pose proof (axiomK_isprop A).
  path_induction.
  assumption.
  Defined.

Notation "[| A |]" := (Truncation minus_one A):truncation_scope.
Notation ".| x |." := (@truncation_incl minus_one _ x):truncation_scope.
Local Open Scope truncation_scope.

Lemma groupcenter_natural' {A} `{QinvUnivalence} : forall (a:A),
  (forall x, [| a = x |]) -> IsHSet (a=a) -> forall (x y:A), IsHSet (x=y). 
  intros a g s x y.
  pose proof (@isHProp_isHSet (x=y) H).
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
  pose proof ((quinv_inv (qequiv_path _ _)
    (qinv_qequiv_path _ _) (Equiv_to_QEquiv X0))^).
  induction X1.
  assumption.
  Defined.

Lemma groupcenter_natural {A} `{QinvUnivalence} : forall (a:A) (q:a=a),
  (forall x, [| a = x |]) -> IsHSet (a=a) -> (forall p, p @ q = q @ p)
  -> {f:forall (x:A), x=x & f a = q}.
  Proof.
  set (funext := QinvUnivalence_implies_Funext).
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
  apply (groupcenter_natural' a g s x x).
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

  Lemma qinvnotprop' `{QinvUnivalence} : 
    True=True.
    Proof.
    (*pose proof QinvUnivalence_implies_Funext as funext.*)
    set (X:= { A:Set & [| Bool = A |]}).
    set (a := ((Bool;.|idpath|.):X)).
    set (q := 
      (path_sigma _ a a
        swapEq
        (@allpath_hprop _ (istrunc_truncation minus_one _) _ _))).
    pose proof (@groupcenter_natural X H a q).
    reflexivity.
    Qed.


  Lemma qinvnotprop' `{QinvUnivalence} : exists X (g f: forall (x:X), x=x),
    not (f = g).
    Proof.
    (*pose proof QinvUnivalence_implies_Funext as funext.*)
    set (X:= { A:Set & [| Bool = A |]}).
    exists X.
    exists (fun x => idpath).
    set (a := ((Bool;.|idpath|.):X)).
    set (q := 
      (path_sigma _ a a
        swapEq
        (@allpath_hprop _ (istrunc_truncation minus_one _) _ _))).
    assert ({f : forall x : X, x = x & f a = q}).
    Check @groupcenter_natural.
    refine (@groupcenter_natural X H a q _ _ _).
    intro.
    pose proof (@equiv_sigma_contr Bool).
    pose proof (istrunc_truncation minus_one (a=x)).
    refine
      (@Truncation_rect_nondep minus_one 
        (Bool = x.1) ([|a=x|]) X1 (fun _ => _ ) (x.2)).
    apply (fun x => .|x|.).
    apply (@equiv_path_sigma _ _ a x).
    exists _H.
    exact (allpath_hprop _ _).
    assert (a=a <~> Bool).
    refine (equiv_compose' _ (equiv_inverse (equiv_path_sigma _ a a))).
    assert (forall p, Contr (transport (fun A : Set => [|Bool = A|]) p a.2=a.2)).
    intro.
    pose proof (istrunc_truncation minus_one (Bool = a.1)).
    pose proof (contr_inhabited_hprop [|Bool = a.1|] a.2).
    apply contr_paths_contr.
    refine (equiv_compose' _ (@equiv_sigma_contr _ _ X0)).
    refine (equiv_compose' _
      (QEquiv_to_Equiv (BuildQEquiv _ _ _ 
      (qinv_qequiv_path Bool Bool))) ).
    exact qequiv_bool_bool_qequiv_bool.
    (*Here we would like to use just qinv_univalence on X0 to
      show the goal but this is still buggy *)


