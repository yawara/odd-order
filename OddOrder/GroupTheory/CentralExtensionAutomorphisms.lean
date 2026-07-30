/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralElementaryExtension
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Isomorphisms of central elementary extensions along coordinate changes

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Lemma 1(c), pp. 139–140.

Let `1 → W → E → V → 1` and `1 → W' → E' → V' → 1` be central extensions of
elementary abelian `2`-groups with square maps `q : V → W` and
`q' : V' → W'`, and let `f : V ≃+ V'` and `g : W ≃+ W'` be isomorphisms.
Lemma 1(c) states that an isomorphism `E ≃* E'` inducing `f` on the
quotients and `g` on the kernels exists if and only if `g ∘ q = q' ∘ f`.

Necessity is immediate from the square-coordinate formulas.  For
sufficiency, transport the primed extension along `(f, g)` — keeping the
middle group `E'` and reindexing the two end groups
(`GroupExtension.twistCoords`) — so that both extensions become extensions
of `V` by `W` with the *same* square map `q`; then
`GroupExtension.equivOfCommonSquareMap` produces the equivalence.

Main declarations:

* `GroupExtension.twistCoords` — reindex the end groups of an extension
  along isomorphisms, keeping the middle group;
* `GroupExtension.comp_squareMap_eq_of_mulEquiv` — Lemma 1(c), necessity;
* `GroupExtension.exists_mulEquiv_of_comp_squareMap_eq` — Lemma 1(c),
  sufficiency;
* `GroupExtension.inducingIdAuts` — the subgroup of `MulAut E` of
  automorphisms inducing the identity on both end groups;
* `GroupExtension.inducingIdAutsEquivHom` — **Lemma 1(d)**: that subgroup is
  isomorphic to the additive group `Hom(V, W)`;
* `GroupExtension.isElementaryAbelian_inducingIdAuts` — hence it is an
  elementary abelian `2`-group when `W` is.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

noncomputable section

universe uV uW uV' uW' uE uE'

section Twist

variable {K : Type uW} [Group K] {K' : Type uW'} [Group K']
variable {Q : Type uV} [Group Q] {Q' : Type uV'} [Group Q']
variable {E : Type uE} [Group E]

/-- Reindex the two end groups of an extension along isomorphisms, keeping
the middle group. -/
def _root_.GroupExtension.twistCoords (S : GroupExtension K E Q)
    (gK : K' ≃* K) (gQ : Q ≃* Q') : GroupExtension K' E Q' where
  inl := S.inl.comp gK.toMonoidHom
  rightHom := gQ.toMonoidHom.comp S.rightHom
  inl_injective := S.inl_injective.comp gK.injective
  range_inl_eq_ker_rightHom := by
    ext e
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨k, rfl⟩
      have hk : S.inl (gK k) ∈ S.rightHom.ker :=
        S.range_inl_eq_ker_rightHom ▸ ⟨gK k, rfl⟩
      rw [MonoidHom.mem_ker] at hk
      rw [hk, map_one]
    · intro he
      have h1 : S.rightHom e = 1 := gQ.injective (by rw [he, map_one])
      have : e ∈ S.inl.range :=
        S.range_inl_eq_ker_rightHom ▸ MonoidHom.mem_ker.mpr h1
      obtain ⟨k, rfl⟩ := this
      exact ⟨gK.symm k, by simp⟩
  rightHom_surjective := gQ.surjective.comp S.rightHom_surjective

@[simp]
theorem _root_.GroupExtension.twistCoords_inl (S : GroupExtension K E Q)
    (gK : K' ≃* K) (gQ : Q ≃* Q') (k : K') :
    (S.twistCoords gK gQ).inl k = S.inl (gK k) :=
  rfl

@[simp]
theorem _root_.GroupExtension.twistCoords_rightHom (S : GroupExtension K E Q)
    (gK : K' ≃* K) (gQ : Q ≃* Q') (e : E) :
    (S.twistCoords gK gQ).rightHom e = gQ (S.rightHom e) :=
  rfl

end Twist

section LemmaOneC

variable {V : Type uV} [AddCommGroup V]
variable {W : Type uW} [AddCommGroup W]
variable {V' : Type uV'} [AddCommGroup V']
variable {W' : Type uW'} [AddCommGroup W']
variable {E : Type uE} [Group E] {E' : Type uE'} [Group E']

/-- **Peterfalvi Appendix III, Lemma 1(c), necessity** (p. 139): if an
isomorphism of central extensions induces `f` on the quotients and `g` on
the kernels, then the square maps are intertwined: `g ∘ q = q' ∘ f`. -/
theorem _root_.GroupExtension.comp_squareMap_eq_of_mulEquiv
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (T : GroupExtension (Multiplicative W') E' (Multiplicative V'))
    (q : V → W) (q' : V' → W')
    (hsqS : ∀ e : E,
      e ^ 2 = S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (hsqT : ∀ e : E',
      e ^ 2 = T.inl (Multiplicative.ofAdd (q' (T.rightHom e).toAdd)))
    (f : V → V') (g : W → W') (Φ : E ≃* E')
    (hinl : ∀ w : W,
      Φ (S.inl (Multiplicative.ofAdd w)) = T.inl (Multiplicative.ofAdd (g w)))
    (hright : ∀ e : E, (T.rightHom (Φ e)).toAdd = f (S.rightHom e).toAdd)
    (v : V) : g (q v) = q' (f v) := by
  obtain ⟨e, he⟩ := S.rightHom_surjective (Multiplicative.ofAdd v)
  have hsq : Φ (e ^ 2) = Φ e ^ 2 := map_pow Φ e 2
  rw [hsqS e, hsqT (Φ e), he, toAdd_ofAdd, hinl] at hsq
  have hcoord := T.inl_injective hsq
  have hW := congrArg (fun z : Multiplicative W' => z.toAdd) hcoord
  simp only [toAdd_ofAdd] at hW
  rw [hW, hright, he, toAdd_ofAdd]

/-- **Peterfalvi Appendix III, Lemma 1(c), sufficiency** (p. 140): given
central extensions of elementary abelian `2`-groups with square maps `q`,
`q'` and isomorphisms `f`, `g` with `g ∘ q = q' ∘ f`, there is an
isomorphism of the middle groups inducing `f` on the quotients and `g` on
the kernels. -/
theorem _root_.GroupExtension.exists_mulEquiv_of_comp_squareMap_eq {n : ℕ}
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (T : GroupExtension (Multiplicative W') E' (Multiplicative V'))
    (hcentralS : S.inl.range ≤ Subgroup.center E)
    (hcentralT : T.inl.range ≤ Subgroup.center E')
    (q : V → W) (q' : V' → W')
    (basis : Module.Basis (Fin n) (ZMod 2) V)
    (hsqS : ∀ e : E,
      e ^ 2 = S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (hsqT : ∀ e : E',
      e ^ 2 = T.inl (Multiplicative.ofAdd (q' (T.rightHom e).toAdd)))
    (f : V ≃+ V') (g : W ≃+ W')
    (hcomp : ∀ v : V, g (q v) = q' (f v)) :
    ∃ Φ : E ≃* E',
      (∀ w : W, Φ (S.inl (Multiplicative.ofAdd w)) =
        T.inl (Multiplicative.ofAdd (g w))) ∧
      ∀ e : E, (T.rightHom (Φ e)).toAdd = f (S.rightHom e).toAdd := by
  -- Transport `T` to an extension of `V` by `W` with square map `q`.
  set T' : GroupExtension (Multiplicative W) E' (Multiplicative V) :=
    T.twistCoords (AddEquiv.toMultiplicative g)
      (AddEquiv.toMultiplicative f.symm) with hT'
  have hcentralT' : T'.inl.range ≤ Subgroup.center E' := by
    rintro x ⟨k, rfl⟩
    exact hcentralT ⟨AddEquiv.toMultiplicative g k, rfl⟩
  have hsqT' : ∀ e : E',
      e ^ 2 = T'.inl (Multiplicative.ofAdd (q (T'.rightHom e).toAdd)) := by
    intro e
    rw [hsqT e]
    have hval : g (q (f.symm (T.rightHom e).toAdd)) =
        q' (T.rightHom e).toAdd := by
      have := hcomp (f.symm (T.rightHom e).toAdd)
      rwa [f.apply_symm_apply] at this
    change T.inl (Multiplicative.ofAdd (q' (T.rightHom e).toAdd)) =
      T.inl (Multiplicative.ofAdd (g (q (f.symm (T.rightHom e).toAdd))))
    rw [hval]
  let equiv := GroupExtension.equivOfCommonSquareMap S T' hcentralS
    hcentralT' q basis hsqS hsqT'
  refine ⟨equiv.toMulEquiv, ?_, ?_⟩
  · intro w
    exact congrFun equiv.inl_comm (Multiplicative.ofAdd w)
  · intro e
    have h1 := congrFun equiv.rightHom_comm e
    have h2 : f.symm (T.rightHom (equiv.toMulEquiv e)).toAdd =
        (S.rightHom e).toAdd :=
      congrArg (fun z : Multiplicative V => z.toAdd) h1
    rw [← h2, f.apply_symm_apply]

end LemmaOneC

section LemmaOneD

variable {V : Type uV} [AddCommGroup V]
variable {W : Type uW} [AddCommGroup W]
variable {E : Type uE} [Group E]
variable (S : GroupExtension (Multiplicative W) E (Multiplicative V))

/-- An automorphism of the middle group of an extension *induces the
identity on both end groups* when it fixes the embedded kernel pointwise
and preserves every quotient coordinate. -/
def _root_.GroupExtension.InducesId (Φ : MulAut E) : Prop :=
  (∀ w : Multiplicative W, Φ (S.inl w) = S.inl w) ∧
    ∀ e : E, S.rightHom (Φ e) = S.rightHom e

/-- The subgroup of `MulAut E` of automorphisms inducing the identity on
both end groups of the extension. -/
def _root_.GroupExtension.inducingIdAuts : Subgroup (MulAut E) where
  carrier := {Φ | S.InducesId Φ}
  one_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro Φ Ψ ⟨hΦ1, hΦ2⟩ ⟨hΨ1, hΨ2⟩
    refine ⟨fun w => ?_, fun e => ?_⟩
    · rw [MulAut.mul_apply, hΨ1, hΦ1]
    · rw [MulAut.mul_apply, hΦ2, hΨ2]
  inv_mem' := by
    rintro Φ ⟨h1, h2⟩
    refine ⟨fun w => ?_, fun e => ?_⟩
    · rw [MulAut.inv_def]
      exact Φ.symm_apply_eq.mpr (h1 w).symm
    · have := h2 (Φ⁻¹ e)
      rw [show Φ (Φ⁻¹ e) = e from Φ.apply_symm_apply e] at this
      exact this.symm

theorem _root_.GroupExtension.mem_inducingIdAuts_iff (Φ : MulAut E) :
    Φ ∈ S.inducingIdAuts ↔ S.InducesId Φ :=
  Iff.rfl

/-- **An automorphism preserving the two ends normalizes `U`.**

If `Ψ` maps the embedded kernel *onto* itself (`Ψ ∘ inl = inl ∘ g` with `g`
surjective) and transforms the quotient coordinate by some `f`
(`rightHom ∘ Ψ = f ∘ rightHom`), then conjugation by `Ψ` preserves the group of
automorphisms inducing the identity on both ends.

No condition on `f` is needed: the quotient half follows by comparing `hright` at
`e` and at `Ψ⁻¹ e`.

Peterfalvi Part II, Ch. III §3, p. 121, step (4) uses this to see `U ⊴ U A`, which
is what makes `A` and `B` complements of `U` there. -/
theorem _root_.GroupExtension.inducingIdAuts_conj_mem (Ψ : MulAut E)
    (g : Multiplicative W → Multiplicative W)
    (f : Multiplicative V → Multiplicative V)
    (hg : Function.Surjective g)
    (hinl : ∀ w : Multiplicative W, Ψ (S.inl w) = S.inl (g w))
    (hright : ∀ e : E, S.rightHom (Ψ e) = f (S.rightHom e))
    {u : MulAut E} (hu : u ∈ S.inducingIdAuts) :
    Ψ * u * Ψ⁻¹ ∈ S.inducingIdAuts := by
  refine ⟨fun w => ?_, fun e => ?_⟩
  · obtain ⟨w', rfl⟩ := hg w
    have h1 : (Ψ⁻¹ : MulAut E) (S.inl (g w')) = S.inl w' := by
      rw [← hinl]
      exact Ψ.symm_apply_apply _
    change Ψ (u ((Ψ⁻¹ : MulAut E) (S.inl (g w')))) = S.inl (g w')
    rw [h1, hu.1 w', hinl]
  · change S.rightHom (Ψ (u ((Ψ⁻¹ : MulAut E) e))) = S.rightHom e
    rw [hright, hu.2]
    have h2 := hright ((Ψ⁻¹ : MulAut E) e)
    rw [show Ψ ((Ψ⁻¹ : MulAut E) e) = e from Ψ.apply_symm_apply e] at h2
    exact h2.symm

open scoped Pointwise in
/-- **A product of subgroups is already a subgroup when one normalizes the other.**

`U · K` is closed under multiplication and inversion as soon as `K ≤ N(U)`, so it
is the subgroup generated by `U` and `K`.

Needed because `Subgroup.normal_mul` asks for normality in the *whole* ambient
group, whereas in Peterfalvi Part II, Ch. III §3, p. 121, step (4) the group `U`
is normalized only by `A` and `B`, not by all of `Aut(S₁)`. -/
theorem _root_.Subgroup.mul_eq_sup_of_le_normalizer {G' : Type*} [Group G']
    {U K : Subgroup G'} (h : K ≤ Subgroup.normalizer (U : Set G')) :
    ((U : Set G') * (K : Set G')) = ((U ⊔ K : Subgroup G') : Set G') := by
  classical
  set S : Subgroup G' :=
    { carrier := (U : Set G') * (K : Set G')
      one_mem' := ⟨1, U.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, k₁, hk₁, rfl⟩ ⟨u₂, hu₂, k₂, hk₂, rfl⟩
        refine ⟨u₁ * (k₁ * u₂ * k₁⁻¹), U.mul_mem hu₁
          ((Subgroup.mem_normalizer_iff.mp (h hk₁) u₂).mp hu₂), k₁ * k₂,
          K.mul_mem hk₁ hk₂, by group⟩
      inv_mem' := by
        rintro _ ⟨u, hu, k, hk, rfl⟩
        refine ⟨k⁻¹ * u⁻¹ * k, ?_, k⁻¹, K.inv_mem hk, by group⟩
        have hmem := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (h hk)) u⁻¹).mp
          (U.inv_mem hu)
        rw [inv_inv] at hmem
        exact hmem } with hS
  have hUS : U ≤ S := fun {u} hu => ⟨u, hu, 1, K.one_mem, mul_one u⟩
  have hKS : K ≤ S := fun {k} hk => ⟨1, U.one_mem, k, hk, one_mul k⟩
  have hle : U ⊔ K ≤ S := sup_le hUS hKS
  refine Set.Subset.antisymm ?_ (fun x hx => hle hx)
  rintro _ ⟨u, hu, k, hk, rfl⟩
  exact Subgroup.mul_mem _ ((le_sup_left : U ≤ U ⊔ K) hu)
    ((le_sup_right : K ≤ U ⊔ K) hk)

/-- **Two homomorphisms differing pointwise by a subgroup have the same product
with it.**

If `(g x)⁻¹ · f x ∈ U` for every `x`, then `U ⊔ f.range = U ⊔ g.range`.  This
upgrades an inclusion of the shape "`B ⊆ U A`" into the equality of products that
the complement form of the Schur–Zassenhaus conjugacy theorem needs — used in
Peterfalvi Part II, Ch. III §3, p. 121, step (4). -/
theorem _root_.Subgroup.sup_range_eq_of_mul_inv_mem {G' : Type*} [Group G']
    {Γ : Type*} [Group Γ] (U : Subgroup G') (f g : Γ →* G')
    (h : ∀ x : Γ, (g x)⁻¹ * f x ∈ U) :
    U ⊔ f.range = U ⊔ g.range := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rintro _ ⟨x, rfl⟩
    have hx : f x = g x * ((g x)⁻¹ * f x) := by group
    rw [hx]
    exact Subgroup.mul_mem _
      ((le_sup_right : g.range ≤ U ⊔ g.range) ⟨x, rfl⟩)
      ((le_sup_left : U ≤ U ⊔ g.range) (h x))
  · rintro _ ⟨x, rfl⟩
    have hx : g x = f x * ((g x)⁻¹ * f x)⁻¹ := by group
    rw [hx]
    exact Subgroup.mul_mem _
      ((le_sup_right : f.range ≤ U ⊔ f.range) ⟨x, rfl⟩)
      ((le_sup_left : U ≤ U ⊔ f.range) (Subgroup.inv_mem _ (h x)))

/-- The `W`-coordinate of an element of the embedded kernel. -/
private noncomputable def kernelCoordinate (x : E) (hx : x ∈ S.inl.range) :
    W :=
  Multiplicative.toAdd ((MonoidHom.ofInjective S.inl_injective).symm ⟨x, hx⟩)

private theorem inl_kernelCoordinate (x : E) (hx : x ∈ S.inl.range) :
    S.inl (Multiplicative.ofAdd (kernelCoordinate S x hx)) = x := by
  simp [kernelCoordinate]

/-- The deviation `Φ e * e⁻¹` of an inducing-the-identity automorphism lies
in the embedded kernel. -/
private theorem deviation_mem (Φ : MulAut E) (hΦ : S.InducesId Φ) (e : E) :
    Φ e * e⁻¹ ∈ S.inl.range := by
  rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
    hΦ.2, mul_inv_cancel]

/-- The deviation only depends on the quotient coordinate. -/
private theorem deviation_eq_of_rightHom_eq (Φ : MulAut E)
    (hΦ : S.InducesId Φ) {e e' : E} (h : S.rightHom e = S.rightHom e') :
    Φ e * e⁻¹ = Φ e' * e'⁻¹ := by
  have hz : e⁻¹ * e' ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, h,
      inv_mul_cancel]
  obtain ⟨w, hw⟩ := hz
  have he' : e' = e * S.inl w := by rw [hw]; group
  rw [he', map_mul, hΦ.1 w, mul_inv_rev]
  group

/-- The deviation is multiplicative (centrality of the kernel). -/
private theorem deviation_mul (hcentral : S.inl.range ≤ Subgroup.center E)
    (Φ : MulAut E) (hΦ : S.InducesId Φ) (e₁ e₂ : E) :
    Φ (e₁ * e₂) * (e₁ * e₂)⁻¹ = (Φ e₁ * e₁⁻¹) * (Φ e₂ * e₂⁻¹) := by
  have hcomm := Subgroup.mem_center_iff.mp
    (hcentral (deviation_mem S Φ hΦ e₂)) e₁⁻¹
  calc Φ (e₁ * e₂) * (e₁ * e₂)⁻¹
      = Φ e₁ * ((Φ e₂ * e₂⁻¹) * e₁⁻¹) := by rw [map_mul, mul_inv_rev]; group
    _ = Φ e₁ * (e₁⁻¹ * (Φ e₂ * e₂⁻¹)) := by rw [← hcomm]
    _ = (Φ e₁ * e₁⁻¹) * (Φ e₂ * e₂⁻¹) := by group

/-- A section of the quotient map. -/
private noncomputable def sect (v : V) : E :=
  Function.surjInv S.rightHom_surjective (Multiplicative.ofAdd v)

private theorem rightHom_sect (v : V) :
    S.rightHom (sect S v) = Multiplicative.ofAdd v :=
  Function.surjInv_eq S.rightHom_surjective (Multiplicative.ofAdd v)

/-- The underlying function of the induced homomorphism `V → W`. -/
private noncomputable def inducesIdFun (Φ : MulAut E) (hΦ : S.InducesId Φ)
    (v : V) : W :=
  kernelCoordinate S (Φ (sect S v) * (sect S v)⁻¹) (deviation_mem S Φ hΦ _)

/-- The characterizing property: the embedded value of `inducesIdFun` at the
quotient coordinate of `e` is the deviation of `e`. -/
private theorem inl_inducesIdFun (Φ : MulAut E) (hΦ : S.InducesId Φ)
    (e : E) :
    S.inl (Multiplicative.ofAdd
      (inducesIdFun S Φ hΦ (S.rightHom e).toAdd)) = Φ e * e⁻¹ := by
  rw [inducesIdFun, inl_kernelCoordinate]
  exact deviation_eq_of_rightHom_eq S Φ hΦ (by rw [rightHom_sect, ofAdd_toAdd])

/-- **Peterfalvi Appendix III, Lemma 1(d)**, forward map (pp. 139–140): an
automorphism inducing the identity on both end groups determines an
additive homomorphism `V → W` measuring its deviation. -/
noncomputable def _root_.GroupExtension.inducesIdHom
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (Φ : MulAut E) (hΦ : S.InducesId Φ) : V →+ W where
  toFun := inducesIdFun S Φ hΦ
  map_zero' := by
    apply Multiplicative.ofAdd.injective
    apply S.inl_injective
    have h1 : S.rightHom (1 : E) = Multiplicative.ofAdd (0 : V) := by
      simp
    have := inl_inducesIdFun S Φ hΦ (1 : E)
    rw [h1, toAdd_ofAdd] at this
    rw [this]
    simp
  map_add' := by
    intro v₁ v₂
    apply Multiplicative.ofAdd.injective
    apply S.inl_injective
    have hr : S.rightHom (sect S v₁ * sect S v₂) =
        Multiplicative.ofAdd (v₁ + v₂) := by
      rw [map_mul, rightHom_sect, rightHom_sect, ← ofAdd_add]
    have h12 := inl_inducesIdFun S Φ hΦ (sect S v₁ * sect S v₂)
    rw [hr, toAdd_ofAdd] at h12
    have h1 := inl_inducesIdFun S Φ hΦ (sect S v₁)
    rw [rightHom_sect, toAdd_ofAdd] at h1
    have h2 := inl_inducesIdFun S Φ hΦ (sect S v₂)
    rw [rightHom_sect, toAdd_ofAdd] at h2
    rw [h12, deviation_mul S hcentral Φ hΦ, ← h1, ← h2, ← map_mul, ← ofAdd_add]

/-- The automorphism is recovered from its deviation homomorphism. -/
theorem _root_.GroupExtension.inducesIdHom_spec
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (Φ : MulAut E) (hΦ : S.InducesId Φ) (e : E) :
    Φ e = S.inl (Multiplicative.ofAdd
      (S.inducesIdHom hcentral Φ hΦ (S.rightHom e).toAdd)) * e := by
  have h := inl_inducesIdFun S Φ hΦ e
  change Φ e = S.inl (Multiplicative.ofAdd
    (inducesIdFun S Φ hΦ (S.rightHom e).toAdd)) * e
  rw [h]
  group

/-- **Lemma 1(d)**, reverse map: an additive homomorphism `h : V → W` gives
an automorphism `e ↦ ι(h(ē)) e` of the middle group. -/
def _root_.GroupExtension.autOfHom
    (hcentral : S.inl.range ≤ Subgroup.center E) (h : V →+ W) : MulAut E where
  toFun e := S.inl (Multiplicative.ofAdd (h (S.rightHom e).toAdd)) * e
  invFun e := (S.inl (Multiplicative.ofAdd (h (S.rightHom e).toAdd)))⁻¹ * e
  left_inv e := by
    simp only [map_mul, GroupExtension.rightHom_inl, one_mul]
    group
  right_inv e := by
    simp only [map_mul, map_inv, GroupExtension.rightHom_inl, inv_one,
      one_mul]
    group
  map_mul' e₁ e₂ := by
    have hcomm := Subgroup.mem_center_iff.mp
      (hcentral ⟨Multiplicative.ofAdd (h (S.rightHom e₂).toAdd), rfl⟩) e₁
    simp only [map_mul, toAdd_mul, map_add, ofAdd_add]
    calc S.inl (Multiplicative.ofAdd (h (S.rightHom e₁).toAdd)) *
          S.inl (Multiplicative.ofAdd (h (S.rightHom e₂).toAdd)) * (e₁ * e₂)
        = S.inl (Multiplicative.ofAdd (h (S.rightHom e₁).toAdd)) *
            (S.inl (Multiplicative.ofAdd (h (S.rightHom e₂).toAdd)) * e₁) *
            e₂ := by group
      _ = S.inl (Multiplicative.ofAdd (h (S.rightHom e₁).toAdd)) *
            (e₁ * S.inl (Multiplicative.ofAdd (h (S.rightHom e₂).toAdd))) *
            e₂ := by rw [hcomm]
      _ = S.inl (Multiplicative.ofAdd (h (S.rightHom e₁).toAdd)) * e₁ *
            (S.inl (Multiplicative.ofAdd (h (S.rightHom e₂).toAdd)) * e₂) :=
          by group

@[simp]
theorem _root_.GroupExtension.autOfHom_apply
    (hcentral : S.inl.range ≤ Subgroup.center E) (h : V →+ W) (e : E) :
    S.autOfHom hcentral h e =
      S.inl (Multiplicative.ofAdd (h (S.rightHom e).toAdd)) * e :=
  rfl

/-- `autOfHom` as a homomorphism from the additive group `Hom(V, W)`. -/
noncomputable def _root_.GroupExtension.autOfHomHom
    (hcentral : S.inl.range ≤ Subgroup.center E) :
    Multiplicative (V →+ W) →* MulAut E :=
  MonoidHom.mk' (fun h => S.autOfHom hcentral h.toAdd) (by
    intro h₁ h₂
    ext e
    have hr : S.rightHom
        (S.inl (Multiplicative.ofAdd (h₂.toAdd (S.rightHom e).toAdd)) * e) =
        S.rightHom e := by
      rw [map_mul, GroupExtension.rightHom_inl, one_mul]
    simp only [MulAut.mul_apply, GroupExtension.autOfHom_apply, hr]
    change S.inl (Multiplicative.ofAdd ((h₁.toAdd + h₂.toAdd)
      (S.rightHom e).toAdd)) * e = _
    rw [AddMonoidHom.add_apply, ofAdd_add, map_mul]
    group)

theorem _root_.GroupExtension.autOfHomHom_injective
    (hcentral : S.inl.range ≤ Subgroup.center E) :
    Function.Injective (S.autOfHomHom hcentral) := by
  intro h₁ h₂ hEq
  apply Multiplicative.toAdd.injective
  ext v
  have := congrArg (fun Φ : MulAut E => Φ (sect S v)) hEq
  simp only [GroupExtension.autOfHomHom, MonoidHom.mk'_apply,
    GroupExtension.autOfHom_apply, rightHom_sect, toAdd_ofAdd] at this
  have hinl := mul_right_cancel this
  exact Multiplicative.ofAdd.injective (S.inl_injective hinl)

theorem _root_.GroupExtension.range_autOfHomHom
    (hcentral : S.inl.range ≤ Subgroup.center E) :
    (S.autOfHomHom hcentral).range = S.inducingIdAuts := by
  ext Φ
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun w => ?_, fun e => ?_⟩
    · simp only [GroupExtension.autOfHomHom, MonoidHom.mk'_apply,
        GroupExtension.autOfHom_apply, GroupExtension.rightHom_inl,
        toAdd_one, map_zero, ofAdd_zero, map_one, one_mul]
    · simp only [GroupExtension.autOfHomHom, MonoidHom.mk'_apply,
        GroupExtension.autOfHom_apply, map_mul,
        GroupExtension.rightHom_inl, one_mul]
  · intro hΦ
    refine ⟨Multiplicative.ofAdd (S.inducesIdHom hcentral Φ hΦ), ?_⟩
    ext e
    simp only [GroupExtension.autOfHomHom, MonoidHom.mk'_apply,
      GroupExtension.autOfHom_apply, toAdd_ofAdd]
    exact (S.inducesIdHom_spec hcentral Φ hΦ e).symm

/-- **Peterfalvi Appendix III, Lemma 1(d)** (pp. 139–140): for a central
extension `W → E → V`, the automorphisms of `E` inducing the identity on
both `V` and `W` form a group isomorphic to the additive group
`Hom(V, W)`. -/
noncomputable def _root_.GroupExtension.inducingIdAutsEquivHom
    (hcentral : S.inl.range ≤ Subgroup.center E) :
    Multiplicative (V →+ W) ≃* S.inducingIdAuts :=
  (MonoidHom.ofInjective (S.autOfHomHom_injective hcentral)).trans
    (MulEquiv.subgroupCongr (S.range_autOfHomHom hcentral))

/-- The inducing-the-identity automorphism group is an elementary abelian
`2`-group when the kernel is one. -/
theorem _root_.GroupExtension.isElementaryAbelian_inducingIdAuts
    [Module (ZMod 2) W] (hcentral : S.inl.range ≤ Subgroup.center E) :
    IsElementaryAbelian 2 S.inducingIdAuts := by
  refine IsElementaryAbelian.of_mulEquiv
    (S.inducingIdAutsEquivHom hcentral) ⟨fun x y => ?_, fun x => ?_⟩
  · apply Multiplicative.toAdd.injective
    exact add_comm _ _
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, ← two_smul (ZMod 2),
      show (2 : ZMod 2) = 0 by decide, zero_smul]

end LemmaOneD

end

end OddOrder.GroupTheory
