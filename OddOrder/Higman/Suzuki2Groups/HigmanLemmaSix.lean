/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanSquareMap
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralDegreeThree
import OddOrder.GroupTheory.FixedPointFreeOrderThree

/-!
# Higman's Lemma 6

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), section 4,
pp. 85--86, Lemma 6.

Higman's first step is a kernel comparison.  If a power of the cyclic actor
is the identity on `L₂` and `L₃`, then it is already the identity on `L₁`.
Indeed the image of `1 - η` on `L₁` is invariant.  Equivariance makes the
actual bracket `L₂ × L₁ → L₃` vanish on that image.  Irreducibility says the
image is zero or all of `L₁`; the latter would make the full-span bracket
zero and hence force `L₃ = 0`.

The later sections establish Higman's odd-dimension reduction through the
order-three fixed-point-free theorem, connect `[u²,u] = 1` to the
triple-commutator sum from p. 86, and eliminate both its distinct- and
repeated-weight terms. The remaining frontier is the final contradiction.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open Module
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open scoped BigOperators commutatorElement IsMulCommutative TensorProduct

universe uK uH uC uMain uV uW uX

local instance instLemmaSixLowerCentralLayerIsMulCommutative
    (H : Type uH) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  ⟨⟨(lowerCentralLayer_isElementaryAbelian H i).1⟩⟩

noncomputable local instance instLemmaSixLowerCentralLayerZModTwoModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-! ## Equality of the three actor kernels -/

/-- **Higman Lemma 6, first paragraph (p. 85).**

For a commutative actor, an element acting trivially on `L₂` and `L₃` also
acts trivially on an irreducible `L₁`, provided `L₃` is nonzero.  The proof
uses the actual mixed commutator and its full-span theorem. -/
theorem lowerCentralLayerZero_action_eq_one_of_second_third_action_eq_one
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 2))]
    (c : C)
    (hsecond : lowerCentralLayerRepresentation phi 1 c = 1)
    (hthird : lowerCentralLayerRepresentation phi 2 c = 1) :
    lowerCentralLayerRepresentation phi 0 c = 1 := by
  let rho₀ := lowerCentralLayerRepresentation phi 0
  let rho₁ := lowerCentralLayerRepresentation phi 1
  let rho₂ := lowerCentralLayerRepresentation phi 2
  let gamma := lowerCentralDegreeThreeCommutatorBilinear H
  change Representation.IsIrreducible rho₀ at hirr
  change rho₁ c = 1 at hsecond
  change rho₂ c = 1 at hthird
  change rho₀ c = 1
  have hcomm : ∀ (g : C) (v : Additive (lowerCentralLayer H 0)),
      rho₀ c (rho₀ g v) = rho₀ g (rho₀ c v) := by
    intro g v
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ← map_mul, ← map_mul, mul_comm]
  let d : Additive (lowerCentralLayer H 0) →ₗ[ZMod 2]
      Additive (lowerCentralLayer H 0) :=
    LinearMap.id - rho₀ c
  let dInter : Representation.IntertwiningMap rho₀ rho₀ :=
    d.intertwiningMap_of_isIntertwiningMap rho₀ rho₀ (by
      intro g v
      dsimp only [d]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
      rw [hcomm])
  let S : Subrepresentation rho₀ := dInter.range
  letI : Representation.IsIrreducible rho₀ := hirr
  rcases eq_bot_or_eq_top S with hS | hS
  · have hdRange : LinearMap.range d = ⊥ := by
      have h := congrArg Subrepresentation.toSubmodule hS
      change LinearMap.range d = ⊥ at h
      exact h
    have hd : d = 0 := LinearMap.range_eq_bot.mp hdRange
    ext v
    have hv := LinearMap.congr_fun hd v
    change v - rho₀ c v = 0 at hv
    simpa using (sub_eq_zero.mp hv).symm
  · have hdRange : LinearMap.range d = ⊤ := by
      have h := congrArg Subrepresentation.toSubmodule hS
      change LinearMap.range d = ⊤ at h
      exact h
    have hzero : ∀ (y : Additive (lowerCentralLayer H 1))
        (x : Additive (lowerCentralLayer H 0)), gamma y x = 0 := by
      intro y x
      have hx : x ∈ LinearMap.range d := by
        rw [hdRange]
        exact Submodule.mem_top
      obtain ⟨w, rfl⟩ := hx
      have heq :=
        lowerCentralDegreeThreeCommutatorBilinear_equivariant_representation
          phi c y w
      change rho₂ c (gamma y w) =
        gamma (rho₁ c y) (rho₀ c w) at heq
      rw [hsecond, hthird] at heq
      simp only [Module.End.one_apply] at heq
      change gamma y (w - rho₀ c w) = 0
      rw [map_sub, heq, sub_self]
    have hspan := lowerCentralDegreeThreeCommutatorBilinear_span_eq_top H
    change Submodule.span (ZMod 2)
        (Set.range fun z :
          Additive (lowerCentralLayer H 1) ×
            Additive (lowerCentralLayer H 0) => gamma z.1 z.2) = ⊤ at hspan
    have hle : Submodule.span (ZMod 2)
        (Set.range fun z :
          Additive (lowerCentralLayer H 1) ×
            Additive (lowerCentralLayer H 0) => gamma z.1 z.2) ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨y, x⟩, rfl⟩
      change gamma y x ∈
        (⊥ : Submodule (ZMod 2) (Additive (lowerCentralLayer H 2)))
      rw [hzero]
      exact Submodule.zero_mem _
    have htopbot :
        (⊤ : Submodule (ZMod 2) (Additive (lowerCentralLayer H 2))) = ⊥ :=
      le_bot_iff.mp (hspan ▸ hle)
    exact (bot_ne_top htopbot.symm).elim

/-- **Higman Lemma 6, first paragraph (p. 85), kernel form.**

The common kernel of the actions on `L₂` and `L₃` is contained in the
kernel of the action on `L₁`. -/
theorem lowerCentralLayerRepresentation_ker_inf_le_ker_zero
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 2))] :
    (lowerCentralLayerRepresentation phi 1).ker ⊓
        (lowerCentralLayerRepresentation phi 2).ker ≤
      (lowerCentralLayerRepresentation phi 0).ker := by
  intro c hc
  exact lowerCentralLayerZero_action_eq_one_of_second_third_action_eq_one
    phi hirr c hc.1 hc.2

/-- Under an equivariant isomorphism `L₂ ≃ L₃`, faithfulness on `L₁`
forces faithfulness on `L₂`.  This is the kernel consequence used immediately
after the first paragraph of Higman's Lemma 6. -/
theorem lowerCentralLayerOneRepresentation_injective_of_equivariant_linearEquiv
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 1))]
    (e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer H 2))
    (hequiv : ∀ c v,
      e (lowerCentralLayerRepresentation phi 1 c v) =
        lowerCentralLayerRepresentation phi 2 c (e v)) :
    Function.Injective (lowerCentralLayerRepresentation phi 1) := by
  let rho₀ := lowerCentralLayerRepresentation phi 0
  let rho₁ := lowerCentralLayerRepresentation phi 1
  let rho₂ := lowerCentralLayerRepresentation phi 2
  change Representation.IsIrreducible rho₀ at hirr
  change Function.Injective rho₀ at hfaith
  change ∀ c v, e (rho₁ c v) = rho₂ c (e v) at hequiv
  change Function.Injective rho₁
  letI : Nontrivial (Additive (lowerCentralLayer H 2)) :=
    e.symm.toEquiv.nontrivial
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro c hc
  change rho₁ c = 1 at hc
  have hc₂ : rho₂ c = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    have h := hequiv c v
    rw [hc] at h
    simpa only [Module.End.one_apply] using h.symm
  have hc₀ : rho₀ c = 1 :=
    lowerCentralLayerZero_action_eq_one_of_second_third_action_eq_one
      phi hirr c hc hc₂
  apply hfaith
  simpa only [map_one] using hc₀

/-- **Higman Lemma 6, dimension step (p. 85).**

If `L₂` and `L₃` are equivariantly isomorphic, the kernel comparison makes
the transitive action on `L₂#` faithful.  The faithful irreducible action on
`L₁` and the faithful transitive action on `L₂` then have the same dimension
by the Singer-field Frobenius-period argument. -/
theorem lowerCentralLayerZero_finrank_eq_one_of_equivariant_linearEquiv
    {H C : Type uMain} [Group H] [Finite H]
    [CommGroup C] [IsCyclic C] [Finite C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 1))]
    (htrans : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w)
    (e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer H 2))
    (hequiv : ∀ c v,
      e (lowerCentralLayerRepresentation phi 1 c v) =
        lowerCentralLayerRepresentation phi 2 c (e v)) :
    Module.finrank (ZMod 2) (Additive (lowerCentralLayer H 0)) =
      Module.finrank (ZMod 2) (Additive (lowerCentralLayer H 1)) := by
  have hfaithOne : Function.Injective
      (lowerCentralLayerRepresentation phi 1) :=
    lowerCentralLayerOneRepresentation_injective_of_equivariant_linearEquiv
      phi hirr hfaith e hequiv
  exact finrank_eq_of_faithful_irreducible_and_faithful_transitive_nonzero
    (lowerCentralLayerRepresentation phi 0)
    (lowerCentralLayerRepresentation phi 1)
    hirr hfaith hfaithOne htrans

/-! ## The class-three quotient -/

/-- If squares in one lower-central term lie in the next term, then the same
holds one step farther down the lower-central series.

For a generator `[x,y]` of `H_(i+1)`, the identity
`[x²,y] = [x,[x,y]] [x,y]²` shows that its square lies in `H_(i+2)`:
the first factor is already one step deeper, while `x² ∈ H_(i+1)` puts the
left-hand side there as well.  Closure under products is checked in the
abelian factor `H_(i+1)/H_(i+2)`. -/
theorem lowerCentralTerm_succ_squares_le_of_squares_le
    (H : Type uH) [Group H] (i : ℕ)
    (hSq : (Agemo (↥(lowerCentralTerm H i)) 2 1).map
      (lowerCentralTerm H i).subtype ≤ lowerCentralTerm H (i + 1)) :
    (Agemo (↥(lowerCentralTerm H (i + 1))) 2 1).map
      (lowerCentralTerm H (i + 1)).subtype ≤ lowerCentralTerm H (i + 2) := by
  let S : Set H :=
    {c | ∃ x ∈ lowerCentralTerm H i,
      ∃ y ∈ (⊤ : Subgroup H), ⁅x, y⁆ = c}
  have hterm : lowerCentralTerm H (i + 1) = Subgroup.closure S := by
    rfl
  have hsquares : ∀ z ∈ lowerCentralTerm H (i + 1),
      z ^ 2 ∈ lowerCentralTerm H (i + 2) := by
    intro z hz
    have hz' : z ∈ Subgroup.closure S := hterm ▸ hz
    refine Subgroup.closure_induction
      (p := fun z _ => z ^ 2 ∈ lowerCentralTerm H (i + 2)) ?_ ?_ ?_ ?_ hz'
    · intro c hc
      rcases hc with ⟨x, hx, y, hy, rfl⟩
      have hxSq : x ^ 2 ∈ lowerCentralTerm H (i + 1) := by
        apply hSq
        apply Subgroup.mem_map.mpr
        refine ⟨(⟨x, hx⟩ : lowerCentralTerm H i) ^ 2, ?_, ?_⟩
        · simpa using (Agemo.mem_of_eq_pow
            (G := ↥(lowerCentralTerm H i)) (p := 2) (n := 1)
            (⟨x, hx⟩ : lowerCentralTerm H i))
        · simp
      have hxy : ⁅x, y⁆ ∈ lowerCentralTerm H (i + 1) := by
        change ⁅x, y⁆ ∈ ⁅lowerCentralTerm H i, (⊤ : Subgroup H)⁆
        exact Subgroup.commutator_mem_commutator hx hy
      have hleft : ⁅x ^ 2, y⁆ ∈ lowerCentralTerm H (i + 2) := by
        change ⁅x ^ 2, y⁆ ∈
          ⁅lowerCentralTerm H (i + 1), (⊤ : Subgroup H)⁆
        exact Subgroup.commutator_mem_commutator hxSq hy
      have hconj : ⁅x, ⁅x, y⁆⁆ ∈ lowerCentralTerm H (i + 2) := by
        have hmem : ⁅x, ⁅x, y⁆⁆ ∈
            ⁅(⊤ : Subgroup H), lowerCentralTerm H (i + 1)⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hxy
        rw [Subgroup.commutator_comm] at hmem
        exact hmem
      have hid : ⁅x, y⁆ ^ 2 = ⁅x, ⁅x, y⁆⁆⁻¹ * ⁅x ^ 2, y⁆ := by
        rw [pow_two x, commutatorElement_mul_left_eq_conj_mul]
        simp only [commutatorElement_def, pow_two]
        group
      rw [hid]
      exact (lowerCentralTerm H (i + 2)).mul_mem
        ((lowerCentralTerm H (i + 2)).inv_mem hconj) hleft
    · simp
    · intro a b ha hb haSq hbSq
      let N := lowerCentralTerm H (i + 2)
      letI : N.Normal := by
        dsimp [N, lowerCentralTerm]
        infer_instance
      let q : H →* H ⧸ N := QuotientGroup.mk' N
      have habN : ⁅a, b⁆ ∈ N := by
        change ⁅a, b⁆ ∈ lowerCentralTerm H (i + 2)
        change ⁅a, b⁆ ∈
          ⁅lowerCentralTerm H (i + 1), (⊤ : Subgroup H)⁆
        exact Subgroup.commutator_mem_commutator
          (hterm ▸ ha) (Subgroup.mem_top b)
      have hab : Commute (q a) (q b) := by
        apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr habN
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((a * b) ^ 2) = 1
      rw [map_pow, map_mul, hab.mul_pow]
      have haOne : q a ^ 2 = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr haSq
      have hbOne : q b ^ 2 = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr hbSq
      rw [haOne, hbOne, one_mul]
    · intro a _ha haSq
      simpa [inv_pow] using (lowerCentralTerm H (i + 2)).inv_mem haSq
  rw [Subgroup.map_le_iff_le_comap, Agemo, Subgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  change (x : H) ^ 2 ∈ lowerCentralTerm H (i + 2)
  exact hsquares (x : H) x.2

local instance instLemmaSixLowerCentralTermThreeNormal
    (H : Type uH) [Group H] :
    (lowerCentralTerm H 3).Normal := by
  dsimp [lowerCentralTerm]
  infer_instance

/-- Fixed-point-freeness on Higman's first three elementary layers descends
directly to `H/H₄`, once their square kernels are the consecutive
lower-central terms.

No coprime fixed-point lifting is needed here.  If a coset of `x` is fixed,
then `φ(a)x · z = x` for some `z ∈ H₄`.  The same relation fixes the
classes of `x` successively in `L₁`, `L₂`, and `L₃`, forcing
`x ∈ H₂`, then `H₃`, and finally `H₄`. -/
theorem classThreeQuotient_fixedPointFree_of_lowerCentralLayers
    {A : Type uC} {H : Type uH} [Group A] [Group H]
    (phi : A →* MulAut H) (a : A)
    (hK₀ : lowerCentralLayerKernelInAmbient H 0 = lowerCentralTerm H 1)
    (hK₁ : lowerCentralLayerKernelInAmbient H 1 = lowerCentralTerm H 2)
    (hK₂ : lowerCentralLayerKernelInAmbient H 2 = lowerCentralTerm H 3)
    (hfree₀ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 0 a))
    (hfree₁ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 1 a))
    (hfree₂ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 2 a)) :
    MonoidHom.FixedPointFree
      ((IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a) := by
  intro q hq
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralTerm H 3) q
  change QuotientGroup.mk' (lowerCentralTerm H 3) ((phi a) x) =
    QuotientGroup.mk' (lowerCentralTerm H 3) x at hq
  obtain ⟨z, hz₃, hrel⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := lowerCentralTerm H 3)).mp hq
  have hzTerm (i : ℕ) (hi : i ≤ 3) : z ∈ lowerCentralTerm H i :=
    (show (⊤ : Subgroup H).lowerCentralSeries 3 ≤
        (⊤ : Subgroup H).lowerCentralSeries i from
      (⊤ : Subgroup H).lowerCentralSeries_antitone hi) hz₃
  have layerFix (i : ℕ) (hi : i ≤ 3) (hx : x ∈ lowerCentralTerm H i)
      (hzK : z ∈ lowerCentralLayerKernelInAmbient H i) :
      lowerCentralLayerAction phi i a
          (QuotientGroup.mk' (lowerCentralLayerKernel H i) ⟨x, hx⟩) =
        QuotientGroup.mk' (lowerCentralLayerKernel H i) ⟨x, hx⟩ := by
    rw [lowerCentralLayerAction_apply_mk]
    apply (QuotientGroup.mk'_eq_mk'
      (N := lowerCentralLayerKernel H i)).mpr
    let zi : lowerCentralTerm H i := ⟨z, hzTerm i hi⟩
    have hzi : zi ∈ lowerCentralLayerKernel H i := by
      have : zi ∈ (lowerCentralLayerKernelInAmbient H i).subgroupOf
          (lowerCentralTerm H i) := hzK
      rwa [lowerCentralLayerKernelInAmbient_subgroupOf] at this
    refine ⟨zi, hzi, ?_⟩
    apply Subtype.ext
    exact hrel
  have hx₀ : x ∈ lowerCentralTerm H 0 := by
    simp [lowerCentralTerm]
  have hzK₀ : z ∈ lowerCentralLayerKernelInAmbient H 0 := by
    rw [hK₀]
    exact hzTerm 1 (by omega)
  have hxKer₀ : (⟨x, hx₀⟩ : lowerCentralTerm H 0) ∈
      lowerCentralLayerKernel H 0 :=
    (QuotientGroup.eq_one_iff _).mp
      (hfree₀ _ (layerFix 0 (by omega) hx₀ hzK₀))
  have hxK₀ : x ∈ lowerCentralLayerKernelInAmbient H 0 :=
    ⟨⟨x, hx₀⟩, hxKer₀, rfl⟩
  have hx₁ : x ∈ lowerCentralTerm H 1 := by
    rwa [hK₀] at hxK₀
  have hzK₁ : z ∈ lowerCentralLayerKernelInAmbient H 1 := by
    rw [hK₁]
    exact hzTerm 2 (by omega)
  have hxKer₁ : (⟨x, hx₁⟩ : lowerCentralTerm H 1) ∈
      lowerCentralLayerKernel H 1 :=
    (QuotientGroup.eq_one_iff _).mp
      (hfree₁ _ (layerFix 1 (by omega) hx₁ hzK₁))
  have hxK₁ : x ∈ lowerCentralLayerKernelInAmbient H 1 :=
    ⟨⟨x, hx₁⟩, hxKer₁, rfl⟩
  have hx₂ : x ∈ lowerCentralTerm H 2 := by
    rwa [hK₁] at hxK₁
  have hzK₂ : z ∈ lowerCentralLayerKernelInAmbient H 2 := by
    rw [hK₂]
    exact hzTerm 3 (by omega)
  have hxKer₂ : (⟨x, hx₂⟩ : lowerCentralTerm H 2) ∈
      lowerCentralLayerKernel H 2 :=
    (QuotientGroup.eq_one_iff _).mp
      (hfree₂ _ (layerFix 2 (by omega) hx₂ hzK₂))
  have hxK₂ : x ∈ lowerCentralLayerKernelInAmbient H 2 :=
    ⟨⟨x, hx₂⟩, hxKer₂, rfl⟩
  apply (QuotientGroup.eq_one_iff x).mpr
  rwa [hK₂] at hxK₂

/-- Higman's hypothesis `H² = H₂` propagates down the lower-central series,
so fixed-point-freeness on `L₁,L₂,L₃` gives a fixed-point-free action on
`H/H₄`. -/
theorem classThreeQuotient_fixedPointFree_of_agemo_eq
    {A : Type uC} {H : Type uH} [Group A] [Group H]
    (phi : A →* MulAut H) (a : A)
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    (hfree₀ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 0 a))
    (hfree₁ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 1 a))
    (hfree₂ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 2 a)) :
    MonoidHom.FixedPointFree
      ((IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a) := by
  have hSq₀ : LowerCentralSquaresLieInSecond H :=
    lowerCentralSquaresLieInSecond_of_agemo_eq H hAgemo
  have hSq₁ :
      (Agemo (↥(lowerCentralTerm H 1)) 2 1).map
          (lowerCentralTerm H 1).subtype ≤ lowerCentralTerm H 2 := by
    simpa using lowerCentralTerm_succ_squares_le_of_squares_le H 0 hSq₀
  have hSq₂ :
      (Agemo (↥(lowerCentralTerm H 2)) 2 1).map
          (lowerCentralTerm H 2).subtype ≤ lowerCentralTerm H 3 := by
    simpa using lowerCentralTerm_succ_squares_le_of_squares_le H 1 hSq₁
  apply classThreeQuotient_fixedPointFree_of_lowerCentralLayers phi a
  · exact lowerCentralLayerKernelInAmbient_zero_eq_of_squares_le H hSq₀
  · rw [lowerCentralLayerKernelInAmbient_eq, sup_eq_right.mpr hSq₁]
  · rw [lowerCentralLayerKernelInAmbient_eq, sup_eq_right.mpr hSq₂]
  · exact hfree₀
  · exact hfree₁
  · exact hfree₂

/-- The fourth lower-central term vanishes in `H/H₄`. -/
theorem classThreeQuotient_lowerCentralSeries_three_eq_bot
    (H : Type uH) [Group H] :
    (⊤ : Subgroup (H ⧸ lowerCentralTerm H 3)).lowerCentralSeries 3 = ⊥ := by
  rw [← Subgroup.map_top_of_surjective
      (QuotientGroup.mk' (lowerCentralTerm H 3))
      (QuotientGroup.mk'_surjective _),
    ← Subgroup.map_lowerCentralSeries]
  change (lowerCentralTerm H 3).map
      (QuotientGroup.mk' (lowerCentralTerm H 3)) = ⊥
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- If Higman's third layer `L₃` is nontrivial, then the third
lower-central term of `H/H₄` is nontrivial. -/
theorem classThreeQuotient_lowerCentralSeries_two_ne_bot
    (H : Type uH) [Group H]
    [Nontrivial (lowerCentralLayer H 2)] :
    (⊤ : Subgroup (H ⧸ lowerCentralTerm H 3)).lowerCentralSeries 2 ≠ ⊥ := by
  rw [← Subgroup.map_top_of_surjective
      (QuotientGroup.mk' (lowerCentralTerm H 3))
      (QuotientGroup.mk'_surjective _),
    ← Subgroup.map_lowerCentralSeries]
  change (lowerCentralTerm H 2).map
      (QuotientGroup.mk' (lowerCentralTerm H 3)) ≠ ⊥
  rw [ne_eq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  intro hle
  have hnextTop :
      (lowerCentralTerm H 3).subgroupOf (lowerCentralTerm H 2) = ⊤ := by
    apply top_unique
    intro x _
    exact hle x.2
  have hkernelTop : lowerCentralLayerKernel H 2 = ⊤ := by
    rw [lowerCentralLayerKernel, hnextTop, sup_top_eq]
  exact (QuotientGroup.nontrivial_iff.mp (by infer_instance)) hkernelTop

/-- Higman's quotient `H/H₄` has nilpotency class exactly three whenever
`L₃` is nontrivial. -/
theorem classThreeQuotient_nilpotencyClass_eq_three
    (H : Type uH) [Group H]
    [Nontrivial (lowerCentralLayer H 2)] :
    Group.nilpotencyClass (H ⧸ lowerCentralTerm H 3) = 3 := by
  letI : Group.IsNilpotent (H ⧸ lowerCentralTerm H 3) :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr
      ⟨3, classThreeQuotient_lowerCentralSeries_three_eq_bot H⟩
  have hle : Group.nilpotencyClass (H ⧸ lowerCentralTerm H 3) ≤ 3 :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
      (classThreeQuotient_lowerCentralSeries_three_eq_bot H)
  have hnle : ¬ Group.nilpotencyClass (H ⧸ lowerCentralTerm H 3) ≤ 2 := by
    intro hc
    exact classThreeQuotient_lowerCentralSeries_two_ne_bot H
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc)
  exact le_antisymm hle (Nat.succ_le_iff.mpr (lt_of_not_ge hnle))

/-- **Higman Lemma 6, parity-step contradiction (p. 85).**

Under `H² = H₂`, an operator which is fixed-point-free on `L₁,L₂,L₃`
is fixed-point-free on `H/H₄`.  If its induced automorphism has order
three, Neumann's theorem makes that quotient class at most two, contradicting
the nontrivial third layer. -/
theorem classThreeQuotientAction_orderOf_ne_three
    {A : Type uC} {H : Type uH} [Group A] [Group H] [Finite H]
    (phi : A →* MulAut H) (a : A)
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    [Nontrivial (lowerCentralLayer H 2)]
    (hfree₀ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 0 a))
    (hfree₁ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 1 a))
    (hfree₂ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 2 a)) :
    orderOf ((IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a) ≠ 3 := by
  intro horder
  have hfree :=
    classThreeQuotient_fixedPointFree_of_agemo_eq
      phi a hAgemo hfree₀ hfree₁ hfree₂
  have hclassTwo :=
    lowerCentralSeries_two_eq_bot_of_fixedPointFree_orderOf_eq_three
      ((IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a)
      hfree horder
  exact classThreeQuotient_lowerCentralSeries_two_ne_bot H hclassTwo

/-! ## The odd-dimension reduction -/

/-- The multiplicative lower-central-layer action is fixed-point-free iff
its associated linear map has no nonzero fixed vector. -/
theorem lowerCentralLayerAction_fixedPointFree_iff
    {H : Type uH} {C : Type uC} [Group H] [Group C]
    (phi : C →* MulAut H) (i : Nat) (a : C) :
    MonoidHom.FixedPointFree (lowerCentralLayerAction phi i a) ↔
      ∀ v : Additive (lowerCentralLayer H i),
        lowerCentralLayerRepresentation phi i a v = v → v = 0 := by
  constructor
  · intro hfree v hv
    apply Additive.toMul.injective
    change Additive.toMul v = 1
    apply hfree
    apply Additive.ofMul.injective
    calc
      Additive.ofMul
          (lowerCentralLayerAction phi i a (Additive.toMul v)) =
          lowerCentralLayerRepresentation phi i a
            (Additive.ofMul (Additive.toMul v)) :=
        (lowerCentralLayerRepresentation_apply
          phi i a (Additive.toMul v)).symm
      _ = v := by simpa only [ofMul_toMul] using hv
  · intro hfree q hq
    apply Additive.ofMul.injective
    change Additive.ofMul q = 0
    apply hfree
    simpa only [lowerCentralLayerRepresentation_apply] using
      congrArg Additive.ofMul hq

/-- Irreducibility and faithfulness make a nontrivial actor fixed-point-free
on a lower-central layer. -/
theorem lowerCentralLayerAction_fixedPointFree_of_faithful_irreducible
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H) (i : Nat)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi i))
    (hfaith : Function.Injective
      (lowerCentralLayerRepresentation phi i))
    (a : C) (ha : a ≠ 1) :
    MonoidHom.FixedPointFree (lowerCentralLayerAction phi i a) := by
  rw [lowerCentralLayerAction_fixedPointFree_iff]
  exact representation_fixedVector_eq_zero_of_faithful_irreducible
    (lowerCentralLayerRepresentation phi i) hirr hfaith a ha

/-- Faithfulness and transitivity on nonzero vectors make a nontrivial actor
fixed-point-free on a lower-central layer. -/
theorem lowerCentralLayerAction_fixedPointFree_of_faithful_transitive_nonzero
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H) (i : Nat)
    (hfaith : Function.Injective
      (lowerCentralLayerRepresentation phi i))
    (htrans : ∀ v w : Additive (lowerCentralLayer H i),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi i c v = w)
    (a : C) (ha : a ≠ 1) :
    MonoidHom.FixedPointFree (lowerCentralLayerAction phi i a) := by
  rw [lowerCentralLayerAction_fixedPointFree_iff]
  exact representation_fixedVector_eq_zero_of_faithful_transitive_nonzero
    (lowerCentralLayerRepresentation phi i) hfaith htrans a ha

/-- An equivariant linear equivalence transports fixed-point-freeness
between lower-central layers. -/
theorem lowerCentralLayerAction_fixedPointFree_of_equivariant_linearEquiv
    {H : Type uH} {C : Type uC} [Group H] [Group C]
    (phi : C →* MulAut H) (i j : Nat)
    (e : Additive (lowerCentralLayer H i) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer H j))
    (hequiv : ∀ c v,
      e (lowerCentralLayerRepresentation phi i c v) =
        lowerCentralLayerRepresentation phi j c (e v))
    (a : C)
    (hfree : MonoidHom.FixedPointFree (lowerCentralLayerAction phi i a)) :
    MonoidHom.FixedPointFree (lowerCentralLayerAction phi j a) := by
  rw [lowerCentralLayerAction_fixedPointFree_iff] at hfree ⊢
  intro w hw
  obtain ⟨v, rfl⟩ := e.surjective w
  have hv : lowerCentralLayerRepresentation phi i a v = v := by
    apply e.injective
    rw [hequiv, hw]
  rw [hfree v hv, map_zero]

/-- The exact `L₁/L₂/L₃` fixed-point-free package needed by Higman's parity
step. -/
theorem lowerCentralLayers_fixedPointFree_of_lemmaSix_hypotheses
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 1))]
    (htrans : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w)
    (e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer H 2))
    (hequiv : ∀ c v,
      e (lowerCentralLayerRepresentation phi 1 c v) =
        lowerCentralLayerRepresentation phi 2 c (e v))
    (a : C) (ha : a ≠ 1) :
    MonoidHom.FixedPointFree (lowerCentralLayerAction phi 0 a) ∧
      MonoidHom.FixedPointFree (lowerCentralLayerAction phi 1 a) ∧
      MonoidHom.FixedPointFree (lowerCentralLayerAction phi 2 a) := by
  have hfaithOne : Function.Injective
      (lowerCentralLayerRepresentation phi 1) :=
    lowerCentralLayerOneRepresentation_injective_of_equivariant_linearEquiv
      phi hirr hfaith e hequiv
  have hfreeZero : MonoidHom.FixedPointFree
      (lowerCentralLayerAction phi 0 a) :=
    lowerCentralLayerAction_fixedPointFree_of_faithful_irreducible
      phi 0 hirr hfaith a ha
  have hfreeOne : MonoidHom.FixedPointFree
      (lowerCentralLayerAction phi 1 a) :=
    lowerCentralLayerAction_fixedPointFree_of_faithful_transitive_nonzero
      phi 1 hfaithOne htrans a ha
  have hfreeTwo : MonoidHom.FixedPointFree
      (lowerCentralLayerAction phi 2 a) :=
    lowerCentralLayerAction_fixedPointFree_of_equivariant_linearEquiv
      phi 1 2 e hequiv a hfreeOne
  exact ⟨hfreeZero, hfreeOne, hfreeTwo⟩

/-- A nontrivial actor of order three which is fixed-point-free on
`L₁,L₂,L₃` induces an automorphism of order three on `H/H₄`. -/
theorem classThreeQuotientAction_orderOf_eq_three
    {A : Type uC} {H : Type uH} [Group A] [Group H] [Finite H]
    (phi : A →* MulAut H) (a : A)
    (horder : orderOf a = 3)
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    [Nontrivial (lowerCentralLayer H 2)]
    (hfree₀ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 0 a))
    (hfree₁ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 1 a))
    (hfree₂ : MonoidHom.FixedPointFree (lowerCentralLayerAction phi 2 a)) :
    orderOf ((IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a) = 3 := by
  let psi :=
    (IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a
  have hdvd : orderOf psi ∣ 3 := by
    have hmap := orderOf_map_dvd
      (IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a
    simpa only [horder] using hmap
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hone | hthree
  · have hpsi : psi = 1 := orderOf_eq_one_iff.mp hone
    have hfree : MonoidHom.FixedPointFree psi :=
      classThreeQuotient_fixedPointFree_of_agemo_eq
        phi a hAgemo hfree₀ hfree₁ hfree₂
    obtain ⟨q, hq⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (classThreeQuotient_lowerCentralSeries_two_ne_bot H)
    have hqOne : (q : H ⧸ lowerCentralTerm H 3) = 1 := by
      apply hfree
      rw [hpsi]
      rfl
    exact absurd (Subtype.ext hqOne) hq
  · exact hthree

/-- **Higman Lemma 6, odd-dimension reduction (p. 85).**

Assume `H² = H₂`, the action on `L₁` is faithful irreducible, the action on
`L₂#` is transitive, and `L₂ ≃ L₃` equivariantly.  If `dim L₂` were even,
the faithful transitive Singer action would contain an actor of order three.
It is fixed-point-free on `L₁,L₂,L₃`, hence on `H/H₄`; Neumann's theorem then
forces that quotient to have class at most two, contrary to `L₃ ≠ 0`.
Therefore `dim L₂` is odd. -/
theorem lowerCentralLayerOne_finrank_odd_of_equivariant_linearEquiv
    {H : Type uH} {C : Type uC} [Group H] [Finite H]
    [CommGroup C] [Finite C]
    (phi : C →* MulAut H)
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 1))]
    (htrans : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w)
    (e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer H 2))
    (hequiv : ∀ c v,
      e (lowerCentralLayerRepresentation phi 1 c v) =
        lowerCentralLayerRepresentation phi 2 c (e v)) :
    Odd (Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  letI : Nontrivial (Additive (lowerCentralLayer H 2)) :=
    e.symm.toEquiv.nontrivial
  letI : Nontrivial (lowerCentralLayer H 2) :=
    (show Function.Injective
        (fun x : Additive (lowerCentralLayer H 2) => x.toMul) from
      fun _ _ h => h).nontrivial
  have hfaithOne : Function.Injective
      (lowerCentralLayerRepresentation phi 1) :=
    lowerCentralLayerOneRepresentation_injective_of_equivariant_linearEquiv
      phi hirr hfaith e hequiv
  obtain ⟨a, ha, horder⟩ :=
    exists_ne_one_orderOf_eq_three_of_even_faithful_transitive_nonzero
      (lowerCentralLayerRepresentation phi 1) hfaithOne htrans heven
  obtain ⟨hfreeZero, hfreeOne, hfreeTwo⟩ :=
    lowerCentralLayers_fixedPointFree_of_lemmaSix_hypotheses
      phi hirr hfaith htrans e hequiv a ha
  have hquotOrder : orderOf
      ((IsAInvariant.lowerCentralSeries phi 3).quotientMulAutHom a) = 3 :=
    classThreeQuotientAction_orderOf_eq_three
      phi a horder hAgemo hfreeZero hfreeOne hfreeTwo
  exact (classThreeQuotientAction_orderOf_ne_three
    phi a hAgemo hfreeZero hfreeOne hfreeTwo) hquotOrder

/-! ## The repeated-index weight orbit -/

private theorem twoPower_cyclicAdd_modEq
    {n : ℕ} [NeZero n] (a s : Fin n) :
    Nat.ModEq (2 ^ n - 1) (2 ^ (a.val + s.val)) (2 ^ (a + s).val) := by
  have hpowpos : 0 < 2 ^ n := by positivity
  have hbase : Nat.ModEq (2 ^ n - 1) (2 ^ n) 1 := by
    convert Nat.add_modEq_left (n := 2 ^ n - 1) (a := 1) using 1; omega
  by_cases hwrap : n ≤ a.val + s.val
  · have hval : (a + s).val = a.val + s.val - n := by
      rw [Fin.val_add_eq_ite]
      simp [hwrap]
    have hsum : a.val + s.val = n + (a.val + s.val - n) := by omega
    rw [hsum, pow_add, hval]
    simpa using hbase.mul
      (Nat.ModEq.refl (2 ^ (a.val + s.val - n)))
  · have hval : (a + s).val = a.val + s.val := by
      rw [Fin.val_add_eq_ite]
      simp [hwrap]
    rw [hval]

/-- **Higman Lemma 6 (p. 86), Frobenius-orbit pair gaps.**

If a pair weight is a Frobenius conjugate of the weight attached to `p`,
then its unordered cyclic index gap is the same `±` gap as that of `p`. -/
theorem primitiveRoot_pairWeight_eq_frobeniusShift_imp_pairGap
    {F : Type*} [Field F] {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (lambda : F) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (i j : Fin n) (p : HigmanExponentPair n) (s : Fin n)
    (h : lambda ^ (2 ^ i.val + 2 ^ j.val) =
      (lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)) ^ (2 ^ s.val)) :
    HasHigmanPairGap (higmanCyclicGap p.1.1 p.1.2) i j := by
  let a : Fin n := p.1.1 + s
  let b : Fin n := p.1.2 + s
  have hab : a ≠ b := by
    intro hab
    exact (by omega : p.1.1 ≠ p.1.2) (add_right_cancel hab)
  have hamod := twoPower_cyclicAdd_modEq p.1.1 s
  have hbmod := twoPower_cyclicAdd_modEq p.1.2 s
  have hmod : Nat.ModEq (2 ^ n - 1)
      ((2 ^ p.1.1.val + 2 ^ p.1.2.val) * 2 ^ s.val)
      (2 ^ a.val + 2 ^ b.val) := by
    rw [add_mul, ← pow_add, ← pow_add]
    exact hamod.add hbmod
  have horbit :
      (lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)) ^ (2 ^ s.val) =
        lambda ^ (2 ^ a.val + 2 ^ b.val) := by
    rw [← pow_mul]
    exact pow_eq_pow_of_modEq hmod hprim.pow_eq_one
  have hpairs : (i = a ∧ j = b) ∨ (i = b ∧ j = a) :=
    primitiveRoot_pairWeight_eq_pairWeight_candidates
      hn lambda hprim i j a b hab (h.trans horbit)
  have hgap : higmanCyclicGap a b = higmanCyclicGap p.1.1 p.1.2 := by
    simp only [a, b, higmanCyclicGap, map_add]
    ring
  have habGap : HasHigmanPairGap
      (higmanCyclicGap p.1.1 p.1.2) a b := Or.inl hgap
  rcases hpairs with hp | hp
  · rw [hp.1, hp.2]
    exact habGap
  · rw [hp.1, hp.2]
    exact HasHigmanPairGap.comm.mpr habGap

private theorem hasEigenvalue_mem_range_of_eigenspaces_iSup_eq_top
    {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (weight : κ → K)
    (hspan : ⨆ mu ∈ Set.range weight, T.eigenspace mu = ⊤)
    {mu : K} (hmu : T.HasEigenvalue mu) : mu ∈ Set.range weight := by
  by_contra hnot
  have hd := (Module.End.eigenspaces_iSupIndep T).disjoint_biSup hnot
  rw [hspan, disjoint_top] at hd
  exact hmu hd

/-- **Higman Lemma 6 (pp. 85--86), the single pair-gap orbit.**

Suppose the first two actual lower-central layers have Frobenius-conjugate
eigenbases for the same actor. The spanning actual bracket makes the first
second-layer eigenvalue a pair weight. Every nonzero basis bracket then has a
pair weight in that eigenvalue's Frobenius orbit, hence all such brackets are
supported on one unordered cyclic gap `±r`. -/
theorem exists_lowerCentralPairGapSupport_of_frobeniusEigenbases
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {H : Type uH} {C : Type uC} [Group H] [Group C]
    (phi : C →* MulAut H) (c : C)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (lambda nu : K) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (b₁ : Basis (Fin n) K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)))
    (hb₁ : ∀ i,
      (lowerCentralLayerRepresentation phi 0 c).baseChange K (b₁ i) =
        lambda ^ (2 ^ i.val) • b₁ i)
    (b₂ : Basis (Fin n) K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)))
    (hb₂ : ∀ s,
      (lowerCentralLayerRepresentation phi 1 c).baseChange K (b₂ s) =
        nu ^ (2 ^ s.val) • b₂ s) :
    ∃ p : HigmanExponentPair n,
      nu = lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val) ∧
      ∀ i j : Fin n,
        lowerCentralCommutatorBilinearBaseChange K H (b₁ i) (b₁ j) ≠ 0 →
          HasHigmanPairGap (higmanCyclicGap p.1.1 p.1.2) i j := by
  let T₁ : Module.End K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :=
    (lowerCentralLayerRepresentation phi 0 c).baseChange K
  let T₂ : Module.End K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) :=
    (lowerCentralLayerRepresentation phi 1 c).baseChange K
  let beta := lowerCentralCommutatorBilinearBaseChange K H
  have hbetaEquiv : ∀ x y, T₂ (beta x y) = beta (T₁ x) (T₁ y) := by
    intro x y
    exact lowerCentralCommutatorBilinearBaseChange_equivariant K phi c x y
  have hpairSpan : ⨆ eta ∈ Set.range (fun p : HigmanExponentPair n ↦
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)), T₂.eigenspace eta = ⊤ :=
    iSup_frobeniusPairWeight_eigenspace_eq_top_of_bilinear
      n lambda T₁ T₂ b₁ hb₁ beta hbetaEquiv
      (lowerCentralCommutatorBilinearBaseChange_self K H)
      (lowerCentralCommutatorBilinearBaseChange_span_eq_top K H)
  let i₀ : Fin n := ⟨0, by omega⟩
  have hnuEigen : T₂ (b₂ i₀) = nu • b₂ i₀ := by
    simpa [i₀] using hb₂ i₀
  have hnuHas : T₂.HasEigenvalue nu :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hnuEigen, b₂.ne_zero i₀⟩
  obtain ⟨p, hp⟩ := hasEigenvalue_mem_range_of_eigenspaces_iSup_eq_top
    T₂ (fun p : HigmanExponentPair n ↦
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)) hpairSpan hnuHas
  refine ⟨p, hp.symm, ?_⟩
  have hOrbitSpan : ⨆ eta ∈ Set.range (fun s : Fin n ↦ nu ^ (2 ^ s.val)),
      T₂.eigenspace eta = ⊤ := by
    apply top_unique
    rw [← b₂.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    apply Submodule.mem_iSup_of_mem (nu ^ (2 ^ s.val))
    apply Submodule.mem_iSup_of_mem (show
      nu ^ (2 ^ s.val) ∈ Set.range (fun t : Fin n ↦ nu ^ (2 ^ t.val)) from
      ⟨s, rfl⟩)
    exact Module.End.mem_eigenspace_iff.mpr (hb₂ s)
  intro i j hne
  have heigen : T₂ (beta (b₁ i) (b₁ j)) =
      lambda ^ (2 ^ i.val + 2 ^ j.val) • beta (b₁ i) (b₁ j) := by
    simpa only [T₁, T₂, beta, pow_add] using
      lowerCentralCommutatorBilinearBaseChange_eigenweight
        K phi c (lambda ^ (2 ^ i.val)) (lambda ^ (2 ^ j.val))
        (b₁ i) (b₁ j) (hb₁ i) (hb₁ j)
  have hhas : T₂.HasEigenvalue
      (lambda ^ (2 ^ i.val + 2 ^ j.val)) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr heigen, hne⟩
  obtain ⟨s, hs⟩ := hasEigenvalue_mem_range_of_eigenspaces_iSup_eq_top
    T₂ (fun s : Fin n ↦ nu ^ (2 ^ s.val)) hOrbitSpan hhas
  apply primitiveRoot_pairWeight_eq_frobeniusShift_imp_pairGap
    hn lambda hprim i j p s
  calc
    lambda ^ (2 ^ i.val + 2 ^ j.val) = nu ^ (2 ^ s.val) := hs.symm
    _ = (lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)) ^ (2 ^ s.val) :=
      congrArg (fun z : K => z ^ (2 ^ s.val)) hp.symm

/-! ## The square identity and the triple-bracket sum -/

/-- **Higman Lemma 6 (p. 86), the layer identity `[u^(2),u] = 0`.**

The actual square of a first-layer vector has zero degree-three bracket
with that vector. On representatives this follows from `[x²,x] = 1` before
passing to the lower-central quotients. -/
theorem lowerCentralDegreeThreeCommutatorBilinear_squareMapAdditive_self
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (u : Additive (lowerCentralLayer H 0)) :
    lowerCentralDegreeThreeCommutatorBilinear H
        (lowerCentralSquareMapAdditive H hSq u) u = 0 := by
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 0) u.toMul
  have hu : u = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel H 0) x) := by
    apply Additive.toMul.injective
    simpa only [toMul_ofMul] using hx.symm
  rw [hu, lowerCentralSquareMapAdditive_mk]
  change lowerCentralDegreeThreeCommutatorBilinear H
      (Additive.ofMul (lowerCentralSquareValue H hSq x))
      (Additive.ofMul
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0) x)) = 0
  rw [lowerCentralSquareValue,
    lowerCentralDegreeThreeCommutatorBilinear_mk]
  apply Additive.toMul.injective
  change lowerCentralDegreeThreeCommutatorValue H
      (lowerCentralSquareRepresentative H hSq x) x = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  have hcomm : ⁅((x : H) ^ 2), (x : H)⁆ = 1 := by
    simp only [commutatorElement_def, pow_two]
    group
  rw [show lowerCentralDegreeThreeCommutator H
      (lowerCentralSquareRepresentative H hSq x) x = 1 from
    Subtype.ext hcomm]
  exact Subgroup.one_mem _

/-- Expanding both arguments of a bilinear map turns a vanishing value into
the triple sum used in Higman's eigenweight argument. -/
private theorem tripleSum_eq_zero_of_bilinear_expansions
    {K : Type uK} [Field K]
    {V : Type uV} {W : Type uW} {X : Type uX}
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X]
    {m : ℕ}
    (b : Fin m → V)
    (beta : V →ₗ[K] V →ₗ[K] W)
    (gamma : W →ₗ[K] V →ₗ[K] X)
    (q : W) (u : V)
    (hq : q = ∑ i : Fin m, ∑ j : Fin m with i < j,
      beta (b i) (b j))
    (hu : u = ∑ i : Fin m, b i)
    (hself : gamma q u = 0) :
    ∑ i : Fin m, ∑ j : Fin m with i < j,
      ∑ k : Fin m, gamma (beta (b i) (b j)) (b k) = 0 := by
  rw [hq, hu] at hself
  simp only [map_sum, LinearMap.sum_apply] at hself
  calc
    ∑ i : Fin m, ∑ j : Fin m with i < j,
          ∑ k : Fin m, gamma (beta (b i) (b j)) (b k) =
        ∑ i : Fin m, ∑ k : Fin m, ∑ j : Fin m with i < j,
          gamma (beta (b i) (b j)) (b k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ i : Fin m, ∑ j : Fin m with i < j,
          gamma (beta (b i) (b j)) (b k) := Finset.sum_comm
    _ = 0 := hself

/-- **Higman Lemma 6 (p. 86), triple-sum identity.**

If a scalar-extended first-layer vector and its square have the Frobenius
basis expansions occurring in Lemma 5, then the sum of the corresponding
scalar-extended actual lower-central triple-bracket terms is zero. -/
theorem lowerCentralTripleCommutator_sum_eq_zero_of_square_formula
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    {m : ℕ}
    (b : Fin m →
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))
    (x : Additive (lowerCentralLayer H 0))
    (hx : (1 : K) ⊗ₜ[ZMod 2] x = ∑ k : Fin m, b k)
    (hq : lowerCentralSquareMapBaseChange K H hSq x =
      ∑ i : Fin m, ∑ j : Fin m with i < j,
        lowerCentralCommutatorBilinearBaseChange K H (b i) (b j)) :
    ∑ i : Fin m, ∑ j : Fin m with i < j, ∑ k : Fin m,
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (lowerCentralCommutatorBilinearBaseChange K H (b i) (b j))
        (b k) = 0 := by
  have hself :
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (lowerCentralSquareMapBaseChange K H hSq x)
        ((1 : K) ⊗ₜ[ZMod 2] x) = 0 := by
    change lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
      ((1 : K) ⊗ₜ[ZMod 2] lowerCentralSquareMapAdditive H hSq x)
      ((1 : K) ⊗ₜ[ZMod 2] x) = 0
    rw [lowerCentralDegreeThreeCommutatorBilinearBaseChange_tmul,
      lowerCentralDegreeThreeCommutatorBilinear_squareMapAdditive_self]
    simp
  exact tripleSum_eq_zero_of_bilinear_expansions b
    (lowerCentralCommutatorBilinearBaseChange K H)
    (lowerCentralDegreeThreeCommutatorBilinearBaseChange K H)
    (lowerCentralSquareMapBaseChange K H hSq x)
    ((1 : K) ⊗ₜ[ZMod 2] x) hq hx hself

/-- **Higman Lemma 6 (p. 86), separation of the triple sum by weight.**

The zero sum of actual scalar-extended triple commutators splits into its
individual eigenvalue fibers. The first two indices are packaged as an
increasing pair, so the repeated candidates remain explicit in each fiber. -/
theorem lowerCentralTripleCommutator_weightFiber_sum_eq_zero
    (K : Type uK) [Field K] [DecidableEq K] [Algebra (ZMod 2) K]
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (n : ℕ) (lambda : K)
    (b : Fin n → K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))
    (hb : ∀ i,
      (lowerCentralLayerRepresentation phi 0 g).baseChange K (b i) =
        lambda ^ (2 ^ i.val) • b i)
    (hsum : ∑ i : Fin n, ∑ j : Fin n with i < j, ∑ k : Fin n,
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (lowerCentralCommutatorBilinearBaseChange K H (b i) (b j))
        (b k) = 0)
    (mu : K) :
    ∑ z : HigmanExponentPair n × Fin n with
        lambda ^ (2 ^ z.1.1.1.val + 2 ^ z.1.1.2.val + 2 ^ z.2.val) = mu,
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (lowerCentralCommutatorBilinearBaseChange K H
          (b z.1.1.1) (b z.1.1.2))
        (b z.2) = 0 := by
  classical
  let I := HigmanExponentPair n × Fin n
  let T : Module.End K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 2)) :=
    (lowerCentralLayerRepresentation phi 2 g).baseChange K
  let weight : I → K := fun z =>
    lambda ^ (2 ^ z.1.1.1.val + 2 ^ z.1.1.2.val + 2 ^ z.2.val)
  let term : I → K ⊗[ZMod 2] Additive (lowerCentralLayer H 2) := fun z =>
    lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
      (lowerCentralCommutatorBilinearBaseChange K H
        (b z.1.1.1) (b z.1.1.2))
      (b z.2)
  have htermEigen : ∀ z ∈ (Finset.univ : Finset I),
      T (term z) = weight z • term z := by
    intro z _hz
    have hbeta := lowerCentralCommutatorBilinearBaseChange_eigenweight
      K phi g
      (lambda ^ (2 ^ z.1.1.1.val))
      (lambda ^ (2 ^ z.1.1.2.val))
      (b z.1.1.1) (b z.1.1.2) (hb z.1.1.1) (hb z.1.1.2)
    have hgamma := lowerCentralDegreeThreeCommutatorBilinearBaseChange_eigenweight
      K phi g
      (lambda ^ (2 ^ z.1.1.1.val) * lambda ^ (2 ^ z.1.1.2.val))
      (lambda ^ (2 ^ z.2.val))
      (lowerCentralCommutatorBilinearBaseChange K H
        (b z.1.1.1) (b z.1.1.2))
      (b z.2) hbeta (hb z.2)
    simpa only [T, term, weight, pow_add, mul_assoc] using hgamma
  have hpairs :
      (∑ p : HigmanExponentPair n, ∑ k : Fin n,
        lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
          (lowerCentralCommutatorBilinearBaseChange K H
            (b p.1.1) (b p.1.2))
          (b k)) =
        ∑ i : Fin n, ∑ j : Fin n with i < j, ∑ k : Fin n,
          lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
            (lowerCentralCommutatorBilinearBaseChange K H (b i) (b j))
            (b k) := by
    let pred : Fin n × Fin n → Prop := fun p => p.1.1 < p.2.1
    let pairTerm : Fin n × Fin n →
        K ⊗[ZMod 2] Additive (lowerCentralLayer H 2) := fun p =>
      ∑ k : Fin n,
        lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
          (lowerCentralCommutatorBilinearBaseChange K H (b p.1) (b p.2))
          (b k)
    have hsub :
        (∑ p : Subtype pred, pairTerm p.1) =
          ∑ p ∈ Finset.univ.filter pred, pairTerm p := by
      exact (Finset.sum_subtype
        (Finset.univ.filter pred) (by simp [pred]) pairTerm).symm
    rw [show (∑ p : HigmanExponentPair n, ∑ k : Fin n,
        lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
          (lowerCentralCommutatorBilinearBaseChange K H
            (b p.1.1) (b p.1.2))
          (b k)) = ∑ p : Subtype pred, pairTerm p.1 by rfl]
    rw [hsub, ← Finset.univ_product_univ, Finset.sum_filter,
      Finset.sum_product]
    simp only [pairTerm, Finset.sum_filter]
    rfl
  have hsum' : ∑ z : I, term z = 0 := by
    simp only [I, Fintype.sum_prod_type, term]
    exact hpairs.trans hsum
  simpa only [I, weight, term, Finset.sum_filter, Finset.mem_univ,
    true_and] using
    (Module.End.sum_filter_weight_eq_zero_of_sum_eq_zero
      T (Finset.univ : Finset I) weight term htermEigen hsum' mu)

/-- **Higman Lemma 6 (p. 86), three-distinct-index terms.**

If the third-layer action is spanned by the pair-weight eigenspaces and the
three Frobenius indices are distinct, the actual scalar-extended triple
commutator lies in an eigenspace which the binary-weight exclusion makes
zero. -/
theorem lowerCentralTripleCommutator_eq_zero_of_threeDistinct
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    {n : ℕ} (hn : 3 ≤ n)
    (lambda : K) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (b : Fin n → K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))
    (hb : ∀ i,
      (lowerCentralLayerRepresentation phi 0 g).baseChange K (b i) =
        lambda ^ (2 ^ i.val) • b i)
    (hspan : ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n ↦
        lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)),
      Module.End.eigenspace
        ((lowerCentralLayerRepresentation phi 2 g).baseChange K :
          Module.End K (K ⊗[ZMod 2] Additive (lowerCentralLayer H 2))) mu = ⊤)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
      (lowerCentralCommutatorBilinearBaseChange K H (b i) (b j))
      (b k) = 0 := by
  let T₃ : Module.End K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 2)) :=
    (lowerCentralLayerRepresentation phi 2 g).baseChange K
  let term : K ⊗[ZMod 2] Additive (lowerCentralLayer H 2) :=
    lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
      (lowerCentralCommutatorBilinearBaseChange K H (b i) (b j))
      (b k)
  have hbeta := lowerCentralCommutatorBilinearBaseChange_eigenweight
    K phi g
    (lambda ^ (2 ^ i.val)) (lambda ^ (2 ^ j.val))
    (b i) (b j) (hb i) (hb j)
  have hgamma := lowerCentralDegreeThreeCommutatorBilinearBaseChange_eigenweight
    K phi g
    (lambda ^ (2 ^ i.val) * lambda ^ (2 ^ j.val))
    (lambda ^ (2 ^ k.val))
    (lowerCentralCommutatorBilinearBaseChange K H (b i) (b j))
    (b k) hbeta (hb k)
  have heigen :
      T₃ term = lambda ^ (2 ^ i.val + 2 ^ j.val + 2 ^ k.val) • term := by
    simpa only [T₃, term, pow_add, mul_assoc] using hgamma
  have hbot :
      T₃.eigenspace (lambda ^ (2 ^ i.val + 2 ^ j.val + 2 ^ k.val)) = ⊥ :=
    primitiveRoot_threeDistinctWeight_eigenspace_eq_bot
      hn lambda hprim T₃ hspan i j k hij hik hjk
  have hmem : term ∈
      T₃.eigenspace (lambda ^ (2 ^ i.val + 2 ^ j.val + 2 ^ k.val)) :=
    Module.End.mem_eigenspace_iff.mpr heigen
  rw [hbot] at hmem
  simpa only [term, Submodule.mem_bot] using hmem

set_option maxHeartbeats 800000 in
-- The finite repeated-weight classification has four nested orientation cases.
/-- **Higman Lemma 6 (p. 86), repeated-weight fiber elimination.**

Assume the actual first-layer brackets are supported on one unordered cyclic
gap and that every three-distinct-index triple bracket vanishes. In a
pair-weight fiber, every nonzero triple bracket therefore has a repeated
third index. The binary-weight classification leaves one predecessor
candidate on either side of the target pair. Each side contains at most one
term, while oddness of the dimension rules out nonzero terms on both sides.
Since the whole fiber sums to zero, every term in it vanishes. -/
theorem lowerCentralTripleCommutator_pairWeightFiber_terms_eq_zero
    (K : Type uK) [Field K] [DecidableEq K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H]
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (hnodd : Odd n)
    (lambda : K) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (b : Fin n → K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))
    (r : ZMod n)
    (hsupport : ∀ i j : Fin n,
      lowerCentralCommutatorBilinearBaseChange K H (b i) (b j) ≠ 0 →
        HasHigmanPairGap r i j)
    (hdistinct : ∀ (q : HigmanExponentPair n) (k : Fin n),
      k ≠ q.1.1 → k ≠ q.1.2 →
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (lowerCentralCommutatorBilinearBaseChange K H
          (b q.1.1) (b q.1.2)) (b k) = 0)
    (p : HigmanExponentPair n)
    (hfiber : ∑ z : HigmanExponentPair n × Fin n with
        lambda ^ (2 ^ z.1.1.1.val + 2 ^ z.1.1.2.val + 2 ^ z.2.val) =
          lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val),
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (lowerCentralCommutatorBilinearBaseChange K H
          (b z.1.1.1) (b z.1.1.2)) (b z.2) = 0) :
    ∀ z : HigmanExponentPair n × Fin n,
      lambda ^ (2 ^ z.1.1.1.val + 2 ^ z.1.1.2.val + 2 ^ z.2.val) =
          lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val) →
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (lowerCentralCommutatorBilinearBaseChange K H
          (b z.1.1.1) (b z.1.1.2)) (b z.2) = 0 := by
  classical
  let I := HigmanExponentPair n × Fin n
  let weight : I → K := fun z =>
    lambda ^ (2 ^ z.1.1.1.val + 2 ^ z.1.1.2.val + 2 ^ z.2.val)
  let target : K := lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)
  let term : I → K ⊗[ZMod 2] Additive (lowerCentralLayer H 2) := fun z =>
    lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
      (lowerCentralCommutatorBilinearBaseChange K H
        (b z.1.1.1) (b z.1.1.2)) (b z.2)
  let fiber : Finset I := Finset.univ.filter fun z => weight z = target
  let IsLeft : I → Prop := fun z =>
    (z.1.1.1 = p.1.1 ∧ z.1.1.2 = p.1.2 - 1 ∧ z.2 = z.1.1.2) ∨
    (z.1.1.2 = p.1.1 ∧ z.1.1.1 = p.1.2 - 1 ∧ z.2 = z.1.1.1)
  let IsRight : I → Prop := fun z =>
    (z.1.1.1 = p.1.2 ∧ z.1.1.2 = p.1.1 - 1 ∧ z.2 = z.1.1.2) ∨
    (z.1.1.2 = p.1.2 ∧ z.1.1.1 = p.1.1 - 1 ∧ z.2 = z.1.1.1)
  have hfinite : IsOfFinOrder lambda :=
    hprim.isOfFinOrder (Nat.sub_ne_zero_of_lt
      (Nat.one_lt_pow (by omega : n ≠ 0) (by omega)))
  have classify : ∀ z : I, weight z = target → term z ≠ 0 →
      (IsLeft z ∧ HasHigmanPairGap r p.1.1 (p.1.2 - 1)) ∨
      (IsRight z ∧ HasHigmanPairGap r p.1.2 (p.1.1 - 1)) := by
    rintro ⟨q, k⟩ hweight hterm
    have hbeta : lowerCentralCommutatorBilinearBaseChange K H
        (b q.1.1) (b q.1.2) ≠ 0 := by
      intro hzero
      apply hterm
      simp only [term]
      rw [hzero]
      simp
    have hgap := hsupport q.1.1 q.1.2 hbeta
    have hmod : Nat.ModEq (2 ^ n - 1)
        (2 ^ q.1.1.val + 2 ^ q.1.2.val + 2 ^ k.val)
        (2 ^ p.1.1.val + 2 ^ p.1.2.val) := by
      have hm := hfinite.pow_eq_pow_iff_modEq.mp hweight
      rwa [← hprim.eq_orderOf] at hm
    by_cases hk₁ : k = q.1.1
    · have hcand := repeated_frobeniusWeight_pairWeight_candidates hn
        q.1.2 q.1.1 p (by
          simpa only [hk₁, add_comm, add_left_comm, add_assoc] using hmod)
      rcases hcand with hcand | hcand
      · left
        constructor
        · right
          exact ⟨hcand.1, hcand.2, hk₁⟩
        · apply HasHigmanPairGap.comm.mp
          simpa only [hcand.1, hcand.2] using hgap
      · right
        constructor
        · right
          exact ⟨hcand.1, hcand.2, hk₁⟩
        · apply HasHigmanPairGap.comm.mp
          simpa only [hcand.1, hcand.2] using hgap
    · by_cases hk₂ : k = q.1.2
      · have hcand := repeated_frobeniusWeight_pairWeight_candidates hn
          q.1.1 q.1.2 p (by simpa only [hk₂] using hmod)
        rcases hcand with hcand | hcand
        · left
          constructor
          · left
            exact ⟨hcand.1, hcand.2, hk₂⟩
          · simpa only [hcand.1, hcand.2] using hgap
        · right
          constructor
          · left
            exact ⟨hcand.1, hcand.2, hk₂⟩
          · simpa only [hcand.1, hcand.2] using hgap
      · exact (hterm (hdistinct q k hk₁ hk₂)).elim
  have left_unique : ∀ z w : I, IsLeft z → IsLeft w → z = w := by
    rintro ⟨q, k⟩ ⟨q', k'⟩ hq hq'
    dsimp only [IsLeft] at hq hq'
    rcases hq with hq | hq <;> rcases hq' with hq' | hq'
    · apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext <;> simp_all
      · simp_all
    · exfalso
      have hlt := q.2
      have hlt' := q'.2
      fin_omega
    · exfalso
      have hlt := q.2
      have hlt' := q'.2
      fin_omega
    · apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext <;> simp_all
      · simp_all
  have right_unique : ∀ z w : I, IsRight z → IsRight w → z = w := by
    rintro ⟨q, k⟩ ⟨q', k'⟩ hq hq'
    dsimp only [IsRight] at hq hq'
    rcases hq with hq | hq <;> rcases hq' with hq' | hq'
    · apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext <;> simp_all
      · simp_all
    · exfalso
      have hlt := q.2
      have hlt' := q'.2
      fin_omega
    · exfalso
      have hlt := q.2
      have hlt' := q'.2
      fin_omega
    · apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext <;> simp_all
      · simp_all
  have atMostOne : ∀ z w : I, z ∈ fiber → w ∈ fiber →
      term z ≠ 0 → term w ≠ 0 → z = w := by
    intro z w hz hw hzne hwne
    have hzw : weight z = target := (Finset.mem_filter.mp hz).2
    have hww : weight w = target := (Finset.mem_filter.mp hw).2
    rcases classify z hzw hzne with ⟨hzL, hgapL⟩ | ⟨hzR, hgapR⟩
    · rcases classify w hww hwne with ⟨hwL, _⟩ | ⟨hwR, hgapR⟩
      · exact left_unique z w hzL hwL
      · exact (p.not_both_predecessor_pairGaps_of_odd hnodd r
          ⟨hgapL, hgapR⟩).elim
    · rcases classify w hww hwne with ⟨hwL, hgapL⟩ | ⟨hwR, _⟩
      · exact (p.not_both_predecessor_pairGaps_of_odd hnodd r
          ⟨hgapL, hgapR⟩).elim
      · exact right_unique z w hzR hwR
  have hsum : Finset.sum fiber term = 0 := by
    simpa only [fiber, term, weight, target, I, Finset.sum_filter,
      Finset.mem_univ, true_and] using hfiber
  intro z hzweight
  change term z = 0
  have hzmem : z ∈ fiber := by
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzweight
  by_contra hzne
  have hothers : ∀ w ∈ fiber, w ≠ z → term w = 0 := by
    intro w hw hwz
    by_contra hwne
    exact hwz (atMostOne w z hw hzmem hwne hzne)
  exact hzne (Finset.eq_zero_of_sum_eq_zero hsum hothers z hzmem)

end OddOrder.Higman.Suzuki2Groups
