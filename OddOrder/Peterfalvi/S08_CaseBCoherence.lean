/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCore
import OddOrder.Peterfalvi.S07_CoherenceGalois

/-!
# Peterfalvi §8: Case (B) coherence (`X ∪ Y` is coherent in case (B))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37, the **(6.8.2)** branch of the (6.8) coherence capstone
(`OddOrder.Peterfalvi.S08.sibleySetup_is_coherent`).

This is the case-`(B)` (`Z = W₂`, `W₂` prime central) analogue of the case-`(A)`/Frobenius
central-commutator program in `S08_CoherenceCore`.  The textbook proof (mmd 04.8 L178-224) runs:

* **(6.8.2.1)** `η^{τ₁}` is constant on `Z^#` — already available in full generality as
  `OddOrder.Peterfalvi.S07.IsCoherent.extension_constant_on_sharp_of_prime` (it needs `Z` of prime
  order, which is exactly the case-`(B)` hypothesis `w₂` prime, and `hyp.tau` is the genuine
  `dadeIntegralCharacterMap`, so the general lemma applies to `hyp.coherentYset`).
* **(6.8.2.2)** the `(6.7)`-congruence inner-product formula (`peterfalvi_67_centralCommutator`
  + the regular-character decomposition).
* **(6.8.2.3)** the `X`-side `(χ − a η₁)^τ` decomposition ([Is] Lemma 2.27).
* the final `τ₂` assembly.

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` ("session 39 cont.²").
-/

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G]

/-- **Galois action commutes with induction.**  For a ring automorphism `σ` of `ℂ` (the cyclotomic
Galois action of Peterfalvi (1.9)) and `θ : ClassFunction ↥H ℂ`,
`σ(Ind_H^G θ) = Ind_H^G (σθ)`.  Indeed `Ind_H^G θ (g) = |H|⁻¹ ∑_x induceTerm θ x g` and `σ` is a
ring homomorphism that fixes the rational coefficient `|H|⁻¹` (`map_natCast`/`map_inv₀`) and acts
termwise on the `θ`-values (`induceTerm` is `θ ⟨x⁻¹gx,·⟩` or `0`, both `σ`-equivariant).

This is the engine behind the Galois-closure of the `Y = S(H')` family (each `Ind_H^L (linear χ)`
maps to `Ind_H^L (linear (σ∘χ))`), one of the hypotheses of
`IsCoherent.extension_constant_on_sharp_of_prime` (Peterfalvi (6.8.2.1)).  Stated in the general
`ClassFunction` namespace (it is not §8-specific) and upstreamable to `InducedCharacter`. -/
theorem ClassFunction.mapRingEquiv_induce {H : Subgroup G} [Fintype G]
    [Invertible (Nat.card H : ℂ)] (σ : ℂ ≃+* ℂ) (θ : ClassFunction ↥H ℂ) :
    mapRingEquiv σ (induce H θ) = induce H (mapRingEquiv σ θ) := by
  ext g
  rw [mapRingEquiv_apply, induce_apply, induce_apply, map_mul, map_sum]
  have hcoef : σ (⅟(Nat.card H : ℂ)) = ⅟(Nat.card H : ℂ) := by
    simp [invOf_eq_inv, map_inv₀, map_natCast]
  rw [hcoef]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [induceTerm_of_mem _ hx, induceTerm_of_mem _ hx, mapRingEquiv_apply]
  · rw [induceTerm_of_not_mem _ hx, induceTerm_of_not_mem _ hx, map_zero]

/-- **Galois twist of a linear character.**  For `σ : ℂ ≃+* ℂ` and a linear character
`χ : H →* ℂˣ`, the `σ`-image of the class function `linearIrreducibleCharacter χ` is again a linear
character, namely the one of the `σ`-twisted units homomorphism `(Units.map σ) ∘ χ`.  This is the
linear-character case of the Galois-twist `character_galoisTwist` (`σ ∘ χ_ρ`), specialized so it
feeds `mapRingEquiv_induce` directly. -/
theorem ClassFunction.mapRingEquiv_linearIrreducibleCharacter {H : Type*} [Group H]
    (σ : ℂ ≃+* ℂ) (χ : H →* ℂˣ) :
    mapRingEquiv σ (linearIrreducibleCharacter χ : ClassFunction H ℂ)
      = (linearIrreducibleCharacter ((Units.map (σ.toRingHom.toMonoidHom)).comp χ) :
          ClassFunction H ℂ) := by
  ext h
  rw [mapRingEquiv_apply, linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply,
    MonoidHom.comp_apply, Units.coe_map]
  rfl

/-- **Induction from a subgroup of a normal subgroup is supported on that normal subgroup.**
If `H' ≤ N` with `N ◁ G`, then `(Ind_{H'}^G θ).support ⊆ N`: a nonzero value at `g` needs some
conjugate `x⁻¹gx ∈ H' ⊆ N`, and `N` normal then forces `g ∈ N`.  Generalizes
`support_induce_subset_of_normal` (the `H' = N` case) to non-normal source subgroups, as needed for
`Ind_{W₂}^L` with `W₂ ⊆ H ◁ L` in Peterfalvi (6.8.2.2). -/
theorem ClassFunction.support_induce_subset_of_le_normal {G : Type*} [Group G] [Fintype G]
    {N H' : Subgroup G} [N.Normal] [Invertible (Nat.card ↥H' : ℂ)]
    (hH'N : H' ≤ N) (θ : ClassFunction ↥H' ℂ) :
    (ClassFunction.induce H' θ).support ⊆ (N : Set G) := by
  intro g hg
  by_contra hgN
  apply hg
  rw [ClassFunction.induce_apply]
  have hterm : ∀ x : G, ClassFunction.induceTerm H' θ x g = 0 := by
    intro x
    have hnotmem : x⁻¹ * g * x ∉ H' := by
      intro hmem
      apply hgN
      have hconj := ‹N.Normal›.conj_mem (x⁻¹ * g * x) (hH'N hmem) x
      have heq : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
      rwa [heq] at hconj
    rw [ClassFunction.induceTerm_of_not_mem _ hnotmem]
  rw [Finset.sum_eq_zero (fun x _ => hterm x), mul_zero]

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.1) input — the `Y = S(H')` family is closed under the cyclotomic Galois action.**
For any `σ : ℂ ≃+* ℂ`, the `σ`-image of an `η ∈ Y` is again in `Y`.  Indeed every `η ∈ Y` is
`Ind_H^L (linear χ)` with `χ ≠ 1` (`exists_linear_source_of_mem_Yset`); `σ` commutes with induction
(`mapRingEquiv_induce`) and twists the linear source to `(Units.map σ) ∘ χ`
(`mapRingEquiv_linearIrreducibleCharacter`), which is still a nontrivial linear character
(`σ` injective), so the image is `Ind_H^L (linear ((Units.map σ) ∘ χ)) ∈ Y`.

This is the `hSu` hypothesis of `S07.IsCoherent.extension_constant_on_sharp_of_prime`, used to
establish Peterfalvi (6.8.2.1) (`η^{τ₁}` constant on `Z^#`) for the Sibley `Y`-coherence. -/
theorem SibleyDadeHypothesis.Yset_mapRingEquiv_mem (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (σ : ℂ ≃+* ℂ) {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    ClassFunction.mapRingEquiv σ φ ∈ hyp.Yset := by
  obtain ⟨χ, hχ_ne, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [ClassFunction.mapRingEquiv_induce, ClassFunction.mapRingEquiv_linearIrreducibleCharacter]
  refine hyp.induce_linearIrreducibleCharacter_mem_Yset ?_
  intro hχ'
  refine hχ_ne ?_
  have hinj : Function.Injective (Units.map (σ.toRingHom.toMonoidHom : ℂ →* ℂ)) :=
    Units.map_injective (f := (σ.toRingHom.toMonoidHom : ℂ →* ℂ)) σ.injective
  ext h
  have key : Units.map (σ.toRingHom.toMonoidHom : ℂ →* ℂ) (χ h) = 1 := by
    have h0 := DFunLike.congr_fun hχ' h
    simpa [MonoidHom.comp_apply] using h0
  have hh : χ h = 1 := hinj (key.trans (map_one _).symm)
  simpa using hh

/-- **(6.8.2.1) input — `hZA`.**  Every nontrivial element of `⁅H, H⁆` maps into `H^# = sharpImage H`.
Since `⁅H, H⁆ ≤ H`, a nontrivial `z ∈ ⁅H, H⁆` lands in `H` with `(z : G) ≠ 1`. -/
theorem SibleyDadeHypothesis.coe_mem_sharpImage_of_mem_commutator
    (hyp : SibleyDadeHypothesis G L H) {z : ↥L} (hz : z ∈ ⁅H, H⁆) (hz1 : z ≠ 1) :
    (L.subtype z) ∈ sharpImage H := by
  have hzH : z ∈ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro p hp q hq
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hp hq) (H.inv_mem hp)) (H.inv_mem hq)
    exact hle hz
  refine ⟨Subgroup.mem_map_of_mem L.subtype hzH, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  exact hz1 (by simpa using hc)

/-- **(6.8.2.1) input — `hηx`.**  A `Y = S(H')` character is constant on `⁅H, H⁆`: `η z = η 1`
for `z ∈ ⁅H, H⁆`.  Indeed `η = Ind_H^L (linear χ)`, and for `z ∈ ⁅H, H⁆ ⊆ H` (with `H ◁ L`) every
conjugate `g⁻¹zg` lies in `⁅H, H⁆` (normal in `L`), on which the linear source `χ` is trivial
(`ℂˣ` abelian ⟹ `⁅H,H⁆ ≤ ker χ`); so every `induceTerm` is `1` and `η z = |L:H| = |W₁| = η 1`. -/
theorem SibleyDadeHypothesis.Yset_apply_eq_apply_one_of_mem_commutator
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ ⁅H, H⁆) : η z = η 1 := by
  obtain ⟨χ, _hχ_ne, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hη
  rw [hyp.induce_apply_one_eq_card_W1_of_degree_one _ (linearIrreducibleCharacter_apply_one χ),
    ClassFunction.induce_apply]
  -- ⅟|H| * ∑ g, induceTerm H (linear χ) g z = |W₁|
  have hcomm_normal : (⁅H, H⁆ : Subgroup ↥L).Normal :=
    Subgroup.commutator_normal H H
  have hterm : ∀ g : ↥L,
      ClassFunction.induceTerm H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) g z = 1 := by
    intro g
    have hgcomm : g⁻¹ * z * g ∈ ⁅H, H⁆ := by
      have := hcomm_normal.conj_mem z hz g⁻¹
      simpa [mul_assoc] using this
    have hgH : g⁻¹ * z * g ∈ H := by
      have hle : ⁅H, H⁆ ≤ H := by
        rw [Subgroup.commutator_le]
        intro p hp q hq
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem hp hq) (H.inv_mem hp)) (H.inv_mem hq)
      exact hle hgcomm
    rw [ClassFunction.induceTerm_of_mem _ hgH, linearIrreducibleCharacter_apply]
    -- `χ ⟨g⁻¹zg, hgH⟩ = 1`: the element lies in the commutator of `↥H`, killed by the abelian `χ`.
    have hmap : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hmem : (⟨g⁻¹ * z * g, hgH⟩ : ↥H) ∈ commutator ↥H := by
      have hin : (g⁻¹ * z * g : ↥L) ∈ (commutator ↥H).map H.subtype := by
        rw [hmap]; exact hgcomm
      obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp hin
      have hweq' : w = (⟨g⁻¹ * z * g, hgH⟩ : ↥H) := Subtype.ext hweq
      rwa [hweq'] at hw
    have hker : χ (⟨g⁻¹ * z * g, hgH⟩ : ↥H) = 1 := by
      have hbot : commutator ℂˣ = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        exact Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
      have hle : (commutator ↥H).map χ ≤ commutator ℂˣ := by
        rw [commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      rw [hbot] at hle
      exact Subgroup.mem_bot.mp (hle (Subgroup.mem_map_of_mem χ hmem))
    rw [hker, Units.val_one]
  rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥hyp.W1 : ℂ) * (Nat.card ↥H : ℂ) := by
    rw [← hyp.index_H_eq_card_W1, ← Nat.cast_mul, Subgroup.index_mul_card]
  rw [hLcard, mul_comm (Nat.card ↥hyp.W1 : ℂ) (Nat.card ↥H : ℂ), ← mul_assoc,
    invOf_mul_self, one_mul]

/-- **Peterfalvi (6.8.2.1), case (B):** the `Y = S(H')`-coherence extension is constant on `W₂^#`.
For `η ∈ Y` and `x, y ∈ W₂^#` (with `W₂` of prime order and `W₂ ⊆ ⁅H, H⁆`),
`η^{τ₁}(y) = η^{τ₁}(x)`.

Assembled from the general `S07.IsCoherent.extension_constant_on_sharp_of_prime`: `W₂` prime is
`hZp`; `hSu` (`Yset_mapRingEquiv_mem`), `hZA` (`coe_mem_sharpImage_of_mem_commutator` via
`W₂ ⊆ ⁅H,H⁆`), `hηx` (`Yset_apply_eq_apply_one_of_mem_commutator`) are the case-(B) discharges;
`hSirr`/`hlat`/`hpair` come from the `Y`-coherence structure (`isIrreducibleCharacter_of_mem_Yset`,
`extension_mem_ZIrr`, `two_le_Yset_ncard`); `hspan` from `zSpan_S_support_subset_of_apply_one_eq_zero`
(via `Y ⊆ S`). -/
theorem SibleyDadeHypothesis.coherentYset_extension_const_on_W2
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hprime : (Nat.card W2).Prime) (hW2 : W2 ≤ ⁅H, H⁆)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x y : ↥L} (hx : x ∈ W2) (hx1 : x ≠ 1) (hy : y ∈ W2) (hy1 : y ≠ 1) :
    hyp.coherentYset.extension η (y : G) = hyp.coherentYset.extension η (x : G) := by
  have hspan : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Yset, φ 1 = 0 →
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun φ hφ h1 =>
      hyp.zSpan_S_support_subset_of_apply_one_eq_zero
        ((Submodule.span_mono hyp.Yset_subset_S) hφ) h1
  exact OddOrder.Peterfalvi.S07.IsCoherent.extension_constant_on_sharp_of_prime
    hyp.coherentYset
    (le_refl _)
    (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ)
    hspan
    (fun σ φ hφ => hyp.Yset_mapRingEquiv_mem σ hφ)
    (fun φ hφ => hyp.coherentYset.extension_mem_ZIrr φ (Submodule.subset_span hφ))
    hη
    (Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega) η)
    hprime
    (fun z hz hz1 => hyp.coe_mem_sharpImage_of_mem_commutator (hW2 hz) hz1)
    hx hx1 (hyp.Yset_apply_eq_apply_one_of_mem_commutator hη (hW2 hx)) hy hy1

/-- **(6.8.2.2) input — the support of `α = Ind_{W₂}^L φ − c·η₁`.**  When `α` vanishes at `1`
(the degree-balancing condition `Ind_{W₂}^L φ (1) = c · η₁(1)`, met by `c = [H:W₂]`), the
difference is supported on `H^# = sharpImage H`: `Ind_{W₂}^L φ` is supported on `H` (since
`W₂ ⊆ H ◁ L`, `support_induce_subset_of_le_normal`), `η₁ ∈ Y` is supported on `H`
(`support_induce_subset_of_normal`), and `α 1 = 0` removes the identity.  This is the
`Supp(α) ⊆ H^#` step of Peterfalvi (6.8.2.2). -/
theorem SibleyDadeHypothesis.support_indW2_sub_smul_subset_sharpImage
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) :
    (ClassFunction.induce W2 φ - c • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  obtain ⟨χ, _hχne, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hη₁
  -- both pieces are supported on `H`
  have hindW2 : (ClassFunction.induce W2 φ).support ⊆ (H : Set ↥L) :=
    ClassFunction.support_induce_subset_of_le_normal hW2H φ
  have hη₁supp : (ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ)).support
      ⊆ (H : Set ↥L) :=
    ClassFunction.support_induce_subset_of_normal H _
  intro x hx
  rw [ClassFunction.mem_support] at hx
  have hxH : x ∈ H := by
    by_contra hxnotH
    have h1' : ClassFunction.induce W2 φ x = 0 := by
      by_contra h; exact hxnotH (hindW2 (ClassFunction.mem_support.mpr h))
    have h2' : (ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ)) x = 0 := by
      by_contra h; exact hxnotH (hη₁supp (ClassFunction.mem_support.mpr h))
    exact hx (by simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, smul_eq_mul,
      h1', h2', mul_zero, sub_zero])
  have hxne : x ≠ 1 := by
    intro hx1
    refine hx ?_
    simp only [hx1, ClassFunction.sub_apply, ClassFunction.smul_apply, smul_eq_mul, h1, sub_self]
  change (x : G) ∈ sharpImage H
  exact ⟨Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩, fun hx1G => hxne (Subtype.ext hx1G)⟩

end OddOrder.Peterfalvi.S08
