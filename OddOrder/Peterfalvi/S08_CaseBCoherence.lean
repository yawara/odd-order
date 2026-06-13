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

/-- **The sum of a nontrivial irreducible character over the group is zero.**  By orthonormality
`⟨φ, 1⟩ = 0` for `φ ≠ 1`, and `⟨φ, 1⟩ = |Γ|⁻¹ ∑_g φ(g)` (the trivial character is constant `1`). -/
theorem sum_apply_eq_zero_of_ne_trivial {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {φ : IrreducibleCharacter Γ}
    (hφ : φ ≠ trivialIrreducibleCharacter Γ) :
    ∑ g : Γ, (φ : ClassFunction Γ ℂ) g = 0 := by
  have h := irreducibleCharacter_inner φ (trivialIrreducibleCharacter Γ)
  rw [if_neg hφ, ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum] at h
  simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter, trivialClassFunction_apply,
    star_one, mul_one] at h
  have hS : (Nat.card Γ : ℂ) * (⅟(Nat.card Γ : ℂ) * ∑ g : Γ, (φ : ClassFunction Γ ℂ) g) = 0 := by
    rw [h, mul_zero]
  rwa [← mul_assoc, mul_invOf_self, one_mul] at hS

/-- **Regular-character decomposition value (Peterfalvi (6.8.2.2) core relation).**  If `f` is a
class function constant on `Γ^#` and `φ` is a nontrivial *linear* irreducible character
(`φ(1) = 1`), then `f(1) − f(z) = |Γ|·⟨f, φ⟩` for any `z ≠ 1`.  This is the substance of
`Res_Z ψ = a·ρ_Z + b·1_Z` with `a = ⟨Res_Z ψ, φ⟩`, `ψ(1) − ψ(z) = a·|Z|`, computed directly from
the inner product via `∑_g φ(g) = 0` (`sum_apply_eq_zero_of_ne_trivial`) and the `Γ^#`-constancy. -/
theorem apply_one_sub_apply_eq_card_mul_inner {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {φ : IrreducibleCharacter Γ}
    (hφ1 : (φ : ClassFunction Γ ℂ) 1 = 1) (hφ : φ ≠ trivialIrreducibleCharacter Γ)
    (f : ClassFunction Γ ℂ) {z : Γ} (hconst : ∀ a : Γ, a ≠ 1 → f a = f z) :
    f 1 - f z = (Nat.card Γ : ℂ) * ClassFunction.inner f (φ : ClassFunction Γ ℂ) := by
  classical
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum, ← mul_assoc,
    mul_invOf_self, one_mul,
    ← Finset.add_sum_erase Finset.univ (fun g => f g * star ((φ : ClassFunction Γ ℂ) g))
      (Finset.mem_univ (1 : Γ)),
    hφ1, star_one, mul_one]
  have hstar : ∑ g ∈ Finset.univ.erase (1 : Γ), star ((φ : ClassFunction Γ ℂ) g) = -1 := by
    have h0 : ∑ g : Γ, star ((φ : ClassFunction Γ ℂ) g) = 0 := by
      rw [← star_sum, sum_apply_eq_zero_of_ne_trivial hφ, star_zero]
    rw [← Finset.add_sum_erase Finset.univ (fun g => star ((φ : ClassFunction Γ ℂ) g))
        (Finset.mem_univ (1 : Γ)), hφ1, star_one] at h0
    linear_combination h0
  have hsum : ∑ g ∈ Finset.univ.erase (1 : Γ), (f g * star ((φ : ClassFunction Γ ℂ) g)) = -f z := by
    rw [Finset.sum_congr rfl (fun g hg => by rw [hconst g (Finset.ne_of_mem_erase hg)]),
      ← Finset.mul_sum, hstar, mul_neg, mul_one]
  rw [hsum]; ring

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

/-- **(6.8.2.2) reciprocity step.**  For `α = Ind_{W₂}^L φ − c·η₁` with `α(1) = 0` and any
`ψ ∈ CF(G)`,
`⟨α^τ, ψ⟩ = ⟨φ, Res_{W₂} Res_L ψ⟩ − c·⟨η₁, Res_L ψ⟩`.
This is the move `⟨α^τ, ψ⟩ = ⟨α, Res_L ψ⟩ = ⟨φ, Res_Z ψ⟩ − |H:Z|⟨η₁, Res_L ψ⟩` of Peterfalvi
(6.8.2.2): the Dade reciprocity `inner_tau_eq_inner_restrict` (valid since `Supp(α) ⊆ H^#`,
`support_indW2_sub_smul_subset_sharpImage`), additivity (`inner_sub_left`/`inner_smul_left`), and
Frobenius reciprocity `inner_induce_eq_inner_restrict` for `Ind_{W₂}^L`. -/
theorem SibleyDadeHypothesis.inner_tau_indW2_sub_smul_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Fintype ↥W2] (hW2H : W2 ≤ H) [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 φ - c • η₁)) ψ
      = ClassFunction.inner φ (ClassFunction.restrict W2 (ClassFunction.restrict L ψ))
        - c * ClassFunction.inner η₁ (ClassFunction.restrict L ψ) := by
  rw [hyp.inner_tau_eq_inner_restrict
        (hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ c h1) ψ,
    ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_induce_eq_inner_restrict]

/-- **`Ĥ = H.map L.subtype` is a Sylow `p`-subgroup of `G`, from the Hall coprimality.**  This is
the coprimality-only generalization of `sylow_map_subtype_of_frobenius` (which uses
`hF.coprime_card_kernel_complement`): the Frobenius hypothesis is needed *only* to supply
`gcd(|H|, |W₁|) = 1`, which in the (6.8)(c2) case is the `cases` side condition.  With `H` a
`p`-group (the (6.5) reduction) and `H ◁ L` with `W₁` a coprime complement, `H` is the unique normal
Sylow `p`-subgroup of `↥L`; combined with `N_G(Ĥ) ≤ L` (`H^#` TI) this forces `Ĥ ∈ Syl_p(G)`.

(Dedupe candidate: `sylow_map_subtype_of_frobenius` in `S08_CoherenceCore` could delegate here.) -/
theorem SibleyDadeHypothesis.sylow_map_subtype_of_coprime
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Ĥ : Subgroup G := H.map L.subtype with hĤ_def
  have hĤp : IsPGroup p ↥Ĥ := hHp.map L.subtype
  have hpH : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hHp
    have h1 : 1 < Nat.card ↥H := (Subgroup.one_lt_card_iff_ne_bot (H := H)).mpr hyp.H_ne_bot
    rw [hn] at h1 ⊢
    rcases n with _ | n
    · simp at h1
    · exact dvd_pow_self p (Nat.succ_ne_zero n)
  have hpidx : ¬ p ∣ H.index := by
    rw [hyp.index_H_eq_card_W1]
    exact (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_left hpH hcop)
  set HSyl : Sylow p ↥L := hHp.toSylow hpidx with hHSyl_def
  have hHSyl : (HSyl : Subgroup ↥L) = H := IsPGroup.toSylow_coe hHp hpidx
  haveI hHSylNormal : (HSyl : Subgroup ↥L).Normal := by rw [hHSyl]; exact ‹H.Normal›
  haveI : Unique (Sylow p ↥L) := Sylow.unique_of_normal HSyl hHSylNormal
  have hpsub : ∀ K : Subgroup ↥L, IsPGroup p K → K ≤ H := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.exists_le_sylow
    calc K ≤ (R : Subgroup ↥L) := hR
      _ = (HSyl : Subgroup ↥L) := by rw [Subsingleton.elim R HSyl]
      _ = H := hHSyl
  have hNle : Subgroup.normalizer Ĥ ≤ L := hyp.normalizer_map_subtype_eq.le
  obtain ⟨Q, hĤQ⟩ := hĤp.exists_le_sylow
  refine ⟨Q, ?_⟩
  apply OddOrder.GroupTheory.sylow_coe_eq_of_normalizer_inf_le hĤQ
  intro x hx
  have hxL : x ∈ L := hNle hx.1
  have hQLp : IsPGroup p ((Q : Subgroup G).comap L.subtype : Subgroup ↥L) :=
    Q.isPGroup'.comap_of_injective L.subtype L.subtype_injective
  have hx'H : (⟨x, hxL⟩ : ↥L) ∈ H :=
    hpsub _ hQLp (Subgroup.mem_comap.mpr (by exact hx.2))
  exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hx'H, rfl⟩

/-- **The `Y`-coherence image of an `η ∈ Y` is `±` an irreducible character of `G`.**  Since `η` is
irreducible (`isIrreducibleCharacter_of_mem_Yset`, so `⟨η,η⟩ = 1`) and the coherence extension is
norm-preserving on `Z[Y]` (`extension_inner_eq`) with image in `ZIrr G` (`extension_mem_ZIrr`), the
image `η^{τ₁}` has squared norm `1`, hence equals `ε·ξ` for `ε = ±1` and `ξ ∈ Irr G`
(`exists_zsmul_irreducibleCharacter_of_inner_self_one`, Peterfalvi (5.9.a)).

This is the reduction that lets the (6.7) congruence for the *virtual* character `η^{τ₁}` be read
off the single irreducible `ξ` (which inherits `η^{τ₁}`'s `W₂^#`-constancy up to sign), in
Peterfalvi (6.8.2.2). -/
theorem SibleyDadeHypothesis.coherentYset_extension_eq_zsmul_irreducible
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        hyp.coherentYset.extension η = ε • (ξ : ClassFunction G ℂ) := by
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hηnorm : ClassFunction.inner η η = 1 := by
    have h := irreducibleCharacter_inner (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηspan : η ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Yset := Submodule.subset_span hη
  have hextnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η hηspan hηspan, hηnorm]
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one
    (hyp.coherentYset.extension_mem_ZIrr η hηspan) hextnorm

end OddOrder.Peterfalvi.S08
