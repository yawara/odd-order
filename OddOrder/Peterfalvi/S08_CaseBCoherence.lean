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
open scoped OddOrder.AlgInt

variable {G : Type*} [Group G]

/-- **Integer trichotomy from divisibility and a strict `< 2a²` norm bound** (Peterfalvi (6.8.2.2)
quadratic endgame).  The `< 2a²` variant of `eq_zero_or_edge_of_dvd_of_normBound` (which uses the
`≤ 1 + a²` bound of the Frobenius (6.8.1) case): in case (B) the source norm is `|L:Z| + |H:Z|²`
with `|L:Z| < |H:Z|²` (the `W₁`-fixed-point-free bound), giving `‖α^τ‖² < 2|H:Z|²`.

Writing `b = a·x` (`a = |H:Z|`), the bound forces `(x−1)² + (m−1)x² < 2`, hence `≤ 1`, so
`x ∈ {0, 1}` (and `x = 1` needs `m = 2`); `x = −1` is excluded since `4a² + (m−1)a² ≥ 2a²`. -/
theorem eq_zero_or_edge_of_dvd_of_normLt {a b m : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hdvd : a ∣ b)
    (hnorm : (b - a) ^ 2 + (m - 1) * b ^ 2 < 2 * a ^ 2) :
    b = 0 ∨ (b = a ∧ m = 2) := by
  obtain ⟨x, rfl⟩ := hdvd
  have ha0 : (0 : ℤ) < a := by linarith
  have hb2 : (a * x) ^ 2 < 2 * a ^ 2 := by
    nlinarith [sq_nonneg (a * x - a), mul_nonneg (by linarith : (0 : ℤ) ≤ m - 2) (sq_nonneg (a * x))]
  have hx2 : x ^ 2 ≤ 1 := by
    by_contra h
    push Not at h
    have hx2' : 2 ≤ x ^ 2 := h
    nlinarith [hb2, mul_pos ha0 ha0, mul_le_mul_of_nonneg_left hx2' (le_of_lt (mul_pos ha0 ha0))]
  have hxlo : -1 ≤ x := by nlinarith [hx2, sq_nonneg (x + 1)]
  have hxhi : x ≤ 1 := by nlinarith [hx2, sq_nonneg (x - 1)]
  interval_cases x
  · exfalso; nlinarith [hnorm, ha, hm, mul_pos ha0 ha0]
  · left; ring
  · right
    refine ⟨by ring, ?_⟩
    nlinarith [hnorm, ha, hm, mul_pos ha0 ha0]

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

/-- **Reverse of `Cong.of_int`: an algebraic-integer congruence between rational integers is an
ordinary `ℤ`-divisibility.**  If `(j : ℂ) ≡ (k : ℂ) [ALGMOD n]` with `j, k, n : ℤ` and `n ≠ 0`, then
`n ∣ j - k` in `ℤ`.  By `cong_def` the quotient `(j - k)/n` is an algebraic integer; being rational,
it is an ordinary integer (`isIntegral_rat_imp_int`), so `n ∣ j - k`.

This converts the (6.7) `ALGMOD |H|` congruence (applied to the rational-integer difference
`ψ(1) − ψ(z) = |W₂|·a`) into the divisibility `|H| ∣ |W₂|·a` of Peterfalvi (6.8.2.2). -/
theorem dvd_of_intCast_algMod {n j k : ℤ} (hn : (n : ℂ) ≠ 0)
    (h : (j : ℂ) ≡ (k : ℂ) [ALGMOD n]) : n ∣ j - k := by
  rw [OddOrder.AlgInt.cong_def] at h
  set q : ℚ := ((j : ℚ) - (k : ℚ)) / (n : ℚ) with hqdef
  have hqcast : (q : ℂ) = ((j : ℂ) - (k : ℂ)) / (n : ℂ) := by rw [hqdef]; push_cast; ring
  rw [← hqcast] at h
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int h
  have hn0 : n ≠ 0 := Int.cast_ne_zero.mp hn
  have hnℚ : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn0
  have hqm : q = (m : ℚ) := by exact_mod_cast hm
  rw [hqdef, div_eq_iff hnℚ] at hqm
  refine ⟨m, ?_⟩
  have hQ : ((j - k : ℤ) : ℚ) = ((n * m : ℤ) : ℚ) := by push_cast; linear_combination hqm
  exact_mod_cast hQ

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
    (_hyp : SibleyDadeHypothesis G L H) {z : ↥L} (hz : z ∈ ⁅H, H⁆) (hz1 : z ≠ 1) :
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
    exact hx (by simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
      h1', h2', mul_zero, sub_zero])
  have hxne : x ≠ 1 := by
    intro hx1
    refine hx ?_
    simp only [hx1, ClassFunction.sub_apply, ClassFunction.smul_apply, h1, sub_self]
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

/-- **Centralizer of a central element is everything (in `G`, intersected with `L`).**  If
`w ∈ Z(↥L)`, then `L ⊓ C_G((w : G)) = L`: every element of `L` commutes with `(w : G)`.  In the
(6.8)(c2) case-(B), `W₂ ⊆ Z(↥L)` (the math-(B) condition `W₂ ⊆ Z(H)` plus `W = W₁ ⊔ W₂` cyclic, so
`W₂` also commutes with `W₁`), so this gives the centralizer-card constancy on `W₂^#`
(`|N_G(Ĥ) ⊓ C_G(w)| = |L|` for all `w ∈ W₂^#`) — the second half of `peterfalvi_67_of_odd`'s
`hconst`, the analogue of the Frobenius `inf_centralizer_centralCommutator_map`. -/
theorem SibleyDadeHypothesis.inf_centralizer_eq_of_mem_center
    (_hyp : SibleyDadeHypothesis G L H) {w : ↥L} (hwc : w ∈ Subgroup.center ↥L) :
    (L : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G) = L := by
  rw [inf_eq_left]
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Subgroup.mem_center_iff] at hwc
  have h := congrArg L.subtype (hwc ⟨g, hg⟩)
  simpa using h

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2) case-(B) (6.7) adapter.**  The case-(B) analogue of
`peterfalvi_67_centralCommutator`: when `Z ≤ H` is a subgroup that is *central in `↥L`*
(`Z ≤ Z(↥L)` — in (6.8.2.2) this is `Z = W₂` under the math-(B) condition `W₂ ⊆ Z(H)` with `W`
cyclic), the (6.7) congruence

`ρ.character z ≡ ρ.character 1  (mod |H|)`

holds for `z ∈ Z^#` and any irreducible `ρ` whose character is constant on
`Z^# = (Z.map L.subtype)^#` (the only character-theoretic input, deferred to the caller — in
(6.8.2.2) it is `η₁^{τ₁}`).

The structural hypotheses of `peterfalvi_67_of_odd` are discharged at `P := Ĥ = H.map L.subtype`
(Sylow in `G` by `sylow_map_subtype_of_coprime`, with `N_G(Ĥ) = L` by `normalizer_map_subtype_eq`)
and `Z := Z.map L.subtype`: `hZP` (`Z ≤ H`), `hZnormal` (central ⇒ normal), `hti`/`hodd`
(`H^#` TI / `|L|` odd), `hPz` (`Ĥ ≤ L ≤ C_G(z)` since `z` is central), and the `|C_L(·)|`-constancy
clause of `hconst` (both sides `= |L|` by `inf_centralizer_eq_of_mem_center`).  The modulus
`|Ĥ| = |H|` via `card_map_of_injective`.  This is the (6.8)(c2) coprimality-only analogue of the
(6.8.1) Frobenius adapter; the Sylow is supplied by the `cases` side condition `gcd(|H|,|W₁|) = 1`. -/
theorem SibleyDadeHypothesis.peterfalvi_67_central (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcen : Z ≤ Subgroup.center ↥L)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ Z.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ Z.map L.subtype, w ≠ 1 → ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_coprime hcop hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- `Z` is normal in `↥L`: central subgroups are normal.
  have hZnorm : Z.Normal := ⟨fun n hn g => by
    have hc : g * n = n * g := (Subgroup.mem_center_iff.mp (hZcen hn)) g
    have hgn : g * n * g⁻¹ = n := by rw [hc]; exact mul_inv_cancel_right n g
    rw [hgn]; exact hn⟩
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : Z.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hZH
  have hZnormal : ((Z.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (Z.map L.subtype).subgroupOf L = Z from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hZnorm
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  obtain ⟨z₀, hz₀Z, hz₀eq⟩ := Subgroup.mem_map.mp hz
  have hz₀z : (z₀ : G) = z := hz₀eq
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    have hbz : (L : Subgroup G) ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G) = L :=
      hyp.inf_centralizer_eq_of_mem_center (hZcen hz₀Z)
    rw [hz₀z] at hbz
    calc (Q : Subgroup G) ≤ L := by rw [hQeq]; exact Subgroup.map_subtype_le H
      _ ≤ Subgroup.centralizer ({z} : Set G) := inf_eq_left.mp hbz
  have hconst : ∀ ⦃w : G⦄, w ∈ Z.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w₀, hw₀Z, hw₀eq⟩ := Subgroup.mem_map.mp hw
    have hw₀w : (w₀ : G) = w := hw₀eq
    rw [hNorm, ← hw₀w, ← hz₀z,
      hyp.inf_centralizer_eq_of_mem_center (hZcen hw₀Z),
      hyp.inf_centralizer_eq_of_mem_center (hZcen hz₀Z)]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2) case-(B) (6.7)-congruence for `η^{τ₁}`** (mmd 04.8 L186 →).  For `η ∈ Y` and
`z ∈ W₂^#`, `Res^G_L(η^{τ₁})(z) ≡ Res^G_L(η^{τ₁})(1) (mod |H|)`.  Wires the case-(B) (6.7) adapter
`peterfalvi_67_central` to `η^{τ₁}`: write `η^{τ₁} = ε•ξ` (`ε = ±1`, `ξ` irreducible from norm `1`,
`coherentYset_extension_eq_zsmul_irreducible`); unpack `ξ = ρ.character` (`ρ` irreducible,
`ξ.isIrreducible`).  The const-on-`W₂^#` of `η^{τ₁}` (`coherentYset_extension_const_on_W2`,
(6.8.2.1)) transfers to `ρ.character` (cancel `ε`), feeding the adapter to get
`ξ(z) ≡ ξ(1) (mod |H|)`; scale by `ε` (`Cong.smul_left`) for `η^{τ₁}(z) ≡ η^{τ₁}(1)`.

`W₂` is prime, `W₂ ⊆ ⁅H,H⁆` (the `cases` (c2) side conditions) and central in `↥L`
(`W₂ ⊆ Z(↥L)`, the math-(B) `W₂ ⊆ Z(H)` with `W` cyclic — deferred to the caller). -/
theorem SibleyDadeHypothesis.restrict_extension_Yset_charValue_cong_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ W2) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  obtain ⟨ε, ξ, hε, hηtε⟩ := hyp.coherentYset_extension_eq_zsmul_irreducible hη
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  have hsmul : ∀ g : G,
      (hyp.coherentYset.extension η) g = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  haveI : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ W2.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ W2.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.coherentYset_extension_const_on_W2 hprime hW2comm hη hz hz1 hw₀ hw₀1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_central hcop hp hHp hW2H hW2cen ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2) integration core: `|H| ∣ |W₂|·a`.**  For `ψ = η^{τ₁}` (`η ∈ Y`) and a nontrivial
*linear* `φ ∈ Irr W₂`, the regular-character coefficient `a = ⟨Res^L_{W₂} Res^G_L ψ, φ⟩` (an integer
`m`) satisfies `|H| ∣ |W₂|·m`.

This is the number-theoretic heart of Peterfalvi (6.8.2.2) ("`a ≡ 0 (mod |H:Z|)`"): pick `z₀ ∈ W₂^#`
(exists since `|W₂|` is prime); `ψ` (hence `Res_{W₂} Res_L ψ =: f`) is constant on `W₂^#`
(`coherentYset_extension_const_on_W2`), so the regular-character relation
`apply_one_sub_apply_eq_card_mul_inner` gives `f(1) − f(z₀) = |W₂|·m`; the (6.7) congruence
`restrict_extension_Yset_charValue_cong_caseB` gives `f(z₀) ≡ f(1) (mod |H|)`, i.e.
`f(1) − f(z₀) ≡ 0`; since that difference equals the rational integer `|W₂|·m`, the reverse bridge
`dvd_of_intCast_algMod` yields `|H| ∣ |W₂|·m`.  The caller cancels `|W₂|` (using `|H| = |H:W₂|·|W₂|`)
for `|H:W₂| ∣ m`. -/
theorem SibleyDadeHypothesis.card_H_dvd_card_W2_mul_regCharCoeff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2) {m : ℤ}
    (hm : ClassFunction.inner
            (ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)))
            (φ : ClassFunction ↥W2 ℂ) = (m : ℂ)) :
    (Nat.card ↥H : ℤ) ∣ (Nat.card ↥W2 : ℤ) * m := by
  classical
  set f : ClassFunction ↥W2 ℂ :=
    ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)) with hfdef
  -- a witness `z₀ ∈ W₂^#` (`|W₂|` prime ⇒ nontrivial).
  haveI : Nontrivial ↥W2 := Finite.one_lt_card_iff_nontrivial.mp hprime.one_lt
  obtain ⟨z₀, hz₀1⟩ := exists_ne (1 : ↥W2)
  -- `f` is constant on `W₂^#`.
  have hfconst : ∀ a : ↥W2, a ≠ 1 → f a = f z₀ := by
    intro a ha
    have hmemA : (W2.subtype a) ∈ W2 := SetLike.coe_mem a
    have hmemZ : (W2.subtype z₀) ∈ W2 := SetLike.coe_mem z₀
    have hA1 : (W2.subtype a) ≠ 1 := fun h => ha (W2.subtype_injective (by simpa using h))
    have hZ1 : (W2.subtype z₀) ≠ 1 := fun h => hz₀1 (W2.subtype_injective (by simpa using h))
    have hc := hyp.coherentYset_extension_const_on_W2 hprime hW2comm hη hmemZ hZ1 hmemA hA1
    simp only [hfdef, ClassFunction.restrict_apply]
    exact hc
  -- regular-character relation `f(1) − f(z₀) = |W₂|·m`.
  have hreg := apply_one_sub_apply_eq_card_mul_inner hφ1 hφ f (z := z₀) hfconst
  rw [hm] at hreg
  -- the value identities relating `f` to `Res_L ψ`.
  have hfz : f z₀ = (ClassFunction.restrict L (hyp.coherentYset.extension η)) (W2.subtype z₀) :=
    ClassFunction.restrict_apply W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)) z₀
  have hf1 : f 1 = (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    ClassFunction.restrict_apply W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
  have hZ1 : (W2.subtype z₀) ≠ 1 := fun h => hz₀1 (W2.subtype_injective (by simpa using h))
  -- (6.7) congruence `f(z₀) ≡ f(1) (mod |H|)`.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_caseB hcop hp hHp hprime hW2comm hW2cen hη
    (z := W2.subtype z₀) (SetLike.coe_mem z₀) hZ1
  rw [← hfz, ← hf1] at hcong
  -- `f(1) − f(z₀) ≡ 0 (mod |H|)`.
  have hsub : f 1 - f z₀ ≡ 0 [ALGMOD (Nat.card ↥H : ℤ)] := by
    have h := OddOrder.AlgInt.Cong.sub hcong.symm (OddOrder.AlgInt.Cong.refl (Nat.card ↥H : ℤ) (f z₀))
    simpa using h
  rw [hreg] at hsub
  -- convert to the integer congruence and apply the reverse bridge.
  have hcong_int : ((Nat.card ↥W2 * m : ℤ) : ℂ) ≡ ((0 : ℤ) : ℂ) [ALGMOD (Nat.card ↥H : ℤ)] := by
    have heq : ((Nat.card ↥W2 * m : ℤ) : ℂ) = (Nat.card ↥W2 : ℂ) * (m : ℂ) := by push_cast; ring
    rw [heq]; simpa using hsub
  have hHne : ((Nat.card ↥H : ℤ) : ℂ) ≠ 0 := by
    have h1 : (Nat.card ↥H : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    exact_mod_cast h1
  have hdvd := dvd_of_intCast_algMod hHne hcong_int
  rwa [sub_zero] at hdvd

/-- **(6.8.2.2) `|H:W₂| ∣ a`** (Peterfalvi (6.8.2.2): "`a ≡ 0 (mod |H:Z|)`").  Cancelling `|W₂|`
from the integration core `card_H_dvd_card_W2_mul_regCharCoeff` (`|H| ∣ |W₂|·m`) via the index
factorization `|H| = |H:W₂|·|W₂|` (`index_mul_card` on `W₂.subgroupOf H`, `subgroupOfEquivOfLe`):
the regular-character coefficient `m = ⟨Res_{W₂} Res_L η^{τ₁}, φ⟩` is divisible by the relative index
`[H:W₂] = (W₂.subgroupOf H).index`.  This is the textbook's `a ≡ 0 (mod |H:Z|)`. -/
theorem SibleyDadeHypothesis.index_W2_dvd_regCharCoeff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2) {m : ℤ}
    (hm : ClassFunction.inner
            (ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)))
            (φ : ClassFunction ↥W2 ℂ) = (m : ℂ)) :
    ((W2.subgroupOf H).index : ℤ) ∣ m := by
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have hdvd :=
    hyp.card_H_dvd_card_W2_mul_regCharCoeff hcop hp hHp hprime hW2comm hW2cen hη φ hφ1 hφ hm
  -- `|H| = |W₂| · |H:W₂|`
  have hcardeq : (Nat.card ↥H : ℤ) = (Nat.card ↥W2 : ℤ) * ((W2.subgroupOf H).index : ℤ) := by
    have h1 := Subgroup.index_mul_card (W2.subgroupOf H)
    have h2 : Nat.card ↥(W2.subgroupOf H) = Nat.card ↥W2 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv
    rw [h2] at h1
    rw [← h1]; push_cast; ring
  rw [hcardeq] at hdvd
  have hW2ne : (Nat.card ↥W2 : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  exact (mul_dvd_mul_iff_left hW2ne).mp hdvd

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2): `⟨α^τ, ψ⟩` is an integer `≡ 0 (mod |H:W₂|)`** for `ψ = η'^{τ₁} ∈ 𝒴^{τ₁}`.
With `α = Ind^L_{W₂}φ − |H:W₂|·η₁` (`φ` nontrivial linear, `η₁ ∈ Y` the anchor), the Dade reciprocity
`inner_tau_indW2_sub_smul_eq` gives `⟨α^τ, ψ⟩ = ⟨φ, Res^L_{W₂} Res^G_L ψ⟩ − |H:W₂|·⟨η₁, Res^G_L ψ⟩`.

The degree relation `c = |H:W₂|` is computed: `Ind_{W₂}φ(1) = [L:W₂]·φ(1) = [H:W₂]·|W₁| = |H:W₂|·η₁(1)`
(`induce_apply_one` + `relIndex_mul_index` + `index_H_eq_card_W1` + `Yset_apply_one`).  The first inner
product equals the integer `a = m` (`⟨φ, Res⟩ = star⟨Res, φ⟩ = m`, `inner_conj_symm`, `m` from
`mem_ZIrr_inner_int`), divisible by `[H:W₂]` (`index_W2_dvd_regCharCoeff`); the second is an integer
`b'` (`mem_ZIrr_inner_int` + flip).  Hence `⟨α^τ, ψ⟩ = m − [H:W₂]·b'`, an integer divisible by
`[H:W₂]`. -/
theorem SibleyDadeHypothesis.inner_tau_alpha_dvd_index
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    {η' : ClassFunction ↥L ℂ} (hη' : η' ∈ hyp.Yset) :
    ∃ n : ℤ,
      ClassFunction.inner
          (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁))
          (hyp.coherentYset.extension η') = (n : ℂ)
        ∧ ((W2.subgroupOf H).index : ℤ) ∣ n := by
  classical
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  set ψ := hyp.coherentYset.extension η' with hψ
  -- degree relation `Ind_{W₂}φ(1) = |H:W₂|·η₁(1)`.
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  have hrecip := hyp.inner_tau_indW2_sub_smul_eq hW2H (φ : ClassFunction ↥W2 ℂ) hη₁
    ((W2.subgroupOf H).index : ℂ) h1 ψ
  -- ZIrr chain and the integer `m`.
  have hψZ : ψ ∈ ZIrr G := hyp.coherentYset.extension_mem_ZIrr η' (Submodule.subset_span hη')
  have hResLZ : ClassFunction.restrict L ψ ∈ ZIrr ↥L := ClassFunction.restrict_mem_ZIrr L hψZ
  have hResWZ : ClassFunction.restrict W2 (ClassFunction.restrict L ψ) ∈ ZIrr ↥W2 :=
    ClassFunction.restrict_mem_ZIrr W2 hResLZ
  obtain ⟨m, hm⟩ := mem_ZIrr_inner_int φ hResWZ
  have hφRes : ClassFunction.inner (φ : ClassFunction ↥W2 ℂ)
      (ClassFunction.restrict W2 (ClassFunction.restrict L ψ)) = (m : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hm]; simp
  have hdvdm := hyp.index_W2_dvd_regCharCoeff hcop hp hHp hprime hW2comm hW2cen hη' φ hφ1 hφ hm
  -- the integer `b' = ⟨η₁, Res_L ψ⟩`.
  have hη₁irr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  obtain ⟨b', hb'⟩ := mem_ZIrr_inner_int (⟨η₁, hη₁irr⟩ : IrreducibleCharacter ↥L) hResLZ
  rw [show ((⟨η₁, hη₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η₁ from rfl] at hb'
  have hη₁Res : ClassFunction.inner η₁ (ClassFunction.restrict L ψ) = (b' : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hb']; simp
  refine ⟨m - (W2.subgroupOf H).index * b', ?_, ?_⟩
  · rw [hrecip, hφRes, hη₁Res]; push_cast; ring
  · exact dvd_sub hdvdm (dvd_mul_right ((W2.subgroupOf H).index : ℤ) b')

/-- **(6.8.2.2) norm preservation `‖α^τ‖² = ‖α‖²`** for `α = Ind^L_{W₂}φ − c·η₁` (`α(1) = 0`).  Since
`Supp(α) ⊆ H^#` (`support_indW2_sub_smul_subset_sharpImage`), the Dade isometry on the supported
singleton `{α}` (`dadeIntegralCharacterMap_inner_eq_on_supported_span`) gives
`⟨α^τ, α^τ⟩ = ⟨α, α⟩`.  This is the source of the norm bound `‖α^τ‖² = ‖α‖² = |L:Z| + |H:Z|²` in the
(6.8.2.2) trichotomy endgame (Peterfalvi (1.5.b)). -/
theorem SibleyDadeHypothesis.inner_self_tau_indW2_sub_smul
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 φ - c • η₁))
        (hyp.tau (ClassFunction.induce W2 φ - c • η₁))
      = ClassFunction.inner (ClassFunction.induce W2 φ - c • η₁)
        (ClassFunction.induce W2 φ - c • η₁) := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hsupp : (ClassFunction.induce W2 φ - c • η₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ c h1
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj
    (S := {ClassFunction.induce W2 φ - c • η₁})
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)

/-- **(6.8.2.2) source cross-term `⟨Ind_{W₂}φ, η' − η⟩ = 0`** for `η, η' ∈ Y`.  Every `η ∈ Y` is
constant on `⁅H,H⁆ ⊇ W₂` (`Yset_apply_eq_apply_one_of_mem_commutator`) with value `η(1) = |W₁|`
(`Yset_apply_one`), so `Res^L_{W₂}η' = Res^L_{W₂}η` (both the constant `|W₁|` on `W₂`).  Frobenius
reciprocity `inner_induce_eq_inner_restrict` then gives
`⟨Ind_{W₂}φ, η'⟩ = ⟨φ, Res_{W₂}η'⟩ = ⟨φ, Res_{W₂}η⟩ = ⟨Ind_{W₂}φ, η⟩`, hence the difference is `0`.

This is the source half of the (6.8.2.2) cross-term `⟨α^τ, η_j^{τ₁} − η_1^{τ₁}⟩ = |H:Z|`: with
`⟨η₁, η_j − η_1⟩ = −1` it gives `⟨α, η_j − η_1⟩ = |H:Z|`. -/
theorem SibleyDadeHypothesis.inner_induce_W2_Yset_diff_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)] (hW2comm : W2 ≤ ⁅H, H⁆)
    (φ : ClassFunction ↥W2 ℂ) {η η' : ClassFunction ↥L ℂ}
    (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) :
    ClassFunction.inner (ClassFunction.induce W2 φ) (η' - η) = 0 := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hRes : ClassFunction.restrict W2 η' = ClassFunction.restrict W2 η := by
    ext w
    have hmem : (↑w : ↥L) ∈ ⁅H, H⁆ := hW2comm (SetLike.coe_mem w)
    simp only [ClassFunction.restrict_apply]
    rw [hyp.Yset_apply_eq_apply_one_of_mem_commutator hη' hmem,
      hyp.Yset_apply_eq_apply_one_of_mem_commutator hη hmem,
      hyp.Yset_apply_one hη', hyp.Yset_apply_one hη]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_induce_eq_inner_restrict, hRes, sub_self]

/-- **(6.8.2.2) cross-term `⟨α^τ, (η' − η₁)^τ⟩ = c`** for `α = Ind^L_{W₂}φ − c·η₁` and `η', η₁ ∈ Y`,
`η' ≠ η₁`.  By the Dade isometry on the supported pair `{α, η' − η₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; both supported on `H^#` via
`support_indW2_sub_smul_subset_sharpImage` / `sMember_diffSupport_of_charValue_eq`) it reduces to the
source inner product `⟨α, η' − η₁⟩`, which expands to
`⟨Ind_{W₂}φ, η' − η₁⟩ − c·⟨η₁, η' − η₁⟩ = 0 − c·(0 − 1) = c` using the source orthogonality
`inner_induce_W2_Yset_diff_eq_zero` and the `Y`-orthonormality (the inner product is linear in its
first argument).

This is the (6.8.2.2) `j > 1` value `⟨α^τ, η_j^{τ₁} − η_1^{τ₁}⟩ = |H:Z|` in `τ`-form (the coherence
agreement `extension = τ` on the supported lattice converts `(η' − η₁)^τ` to `η'^{τ₁} − η₁^{τ₁}`),
with `c = (|H:W₂| : ℂ)`. -/
theorem SibleyDadeHypothesis.inner_tau_indW2_sub_smul_tau_Yset_diff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) (hW2comm : W2 ≤ ⁅H, H⁆)
    [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ η' : ClassFunction ↥L ℂ}
    (hη₁ : η₁ ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η₁) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 φ - c • η₁))
        (hyp.tau (η' - η₁)) = c := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hYirr : ∀ ψ ∈ hyp.Yset, IsIrreducibleCharacter ψ :=
    fun ψ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hsuppα : (ClassFunction.induce W2 φ - c • η₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ c h1
  have hsuppY : (η' - η₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη₁)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη₁).symm)
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj
    (S := ({ClassFunction.induce W2 φ - c • η₁, η' - η₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppα
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso, ClassFunction.inner_sub_left,
    hyp.inner_induce_W2_Yset_diff_eq_zero hW2comm φ hη₁ hη',
    ClassFunction.inner_smul_left, ClassFunction.inner_sub_right,
    hYon η₁ η' hη₁ hη', hYon η₁ η₁ hη₁ hη₁, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.2.1) coherence agreement `η'^{τ₁} − η₁^{τ₁} = (η' − η₁)^τ`** for `η₁, η' ∈ Y`.  The
`Y`-coherence extension `ν = ·^{τ₁}` agrees with the Dade map `τ` on the supported lattice
`zSupportedSpan Y H^#` (`IsCoherent.extends_on_supported`), and the equal-degree difference
`η' − η₁` lies there (`zSpan` membership + `sMember_diffSupport_of_charValue_eq` support).  Combined
with linearity (`map_sub`), `extension η' − extension η₁ = extension (η' − η₁) = τ (η' − η₁)`.

This converts the `τ`-form cross-term `inner_tau_indW2_sub_smul_tau_Yset_diff` into the
`𝒴^{τ₁}`-extension form used in the (6.8.2.2) decomposition `α^τ = X − |H:Z|η_1^{τ₁} + …`. -/
theorem SibleyDadeHypothesis.coherentYset_extension_Yset_diff_eq_tau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {η₁ η' : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) :
    hyp.coherentYset.extension η' - hyp.coherentYset.extension η₁ = hyp.tau (η' - η₁) := by
  have hmem : (η' - η₁) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hη') (Submodule.subset_span hη₁), ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη₁)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη₁).symm)
  rw [← map_sub]
  exact hyp.coherentYset.extends_on_supported (η' - η₁) hmem

omit [Fintype G] [Fintype ↥L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Inertia of a class function on a central subgroup is everything.**  If `W₂ ≤ Z(↥L)` (so `W₂` is
normal), conjugation by any `g ∈ ↥L` fixes each `w ∈ W₂` (`g·w·g⁻¹ = w`, centrality), hence
`conjBy g φ = φ` for every class function `φ` of `W₂`, i.e. `I_{↥L}(φ) = ⊤`.

In (6.8.2.2) this gives `‖Ind^L_{W₂}φ‖² = |L:W₂|` via
`card_mul_inner_self_induce_eq_card_inertia` (`|W₂|·‖Ind φ‖² = |I_L(φ)| = |L|`). -/
theorem inertia_eq_top_of_le_center
    {W2 : Subgroup ↥L} [W2.Normal] (hW2cen : W2 ≤ Subgroup.center ↥L)
    (φ : ClassFunction ↥W2 ℂ) :
    ClassFunction.inertia φ = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  rw [ClassFunction.mem_inertia]
  ext w
  rw [ClassFunction.conjBy_apply]
  have hval : g * (w : ↥L) * g⁻¹ = (w : ↥L) := by
    rw [Subgroup.mem_center_iff.mp (hW2cen w.2) g]
    exact mul_inv_cancel_right _ _
  exact congrArg (⇑φ) (Subtype.ext hval)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **Norm of an induced character from a central subgroup: `‖Ind^L_{W₂}φ‖² = |L:W₂|`** for `φ` an
irreducible (linear) character of `W₂ ≤ Z(↥L)`.  By `card_mul_inner_self_induce_eq_card_inertia`,
`|W₂|·‖Ind^L_{W₂}φ‖² = |I_{↥L}(φ)|`, and `I_{↥L}(φ) = ⊤` (`inertia_eq_top_of_le_center`), so the
right side is `|↥L|`; cancelling `|W₂|` and using `|↥L| = |W₂|·[L:W₂]` (`card_mul_index`) gives
`‖Ind φ‖² = [L:W₂] = W₂.index`.

This is the `|I_L(φ):Z| = |L:Z|` term of the (6.8.2.2) norm `‖α‖² = |L:Z| + |H:Z|²`. -/
theorem inner_self_induce_eq_index_of_le_center
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    (φ : IrreducibleCharacter ↥W2) :
    ClassFunction.inner (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ))
        (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)) = (W2.index : ℂ) := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hcard := card_mul_inner_self_induce_eq_card_inertia φ
  rw [inertia_eq_top_of_le_center hW2cen (φ : ClassFunction ↥W2 ℂ), Subgroup.card_top] at hcard
  have hLeq : (Nat.card ↥L : ℂ) = (Nat.card ↥W2 : ℂ) * (W2.index : ℂ) := by
    rw [← Subgroup.card_mul_index W2]; push_cast; ring
  rw [hLeq] at hcard
  have hW2ne : (Nat.card ↥W2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ hW2ne hcard

/-- **(6.8.2.2) single cross-term `⟨Ind_{W₂}φ, η⟩ = 0`** for a *nontrivial* `φ ∈ Irr W₂` and `η ∈ Y`.
By Frobenius reciprocity `⟨Ind_{W₂}φ, η⟩ = ⟨φ, Res^L_{W₂}η⟩`, and `Res^L_{W₂}η` is the constant `|W₁|`
on `W₂` (each `η ∈ Y` is constant `η(1) = |W₁|` on `⁅H,H⁆ ⊇ W₂`,
`Yset_apply_eq_apply_one_of_mem_commutator` + `Yset_apply_one`); the inner product then factors as
`|W₂|⁻¹·(∑_{w} φ(w))·\overline{|W₁|} = 0` since `∑_w φ(w) = 0` for the nontrivial `φ`
(`sum_apply_eq_zero_of_ne_trivial`).

This is the cross term of the (6.8.2.2) norm `‖α‖² = ‖Ind_{W₂}φ‖² + |H:Z|²` (`⟨Ind_{W₂}φ, η₁⟩ = 0`). -/
theorem SibleyDadeHypothesis.inner_induce_W2_Yset_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)] (hW2comm : W2 ≤ ⁅H, H⁆)
    (φ : IrreducibleCharacter ↥W2) (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)) η = 0 := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
  have hconst : ∀ w : ↥W2, ClassFunction.restrict W2 η w = (Nat.card hyp.W1 : ℂ) := by
    intro w
    rw [ClassFunction.restrict_apply,
      hyp.Yset_apply_eq_apply_one_of_mem_commutator hη (hW2comm (SetLike.coe_mem w)),
      hyp.Yset_apply_one hη]
  simp only [hconst]
  rw [← Finset.sum_mul, sum_apply_eq_zero_of_ne_trivial hφ, zero_mul, mul_zero]

/-- **(6.8.2.2) source norm `‖α‖² = |L:W₂| + c·c̄`** for `α = Ind^L_{W₂}φ − c·η₁` (`φ` nontrivial
linear, `η₁ ∈ Y`, `W₂ ≤ Z(↥L)`).  Expanding the inner product and using `‖Ind_{W₂}φ‖² = |L:W₂|`
(`inner_self_induce_eq_index_of_le_center`), the vanishing cross terms `⟨Ind_{W₂}φ, η₁⟩ = 0`
(`inner_induce_W2_Yset_eq_zero`, and its conjugate), and `‖η₁‖² = 1` (irreducibility):
`‖α‖² = |L:W₂| + c·c̄`.

For the assembly coefficient `c = (|H:W₂| : ℂ)` (real), `c·c̄ = |H:W₂|²`, giving Peterfalvi's
`‖α‖² = |L:Z| + |H:Z|²`.  Combined with `inner_self_tau_indW2_sub_smul` (`‖α^τ‖² = ‖α‖²`), this is the
norm input to the (6.8.2.2) trichotomy. -/
theorem SibleyDadeHypothesis.inner_self_indW2_sub_smul_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hW2comm : W2 ≤ ⁅H, H⁆) (hW2cen : W2 ≤ Subgroup.center ↥L)
    (φ : IrreducibleCharacter ↥W2) (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ) :
    ClassFunction.inner (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) - c • η₁)
        (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) - c • η₁)
      = (W2.index : ℂ) + c * star c := by
  have hIndnorm := inner_self_induce_eq_index_of_le_center hW2cen φ
  have hcross := hyp.inner_induce_W2_Yset_eq_zero hW2comm φ hφ hη₁
  have hcross' : ClassFunction.inner η₁ (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcross, star_zero]
  have hη₁n : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η₁, hyp.isIrreducibleCharacter_of_mem_Yset hη₁⟩ : IrreducibleCharacter ↥L)
      (⟨η₁, hyp.isIrreducibleCharacter_of_mem_Yset hη₁⟩ : IrreducibleCharacter ↥L)
    simpa using h
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
  rw [hIndnorm, hcross, hcross', hη₁n]
  ring

open scoped Classical in
/-- **(6.8.2.2) coefficient dichotomy** (the case-(B) analogue of `coeff_eq_neg_or_edge_of_frobenius`).
For `α = Ind^L_{W₂}φ − |H:Z|·η₁` (`φ` nontrivial linear, `η₁ ∈ Y`), the multiplicity
`⟨α^τ, η₁^{τ₁}⟩` is either `−|H:Z|` or (when `|Y| = 2`) `0`.

Following Peterfalvi (6.8.2.2): set `bb = ⟨α^τ, η₁^{τ₁}⟩ ∈ ℤ` with `|H:Z| ∣ bb`
(`inner_tau_alpha_dvd_index`); for `η ≠ η₁`, `⟨α^τ, η^{τ₁}⟩ = bb + |H:Z|` (cross-term
`inner_tau_indW2_sub_smul_tau_Yset_diff` + agreement `coherentYset_extension_Yset_diff_eq_tau`).
Bessel's inequality over the orthonormal `𝒴^{τ₁}` (`sum_sq_le_inner_self_re`) with the norm
`‖α^τ‖² = |L:Z| + |H:Z|²` (`inner_self_tau_indW2_sub_smul` ∘ `inner_self_indW2_sub_smul_eq`) gives
`bb² + (m−1)(bb+|H:Z|)² ≤ |L:Z| + |H:Z|²`; with the fixed-point-free bound `|L:Z| < |H:Z|²`
(`hFPF`) this is `< 2|H:Z|²`, and `eq_zero_or_edge_of_dvd_of_normLt` forces `bb ∈ {−|H:Z|, 0}`.

`hc2` (`2 ≤ |H:Z|`) and `hFPF` (`|L:Z| < |H:Z|²`) are the deferred `W₁`-FPF-on-`H/W₂` inputs. -/
theorem SibleyDadeHypothesis.coeff_eq_neg_or_edge_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁)
        = -((W2.subgroupOf H).index : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.inner_tau_alpha_dvd_index hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hη₁
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Yset hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Yset hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hEinj : ∀ η ∈ hyp.Yset, ∀ η' ∈ hyp.Yset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' := by
    intro η hη η' hη' heq
    by_contra hne
    have h0 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 0 := by
      rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span hη)
        (Submodule.subset_span hη'), hYon η η' hη hη', if_neg hne]
    have h1' : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1'] at h0; exact one_ne_zero h0
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + (W2.subgroupOf H).index : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm φ hη₁ hη hee
        ((W2.subgroupOf H).index : ℂ) h1
      rw [← hyp.coherentYset_extension_Yset_diff_eq_tau hη₁ hη,
        ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  have hmemt : ∀ {η}, η ∈ hyp.Yset_finite.toFinset ↔ η ∈ hyp.Yset :=
    fun {η} => hyp.Yset_finite.mem_toFinset
  have hEinj_t : ∀ η ∈ hyp.Yset_finite.toFinset, ∀ η' ∈ hyp.Yset_finite.toFinset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' :=
    fun η hη η' hη' => hEinj η (hmemt.mp hη) η' (hmemt.mp hη')
  have horth : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ∀ ψ' ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ hψ ψ' hψ'
    rw [Finset.mem_image] at hψ hψ'
    obtain ⟨η, hη, rfl⟩ := hψ
    obtain ⟨η', hη', rfl⟩ := hψ'
    rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span (hmemt.mp hη))
      (Submodule.subset_span (hmemt.mp hη')), hYon η η' (hmemt.mp hη) (hmemt.mp hη')]
    by_cases hee : η = η'
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η' hη' h))]
  have hη₁t : η₁ ∈ hyp.Yset_finite.toFinset := hmemt.mpr hη₁
  have hβval : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb else bb + (W2.subgroupOf H).index : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)) hβval
  have hnorm_re : (ClassFunction.inner
      (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁))
      (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁))).re
      = ((W2.index + (W2.subgroupOf H).index ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_indW2_sub_smul hW2H φ hη₁ ((W2.subgroupOf H).index : ℂ) h1,
      hyp.inner_self_indW2_sub_smul_eq hW2comm hW2cen φ hφ hη₁ ((W2.subgroupOf H).index : ℂ),
      show (W2.index : ℂ) + ((W2.subgroupOf H).index : ℂ) * star ((W2.subgroupOf H).index : ℂ)
          = ((W2.index + (W2.subgroupOf H).index ^ 2 : ℕ) : ℂ) by
        rw [star_natCast]; push_cast; ring,
      Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + (W2.subgroupOf H).index) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb
          else bb + (W2.subgroupOf H).index) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + (W2.subgroupOf H).index) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hcrd : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hcrd, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2
      ≤ (W2.index : ℤ) + ((W2.subgroupOf H).index : ℤ) ^ 2 := by
    have hb := hbessel
    rw [show ((W2.index + (W2.subgroupOf H).index ^ 2 : ℕ) : ℝ)
        = (((W2.index : ℤ) + ((W2.subgroupOf H).index : ℤ) ^ 2 : ℤ) : ℝ) by push_cast; ring] at hb
    exact_mod_cast hb
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hc2' : (2 : ℤ) ≤ ((W2.subgroupOf H).index : ℤ) := by exact_mod_cast hc2
  have hnorm_lt : ((bb + (W2.subgroupOf H).index) - ((W2.subgroupOf H).index : ℤ)) ^ 2
      + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2
      < 2 * ((W2.subgroupOf H).index : ℤ) ^ 2 := by
    rw [show (bb + ((W2.subgroupOf H).index : ℤ)) - ((W2.subgroupOf H).index : ℤ) = bb by ring]
    have : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2
        < 2 * ((W2.subgroupOf H).index : ℤ) ^ 2 := by linarith [hnorm_ineq, hFPF]
    convert this using 2
  have hdich := eq_zero_or_edge_of_dvd_of_normLt hc2' hm2 (dvd_add habb (dvd_refl _)) hnorm_lt
  rcases hdich with h | ⟨h1', h2⟩
  · left
    rw [hbb]
    have hbeq : bb = -((W2.subgroupOf H).index : ℤ) := by omega
    rw [hbeq]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have hbeq : bb = 0 := by omega
    rw [hbeq]; norm_num

/-- **(6.8.2.2) good-case `X`-structure** (the case-(B) analogue of the Frobenius
`orthogonal_normOne_tau_scaledDiff_add_extension`).  In the good case
`⟨α^τ, η₁^{τ₁}⟩ = −|H:Z|` (the `bb = −|H:Z|` branch of `coeff_eq_neg_or_edge_caseB`), the element
`X := α^τ + |H:Z|·η₁^{τ₁}` is orthogonal to the whole coherent `Y`-image family `𝒴^{τ₁}` and lies in
`ℤ[Irr G]`, giving the decomposition `α^τ = X − |H:Z|·η₁^{τ₁}` of Peterfalvi (6.8.2.2).

(Unlike the Frobenius (6.8.1) case, `‖X‖² ≠ 1` — here `‖X‖² = |L:Z|`, since `Ind^L_{W₂}φ` is not a
single irreducible — so only orthogonality and `ℤ[Irr G]`-membership are asserted.) -/
theorem SibleyDadeHypothesis.orthogonal_tau_indW2_add_extension_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) (hW2comm : W2 ≤ ⁅H, H⁆)
    [Invertible (Nat.card ↥W2 : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁)
      = -((W2.subgroupOf H).index : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.coherentYset.extension η) = 0)
      ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • hyp.coherentYset.extension η₁ ∈ ZIrr G := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (hyp.coherentYset.extension η) (hyp.coherentYset.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span hη)
      (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm φ hη₁ hη hne
      ((W2.subgroupOf H).index : ℂ) h1
    rw [← hyp.coherentYset_extension_Yset_diff_eq_tau hη₁ hη,
      ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  have he₁e₁ : ClassFunction.inner (hyp.coherentYset.extension η₁)
      (hyp.coherentYset.extension η₁) = 1 := by rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  refine ⟨?_, ?_⟩
  · intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee; rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (Ne.symm hee)]; ring
  · have hsuppX : (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁).support
        ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ _ h1
    have hsrcZ : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁ ∈ ZIrr (↥L) := by
      rw [Nat.cast_smul_eq_nsmul]
      exact sub_mem (ClassFunction.induce_mem_ZIrr W2 (IsIrreducibleCharacter.mem_ZIrr φ.2))
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr (W2.subgroupOf H).index)
    have hvZ : hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hyp.hconj hsuppX hsrcZ
    have he₁Z : ((W2.subgroupOf H).index : ℂ) • hyp.coherentYset.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hyp.coherentYset.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁))
        (W2.subgroupOf H).index
    exact add_mem hvZ he₁Z

open scoped Classical in
/-- **(6.8.2.2) good case for `|Y| ≥ 3`.**  When `m = |Y| ≥ 3`, the edge case (`m = 2`) of
`coeff_eq_neg_or_edge_caseB` is impossible, so the good value `⟨α^τ, η₁^{τ₁}⟩ = −|H:Z|` holds with no
relabel.  Combined with `orthogonal_tau_indW2_add_extension_caseB`, this gives the (6.8.2.2)
decomposition `α^τ = X − |H:Z|·η₁^{τ₁}` (`X ⊥ 𝒴^{τ₁}`, `X ∈ ℤ[Irr G]`) unconditionally for `|Y| ≥ 3`
(the `m = 2` edge requires the `η₁^{τ₁} ↦ −η₂^{τ₁}` relabel, handled separately). -/
theorem SibleyDadeHypothesis.inner_tau_indW2_extension_Yset_eq_neg_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2)
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁)
      = -((W2.subgroupOf H).index : ℂ) := by
  rcases hyp.coeff_eq_neg_or_edge_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hc2 hFPF with
    h | ⟨hm2, _⟩
  · exact h
  · exfalso; omega

open scoped Classical in
/-- **(6.8.2.2) Y-coherence witness with the good value** (case-(B) analogue of
`exists_Ycoherence_hgood_of_frobenius`, the `m = 2` relabel folded in).  Produces a `Y`-coherence
witness `cY` with `⟨α^τ, cY.extension η₁⟩ = −|H:Z|` — the uniform `hgood` consumed by the τ₂
assembly.  Generic `|Y| ≥ 3`: `cY = coherentYset` (good branch of `coeff_eq_neg_or_edge_caseB`).
Edge `|Y| = 2`: `coherentYset` may give the bad value `0`; then `Y = {η₁, η₂}` and the sign-swapped
witness `cY'` (`coherentEqualDegree_swap_neg`, `η₁ ↦ −η₂^{τ₁}`) gives
`⟨α^τ, cY' η₁⟩ = −⟨α^τ, η₂^{τ₁}⟩ = −|H:Z|`, since `⟨α^τ, η₂^{τ₁}⟩ = ⟨α^τ, η₁^{τ₁}⟩ + |H:Z| = 0 + |H:Z|`
(`inner_tau_indW2_sub_smul_tau_Yset_diff` + `extends_on_supported`). -/
theorem SibleyDadeHypothesis.exists_Ycoherence_hgood_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
        = -((W2.subgroupOf H).index : ℂ) := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  rcases hyp.coeff_eq_neg_or_edge_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hc2 hFPF with
    hgood | ⟨hm2, hbad⟩
  · exact ⟨hyp.coherentYset, hgood⟩
  · obtain ⟨η₂, hη₂Y, hη₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
    have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
      intro x hx; rcases hx with rfl | rfl
      · exact hη₁
      · exact hη₂Y
    have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
      (Set.eq_of_subset_of_ncard_le hpairsub (hm2.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm)
        hyp.Yset_finite).symm
    have hinner : ∀ ψ ψ' : ClassFunction ↥L ℂ, IsIrreducibleCharacter ψ → IsIrreducibleCharacter ψ' →
        ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
      intro ψ ψ' hψ hψ'
      have h := irreducibleCharacter_inner (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ', hψ'⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : ψ = ψ'
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hY1irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
    have hY2irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₂Y
    have horth : ClassFunction.inner η₁ η₂ = 0 := by
      rw [hinner η₁ η₂ hY1irr hY2irr, if_neg (Ne.symm hη₂ne)]
    have hn1 : ClassFunction.inner η₁ η₁ = 1 := by rw [hinner η₁ η₁ hY1irr hY1irr, if_pos rfl]
    have hn2 : ClassFunction.inner η₂ η₂ = 1 := by rw [hinner η₂ η₂ hY2irr hY2irr, if_pos rfl]
    have hdeg : (η₂ : ↥L → ℂ) 1 = (η₁ : ↥L → ℂ) 1 :=
      (hyp.Yset_apply_one hη₂Y).trans (hyp.Yset_apply_one hη₁).symm
    have hdeg0 : (η₁ : ↥L → ℂ) 1 ≠ 0 := by
      rw [hyp.Yset_apply_one hη₁]; exact_mod_cast Nat.card_pos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (η₂ - η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₂Y) (hyp.Yset_subset_S hη₁) hdeg
    have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
    obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdeg hdeg0 h1A hsupp
    refine ⟨hYeq.symm ▸ cY', ?_⟩
    have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm φ hη₁ hη₂Y hη₂ne
      ((W2.subgroupOf H).index : ℂ) h1
    rw [← hyp.coherentYset_extension_Yset_diff_eq_tau hη₁ hη₂Y,
      ClassFunction.inner_sub_right, hbad, sub_zero] at hconst
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
      ClassFunction.inner_neg_right, hconst]

/-- **(6.8.2.2) `φ`-independence of `⟨α^τ, η'^{τ₁}⟩`** (Peterfalvi's "`Y` is independent of `φ`").
For `α_φ = Ind^L_{W₂}φ − |H:W₂|·η₁` (`φ` a nontrivial linear character of the central `W₂`), the
multiplicity `⟨α_φ^τ, η'^{τ₁}⟩` against a *fixed* `η' ∈ Y` is the **same** for all nontrivial linear
`φ`.

Proof: by Dade reciprocity (`inner_tau_indW2_sub_smul_eq`) the multiplicity is
`⟨φ, Res_{W₂} Res_L η'^{τ₁}⟩ − |H:W₂|·⟨η₁, Res_L η'^{τ₁}⟩`; the second term is already `φ`-free, and
the first equals `(f 1 − f z)/|W₂|` (`apply_one_sub_apply_eq_card_mul_inner`, since
`f = Res_{W₂} Res_L η'^{τ₁}` is constant on `W₂^#` by (6.8.2.1)
`coherentYset_extension_const_on_W2`) — visibly independent of `φ`.  This is the fact that makes the
`m = 2` relabel choice in `exists_Ycoherence_hgood_uniform_caseB` uniform across all `φ`. -/
theorem SibleyDadeHypothesis.inner_tau_alpha_extension_phiIndep
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {η' : ClassFunction ↥L ℂ} (hη' : η' ∈ hyp.Yset)
    (φ φ' : IrreducibleCharacter ↥W2)
    (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1) (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hφ'1 : (φ' : ClassFunction ↥W2 ℂ) 1 = 1) (hφ' : φ' ≠ trivialIrreducibleCharacter ↥W2) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η')
      = ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ' : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η') := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have hdeg : ∀ χ : ClassFunction ↥W2 ℂ, χ 1 = 1 →
      ClassFunction.induce W2 χ 1 = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    intro χ hχ1
    rw [ClassFunction.induce_apply_one, hχ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  rw [hyp.inner_tau_indW2_sub_smul_eq hW2H (φ : ClassFunction ↥W2 ℂ) hη₁
        ((W2.subgroupOf H).index : ℂ) (hdeg _ hφ1) (hyp.coherentYset.extension η'),
    hyp.inner_tau_indW2_sub_smul_eq hW2H (φ' : ClassFunction ↥W2 ℂ) hη₁
        ((W2.subgroupOf H).index : ℂ) (hdeg _ hφ'1) (hyp.coherentYset.extension η')]
  set f := ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η'))
    with hf
  haveI : Nontrivial ↥W2 := Finite.one_lt_card_iff_nontrivial.mp hprime.one_lt
  obtain ⟨z₀, hz₀1⟩ := exists_ne (1 : ↥W2)
  have hfconst : ∀ a : ↥W2, a ≠ 1 → f a = f z₀ := by
    intro a ha
    have hA1 : (W2.subtype a) ≠ 1 := fun h => ha (W2.subtype_injective (by simpa using h))
    have hZ1 : (W2.subtype z₀) ≠ 1 := fun h => hz₀1 (W2.subtype_injective (by simpa using h))
    have hc := hyp.coherentYset_extension_const_on_W2 hprime hW2comm hη'
      (SetLike.coe_mem z₀) hZ1 (SetLike.coe_mem a) hA1
    simp only [hf, ClassFunction.restrict_apply]
    exact hc
  have hcard : (Nat.card ↥W2 : ℂ) ≠ 0 := by
    have h := Nat.card_pos (α := ↥W2); exact_mod_cast h.ne'
  have key : ClassFunction.inner f (φ : ClassFunction ↥W2 ℂ)
      = ClassFunction.inner f (φ' : ClassFunction ↥W2 ℂ) := by
    apply mul_left_cancel₀ hcard
    rw [← apply_one_sub_apply_eq_card_mul_inner hφ1 hφ f (z := z₀) hfconst,
      ← apply_one_sub_apply_eq_card_mul_inner hφ'1 hφ' f (z := z₀) hfconst]
  rw [OddOrder.RepresentationTheory.inner_conj_symm f (φ : ClassFunction ↥W2 ℂ),
    OddOrder.RepresentationTheory.inner_conj_symm f (φ' : ClassFunction ↥W2 ℂ), key]

open scoped Classical in
/-- **(6.8.2.2) uniform good-value `Y`-coherence** (the `hYcard`-free strengthening of
`exists_Ycoherence_hgood_caseB`).  Produces a *single* `Y`-coherence `cY` whose (6.8.2.2) anchor
multiplicity is the good value `−|H:W₂|` **simultaneously for every** nontrivial linear
`φ ∈ Irr(W₂)`.

The `m = 2` relabel (`coherentEqualDegree_swap_neg`, `η₁ ↦ −η₂^{τ₁}`) is folded in *uniformly*:
by `φ`-independence (`inner_tau_alpha_extension_phiIndep`) the good/edge branch of
`coeff_eq_neg_or_edge_caseB` is the same for **all** `φ`, so one global choice of `cY` suffices —
`coherentYset` when `|Y| ≥ 3` or the good branch holds, and the sign-swap relabel in the `|Y| = 2`
edge.  This removes the `|Y| ≠ 2` side condition (`hYcard`) from the case-(B) `X ∪ Y`-coherence
chain. -/
theorem SibleyDadeHypothesis.exists_Ycoherence_hgood_uniform_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ∀ (φ : IrreducibleCharacter ↥W2), (φ : ClassFunction ↥W2 ℂ) 1 = 1 →
        φ ≠ trivialIrreducibleCharacter ↥W2 →
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((W2.subgroupOf H).index : ℂ) := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  classical
  by_cases hYc : hyp.Yset.ncard = 2
  · -- `|Y| = 2` edge: pick the branch with one `φ₀`, propagate by `φ`-independence.
    by_cases hex : ∃ φ₀ : IrreducibleCharacter ↥W2,
        (φ₀ : ClassFunction ↥W2 ℂ) 1 = 1 ∧ φ₀ ≠ trivialIrreducibleCharacter ↥W2
    · obtain ⟨φ₀, hφ₀1, hφ₀⟩ := hex
      rcases hyp.coeff_eq_neg_or_edge_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ₀ hφ₀1 hφ₀ hc2 hFPF
        with hgood₀ | ⟨_, hbad₀⟩
      · -- good branch: `cY = coherentYset`.
        refine ⟨hyp.coherentYset, fun φ hφ1 hφ => ?_⟩
        rw [hyp.inner_tau_alpha_extension_phiIndep hprime hW2comm hη₁ hη₁ φ φ₀ hφ1 hφ hφ₀1 hφ₀]
        exact hgood₀
      · -- edge branch: `cY = coherentEqualDegree_swap_neg`.
        obtain ⟨η₂, hη₂Y, hη₂ne⟩ :=
          Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
        have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
          intro x hx; rcases hx with rfl | rfl
          · exact hη₁
          · exact hη₂Y
        have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
          (Set.eq_of_subset_of_ncard_le hpairsub
            (hYc.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm) hyp.Yset_finite).symm
        have hinner : ∀ ψ ψ' : ClassFunction ↥L ℂ, IsIrreducibleCharacter ψ →
            IsIrreducibleCharacter ψ' →
            ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
          intro ψ ψ' hψ hψ'
          have h := irreducibleCharacter_inner (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
            (⟨ψ', hψ'⟩ : IrreducibleCharacter ↥L)
          simp only [IrreducibleCharacter.coe_mk] at h
          rw [h]
          by_cases hpq : ψ = ψ'
          · rw [if_pos (Subtype.ext hpq), if_pos hpq]
          · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
        have hY1irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
        have hY2irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₂Y
        have horth : ClassFunction.inner η₁ η₂ = 0 := by
          rw [hinner η₁ η₂ hY1irr hY2irr, if_neg (Ne.symm hη₂ne)]
        have hn1 : ClassFunction.inner η₁ η₁ = 1 := by rw [hinner η₁ η₁ hY1irr hY1irr, if_pos rfl]
        have hn2 : ClassFunction.inner η₂ η₂ = 1 := by rw [hinner η₂ η₂ hY2irr hY2irr, if_pos rfl]
        have hdegeq : (η₂ : ↥L → ℂ) 1 = (η₁ : ↥L → ℂ) 1 :=
          (hyp.Yset_apply_one hη₂Y).trans (hyp.Yset_apply_one hη₁).symm
        have hdeg0 : (η₁ : ↥L → ℂ) 1 ≠ 0 := by
          rw [hyp.Yset_apply_one hη₁]; exact_mod_cast Nat.card_pos.ne'
        have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
          rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
        have hsupp : (η₂ - η₁).support ⊆
            OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
          hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₂Y) (hyp.Yset_subset_S hη₁)
            hdegeq
        have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
          OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
        obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
          (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdegeq hdeg0 h1A hsupp
        refine ⟨hYeq.symm ▸ cY', fun φ hφ1 hφ => ?_⟩
        have hW2H : W2 ≤ H := by
          have hle : ⁅H, H⁆ ≤ H := by
            rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
            exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
          exact hW2comm.trans hle
        have h1φ : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
            = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
          rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
          have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
            (Subgroup.relIndex_mul_index hW2H).symm
          rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
        have hvφ : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁) = 0 := by
          rw [hyp.inner_tau_alpha_extension_phiIndep hprime hW2comm hη₁ hη₁ φ φ₀ hφ1 hφ hφ₀1 hφ₀]
          exact hbad₀
        have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm
          (φ : ClassFunction ↥W2 ℂ) hη₁ hη₂Y hη₂ne ((W2.subgroupOf H).index : ℂ) h1φ
        rw [← hyp.coherentYset_extension_Yset_diff_eq_tau hη₁ hη₂Y,
          ClassFunction.inner_sub_right, hvφ, sub_zero] at hconst
        rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
          ClassFunction.inner_neg_right, hconst]
    · -- no nontrivial linear `φ`: the `∀ φ` is vacuous.
      exact ⟨hyp.coherentYset, fun φ hφ1 hφ => absurd ⟨φ, hφ1, hφ⟩ hex⟩
  · -- `|Y| ≥ 3`: every `φ` lies in the good branch; `cY = coherentYset`.
    refine ⟨hyp.coherentYset, fun φ hφ1 hφ => ?_⟩
    have hm3 : 3 ≤ hyp.Yset.ncard := by have := hyp.two_le_Yset_ncard; omega
    exact hyp.inner_tau_indW2_extension_Yset_eq_neg_caseB hcop hp hHp hprime hW2comm hW2cen hη₁
      φ hφ1 hφ hc2 hFPF hm3

end OddOrder.Peterfalvi.S08
