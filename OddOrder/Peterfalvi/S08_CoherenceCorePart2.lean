/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart2.SibleyBounds

/-!
# Peterfalvi §8: normalized degree gaps

Generic normalized-degree and common-index divisibility lemmas for the §8 adjoining steps.
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-- **(T8.11m) normalized degree gap from an absolute degree bound.**

If the new character and the prefix member family have natural degree ratios against the same
anchor `χ₁`, then the absolute §6.6 inequality
`2 * χ(1) * χ₁(1) < ∑ χmem(j)(1)^2` is equivalent, after dividing by the positive square
`χ₁(1)^2`, to the normalized `XAdjoinStepInput.hDeg` inequality
`2 * a < ∑ deg(j)^2`. -/
theorem normalizedDegreeGap_of_realDegreeBound
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a : ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hAbs : 2 *
        ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 := by
  classical
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  have hd₁real_pos : 0 < (d₁ : ℝ) := by exact_mod_cast hd₁pos
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re =
        (a : ℝ) * (d₁ : ℝ) := by
    have h := congrArg Complex.re hχdeg
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hmemre : ∀ i ∈ s,
      (OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re =
        (deg i : ℝ) * (d₁ : ℝ) := by
    intro i hi
    have h := congrArg Complex.re (hmemdeg i hi)
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hleft :
      2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) =
        (2 * (a : ℝ)) * (d₁ : ℝ) ^ 2 := by
    rw [hχre, hχ₁re]
    ring
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, (((deg i : ℝ) * (d₁ : ℝ)) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmemre i hi]
      _ = ∑ i ∈ s, ((deg i : ℝ) ^ 2 * (d₁ : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
            rw [← Finset.sum_mul]
  rw [hleft, hright] at hAbs
  have hd₁sq_pos : 0 < (d₁ : ℝ) ^ 2 := sq_pos_of_pos hd₁real_pos
  nlinarith

/-- **(T8.11n) real absolute degree bound from natural prime-power data.**

This is the adapter from the pure §6.6 number-theoretic leaf in §7 to the real-valued
bound used by
`normalizedDegreeGap_of_realDegreeBound`: if natural degree values identify `χ(1)=dχ`,
`χ₁(1)=d₁`, and the member-family square sum is `D`, then the prime-power gap plus
square-divisibility `dχ^2 ∣ D` gives
`2 * χ(1).re * χ₁(1).re < ∑ χmem(j)(1).re^2`. -/
theorem realDegreeBound_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_primePow_gap hp hpos₁ hq hdiv hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11n1) real absolute degree bound from common-index p-power data.**

This variant of `realDegreeBound_of_natDegreeSumPrimePowerGap` uses the actual §6.6
common-index data instead of asking the caller to name a quotient `q` with
`dχ = q * d₁`.  The strict gap comes from
`two_mul_lt_sq_of_commonIndex_primePower_gap`; square-divisibility then pushes it to
the prefix degree sum. -/
theorem realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_commonIndex_primePower_gap
        hp hidxpos hd₁ hdχ hθ₁ hθχ hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11o) normalized degree gap from natural prime-power data.**

Combines `realDegreeBound_of_natDegreeSumPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`, so a §6.6 caller with natural degree data and ratio data
can produce the `XAdjoinStepInput.hDeg` field directly. -/
theorem normalizedDegreeGap_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hpos₁ hq hdiv hlt hdvd hDpos)

/-- **(T8.11r0) intrinsic degree-divisibility from common-index p-power data.**

`exists_pos_natDegreeRatio_of_dvd` consumes an intrinsic predicate over any natural witnesses for
`χ(1)` and `χ₁(1)`.  This lemma produces that predicate from the (6.6) degree-sort data: both
degrees have the same positive induced index `idx`, their residual factors are powers of the same
base `p`, and the sorted degrees satisfy `d₁ ≤ d`. -/
theorem natDegreeDvd_of_commonIndex_primePowerData
    {G : Type*} [Group G] {χ χ₁ : IrreducibleCharacter G}
    {p idx d d₁ θ θ₁ m n : ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hd : d = idx * θ) (hd₁ : d₁ = idx * θ₁)
    (hθ : θ = p ^ m) (hθ₁ : θ₁ = p ^ n) (hle : d₁ ≤ d) :
    ∀ e e₁ : ℕ, (χ : ClassFunction G ℂ) 1 = (e : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (e₁ : ℂ) → e₁ ∣ e := by
  intro e e₁ he he₁
  have hed : e = d := Nat.cast_injective (he.symm.trans hχone)
  have he₁d₁ : e₁ = d₁ := Nat.cast_injective (he₁.symm.trans hχ₁one)
  subst e
  subst e₁
  exact OddOrder.Peterfalvi.S07.mul_primePow_dvd_mul_primePow_of_le
    hp hidx hd₁ hd hθ₁ hθ hle

/-- **(T8.11o1) normalized degree gap from common-index p-power data.**

Combines `realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`.  This is the consumer form used by the
common-index step constructors after the quotient `q` has been removed from their input data. -/
theorem normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos)

/-- **(T8.11r) degree-divisibility inputs from common-index p-power sorted degrees.**

This packages both divisibility predicates required by
`xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`: the anchor degree divides every
prefix member degree and the new character degree.  The hypotheses are the honest (6.6) data
behind those predicates — common induced index, p-power residual degrees, and sorted natural
degrees — rather than abstract divisibility assumptions. -/
theorem degreeDivisibilityInputs_of_commonIndex_primePowerData
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ : ℕ}
    {dmem θmem mmem : ι → ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction G ℂ) 1 = (dmem j : ℂ))
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j ∈ s, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j ∈ s, θmem j = p ^ mmem j)
    (hleχ : d₁ ≤ dχ) (hlemem : ∀ j ∈ s, d₁ ≤ dmem j) :
    (∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) ∧
    (∀ d dAnchor : ℕ,
      (χ : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      (hmemone j hj) hχ₁one (hdmem j hj) hd₁ (hθmem j hj) hθ₁ (hlemem j hj)
  · exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      hχone hχ₁one hdχ hd₁ hθχ hθ₁ hleχ



end OddOrder.Peterfalvi.S08

