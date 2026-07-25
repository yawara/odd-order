/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart2

/-!
# Peterfalvi §8 — the Sibley–Dade hypothesis: opening layer

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/


namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(T8.11p) X-adjoin input from natural degree-gap data.**

This combines `xAdjoinStepInput_of_memberFamily_degreeRatios` with
`normalizedDegreeGap_of_natDegreeSumPrimePowerGap`.  A §6.6 caller that already has the finite
member-family data, degree-ratio equations, natural degree witnesses, and the prime-power /
square-divisibility gap can now produce the full `XAdjoinStepInput` without separately supplying
the normalized `hDeg` field. -/
noncomputable def xAdjoinStepInput_of_memberFamily_natDegreeGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {deg : ι → ℕ} {i₁ : ι} {a p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (ha1 : deg i₁ = 1)
    (hdeg_mem : ∀ j ∈ s,
      (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) :=
  hyp.xAdjoinStepInput_of_memberFamily_degreeRatios hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    (normalizedDegreeGap_of_natDegreeSumPrimePowerGap hdegχ hdeg_mem
      hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos)

open scoped Classical in
/-- **(T8.11q) X-adjoin input from divisibility and natural degree-gap data.**

This is the same per-step constructor as `xAdjoinStepInput_of_memberFamily_natDegreeGap`,
but it derives the member-family ratios and the new-character ratio from natural degree
divisibility data.  A §6.6 caller can now provide the character-theoretic divisibility
hypotheses together with the prime-power/square-divisibility gap data, without naming the
ratio function `deg` or scalar `a` separately. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let hratioFamily :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatioFamily_of_dvd
      (G := ↥L) (χ := χmem) (s := s) (i₁ := i₁) hdvd_mem
  let deg : ι → ℕ := Classical.choose hratioFamily
  have ha1 : deg i₁ = 1 := (Classical.choose_spec hratioFamily).1
  have hdeg_mem : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 :=
    (Classical.choose_spec hratioFamily).2.2
  let hratioχ :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatio_of_dvd
      (G := ↥L) (χs i) (χmem i₁) hdvdχ
  let a : ℕ := Classical.choose hratioχ
  have hdegχ_char : OddOrder.Peterfalvi.S03.characterDegree (χs i : ClassFunction ↥L ℂ) =
      (a : ℂ) *
        OddOrder.Peterfalvi.S03.characterDegree (χmem i₁ : ClassFunction ↥L ℂ) :=
    (Classical.choose_spec hratioχ).2
  have hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hdegχ_char
  exact hyp.xAdjoinStepInput_of_memberFamily_natDegreeGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos

open scoped Classical in
/-- **(T8.11r1) X-adjoin input from degree divisibility and common-index gap data.**

This is the quotient-free version of
`xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`: the normalized degree inequality is
derived from the common-index p-power factorizations of `d₁` and `dχ`, rather than from a named
quotient `q` with `dχ = q * d₁`. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_commonIndexNatGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let hratioFamily :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatioFamily_of_dvd
      (G := ↥L) (χ := χmem) (s := s) (i₁ := i₁) hdvd_mem
  let deg : ι → ℕ := Classical.choose hratioFamily
  have ha1 : deg i₁ = 1 := (Classical.choose_spec hratioFamily).1
  have hdeg_mem : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 :=
    (Classical.choose_spec hratioFamily).2.2
  let hratioχ :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatio_of_dvd
      (G := ↥L) (χs i) (χmem i₁) hdvdχ
  let a : ℕ := Classical.choose hratioχ
  have hdegχ_char : OddOrder.Peterfalvi.S03.characterDegree (χs i : ClassFunction ↥L ℂ) =
      (a : ℂ) *
        OddOrder.Peterfalvi.S03.characterDegree (χmem i₁ : ClassFunction ↥L ℂ) :=
    (Classical.choose_spec hratioχ).2
  have hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hdegχ_char
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeRatios hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    (normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap hdegχ hdeg_mem
      hχone hχ₁one hmemone hDsum hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos)

open scoped Classical in
/-- **(T8.11r) X-adjoin input from degree divisibility and prime-power sum data.**

This is the same constructor as `xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`, but it
no longer asks the caller to provide the square-divisibility `dχ² ∣ D` as an opaque hypothesis.  The
hypothesis is derived internally from the (6.6) mmd L78-80 arithmetic chain: sorted common-index
p-power tail degrees, total-side p-power square divisibility, the additive head/tail identity, and
coprimality of the fixed induction index with the p-power factor. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_primePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι κ : Type} {s : Finset ι} {tailSet : Finset κ}
    {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ q qtot c total θχ m mχ mq D : ℕ}
    {dmem : ι → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hθχ : θχ = p ^ mχ)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : D + (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_D : idx * idx ∣ D)
    (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hcop : Nat.Coprime idx θχ := coprime_commonIndex_primePower hidx_p hθχ
  have hdvd : dχ * dχ ∣ D :=
    OddOrder.Peterfalvi.S07.sq_dvd_head_of_commonIndex_primePower_sums
      tailSet (by omega) hidxpos hθχ hθtail htail_le hsum hqtot hθsq_le_qtot htotal
      hidx_D hdχ hcop
  have hpos₁ : 0 < d₁ := natDegree_pos_of_irreducibleCharacter_apply_one_eq hχ₁one
  have hDpos : 0 < D := natDegreeSquareSum_pos_of_memberFamily hi₁ hmemone hDsum
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho hdvd_mem hdvdχ
    hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos

open scoped Classical in
/-- **(T8.11t) X-adjoin input from common-index p-power degree data.**

This is the `primePowerSums` constructor with the two degree-divisibility predicate inputs
also derived internally from the (6.6) common-index p-power degree data.  The caller supplies the
anchor, new-character, and prefix-member factorizations through the same fixed index `idx`, sorted
natural-degree inequalities, and the tail square-sum divisibility data; no abstract `hdvd_mem`,
`hdvdχ`, or `dχ ^ 2 ∣ D` arithmetic black boxes remain at this interface. -/
noncomputable def xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι κ : Type} {s : Finset ι} {tailSet : Finset κ}
    {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ qtot c total θ₁ θχ m₁ mχ mq D : ℕ}
    {dmem θmem mmem : ι → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j ∈ s, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j ∈ s, θmem j = p ^ mmem j)
    (hlemem : ∀ j ∈ s, d₁ ≤ dmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : D + (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hdvds :=
    OddOrder.Peterfalvi.S08.degreeDivisibilityInputs_of_commonIndex_primePowerData
      (G := ↥L) (χ := χs i) (χ₁ := χmem i₁) (χmem := χmem) (s := s)
      (p := p) (idx := idx) (d₁ := d₁) (dχ := dχ)
      (θ₁ := θ₁) (θχ := θχ) (m₁ := m₁) (mχ := mχ)
      (dmem := dmem) (θmem := θmem) (mmem := mmem)
      (show 2 ≤ p by omega) hidxpos hχone hχ₁one hmemone hdχ hd₁ hdmem hθχ hθ₁
      hθmem (Nat.le_of_lt hlt) hlemem
  have hidx_D : idx * idx ∣ D :=
    OddOrder.Peterfalvi.S08.sq_dvd_natDegreeSquareSum_of_commonIndex hDsum hdmem
  have hcop : Nat.Coprime idx θχ := coprime_commonIndex_primePower hidx_p hθχ
  have hdvd : dχ * dχ ∣ D :=
    OddOrder.Peterfalvi.S07.sq_dvd_head_of_commonIndex_primePower_sums
      tailSet (by omega) hidxpos hθχ hθtail htail_le hsum hqtot hθsq_le_qtot htotal
      hidx_D hdχ hcop
  have hDpos : 0 < D := natDegreeSquareSum_pos_of_memberFamily hi₁ hmemone hDsum
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeDivisibility_commonIndexNatGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho hdvds.1 hdvds.2
    hχone hχ₁one hmemone hDsum hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos

open scoped Classical in
/-- **(T8.11u) X-adjoin input from a pairUnion enumeration and p-power degree data.**

This specializes `xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums` to the actual
running accumulator `pairUnion (xBaseBlock Z) pair i`.  A caller supplies an injective finite
enumeration of that accumulator; this adapter turns it into the member-family cover and all routine
X-member facts (non-real, conjugate support, conjugate membership, and orthonormality).  The
remaining inputs are the genuine (6.6) degree, p-power, sum, and coprimality data indexed by the
same enumeration. -/
noncomputable def xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {κ : Type} {tailSet : Finset κ}
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hχinj : Function.Injective χmem)
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    {i₁ : Fin k} {p idx d₁ dχ qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : Fin k → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j, θmem j = p ^ mmem j)
    (hlemem : ∀ j, d₁ ≤ dmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : (∑ j : Fin k, dmem j * dmem j) +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    change (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
    rw [← hrange]
    exact Set.mem_range_self j
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  have hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hS₀conj hbase))
    · have hjN : j < N := hji.trans hi
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ | hφ
        · right
          rw [hφ, hpair0 j hjN, hpair1 j hjN]
        · left
          rw [hφ, hpair1 j hjN, hpair0 j hjN]
          simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx
    have hxrange : x ∈ Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) := by
      rw [hrange]
      exact hx
    rcases hxrange with ⟨j, rfl⟩
    exact ⟨j, by simp, rfl⟩
  have hmemreal : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ) := by
    intro j _
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).1
  have hmemdiffsupp : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j _
    exact hyp.xMember_diffSupport_of_irreducible_X hX (hS₁X (hmemS1 j))
  have hmemS1' : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := fun j _ => hmemS1 j
  have hmembarS1 : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁ := fun j _ => hS₁conj (hmemS1 j)
  have hmemconjortho : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0 := by
    intro j _
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).2.2.2.2
  have hmemortho : ∀ j ∈ (Finset.univ : Finset (Fin k)), ∀ l ∈ (Finset.univ : Finset (Fin k)),
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        @ite ℂ (j = l) (Classical.propDecidable (j = l)) 1 0 := by
    intro j _ l _
    by_cases hjl : j = l
    · subst j
      simpa using irreducibleCharacter_inner_eq_ite (χmem l) (χmem l)
    · have hχne : χmem j ≠ χmem l := fun h => hjl (hχinj h)
      simpa [hjl, hχne] using irreducibleCharacter_inner_eq_ite (χmem j) (χmem l)
  let Dprefix : ℕ := ∑ j : Fin k, dmem j * dmem j
  have hDsum : ∑ j ∈ (Finset.univ : Finset (Fin k)), dmem j * dmem j = Dprefix := by
    simp [Dprefix]
  have hsum' : Dprefix +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total := by
    simpa [Dprefix] using hsum
  exact hyp.xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover (by simp) hmemreal hmemdiffsupp
    hmemS1' hmembarS1 hmemconjortho hmemortho
    hχone hχ₁one (fun j _ => hmemone j) hDsum
    hp hlt hdχ hd₁ (fun j _ => hdmem j) hθχ hθ₁
    (fun j _ => hθmem j) (fun j _ => hlemem j)
    hθtail htail_le hsum' hqtot hθsq_le_qtot htotal hidx_p

/-- **(T8.11v0) X-adjoin input from a pairUnion enumeration with a base-block anchor.**

This variant of `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums` removes two sorted-degree
inputs.  If the chosen anchor `χ₁` lies in the minimal-degree base block, then every member of the
running prefix has degree at least `χ₁(1)`.  The current pair is disjoint from the prefix, hence its
first character is not itself in the base block, so its degree is strictly larger. -/
noncomputable def xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {κ : Type} {tailSet : Finset κ}
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hχinj : Function.Injective χmem)
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    {i₁ : Fin k} {p idx d₁ dχ qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : Fin k → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hanchor : (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hp : 3 ≤ p)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j, θmem j = p ^ mmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : (∑ j : Fin k, dmem j * dmem j) +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    change (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
    rw [← hrange]
    exact Set.mem_range_self j
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  have hχnotbase : (χs i : ClassFunction ↥L ℂ) ∉ hyp.xBaseBlock Z := by
    intro hχbase
    have hχprefix : (χs i : ClassFunction ↥L ℂ) ∈ S₁ :=
      OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hχbase)
    exact (Set.disjoint_left.mp (hdisj i hi)) hχpair hχprefix
  have hlt : d₁ < dχ :=
    hyp.natDegree_lt_of_xBaseBlock_anchor_of_not_mem hanchor hχX hχnotbase hχ₁one hχone
  have hlemem : ∀ j : Fin k, d₁ ≤ dmem j := by
    intro j
    exact hyp.natDegree_le_of_xBaseBlock_anchor hanchor (hS₁X (hmemS1 j))
      hχ₁one (hmemone j)
  exact hyp.xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) hχinj hrange
    hχone hχ₁one hmemone hp hlt
    hdχ hd₁ hdmem hθχ hθ₁ hθmem hlemem
    hθtail htail_le hsum hqtot hθsq_le_qtot htotal hidx_p

/-- **(T8.11v) Common-index p-power data for one X-chain step.**

This is the remaining genuine (6.6) payload for one step after the routine `pairUnion` bookkeeping
has been discharged.  The fields are indexed by the same finite enumeration of the running
accumulator `pairUnion (xBaseBlock Z) pair i`, so downstream callers can supply the character-degree
and p-power data directly without rebuilding the member-family facts or the `XAdjoinStepInput`
record by hand. -/
structure PairUnionStepData
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L} where
  κ : Type
  tailSet : Finset κ
  k : ℕ
  χmem : Fin k → IrreducibleCharacter ↥L
  hχinj : Function.Injective χmem
  hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  i₁ : Fin k
  p : ℕ
  idx : ℕ
  d₁ : ℕ
  dχ : ℕ
  qtot : ℕ
  c : ℕ
  total : ℕ
  θ₁ : ℕ
  θχ : ℕ
  m₁ : ℕ
  mχ : ℕ
  mq : ℕ
  dmem : Fin k → ℕ
  θmem : Fin k → ℕ
  mmem : Fin k → ℕ
  θtail : κ → ℕ
  mtail : κ → ℕ
  hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ)
  hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ)
  hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ)
  hp : 3 ≤ p
  hlt : d₁ < dχ
  hdχ : dχ = idx * θχ
  hd₁ : d₁ = idx * θ₁
  hdmem : ∀ j, dmem j = idx * θmem j
  hθχ : θχ = p ^ mχ
  hθ₁ : θ₁ = p ^ m₁
  hθmem : ∀ j, θmem j = p ^ mmem j
  hlemem : ∀ j, d₁ ≤ dmem j
  hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j
  htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j
  hsum : (∑ j : Fin k, dmem j * dmem j) +
    (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total
  hqtot : qtot = p ^ mq
  hθsq_le_qtot : θχ * θχ ≤ qtot
  htotal : total = qtot * c
  hidx_p : Nat.Coprime idx p

/-- **(T8.11v1) Base-anchor common-index p-power data for one X-chain step.**

This is the chain-step payload matching
`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`: the caller supplies the
chosen anchor in `xBaseBlock Z`, and the adapter derives the sorted-degree facts
`d₁ < dχ` and `∀ j, d₁ ≤ dmem j` internally. -/
structure AnchoredPairUnionStepData
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L} where
  κ : Type
  tailSet : Finset κ
  k : ℕ
  χmem : Fin k → IrreducibleCharacter ↥L
  hχinj : Function.Injective χmem
  hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  i₁ : Fin k
  p : ℕ
  idx : ℕ
  d₁ : ℕ
  dχ : ℕ
  qtot : ℕ
  c : ℕ
  total : ℕ
  θ₁ : ℕ
  θχ : ℕ
  m₁ : ℕ
  mχ : ℕ
  mq : ℕ
  dmem : Fin k → ℕ
  θmem : Fin k → ℕ
  mmem : Fin k → ℕ
  θtail : κ → ℕ
  mtail : κ → ℕ
  hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ)
  hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ)
  hanchor : (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z
  hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ)
  hp : 3 ≤ p
  hdχ : dχ = idx * θχ
  hd₁ : d₁ = idx * θ₁
  hdmem : ∀ j, dmem j = idx * θmem j
  hθχ : θχ = p ^ mχ
  hθ₁ : θ₁ = p ^ m₁
  hθmem : ∀ j, θmem j = p ^ mmem j
  hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j
  htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j
  hsum : (∑ j : Fin k, dmem j * dmem j) +
    (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total
  hqtot : qtot = p ^ mq
  hθsq_le_qtot : θχ * θχ ≤ qtot
  htotal : total = qtot * c
  hidx_p : Nat.Coprime idx p


end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08
