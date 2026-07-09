/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart2

/-!
# Peterfalvi §08 Coherence Core — Part 3/3 (second `SibleyDadeHypothesis` block; chain head)

Prefix-split from 旧 `S08_CoherenceCore.lean` (11,969 行 → 3 ファイル, issue 0066)。
本ファイル = 元 L8089–11969 (2 番目の `SibleyDadeHypothesis` namespace)。
import chain head: Part1 ← Part2 ← **S08_CoherenceCore**。**名前を保持**ゆえ下流 import は無改変。
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
    {i₁ : ι} {p idx d₁ dχ q qtot c total θχ mχ mq : ℕ}
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
    {i₁ : ι} {p idx d₁ dχ qtot c total θ₁ θχ m₁ mχ mq : ℕ}
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
structure PairUnionCommonIndexPrimePowerStepData
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
structure PairUnionBaseAnchorCommonIndexPrimePowerStepData
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

open scoped Classical in
/-- **(T8.11w) X-chain coherence from per-step common-index p-power data.**

This is the chain-level consumer of `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums`.
The caller no longer has to construct an `XAdjoinStepInput` at each step: it supplies only a
`PairUnionCommonIndexPrimePowerStepData` package for the actual prefix accumulator chosen by the
conjugate-pair cover.  The adapter folds the chain using
`Xset_isCoherent_from_adjoinSteps_of_irreducible_X` and constructs each step input internally. -/
noncomputable def Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionCommonIndexPrimePowerStepData hyp (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hmemone
    data.hp data.hlt data.hdχ data.hd₁ data.hdmem
    data.hθχ data.hθ₁ data.hθmem data.hlemem data.hθtail data.htail_le data.hsum
    data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

open scoped Classical in
/-- **(T8.11w1) X-chain coherence from base-anchor common-index p-power data.**

This is the chain-level consumer of
`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`.  Compared with
`Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X`, each step package no
longer includes the sorted-degree fields `d₁ < dχ` and `∀ j, d₁ ≤ dmem j`; the base-block anchor
and pair-cover disjointness provide them internally. -/
noncomputable def Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hanchor data.hmemone data.hp
    data.hdχ data.hd₁ data.hdmem data.hθχ data.hθ₁ data.hθmem data.hθtail
    data.htail_le data.hsum data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

/-- **(T8.11w1c) base-anchor X-chain coherence, completeness-exposing variant.**  Like
`Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X` but the per-step
producer `hstepData` additionally receives the Xset-cover completeness witness `hcover` (finding #6)
— required to build the per-step `tailSet`/`htail_le`/`hsum`.  Routes through the `…withCover…`
engine.  Additive (no existing signature changes). -/
noncomputable def
    Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      (∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hanchor data.hmemone data.hp
    data.hdχ data.hd₁ data.hdmem data.hθχ data.hθ₁ data.hθmem data.hθtail
    data.htail_le data.hsum data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

/-- **(6.6)/(6.8.1), central-`Zc`, completeness-exposing form (redesign L2 outer shell, withCover).**
Same as `Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
but the `hstepData` producer receives the Xset-cover completeness witness `hcover` (finding #6), which
the monolith needs to build `tailSet`/`htail_le`/`hsum`.  Routes through the `…withCover…` consumer. -/
noncomputable def
    Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset hyp.centralCommutator) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L)
          (hyp.xBaseBlock hyp.centralCommutator) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      (∀ φ ∈ hyp.Xset hyp.centralCommutator, φ ∈ hyp.xBaseBlock hyp.centralCommutator ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := hyp.centralCommutator) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  exact hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X
    (Z := hyp.centralCommutator) hyp.centralCommutator_le
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hstepData

/-- **Base-anchor index existence** (the StepData `i₁`/`hanchor` data).  If `χmem` enumerates the
running prefix `pairUnion (xBaseBlock Z) pair i` and the minimal-degree base block `xBaseBlock Z`
is nonempty, then some index `i₁` has `χmem i₁ ∈ xBaseBlock Z` (the base block is contained in the
prefix `pairUnion`). -/
theorem exists_xBaseBlock_anchor_index (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i k : ℕ}
    {χmem : Fin k → IrreducibleCharacter ↥L}
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hne : (hyp.xBaseBlock Z).Nonempty) :
    ∃ i₁ : Fin k, (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z := by
  obtain ⟨φ, hφ⟩ := hne
  have hφpair : φ ∈ Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]
    exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  obtain ⟨i₁, hi₁⟩ := hφpair
  have hi₁' : (χmem i₁ : ClassFunction ↥L ℂ) = φ := hi₁
  exact ⟨i₁, by rw [hi₁']; exact hφ⟩

/-- **Tail-degree lower bound (finding #6 `htail_le` core).**  An `X`-member `φ` outside the running
prefix `pairUnion (xBaseBlock Z) pair i` has degree at least that of the current pair head
`(pair i).1`.  Proof: by `hcover`, `φ` is in the base block or some pair `j < N`; it is not in the
base (`⊆` prefix), so `φ ∈ pairSet pair j`; and `φ ∉ prefix` forces `j ≥ i` (pairs `< i` lie in the
prefix), so by degree-monotonicity (`hmono`) `(pair i).1(1) ≤ (pair j).1(1) = φ(1)`.  This is the
step where Xset-cover completeness (`hcover`) is genuinely used. -/
theorem characterDegree_re_le_of_not_mem_pairUnion (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hmono : ∀ j, j + 1 < N →
      (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re)
    (hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    {i : ℕ} (hi : i < N)
    {φ : ClassFunction ↥L ℂ} (hφX : φ ∈ hyp.Xset Z)
    (hφnot : φ ∉ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) :
    (OddOrder.Peterfalvi.S03.characterDegree (pair i).1).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree φ).re := by
  -- degree-monotone chaining: `a ≤ b < N ⟹ deg (pair a).1 ≤ deg (pair b).1`
  have hchain : ∀ d a : ℕ, a + d < N →
      (OddOrder.Peterfalvi.S03.characterDegree (pair a).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair (a + d)).1).re := by
    intro d
    induction d with
    | zero => intro a _; simp
    | succ d ih =>
      intro a haN
      have h1 := ih a (by omega)
      have h2 := hmono (a + d) (by omega)
      have : a + (d + 1) = (a + d) + 1 := by omega
      rw [this]
      exact le_trans h1 h2
  -- `φ` is in some pair `j`, and `j ≥ i`
  rcases hcover φ hφX with hbase | ⟨j, hjN, hjpair⟩
  · exact absurd (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hbase)) hφnot
  · have hij : i ≤ j := by
      by_contra hlt
      push Not at hlt  -- j < i
      exact hφnot (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hlt, hjpair⟩))
    have hdeg_ij : (OddOrder.Peterfalvi.S03.characterDegree (pair i).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re := by
      have := hchain (j - i) i (by omega)
      rwa [Nat.add_sub_cancel' hij] at this
    -- `φ` equals `(pair j).1` or `(pair j).2`, both of degree `(pair j).1(1)`
    have hφdeg : (OddOrder.Peterfalvi.S03.characterDegree φ).re =
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re := by
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hjpair
      rcases hjpair with h | h
      · rw [h]
      · rw [h, hpair1 j hjN, hpair0 j hjN]; simp
    rw [hφdeg]; exact hdeg_ij

/-- **Degree-square partition (finding #6 `hsum` core).**  For a finite character set `Xfin` whose
real degree-square sum is a natural number `totalN`, and an injective member subfamily `memb`
contained in `Xfin`, the natural degree-square sum splits as members `+` tail (`Xfin ∖ members`)
`= totalN`.  Pure `Finset.sum_image` + `Finset.sum_sdiff` + an ℝ→ℕ cast; no character theory.  The
producer supplies `deg φ = |L:H|·p^(eφ)` and `totalN = |L:H|·(|H|−|H:Z|)` (via `sum_re_sq_Xset_eq`). -/
theorem natSum_partition_of_realSum {α : Type*} [DecidableEq α]
    (Xfin : Finset α) (deg : α → ℕ) (totalN : ℕ)
    (hXsum : (∑ φ ∈ Xfin, ((deg φ : ℝ)) ^ 2) = (totalN : ℝ))
    {k : ℕ} {memb : Fin k → α} (hinj : Function.Injective memb)
    (hsub : ∀ j, memb j ∈ Xfin) :
    (∑ j : Fin k, deg (memb j) * deg (memb j))
      + (∑ φ ∈ Xfin \ Finset.univ.image memb, deg φ * deg φ) = totalN := by
  classical
  have hmembers : Finset.univ.image memb ⊆ Xfin := by
    intro φ hφ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hφ
    exact hsub j
  have hreindex : ∑ φ ∈ Finset.univ.image memb, deg φ * deg φ
      = ∑ j : Fin k, deg (memb j) * deg (memb j) :=
    Finset.sum_image (fun a _ b _ h => hinj h)
  have hXsumN : ∑ φ ∈ Xfin, deg φ * deg φ = totalN := by
    have h : ((∑ φ ∈ Xfin, deg φ * deg φ : ℕ) : ℝ) = (totalN : ℝ) := by
      rw [← hXsum, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun φ _ => by push_cast; ring)
    exact_mod_cast h
  rw [← hreindex, add_comm, Finset.sum_sdiff hmembers]
  exact hXsumN

open scoped Classical in
/-- **`X = S − S(Z)` membership bridge: the induced-character `Finset` form equals the `Set` form.**
For any `Z`, a class function `φ` lies in the explicit `Finset`
`(filter bot-kernel).image (Ind ·) \ (filter Z-kernel).image (Ind ·)` (the degree-square-sum domain
of `sum_re_sq_Xset_eq_of_irreducible_X` / `Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X`) iff
`φ ∈ Xset Z = S − S(Z)`.  Extracted from the L2 monolith's inline `hmemXF` so that a `Set`-form
irreducibility hypothesis (the `c2`/case-A `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) can feed the
`Finset`-form nonemptiness lemma. -/
theorem mem_xSetFinset_iff_mem_Xset (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (φ : ClassFunction ↥L ℂ) :
    φ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)) ↔
      φ ∈ hyp.Xset Z := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hbot, hnotZ⟩
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hbot
    obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
    refine hyp.mem_Xset.mpr ⟨by rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩, ?_⟩
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  · intro hφ
    obtain ⟨hφS, hφnotZ⟩ := hyp.mem_Xset.mp hφ
    rw [hyp.S_eq, Set.mem_setOf_eq] at hφS
    obtain ⟨θ, hθne, rfl⟩ := hφS
    refine ⟨Finset.mem_image.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hθne⟩, rfl⟩, ?_⟩
    · intro x hx
      rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
      subst hx; exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
    · intro hmem
      obtain ⟨θ', hθ', hθ'eq⟩ := Finset.mem_image.mp hmem
      obtain ⟨-, hker', hne'⟩ := Finset.mem_filter.mp hθ'
      exact hφnotZ (hyp.mem_SsubFiltration.mpr ⟨θ', hne', hker', hθ'eq.symm⟩)

open scoped Classical in
/-- **(6.6)/(6.8) X = S − S(Zc) coherence — the L2 producer, generalized over the irreducibility
input.**  `X(Zc)` is coherent (`Zc = Z(H) ∩ H′` central) given **only** that every `X`-member is
irreducible (`hX`), that `X` is nonempty (`hXne`), and that `|L:H|` is coprime to `p` (`hidxp`).
Builds the per-step `PairUnionBaseAnchorCommonIndexPrimePowerStepData` for every chain step and feeds
it to the `…withCover…` generic shell.  The Frobenius case (`…_of_frobenius`) and the
certain-type/case-A case (`…_of_c2_caseA`) are thin specializations differing only in how
`hX`/`hXne`/`hidxp` are produced (`isIrreducibleCharacter_of_mem_Xset_of_frobenius` +
`hF.coprime_card_kernel_complement` vs `isIrreducibleCharacter_of_mem_Xset_c2_caseA` +
`cert.card_coprime`). -/
noncomputable def Xset_centralCommutator_isCoherent_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    (hX : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ)
    (hXne : (hyp.Xset hyp.centralCommutator).Nonempty)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (hidxp : Nat.Coprime H.index p) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  haveI : Fact p.Prime := ⟨hp⟩
  -- the common-index degree exponent over `X(Zc)`
  have hdegX : ∀ φ ∈ hyp.Xset hyp.centralCommutator,
      ∃ kφ : ℕ, (φ : ClassFunction ↥L ℂ) 1 = ((H.index * p ^ kφ : ℕ) : ℂ) :=
    fun φ hφ => hyp.exists_index_primePow_degree_of_mem_S hp hHp (hyp.Xset_subset_S hφ)
  choose! e he using hdegX
  -- `qtot = |H:Zc| = p^mq`
  haveI : (hyp.centralCommutator.subgroupOf H).Normal :=
    hyp.centralCommutator_normal.subgroupOf H
  choose mq hmq using
    exists_primePow_card_quotient_of_isPGroup hp hHp (hyp.centralCommutator.subgroupOf H)
  have hZle : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  refine hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X
    (Z := hyp.centralCommutator) hyp.centralCommutator_le hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi
  -- `χs i ∈ X(Zc)`
  have hχiX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
    refine hpairs i hi ?_
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  -- central degree bound for the head
  choose mχ hχdeg hχsq using hyp.exists_source_primePow_centralBound_of_mem_Xset hp hHp
    hyp.centralCommutator_subgroupOf_le_center hχiX
  -- member-family enumeration
  choose k χmem hconj using
    hyp.exists_pairUnion_memberFamily_of_irreducible_X hyp.centralCommutator_le
      hX hpair0 hpair1 hpairs hi
  obtain ⟨hχinj, hrange, -, -, -, -, -, -⟩ := hconj
  -- members lie in `X(Zc)`
  have hmemX : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
    intro j
    have : (χmem j : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock hyp.centralCommutator) pair i := by
      rw [← hrange]; exact Set.mem_range_self j
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp this with hbase | ⟨j', hj', hj'pair⟩
    · exact hyp.xBaseBlock_subset _ hbase
    · exact hpairs j' (hj'.trans hi) hj'pair
  -- base-block anchor
  have hbbne : (hyp.xBaseBlock hyp.centralCommutator).Nonempty := by
    rw [← Set.ncard_pos (hyp.xSet_finite_of_irreducible_X hX |>.subset
        (hyp.xBaseBlock_subset _))]
    exact lt_of_lt_of_le (by norm_num) (hyp.two_le_xBaseBlock_ncard_of_irreducible_X
      hyp.centralCommutator_le hX hXne)
  choose i₁ hanchor using hyp.exists_xBaseBlock_anchor_index hrange hbbne
  -- the `X(Zc)` index Finset (the `sum_re_sq_Xset_eq` domain) and its coe
  set XF := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(hyp.centralCommutator.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXFdef
  have hmemXF : ∀ φ, φ ∈ XF ↔ φ ∈ hyp.Xset hyp.centralCommutator := by
    intro φ; rw [hXFdef]; exact hyp.mem_xSetFinset_iff_mem_Xset (Z := hyp.centralCommutator) φ
  -- real degree-square sum over `XF`
  have hrealSum : (∑ φ ∈ XF, ((H.index * p ^ e φ : ℕ) : ℝ) ^ 2)
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ)
          - (Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) : ℝ)) := by
    rw [← hyp.sum_re_sq_Xset_eq_of_irreducible_X (Z := hyp.centralCommutator)
      (fun χ hχ => hX χ ((hmemXF χ).mp hχ))]
    refine Finset.sum_congr rfl (fun φ hφ => ?_)
    have hφX := (hmemXF φ).mp hφ
    rw [he φ hφX, Complex.natCast_re]
  -- enumerate the tail `XF ∖ members` by `Fin tailF.card` (Type 0, to fit `StepData.κ : Type`)
  set tailF := XF \ Finset.univ.image (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ))
    with htailFdef
  let tElt : Fin tailF.card → ClassFunction ↥L ℂ :=
    fun i => ((tailF.equivFin.symm i : { x // x ∈ tailF }) : ClassFunction ↥L ℂ)
  have htElt_mem : ∀ i, tElt i ∈ tailF := fun i => (tailF.equivFin.symm i).2
  have hreindex : ∀ F : ClassFunction ↥L ℂ → ℕ,
      (∑ i : Fin tailF.card, F (tElt i)) = ∑ x ∈ tailF, F x := by
    intro F
    rw [← Finset.sum_coe_sort tailF F]
    exact Equiv.sum_comp tailF.equivFin.symm (fun y => F (y : ClassFunction ↥L ℂ))
  have hinj : Function.Injective (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hsub : ∀ j : Fin k, (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) j ∈ XF :=
    fun j => (hmemXF _).mpr (hmemX j)
  -- assemble the step data
  exact
    { κ := Fin tailF.card
      tailSet := Finset.univ
      k := k
      χmem := χmem
      hχinj := hχinj
      hrange := hrange
      i₁ := i₁
      p := p
      idx := H.index
      d₁ := H.index * p ^ e (χmem i₁ : ClassFunction ↥L ℂ)
      dχ := H.index * p ^ mχ
      qtot := Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
      c := H.index * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
      total := H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
      θ₁ := p ^ e (χmem i₁ : ClassFunction ↥L ℂ)
      θχ := p ^ mχ
      m₁ := e (χmem i₁ : ClassFunction ↥L ℂ)
      mχ := mχ
      mq := mq
      dmem := fun j => H.index * p ^ e (χmem j : ClassFunction ↥L ℂ)
      θmem := fun j => p ^ e (χmem j : ClassFunction ↥L ℂ)
      mmem := fun j => e (χmem j : ClassFunction ↥L ℂ)
      θtail := fun i => p ^ e (tElt i)
      mtail := fun i => e (tElt i)
      hχone := hχdeg
      hχ₁one := he _ (hyp.xBaseBlock_subset _ hanchor)
      hanchor := hanchor
      hmemone := fun j => he _ (hmemX j)
      hp := hp3
      hdχ := rfl
      hd₁ := rfl
      hdmem := fun _ => rfl
      hθχ := rfl
      hθ₁ := rfl
      hθmem := fun _ => rfl
      hθtail := fun _ _ => rfl
      htail_le := by
        intro t _
        have hφtailF : tElt t ∈ tailF := htElt_mem t
        rw [htailFdef, Finset.mem_sdiff] at hφtailF
        obtain ⟨hφXF, hφnotmem⟩ := hφtailF
        have hφX := (hmemXF (tElt t)).mp hφXF
        have hφnotpair : tElt t ∉ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L)
            (hyp.xBaseBlock hyp.centralCommutator) pair i := by
          intro hmem
          rw [← hrange] at hmem
          obtain ⟨j, hj⟩ := hmem
          exact hφnotmem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
        have hdeg := hyp.characterDegree_re_le_of_not_mem_pairUnion hpair0 hpair1 hmono hcover hi
          hφX hφnotpair
        rw [hpair0 i hi] at hdeg
        have h1 : (OddOrder.Peterfalvi.S03.characterDegree (χs i : ClassFunction ↥L ℂ)).re
            = ((H.index * p ^ mχ : ℕ) : ℝ) := by
          rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχdeg, Complex.natCast_re]
        have h2 : (OddOrder.Peterfalvi.S03.characterDegree (tElt t)).re
            = ((H.index * p ^ e (tElt t) : ℕ) : ℝ) := by
          rw [OddOrder.Peterfalvi.S03.characterDegree_def, he _ hφX, Complex.natCast_re]
        rw [h1, h2] at hdeg
        exact_mod_cast hdeg
      hsum := by
        show (∑ j : Fin k, (H.index * p ^ e (χmem j : ClassFunction ↥L ℂ))
              * (H.index * p ^ e (χmem j : ClassFunction ↥L ℂ)))
            + (∑ i : Fin tailF.card, (H.index * p ^ e (tElt i)) * (H.index * p ^ e (tElt i)))
            = H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
        rw [show (∑ i : Fin tailF.card, (H.index * p ^ e (tElt i)) * (H.index * p ^ e (tElt i)))
              = ∑ x ∈ tailF, (H.index * p ^ e x) * (H.index * p ^ e x) from
            hreindex (fun x => (H.index * p ^ e x) * (H.index * p ^ e x))]
        exact natSum_partition_of_realSum XF (fun φ => H.index * p ^ e φ)
          (H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)))
          (by rw [hrealSum]; push_cast [Nat.cast_sub hZle]; ring) hinj hsub
      hqtot := hmq
      hθsq_le_qtot := by rw [← pow_two]; exact hχsq
      htotal := hyp.index_mul_card_sub_factor (Z := hyp.centralCommutator)
      hidx_p := hidxp }

open scoped Classical in
/-- **(6.6)/(6.8) X = S − S(Zc) coherence at the central commutator — the L2 producer.**
The redesign's L2 deliverable: `X(Zc)` is coherent, with `Zc = Z(H) ∩ H′` central.  Builds the
per-step `PairUnionBaseAnchorCommonIndexPrimePowerStepData` (the first-ever such term) for every
chain step and feeds it to the `…withCover…` Zc shell.  Per step: the current head `χs i` and every
`X`-member `Ind θ` have degree `|L:H|·p^k` (`exists_index_primePow_degree_of_mem_S`), the central
degree bound `θχ² ≤ |H:Zc|` holds ([Is] Cor 2.30 via `exists_source_primePow_centralBound_of_mem_Xset`),
the `htail_le` field is `characterDegree_re_le_of_not_mem_pairUnion` (uses `hcover`), and the `hsum`
partition is `natSum_partition_of_realSum` pinned by `sum_re_sq_Xset_eq`.  `H` is supplied as a
`p`-group (the capstone's ¬-coherent branch gives this via `isPGroup_of_not_coherent`). -/
noncomputable def Xset_centralCommutator_isCoherent_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  haveI : Fact p.Prime := ⟨hp⟩
  -- `|L:H|` coprime to `p`
  have hpdvd : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
    rw [hn]; exact dvd_pow_self p hn0
  have hidxp : Nat.Coprime H.index p := by
    rw [hyp.index_H_eq_card_W1]
    exact (Nat.Coprime.coprime_dvd_left hpdvd hF.coprime_card_kernel_complement).symm
  exact hyp.Xset_centralCommutator_isCoherent_of_irreducible_X
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hp hp3 hHp hidxp

open scoped Classical in
/-- **(6.6)/(6.8) X(Zc) coherence, certain-type case (B), math-(A) sub-case `Z(H) ∩ W₂ = ⊥` (CB3).**
The CertainType/(c2) analogue of `Xset_centralCommutator_isCoherent_of_frobenius` under the math-(A)
hypothesis `Z(H) ⊓ W₂ = 1` (`hA`): `W₁` still acts fixed-point-freely on `Zc = Z(H) ∩ H′`
(`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`), so the same central-`Zc` coherence machinery
of `Xset_centralCommutator_isCoherent_of_irreducible_X` applies.  The three irreducibility/coprimality
inputs are produced from the certain-type data: `hX` from `isIrreducibleCharacter_of_mem_Xset_c2_caseA`,
`hXne` from `Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X` (the `Set`→`Finset` form converted by
`mem_xSetFinset_iff_mem_Xset`), and `hidxp` from `cert.card_coprime` + `index_H_eq_card_W1`. -/
noncomputable def Xset_centralCommutator_isCoherent_of_c2_caseA
    (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  haveI : Fact p.Prime := ⟨hp⟩
  -- every `X`-member is irreducible (`W₁` FPF on `Zc` from math-(A))
  have hX : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ
  -- `Zc.subgroupOf H ≠ ⊥` (since `H` is non-abelian)
  have hZbot : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    intro hbot
    apply hyp.centralCommutator_ne_bot hHnonab
    rw [eq_bot_iff]
    intro z hz
    have hzH : z ∈ H := hyp.centralCommutator_le hz
    have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
      (Subgroup.mem_subgroupOf).mpr hz
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  -- `X` is nonempty
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty :=
    hyp.Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X hZbot
      (fun χ hχ => hX χ ((hyp.mem_xSetFinset_iff_mem_Xset (Z := hyp.centralCommutator) χ).mp hχ))
  -- `|L:H| = |W₁|` coprime to `p`
  have hpdvd : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
    rw [hn]; exact dvd_pow_self p hn0
  have hidxp : Nat.Coprime H.index p := by
    rw [hyp.index_H_eq_card_W1, ← hW1]
    have hcop := cert.card_coprime
    rw [hK] at hcop
    exact (Nat.Coprime.coprime_dvd_left hpdvd hcop).symm
  exact hyp.Xset_centralCommutator_isCoherent_of_irreducible_X hX hXne hp hp3 hHp hidxp

/-- **(6.8.1)/(6.8), L3 outer shell:** `X(Zc) ∪ Y` is coherent, given the (6.8.1) `τ₃` glue data
`ν`.  Mirrors `coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner` but at
the central `Zc` and **stopping at the union coherence** (`Xset Zc ∪ Yset ⊊ S` in general, so the
final `Xset_union_Yset_eq_S` collapse is unavailable; the gap is closed separately by L4
`false_of_coherentXunionYset_of_not_coherentS`).  The `X`-coherence is the L2 monolith
`Xset_centralCommutator_isCoherent_of_frobenius`; the `Y`-coherence is `coherentYset`;
source-orthogonality is `Xset Zc ⊥ Yset` (`Yset ⊆ S(Zc)` by antitonicity, disjoint from `Xset Zc`).
The remaining input is the genuine **(6.8.1) `ν`/`hmixed` data** — the `τ₃` construction (uses (6.7)
`peterfalvi_67_of_odd`), still to be built; once supplied, `⟨…⟩` feeds L4. -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset hyp.centralCommutator,
      ν x = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj)
    hmixed hgen

/-- **(6.8.1)/(6.8), L3 outer shell — diagonal-aware form.**  Same as
`coherentXunionYset_centralCommutator_of_glued_of_frobenius`, but routing through the corrected
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`: the plain shell's generation
hypothesis `hgen` (without the cross-diagonals `D`) is **false** in the (6.8.1) situation — the
supported cross-diagonal `χ₁ − a·η₁ ∈ ℤ[X(Zc) ∪ Y]` is not a sum of a supported `X`-combination and
a supported `Y`-combination (see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`, framing correction
#2, and the `coherentUnion_of_glued_withDiagonal` docstring).  Here `D` carries those cross-diagonals
with `hDτ : ∀ d ∈ D, ν d = τ d` (the (6.8.1) `b ≡ 0` conclusion
`(χ₁ − a·η₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`), and `hgen` is the satisfiable generation including `D`. -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_withDiagonal_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset hyp.centralCommutator, ν x = cX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = cY.extension y)
    (hmixed : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ))
    (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    cX cY ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj)
    hmixed D hDτ hgen

/-- **(6.8) L3 outer shell — diagonal-aware form, case (c2) case (A).**  The certain-type case-(A)
analogue of `coherentXunionYset_centralCommutator_of_glued_withDiagonal_general`: glues the
case-(A) `X(⁅H,H⁆)`-coherence `cX` (from `Xset_centralCommutator_isCoherent_of_c2_caseA`) and the
`Y`-coherence `cY` into `X(⁅H,H⁆) ∪ Y`-coherence.  Identical to the Frobenius version except the
(5.2.e) `X ⊥ Y` orthogonality uses the case-(A) irreducibility
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (`W₁` FPF on `Z(H) ∩ ⁅H,H⁆` from math-(A), via the
case-(A) datum `hA : Z(H) ⊓ W₂ = ⊥`) in place of the Frobenius
`isIrreducibleCharacter_of_mem_Xset_of_frobenius`. -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset hyp.centralCommutator, ν x = cX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = cY.extension y)
    (hmixed : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ))
    (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    cX cY ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj)
    hmixed D hDτ hgen

/-- **`X(Zc)` nonemptiness, case (A) / c2 form.**  As `Xset_centralCommutator_nonempty`, but the
strictly-positive degree-square sum is supplied via
`Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X` (which needs only `X`-irreducibility), with the
`X = S − S(Zc) ⊆ Irr L` fact coming from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of the Frobenius
hypothesis.  The `Zc.subgroupOf H ≠ ⊥` step is the same non-abelian-`H` argument. -/
theorem Xset_centralCommutator_nonempty_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    (hyp.Xset hyp.centralCommutator).Nonempty := by
  haveI := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  have hX : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ
  have hZbot : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    intro hbot
    apply hyp.centralCommutator_ne_bot hHnonab
    rw [eq_bot_iff]
    intro z hz
    have hzH : z ∈ H := hyp.centralCommutator_le hz
    have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
      (Subgroup.mem_subgroupOf).mpr hz
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  exact hyp.Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X hZbot
    (fun χ hχ => hX χ ((hyp.mem_xSetFinset_iff_mem_Xset (Z := hyp.centralCommutator) χ).mp hχ))

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, case (A) / c2 form.  As `two_le_xBaseBlock_ncard`, but
`X`-irreducibility comes from the certain-type input `isIrreducibleCharacter_of_mem_Xset_c2_caseA`
(cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem two_le_xBaseBlock_ncard_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hXne : (hyp.Xset hyp.centralCommutator).Nonempty) :
    2 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard := by
  haveI := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  exact hyp.two_le_xBaseBlock_ncard_of_irreducible_X hyp.centralCommutator_le
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hXne

/-- L3 outer shell at the fixed witnesses (specialization of
`coherentXunionYset_centralCommutator_of_glued_withDiagonal_general`). -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset hyp.centralCommutator,
      ν x = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ))
    (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset ν hagreeX hagreeY hmixed D hDτ hgen

/-- **Peterfalvi (6.8.1) image orthogonality `himg_ortho` via (4.1)** (Frobenius case, mmd 04.8 L166).
`X(Zc)^{τ₂} ⊥ Y^{τ₁}`: for `χ ∈ X(Zc)`, `η ∈ Y`, the coherent images are orthogonal,
`⟨χ^{τ₂}, η^{τ₁}⟩ = 0`.  This is the "by (4.1)" step, **independent** of the deep `b ≡ 0` argument.

Pick distinct references `χ' ≠ χ` in `X(Zc)` (`2 ≤ |X(Zc)|`, from `two_le_xBaseBlock_ncard` +
`xBaseBlock_subset`) and `η' ≠ η` in `Y` (`2 ≤ |Y|`, `two_le_Yset_ncard`), and apply
`pairwise_inner_eq_zero_of_orthogonal_signedDifference` with `α = η^{τ₁}, β = η'^{τ₁}, γ = χ^{τ₂},
δ = χ'^{τ₂}` and **degree coefficients** `u = χ'(1), v = χ(1)`.  Then `u•γ − v•δ =
(χ'(1)•χ − χ(1)•χ')^{τ₂}` is the τ₂-image of a *supported* (degree-`0`,
`sMember_smulDiffSupport_of_charValue_eq` — no divisibility needed) integer `X`-combination, and
`α − β = (η − η')^{τ₁}` the τ₁-image of a supported (equal-degree, `Yset_apply_one`) `Y`-difference;
the difference-orthogonality `inner_extension_eq_inner_of_supported` (`= 0` by `X ⊥ Y`) and degree-`0`
`extension_apply_one_eq_zero_of_supported` discharge `hdiff`/`hα1`/`hγδ1`.  The conclusion `⟨α,γ⟩ = 0`
gives the claim by conjugate symmetry. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (cX.extension χ) (cY.extension η) = 0 := by
  classical
  haveI : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set hXc := cX with hXc_def
  set hYc := cY with hYc_def
  -- irreducibility of members
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  -- `if`-formula for inner products of irreducibles (orthonormality)
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  -- distinct references (n, m ≥ 2)
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty := ⟨χ, hχ⟩
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.xSet_finite_of_irreducible_X hXirr
  have hX2 : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
    le_trans (hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le hXne)
      (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
  obtain ⟨χ', hχ'X, hχ'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (hyp.Xset hyp.centralCommutator).ncard) χ
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  -- positive natural degrees of `χ`, `χ'`
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'X⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  -- membership in the integral spans (`subset_span`)
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ
  have hχ's : χ' ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ'X
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  -- the two supported difference inputs of (4.1)
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ' with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ'X) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  -- the image of `xdiff` is exactly the degree-weighted `u•γ − v•δ`
  have hXeq : ((d' : ℝ) : ℂ) • hXc.extension χ - ((d : ℝ) : ℂ) • hXc.extension χ'
      = hXc.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (hXc.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (hXc.extension χ')]
    push_cast
    ring
  have hYeq : hYc.extension η - hYc.extension η' = hYc.extension ydiff := by
    rw [hydiff_def, map_sub]
  -- disjointness `X(Zc) ⊥ Y` and the source orthogonality `⟨xdiff, ydiff⟩ = 0`
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj xdiff hx_supp.1 ydiff hy_supp.1
  -- discharge the (4.1) hypotheses and read off `⟨α,γ⟩ = 0`
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := hYc.extension η) (β := hYc.extension η')
    (γ := hXc.extension χ) (δ := hXc.extension χ')
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (hYc.extension_mem_ZIrr η hηs)
    (by rw [hYc.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη), if_pos rfl])
    (hYc.extension_mem_ZIrr η' hη's)
    (by rw [hYc.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        if_pos rfl])
    (hXc.extension_mem_ZIrr χ hχs)
    (by rw [hXc.extension_inner_eq χ χ hχs hχs, hinner χ χ (hXirr χ hχ) (hXirr χ hχ), if_pos rfl])
    (hXc.extension_mem_ZIrr χ' hχ's)
    (by rw [hXc.extension_inner_eq χ' χ' hχ's hχ's, hinner χ' χ' (hXirr χ' hχ'X) (hXirr χ' hχ'X),
        if_pos rfl])
    (by rw [hYc.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        if_neg (fun h => hη'ne h.symm)])
    (by rw [hXc.extension_inner_eq χ χ' hχs hχ's, hinner χ χ' (hXirr χ hχ) (hXirr χ' hχ'X),
        if_neg (fun h => hχ'ne h.symm)])
    (by -- hdiff
      rw [hXeq, hYeq, inner_conj_symm (hXc.extension xdiff) (hYc.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hyp.hconj hXc hYc hx_supp hy_supp,
        hsrc0, star_zero])
    (by -- hα1
      rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj hYc hy_supp)
    (by -- hγδ1
      rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj hXc hx_supp)
  rw [inner_conj_symm (hYc.extension η) (hXc.extension χ), hconcl.1, star_zero]

/-- **Case-(A)/c2 mirror of `inner_extension_Xset_centralCommutator_Yset_eq_zero_general`.**  Same
proof as the Frobenius original, with the Frobenius hypothesis `hF` replaced by the certain-type
case-(A) data bundle `cert`/`hK`/`hW1`/`hA`, and the Frobenius `X`-irreducibility /
`two_le_xBaseBlock_ncard` adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (cX.extension χ) (cY.extension η) = 0 := by
  classical
  haveI : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set hXc := cX with hXc_def
  set hYc := cY with hYc_def
  -- irreducibility of members
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  -- `if`-formula for inner products of irreducibles (orthonormality)
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  -- distinct references (n, m ≥ 2)
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty := ⟨χ, hχ⟩
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.xSet_finite_of_irreducible_X hXirr
  have hX2 : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
    le_trans (hyp.two_le_xBaseBlock_ncard_c2_caseA hK hW1 hA hXne)
      (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
  obtain ⟨χ', hχ'X, hχ'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (hyp.Xset hyp.centralCommutator).ncard) χ
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  -- positive natural degrees of `χ`, `χ'`
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'X⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  -- membership in the integral spans (`subset_span`)
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ
  have hχ's : χ' ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ'X
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  -- the two supported difference inputs of (4.1)
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ' with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ'X) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  -- the image of `xdiff` is exactly the degree-weighted `u•γ − v•δ`
  have hXeq : ((d' : ℝ) : ℂ) • hXc.extension χ - ((d : ℝ) : ℂ) • hXc.extension χ'
      = hXc.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (hXc.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (hXc.extension χ')]
    push_cast
    ring
  have hYeq : hYc.extension η - hYc.extension η' = hYc.extension ydiff := by
    rw [hydiff_def, map_sub]
  -- disjointness `X(Zc) ⊥ Y` and the source orthogonality `⟨xdiff, ydiff⟩ = 0`
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj xdiff hx_supp.1 ydiff hy_supp.1
  -- discharge the (4.1) hypotheses and read off `⟨α,γ⟩ = 0`
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := hYc.extension η) (β := hYc.extension η')
    (γ := hXc.extension χ) (δ := hXc.extension χ')
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (hYc.extension_mem_ZIrr η hηs)
    (by rw [hYc.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη), if_pos rfl])
    (hYc.extension_mem_ZIrr η' hη's)
    (by rw [hYc.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        if_pos rfl])
    (hXc.extension_mem_ZIrr χ hχs)
    (by rw [hXc.extension_inner_eq χ χ hχs hχs, hinner χ χ (hXirr χ hχ) (hXirr χ hχ), if_pos rfl])
    (hXc.extension_mem_ZIrr χ' hχ's)
    (by rw [hXc.extension_inner_eq χ' χ' hχ's hχ's, hinner χ' χ' (hXirr χ' hχ'X) (hXirr χ' hχ'X),
        if_pos rfl])
    (by rw [hYc.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        if_neg (fun h => hη'ne h.symm)])
    (by rw [hXc.extension_inner_eq χ χ' hχs hχ's, hinner χ χ' (hXirr χ hχ) (hXirr χ' hχ'X),
        if_neg (fun h => hχ'ne h.symm)])
    (by -- hdiff
      rw [hXeq, hYeq, inner_conj_symm (hXc.extension xdiff) (hYc.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hyp.hconj hXc hYc hx_supp hy_supp,
        hsrc0, star_zero])
    (by -- hα1
      rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj hYc hy_supp)
    (by -- hγδ1
      rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj hXc hx_supp)
  rw [inner_conj_symm (hYc.extension η) (hXc.extension χ), hconcl.1, star_zero]

/-- **Peterfalvi (6.8.1) `himg_ortho`** at the fixed Frobenius-case witnesses `τ₂ =
`Xset_centralCommutator_isCoherent`, `τ₁ = coherentYset` (specialization of
`inner_extension_Xset_centralCommutator_Yset_eq_zero_general`). -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ)
      (hyp.coherentYset.extension η) = 0 :=
  hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hχ hη

/-- **Case-(A)/c2 mirror of `inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ)
      (hyp.coherentYset.extension η) = 0 :=
  hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hχ hη

/-- **Span form of `himg_ortho`:** `⟨x^{τ₂}, η^{τ₁}⟩ = 0` for any `x ∈ ℤ[X(Zc)]` and `η ∈ Y`
(by `ℤ`-linearity from the per-member
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`). -/
theorem inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {x : ClassFunction ↥L ℂ} (hx : x ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator))
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem χ hχ =>
      exact hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
        hF hHnonab hp hp3 hHp hχ hη
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add a b _ _ iha ihb => rw [map_add, ClassFunction.inner_add_left, iha, ihb, add_zero]
  | smul c a _ ih =>
      rw [map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ c
          ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension a),
        ClassFunction.inner_smul_left, ih, mul_zero]

/-- **Case-(A)/c2 mirror of `inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_span_Xset_centralCommutator_Yset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {x : ClassFunction ↥L ℂ} (hx : x ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator))
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem χ hχ =>
      exact hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_c2_caseA
        hK hW1 hA hHnonab hp hp3 hHp hχ hη
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add a b _ _ iha ihb => rw [map_add, ClassFunction.inner_add_left, iha, ihb, add_zero]
  | smul c a _ ih =>
      rw [map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ c
          ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension
            a),
        ClassFunction.inner_smul_left, ih, mul_zero]

/-- **(6.8.1) Res-decomposition orthogonality** (spine steps 1–2): `Res^G_L(η^{τ₁})` is orthogonal
to every *supported* `X(Zc)`-combination.  For `η ∈ Y` and `x ∈ ℤ[X(Zc), H^#]` (supported),
`⟨Res^G_L(η^{τ₁}), x⟩_L = 0`.  By Dade reciprocity (`inner_tau_eq_inner_restrict`,
`⟨x^τ, η^{τ₁}⟩_G = ⟨x, Res_L(η^{τ₁})⟩_L`) and `x^τ = x^{τ₂}` (supported), this reduces to the span
form of `himg_ortho` (`⟨x^{τ₂}, η^{τ₁}⟩_G = 0`).  Hence the `X`-components of `Res^G_L(η^{τ₁})` are
all proportional to `dᵢ`, i.e. `Res^G_L(η^{τ₁}) = c·∑dᵢχᵢ + χ′` with `χ′ ⊥ X(Zc)` (mmd 04.8 L170). -/
theorem inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) x = 0 := by
  classical
  have hrec := hyp.inner_tau_eq_inner_restrict hx.2 (hyp.coherentYset.extension η)
  have hτ : hyp.tau x =
      (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x :=
    ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extends_on_supported
      x hx).symm
  have h0 : ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 :=
    hyp.inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
      hF hHnonab hp hp3 hHp hx.1 hη
  have hxr : ClassFunction.inner x
      (ClassFunction.restrict L (hyp.coherentYset.extension η)) = 0 := by
    rw [← hrec, hτ, h0]
  rw [inner_conj_symm x (ClassFunction.restrict L (hyp.coherentYset.extension η)), hxr, star_zero]

/-- **Case-(A)/c2 mirror of `inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_restrict_extension_Yset_mem_span_Xset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) x = 0 := by
  classical
  have hrec := hyp.inner_tau_eq_inner_restrict hx.2 (hyp.coherentYset.extension η)
  have hτ : hyp.tau x =
      (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension x :=
    ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3
      hHp).extends_on_supported x hx).symm
  have h0 : ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 :=
    hyp.inner_extension_span_Xset_centralCommutator_Yset_eq_zero_c2_caseA
      hK hW1 hA hHnonab hp hp3 hHp hx.1 hη
  have hxr : ClassFunction.inner x
      (ClassFunction.restrict L (hyp.coherentYset.extension η)) = 0 := by
    rw [← hrec, hτ, h0]
  rw [inner_conj_symm x (ClassFunction.restrict L (hyp.coherentYset.extension η)), hxr, star_zero]

/-- **(6.8.1) Res `X`-coefficient proportionality** (mmd 04.8 L170).  For `χ, χ' ∈ X(Zc)` and
`R = Res^G_L(η^{τ₁})` (`η ∈ Y`), `χ'(1)·⟨R, χ⟩ = χ(1)·⟨R, χ'⟩` — the `X`-Fourier coefficients of `R`
are proportional to the degrees (`⟨R,χᵢ⟩ ∝ dᵢ`, the `Res^G_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′` decomposition).
Apply Res-orthogonality (`inner_restrict_extension_Yset_mem_span_Xset_eq_zero`) to the supported
integer combination `χ'(1)•χ − χ(1)•χ'` (degree-`0`, `sMember_smulDiffSupport_of_charValue_eq`). -/
theorem inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    (hχ' : χ' ∈ hyp.Xset hyp.centralCommutator) :
    (χ' 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ
      = (χ 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ' := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  obtain ⟨d, _hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', _hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hx_supp : (d' • χ - d • χ') ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ)
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ')
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ') (by rw [hd_eq, hd'_eq]; ring)
  have hortho := hyp.inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    hF hHnonab hp hp3 hHp hη hx_supp
  rw [ClassFunction.inner_sub_right,
    ← Nat.cast_smul_eq_nsmul ℂ d' χ, ← Nat.cast_smul_eq_nsmul ℂ d χ',
    OddOrder.RepresentationTheory.inner_smul_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast, star_natCast, ← hd'_eq, ← hd_eq] at hortho
  exact sub_eq_zero.mp hortho

/-- **Case-(A)/c2 mirror of `inner_restrict_extension_Yset_mul_degree_eq_of_frobenius`.**  Same as
the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle `cert`/`hK`/`hW1`/`hA`,
and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_restrict_extension_Yset_mul_degree_eq_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    (hχ' : χ' ∈ hyp.Xset hyp.centralCommutator) :
    (χ' 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ
      = (χ 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ' := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  obtain ⟨d, _hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', _hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hx_supp : (d' • χ - d • χ') ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ)
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ')
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ') (by rw [hd_eq, hd'_eq]; ring)
  have hortho := hyp.inner_restrict_extension_Yset_mem_span_Xset_eq_zero_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hx_supp
  rw [ClassFunction.inner_sub_right,
    ← Nat.cast_smul_eq_nsmul ℂ d' χ, ← Nat.cast_smul_eq_nsmul ℂ d χ',
    OddOrder.RepresentationTheory.inner_smul_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast, star_natCast, ← hd'_eq, ← hd_eq] at hortho
  exact sub_eq_zero.mp hortho

/-- **(6.8.1) `η^{τ₁}` constancy value on `Zc^#`** (mmd 04.8 L168, the key constant).  For `η ∈ Y`,
`χ₁ ∈ X(Zc)` and `z ∈ Zc^#`, with `R = Res^G_L(η^{τ₁})`,
`χ₁(1)·(R(z) − R(1)) = -⟨R, χ₁⟩·|L|`.  Since the right side is independent of `z`, this shows `R`
(hence `η^{τ₁}`) is **constant on `Zc^#`** (and gives the value `R(z) − R(1) = -c|H|/a` with
`c = ⟨R,χ₁⟩`, `χ₁(1) = a|W₁|`, after clearing the denominator).

Proof: Fourier-expand `R = ∑_{a∈Irr L} ⟨R,a⟩•a` (`classFunction_eq_sum_inner_smul`); split the sum
by `Zc ⊄ ker`.  On `Zc ⊆ ker` (the non-`X` part) `a(z) = a(1)`, so those terms vanish.  On `X(Zc)`
the coefficient relation `χ₁(1)⟨R,a⟩ = a(1)⟨R,χ₁⟩` (`inner_restrict_extension_Yset_mul_degree_eq`)
factors out `⟨R,χ₁⟩`, leaving `⟨R,χ₁⟩·∑_{a∈X} a(1)(a(z)−a(1)) = ⟨R,χ₁⟩·(-|L|)`
(`sum_filter_degree_mul_charValue_sub_eq`). -/
theorem restrict_extension_Yset_degree_value_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (χ₁ 1) * ((ClassFunction.restrict L (hyp.coherentYset.extension η)) z
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1)
      = -(ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁)
          * (Nat.card ↥L : ℂ) := by
  classical
  haveI : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  have hval : R z - R 1 = ∑ a : IrreducibleCharacter ↥L,
      ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
        ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) := by
    conv_lhs => rw [OddOrder.RepresentationTheory.classFunction_eq_sum_inner_smul R]
    rw [ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : IrreducibleCharacter ↥L => ¬ ((hyp.centralCommutator : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ)))]
  have hnot : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_filter, not_not] at ha
    have haz : (a : ClassFunction ↥L ℂ) z = (a : ClassFunction ↥L ℂ) 1 := by
      have hmem := ha.2 hz
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hmem
      exact hmem
    rw [haz, sub_self, mul_zero, mul_zero]
  rw [hnot, add_zero]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)))
      = (ClassFunction.inner R χ₁) *
        (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
          ¬ ((hyp.centralCommutator : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
          (a : ClassFunction ↥L ℂ) 1 *
            ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have haX : (a : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
      rw [hyp.Xset_eq_irreducible_not_subset_characterKernel hyp.centralCommutator_le
        (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)]
      exact ⟨a.isIrreducible, ha.2⟩
    have hrel := hyp.inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
      hF hHnonab hp hp3 hHp hη haX hχ₁
    rw [← hRdef] at hrel
    linear_combination ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) * hrel
  rw [hfilter, OddOrder.RepresentationTheory.sum_filter_degree_mul_charValue_sub_eq
    (N := hyp.centralCommutator) hz hz1]
  ring

/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_degree_value_eq_of_frobenius`.**  Same as the
Frobenius original, with `hF` replaced by the certain-type case-(A) bundle `cert`/`hK`/`hW1`/`hA`, and
the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_degree_value_eq_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (χ₁ 1) * ((ClassFunction.restrict L (hyp.coherentYset.extension η)) z
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1)
      = -(ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁)
          * (Nat.card ↥L : ℂ) := by
  classical
  haveI : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  have hval : R z - R 1 = ∑ a : IrreducibleCharacter ↥L,
      ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
        ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) := by
    conv_lhs => rw [OddOrder.RepresentationTheory.classFunction_eq_sum_inner_smul R]
    rw [ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : IrreducibleCharacter ↥L => ¬ ((hyp.centralCommutator : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ)))]
  have hnot : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_filter, not_not] at ha
    have haz : (a : ClassFunction ↥L ℂ) z = (a : ClassFunction ↥L ℂ) 1 := by
      have hmem := ha.2 hz
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hmem
      exact hmem
    rw [haz, sub_self, mul_zero, mul_zero]
  rw [hnot, add_zero]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)))
      = (ClassFunction.inner R χ₁) *
        (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
          ¬ ((hyp.centralCommutator : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
          (a : ClassFunction ↥L ℂ) 1 *
            ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have haX : (a : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
      rw [hyp.Xset_eq_irreducible_not_subset_characterKernel hyp.centralCommutator_le
        (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h)]
      exact ⟨a.isIrreducible, ha.2⟩
    have hrel := hyp.inner_restrict_extension_Yset_mul_degree_eq_c2_caseA
      hK hW1 hA hHnonab hp hp3 hHp hη haX hχ₁
    rw [← hRdef] at hrel
    linear_combination ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) * hrel
  rw [hfilter, OddOrder.RepresentationTheory.sum_filter_degree_mul_charValue_sub_eq
    (N := hyp.centralCommutator) hz hz1]
  ring

/-- **(6.8.1) `η^{τ₁}` is constant on `Zc^#`** (mmd 04.8 L168 conclusion).  For `η ∈ Y`, the
restriction `Res^G_L(η^{τ₁})` takes the same value at any two points of `Zc^#`.  Immediate from the
value identity `restrict_extension_Yset_degree_value_eq_of_frobenius` (whose right side `-⟨R,χ₁⟩·|L|`
is independent of the point) and `χ₁(1) ≠ 0` (any anchor `χ₁ ∈ X(Zc)`, nonempty).  This is the exact
"character constant on `Z^#`" hypothesis of the (6.7) adapter `peterfalvi_67_centralCommutator`. -/
theorem restrict_extension_Yset_const_on_centralCommutator_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z z' : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1)
    (hz' : z' ∈ hyp.centralCommutator) (hz'1 : z' ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z' := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hd : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd_eq
    rw [hd_eq]; exact_mod_cast hd_pos.ne'
  have hv := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz hz1
  have hv' := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz' hz'1
  have hcancel : (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z'
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    mul_left_cancel₀ hd (hv.trans hv'.symm)
  linear_combination hcancel

/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_const_on_centralCommutator_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_const_on_centralCommutator_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z z' : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1)
    (hz' : z' ∈ hyp.centralCommutator) (hz'1 : z' ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z' := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.Xset_centralCommutator_nonempty_c2_caseA hK hW1 hA hHnonab
  have hd : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd_eq
    rw [hd_eq]; exact_mod_cast hd_pos.ne'
  have hv := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz hz1
  have hv' := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz' hz'1
  have hcancel : (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z'
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    mul_left_cancel₀ hd (hv.trans hv'.symm)
  linear_combination hcancel

/-- **L3 (3a) shell, ν-free form:** `X(Zc) ∪ Y` is coherent given only the genuine (6.8.1) input
`himg_ortho : ⟨χ^{τ₂}, η^{τ₁}⟩ = 0`.  The `τ₃` glue `ν` is constructed internally
(`exists_integralCharacterMap_glue_of_orthonormal` with `νX = τ₂`, `νY = τ₁`); its agreement
`hagreeX`/`hagreeY` is automatic, and `hmixed` reduces to `himg_ortho` (both `⟨νx,νy⟩` and `⟨x,y⟩`
vanish — the latter by `X ⊥ Y`).  Orthonormality of `X`, `Y` and `X ⊥ Y` are read off irreducibility
(`irreducibleCharacter_inner`) + disjointness.  **The sole remaining (6.8.1) obligation is
`himg_ortho`** — the `b ≡ c ≡ 0 mod a` argument (L3 (3b), via `peterfalvi_67_centralCommutator`). -/
noncomputable def coherentXunionYset_centralCommutator_of_himg_ortho
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (himg_ortho : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner
        ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
        (hyp.coherentYset.extension y) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension)
      hyp.coherentYset.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_of_frobenius hF hHnonab hp hp3 hHp
    hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_) hgen
  rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy, himg_ortho x hx y hy, hXY x hx y hy]

/-- **(6.8.1), Frobenius case:** chain-level coherence for
`X = S - S(H')`, using common-index p-power data.

This is the `Z = H'` specialization of
`Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X` for the Frobenius
alternative.  The subgroup facts `H' ≤ H`, `H' ⊴ L`, and `X ⊆ Irr L` are discharged internally;
the remaining inputs are the honest (6.6) nonemptiness and per-step degree data. -/
noncomputable def Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.8.1), Frobenius case:** chain-level coherence for
`X = S - S(H')`, using the base-anchor common-index p-power step packages.

Compared with
`Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius`, each step data
package only supplies a base-block anchor; the sorted-degree facts are derived by the existing
base-anchor adapter. -/
noncomputable def
    Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.6)/(6.8.1), central-`Zc` form (redesign L2 outer shell):** chain-level coherence for
`X = S − S(Zc)` with the **central** `Zc = Z(H) ∩ H′`, from base-anchor common-index p-power step
packages.  This replaces `Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
(which instantiated the general (6.6) consumer at `Z = ⁅H,H⁆`, where the per-step degree field
`hθsq_le_qtot : θχ² ≤ qtot ≤ |H:⁅H,H⁆|` is *unsatisfiable* for class ≥ 3 `p`-groups — see
`notes/peterfalvi/s08_6_8_blocker_central_Z.md`).  At the central `Zc` that field is honestly fillable
by [Is] Cor 2.30 (`exists_source_primePow_centralBound_of_mem_Xset`), so the `hstepData` hypothesis
is satisfiable here — the remaining work is to *construct* it (the producer monolith).  `hX` is
discharged Z-generically (`isIrreducibleCharacter_of_mem_Xset_of_frobenius`) and `hXne` from `H`
non-abelian (`Xset_centralCommutator_nonempty`). -/
noncomputable def
    Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset hyp.centralCommutator) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L)
          (hyp.xBaseBlock hyp.centralCommutator) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := hyp.centralCommutator) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  exact hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (Z := hyp.centralCommutator) hyp.centralCommutator_le
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hstepData

/-- **(6.8.1), Frobenius case:** final glue from common-index p-power X-chain data.

This composes the Frobenius `X = S - S(H')` coherence constructor with the generator-level `τ₃`
glue adapter.  The caller supplies only the genuine (6.6) X-chain step data and generator-level
`τ₃` agreement/mixed-inner facts; the `X` coherence witness is built internally. -/
noncomputable def coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x = (hyp.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
        hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner hF
    (hyp.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

/-- **(6.8.1), Frobenius case:** final glue from base-anchor common-index p-power X-chain data.

This is the same capstone as
`coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner`, but using the
base-anchor step package that derives the sorted-degree inequalities internally. -/
noncomputable def
    coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
          hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner hF
    (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

/-- **(6.7)-wiring step (b): `N_G(H.map L.subtype) = L`.**  The normalizer (in `G`) of the kernel
realized in the ambient group is exactly `L`: `≤` is the `H^#` TI condition (`H_sharp_ti`; a
nontrivial `a ∈ Ĥ` and its conjugate witness the TI hypothesis), and `≥` holds because `H ◁ L`
(`L = range L.subtype` normalizes the image of the normal `H`, via `le_normalizer_map`). -/
theorem normalizer_map_subtype_eq (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    Subgroup.normalizer (H.map L.subtype) = L := by
  apply le_antisymm
  · haveI : Nontrivial ↥H := H.nontrivial_iff_ne_bot.mpr hyp.H_ne_bot
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥H)
    set a : G := ((x : ↥L) : G) with ha_def
    have haĤ : a ∈ H.map L.subtype := Subgroup.mem_map.mpr ⟨(x : ↥L), x.2, rfl⟩
    have ha1 : a ≠ 1 := by rw [ha_def]; simp only [ne_eq, OneMemClass.coe_eq_one]; exact hx1
    intro g hg
    refine hyp.H_sharp_ti g ⟨a, ⟨haĤ, ha1⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg a).mp haĤ
    · intro hc
      rw [Set.mem_singleton_iff, mul_inv_eq_one, mul_eq_left] at hc
      exact ha1 hc
  · calc L = L.subtype.range := (Subgroup.range_subtype L).symm
      _ = (⊤ : Subgroup ↥L).map L.subtype := MonoidHom.range_eq_map L.subtype
      _ = (Subgroup.normalizer H).map L.subtype := by
          rw [Subgroup.normalizer_eq_top_iff.mpr ‹H.Normal›]
      _ ≤ Subgroup.normalizer (H.map L.subtype) := H.le_normalizer_map L.subtype

/-- **`Ĥ = H.map L.subtype` is a Sylow `p`-subgroup of `G`, from the Hall coprimality** — the
coprimality-only core of `sylow_map_subtype_of_frobenius`.  Peterfalvi (6.8)(a) only assumes `H^#`
TI with normalizer `L`, which alone does *not* force `H` Sylow; the only extra input is
`gcd(|H|, |W₁|) = 1` (Frobenius: `hF.coprime_card_kernel_complement`; (6.8)(c2): the `cases` Hall
side condition).  With `H` a `p`-group and `H ◁ L` with coprime complement `W₁`, `H` is the unique
normal Sylow `p`-subgroup of `↥L`, so every `p`-subgroup of `↥L` (e.g. `Q ⊓ L` for a Sylow
`Q ⊇ Ĥ`) lies in `H`; with `N_G(Ĥ) ≤ L` (`H^#` TI) and the self-normalizing-Sylow criterion
`sylow_coe_eq_of_normalizer_inf_le`, this forces `Ĥ ∈ Syl_p(G)`.  (Lifted from `S08_CaseBCoherence`;
both Frobenius and case-(A)/(B) (6.7)-wirings delegate here.) -/
theorem sylow_map_subtype_of_coprime (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Ĥ : Subgroup G := H.map L.subtype with hĤ_def
  -- `Ĥ` is a `p`-group (image of the `p`-group `H` under the injective `L.subtype`).
  have hĤp : IsPGroup p ↥Ĥ := hHp.map L.subtype
  -- `p ∣ |H|` (nontrivial `p`-group) and `gcd(|H|, |W₁|) = 1`, so `p ∤ [L : H] = |W₁|`.
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
  -- `H` is the unique (normal) Sylow `p`-subgroup of `↥L`.
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
  -- `N_G(Ĥ) ≤ L` from `H^#` TI (the `normalizer_map_subtype_eq` equality).
  have hNle : Subgroup.normalizer Ĥ ≤ L := hyp.normalizer_map_subtype_eq.le
  -- a Sylow overgroup `Q ⊇ Ĥ`; then `N_G(Ĥ) ⊓ Q ≤ Ĥ` via the `p`-subgroup `Q.comap L.subtype ≤ H`.
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

/-- **(6.7)-wiring step (a): the kernel `H`, mapped into `G`, is a Sylow `p`-subgroup of `G`.**

Peterfalvi (6.7) is stated for a Sylow `p`-subgroup `P` of `G` with `L = N_G(P)`; the (6.8.1)
application uses it at `P = H` (modulus `|H|`).  In the **Frobenius case**, `H ◁ L` with complement
`W₁` of coprime order (`hF.coprime_card_kernel_complement`) makes `H` Sylow; delegates to the
coprimality core `sylow_map_subtype_of_coprime`. -/
theorem sylow_map_subtype_of_frobenius (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype :=
  hyp.sylow_map_subtype_of_coprime hF.coprime_card_kernel_complement hp hHp

open scoped OddOrder.AlgInt in
/-- **(6.7)-wiring capstone: Peterfalvi (6.7) specialized to the Sibley Frobenius setup.**

For an irreducible `ρ` whose character is **constant on `Z^# = (Z(H) ∩ H′)^#`** (the only
character-theoretic input, deferred to the caller — in (6.8.1) it is `η₁^{τ₁}`), the congruence

`ρ.character z ≡ ρ.character 1  (mod |H|)`

holds for `z ∈ Z^#`.  This discharges every structural hypothesis of `peterfalvi_67_of_odd` at
`P := Ĥ = H.map L.subtype` (Sylow in `G` by `sylow_map_subtype_of_frobenius`, with `N_G(Ĥ) = L` by
`normalizer_map_subtype_eq`) and `Z := centralCommutator.map L.subtype`: `hZP`, `hZnormal`
(`Z.subgroupOf L = centralCommutator ◁ ↥L`), `hti`/`hodd` (`H^#` TI / `|L|` odd), `hPz`
(`Ĥ ≤ C_G(z)`), and the `|C_L(·)|`-constancy clause of `hconst` (both sides `= |Ĥ|` by
`inf_centralizer_centralCommutator_map`).  The modulus `|Ĥ| = |H|` via `card_map_of_injective`. -/
theorem peterfalvi_67_centralCommutator (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ hyp.centralCommutator.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
        ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_frobenius hF hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : hyp.centralCommutator.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hyp.centralCommutator_le
  have hZnormal : ((hyp.centralCommutator.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (hyp.centralCommutator.map L.subtype).subgroupOf L = hyp.centralCommutator from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hyp.centralCommutator_normal
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hQeq]
    obtain ⟨w', hw', hw'z⟩ := Subgroup.mem_map.mp hz
    have hw'zc : (w' : G) = z := hw'z
    have hw'1 : w' ≠ 1 := fun h => hz1 (hw'zc ▸ OneMemClass.coe_eq_one.mpr h)
    have hbr := hyp.inf_centralizer_centralCommutator_map hF hw' hw'1
    rw [hw'zc] at hbr
    rw [← hbr]; exact inf_le_right
  have hconst : ∀ ⦃w : G⦄, w ∈ hyp.centralCommutator.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w', hw'cc, hw'w⟩ := Subgroup.mem_map.mp hw
    have hw'wc : (w' : G) = w := hw'w
    have hw'1 : w' ≠ 1 := fun h => hw1 (hw'wc ▸ OneMemClass.coe_eq_one.mpr h)
    obtain ⟨z', hz'cc, hz'z⟩ := Subgroup.mem_map.mp hz
    have hz'zc : (z' : G) = z := hz'z
    have hz'1 : z' ≠ 1 := fun h => hz1 (hz'zc ▸ OneMemClass.coe_eq_one.mpr h)
    rw [hNorm, ← hw'wc, ← hz'zc, hyp.inf_centralizer_centralCommutator_map hF hw'cc hw'1,
      hyp.inf_centralizer_centralCommutator_map hF hz'cc hz'1]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.7)-wiring capstone, case-(A) / c2 form.**  The (c2) analogue of
`peterfalvi_67_centralCommutator`: the (6.7) congruence `ρ.character z ≡ ρ.character 1 (mod |H|)`
for `z ∈ Zc^#` and `ρ` irreducible **constant on `Zc^#`**, *without* the Frobenius hypothesis.  `H`
is Sylow in `G` via the coprimality core `sylow_map_subtype_of_coprime` (coprimality from
`cert.card_coprime`), and the `|C_L(·)|`-constancy clause of `hconst` is the case-(A) FPF
`inf_centralizer_centralCommutator_map_c2_caseA`.  Otherwise structurally identical to the
Frobenius form. -/
theorem peterfalvi_67_centralCommutator_c2_caseA (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ hyp.centralCommutator.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
        ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1) := by
    have h := cert.card_coprime; rw [hK, hW1] at h; exact h
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_coprime hcop hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : hyp.centralCommutator.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hyp.centralCommutator_le
  have hZnormal : ((hyp.centralCommutator.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (hyp.centralCommutator.map L.subtype).subgroupOf L = hyp.centralCommutator from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hyp.centralCommutator_normal
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hQeq]
    obtain ⟨w', hw', hw'z⟩ := Subgroup.mem_map.mp hz
    have hw'zc : (w' : G) = z := hw'z
    have hw'1 : w' ≠ 1 := fun h => hz1 (hw'zc ▸ OneMemClass.coe_eq_one.mpr h)
    have hbr := hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hw' hw'1
    rw [hw'zc] at hbr
    rw [← hbr]; exact inf_le_right
  have hconst : ∀ ⦃w : G⦄, w ∈ hyp.centralCommutator.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w', hw'cc, hw'w⟩ := Subgroup.mem_map.mp hw
    have hw'wc : (w' : G) = w := hw'w
    have hw'1 : w' ≠ 1 := fun h => hw1 (hw'wc ▸ OneMemClass.coe_eq_one.mpr h)
    obtain ⟨z', hz'cc, hz'z⟩ := Subgroup.mem_map.mp hz
    have hz'zc : (z' : G) = z := hz'z
    have hz'1 : z' ≠ 1 := fun h => hz1 (hz'zc ▸ OneMemClass.coe_eq_one.mpr h)
    rw [hNorm, ← hw'wc, ← hz'zc,
      hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hw'cc hw'1,
      hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hz'cc hz'1]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.8.1) (6.7)-congruence for `η^{τ₁}`** (mmd 04.8 L168 → L176).  For `η ∈ Y` and `z ∈ Zc^#`,
`Res^G_L(η^{τ₁})(z) ≡ Res^G_L(η^{τ₁})(1) (mod |H|)`.  Wires the (6.7) adapter
`peterfalvi_67_centralCommutator` to `η^{τ₁}`: write `η^{τ₁} = ε•ξ` (`ε = ±1`, `ξ` irreducible, from
norm `1`); unpack `ξ = ρ.character` (`ρ` irreducible).  The const-on-`Zc^#`
(`restrict_extension_Yset_const_on_centralCommutator_of_frobenius`, transferred to `Zc.map`) is the
adapter's hypothesis, giving `ξ(z) ≡ ξ(1) (mod |H|)`; scale by `ε` (`Cong.smul_left`) to get
`η^{τ₁}(z) ≡ η^{τ₁}(1)`. -/
theorem restrict_extension_Yset_charValue_cong_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hηtnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η (Submodule.subset_span hη)
      (Submodule.subset_span hη)]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
    simpa using h
  obtain ⟨ε, ξ, hε, hηtε⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hηtZ hηtnorm
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  -- the eval identity `η^{τ₁}(g) = ε · ξ(g)`.
  have hsmul : ∀ g : G, (hyp.coherentYset.extension η) g = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  haveI : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ hyp.centralCommutator.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.restrict_extension_Yset_const_on_centralCommutator_of_frobenius
        hF hHnonab hp hp3 hHp hη hw₀ hw₀1 hz hz1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_centralCommutator hF hp hHp ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_charValue_cong_of_frobenius`.**  Same as the
Frobenius original, with `hF` replaced by the certain-type case-(A) bundle `cert`/`hK`/`hW1`/`hA`, and
the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_charValue_cong_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hηtnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η (Submodule.subset_span hη)
      (Submodule.subset_span hη)]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
    simpa using h
  obtain ⟨ε, ξ, hε, hηtε⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hηtZ hηtnorm
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  -- the eval identity `η^{τ₁}(g) = ε · ξ(g)`.
  have hsmul : ∀ g : G, (hyp.coherentYset.extension η) g = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  haveI : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ hyp.centralCommutator.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.restrict_extension_Yset_const_on_centralCommutator_c2_caseA
        hK hW1 hA hHnonab hp hp3 hHp hη hw₀ hw₀1 hz hz1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_centralCommutator_c2_caseA hK hW1 hA hp hHp ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **(6.8.1) `a ∣ c`** (mmd 04.8 L176, the `c ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` of degree `χ₁(1) = a·|W₁|` (`a > 0`, the degree ratio against
the `Y`-degree `|W₁|`), the multiplicity `c = ⟨Res^G_L(η^{τ₁}), χ₁⟩` is an **integer divisible by
`a`**.

This is the (6.7) divisibility step.  The value identity
`restrict_extension_Yset_degree_value_eq_of_frobenius` gives `χ₁(1)·(R(z)−R(1)) = −c·|L|` for
`z ∈ Zc^#` (`R = Res^G_L(η^{τ₁})`); with `χ₁(1) = a|W₁|` and `|L| = |H|·|W₁|`
(`index_H_eq_card_W1` + `index_mul_card`) it becomes `a·(R(z)−R(1)) = −c·|H|`, i.e.
`(R(z)−R(1))/|H| = −c/a`.  The (6.7)-congruence
`restrict_extension_Yset_charValue_cong_of_frobenius` says `(R(z)−R(1))/|H|` is an algebraic integer;
so the rational `−c/a` is an algebraic integer, hence an integer (`isIntegral_rat_imp_int`), i.e.
`a ∣ c`.  (`c ∈ ℤ` because `R ∈ ZIrr L` and `χ₁` is irreducible, `mem_ZIrr_inner_int`.) -/
theorem dvd_inner_restrict_extension_Yset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cc : ℤ,
      ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁ = (cc : ℂ)
        ∧ (a : ℤ) ∣ cc := by
  classical
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  -- `c := ⟨R, χ₁⟩` is an integer (`R ∈ ZIrr L`, `χ₁` irreducible).
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : R ∈ ZIrr (↥L) := OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
  obtain ⟨cc, hcc⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ₁ from rfl] at hcc
  refine ⟨cc, hcc, ?_⟩
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hHne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- pick `z ∈ Zc^#`.
  obtain ⟨⟨z, hz⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (hyp.centralCommutator_ne_bot hHnonab)
  have hz1 : z ≠ 1 := fun h => hzne (Subtype.ext h)
  -- value identity: `χ₁(1)·(R z − R 1) = −c·|L|`, with `χ₁(1) = a|W₁|`, `c = cc`, `|L| = |H||W₁|`.
  have hval := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz hz1
  rw [← hRdef, hcc, ha] at hval
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card hyp.W1 : ℂ) := by
    have h := Subgroup.index_mul_card H
    rw [hyp.index_H_eq_card_W1] at h
    have hc : ((Nat.card hyp.W1 * Nat.card ↥H : ℕ) : ℂ) = (Nat.card ↥L : ℂ) := by rw [h]
    push_cast at hc; linear_combination -hc
  rw [hLcard] at hval
  -- cancel `|W₁|`: `a·(R z − R 1) = −c·|H|`.
  have haD : (a : ℂ) * (R z - R 1) = -(cc : ℂ) * (Nat.card ↥H : ℂ) := by
    apply mul_left_cancel₀ hW1ne
    linear_combination hval
  -- the (6.7)-congruence: `(R z − R 1)/|H|` is an algebraic integer.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_of_frobenius
    hF hHnonab hp hp3 hHp hη hz hz1
  rw [← hRdef, OddOrder.AlgInt.cong_def, Int.cast_natCast] at hcong
  -- `c/a = −((R z − R 1)/|H|)`, so `c/a` is an algebraic integer.
  have hccdiv : (cc : ℂ) / (a : ℂ) = -((R z - R 1) / (Nat.card ↥H : ℂ)) := by
    rw [← neg_div, div_eq_div_iff hane hHne]
    linear_combination haD
  have hintc : IsIntegral ℤ ((cc : ℂ) / (a : ℂ)) := by rw [hccdiv]; exact hcong.neg
  -- a rational algebraic integer is an integer ⟹ `a ∣ c`.
  have hqcast : (((cc : ℚ) / (a : ℚ) : ℚ) : ℂ) = (cc : ℂ) / (a : ℂ) := by push_cast; ring
  obtain ⟨n, hn⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int
    (q := (cc : ℚ) / (a : ℚ)) (by rw [hqcast]; exact hintc)
  rw [hqcast, div_eq_iff hane] at hn
  refine ⟨n, ?_⟩
  have : (cc : ℂ) = ((a : ℤ) * n : ℤ) := by rw [hn]; push_cast; ring
  exact_mod_cast this

/-- **(6.8.1) `a ∣ c`**, case (A) / c2 mirror of `dvd_inner_restrict_extension_Yset_of_frobenius`.
`X`-irreducibility uses `isIrreducibleCharacter_of_mem_Xset_c2_caseA`, and the value/congruence
inputs use the case-(A) `restrict_extension_Yset_degree_value_eq_c2_caseA` /
`restrict_extension_Yset_charValue_cong_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem dvd_inner_restrict_extension_Yset_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cc : ℤ,
      ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁ = (cc : ℂ)
        ∧ (a : ℤ) ∣ cc := by
  classical
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  -- `c := ⟨R, χ₁⟩` is an integer (`R ∈ ZIrr L`, `χ₁` irreducible).
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : R ∈ ZIrr (↥L) := OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
  obtain ⟨cc, hcc⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ₁ from rfl] at hcc
  refine ⟨cc, hcc, ?_⟩
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hHne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- pick `z ∈ Zc^#`.
  obtain ⟨⟨z, hz⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (hyp.centralCommutator_ne_bot hHnonab)
  have hz1 : z ≠ 1 := fun h => hzne (Subtype.ext h)
  -- value identity: `χ₁(1)·(R z − R 1) = −c·|L|`, with `χ₁(1) = a|W₁|`, `c = cc`, `|L| = |H||W₁|`.
  have hval := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz hz1
  rw [← hRdef, hcc, ha] at hval
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card hyp.W1 : ℂ) := by
    have h := Subgroup.index_mul_card H
    rw [hyp.index_H_eq_card_W1] at h
    have hc : ((Nat.card hyp.W1 * Nat.card ↥H : ℕ) : ℂ) = (Nat.card ↥L : ℂ) := by rw [h]
    push_cast at hc; linear_combination -hc
  rw [hLcard] at hval
  -- cancel `|W₁|`: `a·(R z − R 1) = −c·|H|`.
  have haD : (a : ℂ) * (R z - R 1) = -(cc : ℂ) * (Nat.card ↥H : ℂ) := by
    apply mul_left_cancel₀ hW1ne
    linear_combination hval
  -- the (6.7)-congruence: `(R z − R 1)/|H|` is an algebraic integer.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hz hz1
  rw [← hRdef, OddOrder.AlgInt.cong_def, Int.cast_natCast] at hcong
  -- `c/a = −((R z − R 1)/|H|)`, so `c/a` is an algebraic integer.
  have hccdiv : (cc : ℂ) / (a : ℂ) = -((R z - R 1) / (Nat.card ↥H : ℂ)) := by
    rw [← neg_div, div_eq_div_iff hane hHne]
    linear_combination haD
  have hintc : IsIntegral ℤ ((cc : ℂ) / (a : ℂ)) := by rw [hccdiv]; exact hcong.neg
  -- a rational algebraic integer is an integer ⟹ `a ∣ c`.
  have hqcast : (((cc : ℚ) / (a : ℚ) : ℚ) : ℂ) = (cc : ℂ) / (a : ℂ) := by push_cast; ring
  obtain ⟨n, hn⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int
    (q := (cc : ℚ) / (a : ℚ)) (by rw [hqcast]; exact hintc)
  rw [hqcast, div_eq_iff hane] at hn
  refine ⟨n, ?_⟩
  have : (cc : ℂ) = ((a : ℤ) * n : ℤ) := by rw [hn]; push_cast; ring
  exact_mod_cast this

/-- **(6.8.1) `a ∣ b`** (mmd 04.8 L176, the `b ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η = η₁ ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|` (`a > 0`), the `η₁^{τ₁}`-coefficient
of the cross-diagonal image `(χ₁−aη₁)^τ` — namely `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩`, which is `b − a` in the
Peterfalvi decomposition (168) `(χ₁−aη₁)^τ = X − aη₁^{τ₁} + b∑η_j^{τ₁}` — is an **integer divisible
by `a`**.  Since `a ∣ (b − a) ⟺ a ∣ b`, this is exactly Peterfalvi's `b ≡ 0 (mod a)`.

Direct route via Dade reciprocity (no need for the full (168) decomposition): `χ₁−aη₁` is supported
on `H^#` (`sMember_scaledDiffSupport_of_charValue_eq`, `χ₁(1) = a·η₁(1)` from `Yset_apply_one`), so
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, Res^G_L(η₁^{τ₁})⟩` (`inner_tau_eq_inner_restrict`)
`= ⟨χ₁, R⟩ − a·⟨η₁, R⟩ = c − a·e` (`R = Res^G_L(η₁^{τ₁})`; conjugate symmetry `inner_conj_symm` +
reality of the integers `c = ⟨R,χ₁⟩`, `e = ⟨R,η₁⟩`, `mem_ZIrr_inner_int`).  Since `a ∣ c`
(`dvd_inner_restrict_extension_Yset_of_frobenius`, step 2) and `a ∣ a·e`, `a ∣ (c − a·e)`. -/
theorem dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ bb : ℤ,
      ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.coherentYset.extension η) = (bb : ℂ)
        ∧ (a : ℤ) ∣ bb := by
  classical
  -- step 2: `c = ⟨R, χ₁⟩` is an integer with `a ∣ c`.
  obtain ⟨cc, hcc, hacc⟩ :=
    hyp.dvd_inner_restrict_extension_Yset_of_frobenius hF hHnonab hp hp3 hHp hη hχ₁ ha_pos ha
  -- `R ∈ ZIrr L`, `η₁` irreducible ⟹ `e := ⟨R, η₁⟩ ∈ ℤ`.
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : ClassFunction.restrict L (hyp.coherentYset.extension η) ∈ ZIrr (↥L) :=
    OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  obtain ⟨e, he⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨η, hηirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η from rfl] at he
  -- `χ₁ − a•η₁` is supported on `H^#`.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  -- reciprocity: `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩`.
  have hrec := hyp.inner_tau_eq_inner_restrict hsupp (hyp.coherentYset.extension η)
  refine ⟨cc - a * e, ?_, ?_⟩
  · rw [hrec, ClassFunction.inner_sub_left, ← Nat.cast_smul_eq_nsmul ℂ a η,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm _ χ₁, hcc,
      OddOrder.RepresentationTheory.inner_conj_symm _ η, he]
    simp only [star_intCast]
    push_cast; ring
  · exact dvd_sub hacc (dvd_mul_right _ _)

/-- **(6.8.1) `a ∣ b`**, case (A) / c2 mirror of `dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius`.
The `a ∣ c` input uses the case-(A) `dvd_inner_restrict_extension_Yset_c2_caseA`
(cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ bb : ℤ,
      ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.coherentYset.extension η) = (bb : ℂ)
        ∧ (a : ℤ) ∣ bb := by
  classical
  -- step 2: `c = ⟨R, χ₁⟩` is an integer with `a ∣ c`.
  obtain ⟨cc, hcc, hacc⟩ :=
    hyp.dvd_inner_restrict_extension_Yset_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ ha_pos ha
  -- `R ∈ ZIrr L`, `η₁` irreducible ⟹ `e := ⟨R, η₁⟩ ∈ ℤ`.
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : ClassFunction.restrict L (hyp.coherentYset.extension η) ∈ ZIrr (↥L) :=
    OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  obtain ⟨e, he⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨η, hηirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η from rfl] at he
  -- `χ₁ − a•η₁` is supported on `H^#`.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  -- reciprocity: `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩`.
  have hrec := hyp.inner_tau_eq_inner_restrict hsupp (hyp.coherentYset.extension η)
  refine ⟨cc - a * e, ?_, ?_⟩
  · rw [hrec, ClassFunction.inner_sub_left, ← Nat.cast_smul_eq_nsmul ℂ a η,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm _ χ₁, hcc,
      OddOrder.RepresentationTheory.inner_conj_symm _ η, he]
    simp only [star_intCast]
    push_cast; ring
  · exact dvd_sub hacc (dvd_mul_right _ _)

/-- **(6.8.1) cross-diagonal/`Y`-difference isometry** (mmd 04.8 L166, the constancy ingredient of
decomposition (168)).  For `η = η₁`, `η' = η_j ∈ Y` with `η' ≠ η`, and an `X`-anchor `χ₁ ∈ X(Zc)`
with `χ₁(1) = a·|W₁|` (`a > 0`):
`⟨(χ₁−aη₁)^τ, (η_j−η₁)^τ⟩ = a`.

By the Dade isometry on the supported pair `{χ₁−aη₁, η_j−η₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; `χ₁−aη₁` supported by
`sMember_scaledDiffSupport_of_charValue_eq`, `η_j−η₁` by `sMember_diffSupport_of_charValue_eq` at the
common degree `|W₁|`), the inner product equals the source `⟨χ₁−aη₁, η_j−η₁⟩`, which expands by
`X ⊥ Y` (`⟨χ₁,η_j⟩ = ⟨χ₁,η₁⟩ = 0`) and `Y`-orthonormality (`⟨η₁,η_j⟩ = 0`, `⟨η₁,η₁⟩ = 1`) to
`a·⟨η₁,η₁⟩ = a`.  This gives the constancy `β_j − β₁ = a` (j>1) of the `η_j^{τ₁}`-coefficients
`β_j = ⟨(χ₁−aη₁)^τ, η_j^{τ₁}⟩` of decomposition (168). -/
theorem inner_tau_scaledDiff_tau_Yset_diff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (η' - η)) = (a : ℂ) := by
  classical
  -- irreducibility + disjointness `X(Zc) ⊥ Y`.
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported difference inputs.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsuppX : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  have hsuppY : (η' - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη).symm)
  -- Dade isometry on the supported pair.
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η, η' - η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- the source orthogonality computation `⟨χ₁ − a•η, η' − η⟩ = a`.
  have hXY : ∀ ψ ∈ hyp.Yset, ClassFunction.inner χ₁ ψ = 0 := by
    intro ψ hψ
    exact inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hXirr φ hφ) (fun φ hφ => hYirr φ hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      ψ (Submodule.subset_span hψ)
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXY η' hη', hXY η hη, hYon η η' hη hη', hYon η η hη hη, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) cross-diagonal/`Y`-difference isometry**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`.  `X`-irreducibility comes from the certain-type
input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Yset_diff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (η' - η)) = (a : ℂ) := by
  classical
  -- irreducibility + disjointness `X(Zc) ⊥ Y`.
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported difference inputs.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsuppX : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  have hsuppY : (η' - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη).symm)
  -- Dade isometry on the supported pair.
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η, η' - η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- the source orthogonality computation `⟨χ₁ − a•η, η' − η⟩ = a`.
  have hXY : ∀ ψ ∈ hyp.Yset, ClassFunction.inner χ₁ ψ = 0 := by
    intro ψ hψ
    exact inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hXirr φ hφ) (fun φ hφ => hYirr φ hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      ψ (Submodule.subset_span hψ)
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXY η' hη', hXY η hη, hYon η η' hη hη', hYon η η hη hη, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) norm of the cross-diagonal image** (mmd 04.8 L176: `‖χ₁−aη₁‖² = 1+a²`).  For `η = η₁ ∈ Y`
and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`:
`⟨(χ₁−aη₁)^τ, (χ₁−aη₁)^τ⟩ = 1 + a²`.

By the Dade isometry on the supported singleton `{χ₁−aη₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`) this equals the source norm
`⟨χ₁−aη₁, χ₁−aη₁⟩`, which expands by `χ₁`/`η₁`-orthonormality (`⟨χ₁,χ₁⟩ = ⟨η₁,η₁⟩ = 1`) and `X ⊥ Y`
(`⟨χ₁,η₁⟩ = ⟨η₁,χ₁⟩ = 0`) to `1 + a²`.  This is the LHS of Peterfalvi's norm identity
`1+a² = ‖X‖² + (b−a)² + (m−1)b²` for the `b = 0` step. -/
theorem inner_self_tau_scaledDiff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (χ₁ - a • η)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- orthonormality / orthogonality scalars.
  have hχ₁n : ClassFunction.inner χ₁ χ₁ = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηn : ClassFunction.inner η η = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hXY : ClassFunction.inner χ₁ η = (0 : ℂ) :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      η (Submodule.subset_span hη)
  have hYX : ClassFunction.inner η χ₁ = (0 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm χ₁ η, hXY, star_zero]
  -- supported singleton ⟹ Dade isometry.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hχ₁n, hηn,
    hXY, hYX, star_natCast]
  ring

/-- **(6.8.1) norm of the cross-diagonal image**, case (A) / c2 mirror of
`inner_self_tau_scaledDiff_of_frobenius`.  `X`-irreducibility comes from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_self_tau_scaledDiff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (χ₁ - a • η)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- orthonormality / orthogonality scalars.
  have hχ₁n : ClassFunction.inner χ₁ χ₁ = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηn : ClassFunction.inner η η = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hXY : ClassFunction.inner χ₁ η = (0 : ℂ) :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      η (Submodule.subset_span hη)
  have hYX : ClassFunction.inner η χ₁ = (0 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm χ₁ η, hXY, star_zero]
  -- supported singleton ⟹ Dade isometry.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hχ₁n, hηn,
    hXY, hYX, star_natCast]
  ring

/-- **(6.8.1) the degree ratio `a` satisfies `a ≥ 2`** (mmd 04.8 L176: "Since `X ∩ Y = ∅`, `a > 1`").
For an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, the ratio `a ≥ 2`.

If `a ≤ 1` then (as `χ₁` is a positive-degree irreducible, `a ≥ 1`, so) `a = 1`, hence the source
`θ` (with `χ₁ = Ind_H^L θ`, `θ ≠ 1`, `χ₁(1) = |W₁|·θ(1)`) has degree `θ(1) = a = 1`, so `θ` is a
nontrivial **linear** character (`exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`); then
`χ₁ = Ind_H^L θ ∈ Y = S(H')` (`mem_Yset_iff_exists_linear_source`), contradicting `χ₁ ∈ X` and the
disjointness `X(Zc) ∩ Y = ∅`.  This is the `2 ≤ a` input of `eq_zero_or_edge_of_dvd_of_normBound`. -/
theorem two_le_degreeRatio_of_mem_Xset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) : 2 ≤ a := by
  classical
  -- extract the source `θ` of `χ₁ ∈ S`.
  have hχ₁S : χ₁ ∈ hyp.S := hyp.Xset_subset_S hχ₁
  rw [hyp.S_eq] at hχ₁S
  obtain ⟨θ, hθne, hχ₁eq⟩ := hχ₁S
  -- `χ₁(1) = |W₁|·θ(1)`.
  have hdeg : χ₁ 1 = (Nat.card hyp.W1 : ℂ) * (θ : ClassFunction ↥H ℂ) 1 := by
    rw [hχ₁eq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      hyp.index_H_eq_card_W1]
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- `(a : ℂ) = θ(1)`.
  have haθ : (a : ℂ) = (θ : ClassFunction ↥H ℂ) 1 := by
    have h : (a : ℂ) * (Nat.card hyp.W1 : ℂ)
        = (θ : ClassFunction ↥H ℂ) 1 * (Nat.card hyp.W1 : ℂ) := by rw [← ha, hdeg]; ring
    exact mul_right_cancel₀ hW1ne h
  -- `θ(1) = d > 0`, so `a = d ≥ 1`.
  obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have had : a = d := by have := haθ.trans hd_eq; exact_mod_cast this
  by_contra hlt
  push Not at hlt
  -- `a ≤ 1` with `a = d ≥ 1` ⟹ `a = 1` ⟹ `θ(1) = 1`.
  have ha1 : a = 1 := by omega
  have hθ1 : (θ : ClassFunction ↥H ℂ) 1 = 1 := by rw [← haθ, ha1]; norm_num
  -- `θ` is a nontrivial linear character ⟹ `χ₁ ∈ Y`, contradicting `χ₁ ∈ X`.
  obtain ⟨ψ, hψeq⟩ := θ.2.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hθ1
  have hlinθ : OddOrder.RepresentationTheory.linearIrreducibleCharacter ψ = θ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.ext hψeq
  have hψne : ψ ≠ 1 := by
    intro hψ1
    apply hθne
    rw [← hlinθ, hψ1]
    exact OddOrder.RepresentationTheory.linearIrreducibleCharacter_eq_trivial_iff.mpr rfl
  have hχ₁Y : χ₁ ∈ hyp.Yset := by
    rw [hyp.mem_Yset_iff_exists_linear_source]
    exact ⟨ψ, hψne, by rw [hχ₁eq, hψeq]⟩
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact absurd hχ₁Y (Set.disjoint_left.mp hdisj hχ₁)

open scoped Classical in
/-- **(6.8.1) step-4 dichotomy** (mmd 04.8 L176, "`b ≡ c ≡ 0 (mod a)` ⟹ `b = 0` or the `m=2`
edge").  For `η₁ ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, the
`η₁^{τ₁}`-coefficient `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩` (Peterfalvi's `b − a`) is either `−a` (the `b = 0`
case) or `0` with
`|Y| = 2` (the `b = a ∧ m = 2` edge case).

Bessel's inequality (`sum_sq_le_inner_self_re`) over the orthonormal `Y^{τ₁}`-family with
`v = (χ₁−aη₁)^τ`: the coefficient is `bb = ⟨v,η₁^{τ₁}⟩` (`= b−a`, `a ∣ bb`, step 3) on `η₁^{τ₁}`
and `bb + a` on the other `m−1` members (the constancy
`inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`); their squares sum to
`bb² + (m−1)(bb+a)² ≤ ‖v‖² = 1 + a²` (norm `inner_self_tau_scaledDiff_of_frobenius`).  With
`a ∣ (bb+a)`, `2 ≤ a` (`two_le_degreeRatio_of_mem_Xset_of_frobenius`), `2 ≤ m`
(`two_le_Yset_ncard`), `eq_zero_or_edge_of_dvd_of_normBound` gives
`bb+a = 0 ∨ (bb+a = a ∧ m = 2)`. -/
theorem coeff_eq_neg_or_edge_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  classical
  -- step 3: `bb = ⟨v, η₁^{τ₁}⟩ ∈ ℤ`, `a ∣ bb`.
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha
  -- `Y`-orthonormality and injectivity of the extension on `Y`.
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
    have h1 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1] at h0; exact one_ne_zero h0
  -- coefficient values `⟨v, η^{τ₁}⟩`.
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hsuppd : (η - η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
        hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
          ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
      have htaud : hyp.tau (η - η₁)
          = hyp.coherentYset.extension η - hyp.coherentYset.extension η₁ := by
        rw [← hyp.coherentYset.extends_on_supported (η - η₁)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
          map_sub]
      have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη hee hχ₁ ha
      rw [htaud, ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  -- the orthonormal `Y^{τ₁}`-image Finset.
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
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  -- Bessel + norm ⟹ the integer norm inequality.
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (χ₁ - a • η₁)) hβval
  have hnorm_re : (ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₁ - a • η₁))).re
      = ((1 + a ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_scaledDiff_of_frobenius hF hη₁ hχ₁ ha,
      show (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + a ^ 2 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + a) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hc : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  -- the integer inequality and `eq_zero_or_edge`.
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 ≤ 1 + (a : ℤ) ^ 2 := by
    exact_mod_cast hbessel
  have ha2 : (2 : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hnorm_lemma : ((bb + a) - (a : ℤ)) ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2
      ≤ 1 + (a : ℤ) ^ 2 := by
    rw [show (bb + (a : ℤ)) - (a : ℤ) = bb by ring]; exact hnorm_ineq
  have hdich := eq_zero_or_edge_of_dvd_of_normBound ha2 hm2 (dvd_add habb (dvd_refl _)) hnorm_lemma
  -- translate `bb+a = 0 ∨ (bb+a = a ∧ m = 2)` to the coefficient dichotomy.
  rcases hdich with h | ⟨h1, h2⟩
  · left
    rw [hbb]
    have : bb = -(a : ℤ) := by omega
    rw [this]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have : bb = 0 := by omega
    rw [this]; norm_num

open scoped Classical in
/-- **(6.8.1) step-4 dichotomy**, case (A) / c2 mirror of `coeff_eq_neg_or_edge_of_frobenius`.
The divisibility/constancy/norm inputs use their case-(A) counterparts
(`dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA`, `inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`,
`inner_self_tau_scaledDiff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem coeff_eq_neg_or_edge_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  classical
  -- step 3: `bb = ⟨v, η₁^{τ₁}⟩ ∈ ℤ`, `a ∣ bb`.
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha
  -- `Y`-orthonormality and injectivity of the extension on `Y`.
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
    have h1 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1] at h0; exact one_ne_zero h0
  -- coefficient values `⟨v, η^{τ₁}⟩`.
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hsuppd : (η - η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
        hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
          ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
      have htaud : hyp.tau (η - η₁)
          = hyp.coherentYset.extension η - hyp.coherentYset.extension η₁ := by
        rw [← hyp.coherentYset.extends_on_supported (η - η₁)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
          map_sub]
      have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη hee hχ₁ ha
      rw [htaud, ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  -- the orthonormal `Y^{τ₁}`-image Finset.
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
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  -- Bessel + norm ⟹ the integer norm inequality.
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (χ₁ - a • η₁)) hβval
  have hnorm_re : (ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₁ - a • η₁))).re
      = ((1 + a ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ ha,
      show (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + a ^ 2 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + a) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hc : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  -- the integer inequality and `eq_zero_or_edge`.
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 ≤ 1 + (a : ℤ) ^ 2 := by
    exact_mod_cast hbessel
  have ha2 : (2 : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hnorm_lemma : ((bb + a) - (a : ℤ)) ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2
      ≤ 1 + (a : ℤ) ^ 2 := by
    rw [show (bb + (a : ℤ)) - (a : ℤ) = bb by ring]; exact hnorm_ineq
  have hdich := eq_zero_or_edge_of_dvd_of_normBound ha2 hm2 (dvd_add habb (dvd_refl _)) hnorm_lemma
  -- translate `bb+a = 0 ∨ (bb+a = a ∧ m = 2)` to the coefficient dichotomy.
  rcases hdich with h | ⟨h1, h2⟩
  · left
    rw [hbb]
    have : bb = -(a : ℤ) := by omega
    rw [this]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have : bb = 0 := by omega
    rw [this]; norm_num

open scoped Classical in
/-- **(6.8.1) step-4 good-case `X`-structure** (mmd 04.8 L176: "`b = 0` ⟹
`(χ₁ − aη₁)^τ = X − aη₁^{τ₁}`, `‖X‖² = ‖χ₁‖² = 1`").  In the good case
`⟨(χ₁ − aη₁)^τ, η₁^{τ₁}⟩ = −a` (the `b = 0` branch of `coeff_eq_neg_or_edge_of_frobenius`), the
element `X := (χ₁ − aη₁)^τ + a·η₁^{τ₁}` is orthogonal to the whole coherent `Y`-image family
`Y^{τ₁}`, has norm `1`, and lies in `ℤ[Irr G]`.  Step 5 then identifies `X = χ₁^{τ₂}`, giving the
crux `(χ₁ − aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`.

The orthogonality uses the constancy `inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`
(`⟨v, (η − η₁)^τ⟩ = a`, so `⟨v, η^{τ₁}⟩ = ⟨v, η₁^{τ₁}⟩ + a = 0` for `η ≠ η₁`) and the norm
`‖v‖² = 1 + a²` (`inner_self_tau_scaledDiff_of_frobenius`); the norm of `X` is
`(1 + a²) − a² − a² + a² = 1`. -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- Y-image orthonormality: `⟨η^{τ₁}, η'^{τ₁}⟩ = ⟨η, η'⟩ = δ`.
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη)
      (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  -- `⟨v, η^{τ₁}⟩ = 0` for `η ≠ η₁` (constancy `⟨v, (η−η₁)^τ⟩ = a` plus `⟨v, η₁^{τ₁}⟩ = −a`).
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner v (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη hne hχ₁ ha
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁)
        = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  -- norm and the conjugate of the good-case coefficient.
  have hvv : ClassFunction.inner v v = 1 + (a : ℂ) ^ 2 :=
    hyp.inner_self_tau_scaledDiff_of_frobenius hF hη₁ hχ₁ ha
  have he₁e₁ : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  have he₁v : ClassFunction.inner (cY.extension η₁) v = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm v (cY.extension η₁), hgood]
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- orthogonality `⟨X, η^{τ₁}⟩ = 0`.
    intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee
      rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (fun h => hee h.symm)]; ring
  · -- norm `⟨X, X⟩ = 1`.
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    rw [hvv, hgood, he₁v, he₁e₁, star_natCast]; ring
  · -- `X ∈ ℤ[Irr G]`.
    have hdeg : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
    have hsuppX : (χ₁ - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁)
        (hyp.Yset_subset_S hη₁) hdeg
    have hsrcZ : χ₁ - a • η₁ ∈ ZIrr (↥L) :=
      sub_mem (hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁).mem_ZIrr
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr a)
    have hvZ : v ∈ ZIrr G := by
      rw [hv]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hyp.hconj hsuppX hsrcZ
    have he₁Z : cY.extension η₁ ∈ ZIrr G :=
      cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)
    have haZ : (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem he₁Z a
    exact add_mem hvZ haZ

open scoped Classical in
/-- **(6.8.1) step-4 good-case `X`-structure**, case (A) / c2 mirror of
`orthogonal_normOne_tau_scaledDiff_add_extension_general`.  The constancy/norm/`X`-irreducibility
inputs use their case-(A) counterparts (`inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`,
`inner_self_tau_scaledDiff_c2_caseA`, `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF`
(cert data `hK`/`hW1`/`hA`). -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- Y-image orthonormality: `⟨η^{τ₁}, η'^{τ₁}⟩ = ⟨η, η'⟩ = δ`.
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη)
      (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  -- `⟨v, η^{τ₁}⟩ = 0` for `η ≠ η₁` (constancy `⟨v, (η−η₁)^τ⟩ = a` plus `⟨v, η₁^{τ₁}⟩ = −a`).
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner v (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη hne hχ₁ ha
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁)
        = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  -- norm and the conjugate of the good-case coefficient.
  have hvv : ClassFunction.inner v v = 1 + (a : ℂ) ^ 2 :=
    hyp.inner_self_tau_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ ha
  have he₁e₁ : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  have he₁v : ClassFunction.inner (cY.extension η₁) v = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm v (cY.extension η₁), hgood]
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- orthogonality `⟨X, η^{τ₁}⟩ = 0`.
    intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee
      rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (fun h => hee h.symm)]; ring
  · -- norm `⟨X, X⟩ = 1`.
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    rw [hvv, hgood, he₁v, he₁e₁, star_natCast]; ring
  · -- `X ∈ ℤ[Irr G]`.
    have hdeg : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
    have hsuppX : (χ₁ - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁)
        (hyp.Yset_subset_S hη₁) hdeg
    have hsrcZ : χ₁ - a • η₁ ∈ ZIrr (↥L) :=
      sub_mem (hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁).mem_ZIrr
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr a)
    have hvZ : v ∈ ZIrr G := by
      rw [hv]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hyp.hconj hsuppX hsrcZ
    have he₁Z : cY.extension η₁ ∈ ZIrr G :=
      cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)
    have haZ : (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem he₁Z a
    exact add_mem hvZ haZ

/-- **(6.8.1) step-4 good-case `X`-structure** at the fixed witness `τ₁ = coherentYset`
(specialization of `orthogonal_normOne_tau_scaledDiff_add_extension_general`). -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.coherentYset.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁ ∈ ZIrr G :=
  hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general hF hyp.coherentYset hη₁ hχ₁ ha hgood

/-- **(6.8.1) step-4 good-case `X`-structure** at the fixed witness, case (A) / c2 mirror of
`orthogonal_normOne_tau_scaledDiff_add_extension_of_frobenius` (specialization of
`orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA`). -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.coherentYset.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁ ∈ ZIrr G :=
  hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA hK hW1 hA hyp.coherentYset
    hη₁ hχ₁ ha hgood

/-- **(6.8.1) `X`-difference isometry** (mmd 04.8 L176, the step-5 input).  For `η₁ ∈ Y`, an
`X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, and a second `X`-member `χ₂ ∈ X(Zc)`, `χ₂ ≠ χ₁`, of
the **same degree** `χ₂(1) = χ₁(1)`:
`⟨(χ₁−aη₁)^τ, (χ₂−χ₁)^τ⟩ = −1`.

By the Dade isometry on the supported pair `{χ₁−aη₁, χ₂−χ₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; `χ₂−χ₁` supported by
`sMember_diffSupport_of_charValue_eq` at the common degree), the inner product equals the source
`⟨χ₁−aη₁, χ₂−χ₁⟩`, which expands by `X`-orthonormality (`⟨χ₁,χ₂⟩=0`, `⟨χ₁,χ₁⟩=1`) and `X ⊥ Y`
(`⟨η₁,χ₂⟩=⟨η₁,χ₁⟩=0`) to `(0 − a·0) − (1 − a·0) = −1`.  Combined with `himg_ortho`
(`η₁^{τ₁} ⊥ X^{τ₂}`) and the `X`-coherence `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}`, this gives
`⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1` for the step-5 element `X` (good case), pinning `X = χ₁^{τ₂}`. -/
theorem inner_tau_scaledDiff_tau_Xset_diff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₂ - χ₁)) = -1 := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported inputs.
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX2 : (χ₂ - χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₂ - χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX2)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- source orthogonality `⟨χ₁ − a•η₁, χ₂ − χ₁⟩ = −1`.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXon χ₁ χ₂ hχ₁ hχ₂, hXon χ₁ χ₁ hχ₁ hχ₁, hYXz χ₂ hχ₂, hYXz χ₁ hχ₁,
    if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) `X`-difference isometry**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius`.  `X`-irreducibility comes from the certain-type
input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Xset_diff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₂ - χ₁)) = -1 := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported inputs.
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX2 : (χ₂ - χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₂ - χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX2)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- source orthogonality `⟨χ₁ − a•η₁, χ₂ − χ₁⟩ = −1`.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXon χ₁ χ₂ hχ₁ hχ₂, hXon χ₁ χ₁ hχ₁ hχ₁, hYXz χ₂ hχ₂, hYXz χ₁ hχ₁,
    if_neg (Ne.symm hne), if_pos rfl]
  ring

open scoped Classical in
/-- **(6.8.1) step-5 inner-product relation** (mmd 04.8 L176).  For the good-case element
`X := (χ₁−aη₁)^τ + a·η₁^{τ₁}`, the `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, and a second
equal-degree `X`-member `χ₂ ∈ X(Zc)`, `χ₂ ≠ χ₁`:
`⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1`.

`X = (χ₁−aη₁)^τ + a·η₁^{τ₁}` and `η₁^{τ₁} ⊥ X^{τ₂}` (himg_ortho
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`) give
`⟨X, χ_j^{τ₂}⟩ = ⟨(χ₁−aη₁)^τ, χ_j^{τ₂}⟩`; the `X`-coherence
`(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (`extends_on_supported` on the supported equal-degree difference)
and the isometry value `⟨(χ₁−aη₁)^τ, (χ₂−χ₁)^τ⟩ = −1`
(`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius`) close it.  Together with `‖X‖² = 1` and Bessel
over the orthonormal `{χ₁^{τ₂}, χ₂^{τ₂}}`, this pins `X = χ₁^{τ₂}` (or `−χ₂^{τ₂}`, the `n = 2`
edge). -/
theorem inner_extension_Xset_sub_eq_neg_one_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁)
      = -1 := by
  classical
  set hXc := cX with hXc_def
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- `⟨X, χ_j^{τ₂}⟩ = ⟨v, χ_j^{τ₂}⟩` (himg_ortho `η₁^{τ₁} ⊥ X^{τ₂}`).
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (hXc.extension χ)
        = ClassFunction.inner v (hXc.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hχ hη₁
    rw [← hXc_def] at h
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  -- `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (X-coherence `extends_on_supported`).
  have hsuppX2 : (χ₂ - χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hXcoh : hyp.tau (χ₂ - χ₁) = hXc.extension χ₂ - hXc.extension χ₁ := by
    have h := hXc.extends_on_supported (χ₂ - χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₂) (Submodule.subset_span hχ₁), hsuppX2⟩
    rw [map_sub] at h
    exact h.symm
  -- isometry value `⟨v, (χ₂−χ₁)^τ⟩ = −1`.
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_diff_of_frobenius hF hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [hXcoh, ClassFunction.inner_sub_right] at hiso
  rw [hXv χ₂ hχ₂, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) step-5 inner-product relation**, case (A) / c2 mirror of
`inner_extension_Xset_sub_eq_neg_one_general`.  The himg_ortho/isometry inputs use their case-(A)
counterparts (`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`,
`inner_tau_scaledDiff_tau_Xset_diff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_sub_eq_neg_one_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁)
      = -1 := by
  classical
  set hXc := cX with hXc_def
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- `⟨X, χ_j^{τ₂}⟩ = ⟨v, χ_j^{τ₂}⟩` (himg_ortho `η₁^{τ₁} ⊥ X^{τ₂}`).
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (hXc.extension χ)
        = ClassFunction.inner v (hXc.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
      hK hW1 hA cX cY hχ hη₁
    rw [← hXc_def] at h
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  -- `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (X-coherence `extends_on_supported`).
  have hsuppX2 : (χ₂ - χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hXcoh : hyp.tau (χ₂ - χ₁) = hXc.extension χ₂ - hXc.extension χ₁ := by
    have h := hXc.extends_on_supported (χ₂ - χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₂) (Submodule.subset_span hχ₁), hsuppX2⟩
    rw [map_sub] at h
    exact h.symm
  -- isometry value `⟨v, (χ₂−χ₁)^τ⟩ = −1`.
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_diff_c2_caseA hK hW1 hA hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [hXcoh, ClassFunction.inner_sub_right] at hiso
  rw [hXv χ₂ hχ₂, hXv χ₁ hχ₁]
  exact hiso

/-- **(6.8.1) step-5 relation** at the fixed witnesses (specialization of
`inner_extension_Xset_sub_eq_neg_one_general`). -/
theorem inner_extension_Xset_sub_eq_neg_one_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁)
      = -1 :=
  hyp.inner_extension_Xset_sub_eq_neg_one_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2

/-- **(6.8.1) step-5 relation** at the fixed witnesses, case (A) / c2 mirror of
`inner_extension_Xset_sub_eq_neg_one_of_frobenius` (the `X`-coherence is
`Xset_centralCommutator_isCoherent_of_c2_caseA`; cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_sub_eq_neg_one_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₁)
      = -1 :=
  hyp.inner_extension_Xset_sub_eq_neg_one_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2

open scoped Classical in
/-- **(6.8.1) step-5 dichotomy `X = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`** (mmd 04.8 L176).  In the good case
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = −a`, the element `X := (χ₁−aη₁)^τ + a·η₁^{τ₁}` (norm `1`, `⊥ Y^{τ₁}`)
equals either `χ₁^{τ₂}` or `−χ₂^{τ₂}` for the second equal-degree anchor `χ₂`.

From the step-5 relation `⟨X,χ₂^{τ₂}⟩ − ⟨X,χ₁^{τ₂}⟩ = −1` (`inner_extension_Xset_sub_eq_neg_one`)
and Bessel `c₁² + c₂² ≤ ‖X‖² = 1` (`sum_sq_le_inner_self_re` over the orthonormal
`{χ₁^{τ₂},χ₂^{τ₂}}`, `c_j = ⟨X,χ_j^{τ₂}⟩ ∈ ℤ`), the integers satisfy `c₂−c₁=−1`, `c₁²+c₂²≤1`,
forcing `(1,0)` or `(0,−1)`; `⟨X,χ₁^{τ₂}⟩=1` (resp. `⟨X,−χ₂^{τ₂}⟩=1`) with both norm `1` gives
`X=χ₁^{τ₂}` (resp. `X=−χ₂^{τ₂}`) by positive-definiteness.  The `n=2` edge `X=−χ₂^{τ₂}` is
resolved by relabelling (deferred); for `n≥3` a third anchor pins `X=χ₁^{τ₂}`. -/
theorem extension_eq_or_eq_neg_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = cX.extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = -cX.extension χ₂
      := by
  classical
  set hXc := cX with hXc_def
  set X := hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ with hX_def
  -- good-case structure: `‖X‖² = 1`, `X ∈ ZIrr` (fold the unfolded `X` from the good-case lemma).
  obtain ⟨_, hXnorm, hXZ⟩ := hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general
    hF cY hη₁ hχ₁ ha hgood
  rw [← hX_def] at hXnorm hXZ
  -- `X`-image orthonormality, ZIrr membership, distinctness.
  have hX1Z : hXc.extension χ₁ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₁ (Submodule.subset_span hχ₁)
  have hX2Z : hXc.extension χ₂ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₂ (Submodule.subset_span hχ₂)
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hX1norm : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₁) = 1 := by
    rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have hX2norm : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₂) = 1 := by
    rw [hXon χ₂ χ₂ hχ₂ hχ₂, if_pos rfl]
  have hX12 : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₂) = 0 := by
    rw [hXon χ₁ χ₂ hχ₁ hχ₂, if_neg (Ne.symm hne)]
  have hX1ne2 : hXc.extension χ₁ ≠ hXc.extension χ₂ := by
    intro heq; rw [heq, hX2norm] at hX12; exact one_ne_zero hX12
  -- integer coefficients `c₁ = ⟨X,χ₁^{τ₂}⟩`, `c₂ = ⟨X,χ₂^{τ₂}⟩`.
  obtain ⟨c₁, hc₁⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX1Z
  obtain ⟨c₂, hc₂⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX2Z
  -- the step-5 relation `c₂ − c₁ = −1`.
  have hrel := hyp.inner_extension_Xset_sub_eq_neg_one_general hF cX cY
    hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [← hXc_def, ← hX_def, hc₁, hc₂] at hrel
  have hrelℤ : c₂ - c₁ = -1 := by exact_mod_cast hrel
  -- Bessel `c₁² + c₂² ≤ ‖X‖² = 1` via positive-definiteness of the projection residual
  -- `X − c₁·χ₁^{τ₂} − c₂·χ₂^{τ₂}`.
  have hAX : ClassFunction.inner (hXc.extension χ₁) X = (c₁ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₁), hc₁, star_intCast]
  have hBX : ClassFunction.inner (hXc.extension χ₂) X = (c₂ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₂), hc₂, star_intCast]
  have hX21 : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₁) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ₁) (hXc.extension χ₂), hX12,
      star_zero]
  have hww : ClassFunction.inner
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      = ((1 - (c₁ ^ 2 + c₂ ^ 2) : ℤ) : ℂ) := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hXnorm, hc₁, hc₂, hAX, hBX, hX1norm, hX2norm, hX12, hX21, star_intCast]
    push_cast; ring
  have hbℤ : c₁ ^ 2 + c₂ ^ 2 ≤ 1 := by
    have hnn := OddOrder.RepresentationTheory.inner_self_re_nonneg
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
    rw [hww, Complex.intCast_re] at hnn
    have hb : (0 : ℤ) ≤ 1 - (c₁ ^ 2 + c₂ ^ 2) := by exact_mod_cast hnn
    linarith
  -- positive-definiteness: `⟨w₁,w₁⟩=⟨w₂,w₂⟩=⟨w₁,w₂⟩=1 ⟹ w₁=w₂`.
  have heq : ∀ w₁ w₂ : ClassFunction G ℂ, ClassFunction.inner w₁ w₁ = 1 →
      ClassFunction.inner w₂ w₂ = 1 → ClassFunction.inner w₁ w₂ = 1 → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ h₁₂
    have hsub : ClassFunction.inner (w₁ - w₂) (w₁ - w₂) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h₁, h₂, h₁₂,
        OddOrder.RepresentationTheory.inner_conj_symm w₁ w₂, h₁₂, star_one]
      ring
    have hz : w₁ - w₂ = 0 := OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
      (by rw [hsub, Complex.zero_re])
    exact sub_eq_zero.mp hz
  -- the integer dichotomy `(c₁,c₂) = (1,0) ∨ (0,−1)` from `c₂ = c₁−1` and `c₁²+c₂² ≤ 1`.
  have hc2eq : c₂ = c₁ - 1 := by omega
  rw [hc2eq] at hbℤ
  obtain ⟨hb0, hb1⟩ : 0 ≤ c₁ ∧ c₁ ≤ 1 := by
    constructor <;> nlinarith [hbℤ, sq_nonneg c₁, sq_nonneg (c₁ - 1)]
  interval_cases c₁
  · -- `c₁ = 0`, `c₂ = −1` ⟹ `X = −χ₂^{τ₂}`.
    right
    have hc₂m : c₂ = -1 := by omega
    subst hc₂m
    refine heq X (-hXc.extension χ₂) hXnorm ?_ ?_
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hX2norm]; ring
    · rw [ClassFunction.inner_neg_right, hc₂]; norm_num
  · -- `c₁ = 1`, `c₂ = 0` ⟹ `X = χ₁^{τ₂}`.
    left
    refine heq X (hXc.extension χ₁) hXnorm hX1norm ?_
    rw [hc₁]; norm_num

open scoped Classical in
/-- **(6.8.1) step-5 dichotomy `X = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`**, case (A) / c2 mirror of
`extension_eq_or_eq_neg_general`.  The good-case structure/relation/`X`-irreducibility inputs use
their case-(A) counterparts (`orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA`,
`inner_extension_Xset_sub_eq_neg_one_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem extension_eq_or_eq_neg_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = cX.extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = -cX.extension χ₂
      := by
  classical
  set hXc := cX with hXc_def
  set X := hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ with hX_def
  -- good-case structure: `‖X‖² = 1`, `X ∈ ZIrr` (fold the unfolded `X` from the good-case lemma).
  obtain ⟨_, hXnorm, hXZ⟩ := hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA
    hK hW1 hA cY hη₁ hχ₁ ha hgood
  rw [← hX_def] at hXnorm hXZ
  -- `X`-image orthonormality, ZIrr membership, distinctness.
  have hX1Z : hXc.extension χ₁ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₁ (Submodule.subset_span hχ₁)
  have hX2Z : hXc.extension χ₂ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₂ (Submodule.subset_span hχ₂)
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hX1norm : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₁) = 1 := by
    rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have hX2norm : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₂) = 1 := by
    rw [hXon χ₂ χ₂ hχ₂ hχ₂, if_pos rfl]
  have hX12 : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₂) = 0 := by
    rw [hXon χ₁ χ₂ hχ₁ hχ₂, if_neg (Ne.symm hne)]
  have hX1ne2 : hXc.extension χ₁ ≠ hXc.extension χ₂ := by
    intro heq; rw [heq, hX2norm] at hX12; exact one_ne_zero hX12
  -- integer coefficients `c₁ = ⟨X,χ₁^{τ₂}⟩`, `c₂ = ⟨X,χ₂^{τ₂}⟩`.
  obtain ⟨c₁, hc₁⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX1Z
  obtain ⟨c₂, hc₂⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX2Z
  -- the step-5 relation `c₂ − c₁ = −1`.
  have hrel := hyp.inner_extension_Xset_sub_eq_neg_one_general_c2_caseA hK hW1 hA cX cY
    hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [← hXc_def, ← hX_def, hc₁, hc₂] at hrel
  have hrelℤ : c₂ - c₁ = -1 := by exact_mod_cast hrel
  -- Bessel `c₁² + c₂² ≤ ‖X‖² = 1` via positive-definiteness of the projection residual
  -- `X − c₁·χ₁^{τ₂} − c₂·χ₂^{τ₂}`.
  have hAX : ClassFunction.inner (hXc.extension χ₁) X = (c₁ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₁), hc₁, star_intCast]
  have hBX : ClassFunction.inner (hXc.extension χ₂) X = (c₂ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₂), hc₂, star_intCast]
  have hX21 : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₁) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ₁) (hXc.extension χ₂), hX12,
      star_zero]
  have hww : ClassFunction.inner
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      = ((1 - (c₁ ^ 2 + c₂ ^ 2) : ℤ) : ℂ) := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hXnorm, hc₁, hc₂, hAX, hBX, hX1norm, hX2norm, hX12, hX21, star_intCast]
    push_cast; ring
  have hbℤ : c₁ ^ 2 + c₂ ^ 2 ≤ 1 := by
    have hnn := OddOrder.RepresentationTheory.inner_self_re_nonneg
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
    rw [hww, Complex.intCast_re] at hnn
    have hb : (0 : ℤ) ≤ 1 - (c₁ ^ 2 + c₂ ^ 2) := by exact_mod_cast hnn
    linarith
  -- positive-definiteness: `⟨w₁,w₁⟩=⟨w₂,w₂⟩=⟨w₁,w₂⟩=1 ⟹ w₁=w₂`.
  have heq : ∀ w₁ w₂ : ClassFunction G ℂ, ClassFunction.inner w₁ w₁ = 1 →
      ClassFunction.inner w₂ w₂ = 1 → ClassFunction.inner w₁ w₂ = 1 → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ h₁₂
    have hsub : ClassFunction.inner (w₁ - w₂) (w₁ - w₂) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h₁, h₂, h₁₂,
        OddOrder.RepresentationTheory.inner_conj_symm w₁ w₂, h₁₂, star_one]
      ring
    have hz : w₁ - w₂ = 0 := OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
      (by rw [hsub, Complex.zero_re])
    exact sub_eq_zero.mp hz
  -- the integer dichotomy `(c₁,c₂) = (1,0) ∨ (0,−1)` from `c₂ = c₁−1` and `c₁²+c₂² ≤ 1`.
  have hc2eq : c₂ = c₁ - 1 := by omega
  rw [hc2eq] at hbℤ
  obtain ⟨hb0, hb1⟩ : 0 ≤ c₁ ∧ c₁ ≤ 1 := by
    constructor <;> nlinarith [hbℤ, sq_nonneg c₁, sq_nonneg (c₁ - 1)]
  interval_cases c₁
  · -- `c₁ = 0`, `c₂ = −1` ⟹ `X = −χ₂^{τ₂}`.
    right
    have hc₂m : c₂ = -1 := by omega
    subst hc₂m
    refine heq X (-hXc.extension χ₂) hXnorm ?_ ?_
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hX2norm]; ring
    · rw [ClassFunction.inner_neg_right, hc₂]; norm_num
  · -- `c₁ = 1`, `c₂ = 0` ⟹ `X = χ₁^{τ₂}`.
    left
    refine heq X (hXc.extension χ₁) hXnorm hX1norm ?_
    rw [hc₁]; norm_num

/-- **(6.8.1) step-5 dichotomy** at the fixed witnesses (specialization of
`extension_eq_or_eq_neg_general`). -/
theorem extension_eq_or_eq_neg_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = -(hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₂ :=
  hyp.extension_eq_or_eq_neg_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2 hgood

/-- **(6.8.1) step-5 dichotomy** at the fixed witnesses, case (A) / c2 mirror of
`extension_eq_or_eq_neg_of_frobenius` (the `X`-coherence is
`Xset_centralCommutator_isCoherent_of_c2_caseA`; cert data `hK`/`hW1`/`hA`). -/
theorem extension_eq_or_eq_neg_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = -(hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₂ :=
  hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2 hgood

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (`n ≥ 3` case)** (mmd 04.8 L176).  Given a third equal-degree `X`-anchor
`χ₃` (distinct from `χ₁, χ₂`), the good-case crux holds:
`(χ₁−aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`.

The step-5 dichotomy gives `X := (χ₁−aη₁)^τ + a·η₁^{τ₁} = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`; the second
disjunct is excluded by the step-5 relation for `χ₃` (`⟨X,χ₃^{τ₂}⟩ − ⟨X,χ₁^{τ₂}⟩ = −1`,
`inner_extension_Xset_sub_eq_neg_one`): under `X = −χ₂^{τ₂}` both `⟨χ₂^{τ₂},χ₃^{τ₂}⟩` and
`⟨χ₂^{τ₂},χ₁^{τ₂}⟩` vanish (distinct `X`-images), giving `0 = −1`.  Hence `X = χ₁^{τ₂}`, i.e. the
crux.  (The `n = 2` case — no third anchor — needs the relabel of `χ₁^{τ₂}, χ₂^{τ₂}`, deferred.) -/
theorem crux_of_third_anchor_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set hXc := cX with hXc_def
  -- `X`-image orthonormality.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general hF cX cY hη₁ hχ₁ hχ₂ hne₂ ha hdeg2
    hgood with h | h
  · -- left disjunct `X = χ₁^{τ₂}` ⟹ the crux by `eq_sub_of_add_eq`.
    rw [← hXc_def] at h
    exact eq_sub_of_add_eq h
  · -- right disjunct `X = −χ₂^{τ₂}` is excluded by the `χ₃` relation.
    exfalso
    rw [← hXc_def] at h
    have hrel3 := hyp.inner_extension_Xset_sub_eq_neg_one_general hF cX cY
      hη₁ hχ₁ hχ₃ hne₃₁ ha hdeg3
    rw [← hXc_def, h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁, if_neg hne₂] at hrel3
    norm_num at hrel3

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (`n ≥ 3` case)**, case (A) / c2 mirror of `crux_of_third_anchor_general`.
The dichotomy/relation/`X`-irreducibility inputs use their case-(A) counterparts
(`extension_eq_or_eq_neg_general_c2_caseA`, `inner_extension_Xset_sub_eq_neg_one_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem crux_of_third_anchor_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set hXc := cX with hXc_def
  -- `X`-image orthonormality.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁ hχ₁ hχ₂ hne₂ ha hdeg2
    hgood with h | h
  · -- left disjunct `X = χ₁^{τ₂}` ⟹ the crux by `eq_sub_of_add_eq`.
    rw [← hXc_def] at h
    exact eq_sub_of_add_eq h
  · -- right disjunct `X = −χ₂^{τ₂}` is excluded by the `χ₃` relation.
    exfalso
    rw [← hXc_def] at h
    have hrel3 := hyp.inner_extension_Xset_sub_eq_neg_one_general_c2_caseA hK hW1 hA cX cY
      hη₁ hχ₁ hχ₃ hne₃₁ ha hdeg3
    rw [← hXc_def, h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁, if_neg hne₂] at hrel3
    norm_num at hrel3

/-- **(6.8.1) crux (`n ≥ 3` case)** at the fixed witnesses (specialization of
`crux_of_third_anchor_general`). -/
theorem crux_of_third_anchor_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hgood

/-- **(6.8.1) crux (`n ≥ 3` case)** at the fixed witnesses, case (A) / c2 mirror of
`crux_of_third_anchor_of_frobenius` (the `X`-coherence is
`Xset_centralCommutator_isCoherent_of_c2_caseA`; cert data `hK`/`hW1`/`hA`). -/
theorem crux_of_third_anchor_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hgood

open scoped Classical in
/-- For `m = |Y| ≥ 3` the step-4 edge case (`m = 2`) is impossible, so the good case
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = −a` of `coeff_eq_neg_or_edge_of_frobenius` holds (no relabel needed). -/
theorem inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ) := by
  have ha_pos : 0 < a := by
    have := hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha; omega
  rcases hyp.coeff_eq_neg_or_edge_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    h | ⟨hm2, _⟩
  · exact h
  · exfalso; omega

/-- case (A) / c2 mirror of `inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius`.  The step-4
dichotomy input uses `coeff_eq_neg_or_edge_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_extension_Yset_eq_neg_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ) := by
  have ha_pos : 0 < a := by
    have := hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha; omega
  rcases hyp.coeff_eq_neg_or_edge_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    h | ⟨hm2, _⟩
  · exact h
  · exfalso; omega

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (generic `m, n ≥ 3` case)** (mmd 04.8 L176).  When `|Y| ≥ 3` (so the step-4
edge `m = 2` is impossible, discharging the good case) and a third equal-degree `X`-anchor `χ₃`
exists (the `n ≥ 3` pinning), the crux `(χ₁−aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}` holds **unconditionally**
(no relabel).  This is the diagonal-shell hypothesis `hDτ` in the generic case. -/
theorem crux_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂
    ha hdeg2 hdeg3
    (hyp.inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha
      hm3)

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (generic `m, n ≥ 3` case)**, case (A) / c2 mirror of `crux_of_frobenius`.
Delegates to `crux_of_third_anchor_c2_caseA` with the good case from
`inner_tau_scaledDiff_extension_Yset_eq_neg_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem crux_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂
    ha hdeg2 hdeg3
    (hyp.inner_tau_scaledDiff_extension_Yset_eq_neg_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha
      hm3)

open scoped Classical in
/-- **(6.8.1) `hgen'` — the diagonal-aware generation hypothesis** (mmd 04.8 L176).  Every supported
`X(Zc) ∪ Y`-combination lies in the span of the supported `X(Zc)`-combinations, the supported
`Y`-combinations, and the single cross-diagonal `χ₁ − a·η₁`:
`ℤ[X(Zc) ∪ Y, A] ⊆ span(ℤ[X(Zc), A] ∪ ℤ[Y, A] ∪ {χ₁ − a·η₁})`.

For `φ = φ_X + φ_Y` (`X, Y` disjoint, `Submodule.span_union`), the degree-ratio integrality
(`exists_charValue_one_eq_mul_xBaseBlock_anchor`) gives `s ∈ ℤ` with `φ_X(1) = s·χ₁(1)` (span
induction); then `φ = (φ_X − s·χ₁) + (φ_Y + s·(a·η₁)) + s·(χ₁ − a·η₁)`, where the first two pieces
are degree-`0` (`φ(1) = 0` from support) hence supported
(`zSpan_S_support_subset_of_apply_one_eq_zero`) and the last is a multiple of the diagonal.  This is
the `hgen` field of `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` with
`D = {χ₁ − a·η₁}`. -/
theorem hgen_withDiagonal_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        {χ₁ - a • η₁}) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  -- `φ(1) = 0`: `1 ∉ A = H^#`.
  have h1 : φ 1 = 0 := by
    by_contra h
    have hmem := hφsupp (ClassFunction.mem_support.mpr h)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2 (by simp)
  -- split `φ = φ_X + φ_Y`.
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  -- the integer `s` with `φ_X(1) = s·χ₁(1)` (span induction + degree-ratio integrality).
  have hsX : ∀ ψ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator),
      ∃ s : ℤ, ψ 1 = (s : ℂ) * χ₁ 1 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d, -, hd⟩ := hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
          hp hHp (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hx hχ₁base
        exact ⟨d, by rw [hd]; push_cast; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
        exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
    | smul c x _ hx =>
        obtain ⟨sx, hsx⟩ := hx
        refine ⟨c * sx, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring
  obtain ⟨s, hφX1⟩ := hsX φX hφX
  -- `φ_Y(1) = −s·χ₁(1)`.
  have hφY1 : φY 1 = -((s : ℂ) * χ₁ 1) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 : (s • χ₁ : ClassFunction ↥L ℂ) 1 = (s : ℂ) * χ₁ 1 := by
    rw [← Int.cast_smul_eq_zsmul ℂ s χ₁, ClassFunction.smul_apply]
  have hsaη₁1 : (s • (a • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 (for the supported ones) and span-members.
  have hp1deg : (φX - s • χ₁ : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1, ha, hyp.Yset_apply_one hη₁]; ring
  have hp1span : (φX - s • χ₁) ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hχ₁X))
  have hp2span : (φY + s • (a • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a))
  -- supports via the degree-0 ⟹ supported helper.
  have hp1supp : (φX - s • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Xset_subset_S hp1span) hp1deg
  have hp2supp : (φY + s • (a • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·χ₁`, `s·(a·η₁)` terms cancel).
  have hφeq : φ = (φX - s • χ₁) + (φY + s • (a • η₁)) + s • (χ₁ - a • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

open scoped Classical in
/-- **(6.8.1) `hgen'` — the diagonal-aware generation hypothesis**, case (A) / c2 mirror of
`hgen_withDiagonal_of_frobenius`.  `X`-irreducibility comes from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem hgen_withDiagonal_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        {χ₁ - a • η₁}) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  -- `φ(1) = 0`: `1 ∉ A = H^#`.
  have h1 : φ 1 = 0 := by
    by_contra h
    have hmem := hφsupp (ClassFunction.mem_support.mpr h)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2 (by simp)
  -- split `φ = φ_X + φ_Y`.
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  -- the integer `s` with `φ_X(1) = s·χ₁(1)` (span induction + degree-ratio integrality).
  have hsX : ∀ ψ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator),
      ∃ s : ℤ, ψ 1 = (s : ℂ) * χ₁ 1 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d, -, hd⟩ := hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
          hp hHp (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hx hχ₁base
        exact ⟨d, by rw [hd]; push_cast; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
        exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
    | smul c x _ hx =>
        obtain ⟨sx, hsx⟩ := hx
        refine ⟨c * sx, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring
  obtain ⟨s, hφX1⟩ := hsX φX hφX
  -- `φ_Y(1) = −s·χ₁(1)`.
  have hφY1 : φY 1 = -((s : ℂ) * χ₁ 1) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 : (s • χ₁ : ClassFunction ↥L ℂ) 1 = (s : ℂ) * χ₁ 1 := by
    rw [← Int.cast_smul_eq_zsmul ℂ s χ₁, ClassFunction.smul_apply]
  have hsaη₁1 : (s • (a • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 (for the supported ones) and span-members.
  have hp1deg : (φX - s • χ₁ : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1, ha, hyp.Yset_apply_one hη₁]; ring
  have hp1span : (φX - s • χ₁) ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hχ₁X))
  have hp2span : (φY + s • (a • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a))
  -- supports via the degree-0 ⟹ supported helper.
  have hp1supp : (φX - s • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Xset_subset_S hp1span) hp1deg
  have hp2supp : (φY + s • (a • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·χ₁`, `s·(a·η₁)` terms cancel).
  have hφeq : φ = (φX - s • χ₁) + (φY + s • (a • η₁)) + s • (χ₁ - a • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

open scoped Classical in
/-- **(6.8.1) `X`-difference isometry, degree-ratio form** (mmd 04.8 L176: the `n ≥ 3` exclusion uses
`(χ₃ − d₃χ₁)^τ` for ANY third `X`-member `χ₃`, of any degree).  For `η₁ ∈ Y`, `χ₁ ∈ X(Zc)` with
`χ₁(1) = a·|W₁|`, and a second member `χ₃ ∈ X(Zc)`, `χ₃ ≠ χ₁`, with degree ratio `d` (`χ₃(1) =
d·χ₁(1)`):  `⟨(χ₁−aη₁)^τ, (χ₃−d·χ₁)^τ⟩ = −d`.  Generalizes
`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius` (the `d = 1` equal-degree case `= −1`); the
supported diff `χ₃ − d·χ₁` is degree-`0` (`sMember_scaledDiffSupport_of_charValue_eq`), so the Dade
isometry reduces to the source `⟨χ₁−aη₁, χ₃−d·χ₁⟩ = −d` (`X`-orthonormality + `X ⊥ Y`). -/
theorem inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₃ - d • χ₁)) = -(d : ℂ) := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₃ - d • χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX3)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  have e13 : ClassFunction.inner χ₁ χ₃ = 0 := by rw [hXon χ₁ χ₃ hχ₁ hχ₃, if_neg (Ne.symm hne)]
  have e11 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have ey3 : ClassFunction.inner η₁ χ₃ = 0 := hYXz χ₃ hχ₃
  have ey1 : ClassFunction.inner η₁ χ₁ = 0 := hYXz χ₁ hχ₁
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η₁, ← Nat.cast_smul_eq_nsmul ℂ d χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    e13, e11, ey3, ey1, star_natCast]
  ring

open scoped Classical in
/-- **(6.8.1) `X`-difference isometry, degree-ratio form**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius`.  `X`-irreducibility comes from the
certain-type input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`)
instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₃ - d • χ₁)) = -(d : ℂ) := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₃ - d • χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX3)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  have e13 : ClassFunction.inner χ₁ χ₃ = 0 := by rw [hXon χ₁ χ₃ hχ₁ hχ₃, if_neg (Ne.symm hne)]
  have e11 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have ey3 : ClassFunction.inner η₁ χ₃ = 0 := hYXz χ₃ hχ₃
  have ey1 : ClassFunction.inner η₁ χ₁ = 0 := hYXz χ₁ hχ₁
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η₁, ← Nat.cast_smul_eq_nsmul ℂ d χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    e13, e11, ey3, ey1, star_natCast]
  ring

open scoped Classical in
/-- **(6.8.1) step-5 relation, degree-ratio form.**  For the good-case element
`X := (χ₁−aη₁)^τ + a·η₁^{τ₁}` and a third `X`-member `χ₃` of degree ratio `d` (`χ₃(1) = d·χ₁(1)`):
`⟨X, χ₃^{τ₂}⟩ − d·⟨X, χ₁^{τ₂}⟩ = −d`.  himg_ortho (`η₁^{τ₁} ⊥ X^{τ₂}`) gives `⟨X,·⟩ = ⟨v,·⟩`; the
`X`-coherence `(χ₃−d·χ₁)^τ = χ₃^{τ₂} − d·χ₁^{τ₂}` and the degree-ratio isometry value
`⟨v, (χ₃−d·χ₁)^τ⟩ = −d` close it.  Generalizes `inner_extension_Xset_sub_eq_neg_one_general`
(the `d = 1` case). -/
theorem inner_extension_Xset_scaledSub_eq_neg_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) (cX.extension χ₃)
      - (d : ℂ) * ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁) = -(d : ℂ) := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (cX.extension χ)
        = ClassFunction.inner v (cX.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hχ hη₁
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (cX.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hXcoh : hyp.tau (χ₃ - d • χ₁) = cX.extension χ₃ - (d : ℂ) • cX.extension χ₁ := by
    have h := cX.extends_on_supported (χ₃ - d • χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₃)
        (nsmul_mem (Submodule.subset_span hχ₁) d), hsuppX3⟩
    rw [map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ d (cX.extension χ₁)] at h
    exact h.symm
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius hF hη₁ hχ₁ hχ₃ hne ha hd
  rw [hXcoh, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast] at hiso
  rw [hXv χ₃ hχ₃, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) step-5 relation, degree-ratio form**, case (A) / c2 mirror of
`inner_extension_Xset_scaledSub_eq_neg_general`.  The himg_ortho/isometry inputs use their case-(A)
counterparts (`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`,
`inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) (cX.extension χ₃)
      - (d : ℂ) * ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁) = -(d : ℂ) := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (cX.extension χ)
        = ClassFunction.inner v (cX.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
      hK hW1 hA cX cY hχ hη₁
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (cX.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hXcoh : hyp.tau (χ₃ - d • χ₁) = cX.extension χ₃ - (d : ℂ) • cX.extension χ₁ := by
    have h := cX.extends_on_supported (χ₃ - d • χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₃)
        (nsmul_mem (Submodule.subset_span hχ₁) d), hsuppX3⟩
    rw [map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ d (cX.extension χ₁)] at h
    exact h.symm
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ hχ₃ hne ha hd
  rw [hXcoh, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast] at hiso
  rw [hXv χ₃ hχ₃, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) crux, general witnesses + ANY third anchor (`|X(Zc)| ≥ 3`)** — closes the
`|xBaseBlock| = 2 ∧ |X(Zc)| ≥ 3` gap that the equal-degree `crux_of_third_anchor_general` (which
needs a *third equal-degree* anchor, i.e. `|xBaseBlock| ≥ 3`) cannot reach.  Given the good case
`⟨(χ₁−aη₁)^τ, cY η₁⟩ = −a`, the dichotomy `X = cX χ₁ ∨ X = −cX χ₂` (equal-degree `χ₂`); the right
disjunct is excluded by ANY third `X`-member `χ₃` (any degree) via the degree-ratio relation
`⟨X, cX χ₃⟩ − d₃·⟨X, cX χ₁⟩ = −d₃` (`inner_extension_Xset_scaledSub_eq_neg_general`): under
`X = −cX χ₂` both inner products vanish (distinct `X`-images), giving `0 = −d₃`, impossible since
`d₃ > 0`.  Hence the crux `(χ₁−aη₁)^τ = cX χ₁ − a·cY η₁`. -/
theorem crux_general_of_higher_anchor
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  obtain ⟨d, hdpos, hd⟩ :=
    hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X hp hHp
      (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχ₃ hχ₁base
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (cX.extension ψ) (cX.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [cX.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general hF cX cY hη₁ hχ₁X hχ₂ hne₂ ha hdeg2 hgood with h | h
  · exact eq_sub_of_add_eq h
  · exfalso
    have hrel3 := hyp.inner_extension_Xset_scaledSub_eq_neg_general hF cX cY hη₁ hχ₁X hχ₃ hne₃₁ ha hd
    rw [h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁X, if_neg hne₂] at hrel3
    have hd0 : (d : ℂ) = 0 := by linear_combination hrel3
    rw [Nat.cast_eq_zero] at hd0
    omega

open scoped Classical in
/-- **(6.8.1) crux, general witnesses + ANY third anchor**, case (A) / c2 mirror of
`crux_general_of_higher_anchor`.  The dichotomy/relation/`X`-irreducibility inputs use their
case-(A) counterparts (`extension_eq_or_eq_neg_general_c2_caseA`,
`inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem crux_general_of_higher_anchor_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  obtain ⟨d, hdpos, hd⟩ :=
    hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X hp hHp
      (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hχ₃ hχ₁base
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (cX.extension ψ) (cX.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [cX.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁ hχ₁X hχ₂ hne₂ ha hdeg2
    hgood with h | h
  · exact eq_sub_of_add_eq h
  · exfalso
    have hrel3 := hyp.inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁
      hχ₁X hχ₃ hne₃₁ ha hd
    rw [h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁X, if_neg hne₂] at hrel3
    have hd0 : (d : ℂ) = 0 := by linear_combination hrel3
    rw [Nat.cast_eq_zero] at hd0
    omega

open scoped Classical in
/-- **(6.8.1) E2: a `Y`-coherence witness in the good case** (the `m = 2` relabel, folded in).
Produces a `Y`-coherence witness `cY` with `⟨(χ₁−aη₁)^τ, cY η₁⟩ = −a` — the `hgood` that the crux
consumes.  Generic `|Y| ≥ 3`: `cY = coherentYset` (good branch of the step-4 dichotomy
`coeff_eq_neg_or_edge_of_frobenius`).  Edge `|Y| = 2`: `coherentYset` may give the bad value `0`;
then `Y = {η₁, η₂}` and the sign-swapped witness `cY'` (`coherentEqualDegree_swap_neg`,
`η₁ ↦ −η₂^{τ₁}`) gives `⟨v, cY' η₁⟩ = −⟨v, coherentYset η₂⟩ = −a`, since
`⟨v, coherentYset η₂⟩ = ⟨v, coherentYset η₁⟩ + a = 0 + a = a` (`inner_tau_scaledDiff_tau_Yset_diff`
+ `extends_on_supported`). -/
theorem exists_Ycoherence_hgood_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ) := by
  classical
  rcases hyp.coeff_eq_neg_or_edge_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    hgood | ⟨hm2, hbad⟩
  · exact ⟨hyp.coherentYset, hgood⟩
  · -- edge `|Y| = 2`: relabel.
    obtain ⟨η₂, hη₂Y, hη₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
    have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
      intro x hx; rcases hx with rfl | rfl
      · exact hη₁
      · exact hη₂Y
    have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
      (Set.eq_of_subset_of_ncard_le hpairsub (hm2.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm)
        hyp.Yset_finite).symm
    -- orthonormality of `η₁, η₂` (distinct irreducible `Y`-members).
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
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
    -- transport `coherentYset` to the pair, build the swapped witness, transport back.
    have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
    obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdeg hdeg0 h1A hsupp
    refine ⟨hYeq.symm ▸ cY', ?_⟩
    -- `⟨v, η₂^{τ₁}⟩ = a` from the constancy + the bad value `⟨v, η₁^{τ₁}⟩ = 0`.
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη₂Y hη₂ne hχ₁ ha
    have htaud : hyp.tau (η₂ - η₁)
        = hyp.coherentYset.extension η₂ - hyp.coherentYset.extension η₁ := by
      rw [← hyp.coherentYset.extends_on_supported (η₂ - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂Y) (Submodule.subset_span hη₁), hsupp⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hbad, sub_zero] at hconst
    -- assemble: `⟨v, (cY' η₁)⟩ = −⟨v, coherentYset η₂⟩ = −a`.
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
      ClassFunction.inner_neg_right, hconst]

open scoped Classical in
/-- **(6.8.1) E2: a `Y`-coherence witness in the good case**, case (A) / c2 mirror of
`exists_Ycoherence_hgood_of_frobenius`.  The step-4 dichotomy/constancy inputs use their case-(A)
counterparts (`coeff_eq_neg_or_edge_c2_caseA`, `inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`)
instead of `hF` (cert data `hK`/`hW1`/`hA`); the non-`hF` `coherentEqualDegree_swap_neg` relabel is
copied verbatim. -/
theorem exists_Ycoherence_hgood_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ) := by
  classical
  rcases hyp.coeff_eq_neg_or_edge_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    hgood | ⟨hm2, hbad⟩
  · exact ⟨hyp.coherentYset, hgood⟩
  · -- edge `|Y| = 2`: relabel.
    obtain ⟨η₂, hη₂Y, hη₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
    have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
      intro x hx; rcases hx with rfl | rfl
      · exact hη₁
      · exact hη₂Y
    have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
      (Set.eq_of_subset_of_ncard_le hpairsub (hm2.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm)
        hyp.Yset_finite).symm
    -- orthonormality of `η₁, η₂` (distinct irreducible `Y`-members).
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
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
    -- transport `coherentYset` to the pair, build the swapped witness, transport back.
    have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
    obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdeg hdeg0 h1A hsupp
    refine ⟨hYeq.symm ▸ cY', ?_⟩
    -- `⟨v, η₂^{τ₁}⟩ = a` from the constancy + the bad value `⟨v, η₁^{τ₁}⟩ = 0`.
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη₂Y hη₂ne hχ₁ ha
    have htaud : hyp.tau (η₂ - η₁)
        = hyp.coherentYset.extension η₂ - hyp.coherentYset.extension η₁ := by
      rw [← hyp.coherentYset.extends_on_supported (η₂ - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂Y) (Submodule.subset_span hη₁), hsupp⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hbad, sub_zero] at hconst
    -- assemble: `⟨v, (cY' η₁)⟩ = −⟨v, coherentYset η₂⟩ = −a`.
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
      ClassFunction.inner_neg_right, hconst]

open scoped Classical in
/-- **(6.8.1) E3: `X`-coherence witness + crux in the `|X(Zc)| = 2` edge** (the `n = 2` relabel).
When `X(Zc) = {χ₁, χ₂}` (a conjugate pair, equal degree), the step-5 dichotomy
`X = cX₀ χ₁ ∨ X = −cX₀ χ₂` (`extension_eq_or_eq_neg_general` at the fixed `cX₀`) has no third anchor
to exclude the right disjunct; instead, the right disjunct is *absorbed* by the sign-swapped witness
`cX'` (`coherentEqualDegree_swap_neg`, `χ₁ ↦ −χ₂^{τ₂}`, valid because `|X| = 2` is the whole set):
`cX' χ₁ = −cX₀ χ₂ = X`, giving the crux `(χ₁−aη₁)^τ = cX' χ₁ − a·cY η₁`.  Left disjunct uses `cX = cX₀`
directly.  Produces a witness + crux for *some* `cX`. -/
theorem exists_Xcoherence_crux_of_card_two_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)))
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    ∃ cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set cX0 := hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp with hcX0def
  rcases hyp.extension_eq_or_eq_neg_general hF cX0 cY hη₁ hχ₁ hχ₂ hne ha hdeg2 hgood with h | h
  · -- left disjunct `X = cX₀ χ₁` ⟹ crux for `cX₀`.
    exact ⟨cX0, eq_sub_of_add_eq h⟩
  · -- right disjunct `X = −cX₀ χ₂` ⟹ relabel `cX' χ₁ = −cX₀ χ₂`.
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have hh := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hh
      rw [hh]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hX1irr := hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
    have hX2irr := hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₂
    have horth : ClassFunction.inner χ₁ χ₂ = 0 := by
      rw [hinner χ₁ χ₂ hX1irr hX2irr, if_neg (Ne.symm hne)]
    have hn1 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hinner χ₁ χ₁ hX1irr hX1irr, if_pos rfl]
    have hn2 : ClassFunction.inner χ₂ χ₂ = 1 := by rw [hinner χ₂ χ₂ hX2irr hX2irr, if_pos rfl]
    have hdeg0 : (χ₁ : ↥L → ℂ) 1 ≠ 0 := by
      obtain ⟨d, hdpos, hdeq⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ₁, hX1irr⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hdeq
      rw [hdeq]; exact_mod_cast hdpos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (χ₂ - χ₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
    have hcX0map : (hXeq ▸ cX0).extension = cX0.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq cX0
    obtain ⟨cX', hcX'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hXeq ▸ cX0) horth hn1 hn2 hdeg2 hdeg0 h1A hsupp
    refine ⟨hXeq.symm ▸ cX', ?_⟩
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq.symm cX', hcX'1, hcX0map]
    exact eq_sub_of_add_eq h

open scoped Classical in
/-- **(6.8.1) E3: `X`-coherence witness + crux in the `|X(Zc)| = 2` edge**, case (A) / c2 mirror of
`exists_Xcoherence_crux_of_card_two_of_frobenius`.  The fixed `X`-coherence/dichotomy/`X`-irreducibility
inputs use their case-(A) counterparts (`Xset_centralCommutator_isCoherent_of_c2_caseA`,
`extension_eq_or_eq_neg_general_c2_caseA`, `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of
`hF` (cert data `hK`/`hW1`/`hA`); the non-`hF` `coherentEqualDegree_swap_neg` relabel is copied
verbatim. -/
theorem exists_Xcoherence_crux_of_card_two_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)))
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    ∃ cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set cX0 := hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp
    with hcX0def
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX0 cY hη₁ hχ₁ hχ₂ hne ha hdeg2
    hgood with h | h
  · -- left disjunct `X = cX₀ χ₁` ⟹ crux for `cX₀`.
    exact ⟨cX0, eq_sub_of_add_eq h⟩
  · -- right disjunct `X = −cX₀ χ₂` ⟹ relabel `cX' χ₁ = −cX₀ χ₂`.
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have hh := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hh
      rw [hh]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hX1irr := hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
    have hX2irr := hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₂
    have horth : ClassFunction.inner χ₁ χ₂ = 0 := by
      rw [hinner χ₁ χ₂ hX1irr hX2irr, if_neg (Ne.symm hne)]
    have hn1 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hinner χ₁ χ₁ hX1irr hX1irr, if_pos rfl]
    have hn2 : ClassFunction.inner χ₂ χ₂ = 1 := by rw [hinner χ₂ χ₂ hX2irr hX2irr, if_pos rfl]
    have hdeg0 : (χ₁ : ↥L → ℂ) 1 ≠ 0 := by
      obtain ⟨d, hdpos, hdeq⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ₁, hX1irr⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hdeq
      rw [hdeq]; exact_mod_cast hdpos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (χ₂ - χ₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
    have hcX0map : (hXeq ▸ cX0).extension = cX0.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq cX0
    obtain ⟨cX', hcX'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hXeq ▸ cX0) horth hn1 hn2 hdeg2 hdeg0 h1A hsupp
    refine ⟨hXeq.symm ▸ cX', ?_⟩
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq.symm cX', hcX'1, hcX0map]
    exact eq_sub_of_add_eq h

/-- **(6.8.1) capstone `X(Zc) ∪ Y` coherence from a witness-level crux** (general form).  Given
arbitrary coherence witnesses `cX` (for `X(Zc)`), `cY` (for `Y`), a base-block anchor `χ₁` with
`χ₁(1) = a·|W₁|`, an `η₁ ∈ Y`, and the **crux** `(χ₁−aη₁)^τ = cX χ₁ − a·cY η₁` (whichever way it is
established — the generic `n,m ≥ 3` argument or the `m=2`/`n=2` relabel), the union `X(Zc) ∪ Y` is
coherent.  `ν` is the `τ₃` glue of `cX`/`cY`; `hmixed = himg_ortho_general`, `hDτ = hcrux`,
`hgen = hgen_withDiagonal`.  This is the common assembly shared by the generic case and both edge
cases (which differ only in how `hcrux` is produced for the chosen witnesses). -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hcrux : hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      cX.extension cY.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_general
    hF cX cY hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_)
    {χ₁ - a • η₁} (fun d hd => ?_)
    (hyp.hgen_withDiagonal_of_frobenius hF hp hHp hη₁ hχ₁base ha)
  · -- `hmixed`: `⟨ν x, ν y⟩ = ⟨x, y⟩` (both `0`).
    rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy,
      hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hx hy, hXY x hx y hy]
  · -- `hDτ`: `ν(χ₁−aη₁) = (χ₁−aη₁)^τ` = the crux.
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [map_sub, map_nsmul, hglue.choose_spec.1 χ₁ hχ₁X, hglue.choose_spec.2 η₁ hη₁,
      ← Nat.cast_smul_eq_nsmul ℂ a (cY.extension η₁)]
    exact hcrux.symm

/-- **(6.8.1) capstone `X(Zc) ∪ Y` coherence from a witness-level crux**, case (A) / c2 mirror of
`coherentXunionYset_centralCommutator_diagonal_general`.  The glue/`X ⊥ Y`/`hgen`/`X`-irreducibility
inputs use their case-(A) counterparts
(`coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA`,
`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`, `hgen_withDiagonal_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hcrux : hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      cX.extension cY.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA
    hK hW1 hA cX cY hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_)
    {χ₁ - a • η₁} (fun d hd => ?_)
    (hyp.hgen_withDiagonal_c2_caseA hK hW1 hA hp hHp hη₁ hχ₁base ha)
  · -- `hmixed`: `⟨ν x, ν y⟩ = ⟨x, y⟩` (both `0`).
    rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy,
      hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA hK hW1 hA cX cY hx hy,
      hXY x hx y hy]
  · -- `hDτ`: `ν(χ₁−aη₁) = (χ₁−aη₁)^τ` = the crux.
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [map_sub, map_nsmul, hglue.choose_spec.1 χ₁ hχ₁X, hglue.choose_spec.2 η₁ hη₁,
      ← Nat.cast_smul_eq_nsmul ℂ a (cY.extension η₁)]
    exact hcrux.symm

/-- **(6.8.1) generic capstone Frobenius branch (`m, n ≥ 3`):** `X(Zc) ∪ Y` is coherent.

Given three distinct equal-degree `X(Zc)`-anchors `χ₁ ∈ xBaseBlock`, `χ₂, χ₃` (the `n ≥ 3`
pinning) with `χ₁(1) = a·|W₁|`, an `η₁ ∈ Y` and `|Y| ≥ 3` (the `m ≥ 3` good case), the union is
coherent.  Delegates to `coherentXunionYset_centralCommutator_diagonal_general` at the fixed
witnesses, with `hcrux = crux_of_frobenius`.  The `m = 2` / `n = 2` edge cases (relabel) are not
covered. -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1) (hm3 : 3 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁base ha
    (hyp.crux_of_frobenius hF hHnonab hp hp3 hHp hη₁ (hyp.xBaseBlock_subset _ hχ₁base) hχ₂ hne₂
      hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hm3)

/-- **(6.8.1) generic capstone branch (`m, n ≥ 3`)**, case (A) / c2 mirror of
`coherentXunionYset_centralCommutator_diagonal_of_frobenius`.  Delegates to
`coherentXunionYset_centralCommutator_diagonal_general_c2_caseA` at the case-(A) `X`-coherence
(`Xset_centralCommutator_isCoherent_of_c2_caseA`) with `hcrux = crux_c2_caseA` (cert data
`hK`/`hW1`/`hA`) instead of `hF`. -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1) (hm3 : 3 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentXunionYset_centralCommutator_diagonal_general_c2_caseA hK hW1 hA hp hHp
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁base ha
    (hyp.crux_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ (hyp.xBaseBlock_subset _ hχ₁base) hχ₂ hne₂
      hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hm3)

/-- **(6.8) capstone, case (A) (Frobenius, `m, n ≥ 3` with given anchors): `S` is coherent.**
Combines the generic capstone Frobenius branch
(`coherentXunionYset_centralCommutator_diagonal_of_frobenius`, giving `X(Zc) ∪ Y` coherent) with the
(6.8.3) extension `false_of_coherentXunionYset_of_not_coherentS` (`X ∪ Y` coherent ∧ `S` not
coherent ⟹ False): so `S` is coherent.  The anchors `χ₁ ∈ xBaseBlock, χ₂, χ₃` (distinct,
equal-degree, the `n ≥ 3` data) and `3 ≤ |Y|` (the `m ≥ 3` data) are taken as hypotheses; their
existence (vs the
`m = 2` / `n = 2` relabels) is a separate concern. -/
theorem nonempty_coherent_S_caseA_of_anchors_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1) (hm3 : 3 ≤ hyp.Yset.ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  by_contra hncoh
  exact hyp.false_of_coherentXunionYset_of_not_coherentS hF hHnonab
    ⟨hyp.coherentXunionYset_centralCommutator_diagonal_of_frobenius hF hHnonab hp hp3 hHp
      hη₁ hχ₁base hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hm3⟩ hncoh

/-- **(6.8) capstone, case (A) under the `m, n ≥ 3` cardinality data: `S` is coherent.**
From `3 ≤ |xBaseBlock Zc|` (giving three distinct base-block anchors `χ₁, χ₂, χ₃`, all of equal
degree since the base block is equal-degree, `xBaseBlock_degree_re_eq`) and `3 ≤ |Y|`, the anchor
hypotheses of `nonempty_coherent_S_caseA_of_anchors_of_frobenius` are met (with `χ₁(1) = a·|W₁|`
extracted via a degree-`|W₁|` `Y`-anchor), so `S` is coherent.  This is the (6.8) capstone Frobenius
branch in the generic `m, n ≥ 3` case; the `m = 2` / `n = 2` edge cases (relabels) are not
covered. -/
theorem nonempty_coherent_S_caseA_of_card_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (h3X : 3 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard)
    (h3Y : 3 ≤ hyp.Yset.ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  -- three distinct base-block anchors (from `3 ≤ |xBaseBlock|`).
  obtain ⟨χ₁, hχ₁base, χ₂, hχ₂base, χ₃, hχ₃base, hne12, hne13, hne23⟩ :
      ∃ a ∈ hyp.xBaseBlock hyp.centralCommutator, ∃ b ∈ hyp.xBaseBlock hyp.centralCommutator,
        ∃ c ∈ hyp.xBaseBlock hyp.centralCommutator, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    obtain ⟨a, ha⟩ : (hyp.xBaseBlock hyp.centralCommutator).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard
      (s := hyp.xBaseBlock hyp.centralCommutator) (by omega) a
    have hpair : ({a, b} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.xBaseBlock hyp.centralCommutator := by
      intro x hx; rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have hdc : (hyp.xBaseBlock hyp.centralCommutator \ {a, b}).ncard
        = (hyp.xBaseBlock hyp.centralCommutator).ncard - 2 := by
      rw [Set.ncard_sdiff hpair, Set.ncard_pair (Ne.symm hba)]
    have hcne : (hyp.xBaseBlock hyp.centralCommutator \ {a, b}).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he; rw [he, Set.ncard_empty] at hdc; omega
    obtain ⟨c, hcs, hcnp⟩ := hcne
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcnp
    exact ⟨a, ha, b, hb, c, hcs, Ne.symm hba, fun h => hcnp.1 h.symm, fun h => hcnp.2 h.symm⟩
  have hχ₁X := hyp.xBaseBlock_subset _ hχ₁base
  have hχ₂X := hyp.xBaseBlock_subset _ hχ₂base
  have hχ₃X := hyp.xBaseBlock_subset _ hχ₃base
  -- `η₁ ∈ Y` (degree `|W₁|`) and the degree ratio `a`.
  obtain ⟨η₁, hη₁⟩ := hyp.Yset_nonempty
  obtain ⟨a, _, ha⟩ := hyp.sMember_charValue_one_eq_mul_anchor (hyp.Xset_subset_S hχ₁X)
    (hyp.Yset_apply_one hη₁)
  rw [hyp.Yset_apply_one hη₁] at ha
  -- the base block is equal-degree.
  have hdegeq : ∀ χ' ∈ hyp.xBaseBlock hyp.centralCommutator, χ' 1 = χ₁ 1 := by
    intro χ' hχ'
    have hre := hyp.xBaseBlock_degree_re_eq hχ' hχ₁base
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hre
    obtain ⟨d', _, hd'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ', hXirr χ' (hyp.xBaseBlock_subset _ hχ')⟩ : IrreducibleCharacter ↥L)
    obtain ⟨d₁, _, hd₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hXirr χ₁ hχ₁X⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd' hd₁
    rw [hd', hd₁] at hre ⊢
    exact_mod_cast hre
  exact hyp.nonempty_coherent_S_caseA_of_anchors_of_frobenius hF hHnonab hp hp3 hHp hη₁
    hχ₁base hχ₂X hne12.symm hχ₃X hne13.symm hne23.symm ha
    (hdegeq χ₂ hχ₂base) (hdegeq χ₃ hχ₃base) h3Y

open scoped Classical in
/-- **(6.8) capstone, case (A) (Frobenius): `S` is coherent — UNCONDITIONAL** (no `3 ≤` cardinality
hypotheses; the `m = 2` / `n = 2` edge relabels are handled internally).  This is the full case-(A)
result: only `2 ≤ |xBaseBlock|` (`two_le_xBaseBlock_ncard`) and `2 ≤ |Y|` (`two_le_Yset_ncard`),
both unconditionally available, are used.  E2 (`exists_Ycoherence_hgood_of_frobenius`) supplies the
`Y`-witness + good case (the `m = 2` relabel).  The `X`-side splits on `|X(Zc)|`: `≥ 3` uses the
degree-ratio crux E1 (`crux_general_of_higher_anchor`) at the fixed `X`-witness; `= 2` uses the
relabel crux E3 (`exists_Xcoherence_crux_of_card_two_of_frobenius`).  Either way the crux feeds the
shared assembly `coherentXunionYset_centralCommutator_diagonal_general`, giving `X(Zc) ∪ Y` coherent,
and the (6.8.3) extension `false_of_coherentXunionYset_of_not_coherentS` lifts it to `S`. -/
theorem nonempty_coherent_S_caseA_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  by_contra hncoh
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty :=
    hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.Xset_finite hyp.centralCommutator
  have h2X : 2 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard :=
    hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le hXne
  -- two distinct base-block anchors.
  obtain ⟨χ₁, hχ₁base, χ₂, hχ₂base, hne⟩ : ∃ a ∈ hyp.xBaseBlock hyp.centralCommutator,
      ∃ b ∈ hyp.xBaseBlock hyp.centralCommutator, b ≠ a := by
    obtain ⟨a, ha⟩ : (hyp.xBaseBlock hyp.centralCommutator).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard
      (s := hyp.xBaseBlock hyp.centralCommutator) (by omega) a
    exact ⟨a, ha, b, hb, hba⟩
  have hχ₁X := hyp.xBaseBlock_subset _ hχ₁base
  have hχ₂X := hyp.xBaseBlock_subset _ hχ₂base
  -- `η₁ ∈ Y` (degree `|W₁|`) and the degree ratio `a`.
  obtain ⟨η₁, hη₁⟩ := hyp.Yset_nonempty
  obtain ⟨a, ha_pos, ha⟩ := hyp.sMember_charValue_one_eq_mul_anchor (hyp.Xset_subset_S hχ₁X)
    (hyp.Yset_apply_one hη₁)
  rw [hyp.Yset_apply_one hη₁] at ha
  -- base block equal-degree.
  have hdegeq : ∀ χ' ∈ hyp.xBaseBlock hyp.centralCommutator, χ' 1 = χ₁ 1 := by
    intro χ' hχ'
    have hre := hyp.xBaseBlock_degree_re_eq hχ' hχ₁base
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hre
    obtain ⟨d', _, hd'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ', hXirr χ' (hyp.xBaseBlock_subset _ hχ')⟩ : IrreducibleCharacter ↥L)
    obtain ⟨d₁, _, hd₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hXirr χ₁ hχ₁X⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd' hd₁
    rw [hd', hd₁] at hre ⊢
    exact_mod_cast hre
  have hdeg2 : χ₂ 1 = χ₁ 1 := hdegeq χ₂ hχ₂base
  -- E2: the `Y`-witness with the good case (m = 2 relabel folded in).
  obtain ⟨cY, hgood⟩ :=
    hyp.exists_Ycoherence_hgood_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁X ha_pos ha
  -- build `X(Zc) ∪ Y` coherent, splitting on `|X(Zc)|`.
  have hXYcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    by_cases h3X : 3 ≤ (hyp.Xset hyp.centralCommutator).ncard
    · -- `|X(Zc)| ≥ 3`: a third `X`-member of ANY degree (E1, degree-ratio exclusion).
      have hex : ∃ c ∈ hyp.Xset hyp.centralCommutator, c ≠ χ₁ ∧ c ≠ χ₂ := by
        have hpair : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
          intro x hx; rcases hx with rfl | rfl
          · exact hχ₁X
          · exact hχ₂X
        have hdc : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).ncard
            = (hyp.Xset hyp.centralCommutator).ncard - 2 := by
          rw [Set.ncard_sdiff hpair, Set.ncard_pair (Ne.symm hne)]
        have hcne : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]; intro he; rw [he, Set.ncard_empty] at hdc; omega
        obtain ⟨c, hcs, hcnp⟩ := hcne
        rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcnp
        exact ⟨c, hcs, hcnp.1, hcnp.2⟩
      have cX0 := hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp cX0 cY hη₁
        hχ₁base ha (hyp.crux_general_of_higher_anchor hF hp hHp cX0 cY hη₁ hχ₁base hχ₂X hne hdeg2
          hex.choose_spec.1 hex.choose_spec.2.1 hex.choose_spec.2.2 ha hgood)
    · -- `|X(Zc)| = 2`: relabel (E3).
      have h2Xle : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
        le_trans h2X (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
      have h2Xeq : (hyp.Xset hyp.centralCommutator).ncard = 2 := by omega
      have hpairsub : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
        intro x hx; rcases hx with rfl | rfl
        · exact hχ₁X
        · exact hχ₂X
      have hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) :=
        (Set.eq_of_subset_of_ncard_le hpairsub
          (h2Xeq.le.trans_eq (Set.ncard_pair (Ne.symm hne)).symm) hXfin).symm
      have hexX := hyp.exists_Xcoherence_crux_of_card_two_of_frobenius hF hHnonab hp hp3 hHp
        cY hη₁ hχ₁X hχ₂X hne hdeg2 hXeq ha hgood
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp hexX.choose cY hη₁
        hχ₁base ha hexX.choose_spec
  exact hyp.false_of_coherentXunionYset_of_not_coherentS hF hHnonab ⟨hXYcoh⟩ hncoh

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08
