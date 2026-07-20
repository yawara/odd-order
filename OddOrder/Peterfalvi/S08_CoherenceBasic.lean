/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart2

/-!
# S08_CoherenceBasic

Prefix-split from `OddOrder.Peterfalvi.S08_CoherenceCore` (2000-line limit, issue 0103 第 2 パス).
-/

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
`Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X` but the
per-step
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

/-- **(6.6)/(6.8.1), central-`Zc`, completeness-exposing form (redesign L2 outer shell,
withCover).**
Same as
`Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
but the `hstepData` producer receives the Xset-cover completeness witness `hcover` (finding #6),
which
the monolith needs to build `tailSet`/`htail_le`/`hsum`.  Routes through the `…withCover…`
consumer. -/
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
  exact
    hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X
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
    {i : ℕ} (_hi : i < N)
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
producer supplies `deg φ = |L:H|·p^(eφ)` and `totalN = |L:H|·(|H|−|H:Z|)` (via
`sum_re_sq_Xset_eq`). -/
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
irreducibility hypothesis (the `c2`/case-A `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) can feed
the
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
/-- **Peterfalvi (6.6)(b): `X = S − S(Z)` is coherent — the Z-generic form.**  For any normal
subgroup `Z` of `L` with `Z ≤ H` central in `H` (`Z.subgroupOf H ≤ Z(H)`, the book's
`Z ⊆ Z(K)`), the set `X(Z) = S − S(Z)` is coherent, given that every `X`-member is irreducible
(`hX` — the book's hypothesis `𝒳 ⊆ Irr L`), that `X` is nonempty (`hXne` — in the book from
`Z ≠ 1` via (1.1)), that `H` is a `p`-group for a prime `p ≥ 3` (the book reduces to this case
by (6.5), and `p` is odd since `|L|` is), and that `|L:H|` is coprime to `p` (`hidxp`, from
(6.4.c)/(6.5.c)).  Builds the per-step `PairUnionBaseAnchorCommonIndexPrimePowerStepData` for
every chain step and feeds it to the `…withCover…` generic shell.  The central-commutator
(`Zc = Z(H) ∩ H′`) instantiations (`…_of_frobenius`, `…_of_c2_caseA`) are thin specializations
differing only in how `hX`/`hXne`/`hidxp` are produced
(`isIrreducibleCharacter_of_mem_Xset_of_frobenius` + `hF.coprime_card_kernel_complement` vs
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` + `cert.card_coprime`). -/
noncomputable def Xset_isCoherent_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (hZle : Z ≤ H)
    (hZcent : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    (hXne : (hyp.Xset Z).Nonempty)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (hidxp : Nat.Coprime H.index p) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  haveI : Fact p.Prime := ⟨hp⟩
  -- the common-index degree exponent over `X(Zc)`
  have hdegX : ∀ φ ∈ hyp.Xset Z,
      ∃ kφ : ℕ, (φ : ClassFunction ↥L ℂ) 1 = ((H.index * p ^ kφ : ℕ) : ℂ) :=
    fun φ hφ => hyp.exists_index_primePow_degree_of_mem_S hp hHp (hyp.Xset_subset_S hφ)
  choose! e he using hdegX
  -- `qtot = |H:Zc| = p^mq`
  haveI : (Z.subgroupOf H).Normal := ‹Z.Normal›.subgroupOf H
  choose mq hmq using
    exists_primePow_card_quotient_of_isPGroup hp hHp (Z.subgroupOf H)
  have hZqle : Nat.card (↥H ⧸ Z.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  refine
    hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X
      (Z := Z) hZle hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi
  -- `χs i ∈ X(Zc)`
  have hχiX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := by
    refine hpairs i hi ?_
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  -- central degree bound for the head
  choose mχ hχdeg hχsq using hyp.exists_source_primePow_centralBound_of_mem_Xset hp hHp
    hZcent hχiX
  -- member-family enumeration
  choose k χmem hconj using
    hyp.exists_pairUnion_memberFamily_of_irreducible_X hZle
      hX hpair0 hpair1 hpairs hi
  obtain ⟨hχinj, hrange, -, -, -, -, -, -⟩ := hconj
  -- members lie in `X(Zc)`
  have hmemX : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := by
    intro j
    have : (χmem j : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i :=
            by
      rw [← hrange]; exact Set.mem_range_self j
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp this with hbase | ⟨j', hj', hj'pair⟩
    · exact hyp.xBaseBlock_subset _ hbase
    · exact hpairs j' (hj'.trans hi) hj'pair
  -- base-block anchor
  have hbbne : (hyp.xBaseBlock Z).Nonempty := by
    rw [← Set.ncard_pos (hyp.xSet_finite_of_irreducible_X hX |>.subset
        (hyp.xBaseBlock_subset _))]
    exact lt_of_lt_of_le (by norm_num) (hyp.two_le_xBaseBlock_ncard_of_irreducible_X
      hZle hX hXne)
  choose i₁ hanchor using hyp.exists_xBaseBlock_anchor_index hrange hbbne
  -- the `X(Zc)` index Finset (the `sum_re_sq_Xset_eq` domain) and its coe
  set XF := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆
                OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXFdef
  have hmemXF : ∀ φ, φ ∈ XF ↔ φ ∈ hyp.Xset Z := by
    intro φ; rw [hXFdef]; exact hyp.mem_xSetFinset_iff_mem_Xset (Z := Z) φ
  -- real degree-square sum over `XF`
  have hrealSum : (∑ φ ∈ XF, ((H.index * p ^ e φ : ℕ) : ℝ) ^ 2)
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ)
          - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
    rw [← hyp.sum_re_sq_Xset_eq_of_irreducible_X (Z := Z)
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
      qtot := Nat.card (↥H ⧸ Z.subgroupOf H)
      c := H.index * (Nat.card ↥(Z.subgroupOf H) - 1)
      total := H.index * (Nat.card ↥H - Nat.card (↥H ⧸ Z.subgroupOf H))
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
            (hyp.xBaseBlock Z) pair i := by
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
            = H.index * (Nat.card ↥H - Nat.card (↥H ⧸ Z.subgroupOf H))
        rw [show (∑ i : Fin tailF.card, (H.index * p ^ e (tElt i)) * (H.index * p ^ e (tElt i)))
              = ∑ x ∈ tailF, (H.index * p ^ e x) * (H.index * p ^ e x) from
            hreindex (fun x => (H.index * p ^ e x) * (H.index * p ^ e x))]
        exact natSum_partition_of_realSum XF (fun φ => H.index * p ^ e φ)
          (H.index * (Nat.card ↥H - Nat.card (↥H ⧸ Z.subgroupOf H)))
          (by rw [hrealSum]; push_cast [Nat.cast_sub hZqle]; ring) hinj hsub
      hqtot := hmq
      hθsq_le_qtot := by rw [← pow_two]; exact hχsq
      htotal := hyp.index_mul_card_sub_factor (Z := Z)
      hidx_p := hidxp }

open scoped Classical in
/-- **(6.6)/(6.8) X = S − S(Zc) coherence at the central commutator — the L2 producer.**
The redesign's L2 deliverable: `X(Zc)` is coherent, with `Zc = Z(H) ∩ H′` central.  Builds the
per-step `PairUnionBaseAnchorCommonIndexPrimePowerStepData` (the first-ever such term) for every
chain step and feeds it to the `…withCover…` Zc shell.  Per step: the current head `χs i` and every
`X`-member `Ind θ` have degree `|L:H|·p^k` (`exists_index_primePow_degree_of_mem_S`), the central
degree bound `θχ² ≤ |H:Zc|` holds ([Is] Cor 2.30 via
`exists_source_primePow_centralBound_of_mem_Xset`),
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
  haveI := hyp.centralCommutator_normal
  exact hyp.Xset_isCoherent_of_irreducible_X hyp.centralCommutator_le
    hyp.centralCommutator_subgroupOf_le_center
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hp hp3 hHp hidxp

open scoped Classical in
/-- **(6.6)/(6.8) X(Zc) coherence, certain-type case (B), math-(A) sub-case `Z(H) ∩ W₂ = ⊥` (CB3).**
The CertainType/(c2) analogue of `Xset_centralCommutator_isCoherent_of_frobenius` under the math-(A)
hypothesis `Z(H) ⊓ W₂ = 1` (`hA`): `W₁` still acts fixed-point-freely on `Zc = Z(H) ∩ H′`
(`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`), so the same central-`Zc` coherence
machinery
of `Xset_isCoherent_of_irreducible_X` applies. The three
irreducibility/coprimality
inputs are produced from the certain-type data: `hX` from
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`,
`hXne` from `Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X` (the `Set`→`Finset` form converted
by
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
  exact hyp.Xset_isCoherent_of_irreducible_X hyp.centralCommutator_le
    hyp.centralCommutator_subgroupOf_le_center hX hXne hp hp3 hHp hidxp

/-- **(6.8.1)/(6.8), L3 outer shell:** `X(Zc) ∪ Y` is coherent, given the (6.8.1) `τ₃` glue data
`ν`.  Mirrors `coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner` but
at
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
#2, and the `coherentUnion_of_glued_withDiagonal` docstring).  Here `D` carries those
cross-diagonals
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
`Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X` (which needs only `X`-irreducibility), with
the
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

end SibleyDadeHypothesis
end OddOrder.Peterfalvi.S08
