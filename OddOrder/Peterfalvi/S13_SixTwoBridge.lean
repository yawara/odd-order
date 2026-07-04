/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core
import OddOrder.Peterfalvi.S08_SixTwoGeneral

/-!
# Peterfalvi §11 bridge to the general (6.2) index bound (the h56 routine pins)

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §11,
(11.3)/(11.4) via the general (6.2)/(6.3).

This leaf discharges the *routine pins* of the h56 producer
`exists_source_index_le_two_psi_of_break` (`S08_SixTwoGeneral`, issue 2022) in the concrete
§10/§11 context `S12.Hypothesis M` (type III/IV/V maximal `M` with the (8.15) Dade data on
`A₀(M)`, kernel `K = M' = (derivedInG M).subgroupOf M`):

* `mderivSharp_subset_A0` — **`hKsupp`**: `(M')^# ⊆ A₀(M)` inside `M`.  By
  `typePA_eq_sharpSubgroup_derivedInG`, Peterfalvi's `A(M)` is *exactly* `(M')^#`, and
  `A₀(M) = A(M) ∪ V^M ⊇ A(M)`.
* `one_notMem_A0` — **`h1A`**: `1 ∉ A₀(M)` (`S04.Hypothesis.ne_one`, `A₀ ⊆ G^#`).
* `inducedFamily_eq_inducedKernelFamily_bot` — the §10 family `S` (`S12.inducedFamily`,
  already pinned in `Sset`) **is** the general kernel-filter family at `X = ⊥`, so the
  `S08_SixTwoGeneral` layer (orthogonality/norms/real-freeness/B2/producer) applies verbatim
  to the §11 family; the §11 filtration `S(X)` is `inducedKernelFamily K X`.
* `card_odd_of_isMinimalSimpleOdd` — **`hodd`**: `|M|` is odd in the minimal-simple-odd ambient.

With these, the h56 producer for `hyp : S12.Hypothesis M` needs only the **anchor** and the
**(5.2.d) decomposition data** (grid-backed, issue 2022) — see
`Hypothesis.exists_source_index_le_two_psi` below for the fully-pinned form.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory
open OddOrder.GroupTheory
open scoped FiniteInduce

variable {G : Type*} [Group G] {M : Subgroup G}

namespace Hypothesis

/-- **`hKsupp` pin: `(M')^# ⊆ A₀(M)` inside `M`.**  Peterfalvi's type-`P` support satisfies
`A(M) = (M')^#` (`typePA_eq_sharpSubgroup_derivedInG`) and `A₀(M) = A(M) ∪ V^M ⊇ A(M)`, so a
nonidentity element of `M' = (derivedInG M).subgroupOf M` lies in the Dade support.  This is
the `hKsupp` input of the h56 producer: member differences of the induced family vanish off
`(M')^#`, hence are `A₀`-supported. -/
theorem mderivSharp_subset_A0 (hyp : Hypothesis M) :
    ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 → x ∈ hyp.A0 := by
  intro x hxK hx1
  simp only [A0, OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  refine Set.mem_union_left _ ?_
  rw [typePA_eq_sharpSubgroup_derivedInG]
  refine ⟨Subgroup.mem_subgroupOf.mp hxK, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hcoe
  exact hx1 (by ext; exact hcoe)

/-- **`h1A` pin: `1 ∉ A₀(M)`** (`S04.Hypothesis.ne_one`: the Dade support avoids the
identity). -/
theorem one_notMem_A0 (hyp : Hypothesis M) : (1 : ↥M) ∉ hyp.A0 := by
  haveI := hyp.finiteG
  intro h
  exact hyp.dadeData.dade.ne_one (a := ((1 : ↥M) : G)) h (OneMemClass.coe_one M)

/-- **`hodd` pin: `|M|` is odd** in the minimal-simple-odd ambient (`|M| ∣ |G|`). -/
theorem card_odd_of_isMinimalSimpleOdd [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (_hyp : Hypothesis M) : Odd (Nat.card ↥M) :=
  hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)

end Hypothesis

/-- **The §10 family `S` is the general kernel-filter family at `X = ⊥`**: the `⊥`-kernel
condition is vacuous (`1 ∈ Ker θ` always), so `S12.inducedFamily M` (the pinned `Sset`) equals
`S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥`.  Through this identification the
whole `S08_SixTwoGeneral` layer (family structure, B2, the h56 producer) applies to the §11
family, with the §11 filtration `S(X)` given by `inducedKernelFamily K X`. -/
theorem inducedFamily_eq_inducedKernelFamily_bot [Finite G] :
    inducedFamily M = OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
  ext φ
  constructor
  · rintro ⟨θ, hθne, rfl⟩
    refine ⟨θ, hθne, ?_, rfl⟩
    intro x hx
    have hx1 : x = 1 := by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx
      ext
      exact congrArg Subtype.val hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1]
    rfl
  · rintro ⟨θ, hθne, -, rfl⟩
    exact ⟨θ, hθne, rfl⟩

namespace Hypothesis

open scoped FiniteInduce in
/-- **The h56 producer, fully pinned to the §10/§11 context** (`S12.Hypothesis M`): Peterfalvi's
(6.2) break index bound `|M':A'| − 1 ≤ 2ψ(1)` over the genuine Dade data
(`hyp.dadeData.dade` on `A₀(M)`, `hyp.hconj`), kernel `K = M' = (derivedInG M).subgroupOf M`,
with the routine pins discharged (`mderivSharp_subset_A0`, `one_notMem_A0`,
`card_odd_of_isMinimalSimpleOdd`).  The remaining hypotheses are exactly the issue-2022
obligations: the **anchor** (an irreducible degree-`|M:M'|` member of `S(A')`, from the
`W₁`-action), `S(B)`-nonemptiness, and the **(5.2.d) decomposition data** (grid-backed).

The conclusion is the `h56` oracle shape of
`six_three_of_six_two_oracle`/`six_two_general` (`S08_Theorem62_63_Standalone`) at
`SOf X := inducedKernelFamily K X`, `τ := hyp.tau`, `A₀ := hyp.A0`. -/
theorem exists_source_index_le_two_psi
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {A' B : Subgroup ↥M} [A'.Normal]
    (hanchor : ∃ χ₁ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) A',
      IsIrreducibleCharacter χ₁ ∧ χ₁ 1 = (((derivedInG M).subgroupOf M).index : ℂ))
    (hSBne : (OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) B).Nonempty)
    (hdatum : ∀ (S₁ : Set (ClassFunction ↥M ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A' ∪
        OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj))
        S₁ hyp.A0),
      ∀ (ψ : ClassFunction ↥M ℂ),
        ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
        ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥M ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj))
        (S₁ ∪ {ψ, ψ.conj}) hyp.A0) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
            (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) ψ (a • χ₁),
        Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
              (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ)
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A')
      hyp.A0))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
      hyp.A0)) :
    ∃ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      (↑(B.subgroupOf ((derivedInG M).subgroupOf M)) :
          Set ↥((derivedInG M).subgroupOf M)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) ∧
      (Nat.card (↥((derivedInG M).subgroupOf M) ⧸
          A'.subgroupOf ((derivedInG M).subgroupOf M)) : ℝ) - 1 ≤
        2 * (ClassFunction.induce ((derivedInG M).subgroupOf M)
          (θ : ClassFunction
            ↥((derivedInG M).subgroupOf M) ℂ) 1).re := by
  haveI := hyp.finiteG
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  exact OddOrder.Peterfalvi.S08.exists_source_index_le_two_psi_of_break
    hyp.dadeData.dade hyp.hconj (hyp.card_odd_of_isMinimalSimpleOdd hG)
    hyp.mderivSharp_subset_A0 hyp.one_notMem_A0 hanchor hSBne hdatum hAcoh hBncoh

end Hypothesis

end OddOrder.Peterfalvi.S12
