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

end OddOrder.Peterfalvi.S12
