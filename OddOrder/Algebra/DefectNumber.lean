/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.DefectGroup

/-!
# The defect of a block

A defect group of a `G`-fixed idempotent is a `p`-group (`isPGroup_of_isDefectGroup`), so its
order is `p^d` for a well-defined `d`: the **defect**.  Since all defect groups of a block are
conjugate, `d` depends only on the block — that is `defect_eq_of_isDefectGroup` below, stated with
the conjugacy as a hypothesis so that it applies both to the abstract setting of `DefectGroup` and
to the group-algebra one (`OddOrder.GroupAlgebra.exists_conj_eq_of_isDefectGroup`).

The defect is what the *height* of an ordinary character is measured against:
`ν(χ(1)) = ν(|G|) - d(B) + ht(χ)`.

## Main definitions

* `OddOrder.GAlgebra.defectGroup` — a chosen defect group
* `OddOrder.GAlgebra.defect` — `d`, the exponent of `p` in its order

## Main results

* `OddOrder.GAlgebra.card_defectGroup` — `|D| = p^d`
* `OddOrder.GAlgebra.card_eq_of_isDefectGroup` — any defect group has order `p^d`
-/

namespace OddOrder.GAlgebra

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {A : Type*} [Ring A] [MulSemiringAction G A] {p : ℕ}

/-- A chosen defect group of a `G`-fixed element. -/
noncomputable def defectGroup {b : A} (hb : ∀ g : G, g • b = b) : Subgroup G :=
  (exists_isDefectGroup hb).choose

theorem isDefectGroup_defectGroup {b : A} (hb : ∀ g : G, g • b = b) :
    IsDefectGroup b (defectGroup hb) := (exists_isDefectGroup hb).choose_spec

/-- **The defect** `d`: the exponent of `p` in the order of a defect group. -/
noncomputable def defect (p : ℕ) {b : A} (hb : ∀ g : G, g • b = b) : ℕ :=
  (Nat.card ↥(defectGroup hb)).factorization p

/-- **`|D| = p^d`** for the chosen defect group. -/
theorem card_defectGroup (hp : p.Prime)
    (hinv : ∀ n : ℕ, ¬ p ∣ n → ∃ v : A, (∀ g : G, g • v = v) ∧ (n • (1 : A)) * v = 1)
    {b : A} (hb : ∀ g : G, g • b = b) :
    Nat.card ↥(defectGroup hb) = p ^ defect p hb := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ :=
    (isPGroup_of_isDefectGroup hp hinv (isDefectGroup_defectGroup hb)).exists_card_eq
  rw [defect, hn, hp.factorization_pow, Finsupp.single_eq_same]

/-- **Every defect group has order `p^d`.**  All defect groups of a block are conjugate, and
conjugation preserves the order. -/
theorem card_eq_of_isDefectGroup (hp : p.Prime)
    (hinv : ∀ n : ℕ, ¬ p ∣ n → ∃ v : A, (∀ g : G, g • v = v) ∧ (n • (1 : A)) * v = 1)
    {b : A} (hb : ∀ g : G, g • b = b)
    (hconj : ∀ D D' : Subgroup G, IsDefectGroup b D → IsDefectGroup b D' →
      ∃ g : G, D = MulAut.conj g • D')
    {D : Subgroup G} (hD : IsDefectGroup b D) :
    Nat.card ↥D = p ^ defect p hb := by
  obtain ⟨g, hg⟩ := hconj D (defectGroup hb) hD (isDefectGroup_defectGroup hb)
  rw [hg, ← card_defectGroup hp hinv hb]
  exact Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) (defectGroup hb)).toEquiv.symm

end OddOrder.GAlgebra
