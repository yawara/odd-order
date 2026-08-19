/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality

/-!
# The `p`-defect of a conjugacy class

Navarro writes `d(K)` for the `p`-part of the centraliser order of a class `K`:
`|C_G(x_K)|_p = p^{d(K)}`.  Since `|K| · |C_G(x_K)| = |G|`, this is the same as saying

`|K|_p = p^{a - d(K)}`,  where `p^a = |G|_p`,

which is the normalisation appearing in Navarro (4.19): the quantity `|Ω_{K,L}|/|K|` lies in the
valuation ring because the only obstruction is the `p`-part of `|K|`.

## Main definitions

* `OddOrder.GroupTheory.classDefect`

## Main results

* `OddOrder.GroupTheory.classDefect_add_factorization_conjugacyClassSize` —
  `d(K) + ν_p(|K|) = ν_p(|G|)`
-/

namespace OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- **The `p`-defect of a conjugacy class**: `|C_G(x_K)|_p = p^{d(K)}`. -/
noncomputable def classDefect (p : ℕ) (C : ConjClasses G) : ℕ :=
  (Nat.card (Subgroup.centralizer ({C.out} : Set G))).factorization p

set_option backward.isDefEq.respectTransparency false in
/-- **`d(K) + ν_p(|K|) = ν_p(|G|)`.**  Immediate from `|K| · |C_G(x_K)| = |G|`. -/
theorem classDefect_add_factorization_conjugacyClassSize (C : ConjClasses G) :
    classDefect p C + (conjugacyClassSize C).factorization p
      = (Nat.card G).factorization p := by
  have hmk : ConjClasses.mk C.out = C := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  have hmul : conjugacyClassSize C * Nat.card (Subgroup.centralizer ({C.out} : Set G))
      = Nat.card G := by
    have h := conjugacyClassSize_mk_mul_card_centralizer (G := G) C.out
    rwa [hmk] at h
  have hsize : conjugacyClassSize C ≠ 0 := by
    rw [conjugacyClassSize]
    have : Nonempty ↥C.carrier := ⟨⟨C.out, ConjClasses.mem_carrier_iff_mk_eq.mpr hmk⟩⟩
    exact Nat.card_ne_zero.mpr ⟨inferInstance, Set.Finite.to_subtype (Set.toFinite _)⟩
  have hcent : Nat.card (Subgroup.centralizer ({C.out} : Set G)) ≠ 0 := Nat.card_pos.ne'
  rw [classDefect, ← hmul, Nat.factorization_mul hsize hcent]
  simp [add_comm]

/-- **`|K|_p · p^{d(K)} = |G|_p`.** -/
theorem ordProj_conjugacyClassSize_mul_pow_classDefect (C : ConjClasses G) :
    ordProj[p] (conjugacyClassSize C) * p ^ classDefect p C = ordProj[p] (Nat.card G) := by
  rw [← pow_add, add_comm, classDefect_add_factorization_conjugacyClassSize]

end OddOrder.GroupTheory
