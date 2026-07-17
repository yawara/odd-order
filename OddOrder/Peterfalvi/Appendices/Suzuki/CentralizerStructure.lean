/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.InvertedProduct

/-!
# Peterfalvi Part II, Ch. I §1: Proposition 5 (`V = C_D(s)`, `W = C_D(H∩I)`)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §1, p. 101.

Proposition 5: `V = C_D(s)` and `W = C_D(H ∩ I)`, where `s` is the
distinguished involution (Prop 4(b)).

The inclusion `V ⊆ C_D(s)` follows from the uniqueness of the distinguished
pair `(s, r)` (conjugating the structure equation by `v ∈ V` gives another
valid pair `(sᵛ, rᵛ)`, hence `sᵛ = s`).  Equality then follows by counting:
`|D:V| = |K|` (the Lemma (a) applied to `(D, t)`), `|K| = |H∩I|` (Prop 3), and
`|H∩I| = |sᴰ| = |D:C_D(s)|` (orbit–stabilizer for `D` acting on `s` by
conjugation, `sᴰ = H∩I`).
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

open scoped Pointwise

/-! ## `V ⊆ C_D(s)` (p. 101) -/

/-- **Peterfalvi Part II, Ch. I Prop 5** (p. 101), first inclusion —
`V ⊆ C_D(s)`.  For `v ∈ V = C_D(t)`, conjugating the structure equation
`tst = r⁻¹tr` by `v` yields `t sᵛ t = (rᵛ)⁻¹ t rᵛ`; the pair `(sᵛ, rᵛ)`
satisfies the defining conditions, so by uniqueness `sᵛ = s`, i.e. `v`
centralizes `s`. -/
theorem V_le_centralizer_distinguishedInvolution :
    hyp.V ≤ hyp.D ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} := by
  intro v hv
  have hvD : v ∈ hyp.D := hyp.V_le_D hv
  have hvH : v ∈ hyp.H := hyp.D_le_H hvD
  have hvt : Commute v hyp.t := hyp.commute_t_of_mem_V hv
  have hv't : v⁻¹ * hyp.t = hyp.t * v⁻¹ := hvt.inv_left.eq
  have hvtv : v⁻¹ * hyp.t * v = hyp.t := by
    rw [mul_assoc, ← hvt.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  set s := hyp.distinguishedInvolution with hs
  set r := hyp.structureConjugator with hr
  have hsH : s ∈ hyp.H := hyp.distinguishedInvolution_mem_H
  have hs2 : s ^ 2 = 1 := hyp.distinguishedInvolution_sq
  have hs1 : s ≠ 1 := hyp.distinguishedInvolution_ne_one
  have hrQ : r ∈ hyp.Q := hyp.structureConjugator_mem_Q
  have hstr : hyp.t * s * hyp.t = r⁻¹ * hyp.t * r := hyp.structure_equation
  -- conjugated structure equation
  have hconj : hyp.t * (v⁻¹ * s * v) * hyp.t
      = (v⁻¹ * r * v)⁻¹ * hyp.t * (v⁻¹ * r * v) := by
    calc hyp.t * (v⁻¹ * s * v) * hyp.t
        = (hyp.t * v⁻¹) * s * (v * hyp.t) := by group
      _ = (v⁻¹ * hyp.t) * s * (hyp.t * v) := by rw [← hv't, hvt.eq]
      _ = v⁻¹ * (hyp.t * s * hyp.t) * v := by group
      _ = v⁻¹ * (r⁻¹ * hyp.t * r) * v := by rw [hstr]
      _ = (v⁻¹ * r⁻¹ * v) * (v⁻¹ * hyp.t * v) * (v⁻¹ * r * v) := by group
      _ = (v⁻¹ * r⁻¹ * v) * hyp.t * (v⁻¹ * r * v) := by rw [hvtv]
      _ = (v⁻¹ * r * v)⁻¹ * hyp.t * (v⁻¹ * r * v) := by
          have hinv : (v⁻¹ * r * v)⁻¹ = v⁻¹ * r⁻¹ * v := by
            rw [mul_inv_rev, mul_inv_rev, inv_inv]; group
          rw [hinv]
  -- (sᵛ, rᵛ) is a valid pair, so sᵛ = s
  have hsv2 : (v⁻¹ * s * v) ^ 2 = 1 := by
    rw [sq]
    calc (v⁻¹ * s * v) * (v⁻¹ * s * v) = v⁻¹ * (s * s) * v := by group
      _ = 1 := by rw [← sq, hs2]; group
  have hsvne : v⁻¹ * s * v ≠ 1 := by
    intro h
    apply hs1
    have h2 : v * (v⁻¹ * s * v) * v⁻¹ = v * 1 * v⁻¹ := by rw [h]
    rw [show v * (v⁻¹ * s * v) * v⁻¹ = s from by group,
      show v * 1 * v⁻¹ = 1 from by group] at h2
    exact h2
  have hrvQ : v⁻¹ * r * v ∈ hyp.Q := by
    have := hyp.Q_normal_in_H v⁻¹ (inv_mem hvH) r hrQ
    rwa [inv_inv] at this
  obtain ⟨hsv, -⟩ := hyp.eq_distinguishedPair_of_structure
    (mul_mem (mul_mem (inv_mem hvH) hsH) hvH) hsv2 hsvne hrvQ hconj
  -- hsv : v⁻¹ * s * v = s  ⟹  Commute v s
  have hcomm : v * s = s * v := by
    have h2 : v * (v⁻¹ * s * v) = v * s := by rw [hsv]
    rw [show v * (v⁻¹ * s * v) = s * v from by group] at h2
    exact h2.symm
  exact Subgroup.mem_inf.mpr ⟨hvD, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
