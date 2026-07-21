/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibley

/-!
# Peterfalvi Appendix IV: the Feit–Sibley Theorem — supporting layer (pp. 145–150)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 145–150.  Support for the Theorem `feit_sibley_coherence`
(campaign issue 1054): the derived subgroups `S' = [S,S]` and `Q' = [Q,Q]` of the
"Hypotheses and Notation" block (p. 145) with their elementary group-theoretic
facts, feeding the Remark (`𝒮(Q')` is coherent), the reduction steps (1)–(3) and
the endgame (4)–(8) of pp. 146–150.

The statements live in the `Hypothesis` namespace of
`OddOrder.Peterfalvi.Appendices.FeitSibley` and extend the structure API of that
file.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-! ## The derived subgroups `S' = [S,S]` and `Q' = [Q,Q]` (p. 145) -/

/-- **`S' = [S,S]`** (p. 145, "Set `S' = [S,S]`"). -/
def Sder : Subgroup G := ⁅hyp.S, hyp.S⁆

/-- **`Q' = [Q,Q]`** (p. 145, "`Q' = [Q,Q]`"). -/
def Qder : Subgroup G := ⁅hyp.Q, hyp.Q⁆

theorem Sder_le_S : hyp.Sder ≤ hyp.S := by
  change ⁅hyp.S, hyp.S⁆ ≤ hyp.S
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact hyp.S.mul_mem (hyp.S.mul_mem (hyp.S.mul_mem hg hh) (hyp.S.inv_mem hg))
    (hyp.S.inv_mem hh)

theorem Qder_le_Q : hyp.Qder ≤ hyp.Q := by
  change ⁅hyp.Q, hyp.Q⁆ ≤ hyp.Q
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact hyp.Q.mul_mem (hyp.Q.mul_mem (hyp.Q.mul_mem hg hh) (hyp.Q.inv_mem hg))
    (hyp.Q.inv_mem hh)

theorem Sder_le_H : hyp.Sder ≤ hyp.H :=
  le_trans hyp.Sder_le_S hyp.S_le_H

theorem Qder_le_H : hyp.Qder ≤ hyp.H :=
  le_trans hyp.Qder_le_Q hyp.Q_le_H

/-- Conjugation by `h ∈ H` fixes `Q` as a set: `Q^h = Q` (both inclusions of the
elementwise normality `Q ⊴ H`). -/
theorem Q_map_conj_eq {h : G} (hh : h ∈ hyp.H) :
    hyp.Q.map (MulAut.conj h).toMonoidHom = hyp.Q := by
  apply le_antisymm
  · rintro _ ⟨x, hxQ, rfl⟩
    exact hyp.Q_normal_in_H h hh x hxQ
  · intro x hxQ
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    · have := hyp.Q_normal_in_H h⁻¹ (hyp.H.inv_mem hh) x hxQ
      simpa using this
    · simp [MulAut.conj]
      group

/-- **`Q' ⊴ H`** (elementwise): `H`-conjugation fixes `Q` (`Q_map_conj_eq`), hence
fixes `[Q,Q]` (`Subgroup.map_commutator`). -/
theorem Qder_conj_mem_of_mem_H {h : G} (hh : h ∈ hyp.H) {x : G}
    (hx : x ∈ hyp.Qder) : h * x * h⁻¹ ∈ hyp.Qder := by
  have hmap : hyp.Qder.map (MulAut.conj h).toMonoidHom = hyp.Qder := by
    change (⁅hyp.Q, hyp.Q⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom = ⁅hyp.Q, hyp.Q⁆
    rw [Subgroup.map_commutator, hyp.Q_map_conj_eq hh]
  rw [← hmap]
  exact ⟨x, hx, rfl⟩

theorem Sder_le_Q : hyp.Sder ≤ hyp.Q :=
  le_trans hyp.Sder_le_S hyp.S_le_Q

/-- `Q'.subgroupOf H ⊴ ↥H`, the `Subgroup.Normal` instance form of
`Qder_conj_mem_of_mem_H`. -/
theorem Qder_subgroupOf_H_normal : (hyp.Qder.subgroupOf hyp.H).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simpa using hyp.Qder_conj_mem_of_mem_H g.2 hx

/-- `𝒮(Q')` is closed under complex conjugation: `χ̄` is irreducible when `χ` is,
`Q₁ ⊄ Ker χ̄` iff `Q₁ ⊄ Ker χ` (conjugating the constancy equation), and likewise
`Q' ⊆ Ker` is preserved.  This is the conjugation-closure input for the coherence
of `𝒮(Q')` (Remark, p. 145). -/
theorem conj_mem_SsetOf_Qder [Finite G] {χ : ClassFunction ↥hyp.H ℂ}
    (hχ : χ ∈ hyp.SsetOf hyp.Qder) : χ.conj ∈ hyp.SsetOf hyp.Qder := by
  obtain ⟨⟨hirr, hker1⟩, hkerQ'⟩ := hχ
  refine ⟨⟨hirr.conj, ?_⟩, ?_⟩
  · -- `Q₁ ⊄ Ker χ̄` from `Q₁ ⊄ Ker χ`
    intro hall
    apply hker1
    intro x hxQ1
    have := hall x hxQ1
    rw [ClassFunction.conj_apply, ClassFunction.conj_apply] at this
    exact star_injective this
  · -- `Q' ⊆ Ker χ̄` from `Q' ⊆ Ker χ`
    intro x hxQ'
    rw [ClassFunction.conj_apply, ClassFunction.conj_apply, hkerQ' x hxQ']

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
