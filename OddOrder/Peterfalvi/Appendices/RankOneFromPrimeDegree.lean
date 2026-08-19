/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.RankOneAffineModel
import OddOrder.GroupTheory.PrimeDegreeTwoTransitive

/-!
# The rank-one hypothesis from a degree-`p` action of order `p(p-1)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (12), p. 113 (supporting App. II, Prop. 1).

A finite group of order `p·(p-1)` (`p` an odd prime) acting faithfully and
transitively on a set of cardinality `p` satisfies the full rank-one
hypothesis of Appendix II: the action is (sharply) two-transitive
(`OddOrder.GroupTheory.PrimeDegreeTwoTransitive`), a swap of two points
provides the distinguished involution `t`, two-point stabilizers vanish
(`D = 1`, so `Q = H` works), the point stabilizer has even order `p - 1`,
and the group has `2`-rank one.

Step (12) of the first case of the theorem of Suzuki applies this to
`N_G(R)/R` acting on the set `𝒜` of the `p` subgroups of order `p` of `R`
not contained in `T`.
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields

open MulAction OddOrder.GroupTheory

variable {G : Type*} {Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] [IsPretransitive G Ω] {p : ℕ}

/-- **The rank-one hypothesis for a degree-`p` action of order `p(p-1)`**
(`p` an odd prime): two-transitivity, a point-swapping involution `t`,
trivial two-point stabilizers (`Q = H`, `D = 1`), and `2`-rank one. -/
noncomputable def rankOneHypothesisOfCardEqMulPred (hp : p.Prime) (hp2 : p ≠ 2)
    (hΩ : Nat.card Ω = p) (hG : Nat.card G = p * (p - 1)) (a : Ω) :
    RankOneHypothesis G Ω := by
  classical
  -- a second point, and a swap.
  have hcard3 : 3 ≤ Nat.card Ω := by
    rw [hΩ]
    have h1 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  have hbex : ∃ b : Ω, b ≠ a := by
    have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne a
  set b := Classical.choose hbex with hbdef
  have hab : b ≠ a := Classical.choose_spec hbex
  have h2t := isMultiplyPretransitive_of_card_eq_mul_pred hp hΩ hG (G := G) (Ω := Ω)
  have hgex : ∃ g : G, g • a = b ∧ g • b = a := by
    obtain ⟨g, h1, h2⟩ := (is_two_pretransitive_iff.mp h2t) hab.symm hab
    exact ⟨g, h1, h2⟩
  set g := Classical.choose hgex with hgdef
  have hga : g • a = b := (Classical.choose_spec hgex).1
  have hgb : g • b = a := (Classical.choose_spec hgex).2
  -- `g` swaps `a` and `b`; its square fixes both, hence `g² = 1`.
  have hg2 : g ^ 2 = 1 := by
    refine eq_one_of_smul_eq_of_smul_eq hp hΩ hG (Ne.symm hab) ?_ ?_
    · rw [pow_two, mul_smul, hga, hgb]
    · rw [pow_two, mul_smul, hgb, hga]
  have hgne : g ≠ 1 := by
    intro h0
    rw [h0, one_smul] at hga
    exact hab hga.symm
  -- two-point stabilizers vanish.
  have hD : stabilizer G a ⊓ (stabilizer G a).map (MulAut.conj g).toMonoidHom
      = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, y, hy, rfl⟩
    rw [Subgroup.mem_bot]
    have hxa : (MulAut.conj g) y • a = a := hx1
    have hxb : (MulAut.conj g) y • b = b := by
      have h1 : (MulAut.conj g) y • b = (g * y * g⁻¹) • b := rfl
      have h2 : g⁻¹ • b = a := by
        rw [← hga, inv_smul_smul]
      rw [h1, mul_smul, mul_smul, h2, hy, hga]
    exact eq_one_of_smul_eq_of_smul_eq hp hΩ hG (Ne.symm hab) hxa hxb
  -- the stabilizer has order `p - 1`.
  have hstab : Nat.card ↥(stabilizer G a) = p - 1 := by
    have h1 := (stabilizer G a).card_mul_index
    rw [index_stabilizer_of_transitive, hΩ, hG] at h1
    have h2 : Nat.card ↥(stabilizer G a) * p = (p - 1) * p := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  refine
    { basept := a
      doubly_transitive := h2t
      faithful := inferInstance
      H := stabilizer G a
      Q := stabilizer G a
      D := stabilizer G a ⊓ (stabilizer G a).map (MulAut.conj g).toMonoidHom
      H_def := rfl
      t := g
      t_sq := hg2
      t_ne_one := hgne
      t_not_mem_H := ?_
      D_def := rfl
      Q_le_H := le_rfl
      Q_normal_in_H := ?_
      Q_inf_D_eq_bot := ?_
      Q_mul_D_eq_H := ?_
      Q_even := ?_
      D_odd := ?_
      two_rank_one := not_exists_elementaryAbelian_four hp hp2 hΩ hG }
  · intro hgH
    exact hab (hga ▸ hgH)
  · intro h hh x hx
    exact (stabilizer G a).mul_mem ((stabilizer G a).mul_mem hh hx)
      ((stabilizer G a).inv_mem hh)
  · rw [hD, inf_bot_eq]
  · rw [hD]
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      simp only [Subgroup.coe_bot, Set.mem_singleton_iff] at hz
      rw [hz]
      simpa using hy
    · intro hx
      exact ⟨x, hx, 1, by simp, mul_one x⟩
  · rw [hstab]
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    exact ⟨j, by omega⟩
  · rw [hD, Subgroup.card_bot]
    exact odd_one

end OddOrder.Peterfalvi.Appendices.NearFields
