/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyXsetInduction

/-!
# Peterfalvi Appendix IV: the Feit–Sibley endgame (steps (4)–(8))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 148–150 (campaign issue 1054, endgame).  With `Q₁` a
non-abelian `p`-group, the two coherent families `𝒳 = 𝒮 − 𝒮(Z)` (reduction (3),
`xset_coherent_of_le_center_Q1`) and `𝒴 = 𝒮(Q')` (the Remark,
`ssetOf_Qder_coherent`) are combined into a single coherence of `𝒳 ∪ 𝒴`, which
then extends to `𝒮(S')` and, by reduction (2), to all of `𝒮`.

This file collects the self-contained pieces of the endgame; the coherence
assembly ((4) notation → (5) orthogonality → (6) `a ∣ λ ⟹ 𝒮` coherent → (7)
class-algebra congruence → (8) conclusion) is built on top.

* `x_eq_zero_or_x_one_of_norm_identity` — the (6) integer inequality core
  (p. 148): from the norm identity `1 + a² = (v,v) + a²(x−1)² + (m−1)x²a²` with
  `(v,v) ≥ 0`, `a ≥ 2` and `m ≥ 2`, the only solutions are `x = 0` or
  `x = 1 ∧ m = 2` (the latter reduces to the former by a sign swap of the `e'`).
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open scoped commutatorElement

/-! ## The (6) integer inequality core (p. 148) -/

/-- **Peterfalvi (6) integer core** (p. 148): writing `χ₁(1) = a·d` and expanding
`(Ind(χ₁ − aη₁), Ind(χ₁ − aη₁)) = 1 + a²` through the orthogonal decomposition
`Ind(χ₁ − aη₁) = v − a·e'₁ + λ·∑ e'ᵢ` (with `λ = a·x`) gives the integer identity
`1 + a² = (v,v) + a²(x−1)² + (m−1)·x²·a²`.  Since `(v,v) ≥ 0`, `a ≥ 2` (as
`𝒳 ∩ 𝒴 = ∅` forces `a > 1`) and `m ≥ 2`, the bracket `(x−1)² + (m−1)x²` is at
most `1 + 1/a² < 2`, hence at most `1`: the only integer solutions are `x = 0`
or `x = 1 ∧ m = 2`. -/
theorem x_eq_zero_or_x_one_of_norm_identity {a m x nvv : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hnvv : 0 ≤ nvv)
    (heq : 1 + a ^ 2 = nvv + a ^ 2 * (x - 1) ^ 2 + (m - 1) * x ^ 2 * a ^ 2) :
    x = 0 ∨ (x = 1 ∧ m = 2) := by
  -- `a² · ((x−1)² + (m−1)x²) ≤ 1 + a²`
  have hb : a ^ 2 * ((x - 1) ^ 2 + (m - 1) * x ^ 2) ≤ 1 + a ^ 2 := by nlinarith [heq, hnvv]
  -- integrality: the bracket is `≤ 1`
  have hk : (x - 1) ^ 2 + (m - 1) * x ^ 2 ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : 2 ≤ (x - 1) ^ 2 + (m - 1) * x ^ 2 := h
    nlinarith [hb, ha, h2, mul_nonneg (sq_nonneg a)
      (by linarith : (0 : ℤ) ≤ (x - 1) ^ 2 + (m - 1) * x ^ 2 - 2)]
  -- `(m−1)x² ≥ 0`, so `(x−1)² ≤ 1`, whence `0 ≤ x ≤ 2`
  have hmx : (0 : ℤ) ≤ (m - 1) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  have hx1 : (x - 1) ^ 2 ≤ 1 := by linarith [hk, hmx]
  have hxlo : 0 ≤ x := by nlinarith [hx1, sq_nonneg (x - 1)]
  have hxhi : x ≤ 2 := by nlinarith [hx1, sq_nonneg (x - 1)]
  interval_cases x
  · exact Or.inl rfl
  · -- `x = 1`: the bracket is `m − 1 ≤ 1`, so `m = 2`
    refine Or.inr ⟨rfl, ?_⟩
    have : m - 1 ≤ 1 := by nlinarith [hk]
    omega
  · -- `x = 2`: the bracket is `1 + 4(m−1) ≥ 5 > 1`, impossible
    exfalso
    nlinarith [hk, hm]

/-! ## The endgame central subgroup `Z = ⁅Q₁, Q₁⁆ ⊓ Z(Q₁)` (Peterfalvi (4), p. 147)

For a non-abelian `p`-group `Q₁` the subgroup `Z = [Q₁,Q₁] ∩ Z(Q₁)` is a
nontrivial `H`-invariant central subgroup of `Q₁`; it supplies the `Z` of
reduction (3) (`xset_coherent_of_le_center_Q1`), so `𝒳 = 𝒮 − 𝒮(Z)` is coherent. -/

namespace Hypothesis

variable {G : Type*} [Group G] (hyp : Hypothesis G)

/-- **The endgame central subgroup** `Z = ⁅Q₁, Q₁⁆ ⊓ C_G(Q₁)` (Peterfalvi (4)).
The intersection with the centralizer realises the `Z(Q₁)`-part: `Z ≤ Q₁` and `Z`
centralises `Q₁`, i.e. `Z ≤ Z(Q₁)`. -/
def endgameZ : Subgroup G := ⁅hyp.Q1, hyp.Q1⁆ ⊓ Subgroup.centralizer (hyp.Q1 : Set G)

/-- `⁅Q₁, Q₁⁆ ≤ Q₁`: a subgroup is closed under commutators. -/
theorem commutator_Q1_le_Q1 : ⁅hyp.Q1, hyp.Q1⁆ ≤ hyp.Q1 :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact hyp.Q1.mul_mem (hyp.Q1.mul_mem (hyp.Q1.mul_mem ha hb) (hyp.Q1.inv_mem ha))
      (hyp.Q1.inv_mem hb)

theorem endgameZ_le_Q1 : hyp.endgameZ ≤ hyp.Q1 := inf_le_left.trans hyp.commutator_Q1_le_Q1

/-- **`Z` centralises `Q₁`** (`Z ≤ Z(Q₁)`): `⁅z, y⁆ = 1` for `z ∈ Z`, `y ∈ Q₁`. -/
theorem endgameZ_centralizes {z : G} (hz : z ∈ hyp.endgameZ) {y : G} (hy : y ∈ hyp.Q1) :
    ⁅z, y⁆ = 1 := by
  have hyz : ⁅y, z⁆ = 1 :=
    (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hz.2) y hy
  have : Commute z y := (commutatorElement_eq_one_iff_commute.mp hyz).symm
  exact commutatorElement_eq_one_iff_commute.mpr this

/-- The `↥Q₁`-level commutator maps onto `⁅Q₁, Q₁⁆`. -/
theorem map_commutator_Q1 :
    (commutator ↥hyp.Q1).map hyp.Q1.subtype = ⁅hyp.Q1, hyp.Q1⁆ := by
  rw [commutator_def, Subgroup.map_commutator]
  simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **`Z ≠ ⊥`** for a non-abelian `p`-group `Q₁` (Peterfalvi (4)): the nontrivial
normal subgroup `[Q₁,Q₁]` of the `p`-group `Q₁` meets the centre nontrivially
(`IsPGroup.normal_inf_center_nontrivial`), and the injective `Q₁ ↪ G` carries the
nontriviality up to `Z`. -/
theorem endgameZ_ne_bot [Finite G] {p : ℕ} (hp : p.Prime) (hQ1p : IsPGroup p ↥hyp.Q1)
    (hnonab : ⁅hyp.Q1, hyp.Q1⁆ ≠ ⊥) : hyp.endgameZ ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `commutator ↥Q₁` is nontrivial, else `⁅Q₁,Q₁⁆ = ⊥`
  have hcomm_nt : Nontrivial (commutator ↥hyp.Q1) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hcbot
    exact hnonab (by rw [← hyp.map_commutator_Q1, hcbot, Subgroup.map_bot])
  -- `[Q₁,Q₁] ⊓ Z(Q₁) ≠ ⊥` in `↥Q₁`
  have hK : (commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1 ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    exact OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hQ1p hcomm_nt
  -- its `G`-image sits inside `Z` and is nontrivial (subtype injective)
  have hmaple : ((commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1).map hyp.Q1.subtype
      ≤ hyp.endgameZ := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzc, hzcent⟩ := Subgroup.mem_inf.mp hz
    refine ⟨?_, ?_⟩
    · exact hyp.map_commutator_Q1 ▸ Subgroup.mem_map_of_mem hyp.Q1.subtype hzc
    · refine Subgroup.mem_centralizer_iff_commutator_eq_one.mpr fun g hg => ?_
      have hcz : Commute (⟨g, hg⟩ : ↥hyp.Q1) z :=
        (Subgroup.mem_center_iff.mp hzcent) (⟨g, hg⟩ : ↥hyp.Q1)
      have hcomm : Commute g (hyp.Q1.subtype z) := by
        simpa using hcz.map hyp.Q1.subtype
      exact commutatorElement_eq_one_iff_commute.mpr hcomm
  have hmapne : ((commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1).map hyp.Q1.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]
    exact hK
  exact fun hbot => hmapne (le_bot_iff.mp (by rw [← hbot]; exact hmaple))

/-- **`Z` is `H`-invariant** (element form): `h · x · h⁻¹ ∈ Z` for `h ∈ H`,
`x ∈ Z`.  Both factors are `H`-invariant — `⁅Q₁,Q₁⁆` because `Q₁ ⊴ H`
(`Q1_map_conj_eq` + `map_commutator`), and `C_G(Q₁)` because conjugation permutes
`Q₁`. -/
theorem endgameZ_conj_mem_of_mem_H [Finite G] {h : G} (hh : h ∈ hyp.H)
    {x : G} (hx : x ∈ hyp.endgameZ) : h * x * h⁻¹ ∈ hyp.endgameZ := by
  obtain ⟨hxc, hxcent⟩ := hx
  refine ⟨?_, ?_⟩
  · -- `h·x·h⁻¹ ∈ ⁅Q₁,Q₁⁆`
    have hφ : Subgroup.map (MulAut.conj h).toMonoidHom ⁅hyp.Q1, hyp.Q1⁆ = ⁅hyp.Q1, hyp.Q1⁆ := by
      rw [Subgroup.map_commutator, hyp.Q1_map_conj_eq hh]
    have hmem : (MulAut.conj h) x ∈ ⁅hyp.Q1, hyp.Q1⁆ :=
      hφ ▸ Subgroup.mem_map_of_mem _ hxc
    simpa [MulAut.conj] using hmem
  · -- `h·x·h⁻¹ ∈ C_G(Q₁)`
    refine Subgroup.mem_centralizer_iff_commutator_eq_one.mpr fun y hy => ?_
    have hy' : h⁻¹ * y * h ∈ hyp.Q1 := by
      have := hyp.Q1_normal_in_H (hyp.H.inv_mem hh) hy
      simpa using this
    -- `x` commutes with `h⁻¹yh`; conjugating by `h` gives `hxh⁻¹` commutes with `y`
    have hxc' : ⁅h⁻¹ * y * h, x⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hxcent) (h⁻¹ * y * h) hy'
    have hc : Commute (h⁻¹ * y * h) x := commutatorElement_eq_one_iff_commute.mp hxc'
    have hcm := hc.map (MulAut.conj h).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcm
    have hyeq : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rw [hyeq] at hcm
    exact commutatorElement_eq_one_iff_commute.mpr hcm

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
