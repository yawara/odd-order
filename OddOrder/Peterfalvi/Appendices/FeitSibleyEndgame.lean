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

end OddOrder.Peterfalvi.Appendices.FeitSibley
