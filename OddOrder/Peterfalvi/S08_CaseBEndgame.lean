/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBCoherence2

/-!
# Peterfalvi §8: Case (B) endgame — `S` is coherent (the (6.8.3) extension)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37, the **(6.8.3)** step of the (6.8) coherence capstone, in case (B)
(`Z = W₂`, `Z` central in `H`).

(6.8.3) is a *uniform* argument across cases (A)/(B): assuming `S` is not coherent, a break pair
`S₂ = {ψ, ψ̄} ⊆ S` with `X ∪ Y ⊆ S₁ ⊆ S` coherent but `S₁ ∪ S₂` not yields, via Theorem (5.6)
and the `X`-degree computation `∑_{χ∈X} χ(1)²/‖χ‖² = |W₁|·|H:Z|·(|Z|−1)`, the inequality

  `2·|W₁|²·d > |W₁|·|H:Z|·(|Z|−1)`,    (`ψ(1) = |W₁|·d`, `η₁(1) = |W₁|`)

which with [Is] Cor 2.30 (`d² ≤ |H:Z|`) gives `4|W₁|² > |H:Z|·(|Z|−1)²`.  The **only** difference
between the two cases is the final fixed-point-free arithmetic (04.8 L244):

* case (A): `W₁` acts FPF on the odd `Z`, so `|Z|−1 ≥ 2|W₁|`;
* case (B): `W₁` acts FPF on `H/H′` and on `H′/Z`, so `|H:Z| ≥ (2|W₁|+1)²`.

This file holds the case-(B) endgame.  Its first inhabitant is the case-(B) **arithmetic core**
`false_of_w2_break_arith`, the numeric contradiction mirroring case (A)'s
`false_of_centralCommutator_break_arith` (`S08_CoherenceCorePart2`) but driven by the case-(B)
FPF bound `(2|W₁|+1)² ≤ |H:Z|` instead of `2|W₁| ≤ |Z|−1`.

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` ("session 43 cont.²⁵+").
-/

namespace OddOrder.Peterfalvi.S08

/-- **(6.8.3) arithmetic core, case (B).**  The numeric contradiction closing the (6.8.3) extension
in case (B).  From the break-pair (5.6) bound `∑_{χ∈X} χ(1)²/‖χ‖² < 2ψ(1)η₁(1)` — i.e.
`|W₁|·|H:Z|·(|Z|−1) ≤ 2·|W₁|²·d` with `ψ(1) = |W₁|·d`, `η₁(1) = |W₁|` — together with [Is] Cor 2.30
`d² ≤ |H:Z|` (valid since `Z` is central in `H`) and the case-(B) fixed-point-free bound
`|H:Z| ≥ (2|W₁|+1)²` (`W₁` acts FPF on `H/H′` and `H′/Z`), one derives `|H:Z| ≤ 2|W₁|d ≤ 4|W₁|²`
(dropping the `|Z|−1 ≥ 1` factor, then `d ≤ 2|W₁|` from `d² ≤ |H:Z| ≤ 2|W₁|d`), contradicting
`(2|W₁|+1)² = 4|W₁|² + 4|W₁| + 1 ≤ |H:Z|`.

Here `w1 = |W₁|`, `d = θ(1)` (the degree of the `H`-source of `ψ`), `hZ = |H:Z|`, `cZ = |Z|`.
The hypothesis `2 ≤ cZ` holds because `Z ≠ 1` (so `|Z| ≥ 2`); only the factor `|Z|−1 ≥ 1` is used,
so unlike case (A) no lower bound on `|Z|` beyond nontriviality is needed (the FPF strength sits in
`hfpf` on `|H:Z|` instead).  Compare `false_of_centralCommutator_break_arith` (case A). -/
theorem false_of_w2_break_arith {w1 d hZ cZ : ℕ}
    (hw1 : 1 ≤ w1) (hd : 1 ≤ d) (hdsq : d ^ 2 ≤ hZ) (hcZ : 2 ≤ cZ)
    (hfpf : (2 * w1 + 1) ^ 2 ≤ hZ)
    (hbreak : w1 * hZ * (cZ - 1) ≤ 2 * w1 ^ 2 * d) : False := by
  -- the factor `|Z|−1` is at least `1`
  have hm1 : 1 ≤ cZ - 1 := by omega
  -- drop the `(cZ−1)` factor: `w1·hZ ≤ w1·hZ·(cZ−1) ≤ 2·w1²·d`
  have hwz : w1 * hZ ≤ 2 * w1 ^ 2 * d :=
    le_trans (le_mul_of_one_le_right (Nat.zero_le _) hm1) hbreak
  -- cancel `w1`: `hZ ≤ 2·w1·d`
  have hzle : hZ ≤ 2 * w1 * d := by
    refine Nat.le_of_mul_le_mul_left ?_ hw1
    calc w1 * hZ ≤ 2 * w1 ^ 2 * d := hwz
      _ = w1 * (2 * w1 * d) := by ring
  -- cancel `d`: `d ≤ 2·w1` (from `d² ≤ hZ ≤ 2·w1·d`)
  have hdle : d ≤ 2 * w1 := by
    refine Nat.le_of_mul_le_mul_right ?_ hd
    calc d * d = d ^ 2 := (sq d).symm
      _ ≤ hZ := hdsq
      _ ≤ 2 * w1 * d := hzle
  -- hence `hZ ≤ 2·w1·d ≤ 4·w1²`
  have hz4 : hZ ≤ 4 * w1 ^ 2 := by
    calc hZ ≤ 2 * w1 * d := hzle
      _ ≤ 2 * w1 * (2 * w1) := by gcongr
      _ = 4 * w1 ^ 2 := by ring
  -- contradiction: `(2·w1+1)² = 4·w1² + 4·w1 + 1 ≤ hZ ≤ 4·w1²`
  have hcontra : (2 * w1 + 1) ^ 2 ≤ 4 * w1 ^ 2 := le_trans hfpf hz4
  have hexp : (2 * w1 + 1) ^ 2 = 4 * w1 ^ 2 + 4 * w1 + 1 := by ring
  rw [hexp] at hcontra
  omega

end OddOrder.Peterfalvi.S08
