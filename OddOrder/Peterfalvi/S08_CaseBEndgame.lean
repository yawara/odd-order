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

/-- **(6.8.3) case-(B) fixed-point-free bound** `(2|W₁|+1)² ≤ |H:Z|`.
In case (B), `W₁` acts fixed-point-freely on `H/H′` and on `H′/Z` (`Z = W₂ ≤ H′`); with all orders
odd this forces `|H:H′|, |H′:Z| ≥ 2|W₁|+1` (`two_mul_add_one_le_of_odd_dvd`), and the index
multiplicativity `|H:Z| = |H:H′|·|H′:Z|` for the chain `Z ≤ H′ ≤ H` gives the square bound.

Stated over the two intermediate index factors as oddness + `card_modEq_one` divisibility
hypotheses (`w1 ∣ idx − 1`, the fixed-point-free outputs) together with the index product, so the
group-theoretic inputs (the two fixed-point-free actions and the chain index identity) are isolated
as named obligations for the case-(B) (6.8.3) extension.  This supplies the `hfpf` hypothesis of
`false_of_w2_break_arith` (with `idxHZ = |H:Z|`).  Mirrors the *single*-factor case-(A) bound
`2|W₁| ≤ |Z| − 1` (`centralCommutator_card_subgroupOf_lower`), which only needs FPF on `Z` itself. -/
theorem two_mul_add_one_sq_le_of_two_fpf_factors {w1 idxHHc idxHcZ idxHZ : ℕ}
    (hw1odd : Odd w1)
    (h1odd : Odd idxHHc) (h1gt : 1 < idxHHc) (h1dvd : w1 ∣ idxHHc - 1)
    (h2odd : Odd idxHcZ) (h2gt : 1 < idxHcZ) (h2dvd : w1 ∣ idxHcZ - 1)
    (hprod : idxHZ = idxHHc * idxHcZ) :
    (2 * w1 + 1) ^ 2 ≤ idxHZ := by
  have h1 : 2 * w1 + 1 ≤ idxHHc := two_mul_add_one_le_of_odd_dvd hw1odd h1odd h1dvd h1gt
  have h2 : 2 * w1 + 1 ≤ idxHcZ := two_mul_add_one_le_of_odd_dvd hw1odd h2odd h2dvd h2gt
  calc (2 * w1 + 1) ^ 2 = (2 * w1 + 1) * (2 * w1 + 1) := by ring
    _ ≤ idxHHc * idxHcZ := Nat.mul_le_mul h1 h2
    _ = idxHZ := hprod.symm

/-- **(6.8.3) case-(B) FPF index bound over a subgroup chain.**  The group-theoretic bridge from the
abstract FPF bound `two_mul_add_one_sq_le_of_two_fpf_factors` to a concrete chain `W ≤ M ≤ K` in a
finite group `K` of odd order (the Sibley instance is `K = ↥H`, `M = H′ = [H,H]`, `W = W₂` with
`w1 = |W₁|`): all section indices `|K:M|`, `|M:W|` are odd (dividing the odd `|K|`), so the two
fixed-point-free divisibilities `w1 ∣ |K:M| − 1` and `w1 ∣ |M:W| − 1` (the `card_modEq_one` outputs)
force `|K:M|, |M:W| ≥ 2·w1 + 1` and `|K:W| = |K:M|·|M:W| ≥ (2·w1+1)²`.

Only the two fixed-point-free divisibilities and the two section-nontriviality facts (`1 < |K:M|`,
i.e. `M < K`; `1 < |M:W|`, i.e. `W < M`) remain as inputs — the oddness and the chain index identity
are discharged here from `Odd (Nat.card K)`. -/
theorem two_mul_add_one_sq_le_index_of_chain {K : Type*} [Group K] [Finite K]
    {W M : Subgroup K} (hWM : W ≤ M) (hKodd : Odd (Nat.card K))
    {w1 : ℕ} (hw1odd : Odd w1)
    (hMgt : 1 < M.index) (hWMgt : 1 < W.relIndex M)
    (h1dvd : w1 ∣ M.index - 1) (h2dvd : w1 ∣ W.relIndex M - 1) :
    (2 * w1 + 1) ^ 2 ≤ W.index := by
  -- every divisor of the odd `|K|` is odd
  have oddDvd : ∀ {a : ℕ}, a ∣ Nat.card K → Odd a := by
    intro a ha
    rcases ha with ⟨c, hc⟩
    rcases Nat.even_or_odd a with he | ho
    · exact absurd (hc ▸ he.mul_right c) (Nat.not_even_iff_odd.mpr hKodd)
    · exact ho
  -- `|M:W|` divides `|K|` (via `|K|` of the subgroup `M`)
  have hMcard : Nat.card ↥M ∣ Nat.card K := Subgroup.card_subgroup_dvd_card M
  have h1odd : Odd M.index := oddDvd M.index_dvd_card
  have h2odd : Odd (W.relIndex M) :=
    oddDvd (dvd_trans ((W.subgroupOf M).index_dvd_card) hMcard)
  -- chain index identity `|K:W| = |K:M|·|M:W|`
  have hprod : W.index = M.index * W.relIndex M := by
    rw [mul_comm]; exact (Subgroup.relIndex_mul_index hWM).symm
  exact two_mul_add_one_sq_le_of_two_fpf_factors hw1odd h1odd hMgt h1dvd h2odd hWMgt h2dvd hprod

/-- **(6.8.3) case-(B) arithmetic spine.**  The complete numeric reduction of the case-(B) (6.8.3)
contradiction: given the break-pair (5.6) bound `w1·hZ·(cZ−1) ≤ 2·w1²·d`, the [Is] Cor 2.30 bound
`d² ≤ hZ`, and the case-(B) fixed-point-free data on the two intermediate factors `|H:H′|`, `|H′:Z|`
(oddness + `card_modEq_one` divisibility + the chain index identity `hZ = |H:H′|·|H′:Z|`), one derives
`False`.  This composes the FPF index bound `two_mul_add_one_sq_le_of_two_fpf_factors` (giving the
`(2·w1+1)² ≤ hZ` input) with the break arithmetic core `false_of_w2_break_arith`.

Every hypothesis is labelled by its source, so the remaining case-(B) (6.8.3) extension reduces to
supplying these inputs from the Sibley data:

* `hbreak` — the (5.6) break-pair degree bound over the **mixed** `X` (`X` contains reducible
  certain-type columns, so the case-(A) all-irreducible break-pair engine `exists_coherentBreakPair`
  / `xSum_le_two_psi` does **not** transfer; a norm-`‖χ‖²`-weighted break is required);
* `hdsq` — [Is] Cor 2.30, valid because `Z = W₂` is central in `H`;
* `hcZ` — `|W₂| ≥ 2` (`W₂ ≠ 1`);
* the two FPF blocks — `W₁` acts fixed-point-freely on `H/H′` and on `H′/W₂`, and
  `|H:W₂| = |H:H′|·|H′:W₂|`.

Here `w1 = |W₁|`, `d = θ(1)`, `hZ = |H:W₂|`, `cZ = |W₂|`, `idxHHc = |H:H′|`, `idxHcZ = |H′:W₂|`. -/
theorem false_of_caseB_break_of_bounds {w1 d hZ cZ idxHHc idxHcZ : ℕ}
    (hw1 : 1 ≤ w1) (hw1odd : Odd w1) (hd : 1 ≤ d)
    (hdsq : d ^ 2 ≤ hZ) (hcZ : 2 ≤ cZ)
    (hbreak : w1 * hZ * (cZ - 1) ≤ 2 * w1 ^ 2 * d)
    (h1odd : Odd idxHHc) (h1gt : 1 < idxHHc) (h1dvd : w1 ∣ idxHHc - 1)
    (h2odd : Odd idxHcZ) (h2gt : 1 < idxHcZ) (h2dvd : w1 ∣ idxHcZ - 1)
    (hprod : hZ = idxHHc * idxHcZ) :
    False :=
  false_of_w2_break_arith hw1 hd hdsq hcZ
    (two_mul_add_one_sq_le_of_two_fpf_factors hw1odd h1odd h1gt h1dvd h2odd h2gt h2dvd hprod)
    hbreak

end OddOrder.Peterfalvi.S08
