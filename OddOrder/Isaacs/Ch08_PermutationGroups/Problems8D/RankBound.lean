/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import OddOrder.Isaacs.Ch08_PermutationGroups.Subdegrees

/-!
# Isaacs Problem 8D.3 (p. 269) — rank と最大 subdegree による位数の評価

`G` が rank `r` の推移置換群で最大 subdegree が `n` なら, `|G|` は `r` と `n` だけで
決まる量で上から抑えられる。ここでは具体的に **`|G| ≤ (r · n)!`** を示す。

rank は点安定化群 `G_α` の `Ω` 上の軌道 (= suborbit) の個数
`Nat.card (orbitRel.Quotient ↥(stabilizer G α) Ω)` として扱う (Isaacs の定義と一致)。

## 証明の流れ

* `Ω` は `G_α`-軌道の直和 (`MulAction.selfEquivSigmaOrbits`) で, 軌道は `r` 個,
  それぞれ長さ `≤ n` なので `|Ω| ≤ r · n`。
* 作用は忠実なので `G ↪ Sym(Ω)`, つまり `|G| ≤ |Ω|! ≤ (r · n)!`。

## Main results

- `card_le_rank_mul_max_subdegree` — `|Ω| ≤ r · n`。
- `card_le_factorial_rank_mul_max_subdegree` — **Problem 8D.3** 本体 `|G| ≤ (r · n)!`。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problem 8D.3 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- 軌道が `r` 個でそれぞれ長さ `≤ n` なら `|Ω| ≤ r · n`。 -/
theorem card_le_rank_mul_max_subdegree [Finite Ω] (α : Ω) {r n : ℕ}
    (hr : Nat.card (orbitRel.Quotient ↥(stabilizer G α) Ω) = r)
    (hn : ∀ γ : Ω, Set.ncard (orbit ↥(stabilizer G α) γ) ≤ n) :
    Nat.card Ω ≤ r * n := by
  classical
  have : Fintype (orbitRel.Quotient ↥(stabilizer G α) Ω) := Fintype.ofFinite _
  have hsigma : Nat.card Ω =
      ∑ ω : orbitRel.Quotient ↥(stabilizer G α) Ω,
        Nat.card ↥(orbit ↥(stabilizer G α) ω.out) := by
    rw [Nat.card_congr (selfEquivSigmaOrbits ↥(stabilizer G α) Ω), Nat.card_sigma]
  have hbound : ∀ ω : orbitRel.Quotient ↥(stabilizer G α) Ω,
      Nat.card ↥(orbit ↥(stabilizer G α) ω.out) ≤ n := by
    intro ω
    rw [Nat.card_coe_set_eq]
    exact hn _
  calc Nat.card Ω
      = ∑ ω : orbitRel.Quotient ↥(stabilizer G α) Ω,
          Nat.card ↥(orbit ↥(stabilizer G α) ω.out) := hsigma
    _ ≤ (Finset.univ : Finset (orbitRel.Quotient ↥(stabilizer G α) Ω)).card * n :=
        Finset.sum_le_card_nsmul _ _ _ fun ω _ => hbound ω
    _ = r * n := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hr]

/-- **Isaacs Problem 8D.3** (p. 269)。rank `r` で最大 subdegree が `n` の推移置換群は
`|G| ≤ (r · n)!` を満たす — すなわち `|G|` は `r` と `n` の関数で抑えられる。

忠実な作用なので `G ↪ Sym(Ω)` であり, `|Ω| ≤ r · n` (上の補題) から従う。 -/
theorem card_le_factorial_rank_mul_max_subdegree [Finite Ω] [FaithfulSMul G Ω]
    (α : Ω) {r n : ℕ}
    (hr : Nat.card (orbitRel.Quotient ↥(stabilizer G α) Ω) = r)
    (hn : ∀ γ : Ω, Set.ncard (orbit ↥(stabilizer G α) γ) ≤ n) :
    Nat.card G ≤ Nat.factorial (r * n) := by
  classical
  have hΩ : Nat.card Ω ≤ r * n := card_le_rank_mul_max_subdegree α hr hn
  have hinj : Function.Injective (MulAction.toPermHom G Ω) := by
    intro a b hab
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun γ => ?_
    exact congrArg (fun (f : Equiv.Perm Ω) => f γ) hab
  calc Nat.card G ≤ Nat.card (Equiv.Perm Ω) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.factorial (Nat.card Ω) := Nat.card_perm
    _ ≤ Nat.factorial (r * n) := Nat.factorial_le hΩ

end -- Problem 8D.3

end OddOrder.Isaacs.Ch08
