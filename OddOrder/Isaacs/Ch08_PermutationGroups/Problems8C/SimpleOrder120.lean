/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# Isaacs Problems 8C (pp. 256–257) — 位数 120 の単純群は無い

**Problem 8C.1**: `A₆` は位数 120 の部分群をもたない。そこから位数 120 の群が単純に
なり得ないことを導く。

## Main results

- `card_ne_onetwenty_of_subgroup_alternating` — 6 点の交代群 `A₆` (位数 360) には
  位数 120 の部分群が無い。指数 3 なので **Isaacs Cor 1.3** から `360 ∣ 3! = 6`。
- `not_isSimpleGroup_of_card_eq_onetwenty` — 位数 120 の群は単純でない。
  Sylow 5-部分群の個数は `1` か `6` で, 単純性から `6`。その正規化群への剰余類作用は
  忠実なので `G ↪ S₆`, さらに符号写像の核が単純性から `G` 全体になり `G ↪ A₆`,
  前半に矛盾。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problems 8C (pp. 256-257) -/

/-! ### Problem 8C.1 — 位数 120 の群は単純でない -/

/-- **Isaacs Problem 8C.1** (p. 256), 前半。6 点集合の交代群 `A₆` (位数 360) には
位数 120 の部分群が無い。

証明: そのような `H` は指数 3 をもつが, `A₆` は単純 (mathlib
`alternatingGroup.isSimpleGroup`) なので **Isaacs Cor 1.3**
(`Ch01.card_dvd_factorial_of_simple_subgroup_index`) より `360 ∣ 3! = 6` となり矛盾。 -/
theorem card_ne_onetwenty_of_subgroup_alternating {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Nat.card α = 6) (H : Subgroup (alternatingGroup α)) :
    Nat.card H ≠ 120 := by
  intro hH
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hcard : Nat.card (alternatingGroup α) = 360 := by
    rw [nat_card_alternatingGroup, hα]
    norm_num [Nat.factorial]
  have : IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup (by omega)
  have hidx : H.index = 3 := by
    have h := Subgroup.card_mul_index H
    rw [hH, hcard] at h
    omega
  have hdvd := Ch01.card_dvd_factorial_of_simple_subgroup_index H (by omega)
  rw [hidx, hcard] at hdvd
  norm_num [Nat.factorial] at hdvd

variable {G : Type*} [Group G]

/-- 位数 120 の単純群があれば, Sylow `5`-部分群の正規化群は指数 `6` をもつ。

`n₅ = |Syl₅(G)|` は `|G| = 120` を割り, `n₅ ≡ 1 (mod 5)` (Sylow の第三定理) なので
`n₅ ∈ {1, 6}`。`n₅ = 1` なら Sylow `5`-部分群 `P` は正規で, 単純性から `P = ⊥` または
`P = ⊤`。`P = ⊥` は `5 ∣ [G : P] = 120` が `Sylow.not_dvd_index` に反し,
`P = ⊤` は `|G| = 5 ^ n` を強いるが `2 ∣ 120`。よって `n₅ = 6`。 -/
private lemma exists_normalizer_index_eq_six [IsSimpleGroup G] (hG : Nat.card G = 120) :
    ∃ N : Subgroup G, N.index = 6 := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := G)
  refine ⟨Subgroup.normalizer (P : Set G), ?_⟩
  -- `n₅` は `|G| = 120` を割り, `1 (mod 5)` に合同
  have hdvd : Nat.card (Sylow 5 G) ∣ 120 :=
    hG ▸ P.card_dvd_index.trans (P : Subgroup G).index_dvd_card
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 G
  have hmem : Nat.card (Sylow 5 G) ∈ Nat.divisors 120 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hcases : ∀ d ∈ Nat.divisors 120, d % 5 = 1 % 5 → d = 1 ∨ d = 6 := by decide
  rcases hcases _ hmem hmod with h1 | h6
  · -- `n₅ = 1`: `P` は正規, 単純性から `P = ⊥` か `P = ⊤` だがどちらも矛盾
    exfalso
    have hnormal : (P : Subgroup G).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact Subgroup.index_eq_one.mp (P.card_eq_index_normalizer.symm.trans h1)
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · have h5 : (5 : ℕ) ∣ (P : Subgroup G).index := by
        rw [hbot, Subgroup.index_bot, hG]; norm_num
      exact P.not_dvd_index h5
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 5) (G := (P : Subgroup G))).mp P.2
      rw [htop, Subgroup.card_top, hG] at hn
      have h2 : (2 : ℕ) ∣ 5 ^ n := hn ▸ (by norm_num : (2 : ℕ) ∣ 120)
      have := (Nat.prime_two).dvd_of_dvd_pow h2
      norm_num at this
  · exact P.card_eq_index_normalizer.symm.trans h6

/-- **Isaacs Problem 8C.1** (p. 256), 後半。位数 120 の群は単純でない。

証明: 単純と仮定する。Sylow `5`-部分群の正規化群 `N` は指数 `6` (上の補題)。
`N` の剰余類 `G ⧸ N` への作用の核は `N.normalCore ≤ N ≠ ⊤` なので単純性から `⊥`,
すなわち `G ↪ Sym(G ⧸ N)` (6 点の対称群)。符号写像との合成 `G →* ℤˣ` の核も正規で,
`⊥` なら `|G| ≤ 2` に反するから `⊤`, つまり像は `A₆` に入る。こうして `A₆` の中に
位数 120 の部分群ができ, 前半に矛盾する。

**Note** (Isaacs). 位数 120 の完全群は存在する: `SL(2, 5)`。 -/
theorem not_isSimpleGroup_of_card_eq_onetwenty (hG : Nat.card G = 120) :
    ¬ IsSimpleGroup G := by
  intro hsimp
  have := hsimp
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  classical
  obtain ⟨N, hN⟩ := exists_normalizer_index_eq_six hG
  have : Finite (G ⧸ N) := Subgroup.index_ne_zero_iff_finite.mp (by omega)
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  -- 剰余類作用は忠実
  set f : G →* Equiv.Perm (G ⧸ N) := MulAction.toPermHom G (G ⧸ N) with hf
  have hker : f.ker = ⊥ := by
    rw [hf, ← Subgroup.normalCore_eq_ker]
    rcases (Subgroup.normalCore_normal N).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (le_antisymm le_top (h ▸ N.normalCore_le)) (by
        intro hNtop; rw [hNtop, Subgroup.index_top] at hN; omega)
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  -- 符号写像との合成の核は `⊤`
  set s : G →* ℤˣ := (Equiv.Perm.sign (α := G ⧸ N)).comp f with hs
  have hsker : s.ker = ⊤ := by
    rcases (MonoidHom.normal_ker s).eq_bot_or_eq_top with h | h
    · exfalso
      have hinj : Function.Injective s := (MonoidHom.ker_eq_bot_iff s).mp h
      have := Nat.card_le_card_of_injective s hinj
      rw [hG] at this
      simp [Nat.card_eq_fintype_card] at this
    · exact h
  have hmem : ∀ g : G, f g ∈ alternatingGroup (G ⧸ N) := by
    intro g
    have : s g = 1 := by rw [← MonoidHom.mem_ker, hsker]; exact Subgroup.mem_top g
    simpa [hs, Equiv.Perm.mem_alternatingGroup] using this
  -- `G ↪ A₆` の像は位数 120 の部分群
  set f' : G →* alternatingGroup (G ⧸ N) := f.codRestrict _ hmem with hf'
  have hf'inj : Function.Injective f' := by
    intro a b hab
    exact hfinj (congrArg Subtype.val hab)
  refine card_ne_onetwenty_of_subgroup_alternating (α := G ⧸ N) ?_ f'.range ?_
  · rw [← Subgroup.index_eq_card, hN]
  · rw [← hG]
    exact (Nat.card_range_of_injective hf'inj)

end -- Problems 8C

end OddOrder.Isaacs.Ch08
