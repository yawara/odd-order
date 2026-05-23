/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite

/-!
# OddOrder.Isaacs.Ch06 — Frobenius Actions

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 6
"Frobenius Actions" (pp. 177-200) の Lean 化.

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 6A | Frobenius action の定義と equivalences | 6.1 – 6.7 | 進行中: 6.1 ✅, 6.3-6.6 未, 6.2/6.7 保留 |
| 6B | Frobenius complement Sylow 構造 | 6.8 – 6.21 | 未着手 |
| 6C | Frobenius kernel nilpotent + Thompson | 6.22 – 6.24 | 未着手 |

## 方針

mathlib カバレッジ薄 (~21%; `DihedralGroup`/`QuaternionGroup` の具体群以外は新規実装).
**`FrobeniusGroup` / `FrobeniusAction` は mathlib 完全未収載** — 本ファイルで一次定義.

設計: Isaacs 本文に従い **action ベース** (`IsFrobeniusAction A N` on `MulDistribMulAction A N`) を
中核に置き, subgroup-pair 版 (`IsFrobeniusGroup G N A`) は conjugation action で導出.

## 先行章依存

本ファイル §6A の本実装範囲 (6.1, 6.3, 6.4, 6.5, 6.6) は **Isaacs 先行章への依存なし**.
6.2 (Cor 3.28) と 6.7 (Schur-Zassenhaus) は Ch.3 完成後 / mathlib SZ 経由で別 commit.

ノート: [`notes/isaacs/ch06_frobenius_actions.md`](../../notes/isaacs/ch06_frobenius_actions.md)
-/

namespace OddOrder.Isaacs.Ch06

section /- 6A: Frobenius action basics (pp. 177-183) -/

/-! ### Definition of Frobenius action

Isaacs Defn (p. 177): an action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity
element of `A` fixes any nonidentity element of `N`. Equivalently `C_N(a) = 1` for all `1 ≠ a ∈ A`,
or `C_A(n) = 1` for all `1 ≠ n ∈ N`, or the action of `A` on `N \ {1}` is semiregular. -/

/-- An action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity element of `A`
fixes any nonidentity element of `N`.

Isaacs p. 177: "the action of `A` on `N` is said to be Frobenius if `n^a ≠ n` whenever `n ∈ N`
and `a ∈ A` are nonidentity elements." -/
def IsFrobeniusAction (A N : Type*) [Group A] [Group N] [MulDistribMulAction A N] : Prop :=
  ∀ a : A, a ≠ 1 → ∀ n : N, n ≠ 1 → a • n ≠ n

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

namespace IsFrobeniusAction

/-- The orbit of `1 ∈ N` under any `MulDistribMulAction` is `{1}`. (Structural, not Frobenius.) -/
theorem orbit_one : MulAction.orbit A (1 : N) = {1} := by
  ext n
  simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩; exact smul_one a
  · rintro rfl; exact ⟨1, smul_one 1⟩

/-- **Frobenius action ⇒ stabilizer trivial on nonidentity.** -/
theorem stabilizer_eq_bot (h : IsFrobeniusAction A N) {n : N} (hn : n ≠ 1) :
    MulAction.stabilizer A n = ⊥ := by
  ext a
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  refine ⟨fun hax => ?_, ?_⟩
  · by_contra ha; exact h a ha n hn hax
  · rintro rfl; exact one_smul A n

/-- **Frobenius action: `fixedBy N a = {1}` for `a ≠ 1`.** -/
theorem fixedBy_eq_singleton_one (h : IsFrobeniusAction A N) {a : A} (ha : a ≠ 1) :
    MulAction.fixedBy N a = {1} := by
  ext n
  simp only [MulAction.mem_fixedBy, Set.mem_singleton_iff]
  refine ⟨fun hn => ?_, ?_⟩
  · by_contra hne; exact h a ha n hne hn
  · rintro rfl; exact smul_one a

/-- **Isaacs Lemma 6.1**: a Frobenius action gives `|N| ≡ 1 (mod |A|)`.

Proof via Burnside's lemma:
`∑_{a ∈ A} |fixedBy N a| = (#orbits) * |A|`. For `a = 1` the fixed-set is all of `N` (size `|N|`),
and for `a ≠ 1` it is `{1}` (size 1). So `|N| + (|A| - 1) = (#orbits) * |A|`, hence
`|A| ∣ |N| - 1`. -/
theorem card_modEq_one [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Fintype.card N ≡ 1 [MOD Fintype.card A] := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient A N) := Quotient.fintype _
  -- Burnside.
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group A N
  -- Compute LHS: split `a = 1` from `a ≠ 1`.
  have h_one : Fintype.card (MulAction.fixedBy N (1 : A)) = Fintype.card N := by
    have h_eq : MulAction.fixedBy N (1 : A) = Set.univ := by
      ext n; simp
    calc Fintype.card (MulAction.fixedBy N (1 : A))
        = Fintype.card ((Set.univ : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = Fintype.card N := Fintype.card_congr (Equiv.Set.univ N)
  have h_other : ∀ a ∈ Finset.univ.erase (1 : A),
      Fintype.card (MulAction.fixedBy N a) = 1 := by
    intro a ha
    have ha_ne : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have h_eq := fixedBy_eq_singleton_one h ha_ne
    calc Fintype.card (MulAction.fixedBy N a)
        = Fintype.card (({1} : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = 1 := by simp
  have hLHS : ∑ a : A, Fintype.card (MulAction.fixedBy N a)
            = Fintype.card N + (Fintype.card A - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : A)), h_one,
        Finset.sum_congr rfl h_other, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, add_comm]
  rw [hLHS] at hburn
  -- Now: |N| + (|A| - 1) = (#orbits) * |A|, so |A| ∣ |N| - 1.
  haveI : Nonempty (MulAction.orbitRel.Quotient A N) := ⟨⟦1⟧⟩
  set k := Fintype.card (MulAction.orbitRel.Quotient A N)
  set a := Fintype.card A
  set n := Fintype.card N
  have ha_pos : 0 < a := Fintype.card_pos
  have hn_pos : 0 < n := Fintype.card_pos
  have hk_pos : 0 < k := Fintype.card_pos
  -- |N| - 1 = a * (k - 1).
  have hdvd : a ∣ n - 1 := by
    refine ⟨k - 1, ?_⟩
    rw [mul_comm a (k - 1), tsub_mul, one_mul]
    omega
  exact ((Nat.modEq_iff_dvd' hn_pos).mpr hdvd).symm

/-- Corollary of Lemma 6.1: a Frobenius action implies `|N|` and `|A|` are coprime. -/
theorem coprime_card [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Nat.Coprime (Fintype.card N) (Fintype.card A) := by
  unfold Nat.Coprime
  rw [(card_modEq_one h).gcd_eq, Nat.gcd_one_left]

end IsFrobeniusAction

end

end OddOrder.Isaacs.Ch06
