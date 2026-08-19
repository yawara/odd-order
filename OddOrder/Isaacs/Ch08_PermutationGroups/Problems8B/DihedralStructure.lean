/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8B.SmallSuborbits

/-!
# Isaacs Problem 8B.6 (p. 249) の結論 — `G ≅ D₂ₚ`

`|G_α| = 2` の原始置換群 `G` は, 奇素数 `p = |Ω|` の二面体群 `D₂ₚ` に同型。

数学的な中身 (`|Ω| = p` は奇素数, `Ω` に正則に作用する正規部分群 `K` が位数 `p` で
点安定化群の生成元 `t` がそれを反転する) は `SmallSuborbits.lean` で landing 済で,
本ファイルはそれを mathlib の `DihedralGroup p` へ橋渡しする。

## 二面体群の認識

橋渡しは特定の作用に依らない一般補題として書く (`dihedralHom` / `dihedralEquiv`):
群 `G` に位数 `n` の元 `y` と対合 `t` があって `t y t⁻¹ = y⁻¹`, `⟨y⟩ ⊔ ⟨t⟩ = G`,
`|G| = 2n` なら `DihedralGroup n ≃* G`。

`DihedralGroup n` の積は `r i * sr j = sr (j - i)` / `sr i * sr j = r (j - i)` なので,
対応は `r i ↦ y ^ i.val`, **`sr i ↦ t * y ^ i.val`** (`y ^ i.val * t` ではない)。
実際 `y^i t = t y^{-i}` から `(r i)(sr j) ↦ y^i t y^j = t y^{j-i}` となり `sr (j-i)` の
像に一致する。指数が `ZMod n` で well-defined なのは `orderOf y = n` から。

## Main results

- `dihedralHom` / `dihedralEquiv` — 二面体群の認識 (一般補題)。
- `nonempty_mulEquiv_dihedralGroup_of_card_stabilizer_eq_two` — **Problem 8B.6** の結論。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- 二面体群の認識 (一般補題) -/

variable {G : Type*} [Group G] {n : ℕ} {y t : G}

private lemma natCast_val_self [NeZero n] (i : ZMod n) : ((i.val : ℕ) : ZMod n) = i :=
  ZMod.natCast_rightInverse i

/-- `orderOf y = n` なら `y` の整数冪は指数の `ZMod n` での像だけで決まる。 -/
private lemma zpow_congr_of_orderOf (hy : orderOf y = n) {a b : ℤ}
    (h : (a : ZMod n) = (b : ZMod n)) : y ^ a = y ^ b := by
  rw [zpow_eq_zpow_iff_modEq, hy]
  exact (ZMod.intCast_eq_intCast_iff a b n).mp h

/-- `DihedralGroup n → G` の台となる写像。 -/
private def dihedralFun (y t : G) (n : ℕ) : DihedralGroup n → G
  | .r i => y ^ (i.val : ℤ)
  | .sr i => t * y ^ (i.val : ℤ)

/-- **二面体群の認識** (準同型部分)。位数 `n` の `y` と対合 `t` が `t y t⁻¹ = y⁻¹` を
満たすとき, `r i ↦ y ^ i.val`, `sr i ↦ t * y ^ i.val` は準同型 `DihedralGroup n →* G`。 -/
def dihedralHom [NeZero n] (hy : orderOf y = n) (ht : t * t = 1)
    (hconj : t * y * t⁻¹ = y⁻¹) : DihedralGroup n →* G where
  toFun := dihedralFun y t n
  map_one' := by
    change y ^ (((0 : ZMod n)).val : ℤ) = 1
    simp
  map_mul' := by
    -- `t` による共役は `y` の冪を反転する: `y^a t = t y^{-a}`。
    have hconjz : ∀ a : ℤ, t * y ^ a * t⁻¹ = y ^ (-a) := by
      intro a
      have h : (MulAut.conj t) (y ^ a) = ((MulAut.conj t) y) ^ a := map_zpow _ _ _
      simp only [MulAut.conj_apply] at h
      rw [h, hconj, inv_zpow, ← zpow_neg]
    have hyt : ∀ a : ℤ, y ^ a * t = t * y ^ (-a) := by
      intro a
      have h := hconjz (-a)
      rw [neg_neg] at h
      rw [← h]
      group
    -- 指数の加法性・減法性。
    have hadd : ∀ i j : ZMod n,
        y ^ (((i + j).val : ℕ) : ℤ) = y ^ ((i.val : ℕ) : ℤ) * y ^ ((j.val : ℕ) : ℤ) := by
      intro i j
      rw [← zpow_add]
      refine zpow_congr_of_orderOf hy ?_
      push_cast
      simp only [natCast_val_self]
    have hsub : ∀ i j : ZMod n,
        y ^ (((j - i).val : ℕ) : ℤ) = (y ^ ((i.val : ℕ) : ℤ))⁻¹ * y ^ ((j.val : ℕ) : ℤ) := by
      intro i j
      rw [← zpow_neg, ← zpow_add]
      refine zpow_congr_of_orderOf hy ?_
      push_cast
      simp only [natCast_val_self]
      ring
    rintro (i | i) (j | j)
    · change y ^ (((i + j).val : ℕ) : ℤ) = y ^ ((i.val : ℕ) : ℤ) * y ^ ((j.val : ℕ) : ℤ)
      exact hadd i j
    · change t * y ^ (((j - i).val : ℕ) : ℤ) = y ^ ((i.val : ℕ) : ℤ) * (t * y ^ ((j.val : ℕ) : ℤ))
      calc t * y ^ (((j - i).val : ℕ) : ℤ)
          = t * ((y ^ ((i.val : ℕ) : ℤ))⁻¹ * y ^ ((j.val : ℕ) : ℤ)) := by rw [hsub i j]
        _ = t * y ^ (-((i.val : ℕ) : ℤ)) * y ^ ((j.val : ℕ) : ℤ) := by rw [zpow_neg, mul_assoc]
        _ = y ^ ((i.val : ℕ) : ℤ) * t * y ^ ((j.val : ℕ) : ℤ) := by rw [hyt]
        _ = y ^ ((i.val : ℕ) : ℤ) * (t * y ^ ((j.val : ℕ) : ℤ)) := mul_assoc _ _ _
    · change t * y ^ (((i + j).val : ℕ) : ℤ) = t * y ^ ((i.val : ℕ) : ℤ) * y ^ ((j.val : ℕ) : ℤ)
      rw [hadd i j, mul_assoc]
    · change y ^ (((j - i).val : ℕ) : ℤ)
          = t * y ^ ((i.val : ℕ) : ℤ) * (t * y ^ ((j.val : ℕ) : ℤ))
      calc y ^ (((j - i).val : ℕ) : ℤ)
          = (y ^ ((i.val : ℕ) : ℤ))⁻¹ * y ^ ((j.val : ℕ) : ℤ) := hsub i j
        _ = t * t * (y ^ (-((i.val : ℕ) : ℤ)) * y ^ ((j.val : ℕ) : ℤ)) := by
              rw [ht, one_mul, zpow_neg]
        _ = t * (y ^ ((i.val : ℕ) : ℤ) * t) * y ^ ((j.val : ℕ) : ℤ) := by rw [hyt]; group
        _ = t * y ^ ((i.val : ℕ) : ℤ) * (t * y ^ ((j.val : ℕ) : ℤ)) := by group

lemma dihedralHom_r [NeZero n] (hy : orderOf y = n) (ht : t * t = 1)
    (hconj : t * y * t⁻¹ = y⁻¹) (i : ZMod n) :
    dihedralHom hy ht hconj (.r i) = y ^ (i.val : ℤ) := rfl

lemma dihedralHom_sr [NeZero n] (hy : orderOf y = n) (ht : t * t = 1)
    (hconj : t * y * t⁻¹ = y⁻¹) (i : ZMod n) :
    dihedralHom hy ht hconj (.sr i) = t * y ^ (i.val : ℤ) := rfl

/-- **二面体群の認識**。有限群 `G` に位数 `n` の元 `y` と対合 `t` があって
`t y t⁻¹ = y⁻¹`, `⟨y⟩ ⊔ ⟨t⟩ = G`, `|G| = 2n` なら `DihedralGroup n ≃* G`。

`dihedralHom` の像は `y` と `t` を含むので `⟨y⟩ ⊔ ⟨t⟩ = ⊤` から全射。
`|DihedralGroup n| = 2n = |G|` なので全単射。 -/
noncomputable def dihedralEquiv [NeZero n] [Finite G] (hy : orderOf y = n) (ht : t * t = 1)
    (hconj : t * y * t⁻¹ = y⁻¹) (hgen : Subgroup.zpowers y ⊔ Subgroup.zpowers t = ⊤)
    (hcard : Nat.card G = 2 * n) : DihedralGroup n ≃* G := by
  refine MulEquiv.ofBijective (dihedralHom hy ht hconj)
    ((Nat.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩)
  · -- 全射: 像は `y` と `t` を含む
    rw [← MonoidHom.range_eq_top]
    refine eq_top_iff.mpr (hgen ▸ sup_le (Subgroup.zpowers_le.mpr ?_)
      (Subgroup.zpowers_le.mpr ?_))
    · refine ⟨.r ((1 : ℕ) : ZMod n), ?_⟩
      have h1 : y ^ (((((1 : ℕ) : ZMod n)).val : ℕ) : ℤ) = y ^ (1 : ℤ) :=
        zpow_congr_of_orderOf hy (by push_cast; simp only [natCast_val_self])
      rw [dihedralHom_r, h1, zpow_one]
    · exact ⟨.sr 0, by rw [dihedralHom_sr]; simp⟩
  · rw [DihedralGroup.nat_card, hcard]

end -- 二面体群の認識

section /- Problem 8B.6 の結論 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **Isaacs Problem 8B.6** (p. 249) 🎉 完結: 点安定化群が `Ω ∖ {α}` に長さ 2 の軌道を
もつ原始置換群 `G` は, **奇素数 `p = |Ω|` の二面体群 `D₂ₚ` に同型**。

`SmallSuborbits.lean` の構造データ (正則正規部分群 `K` = 位数 `p`, その反転を与える
点安定化群の生成元 `t`) を `dihedralEquiv` に載せるだけ。`K` は素数位数なので
任意の非自明元 `y` が生成し `orderOf y = p`, したがって
`⟨y⟩ ⊔ ⟨t⟩ = K ⊔ G_α = ⊤` かつ `|G| = |Ω| · |G_α| = 2p`。 -/
theorem nonempty_mulEquiv_dihedralGroup_of_card_stabilizer_eq_two [Finite G] [Finite Ω]
    [FaithfulSMul G Ω] [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) :
    Nonempty (G ≃* DihedralGroup (Nat.card Ω)) := by
  classical
  have hp : (Nat.card Ω).Prime := prime_card_of_card_stabilizer_eq_two hcard
  have : Fact (Nat.card Ω).Prime := ⟨hp⟩
  have : NeZero (Nat.card Ω) := ⟨hp.pos.ne'⟩
  obtain ⟨K, t, hKnormal, hKΩ, -, hsup, hzt, htord, hinvK⟩ :=
    exists_inverting_involution_of_card_stabilizer_eq_two hcard
  -- `K` は素数位数なので位数 `|Ω|` の元 `y` で生成される。
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) (Nat.card Ω) (hKΩ ▸ dvd_rfl)
  have hyord : orderOf (y : G) = Nat.card Ω := by rw [← hy, Subgroup.orderOf_coe]
  have hyK : Subgroup.zpowers (y : G) = K :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2)
      (by rw [Nat.card_zpowers, hyord, hKΩ])
  -- `t` は対合で `y` を反転する。
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htord, pow_two] at this
  have hconj : t * (y : G) * t⁻¹ = (y : G)⁻¹ := hinvK _ y.2
  -- `⟨y⟩ ⊔ ⟨t⟩ = ⊤` と `|G| = 2 |Ω|`。
  have hgen : Subgroup.zpowers (y : G) ⊔ Subgroup.zpowers t = ⊤ := by
    rw [hyK, ← hzt]; exact hsup
  have hGcard : Nat.card G = 2 * Nat.card Ω := by
    have h := Subgroup.index_mul_card (stabilizer G α)
    rw [index_stabilizer_of_transitive G α, hcard] at h
    omega
  exact ⟨(dihedralEquiv hyord htt hconj hgen hGcard).symm⟩

end -- Problem 8B.6 の結論

end OddOrder.Isaacs.Ch08
