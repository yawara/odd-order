/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.OrderOfElement
import OddOrder.Isaacs.Ch05_Transfer.Dietzmann

/-!
# Isaacs Chapter 5 — Problems 5B (transfer evaluation / Dietzmann)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 5B (書籍 p. 157)。

* **5B.1** `P ∈ Syl_p(G)`, `g ∈ P` は位数 `p`, `g ∈ G'` かつ `g ∉ P'` ⇒
  `g^t ∈ P` なる `t ∉ P` が存在する。
  ⚠ **書籍の印刷は `g^t ∈ P'` だが、巻末 errata (項目 3, p. 157) が
  「`P` の dash を削れ」= `g^t ∈ P` に訂正している**。PDF ページ画像 (書籍 p.157 =
  PDF p.170) と errata の両方で確認済。
* **5B.2** Thm 5.10 (Dietzmann) の状況で `|X| = m` なら `|⟨X⟩| ≤ n^m`。
* **5B.3** `x ∈ G` がある有限正規部分群に属する ⟺ `x` の位数が有限かつ共役類が有限。

Dietzmann の定理 (Thm 5.10) は `Dietzmann.lean` に landing 済
(`dietzmann` / `dietzmann_setFinite`)。
-/

namespace OddOrder.Isaacs.Ch05

section /- 5B: Problems (p. 157) -/

variable {G : Type*} [Group G]

/-! ### Problem 5B.3 -/

/-- 共役で閉じた集合が生成する部分群は正規。

`Subgroup.closure_induction` で各生成手順が共役に耐えることを見るだけ。 -/
theorem normal_closure_of_conj_closed {X : Set G}
    (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X) : (Subgroup.closure X).Normal := by
  refine ⟨fun y hy g => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem z hz => exact Subgroup.subset_closure (hconj z hz g)
  | one => simp
  | mul a b _ _ ha hb =>
    have hab : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
    rw [hab]
    exact mul_mem ha hb
  | inv a _ ha =>
    have hinv : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [hinv]
    exact inv_mem ha

/-- **Isaacs Problem 5B.3**: `x` がある有限正規部分群に属する ⟺ `x` の位数が有限で,
かつ `x` の共役類が有限。`G` は有限とは限らない。

**証明**: (⟸) `X := x` の共役類は有限・共役閉で, 各元の位数は `orderOf x` を割るので
Dietzmann (Thm 5.10) より `⟨X⟩` は有限。共役閉なので `⟨X⟩ ⊴ G` (`normal_closure_of_conj_closed`),
かつ `x ∈ X ⊆ ⟨X⟩`。
(⟹) `x ∈ N` で `N` 有限なら `x ^ |N| = 1` で位数有限, 共役類は `N` 正規性から `N` に含まれ有限。 -/
theorem exists_finite_normal_iff (x : G) :
    (∃ N : Subgroup G, N.Normal ∧ Finite ↥N ∧ x ∈ N) ↔
      IsOfFinOrder x ∧ (conjugatesOf x).Finite := by
  constructor
  · rintro ⟨N, hNnormal, hNfin, hxN⟩
    haveI := hNfin
    refine ⟨?_, ?_⟩
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card N, Nat.card_pos,
        congrArg Subtype.val (pow_card_eq_one' (G := ↥N) (x := ⟨x, hxN⟩))⟩
    · have hNset : (N : Set G).Finite := Set.toFinite _
      refine hNset.subset ?_
      intro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      rw [← hc]
      exact hNnormal.conj_mem x hxN c
  · rintro ⟨hord, hfin⟩
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hord
    have hconj : ∀ y ∈ conjugatesOf x, ∀ g : G, g * y * g⁻¹ ∈ conjugatesOf x := by
      intro y hy g
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      exact isConj_iff.mpr ⟨g * c, by rw [← hc]; group⟩
    have hexp : ∀ y ∈ conjugatesOf x, y ^ n = 1 := by
      intro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      have hcp : ∀ m : ℕ, (c * x * c⁻¹) ^ m = c * x ^ m * c⁻¹ := by
        intro m
        induction m with
        | zero => simp
        | succ k ih => rw [pow_succ, ih, pow_succ]; group
      rw [← hc, hcp, hxn]
      group
    exact ⟨Subgroup.closure (conjugatesOf x), normal_closure_of_conj_closed hconj,
      dietzmann hfin hconj hn hexp, Subgroup.subset_closure (IsConj.refl x)⟩

end

end OddOrder.Isaacs.Ch05
