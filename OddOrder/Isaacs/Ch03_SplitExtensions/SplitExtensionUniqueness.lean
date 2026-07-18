/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Isaacs Ch. 3 — Lemma 3.1: split extension の同型を除く一意性 (pp. 69-70)

Isaacs, *Finite Group Theory* (AMS GSM 92), section 3A, **Lemma 3.1** の完全形
(書籍の two-abstract-groups 形).

書籍の主張 (p. 70):

> `N ◁ G` が `H` で補われ, `N₀ ◁ G₀` が `H₀` で補われるとする. 同型
> `( )₀ : N ≅ N₀`, `( )₀ : H ≅ H₀` が共役作用と両立する
> (`(n^h)₀ = (n₀)^(h₀)`) ならば, この 2 つの同型を延長する同型 `G ≅ G₀` が
> **ただ 1 つ**存在する.

すなわち split extension は「`N` と `H` と `H` の `N` への作用」だけで同型を除いて
一意に決まる — これが §3A で `N ⋊ H` を「the semidirect product」と呼べる根拠であり,
Thm 3.2 (半直積の構成) と対になる。

## 実装方針

存在部分は mathlib の半直積を経由する:
`G ≃* N ⋊ H` (`SemidirectProduct.mulEquivSubgroup`) と
`N ⋊ H ≃* N₀ ⋊ H₀` (`SemidirectProduct.congr`, 両立条件がそのまま仮説) を繋ぐ。
一意性部分は `N ⊔ H = ⊤` (`Subgroup.IsComplement'.sup_eq_top`) から生成による外延性
(`MonoidHom.eq_of_eqOn_dense`) で出る。書籍の証明が `θ(hn) = h₀n₀` を直接定義して
準同型性を計算するのに対し, ここでは半直積の普遍性に肩代わりさせている。

`G₀ = N ⋊ H` に固定した特殊形が mathlib の `SemidirectProduct.mulEquivSubgroup`
そのもので, 書籍が Thm 3.2 の直後で述べる「任意の split extension は半直積と同型」
という帰結にあたる。

ノート: [notes/isaacs/ch03_split.md](../../../notes/isaacs/ch03_split.md)
-/

namespace OddOrder.Isaacs.Ch03

variable {G G₀ : Type*} [Group G] [Group G₀]

section /- 3A: Uniqueness of split extensions (pp. 69-70) -/

/-- 正規部分群 `N ◁ G` への部分群 `H ≤ G` の共役作用を束ねた準同型 `H →* MulAut N`
(`n ↦ h * n * h⁻¹`).

mathlib の `Subgroup.normalizerMonoidHom : N.normalizer →* MulAut N` を
`N.normalizer = ⊤` で `H` 全体に引き戻した形 (仮定特殊化)。Isaacs が Lemma 3.1 /
Thm 3.2 で「`H` が `N` に共役で作用する」と書くときの作用がこれ。 -/
def conjAutHom (N H : Subgroup G) [N.Normal] : H →* MulAut N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))

@[simp]
theorem conjAutHom_apply_coe (N H : Subgroup G) [N.Normal] (h : H) (n : N) :
    ((conjAutHom N H h n : N) : G) = (h : G) * (n : G) * (h : G)⁻¹ :=
  rfl

/-- 補集合対 `N`, `H` は `G` を生成する (集合和の閉包が `⊤`). -/
theorem closure_union_eq_top_of_isComplement' {N H : Subgroup G} (hC : N.IsComplement' H) :
    Subgroup.closure ((N : Set G) ∪ (H : Set G)) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hC.sup_eq_top]

/-- **Isaacs Lemma 3.1 一意性部分**: 補集合対 `N`, `H` の上で一致する 2 つの準同型
`G →* G₀` は一致する.

書籍の「`g = hn` の分解が一意だから `θ` は `H` と `N` 上の値で決まる」に対応。 -/
theorem monoidHom_eq_of_eqOn_isComplement' {N H : Subgroup G} (hC : N.IsComplement' H)
    {f g : G →* G₀} (hN : ∀ n : N, f (n : G) = g (n : G))
    (hH : ∀ h : H, f (h : G) = g (h : G)) : f = g :=
  MonoidHom.eq_of_eqOn_dense (closure_union_eq_top_of_isComplement' hC)
    fun _ hx => hx.elim (fun h => hN ⟨_, h⟩) fun h => hH ⟨_, h⟩

/-- **Isaacs Lemma 3.1** (split extension の同型を除く一意性, 書籍 p. 70 の完全形).

`N ◁ G` が `H` で補われ, `N₀ ◁ G₀` が `H₀` で補われ, 同型 `α : N ≃* N₀`,
`β : H ≃* H₀` が共役作用と両立する (`α (h n h⁻¹) = β h * α n * (β h)⁻¹`) とき,
`α` と `β` を延長する同型 `θ : G ≃* G₀` が**一意に存在する**。

書籍の証明は `θ(hn) := h₀ n₀` を直接定義し, `(hn)(km) = (hk)(n^k m)` から準同型性を
計算する。ここでは同じ内容を半直積経由で組む:
`G ≃* N ⋊ H ≃* N₀ ⋊ H₀ ≃* G₀` (中央の同型の仮説が両立条件そのもの)。 -/
theorem existsUnique_mulEquiv_of_isComplement' {N H : Subgroup G} {N₀ H₀ : Subgroup G₀}
    [N.Normal] [N₀.Normal] (hC : N.IsComplement' H) (hC₀ : N₀.IsComplement' H₀)
    (α : N ≃* N₀) (β : H ≃* H₀)
    (hact : ∀ (h : H) (n : N), α (conjAutHom N H h n) = conjAutHom N₀ H₀ (β h) (α n)) :
    ∃! θ : G ≃* G₀,
      (∀ n : N, θ (n : G) = ((α n : N₀) : G₀)) ∧ (∀ h : H, θ (h : G) = ((β h : H₀) : G₀)) := by
  -- `G ≃* N ⋊ H` と `G₀ ≃* N₀ ⋊ H₀` (mathlib の半直積による split extension の再構成).
  let e : N ⋊[conjAutHom N H] H ≃* G := SemidirectProduct.mulEquivSubgroup hC
  let e₀ : N₀ ⋊[conjAutHom N₀ H₀] H₀ ≃* G₀ := SemidirectProduct.mulEquivSubgroup hC₀
  -- 両立条件から半直積の同型 `N ⋊ H ≃* N₀ ⋊ H₀`.
  let c : N ⋊[conjAutHom N H] H ≃* N₀ ⋊[conjAutHom N₀ H₀] H₀ :=
    SemidirectProduct.congr α β fun h => MulEquiv.ext fun n => hact h n
  let θ₀ : G ≃* G₀ := (e.symm.trans c).trans e₀
  -- `mulEquivSubgroup` は `⟨n, h⟩ ↦ n * h` なので `inl` / `inr` 上では包含そのもの.
  have he_inl : ∀ n : N, e (SemidirectProduct.inl n) = (n : G) := fun _ => mul_one _
  have he_inr : ∀ h : H, e (SemidirectProduct.inr h) = (h : G) := fun _ => one_mul _
  have he₀_inl : ∀ n : N₀, e₀ (SemidirectProduct.inl n) = (n : G₀) := fun _ => mul_one _
  have he₀_inr : ∀ h : H₀, e₀ (SemidirectProduct.inr h) = (h : G₀) := fun _ => one_mul _
  have hc_inl : ∀ n : N, c (SemidirectProduct.inl n) = SemidirectProduct.inl (α n) :=
    fun _ => SemidirectProduct.ext rfl (map_one β)
  have hc_inr : ∀ h : H, c (SemidirectProduct.inr h) = SemidirectProduct.inr (β h) :=
    fun _ => SemidirectProduct.ext (map_one α) rfl
  have h1 : ∀ n : N, θ₀ (n : G) = ((α n : N₀) : G₀) := by
    intro n
    have hn : e.symm (n : G) = SemidirectProduct.inl n := by
      rw [MulEquiv.symm_apply_eq, he_inl]
    change e₀ (c (e.symm (n : G))) = _
    rw [hn, hc_inl, he₀_inl]
  have h2 : ∀ h : H, θ₀ (h : G) = ((β h : H₀) : G₀) := by
    intro h
    have hh : e.symm (h : G) = SemidirectProduct.inr h := by
      rw [MulEquiv.symm_apply_eq, he_inr]
    change e₀ (c (e.symm (h : G))) = _
    rw [hh, hc_inr, he₀_inr]
  refine ⟨θ₀, ⟨h1, h2⟩, ?_⟩
  rintro θ ⟨hθN, hθH⟩
  refine MulEquiv.toMonoidHom_injective
    (monoidHom_eq_of_eqOn_isComplement' hC (fun n => ?_) fun h => ?_)
  · simpa using (hθN n).trans (h1 n).symm
  · simpa using (hθH h).trans (h2 h).symm

end

end OddOrder.Isaacs.Ch03
