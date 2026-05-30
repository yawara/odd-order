/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main

/-!
# BG §4 I-1b — Prop 1.6(b) の R-内部 (actionCommutator) 形

> **本** Bender–Glauberman, *Local Analysis for the Odd Order Theorem* §4.

repo は BG の "`A` = group of operators on `R`" を `φ : A →* MulAut R` で表す
(`OddOrder.Isaacs.Ch03.IsAInvariant`, `OddOrder.Isaacs.Ch04.actionCommutator`)。

repo の Prop 1.6(b) は **半直積 Γ = R ⋊[φ] A 内**の主張
`⁅⁅XR,YA⁆,YA⁆ = ⁅XR,YA⁆` (Isaacs Lemma 4.29,
`OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one`, Ch04:2785)。
BG Thm 4.12(a) step a-1 が消費するのは **R-内部の「`R = [R,A]` と仮定してよい」reduction**:
`N := [R,A] = actionCommutator φ` への制限作用 `ψN := hN.toMulAutHom` の作用交換子は
`N` 全体になる (`[N,A] = N`, i.e. `[[R,A],A] = [R,A]`)。本ファイルはこの **Γ → R-内部 変換**を
genuine に供給する (= BG §4 I-1b)。

主結果:
* `actionCommutator_toMulAutHom_map_subtype_map_inl` : 一般橋 (生成元レベルの計算を集約)
* `actionCommutator_restrict_self_map_subtype_eq` : `([N,A] の像) = N` (G 内の等式形)
* `actionCommutator_restrict_self_eq_top` : `actionCommutator ψN = ⊤` (⊤ 形, headline,
  Thm 4.12(a) step a-1 が消費)

**注意 (重複回避)**: A-invariant normal `S ⊴ R` の商 `R ⧸ S` への作用持ち上げ自体
(`IsAInvariant.quotientMulAutHom`, apply 補題, descent `actionCommutator_quotient_eq_map`,
`≤N ⇒ [R/S,A]=⊥`) は **既に Ch04 (`Ch04_Commutators/Main.lean:2248`, commit d53f690) に存在**
するので, 本ファイルでは **再実装しない** (設計書 N-4 の "lift" 半分は既存)。残る Maschke
complement bridge は `notes/bg/s04_n4_maschke_bridge_design.md` を参照。

設計書: [`notes/bg/s04_prop411_thm416_design.md`](../../../notes/bg/s04_prop411_thm416_design.md)
§4 (Thm 4.12 a-1)。

**ANTI-SCAFFOLD**: 既存 Γ 形 `iterCommutator_inl_inr_two_eq_one` から genuine に導く
(制限作用 `toMulAutHom` も Ch04 既存の本物の構成、`sorry` instance ではない)。
-/

open scoped Pointwise

namespace OddOrder.BG.Ch1.OperatorQuotientAction

open OddOrder.Isaacs.Ch03 (IsAInvariant)
open OddOrder.Isaacs.Ch04

section RestrictSelf

/-- **一般橋 (常に成立)**: `H` が `φ`-不変なら, 制限作用 `ψH := hH.toMulAutHom` の作用交換子を
`H.subtype` で `G` に押し戻したものは, `H` を `G⋊A` に `inl` で送った先で測ると元の作用交換子の
`inl` 像と一致する。具体的には `inl ∘ H.subtype = F ∘ inl_H` (`F` は下の橋) なので
`((actionCommutator ψH).map H.subtype).map inl = ⁅inl(H).range, inr(A).range⁆`。

これが `actionCommutator_restrict_self_*` の共通骨格 (生成元レベルの計算をここに集約)。 -/
theorem actionCommutator_toMulAutHom_map_subtype_map_inl
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) :
    ((actionCommutator hH.toMulAutHom).map H.subtype).map
        (SemidirectProduct.inl : G →* G ⋊[φ] A) =
      ⁅((SemidirectProduct.inl : G →* G ⋊[φ] A).comp H.subtype).range,
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ := by
  set ψ : A →* MulAut H := hH.toMulAutHom with hψ
  -- F : H ⋊[ψ] A →* G ⋊[φ] A, 既存 private template (Ch04:2948) と同型 (条件は rfl)
  let F : H ⋊[ψ] A →* G ⋊[φ] A :=
    SemidirectProduct.map H.subtype (MonoidHom.id A) (fun a => by
      ext h
      rfl)
  -- inl ∘ H.subtype = F ∘ inl_H なので map を合成で書き換え (SemidirectProduct.map_comp_inl)
  have hcomp : (SemidirectProduct.inl : G →* G ⋊[φ] A).comp H.subtype
      = F.comp (SemidirectProduct.inl : H →* H ⋊[ψ] A) :=
    (SemidirectProduct.map_comp_inl H.subtype (MonoidHom.id A) _).symm
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  -- (actionCommutator ψ).map inl_H = ⁅inl(H).range, inr(A).range⁆ (in H⋊A)
  rw [actionCommutator_map_inl ψ]
  -- map by F: ⁅XH, YA_H⁆.map F = ⁅XH.map F, YA_H.map F⁆, then identify images
  rw [Subgroup.map_commutator]
  congr 1
  · -- XH.map F = (inl ∘ H.subtype).range
    ext x
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, by simp [F, SemidirectProduct.map_inl]⟩
    · rintro ⟨h, rfl⟩
      exact ⟨(SemidirectProduct.inl : H →* H ⋊[ψ] A) h, ⟨h, rfl⟩, by
        simp [F, SemidirectProduct.map_inl]⟩
  · -- YA_H.map F = inr(A).range
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by simp [F, SemidirectProduct.map_inr]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(SemidirectProduct.inr : A →* H ⋊[ψ] A) a, ⟨a, rfl⟩, by
        simp [F, SemidirectProduct.map_inr]⟩

/-- **Prop 1.6(b) R-内部形 (G 内の等式)** ⭐: coprime + (A or G solvable) ⇒
`N := [R,A] = actionCommutator φ` への制限作用 `ψN := hN.toMulAutHom` の作用交換子を
`N.subtype` で `G` に押し戻すと `N` 全体に一致 (`([N,A] の像) = N = [R,A]`)。

これが BG「`[R,A] = [R,A,A]` だから `R = [R,A]` と仮定してよい」の核心 `[[R,A],A] = [R,A]`。

**証明**: injective `inl : G →* G⋊A` を通して両辺の `inl` 像を比較する。
- 左辺 `inl` 像 = `⁅inl(N).range, inr(A).range⁆` (上の一般橋, `H = N`)。
- `N = actionCommutator φ` なので `inl(N).range = N.map inl = ⁅XG, YA⁆`
  (`actionCommutator_map_inl φ`)。よって左辺 `inl` 像 = `⁅⁅XG,YA⁆, YA⁆ = iterCommutator XG YA 2`。
- Prop 1.6(b) Γ形 `iterCommutator XG YA 2 = iterCommutator XG YA 1 = ⁅XG,YA⁆ = N.map inl`。
- 右辺 `inl` 像 = `N.map inl`。両者一致, `inl` 単射で結論。 -/
theorem actionCommutator_restrict_self_map_subtype_eq
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    (actionCommutator (IsAInvariant.actionCommutator φ).toMulAutHom).map
        (actionCommutator φ).subtype = actionCommutator φ := by
  set N : Subgroup G := actionCommutator φ with hN_def
  have hN_inv : IsAInvariant φ N := IsAInvariant.actionCommutator φ
  -- inl 単射で両辺の inl 像を比較
  apply Subgroup.map_injective (f := (SemidirectProduct.inl : G →* G ⋊[φ] A))
    SemidirectProduct.inl_injective
  -- 左辺 inl 像 = ⁅inl(N).range, inr(A).range⁆
  rw [actionCommutator_toMulAutHom_map_subtype_map_inl hN_inv]
  -- inl(N).range = N.map inl = ⁅XG, YA⁆  (N = actionCommutator φ)
  have hN_inl : ((SemidirectProduct.inl : G →* G ⋊[φ] A).comp N.subtype).range
      = ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
          (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ := by
    rw [MonoidHom.range_comp, N.range_subtype, hN_def]
    exact actionCommutator_map_inl φ
  rw [hN_inl]
  -- 目標: ⁅⁅XG,YA⁆, YA⁆ = N.map inl  (= ⁅XG,YA⁆ via Prop 1.6(b))
  rw [actionCommutator_map_inl φ]
  -- ⁅⁅XG,YA⁆,YA⁆ = iterCommutator XG YA 2, ⁅XG,YA⁆ = iterCommutator XG YA 1
  have h16b := iterCommutator_inl_inr_two_eq_one (φ := φ) hCop hSolv
  -- iterCommutator _ _ 2 = ⁅⁅XG,YA⁆, YA⁆, iterCommutator _ _ 1 = ⁅XG, YA⁆
  -- (iterCommutator_zero : _ 0 = XG (1st arg); succ で 1 段ずつ展開)
  simpa only [iterCommutator_succ, iterCommutator_zero] using h16b

/-- **Prop 1.6(b) R-内部形 (⊤ 形, headline)** ⭐ (= BG Thm 4.12(a) step a-1 が消費):
coprime + (A or G solvable) ⇒ `N := [R,A] = actionCommutator φ` への制限作用
`ψN := hN.toMulAutHom` の作用交換子は `⊤` (= `[N,A] = N`)。

`R := N`, `φ := ψN` への型置換で `actionCommutator ψN = ⊤` (= `hRA : R = [R,A]`) を再生する,
BG の WLOG `R = [R,A]` の Lean 化。`actionCommutator_restrict_self_map_subtype_eq` (G 内等式)
に `N.subtype` 単射 + `range_subtype` を被せた直接の系。 -/
theorem actionCommutator_restrict_self_eq_top
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    actionCommutator (IsAInvariant.actionCommutator φ).toMulAutHom = ⊤ := by
  set N : Subgroup G := actionCommutator φ with hN_def
  -- map N.subtype injective + ⊤.map N.subtype = N.subtype.range = N でゴールを等式形に還元
  apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
  rw [actionCommutator_restrict_self_map_subtype_eq hCop hSolv,
    ← MonoidHom.range_eq_map, N.range_subtype]

end RestrictSelf

end OddOrder.BG.Ch1.OperatorQuotientAction
