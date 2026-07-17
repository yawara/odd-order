/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
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
* `actionCommutator_le_centralizer_of_isCyclic_isAInvariant` : `S ⊴ G` cyclic A-不変 ⇒
  `[G,A] ⊆ C_G(S)` (= BG Thm 4.12(a) step a-2 核心、**半直積 `GA` を経由しない**共役同変性版)
* `isCyclic_le_center_of_actionCommutator_eq_top` : 上の系で `[G,A]=⊤` ⇒ `S ⊆ Z(G)` (a-2 結論)

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

open scoped Pointwise commutatorElement

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

section CentralizerOfCyclicAInvariant

/-- **BG Thm 4.12(a) step a-2 核心** (`R = [R,A] ⊆ (RA)′ ⊆ C_{RA}(S) ⇒ S ⊆ Z(R)` の前半),
半直積を経由しない版。

`S ⊴ G` が cyclic かつ `A`-不変 (`IsAInvariant φ S`) なら, 作用交換子
`[G,A] = actionCommutator φ` は `S` を中心化する (`⊆ C_G(S)`).

BG の証明は `G = [G,A] ⊆ (GA)′ ⊆ C_{GA}(S)` を半直積 `GA = G ⋊ A` 経由で辿るが, ここでは
`GA` を一切作らない。共役作用 `α : G →* MulAut ↥S` (`S ⊴ G`) と制限作用 `ρ := φ|_S : A →* MulAut ↥S`
(`S` `A`-不変) を取ると, `α` を `ρ a` で共役する同変性 `ρ a * α g = α ((φ a) g) * ρ a` が成り立つ。
`S` cyclic ゆえ `MulAut ↥S` は abelian なので, これは `α ((φ a) g) = α g` を強制する。よって `[G,A]` の
各生成元 `g · (φ a) g⁻¹` は `α (g · (φ a) g⁻¹) = α g · (α g)⁻¹ = 1`, すなわち `S` を中心化する。 -/
theorem actionCommutator_le_centralizer_of_isCyclic_isAInvariant
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {S : Subgroup G} [IsCyclic ↥S] (hS_norm : S.Normal) (hS_inv : IsAInvariant φ S) :
    actionCommutator φ ≤ Subgroup.centralizer (S : Set G) := by
  -- 共役作用 α : G →* MulAut ↥S を「`MulAut.conj` 下での S の A-不変性」として得る (S ⊴ G ⇔ これ)
  have hconj : IsAInvariant (MulAut.conj : G →* MulAut G) S := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro r s hs
    simpa using hS_norm.conj_mem s hs r
  -- S cyclic ⇒ MulAut ↥S abelian (`MulAut ↥S ≃* (ZMod _)ˣ`)。**インスタンス登録はしない**
  -- (canonical `MulAut.instGroup` と競合する 2 つ目の inv が出来てダイヤモンドになる)。
  -- 必要な `mul_comm` だけを局所事実として取り出す。
  have hcomm : ∀ x y : MulAut ↥S, x * y = y * x := by
    intro x y
    apply (IsCyclic.mulAutMulEquiv (G := ↥S)).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  -- 共役作用 α と制限作用 ρ。`((toMulAutHom · ·) ·).val = (φ ·) (·).val` は定義的等号なので
  -- 以下 `show`/`congrArg Subtype.val` で defeq 展開する (Ch04 の `_root_` 欠落で apply_val 補題名が
  -- 二重 nest し名前参照できないため、名前を介さない)。
  set α : G →* MulAut ↥S := hconj.toMulAutHom
  set ρ : A →* MulAut ↥S := hS_inv.toMulAutHom
  -- 同変性: ρ a * α g = α ((φ a) g) * ρ a  (両辺 s への作用が (φa)g · (φa)s · ((φa)g)⁻¹ に一致)
  have hint : ∀ (a : A) (g : G), ρ a * α g = α ((φ a) g) * ρ a := by
    intro a g
    ext s
    change (φ a) (g * (s : G) * g⁻¹) = (φ a) g * (φ a) (s : G) * ((φ a) g)⁻¹
    rw [map_mul, map_mul, map_inv]
  -- abelian で同変性から α ((φ a) g) = α g
  have heq : ∀ (a : A) (g : G), α ((φ a) g) = α g := by
    intro a g
    have hi := hint a g
    rw [hcomm (α ((φ a) g)) (ρ a)] at hi
    exact (mul_left_cancel hi).symm
  -- 生成元 g · (φ a) g⁻¹ は α で 1 に飛ぶ ⇒ C_G(S) に属する
  rw [actionCommutator, Subgroup.closure_le]
  rintro x ⟨g, a, rfl⟩
  have hx1 : α (g * (φ a) g⁻¹) = 1 := by
    rw [map_mul, heq a g⁻¹, map_inv]
    exact mul_inv_cancel (α g)
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro s hs
  have h : (α (g * (φ a) g⁻¹)) ⟨s, hs⟩ = ⟨s, hs⟩ := by rw [hx1]; simp
  have hval : (g * (φ a) g⁻¹) * s * (g * (φ a) g⁻¹)⁻¹ = s := congrArg Subtype.val h
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- **BG Thm 4.12(a) step a-2** (`S ⊆ Z(R)`): cyclic A-不変 normal `S ⊴ G` で `[G,A] = ⊤`
(`actionCommutator φ = ⊤`) なら `S` は中心に含まれる (`S ⊆ Z(G)`).

`actionCommutator_le_centralizer_of_isCyclic_isAInvariant` と
`Subgroup.centralizer_eq_top_iff_subset` から直ちに従う。 -/
theorem isCyclic_le_center_of_actionCommutator_eq_top
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {S : Subgroup G} [IsCyclic ↥S] (hS_norm : S.Normal) (hS_inv : IsAInvariant φ S)
    (hGA : actionCommutator φ = ⊤) :
    S ≤ Subgroup.center G := by
  have hle := actionCommutator_le_centralizer_of_isCyclic_isAInvariant hS_norm hS_inv
  rw [hGA, top_le_iff] at hle
  intro x hx
  exact (Subgroup.centralizer_eq_top_iff_subset.mp hle) hx

/-- **BG Thm 4.12(a) step a-2, `S` の構成**: 有限群 `G` で `R' = commutator G` が cyclic なら,
`R'` を含む cyclic A-不変部分群のうち**包含について極大**なもの `S` が存在する。

`R'` 自身が cyclic (`hcyc`) かつ characteristic ゆえ A-不変 (`IsAInvariant.commutator_self`) なので
述語 `IsAInvariant φ · ∧ IsCyclic · ∧ R' ≤ ·` を満たし, 有限部分群束の極大元
(`Finite.exists_le_maximal`) を取って antisymmetry で極大性を仕上げる。

(`IsCyclic ↥(commutator G)` は metacyclic から `IsMetacyclic.isCyclic_commutator` で供給される;
ここでは `IsMetacyclic` import を避けるため仮説として受け取る。) -/
theorem exists_maximal_isCyclic_isAInvariant_commutator_le
    {A G : Type*} [Group A] [Group G] [Finite G] (φ : A →* MulAut G)
    (hcyc : IsCyclic ↥(commutator G)) :
    ∃ S : Subgroup G, IsAInvariant φ S ∧ IsCyclic ↥S ∧ commutator G ≤ S ∧
      ∀ T : Subgroup G, IsAInvariant φ T → IsCyclic ↥T → commutator G ≤ T → S ≤ T → S = T := by
  obtain ⟨S, hsub, hmax⟩ :=
    Finite.exists_le_maximal
      (p := fun H : Subgroup G => IsAInvariant φ H ∧ IsCyclic ↥H ∧ commutator G ≤ H)
      ⟨IsAInvariant.commutator_self φ, hcyc, le_refl _⟩
  exact ⟨S, hmax.1.1, hmax.1.2.1, hsub, fun T hT hTcyc hTle hST =>
    le_antisymm hST (hmax.2 ⟨hT, hTcyc, hTle⟩ hST)⟩

end CentralizerOfCyclicAInvariant

section ConjNormalBridge

/-- **`actionCommutator` ↔ subgroup commutator 基盤橋**: `H ⊴ G`, `R ≤ G`.  `R` の `H` への
**共役作用** `φ := conjNormal ∘ R.subtype : R →* MulAut H` の作用交換子を `H.subtype` で `G` に
押し戻すと, 部分群交換子 `⁅H, R⁆` に一致する。

`actionCommutator φ` の生成元は `h * (φ r) h⁻¹` (`h ∈ H`, `r ∈ R`) で, `G` 内の値は
`h * (r h⁻¹ r⁻¹) = ⁅h, r⁆` (= mathlib `⁅H, R⁆` の生成元)。両 `closure` が同じ生成集合を持つ。

BG §3 (Theorem 3.6) ほか, 内部共役作用に対する Prop 1.6 系 (`actionCommutator` 言語で証明済) を
部分群交換子 `⁅H, R⁆` の主張へ翻訳する際の土台。`OddOrder.Isaacs.Ch05` (transfer) に同型の
生成元計算の先例がある。 -/
theorem actionCommutator_conjNormal_map_subtype_eq {G : Type*} [Group G] (H R : Subgroup G)
    [H.Normal] :
    (actionCommutator ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype)).map H.subtype
      = ⁅H, R⁆ := by
  set φ : ↥R →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R.subtype with hφ
  -- generator value: `↑(hA * (φ rB) hA⁻¹) = ⁅↑hA, ↑rB⁆` in `G`.
  have hval : ∀ (hA : ↥H) (rB : ↥R),
      ((hA * (φ rB) hA⁻¹ : ↥H) : G) = ⁅(hA : G), (rB : G)⁆ := by
    intro hA rB
    have he : (φ rB) hA⁻¹ = MulAut.conjNormal (rB : G) hA⁻¹ := by
      simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [Subgroup.coe_mul, he, MulAut.conjNormal_apply, Subgroup.coe_inv, commutatorElement_def]
    group
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold actionCommutator
    rw [Subgroup.closure_le]
    rintro x ⟨h, r, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.coe_subtype, hval]
    exact Subgroup.commutator_mem_commutator h.2 r.2
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨(⟨a, ha⟩ : ↥H) * (φ ⟨b, hb⟩) (⟨a, ha⟩)⁻¹,
      Subgroup.subset_closure ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, hval]

/-- **BG Prop 1.6(b), subgroup-commutator form** ⭐: `H ⊴ G`, `R ≤ G`, coprime orders, `G`
solvable ⟹ `⁅⁅H, R⁆, R⁆ = ⁅H, R⁆`.

This is the `G`-internal subgroup-commutator statement BG uses directly (e.g. Theorem 3.6 (3.6):
`[H,R] = [[H,R],R]` lets one assume `H = [H,R]`; also (3.24), (3.32)).  Derived from the
`actionCommutator` "restrict-self" lemma (`actionCommutator_restrict_self_map_subtype_eq`, which
already encodes `[[N,A],A]=[N,A]` *without* needing `[H,R] ⊴ G`) plus the conjugation bridge
`actionCommutator_conjNormal_map_subtype_eq` at two nesting levels.  The restricted `R`-action on
`N := actionCommutator φ` agrees with `φ` on `N` (`toMulAutHom_apply_val`), so its generators carry
the same commutator values `⁅↑↑n, ↑r⁆`. -/
theorem commutator_commutator_right_eq {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (H R : Subgroup G) [H.Normal] (hCop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥R)) :
    ⁅⁅H, R⁆, R⁆ = ⁅H, R⁆ := by
  set φ : ↥R →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R.subtype with hφ
  set N : Subgroup ↥H := actionCommutator φ with hN
  set ψ : ↥R →* MulAut ↥N := (IsAInvariant.actionCommutator φ).toMulAutHom with hψ
  have hb : N.map H.subtype = ⁅H, R⁆ := actionCommutator_conjNormal_map_subtype_eq H R
  have hself : (actionCommutator ψ).map N.subtype = N :=
    actionCommutator_restrict_self_map_subtype_eq (φ := φ) hCop.symm (Or.inr inferInstance)
  -- generator value (two coercion layers `↥N → ↥H → G`): `↑↑(nN * (ψ rB) nN⁻¹) = ⁅↑↑nN, ↑rB⁆`.
  have hval2 : ∀ (nN : ↥N) (rB : ↥R),
      (((nN * (ψ rB) nN⁻¹ : ↥N) : ↥H) : G) = ⁅(((nN : ↥H) : G)), (rB : G)⁆ := by
    intro nN rB
    have hφr : φ rB = MulAut.conjNormal (rB : G) := by rw [hφ]; rfl
    simp only [hψ, Subgroup.coe_mul,
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val, Subgroup.coe_inv, hφr,
      MulAut.conjNormal_apply, commutatorElement_def]
    group
  -- nested bridge: `((actionCommutator ψ).map N.subtype).map H.subtype = ⁅⁅H,R⁆, R⁆`.
  have hnest : ((actionCommutator ψ).map N.subtype).map H.subtype = ⁅⁅H, R⁆, R⁆ := by
    rw [Subgroup.map_map]
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      unfold actionCommutator
      rw [Subgroup.closure_le]
      rintro x ⟨nN, rB, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.coe_subtype, hval2]
      have hmem : (((nN : ↥H) : G)) ∈ ⁅H, R⁆ := hb ▸ ⟨(nN : ↥H), nN.2, rfl⟩
      exact Subgroup.commutator_mem_commutator hmem rB.2
    · rw [Subgroup.commutator_le]
      intro c hc r hr
      rw [← hb] at hc
      obtain ⟨nH, hnH, rfl⟩ := hc
      refine ⟨(⟨nH, hnH⟩ : ↥N) * (ψ ⟨r, hr⟩) (⟨nH, hnH⟩ : ↥N)⁻¹,
        Subgroup.subset_closure ⟨(⟨nH, hnH⟩ : ↥N), ⟨r, hr⟩, rfl⟩, ?_⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_subtype, hval2]
  rw [← hnest, hself, hb]

end ConjNormalBridge

end OddOrder.BG.Ch1.OperatorQuotientAction
