---
id: 3011
slug: thm310-nilpotent-packaging
title: "BG Thm 3.10 general nilpotent M packaging — group-level Case-1 induction (elem-abelian leaf は済)"
created: 2026-07-18
---

# BG Thm 3.10 general nilpotent M packaging — group-level Case-1 induction

## 背景

BG §3 の唯一の残 (survey L318)。BG §3 = 10 結果、9 済。Thm 3.10 は **elementary-abelian M +
general kernel の (a)(b)(c) 全形 (group/card/rep) が issue 8013 で完成済** (2026-06-17, sorry-free +
axiom-clean)。**残 = book の general nilpotent M への packaging** = group-level Case-1 induction。

⚠ **FT-noncritical**: FT 経路は elementary-abelian 形 (§15.2 Q̄ = chief factor) を消費、それは済。
general nilpotent M は book の正確な statement (in-scope、specialization debt の一般化) だが FT gate 無。

## statement (BG mmd L1282-1294)

> `G=KR` solvable Frobenius (kernel K, complement R) が非自明**冪零** M に作用、
> (1) `(|G|,|M|)=1`, (2) `C_M(K)=1`, (3) `C_M(x)=C_M(R)` ∀`x∈R^#`。結論:
> (a) R cyclic of prime order p; (b) `|M|=|C_M(R)|^p`; (c) `C_M(R)` cyclic ⟹ `K'⊆C_K(M)`。

## 既存 elementary-abelian base (reuse、S03g_Thm310ElemAbelian.lean)

- `card_eq_pow_card_invariants_of_elemAbelian_general` — (b) `Nat.card (Additive M) = |inv|^|R|`
  (M CommGroup + `[Module (ZMod p)(Additive M)]` + MulDistribMulAction H M, K◁H, hRne/hKne/hpH/hcop/
  hCK/hFrob/hcond3)。
- `commutator_acts_trivially_of_elemAbelian_general` — (c) `IsFrobeniusGroup H K R` + cyclic C_M(R)
  ⟹ K' acts trivially。
- `prime_card_and_finrank_of_elemAbelian_general` — (a)+(b) finrank。
- (a) `R` prime order は M 非依存 (`isCyclic_of_isPGroup_of_isFrobeniusAction` + Hall + Prop 3.9)。

## 形式化計画 (group-level Case-1 induction on |M|)

- **top-level statement**: `M : Type*` `[Group M] [Finite M] [Nontrivial M]` `(hMnil : IsNilpotent M)`,
  `[MulDistribMulAction H M]`, IsFrobeniusGroup H K R, hcop `(|H|,|M|)=1`, hCK `C_M(K)=1`
  (fixed-points-of-K = trivial), hcond3 prime-manner。C_M(R) = `{m | ∀ r∈R, (r:H)•m = m}` subgroup
  (`MulAction.fixedBy` / fixed-point subgroup)。結論 (a)(b)(c)。
- **induction**: `Nat.card M` 強帰納。
  - **base (M elementary abelian)**: `Additive M` に `Module (ZMod r)` を与えて既存 base leaf。
    (nilpotent + elementary abelian ⟺ M が elementary abelian; あるいは M_0 が無いとき)。
  - **step**: M_0 = maximal proper H-invariant normal subgroup (M nilpotent ⟹ solvable ⟹ H-chief
    factor M/M_0 が elementary abelian)。M_0 と M/M_0 に IH:
    - M_0: MulDistribMulAction H ↥M_0 (制限)、C_{M_0}(K)=M_0∩C_M(K)=1、hcond3 制限 ⟹ IH で (a)(b)(c)。
    - M/M_0: MulDistribMulAction H (M⧸M_0)、Prop 1.5(d) group 形で `C_{M/M_0}(K)=C_M(K)M_0/M_0=1`,
      `C_{M/M_0}(x)=C_M(x)M_0/M_0=C_M(R)M_0/M_0=C_{M/M_0}(R)` ⟹ IH で (b)(c)。
  - **glue (b)**: `|M|=|M_0|·|M/M_0|`, `|M/M_0|=|C_{M/M_0}(R)|^p=|C_M(R)M_0/M_0|^p=|C_M(R)|^p/|C_{M_0}(R)|^p`
    (Prop 1.5(d) order 公式) + (3.42) ⟹ `|M|=|C_M(R)|^p`。
  - **glue (c)**: cyclic C_M(R) ⟹ `K'⊆C_K(M_0)∩C_K(M/M_0)⊆C_K(M)` (Lemma 1.9 / chain stabilizer,
    S01 §1 に済)。

## ⚠ 2 つの action framework (要 bridge、実行時の主 friction)

- **base leaf** (`S03g_Thm310ElemAbelian`) = `[MulDistribMulAction H M]` (M CommGroup)。
- **coprime fixed-point / minimal-invariant-normal / chief-factor infra** = `φ : L →* MulAut H`
  形 (`CoprimeFixedPoints.lean`, `MinimalInvariantNormal.lean`, `S03h` の
  `fixedPointsOfMulAut_quotientMulAutHom_eq_map` = Prop 1.5(d) group 形,
  `coprime_fixedPoints_quotient`)。
- **bridge**: `MulDistribMulAction H M` から `φ : H →* MulAut M` を構成 (各 h の作用は M の自己同型;
  `MulDistribMulAction.toMulEquiv`/`toMulAut` 系)。逆に φ から subgroup/quotient への誘導作用。
  top-level statement は `MulDistribMulAction H M` で述べ (base leaf に合わせる)、coprime infra を
  使う箇所で φ に変換する。**この bridge が最初に解決すべき設計点。**

## 既存 infra (reuse)

- **chief factor**: `S03c_Thm37` / `S03h_Thm38` の chief-factor machinery (Thm 3.7/3.8 と構造同一)、
  `chiefFactorCentralizer`。
- **coprime fixed points (Prop 1.5(d) group 形)**: `OddOrder/GroupTheory/CoprimeAction.lean`,
  S03h の `fixedPointsOfMulAut_quotientMulAutHom_eq_map` 系。C_{M/N}(K)=C_M(K)N/N。
- **Lemma 1.9** (chain stabilizer, (c) glue): S01_Solvable §1 (済)。
- **nilpotent ⟹ solvable ⟹ chief factor elementary abelian**: mathlib `IsNilpotent.isSolvable` +
  `solvable_minimal_normal_isElementaryAbelian` (S03g_Thm310General で既使用)。

## 進捗 (2026-07-18)

- [x] **piece 1 (b)-glue 順序公式** ✅ commit 69516988: `S03g_Thm310FixedPointSplit.card_fixedSubgroup_eq_mul_of_mulDistribMulAction` — `|C_M(R)|=|C_{M₀}(R)|·|C_{M/M₀}(R)|` (MulDistribMulAction 形)。core は既存 `Ch04.card_fixedSubgroup_eq_mul_of_normal` (HartleyTurull)。framework bridge (`toMulAut` + `IsAInvariant.restrict/.quotientMulAutHom`) friction 無を確認。axiom-clean。
- [x] **piece 2 base (elem-abelian group form)** ✅ commit (S03g_Thm310GroupForm): `bgThm310_elemAbelian_group` — module leaf を group 形 (fixedSubgroup) で wrap。crux bridge `card_invariants_eq_card_fixedSubgroup` = invariants↔fixedSubgroup の card 一致 (`Equiv.subtypeEquiv Additive.toMul`)。(c) も統合済。axiom-clean。
- [ ] **piece 3 induction** 🔄 in flight (S03g_Thm310Nilpotent): general nilpotent M、`Nat.card M` 型多相強帰納、base=piece 2 (M H-chief ⟹ elem abelian)、step=piece 1 order 公式 + M_0 proper H-invariant normal (MinimalInvariantNormal `exists_aInvariant_normal_isElementaryAbelian`)。likely sticking = MulDistribMulAction on ↥M_0/M⧸M_0 の instance 構成。(c) は Lemma 1.9 で induction 内 glue。

**top-level statement shape (確定)**: `C_M(R) := fixedSubgroup (MulDistribMulAction.toMulAut H M) R` (Subgroup)。piece 1/2/3 全て同 `fixedSubgroup`+`IsAInvariant` framework で統一 (module 摩擦は piece 2 内に閉じ込め)。

## 完了条件

group-level `bgTheorem310_nilpotent` (general nilpotent M, general kernel, (a)+(b)+(c)) を book
strength・sorry-free・axiom-clean。AxiomsCheck 登録、survey 正本 Thm 3.10「済」+ BG §3 完成を記録。
⚠ 規模大 (1-3日、piece 分割推奨: (a) は M 非依存で即、(b) の Case-1 induction が本体、(c) は Lemma 1.9)。

## 参照

- issue 8013 (closed, elementary-abelian 全形完成、reuse map 精密)
- survey 正本 L318 (§3 summary)、BG mmd L1282-1357
- 既存: S03g_Thm310{,Core,ElemAbelian,General,Module}.lean (~1900 行)
