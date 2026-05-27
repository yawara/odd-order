---
id: 39
slug: peterfalvi-2-7-adjoint-formula
title: "Peterfalvi (2.7) adjoint formula の sorry を埋める"
created: 2026-05-27
---

# Peterfalvi (2.7) adjoint formula の sorry を埋める

## 背景

`OddOrder/Peterfalvi/S04_DadeIsometry.lean` の `adjoint_formula` (Peterfalvi (2.7))
が唯一の `sorry`. §4 で最も多く外部引用される補題 (§7, §9, §12×2, §13, §16×2 =
外部 7 cite). 直前コミット 0782571 で statement と `adjointAverageFun` のみ追加済み.

教科書は証明を「On taking (2.4) into account, ...」の一行で済ませているが、実体は
**共役類カウンティング (orbit-stabilizer) を要する大きな証明**.

## 証明の数学的構造 (確定)

目標: `⟨α^τ, χ⟩_G = ⟨α, ψ⟩_L`, ただし `ψ(a) = |H(a)|⁻¹ ∑_{x∈H(a)} χ(ax)`.

**代表系 T を選ぶ Finset 分割を回避**し、三重和の double-count に組み替える:

    M := ∑_{a∈A} ∑_{x∈H(a)} ∑_{t∈G} (1/|H(a)|)·α(a)·\overline{χ}(t·(a·x)·t⁻¹)

- **Way 1 (易)**: 内側 `∑_t \overline{χ}(t·g·t⁻¹) = |G|·\overline{χ}(g)` (χ はクラス関数).
  ⟹ `M = |G| ∑_{a∈A} α(a)·\overline{ψ(a)}` (ψ の定義より).
- **Way 2 (難, カウンティング)**: `g := t·(a·x)·t⁻¹` でまとめ直す.
  `M = ∑_g \overline{χ}(g)·W(g)`, `W(g) = ∑_{(a,x,t):...=g}(1/|H(a)|)α(a)`.
  各 `g∈dadeSupport` について `W(g) = |L|·α^τ(g)` を示す ⟹ `M = |L| ∑_g α^τ(g)\overline{χ}(g)`.

両者を等置: `|L| ⟨α^τ,χ⟩_G·|G| = |G| ⟨α,ψ⟩_L·|L|` 相当 → 正規化込みで結論.

### 核心 = fiber count

`W(g)` 計算の中核は、各 `a∈A` 固定で

    P(a,g) := #{(x,t) ∈ H(a)×G : t·(a·x)·t⁻¹ = g} = |C_G(a)|   (g∈(aH(a))^G のとき; 否なら 0)

証明: `P(a,g) = |C_G(g)|·#{x∈H(a): a·x ~_G g}`,
`#{x∈H(a):a·x~g} = C_G(a)-orbit of x₀` (rigidity 経由),
`|C_G(a·x₀)| = |C_{C_G(a)}(x₀)| = Stab`,
orbit-stabilizer で `P = |Stab|·|orbit| = |C_G(a)|`.

そして `{a∈A : g∈(aH(a))^G} = a₀^L` (2.4.b + 2.4.a), `|a₀^L|=|L|/|C_L(a₀)|`,
`|C_G(a)|/|H(a)| = |C_L(a)|` ⟹ `W(g) = |a₀^L|·|C_L(a₀)|·α(a₀) = |L|·α(a₀) = |L|α^τ(g)`.

## やること

- [x] 基礎: commuting coprime 元の CRT 指数抽出 + 共役 rigidity
      → `OddOrder/GroupTheory/CoprimeConjugacy.lean`
      (`exists_pow_eq_self_and_forall_pow_eq_one`, `conj_fixes_of_commute`) — commit a6a1514
- [x] fiber count `P(a,g)=|C_G(a)|` → `card_conj_fiber`
      (orbit-stabilizer は不要、fiber=C_G(a) コセットの全単射で直接) — commit 7cbc6b6
      付随: `card_conjugatorBy_eq_card_centralizer`
- [x] (2.4.b): cross-rigidity `isConj_of_isConj_mul` (commit b531ca5) +
      S04 `Hypothesis.isConj_in_L_of_mul_H` (commit 18ee01c).
      付随 helper: `commute_of_mem_H`, `orderOf_dvd_card_centralizerIn`
- [ ] **⚠ Hypothesis 符号化の修正が必要 (BLOCKER)**: 下記参照
- [ ] `|C_G(a)| = |H(a)|·|C_L(a)|` (正規性フィールド追加後)
- [ ] `|a^L|·|C_L(a)| = |L|` (L 内 orbit-stabilizer)
- [ ] S04 で三重和 double-count 組立 + 正規化 (star/inv, supportedness, ψ averaging)
      + `adjoint_formula` に `HConjInvariant` 前提を追加

## ⚠ 発見: Hypothesis 符号化が (2.2.b) の ⋊ より弱い

現在の `Hypothesis` は (2.2.b) `C_G(a) = H(a) ⋊ C_L(a)` を
`centralizer_eq_sup` (join `H a ⊔ C_L a`) + `centralizer_disjoint` (`H a ⊓ C_L a = ⊥`)
で符号化しているが、**H(a) が C_G(a) で正規であること (⋊ の核心) が落ちている**.

- join + disjoint だけでは `|C_G(a)| = |H(a)|·|C_L(a)|` は**導けない** (一般に
  `|H ⊔ K| ≠ |H||K|`; 集合積 `HK` が部分群 = 一方が正規, が必要).
- `card_conj_fiber` の適用にも `hnorm` (C_G(a) が H(a) を正規化) が必要.

**修正案**: `Hypothesis` に field 追加:
```
H_normalized : ∀ (a : {a // a ∈ A}) (c : G),
  c ∈ Subgroup.centralizer {a.1} → ∀ x ∈ H a, c * x * c⁻¹ ∈ H a
```
- `of_isTISubset` (H=⊥): `c*x*c⁻¹ ∈ ⊥` は x=1 から自明.
- `restrict`: H 不変なので持ち越し.
これで `|C_G(a)|=|H||C_L|` (H 正規 ⟹ join=集合積 ⟹ 位数積) と fiber count 適用が可能.

## 完了条件

`adjoint_formula` の `sorry` が消え、`lake build OddOrder.Peterfalvi.S04_DadeIsometry`
が通る.

## 参照

- 教科書: `references/peterfalvi/04.4_pp_10_14_The_Dade_Isometry.mmd` (2.7) の証明
- ミニロードマップ: `notes/peterfalvi/s04_dade_isometry.md`
- 直前コミット: 0782571 (statement 追加)
- π-part 一般理論は **不要** (commuting coprime に対し CRT で具体的指数 k を作れば足りる)
