---
id: 9110
slug: module-induced-clifford
title: "Shared infra claim: module-level induced-rep irreducibility (Clifford corresp.) over general alg-closed field"
created: 2026-07-18
---

# Shared infra claim: module-level induced-rep irreducibility over general alg-closed field

## ⚠ 撤回 (2026-07-18, 起票と同日)

**この claim は不要と判明。close する。** BG Lem 2.3 case (ii) は induced-representation を
経由せずに済む: M を p 個の conjugate simple 部分加群 `ρ(x^i)L` の**内部直和**として
直接与えられる (G-不変性 ⟹ M 既約から全体を張る; pairwise 非同型 simple ⟹ 直和)。
よって `dim M = p·dim L` が multiplicity/induced module 抜きで出る。必要 infra は
CliffordAlgClosed の既存 `conjSemilinearEnd` 機構 + 小さい directness lemma のみ
(module-level induced Clifford の shared infra は不要)。詳細は [[3008]] case (ii)。

module-level induced Clifford が将来別文脈で必要になったら改めて claim すること。

---

## claim (lane c, 2026-07-18) [撤回済]

lane c が **module-level** の induced-representation 既約性 / Clifford correspondence を
**general algebraically closed field 上** (任意標数) で構築することを claim する。
着手前に既存を検索済み: repo の Clifford correspondence は全て **ℂ character-level**
(`CliffordCorrespondence`, `CliffordDecomposition`, `InducedIrreducible` — 全て ClassFunction/ℂ)。
mathlib は `Rep.ind` (Mathlib/RepresentationTheory/Induced.lean) を持つが **既約性の結果は無い**。
module-level (Representation k G V / asModule / IsSimpleModule) over general field は未形式化。

## やること (最小)

BG Lem 2.3 (issue 3008) case (ii) が要求する brick:

- [ ] `L` simple `k[H]`-module, inertia_G(L) = H (全 conjugate が非同型) ⟹ simple `M ⊇_H L`
      の `L`-isotypic component の次元 = `dim L` (multiplicity e=1)、ゆえに
      `dim M = [G:H]·dim L`。
- [ ] ルート案: module-level Frobenius reciprocity (`Hom_kG(M, Ind L) ≅ Hom_kH(M_H, L)`) +
      isotypic socle injection `S ⊗_{End S} Hom(S,N) ↪ N`、または
      End_{kG}(M)=k = End_{kH}(M_H) の ρ(x)-fixed points の次元計算 = e²。

## 完了条件

module-level induced Clifford brick が sorry-free で、issue 3008 (BG Lem 2.3) case (ii) を
閉じられる。配置: 新 leaf `OddOrder/GroupTheory/RepresentationTheory/CliffordInducedDimension.lean`
(仮) または `CliffordAlgClosed` 系の sibling。lane c 所有。

## 参照

- consumer: [[3008]] BG Lem 2.3
- 他レーンへ: module-level induced Clifford が必要になったら本 issue を見て重複構築を避ける
  (character-level ℂ 版は既存)。
