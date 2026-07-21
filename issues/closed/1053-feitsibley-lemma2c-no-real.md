---
id: 1053
slug: feitsibley-lemma2c-no-real
title: "FeitSibley Lemma 2(c): 𝒮 に実指標なし — Clifford single-orbit ルートで完全証明"
created: 2026-07-21
---

# FeitSibley Lemma 2(c): 𝒮 に実指標なし — Clifford single-orbit ルートで完全証明

## 背景

Peterfalvi Appendix IV (pp. 144–150) Lemma 2(c): 「d = |D| が奇なら χ ∈ 𝒮 は実でない
(χ̄ ≠ χ)」。1051 (Lemma 2(a)) / 1052 (Lemma 2(b)) に続く FeitSibley.lean の上流 frontier。
残っていた形式化ギャップは 2 点だった:

1. **制限ステップ**: 原文は「Res_{Q₁D} Ind_Q^H φ = Ind_{Q₁}^{Q₁D} θ が既約」という
   Mackey 型計算を経由する。
2. **|Q₁D| の奇性の出所**: 原文の証明は「odd order group Q₁D」と書くが、仮定ブロックは
   d odd しか与えない。

## 決着 (2026-07-21, commit 参照)

**statement 裁定 — `Odd |Q₁|` を明示仮定に追加**。d odd + 「Q₁ は 2-群でない」+ D の
f.p.f. 作用だけでは |Q₁| 奇は出ない (例: Q₁ = V₄ × C₇ に D = C₃ が f.p.f. 作用、
θ = V₄ 成分の非主実指標が反例候補 — ambient TI の存在までは未検証だが、少なくとも原文の
証明はこの構成に対して機能しない)。原文が「odd order group Q₁D」と書けるのは Theorem 側の
還元 (1)(2) 後 — そこでは Q₁ が単一素数 p の p-群かつ「2-群でない」ので p ≠ 2、|Q₁| 奇が
自動で立つ。よって 2(c) の honest な形式化は `hd : Odd hyp.d` + `hQ1odd : Odd (Nat.card ↥hyp.Q1)`
の 2 仮定 ([[repo-stronger-hypothesis-is-specialization-not-gap]] の逆方向:
書籍 statement の overclaim を証明可能な形に絞る)。Theorem (`feit_sibley_coherence`) の
statement は書籍どおり d odd のみで据え置き (還元後に oddness を導出する)。

**証明 — Mackey 制限計算を完全回避** (原文ルートより短い):

1. χ ∈ 𝒮 real と仮定。非自明成分 θ ∈ Irr(Q₁) を取る
   (`exists_ne_trivial_liesOver_of_not_forall_eq_one`)。
2. χ real ⟹ Res χ real ⟹ θ̄ も成分 (`inner_conj_conj` ZIrrFourier 版 +
   `(Res χ).conj = Res (χ.conj)` は rfl)。
3. **Clifford single-orbit** (`restrictionConstituentsSingleOrbit_of_isIrreducible`,
   CliffordSingleOrbit.lean — 完全証明済を発見) で θ̄ = θ^g, g ∈ H。
4. g = q·δ (`exists_mem_Q_mul_mem_D_subtype`)、Q は Irr(Q₁) に自明作用
   (`Q_conjBy_eq`) ⟹ θ̄ = θ^δ, δ ∈ D。
5. θ^{δ²} = θ̄̄ = θ ⟹ δ² ∈ I_H(θ) = Q (`inertia_theta_eq_Q`)。δ² ∈ D でもあり
   Q ⊓ D = ⊥ ⟹ δ² = 1。δ の位数は d の約数で奇 ⟹ δ = 1 ⟹ θ̄ = θ。
6. θ は奇数位数群 Q₁ の非自明実既約指標 — Peterfalvi (1.1)
   (`not_isReal_of_ne_trivial_of_odd_card'`) に矛盾。

原文の「Q₁D への制限が既約」(Isaacs 6.34 Frobenius + Mackey) は一切不要になった。
1051 で整備済みの慣性群インフラ (`inertia_theta_eq_Q` 系) がそのまま効いた形。

## 技術メモ

- `(Res_N χ).conj = Res_N (χ.conj)` を `ext` + rw 連鎖で示そうとすると
  ClassFunction = ↥(classFunctionSubmodule) の defeq 不一致で instances-transparency
  エラー ([[lean-instance-defeq-traps]] 型)。**rfl ブリッジ** (`have h1 : _ = Res (χ.conj) := rfl`)
  で回避。
- `IrreducibleCharacter.liesOver_iff` は (χ) (θ) 2 明示引数 + H — term 適用より
  `rw ... at` の方が安全。
- `θ^{δ²} = θ` の導出は CliffordDecomposition.lean `conjBy_ne_conj_of_odd` の
  hg2 パターン (conjBy_mul + conj 交換 + conj_conj) を移植。conj 交換
  (`(θ^δ)̄ = (θ̄)^δ`) は inline ext 4 行 (CliffordDecomposition への import 追加不要)。

## 完了条件

- [x] `hasNoRealCharacters_Sset` sorry-free (build green 4375 jobs)
- [x] axiom-clean (`propext`/`Classical.choice`/`Quot.sound` のみ、#print axioms 実測)
- [x] census テーブル + Theorem docstring 更新 (残 prerequisite = step (7) 類算congruence のみ)

## 参照

- `OddOrder/Peterfalvi/Appendices/FeitSibley.lean` (`hasNoRealCharacters_Sset`)
- `OddOrder/GroupTheory/RepresentationTheory/CliffordSingleOrbit.lean`
  (`restrictionConstituentsSingleOrbit_of_isIrreducible`)
- `references/peterfalvi/pdf/09.0_pp_144_150_The_Feit-Sibley_Theorem.pdf` p.145 (原文確定は
  PDF ページ画像 — pdftotext は文字散乱で不可)
- issue 1049 (Lemma 1(a)) / 1051 (Lemma 2(a)) / 1052 (Lemma 2(b))
- 下流 = `feit_sibley_coherence` (Theorem, pp. 146–150 の 8 ステップ; 残 sorry は step (7)
  class-sum congruence が主ギャップ)
