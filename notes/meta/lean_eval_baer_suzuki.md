# lean-eval Baer-Suzuki problem (p-core 版) 対応メモ

issue: [#0042](../../issues/closed/0042-lean-eval-baer-suzuki-p-core.md) (closed 2026-05-28)
lean-eval URL: <https://lean-lang.org/eval/problems/baer_suzuki/>

## 問題

lean-eval が提示する signature:

```lean
theorem baer_suzuki {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (x : G) :
    x ∈ LeanEval.GroupTheory.Defs.pCore p G ↔
    ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))
```

> 「単一元 `x` が `O_p(G)` に属する ⇔ 任意の共役 `gxg⁻¹` と `x` が生成する閉部分群が `p`-群」

## 本 repo の実装

[`OddOrder.Isaacs.Ch02.baerSuzuki_pCore`](../../OddOrder/Isaacs/Ch02_Subnormality/Main.lean)
(2B section 末尾, Matsuyama 2.13 の後).

```lean
theorem baerSuzuki_pCore [Finite G] {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ opCore p G ↔
      ∀ g : G, IsPGroup p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G))
```

`Subgroup` の coercion (lean-eval は subset 流の `IsPGroup p (closure ...)` で型強制
省略、本 repo は明示的 `↥` 強制) 以外は signature 一致。

## 証明の流れ

Isaacs Thm 2.12 (`le_fitting_iff_baer_sup_conj_isNilpotent`,
`H ≤ F(G) ↔ ∀ x, ⟨H, H^x⟩` 冪零) の `H := ⟨x⟩` 特殊化 + `p`-元の `F(G)` ⇒ `O_p(G)`
橋渡し (`mem_opCore_of_le_fitting_of_isPGroup`) の合成:

1. **順方向** `x ∈ O_p(G) ⇒ ∀ g, ⟨x, gxg⁻¹⟩ p-群`:
   `O_p(G) ⊴ G` で共役不変 ⇒ `closure {x, gxg⁻¹} ≤ O_p(G)`,
   `O_p(G)` が `p`-群なのでその部分群も `p`-群.

2. **逆方向** `∀ g, ⟨x, gxg⁻¹⟩ p-群 ⇒ x ∈ O_p(G)`:
   - `g = 1` で `closure {x, x} = ⟨x⟩` が `p`-群.
   - 各 `g` で `⟨x⟩ ⊔ MulAut.conj g • ⟨x⟩ = closure {x, gxg⁻¹}` は `p`-群
     ([`IsPGroup.isNilpotent`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Nilpotent.html#IsPGroup.isNilpotent)
     で冪零).
   - Isaacs 2.12 iff (`le_fitting_iff_baer_sup_conj_isNilpotent`) で `⟨x⟩ ≤ F(G)`.
   - 橋渡し補題 `mem_opCore_of_le_fitting_of_isPGroup` で `⟨x⟩ ≤ O_p(G)`,
     `x ∈ ⟨x⟩ ≤ O_p(G)`.

CI: [`OddOrder/AxiomsCheck.lean`](../../OddOrder/AxiomsCheck.lean) で
`#assert_only_allowed_axioms OddOrder.Isaacs.Ch02.baerSuzuki_pCore` により
`{propext, Classical.choice, Quot.sound}` のみ依存 を CI 保証.

## lean-eval submit 用の橋渡し

eval 側の `LeanEval.GroupTheory.Defs.pCore p G` は問題説明文によれば
「正規 `p`-部分群の supremum」(= 最大正規 `p`-部分群).
本 repo の `OddOrder.Isaacs.Ch01.opCore p G` も
`Subgroup.Normal.isP` で「最大正規 `p`-部分群」と等価:

- 包含 `≤`: `opCore_isPGroup` + `opCore.normal` ⇒ `opCore p G` 自体が正規 `p`-部分群 ⇒
  `≤ ⨆ {N | N.Normal ∧ IsPGroup p N}`.
- 包含 `≥`: `Subgroup.Normal` `IsPGroup` な任意の `N` は `normal_pgroup_le_opCore`
  ([Ch01 Main.lean](../../OddOrder/Isaacs/Ch01_Sylow/Main.lean#L605)) で
  `N ≤ opCore p G`, よって `sup ≤ opCore p G`.

つまり `opCore p G = LeanEval.Defs.pCore p G` (extensionality + 最大性).

### 提出方法 (2 通り)

1. **直接 submit**: eval submission の preamble に本 repo の `OddOrder` import + 2 行の
   `pCore = opCore` ext 補題を書く. 依存閉包は重い (Isaacs Ch01-2 + mathlib)
   が, sorry/axiom-free が保証されているため eval-checker は通る想定.

2. **self-contained 化** (将来必要なら):
   - Isaacs 2.12 iff の Zipper Lemma 経由証明 (本 repo `le_fitting_of_baer_aux`
     L1718) を eval 側に展開. mathlib `Sylow.normal_of_isNilpotent`,
     `Subgroup.Normal.conj_smul_eq_self` などの mathlib API は使える前提.
   - 行数概算: 補助 `le_fitting_aux` (L272), `le_fitting_of_baer_aux` (L1718),
     `mem_opCore_of_le_fitting_of_isPGroup` (L1973) で本体 ~250 行. Wielandt Zipper
     Lemma (Ch01 想定) も必要なので, **self-contained 化はコスト高** (Isaacs Ch01
     の Zipper 周辺をまるごと移植する必要).

現状は **1. 直接 submit** が現実的. 2. が要求された時点で再評価.

## 関連定理

- [Isaacs Thm 2.12 iff (Baer)](../../OddOrder/Isaacs/Ch02_Subnormality/Main.lean):
  `le_fitting_iff_baer_sup_conj_isNilpotent` (本 issue の母定理)
- [Isaacs Thm 2.13 (Matsuyama)](../../OddOrder/Isaacs/Ch02_Subnormality/Main.lean):
  `matsuyama` (橋渡し補題 `mem_opCore_of_le_fitting_of_isPGroup` を共有する近縁定理)
- [古典 Baer-Suzuki theorem (subset 版)]:
  `X ⊆ O_p(G) ↔ ∀ a b ∈ X, ⟨a, b⟩` `p`-群. 単一元版から数行で出るが, 本リポでは
  未実装 (BG/Peterfalvi クリティカルパス外). lean-eval が subset 版を将来追加した
  場合に対応.

## 履歴

- 2026-05-28: `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` 実装 (issue #0042 close).
  `mem_opCore_of_le_fitting_of_isPGroup` を `private` 解除 (Matsuyama+本定理で共有).
