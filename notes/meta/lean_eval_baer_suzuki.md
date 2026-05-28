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

### 提出方法 — self-contained 化 (採用)

**機密性制約**: 本 repo は Feit-Thompson 形式化 (BG App.A, Peterfalvi §§1-14)
の進行中作業を含む. `OddOrder` を直接 `import` する形で submit すると, 依存閉包
解決時に未公開の補助補題群・命名・章割り構成等が lean-eval 比較器側に露出する.
これを避けるため, **必要最小コードを別 repo にコピーして self-contained submission**
とする.

別 repo 位置: [`../../../baer_suzuki/`](../../../baer_suzuki/) (lean-eval ローカル
workspace, `Submission.lean` + `Submission/Helpers.lean` を編集).

#### 移植スコープ (最小化)

`baerSuzuki_pCore` のクロージャ閉包 — 抽出すべき定義/補題:

| 項目 | 本 repo 所在 | 役割 |
|---|---|---|
| `opCore`, `opCore.normal`, `opCore_isPGroup`, `normal_pgroup_le_opCore` | Ch01 Main.lean (L533 周辺) | `O_p(G)` 定義と最大性 |
| `fitting`, `fitting.normal`, `fitting.isNilpotent`, `nilpotent_normal_le_fitting` | Ch01 Main.lean | `F(G)` 定義と最大冪零正規性 |
| Wielandt Zipper Lemma (`zipper_lemma`) と支援補題群 | Ch02 Main.lean:697 周辺 | Isaacs Thm 2.12 逆方向の核 |
| `le_fitting_iff_baer_sup_conj_isNilpotent` | Ch02 Main.lean:1829 | Isaacs Thm 2.12 iff |
| `mem_opCore_of_le_fitting_of_isPGroup` | Ch02 Main.lean:1976 | F(G) → O_p(G) 橋渡し |
| `baerSuzuki_pCore` 本体 | Ch02 Main.lean:2134 | 単一元 Baer-Suzuki |

提出時には `LeanEval.GroupTheory.Defs.pCore = opCore` の extensionality 補題を
`Submission/Helpers.lean` に書き signature 整合.

機密性のため移植コードは命名・コメントを **lean-eval 側 namespace**
(`Submission.Helpers` 等) に rebrand し, 本 repo の `OddOrder.Isaacs.Ch0X` 命名・
章割り情報は持ち出さない. 出典 (Isaacs FGT § 等) のみ記載可.

#### 不採用: 直接 submit (`import OddOrder`)

`import OddOrder` + ext 補題 2 行案は手軽だが, lean-eval 比較器側へ
`OddOrder` 全モジュール (BG/Peterfalvi 含む) のシンボル名・補助補題構成が露出し,
進行中の Feit-Thompson 形式化の進捗情報が漏れる. 機密性の観点で却下.

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
- 2026-05-28: 提出方針を **self-contained 化** へ変更. `import OddOrder` 案は
  機密性 (Feit-Thompson 進捗情報の流出) の観点で却下. `../baer_suzuki/` workspace
  に必要最小コードをコピーして submit する方針へ.
