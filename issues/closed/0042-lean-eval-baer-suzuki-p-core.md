---
id: 42
slug: lean-eval-baer-suzuki-p-core
title: "lean-eval Baer-Suzuki problem (p-core 版) を解く"
created: 2026-05-28
---

# lean-eval Baer-Suzuki problem (p-core 版) を解く

## 背景

lean-lang.org の eval problem suite に Baer-Suzuki 定理の p-core 版が `sorry`
stub として提示されている:

  https://lean-lang.org/eval/problems/baer_suzuki/

signature:

```lean
theorem baer_suzuki {G : Type*} [Group G] [Finite G] {p : ℕ}
  [Fact p.Prime] (x : G) :
  x ∈ LeanEval.GroupTheory.Defs.pCore p G ↔
  ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))
```

> 「単一元 x が `O_p(G)` に属する ⇔ 任意の共役 `gxg⁻¹` と x の生成する閉部分群が p-群」

これは古典 Baer-Suzuki theorem (subset 版) の **単一元への特殊化** で,
[OddOrder/Isaacs/Ch02_Subnormality/Main.lean:1829](OddOrder/Isaacs/Ch02_Subnormality/Main.lean:1829)
の `le_fitting_iff_baer_sup_conj_isNilpotent` (Isaacs Thm 2.12, Baer の F(G) iff 形)
から **系として導出可能** な近縁定理.

### スコープ注記

本リポの主目的 (Feit-Thompson 形式化) では BG/Peterfalvi が p-core 版を直接呼ぶ
箇所が無いため, 通常進行では自動的には追加されない. この issue は
**「lean-eval を解く」観点だけ** で立てているオプショナルなもの — BG App.A や
Peterfalvi §2 等のクリティカルパスより優先度は低い.

## 導出の見取り図

Isaacs 2.12: `H ≤ F(G) ⇔ ∀ x ∈ G, ⟨H, H^x⟩` が冪零

から p-core 版を導く流れ:

1. `H := Subgroup.zpowers x` を取る (cyclic 部分群).
2. `⟨H, H^g⟩ = Subgroup.closure {x, gxg⁻¹}`.
3. RHS の "∀ g, p-群" 仮定 ⇒ 特に `g = 1` で `⟨x⟩` が p-群 ⇒ x は p-元.
4. p-群 は冪零なので Isaacs 2.12 適用 ⇒ `⟨x⟩ ≤ F(G)` ⇒ x ∈ F(G).
5. x は p-元 + x ∈ F(G) ⇒ x ∈ `O_p(F(G)) = O_p(G)`.
   (F(G) は冪零 ⇒ Sylow p-subgroup 一意 ⇒ それが `O_p(F(G)) = O_p(G)`.)
6. 逆向きは `O_p(G) ⊴ G` から共役で閉じている + O_p(G) は p-群なので trivial.

ボトルネックは step 5 の **F(G) → O_p(G) 橋渡し補題**.

## やること

1. [ ] **F(G) → O_p(G) 橋渡し補題の所在確認**
   - mathlib に `Subgroup.fitting` と `Subgroup.pCore p` 間の関係 (p-元 ∈ F ⇒ p-元 ∈ O_p)
     を与える補題があるか, memory `feedback_mathlib_api_3layer_lookup` の 3-layer で確認
   - 典型形: `IsPGroup p H → H ≤ Subgroup.fitting G → H ≤ Subgroup.pCore p G`
   - 無ければ `OddOrder/Isaacs/Ch02_Subnormality/` 内に補題追加 (F(G) は冪零 ⇒
     Sylow p-subgroup unique ⇒ それが O_p(G))
2. [ ] **p-core 版 statement を Isaacs 2.12 から導出**
   - 配置: [OddOrder/Isaacs/Ch02_Subnormality/Main.lean](OddOrder/Isaacs/Ch02_Subnormality/Main.lean)
     の 2B section 末尾 (Thm 2.12 iff の直後)
   - repo 内名: `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` 程度. docstring に
     `**Baer-Suzuki Theorem (p-core single-element form)**` と本での呼称を明記
3. [ ] **lean-eval signature との整合確認**
   - `LeanEval.GroupTheory.Defs.pCore p G` の定義を eval 側で確認.
     mathlib の `Subgroup.pCore p` と defeq or unfolding 一致なら直接, ズレていれば
     unfolding 補題で橋渡し
   - lean-eval submit 用には repo 内部 API への依存を最小化する形が望ましい
     (Isaacs 2.12 の証明本体は重いので, 提出用 self-contained 版が必要なら
     `notes/meta/lean_eval_baer_suzuki_self_contained.md` 等に複製)
4. [ ] **(option) subset 版 古典 Baer-Suzuki も同時に書く**
   - `X ⊆ Subgroup.pCore p G ↔ ∀ a b ∈ X, IsPGroup p ⟨a, b⟩`
   - 単一元版から数行で出る. lean-eval が将来 subset 版を追加した場合のため

## 完了条件

- [OddOrder/Isaacs/Ch02_Subnormality/Main.lean](OddOrder/Isaacs/Ch02_Subnormality/Main.lean)
  に, lean-eval signature と equivalent な theorem が `sorry`/`axiom` なしで存在
- `lake build OddOrder` green
- docstring に Isaacs Thm 2.12 への trace + lean-eval URL を記載
- lean-eval problem に提出可能な形になっていること
  (mathlib + Isaacs Ch02 既存定理のみへの依存. self-contained 版が必要なら別途記録)

## 参照

- lean-eval URL: https://lean-lang.org/eval/problems/baer_suzuki/
- Isaacs FGT Thm 2.12 (Baer) 原文: `references/isaacs/finite-group-theory.mmd` L1141-1180
- 既存実装: [OddOrder/Isaacs/Ch02_Subnormality/Main.lean:1829](OddOrder/Isaacs/Ch02_Subnormality/Main.lean:1829)
  `le_fitting_iff_baer_sup_conj_isNilpotent` (iff 完全形)
- 関連 wrapper policy: CLAUDE.md "ラッパー方針" — 本 issue は単なる rename ではなく
  F(G) → O_p(G) の真の翻訳を含むので no-wrapper policy には抵触しない
- 同 ch.2 内の Baer 応用例: Zenkov (`OddOrder/Isaacs/Ch02_Subnormality/Main.lean:3501`),
  Matsuyama Thm 2.13 (同 file:2000)

## 結果 (2026-05-28 close)

- [x] **F(G) → O_p(G) 橋渡し補題**: 既存 `mem_opCore_of_le_fitting_of_isPGroup`
  ([Ch02 Main.lean:1973](../../OddOrder/Isaacs/Ch02_Subnormality/Main.lean#L1973))
  を `private` から解除 (Matsuyama と本定理で共用).
- [x] **`baerSuzuki_pCore` 実装**: [Ch02 Main.lean](../../OddOrder/Isaacs/Ch02_Subnormality/Main.lean)
  2B 末尾 (Matsuyama の後). `mem_opCore_of_le_fitting_of_isPGroup`
  + Isaacs 2.12 iff (`le_fitting_iff_baer_sup_conj_isNilpotent`) の合成で 80 行弱.
- [x] **CI 公理保証**: [`AxiomsCheck.lean`](../../OddOrder/AxiomsCheck.lean) に
  `#assert_only_allowed_axioms OddOrder.Isaacs.Ch02.baerSuzuki_pCore` 追加.
  `{propext, Classical.choice, Quot.sound}` のみ依存.
- [x] **lean-eval submit 対応メモ**:
  [`notes/meta/lean_eval_submission.md`](../../notes/meta/lean_eval_submission.md) §2
  に `LeanEval.Defs.pCore = opCore` の対応と submit 戦略を記録
  (旧 `lean_eval_baer_suzuki.md` を 2026-07-22 に統合).
- [ ] (option) subset 版 — 未実装 (lean-eval が subset 版を追加した時点で対応).

`lake build OddOrder` green, full AxiomsCheck pass.
