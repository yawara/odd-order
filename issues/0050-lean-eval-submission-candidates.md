---
id: 50
slug: lean-eval-submission-candidates
title: "lean-eval 提出候補の定理を棚卸し・パイプライン化"
created: 2026-05-30
---

# lean-eval 提出候補の定理を棚卸し・パイプライン化

## 背景

`leanprover/lean-eval` (公開面 https://lean-lang.org/eval/) は **comparator 方式**の公式
formal-math ベンチ。problem ごとに `Challenge.lean` が文を固定し, 解答者が `Submission.lean`
で証明 → **comparator が受理したら solved**。解答側は **Mathlib 自由使用可**。トピック
フォルダに `GroupTheory` / `Algebra` / `RepresentationTheory` があり, 本リポ (3 冊の形式化) は
「mathlib にまだ無い研究級の有限群論定理」を量産できる立場なので, lean-eval の弾の鉱脈。

**既提出**: `baer_suzuki` (2026-05-29, issue 0042) / **`feit_thompson` (2026-07-16)**。

「良い challenge / 解きやすい submission」の 3 軸:
1. **有名・名前がある** (ベンチ価値)
2. **statement が mathlib 既存 def だけで self-contained** (comparator が文を pin する。
   自作 def への依存が少ないほど提出が楽。ただし `Defs/*.lean` への小さな持ち込みは前例あり)
3. **証明が難しく mathlib 未収録** (でないとベンチにならない)

## 📋 候補一覧 (2026-07-19 全面差し替え)

> **正本 = [`notes/meta/lean_eval_candidates_2026_07_19.md`](../notes/meta/lean_eval_candidates_2026_07_19.md)**
> — 79 エージェント fan-out (発掘 4 スライス + 既存 11 件再測 + lean-eval recon → 候補 77 件を
> 敵対的検証 → 68 件通過 / 4 件 reject) の実測結果。strong 31 件 + viable 27 件の全表、
> トップ 5 の statement 素案、reject 理由、lean-eval 側の problem 一覧・提出フローを収録。
> 本 issue には要約のみ置く。
>
> ⚠ **旧表 (2026-05-30) は破棄**。事実誤認 3 件: Frobenius 核存在は repo に**不在** /
> Burnside 正規 p-補群は **mathlib 収録済** (`MonoidHom.ker_transferSylow_isComplement'`) /
> Brauer–Fowler は repo に**不在** (Gorenstein 由来ゆえ恒久スコープ外、かつ eval では既に Solved)。

### 最優先 5 件 (verdict = strong, bespoke def ほぼゼロ)

| # | 定理 | repo の Lean 名 | mathlib | 備考 |
|---|---|---|---|---|
| 1 | **Jordan の定理** (素数長サイクルを含む原始群 ⊇ Aₙ) | `Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` | **`proof_wanted` が同一 signature で存在** (`Mathlib/GroupTheory/GroupAction/Jordan.lean:462`) | bespoke 0・焼き込み不要。理想形 |
| 2 | **Chermak–Delgado 定理** (Isaacs 1.41) | `Subgroup.chermakDelgado` | absent ("chermak" 0 hit) | statement 1 行・完全 mathlib 語彙 |
| 3 | **Furtwängler 主イデアル定理** (Isaacs 10.18) | `Isaacs.Ch10.transfer_commutator_eq_one` | absent | statement 3 行 / 証明は群環 Witt 計算 2,500 行 |
| 4 | **Thompson: FPF 作用 ⇒ 冪零** (Isaacs 6.24) | `Isaacs.Ch06.isNilpotent_of_isFrobeniusAction` | absent | 既存 `frobenius_kernel_isNormal` の自然な次段 |
| 5 | **PSL(n,K) の単純性** (Isaacs 8.33) | `Isaacs.Ch08.isSimpleGroup_projectiveSpecialLinearGroup` | partial (PSL の def と Iwasawa 判定はあるが単純性は無い) | bespoke 0 |

次点: **Hall E/C/D** (知名度最上位、`IsHallSubgroup` 2 行の展開のみ) / Dietzmann (5.10) /
`finrank_dvd_card` / Thompson critical subgroup。

### lean-eval 側の状況 (2026-07-19 実測)

- GroupTheory の**未解決**: `glauberman_zStar` / `brauer_suzuki` / `gorenstein_walter` /
  `schreier_conjecture` / `five_transitive_card_classification` / `higman_infinite_simple` /
  `novikov_unsolvable`。RepresentationTheory は `brauer_splitting_field` が未解決。
- **新規 problem の提案は可能** — `leanprover/lean-eval` への PR (`@[eval_problem]` +
  `manifests/problems/<id>.toml`)。外部 PR の merge 実績あり。mathlib 非収録の定義は
  `Defs/*.lean` に小さく持ち込んでよい (`Defs/PCore.lean` / `Defs/OddCore.lean` の前例)。

## やること

- [ ] **(提案) Jordan の定理を problem 提案 PR で出す** — mathlib が `proof_wanted` で明示的に
      欲しがっており bespoke def ゼロ。`lake exe lean-eval validate-manifest` +
      `check-problem-build` で検証してから PR
- [ ] **(提案) Chermak–Delgado / Furtwängler / Thompson FPF-nilpotency の 3 本**を続けて提案 PR。
      提案 PR を先に merge させ、solver 側は他者に開放してよい (`feit_thompson` の前例)
- [ ] **(解答) GroupTheory の未解決 3 問の着手判断** — 順序は `glauberman_zStar` →
      `brauer_suzuki` → `gorenstein_walter` (最後は Bender method + signalizer functor + Z\* 依存)。
      `schreier_conjecture` / `five_transitive_card_classification` は CFSG 依存で着手しない
- [ ] **(整備) AxiomsCheck 未登録の strong 候補を登録** — Ch08 の Jordan / PSL 単純性、
      `GroupTheory.isCritical_exists`、`GroupTheory.transfer_transfer`、Ch01 の Fitting 系、
      `RepresentationTheory.span_range_representation_eq_top` (いずれも `#print axioms` で clean 実測済)
- [ ] **(整備) stale docstring の掃除** — `burnside_p_pow_q_pow` の「local axiom に封じ込め」、
      `Ch07.normal_J` の「Remaining local axioms」、`AppC_NormSet` の「Proof (to be formalized)」、
      `brauer_permutation_lemma'` の「Isaacs Thm 6.32」誤引用ほか (詳細は note §4-5)。
      提出物に写すと誤解を招く
- [ ] `notes/meta/lean_eval_baer_suzuki.md` のパス修正 (提出 workspace は
      `/home/ywr/lean-eval-submissions/baer_suzuki`、note の `../../../baer_suzuki/` は stale)

## 完了条件

- アンブレラ issue。上記 4 本の提案 PR がそれぞれ per-theorem sub-issue (0042 型) に落ちきったら close。
- 単発の提出そのものは各 sub-issue 側の完了条件 (eval submit 可能形 + `AxiomsCheck` pass) に従う。

## 参照

- **候補の正本**: [`notes/meta/lean_eval_candidates_2026_07_19.md`](../notes/meta/lean_eval_candidates_2026_07_19.md)
- lean-eval: https://github.com/leanprover/lean-eval / 提出先 https://github.com/leanprover/lean-eval-submissions / 公開面 https://lean-lang.org/eval/
- 先行: issue 0042 (Baer-Suzuki), [`notes/meta/lean_eval_baer_suzuki.md`](../notes/meta/lean_eval_baer_suzuki.md)
- 文献: 100定理の未形式化は幾何/解析/超越数中心で群論の低い果実は無い
  (https://leanprover-community.github.io/100-missing.html); research-level は SOTA でも
  pass 率 ~10% (RLMEval, https://arxiv.org/pdf/2510.25427)

## 🧾 履歴

- 2026-07-02 hub レビューで「off-FT-path につき park」とされたが、**2026-07-16 に FT 本体が
  axiom-clean 完成 → 全 3 冊フェーズへ移行**したため park の前提は失効。本 issue は再び active。
- 2026-07-19 候補表を実測で全面差し替え (上記 note)。
