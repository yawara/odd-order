---
id: 50
slug: lean-eval-submission-candidates
title: "lean-eval への proof 提出 (tracker)"
created: 2026-05-30
---

# lean-eval への proof 提出 (tracker)

> **正本 = [`notes/meta/lean_eval_submission.md`](../../notes/meta/lean_eval_submission.md)** (単一ドキュメント)。
> playbook・候補全表 (proof submit 監査 §2.5 / proposal Tier A/B/C)・reject 記録・eval 側仕様は**全てそこ**。
> 本 issue は actionable checklist のみを持つ tracker。個別作業は per-problem sub-issue (0042 型) を切る。
>
> **用語規約 (2026-07-24, ユーザー指示)**: 「submit」= **proof submit (既存 problem への解答提出)
> のみ**。新規 problem の追加は **proposal (提案)** と呼ぶ。「他者 solved 済み」は proof submit
> 候補の除外理由にならない (per-account sticky) — この絞りの誤りで Burnside p^aq^b 等を
> 見落としていた (正本 note §2.5 の全数監査で訂正)。
>
> 2026-07-22 に旧 3 note (baer_suzuki / candidates_2026_07_19 / forward_list_2026_07_22) を
> 1 本に統合。

## 背景 (要点)

`leanprover/lean-eval` は comparator 方式の公式 formal-math ベンチ。本リポ (3 冊の形式化) は
「mathlib 未収録の研究級有限群論定理」を量産できる立場。**既提出 2 件**: `baer_suzuki`
(2026-05-29, #118) / `feit_thompson` (2026-07-16, #828)。良い候補 3 軸 = 有名 / statement が
self-contained / 証明が難しく mathlib 未収録。詳細と全候補は正本 note。

## やること

- [x] **(整備 2026-07-22) AxiomsCheck 未登録の strong 候補 10 件を登録** — ZJ / Replacement /
      Galois–Burnside / Ch08 Jordan / PSL 単純性 / `isCritical_exists` / `transfer_transfer` /
      Ch01 Fitting 冪零性・最大性 / `span_range_representation_eq_top`。`lake build
      OddOrder.AxiomsCheck` green (全件 allowlist の 3 公理のみ)。proposal 前の手動 `#print axioms` が不要に
- [ ] **🆕 (proof submit) Burnside p^aq^b** = `finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow`。
      repo `Isaacs.Ch07.burnside_p_pow_q_pow` が eval より一般な形で完成・AxiomsCheck 登録済。
      主作業 = self-contained workspace 化 (正本 note §2.5)
- [ ] **🆕 (proof submit) `brauer_character_in_cyclotomic`** — 数学は既済 (trace = 1 の冪根の和、
      `ClassSumCongruence.lean`)。`CyclotomicField (exponent G) ℚ →+* ℂ` packaging のみ (§2.5)
- [ ] **🎯 (proof submit) `brauer_suzuki`** — **前提条件は解消済** (Q₈ = issue 0147 が 2026-08-07 close)。
      2026-08-20 に eval statement を repo から逐語で証明できることを実測 (issue **0184**、
      `brauerSuzuki_mk_mem_center_oddCore` の 1 行適用、axiom-clean)。残作業 = self-contained 化のみ。
      **eval GroupTheory で唯一 repo が落とせる未解決 problem (solver 0)**
- [ ] **🆕 (proposal) Glauberman ZJ 定理** — 2026-07-22 完成・AxiomsCheck 登録済
      (`Subgroup.oPiCorePrime_sup_normalizer_zCenter_thompsonJAbelian`、伝説級・mathlib/eval 双方に無い)
- [ ] **🆕 (proposal) B.H.Neumann 位数 3** (`lowerCentralSeries_two_eq_bot_of_fixedPointFree_orderOf_eq_three`、
      登録済・bespoke≈0) + **一般 Hall–Petresco** (`HallPetresco.exists_hallPetresco`、登録済、旧 class≤3 を差替)
- [ ] **(proposal) Jordan の定理** — mathlib が `proof_wanted` で明示、bespoke 0。
      `lake exe lean-eval validate-manifest` + `check-problem-build` で検証してから PR
- [ ] **(proposal) Chermak–Delgado / Furtwängler / Thompson FPF-nilpotency** を続けて proposal PR。
      merge 後、solver は他者開放 (`feit_thompson` 前例)
- [x] **(整備 2026-08-11 完了) stale docstring 掃除** — 「未形式化」「TODO」「gated」の
      陳腐化記述 12 件 + 誤引用 1 件を実測で洗い出して修正 (commit `613559800`)。
      内訳: `AppC_Problem1` の補題 B「未形式化・Weil 要」/ `S14 Basics` の `R(x)`・`M̃`
      「未形式化」/ `S16 TypeBridges` の型 III/IV 最後の一里「未形式化」(実際は直下で証明済) /
      `S09 NormalCase` の (7.7.a) / `PSU3StepTwenty` の (H5) 連鎖 / `CharacterCompleteness` /
      `S06_Additional` 対応表 (Thm 6.2 一般形・Lem 6.3(a) 第 2 結論・6.3(b)/6.4/6.7) /
      `TheoremsAE` の G# 被覆 / `Theorem315` の placeholder / `SemidirectAut` の実装 TODO /
      `Ch07 S7B2`・`S7D1` の local axiom / `AppC_NormSet` lemmaC1 / `Modular/
      GeneralizedDecomposition` ほか。**誤引用** = `brauer_permutation_lemma` の
      「[Isaacs] Thm 6.32」は *Finite Group Theory* に存在しない (同書 Ch.6 は 6.24 で終わる)
      — 正しくは *Character Theory of Finite Groups* (1976) で、4 箇所に書名を明示

## 完了条件

- アンブレラ tracker。提案 PR がそれぞれ per-theorem sub-issue (0042 型) に落ちきったら close。
- 単発の提出そのものは各 sub-issue 側の完了条件 (eval submit 可能形 + `AxiomsCheck` pass) に従う。

## 参照

- **正本**: [`notes/meta/lean_eval_submission.md`](../../notes/meta/lean_eval_submission.md)
- lean-eval: https://github.com/leanprover/lean-eval / 提出先 https://github.com/leanprover/lean-eval-submissions / 公開面 https://lean-lang.org/eval/
- 先行 issue: 0042 (Baer–Suzuki, closed), 0120 (feit_thompson leanOptions parity, closed)
- 文献: 100 定理未形式化は幾何/解析中心で群論の低い果実は無い
  (https://leanprover-community.github.io/100-missing.html); research-level は SOTA でも
  pass 率 ~10% (RLMEval, https://arxiv.org/pdf/2510.25427)

## 🧾 履歴

- 2026-07-02 hub レビューで「off-FT-path につき park」→ **2026-07-16 に FT 本体 axiom-clean 完成 →
  全 3 冊フェーズ移行**で park 前提失効、再び active。
- 2026-07-19 候補表を実測で全面差し替え。
- 2026-07-22 lean-eval 関連 3 note を [`lean_eval_submission.md`](../../notes/meta/lean_eval_submission.md)
  に統合、本 issue を tracker 化。ZJ 定理の reject を撤回 (完成確認)。
- 2026-07-24 **用語統一** (submit = proof submit のみ、新規問題は proposal) + **proof submit 全数監査**
  (全 219 problem)。「他者 solved 済み = 候補外」の暗黙の絞りが誤り (per-account sticky) と
  ユーザー指摘で判明 — Burnside p^aq^b / `brauer_character_in_cyclotomic` を proof submit 候補に追加。
  brauer_suzuki 項を 9318-closed/0147-凍結の現況に更新。

---

## ❄ 2026-07-24 FROZEN (ユーザー裁定) — pending へ

lean-eval への proof submit / proposal 活動はユーザー裁定でいったん凍結。
正本 (`notes/meta/lean_eval_submission.md` — playbook・候補全表・reject 記録) は保存済みで、
解凍時はそこと本 checklist から再開。

---

## 🔓 2026-08-07 REOPENED (ユーザー指示)

2026-07-24 の凍結を解除。正本 (`notes/meta/lean_eval_submission.md` — playbook・候補全表
§2.5・reject 記録) はそのまま使える。⚠ 再開時の注意 = **用語** (submit = proof submit のみ、
新規問題は proposal) と **「他者 solved 済みは候補外」ではない** (per-account sticky) の 2 点。


---

## 🛑 2026-08-20 CLOSED (ユーザー裁定) — lean-eval 関連は今後触らない

> **「submission系は記録に過ぎないから、今後も触らないで」** (ユーザー 2026-08-20)

lean-eval への **proof submit も proposal も今後の作業対象から外す**。
`odd-order-submission` リポジトリも同様 (未 push のローカル commit `1a048d1` はそのまま放置)。

- 本 tracker の未チェック項目 (Burnside p^aq^b / `brauer_character_in_cyclotomic` /
  ZJ・Neumann・Hall–Petresco・Jordan・Chermak–Delgado 等の proposal) は**着手しない**。
- 直前に完遂した [`brauer_suzuki`](0184-brauer-suzuki-eval-submit.md) は、
  **repo 側の成果 (一般化・商形の橋・`O(G)` 対応・import 衛生) が本体**であり、
  それらは全て main に入っている。提出可能な状態まで検証したという事実のみ記録に残す。
- 正本 note [`lean_eval_submission.md`](../../notes/meta/lean_eval_submission.md) は
  **調査記録として保持**する (再調査を防ぐため)。判断が覆るまで更新しない。

⚠ 将来のセッションへ: **この issue を「未消化の backlog」として拾い直さないこと**。
