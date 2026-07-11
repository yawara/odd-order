---
id: 9081
slug: mu-diff-support-sorryax-routing
title: "mu_diff_support field の producer discharge が spine producer に sorryAx を推移混入 — HOLD 解釈 or Core-split の hub 裁定"
created: 2026-07-11
---

# mu_diff_support field の producer discharge が spine producer に sorryAx を推移混入 — HOLD 解釈 or Core-split の hub 裁定

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

# 背景 (issue 2038 iter 43-44、lane b)

(13.18) support pin の grounding として `mu_diff_support` field を S15.Hypothesis + Section16Inputs +
cd 層に追加し、producer (FT.lean `section16CharacterData_of_isMinimalSimpleOdd` 構築) で proven
`Section16CharacterData.muS_diff_support` により discharge した (c2400d81)。leaf build green だが
**AxiomsCheck red**: 従来 sorry-free の spine producer `section16CharacterData_of_isMinimalSimpleOdd`
に sorryAx が推移混入 → **revert 済 (1b12b8cf、現 tree は green)**。

## 混入経路 (本質的)

muS_diff_support → `hyp46Smp` (certainTypeS-based Hypothesis46、FT.lean:360) → **dade0/tau fields =
`dadeSupportHypothesisData_honestTypeP2A0Set` (deep FT-support pin `not_isConj_honestTypeP2ASet_typePV`
が sorried)**。engine (`certainType_diff_supp_subset_A0`) の証明は dade0/tau を射影しない見込みだが、
**Hypothesis46 という入力型が Dade を bundle** するため、hyp46Smp 定数の axioms 閉包に sorryAx が
入る (証明が使うかに無関係)。

## hub 裁定依頼 (2 択)

- **(a) sorryAx 受容 + AxiomsCheck assert 更新**: 当該 assert (AxiomsCheck:6764) を sorryAx-許容形に
  変更 (docstring で「A₀-Dade 存在 pin 由来の意図的 sorried-cite」と明示)。
  [[feedback-cite-sorried-lemmas-if-signature-correct]] の sanctioned パターンに合致する一方、
  [[scaffold-sorry-free-not-done]] の HOLD「従来 sorry-free spine への sorry 混入禁止」の解釈に
  抵触し得る (b 単独で判断せず hub に諮る)。軽量・即再 landing 可。
- **(b) Hypothesis46 Core-split refactor**: S06_CertainHypothesis46 を `Hypothesis46Core`
  (dade/dade0/tau 抜き) + 拡張に分割し、(4.7)-chain
  (`chiRestrict_apply_eq_zero_of_not_mem_union` / `not_subset_characterKernel_chiRestrict` /
  `apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel` / `certainType_diff_supp_subset_A0`)
  を Core-typed に付け替え。producer は sorry-free 維持。**shared S06 の signature 変更**
  (下流 call sites は `.toHypothesis46Core` 挿入 or wrapper 維持) — 規模中、cross-lane 影響あり
  ゆえ hub 承認要。

## b の進行

裁定待ちの間、b は **9080 step 1 (TypeICovering migration、hub 承認済)** に切替。V-value pin 側
(certainType_diff_dade_apply_eq_of_mem_V) は tau を本質使用するため (a) でも (b) でも sorried-cite
になる点は共通 (V-value pin 自体が現在 sorried ゆえ問題なし)。

---

# 🧭 HUB RULING (2026-07-11, hub 自律裁定): **(b) Hypothesis46 Core-split を承認** — (a) sorryAx 受容は却下

## hub 実測 (2026-07-11、merged main 上)

1. **汚染は実在** (自然治癒していない): `#print axioms OddOrder.Section16CharacterData.hyp46Smp`
   → `sorryAx` 含む。`dadeSupportHypothesisData_honestTypeP2A0Set` も同様。
2. **ただし issue 記載の leaf は outdated**: `not_isConj_honestTypeP2ASet_typePV` は現 main で
   **proven** (S15_HonestTypeP2A0:475、実証明本体あり)。live な汚染経路は
   `honestTypeP2A0Set_tame_conj` → BG §16 `theoremII_tame_embedding` の**さらに深部の
   prerequisite** 経由 (BG S15_MF / S16_MainResults 自体は bare sorry 0 — cite 先の深部、
   いずれも b の BG territory)。
3. **(4.7)-chain + (4.8) 結論(1) engine は dade/dade0/tau を射影しない** (hub が proof 通読+grep):
   - `certainType_diff_supp_subset_A0` (S06_CertainTypeIsometry:275): columnFamily / K / W1 / W2 /
     tic\* / W_disjoint / mem_compl_conj_into_W のみ。
   - S06_CertainTypeSupport 全体で `.dade` 使用は **1 箇所のみ** = line 159
     `h.dade.L_normalizes_A` (構造的 normalization prop)。producer 側は
     `honestTypeP2ASet_conj_mem` で honest 供給可 (hyp46Smp の `dade := ….restrict` の
     第 2 引数が現にこの供給)。
   - Dade の実使用開始点 = S06_CertainTypeIsometry:374+ / S06_CertainTypeCoherence:331+
     (これらは Hypothesis46-typed のまま残す)。
4. **grid 機構は split の影響ゼロ**: `columnFamily` / `chiRestrict` (§4.1–4.5) は既に基底
   `Hypothesis L` 型 (S06_CertainTypeCharacters:205 / S06_CertainTypeClifford:365 の variable) —
   Core-typing 不要。b の「規模中」見積もりより軽い。

## 裁定理由

- **(a) は HOLD 規約に正面から抵触**: 「従来 sorry-free な FT spine def への sorry 混入禁止 /
  新 obligation は off-spine lemma に隔離し consumer が cite」(merge_monitor +
  [[scaffold-sorry-free-not-done]] §3)。spine producer
  `section16CharacterData_of_isMinimalSimpleOdd` の閉包汚染はまさに禁止対象。
- **sorried-cite 規約は適用外**: [[feedback-cite-sorried-lemmas-if-signature-correct]] が認めるのは
  「数学的に必要な sorried math の cite」。本件は engine が**依存しない** Dade bundle の
  型バンドル起因 spurious dependency — spurious dependency への正答は型を細くすることであり、
  汚染を文書化して受容することではない。
- **(a) の隠れコスト**: AxiomsCheck assert の sorryAx 許容化は tripwire の恒久弱体化
  (sorryAx は出所不可分 → 以後、同 constant への*意図せぬ*新規混入を自動検出できない)。
- (b) の規模・cross-lane 影響は判断基準でない ([[feedback-cost-scope-not-a-criterion]])。
  feasibility は上記 3–4 で検証済み。

## 実装条件 (b への narrow carve-out — S06 は名目 lane-a regex 内のため本裁定で付与)

- **b が実施してよい**: (i) `S06_CertainHypothesis46.lean` に `Hypothesis46Core` 構造
  (base Hypothesis + tic/tic_W1/tic_W2/tic_V + subH 系 + A_covers + 軽量 normalization field) +
  `Hypothesis46` の extends 化 or `Hypothesis46.toCore` 射を追加、(ii) (4.7)-chain
  (`chiRestrict_apply_eq_zero_of_not_mem_union` / `not_subset_characterKernel_chiRestrict` /
  `apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel` + induce 変種) と
  `certainType_diff_supp_subset_A0` (+ 必要なら `certainTypeDiffSupported`) の署名を
  Core-typed 化、(iii) 既存 call sites (S08_CaseBAnchoredSeed:227 / S08_CaseBCoherence2:1605 /
  S15_HonestTypeP2A0:784 / FeitThompson.lean:435,1237) への `.toCore` 挿入 =
  🔩 機械的 call-site 追従 (a-owned file 内でも非逸脱、commit message で self-flag)。
- **⚠ field 名・dot-access 経路は保存必須**: `h.dade` / `h.tic` / `h.subH` / `h.A_covers` 等の
  既存アクセスを壊さない。**lane a が `Hypothesis.toHypothesis46` (S12_Core:1057) 経由で
  Hypothesis46 を active に構築・消費中** (issue 1021 tick¹⁷–¹⁸) — 名前保存なら structure
  instance notation は extends flattening で解決され a 側は無変更で通る。
- a の S06 その他 decl の statement・証明内容には触れない (触る必要が生じたら 9081 に追記して
  hub へ)。
- 完了時: producer `section16CharacterData_of_isMinimalSimpleOdd` の sorry-free 維持を
  AxiomsCheck で確認 (assert は現行の厳格形のまま)。

## b への注記

- 深部 pin (BG §16 tame-embedding の prerequisite 群) は b 自身の BG territory — これが閉じれば
  Dade route 自体も除染されるが、Core-split は timing に依らず正しいアーキテクチャ
  (minimal hypotheses = mathlib 衛生 + spine tripwire 厳格維持) ゆえ先行してよい。
- V-value pin 側 (`certainType_diff_dade_apply_eq_of_mem_V`) が tau 本質使用で sorried-cite に
  なる点は issue 記載どおり問題なし (off-spine cite の正規形)。
- 再 landing 順序 (9080 step 1 との前後) は b の自律判断。

## 🧭 HUB 状態記録 (2026-07-11 19:53 tick): b セッション停止を検出 — WIP は worktree に保全済み

b の Core-split WIP (9 files、+165/−50: S06_CertainHypothesis46 + chain 4 file + FT.lean +
Isometry105 / TypeIIColumnPin / S15_HonestTypeP2A0 の call-site 追従) は **10:36–10:41 で凍結**
(以後 9h 無活動 = セッション停止とみられる)。**WIP は b worktree に uncommitted のまま保全されている**
— hub は非接触 (b territory)。**b 再起動時**: `git status` で本 WIP を確認し、Core-split を途中から
再開すること (裁定条件は上の HUB RULING 節: field 名保存・producer sorry-free 維持・AxiomsCheck
assert は厳格形のまま)。

---

## ✅ lane-b 実装 (2026-07-11, commit ef1f172a): Core-split 本体 landed

裁定 (b) の実装条件 (i)(ii) + FT producer 側を完了:
- `Hypothesis46Core` + `@[reducible] Hypothesis46.toCore` (S06_CertainHypothesis46)。
  Hypothesis46 本体・field 名・dot-access は無変更 (a の S12_Core:1057 構築は無影響)。
- (4.7)-chain 6 本 + (4.8)-(1) engine 5 本を Core-typed 化、call site 30 箇所 .toCore 追従。
- `hyp46SmpCore` (FT.lean): Dade-free producer core。⚠ 実装知見: 証明 field を
  `(hyp46Smp …).field` の projection で書くと **hyp46Smp 定数経由で sorried Dade pin が
  axiom closure に入る** — verbatim 複製が必須。
- **検証済**: full build green (4152 jobs) / `#print axioms muS_diff_support` =
  standard 3 axioms のみ (sorryAx 消滅)。

**残タスク (次セッション)**: c2400d81 の cherry-pick 再 landing (mu_diff_support field
threading、3 files +30 行、構築サイト不変を確認済) → AxiomsCheck の producer assert
(厳格形のまま) が green を維持することを確認 → 本 issue close。その後 9076
(tauS_mu_row0_diff_support の hj0/hdeg signature 修正) が field から discharge 可能。
