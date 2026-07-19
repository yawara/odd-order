---
id: 128
slug: pf-135a-ccoeff-int-dup-dedup
title: "(13.5.a) H_sharp cCoeff-int の重複 — hub dedup 済、lane a は main sync 必須"
created: 2026-07-19
---

# (13.5.a) `H_sharp_hypothesis76_base_cCoeff_int` の重複 — hub 裁定と修復記録

## 背景

2026-07-19 監視 tick (merge `2cad89c1d` = issue 1041 の (13.8) S 側完成) の full build gate で
**main が 2 系統の破綻**を起こした。いずれも lane a のブランチ由来で、**leaf build では構造的に
検出できない**型 (gate の設計どおり hub が捕捉し、hub が機械修復した)。

### 破綻 1: 同名 theorem の環境衝突 (hub aggregator import 失敗)

- 既存: `S15_CaseBEndgameSupply/LambdaCorrection.lean:34`
  `H_sharp_hypothesis76_base_cCoeff_int [Fintype G] [Invertible (Nat.card G : ℂ)]`
- 新規 (a, commit 322c71afe): `Eta01Correction.lean:614` に同名の `[Finite G]` 版
  (docstring は Q-side `Q_sharp_hypothesis76_base_cCoeff_int` の mirror と記載 —
  **同 dir の H-side 既存版を見落とした**。issue 0127 ①・9161 と同型パターンの 3 例目)
- 各 leaf は独立に green だが、hub file `S15_CaseBEndgameSupply.lean` が両方を import した
  時点で `environment already contains ...` で崩壊。

### hub dedup の方向 (逆に見えるが正しい)

**旧 `[Fintype][Invertible]` binder 版を正とし、新 `[Finite G]` 版を削除**して
`Eta01Correction` に `import ...LambdaCorrection` を追加 (call site は同名ゆえ無変更で解決)。
理由は instance-defeq の非対称性 ([[lean-instance-defeq-traps]] 「statement 明示
data-instance は scoped と unify 不能」):

- 新版は `open scoped FiniteInduce` 下で statement を書くため、結論の
  `H_sharp_hypothesis76_base` に **ambient instance (`FiniteInduce.ambientFintype` /
  `ambientNatCardInvC`) が焼き込まれる** → `[Fintype G] [Invertible]` binder 文脈の consumer
  (`exists_lambda_alphaFun_one_int_base` 等) と項が unify せず Application type mismatch
  (hub が gate 中に実測 — 最初は新版を残す逆方向を試して失敗した)。
- 旧版は binder 文脈でも scoped 文脈でも適用可 (scoped 側では ambient instance が binder を
  満たす)。全 consumer (LambdaCorrection 内 / `Eta10HCorrection:135` / Eta01Correction 内) が
  無変更で通るのは旧版のみ。

「hypothesis が弱い方が一般」は binder 部分だけ見た錯覚で、**適用可能な文脈の集合**では
旧版が真に広い。

### 破綻 2: AxiomsCheck 登録に import が伴っていない

a は `#assert_only_allowed_axioms` 3 件 (`Hypothesis.exists_muS_index_eta01_core` /
`exists_caseB_data_eta01_S_core` / `eta01_Hsharp_norm_lower_core`) を AxiomsCheck.lean に
追記したが、宣言モジュール (Eta01Correction) が AxiomsCheck の import closure に無く
`constant not found` × 3。hub が `import OddOrder.Peterfalvi.S15_CaseBEndgameSupply` を
追記 (step 3b 型の機械的修正)。

## やること

- [ ] **lane a: 次の作業前に必ず `git merge main`** — a のブランチは現状 self-broken
      (hub aggregator 衝突 + AxiomsCheck 落ち)。main 取り込みで両方直る。
      merge 後、`H_sharp_hypothesis76_base_cCoeff_int` の `[Finite G]` 版を**再追加しない**。
- [ ] (低優先・a の裁量) LambdaCorrection の残り `[Fintype]` straggler
      (`lambda_alphaFun_inner_zero_base` / `exists_lambda_alphaFun_one_int_base` /
      `exists_lambda_alphaFun_one_qb_base` / `H_sharp_hypothesis76_base_alphaFun_inflation`)
      を scoped スタイルへ変換する際に、生き残った cCoeff_int を **in-place で一般化**する
      (その時点で binder 文脈 consumer が消えるため安全)。別名コピーは作らない。

## 完了条件

lane a が main を取り込み、(13.8) 後続作業が重複なしで進行していること
(straggler 一般化は任意 — 実施したらこの issue に追記して close)。

## 再発防止メモ (全レーン)

- AxiomsCheck 登録を足すときは**宣言モジュールが AxiomsCheck の import に載っているか**を
  同 commit で確認する (hub re-export 1 行で足りる)。
- 新 theorem を切る前に同名 grep: `grep -rn '<name>' OddOrder/ --include='*.lean'`。

## 参照

- 関連: issues/0127 (① 重複 2 件、同型パターン)、issues/closed/9161
- 修復 commit: 本 issue と同時にマージされる hub commit を参照
- gate ログ: dup 衝突 → 逆方向 dedup の type mismatch → 正方向で green の 3 回の build 実測
