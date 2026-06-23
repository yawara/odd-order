---
id: 2021
slug: hub-lane-h-exhausted-char-pivot
title: "HUB: lane-h ungated runway 枯渇 — relane #5 stale (14.7 done) + char pivot 可否判断"
created: 2026-06-23
---

# HUB: lane-h ungated runway 枯渇 — relane #5 stale (14.7 done) + char pivot 可否判断

> 宛先 = hub。発信 = lane-h。lane↔hub 調整は issue 経由 ([[cross-lane-sync-via-notes]])。
> ユーザー指示「char pivot は独断せず hub にお伺いを立てる」(2026-06-23) を受けて起票。

## 要旨 (hub への判断依頼)

**lane-h の clean な group-theory/構造 runway は全 owned files で枯渇した。** relane #5 (issue 2009)
が指した「workable-now = (14.7) Singer-field 核」は **既に sorry-free で完了済み** (stale)。残る sorry は
すべて lane-b の character 理論 (§5/§6/§9 coherence + Dade) / lane-c・lane-f の §13 structure producer /
carrier F-ask に bottom-out。**lane-h の次手 (char pivot 可否・target・所有調整) を hub に委ねる。**

## 1. relane #5 の指示は stale

- LAUNCH.md relane #5 (2026-06-23) = 「🟢 ungated・workable-now = `field_normalizer_of_U_characteristic`
  (14.7) の Singer-field 核。ここから着手」。
- **しかし (14.7) は既に sorry-free** (`OddOrder/Peterfalvi/S16_NonExistenceG.lean:2384`)。Singer-field
  engine (`exists_galoisField_repr`/`exists_pu_field_repr`)・σ-bridge (`fieldNormalizerData_of_repr`)・
  FPF value-argument は 2026-06-18〜06-20 セッションで landing 済み (issue 2009 履歴に詳細)。
- relane #5 自身が列挙した残 sorry (1564/1889/1974/1991/136/1802) と矛盾 — それらは全て char/§13-producer
  gated で、14.7 ではない。⟹ hub は枯渇済みの frontier に stale pointer で lane-h を戻していた。

## 2. lane-h 所有全ファイルの残 sorry は全て gated

| file | bare sorry | gate |
|---|---|---|
| `S16_NonExistenceG.lean` (POLE-2) | 11 | §13/§9/§11 char (lane-b) / §13 producer `basic_structure`・`card_Q_eq` (S15_SAndT=lane-c) / carrier F-ask / Dade (`exists_MHypothesis`) |
| `S13_MaximalIII_IV.lean` | 8 | §5/§6/§9 coherence + Dade API (lane-b, issue 2018) |
| `S14_MaximalI.lean` | driver | (12.9) は Prop 16.1 (lane-f) landing で自己復帰 (issue 2016) |

- **lane-h が landable な構造/群論 fragment は全て完了済み**: Huppert V.8.18 (`Isaacs/Ch06/OddComplement.lean`,
  sorry-free, commit `5a577c10`)、maxNNH 自己同型同変性 (`MaxNilpotentNormalHall.lean`, `8e6b3379`)、
  (9.1) Wielandt、FPF 機構一式、Singer-field、σ-bridge、(13.17) structural gates 1-3、(11.3)/(11.5)
  cite-reduction、secondDerived_le_HC/derivedU_le_C。
- (13.17) の残 obligation は `S15_SAndT.lean` (lane-c 所有「触らない」) に移動済み + carrier F-ask
  (`P_inf_U_eq_bot`/`W1_complements_derived`、lane-f) に gated。
- lane-h 自身の最新 notes (`s13_17_structural_program.md` 末尾, 2026-06-20¹¹) が既に結論:
  「§13.17 / POLE-2 構造的 frontier は honestly-closable 分を出し尽くした。次手は要ユーザー/hub 判断」。

## 3. FT endgame は lane-b character に収束

- POLE-1 critical path: `S_typeP2` (done) ← char 核 `card_kappaHall_lt_of_isTypeP1` (issue 2020, lane-b)
  ← discharge target `final_typeIII_conclusions` (S13, char gate #3)。
- POLE-2: `field_normalizer_structure` の残 = `exists_MHypothesis` (Dade)・`U_cyclic_and_Q_elemAbelian`
  (§9/§11 char)・`basic_structure`/`card_Q_eq` (§13 structure)・char cascade (betaM/orthogonality)。
- cd `charData` producer も lane-b。⟹ 4 レーン進捗統合で「FT endgame は lane-b char に収束、lane-h idle」
  (hub 2026-06-23 統合レビュー) は正しく、relane #5 の POLE-2 復帰は実効が無かった。

## やること (hub 判断)

- [ ] **lane-h の次手を決定**:
  - **(A) char 理論に pivot** (ユーザーは AskUserQuestion で (A) を一旦選択、ただし「独断せず hub へ」と保留)
    — 最も近い critical-path target = lane-h 自所有 `S13_MaximalIII_IV.lean` の §13 char chain (issue 2018)
    + その上流 Pf Thm 6.2 (`coherent_quotient_bound`) / Thm 6.3 (`coherent_S_of_coherent_SH0C`) = §6 coherence。
    **要 hub 指示**: (i) 具体 target (どの char gate を lane-h が引き取るか)、(ii) lane-b (ユーザー直接管理)
    との所有境界 — §6 (S08) が現 active lane の誰の所有か、§13 char を lane-b と分担する境界。衝突回避が必須。
  - **(B) idle + 自己復帰モニター** — lane-b char (issue 2018/2020 の特定項目) landing 待ち、auto-wire 再開。
  - **(C) lane-h を別領域に再 relane**。
- [ ] 決定を lane-h の `LAUNCH.md` 更新 **or** 本 issue を `issues/closed/` へ移動で通知 (どちらでも
  lane-h の自己復帰モニターが拾う)。

## lane-h 推奨

レーン等価方針 ([[lanes-are-equivalent-no-specialty]]) + 難所正面 ([[feedback-no-avoiding-hard-parts]]) より
**(A) char pivot が価値最大** (critical path 直結)。ただし lane-b はユーザー直接管理ゆえ、target と所有境界の
確定は hub/ユーザーの裁可が要る。それまで lane-h は自己復帰モニターで idle (本 issue close or LAUNCH.md 変化で復帰)。

## 2026-06-23 UPDATE (本 issue は未 merge のまま hub が relane #6 を実施) — char pivot は MOOT

本 issue を起票・自己復帰モニター arm 後、hub が **relane #6** (origin/main `53dbaa8f`,
`chore(hub): relane #6 — lane-c を char ボトルネック支援に再配置 (issue 4011 RESOLVED)`) を実施。
**この relane #6 は本 issue 2021 を見ずに** (ancestry 確認: `ee93e1ee` は `53dbaa8f` の祖先でない)、
lane-c の HUB issue 4011 (lane-c も §15 枯渇) に応答したもの。内容 (issue 4011 の RESOLVED ブロック):

- **S13_MaximalIII_IV.lean を lane-h→lane-c 移譲** (issue 2018、Pf §13 char-directions)。
- **`card_kappaHall_lt_of_isTypeP1` を lane-b→lane-c 移譲** (issue 2020、POLE-1 char 核)。
- ⟹ **char ボトルネックは lane-c が引き取った**。

**含意 (本 issue の問いへの部分的回答)**:
- 本 issue option (A)「lane-h を char に pivot」は **MOOT** — char は今や lane-c の領域。lane-h が char を
  触ると lane-c と衝突する。⟹ lane-h は char に行ってはいけない。
- relane #6 は lane-h の LAUNCH.md を S13 オーナーシップ注記のみ更新 (S13→lane-c、lane-h は cite のみ)。
  **lane-h の現タスクは依然 stale な POLE-2 (14.7 = done) のまま**で、lane-h を実 actionable な仕事に
  re-task していない。
- lane-h は S13 を失い (char work が lane-c へ)、**残る ungated work = ゼロ** (POLE-2 全 char-gated、
  その char producer は今 lane-c が作る → lane-h は consumer として待つだけ)。

**sharpened ask (hub へ)**: relane #6 で char が lane-c に集約された前提で、lane-h はどうする?
1. **idle + await POLE-2 unblock** — lane-c が POLE-2 の char producer (basic_structure/exists_MHypothesis/
   U_cyclic 等) を landing したら lane-h が `field_normalizer_structure` を wire (consumer 復帰)。
2. **非 char の FT-path task に re-task** — もし collision-free な non-char endpoint があれば (現時点で
   lane-h は発見できず)。
3. その他 hub 判断。

lane-h は **option 1 (idle + await)** を既定として自己復帰モニターを継続 (新 baseline で re-arm)。
hub の明示裁定 (本 issue close or LAUNCH.md 再 task) があれば従う。

## 完了条件

hub が lane-h の次割当を決定し、`LAUNCH.md` 更新 or 本 issue を closed/ へ移動。lane-h はそれを検知して自己復帰。

## 参照

- relane #5: lane-h `LAUNCH.md`「🎯 現タスク (2026-06-23 relane #5、issue 2009)」, issue 2009 REACTIVATE block
- 枯渇の根拠: `notes/peterfalvi/s13_17_structural_program.md` 末尾 (2026-06-20¹¹), issue 2018, issue 2020
- POLE-2 現状: `S16_NonExistenceG.lean` (14.7 sorry-free at :2384, `field_normalizer_structure` at :3369)
- build: green 3882 jobs / AxiomsCheck OK at main merge (`98bf3929`)
- 関連: [[ft-endgame-two-poles]] (POLE-1/POLE-2), [[lanes-are-equivalent-no-specialty]], [[feedback-flag-poor-progress]]
