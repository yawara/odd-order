---
id: 2019
slug: hub-lane-h-s13-exhausted
title: "HUB: lane-h next assignment — §13 clean work done, residual all cross-lane gated"
created: 2026-06-23
---

# HUB: lane-h next assignment — §13 clean work done, residual all cross-lane gated

> 宛先 = hub (merge monitor / 分担設計)。発信 = lane-h。批判でなく分担更新の依頼。
> issue 2017 (relane #2 で §13 受領、CLOSED) と同じ starve パターンが §13 完遂後に再発。

## 背景: relane #2 で受けた §13 の lane-h-clean work を完遂

relane #2 (issue 8018+2017) で lane-h = `S13_MaximalIII_IV` (Pf §11 types III/IV) を受領。
本セッション (2026-06-23 resume¹³, 10 commit, 全 main 合流済) で **§13 の §8/char-free な
lane-h-attemptable work を完遂**:

- **de-opacify**: `S13.Hypothesis` の opaque `Prop` conclusion-field 8 個削除 → (11.4)/(11.5)/(11.6)/(11.7)
  を実ステートメント化。
- **axiom-clean reusable 群論補題 4 本**: `secondDerived_le_HC` (M''⊆HC, (8.5.a)) / `derivedU_le_C`
  (U'⊆C, (8.5.b)) / `U_centralizes_H0_of_W1_fpf` ((9.1) Wielandt 経由 U が H₀ 中心化) /
  `U_centralizes_H0_of_W2_inf_H0_bot` (clean gate `W₂⊓H₀=⊥` 版)。
- **(11.3)/(11.5) を cite-reduction で sorry-free 化**: (11.3) = Thm 6.3 obligation
  `coherent_S_of_coherent_SH0C` + (10.8) `S12.S_not_coherent` cite → 矛盾; (11.5) `M''=HC` =
  proven `≤` + `≥` obligation の `le_antisymm`。

## 残 §13 は全て cross-lane gated (lane-h 単独で手が動かない)

| 残 obligation / 結果 | gate | 担当 |
|---|---|---|
| `coherent_S_of_coherent_SH0C` (Thm 6.3) / `HC_le_secondDerived` ((11.5)≥) / (11.4) (=Thm 6.2) | §6 coherence。repo の §6 は `SibleyDadeHypothesis` filtration (`S08_Theorem63`) 経由で standalone subfamily-extension 形が無い | **lane-b** §6 char |
| (11.6) 残 conjunct (`IsPGroup` / `H₀=H'`) + fpf 入力 `W₂⊓H₀=⊥` | §8 `typeIIIorIV_W2_prime` (`|W₂|=p`, sorried、←(8.8)) + (11.5) | lane-b/§8 |
| (11.8)/(11.9) | σ/ω/(Irr W) char API (gate #3) | lane-b char |
| **S14 (12.9)** (driver) | Prop 16.1 (auto-close、issue 2016) | lane-f |

物理的に残せる lane-h 作業は (11.6)/(11.7) の機械的 obligation-split のみだが、char/§8 ゲートを
rename するだけで実質的証明の前進ゼロ・sorry 数 +3 ⟹ cosmetic ゆえやらない ([[scaffold-sorry-free-not-done]])。
正本 = `notes/peterfalvi/s10_13_maximal_structure.md` §10、§13 gate 詳細 = issue 2018。

## 判断を仰ぐ内容 (HUB へ)

lane-h は §13 の ungated closable work を出し尽くした (S14 は driver で Prop 16.1 待ち)。
relane #3 で lane-c を再配置したのと同型の starve。lane-h の次の割当を裁定してほしい:

- **(a) 再配置** — 例: §13 の直接 gate である lane-b §6 coherence (Thm 6.2/6.3 を `SibleyDadeHypothesis`
  から standalone 形に抽出 or 別途) の支援 / 別 productive segment。lanes 等価方針ゆえ carrier/char も可。
- **(b) stand by** — §13 obligations + S14 (12.9) は lane-b §6 / lane-f Prop 16.1 landing で
  自己復帰モニター (issue 2018 / 2016 トリガ) 経由 opportunistic close。投機作業はしない。

lane-h 自身では cross-lane ゆえ独断しない。read-only 監査 + 必要ならユーザーへ AskUserQuestion で。

## 完了条件

hub が lane-h の次タスク (再配置先 or stand by) を裁定し、LAUNCH.md / merge_monitor.md を更新。

## 参照

- issue 2018 (§13 char-direction completion 詳細 gate map) / issue 2016 ((12.9)←Prop 16.1)
- issue 2017 (relane #2 で §13 受領、CLOSED) — 同 starve パターンの前例
- relane #3 (commit `50b2e2c9`, lane-c 再配置) — 同型 starve の処理例
- 本セッション commits: `81b633cc`/`04eb6f32`/`558619f2`/`abefd919`/`5a212bc4`/`0adb8560` + docs
- memory [[lane-h-driving-wielandt-91]] resume¹³
