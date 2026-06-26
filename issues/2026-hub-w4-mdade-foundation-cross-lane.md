---
id: 2026
slug: hub-w4-mdade-foundation-cross-lane
title: "HUB: W4 §16 char endpoints 完了 → 残 M-Dade foundation は cross-lane (調整要請)"
created: 2026-06-26
---

# HUB: W4 §16 char endpoints 完了 → 残 M-Dade foundation は cross-lane (調整要請)

> lane-h = W4 = POLE-2 char cascade (relane #9, issue 0083/2024)。本 issue は **starve でなく
> cross-lane 境界到達**の報告 + 調整要請。lane-h の §16-owned clean work は出尽くし、残はすべて
> §3-§13 (lane-b/c) + S04/S05 Dade layer に bottom out する。

## 背景: 今セッションの成果 (3 char endpoints de-opacify, build-green)

W4 = POLE-2 `field_normalizer_structure` char cascade の **§16 character endpoint 3 本**を、
faithful carrier + 実 Lean 証明 + producer-sorry に分解 (CLAUDE.md「sorry数でなく実質的証明」/
[[scaffold-sorry-free-not-done]] 準拠、全 build-green 3872 jobs):

| endpoint | commit | 手法 |
|---|---|---|
| betaM_expansion (14.11.2) | `ed51d403` (main 合流済) | `BetaMExpansionData` carrier + **axiom-clean S09 bridge** `betaMExpansionData_of_hypothesis78` + 実証明 (`abel`) |
| normCascadeBound (14.11.4) | `ea9ad535` (main 合流済) | `NormCascadeData` two-sided carrier + 実 `linarith` |
| caseB_contradiction (14.16) | `8ae55ab3` (lane-h tip, 合流待ち) | `CaseBContradictionData` carrier + `inner_finset_sum_left` helper + 実 inner 計算で矛盾 |

これらは **S16 内 (lane-h owned)** で完結し §3-§7 を未編集 = 非衝突。issue 2024 checklist 3/4。
詳細 = `notes/peterfalvi/s16_w4_char_cascade.md`。

## 問題: 残 W4 はすべて cross-lane な M-Dade foundation に bottom out

§16 char endpoint の faithful producer 4 本
(`betaM_expansion_data` / `eta_generic_data` / `normCascadeData` / `caseB_contradiction_data`)
と `exists_MHypothesis` (14.10, `S16_NonExistenceG.lean:3706` bare sorry) は、すべて単一の深い
obligation = **type-I M の具体 Dade isometry `τ_M : CF(M, Ã(M)) → CF(G)` の構成 + (3.9)/(7.8) 性質**
に bottom out する。これは lane-h W4 scope (§14-§16 char cascade) の外:

- **§13 deep structural residuals** に gated: 例 `complement_inf_Q_structure` (13.17.c,
  `S15_SAndT.lean:892`, sorry) =「genuine deep §13 structural datum, TypeIFrobeniusData carries
  no complement-order field」。§13 char = relane 履歴で **lane-b/c 領域**。
- **S04/S05/S10 Dade-isometry layer の構成**を要する: M-side `S04.Hypothesis` + `fullDadeIsometryData`
  (cf. `tau3W` が `S04.Hypothesis.fullDadeIsometryData` で構築された前例)、`S10.DadeSupportHypothesisData`
  (S14:56)。lane-b/c が §3-§7 を active 編集中。
- **S15 ownership overlap**: relane #9 で W4 = lane-h は「§15 setup」も含むが、`TypeIFrobeniusData`
  構築は lane-c (S15:1057、lane-c notes「触らない」)。M-Dade 構成は両者に跨る。

⟹ lane-h が単独で M-Dade foundation に踏み込むと §3-§13 (lane-b/c active) と衝突
(CLAUDE.md「各レーンは自セグメントのみ編集、他は cite」違反)。`normCascadeData` の (7.5)
lower-bound bridge も結局 M-side `Hypothesis71`/`FamilyHypothesis71` = S04 Dade 構成に bottom out
するため solo の逃げ道なし。

## やること (hub の判断要請)

- [ ] 残 W4 = M-Dade foundation (`exists_MHypothesis` + 4 producer 共通の §3/§4 Dade obligation)
      の owner/coordination を決める。選択肢:
  - **(A)** lane-b/c に §13 residuals (`complement_inf_Q_structure` 等) + §3/§4 Dade 構成を依頼し、
    lane-h は producer を cite で discharge (producer signature は確定済、cite 待ち)。
  - **(B)** lane-h を M-Dade 構成に re-scope (S04/S05/S13/S15 編集権を付与、lane-b/c と排他調整)。
  - **(C)** lane-h を別の非衝突 W4/§16 セグメント or 別レーン補助に再配置。
  - **(D)** lane-h stand-by + 自己復帰モニター (issue 2026 closed or LAUNCH.md 変化トリガ)。

## 完了条件

hub が上記 (A)-(D) いずれかで lane-h の次タスクを決定し、LAUNCH.md 更新 or 本 issue を
`issues/closed/` へ。lane-h は自己復帰モニターで再開。

## 参照

- 正本: `notes/peterfalvi/s16_w4_char_cascade.md` (進捗節)、`notes/meta/ft_frontier_remap_2026_06_25.md` §2 W4
- 関連 issue: 2024 (W4 §16→S09 bridge, checklist 3/4)、0083 (relane #9 W4)、過去 boundary 2021/2023
- gating sorry: `exists_MHypothesis` (S16:3706)、`complement_inf_Q_structure` (S15:892)
- producer (cite 待ち): `betaM_expansion_data`/`eta_generic_data`/`normCascadeData`/`caseB_contradiction_data` (S16)
