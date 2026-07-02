---
id: 4003
slug: s15-eta-carrier-honest
title: "lane-h ask: S15 η-grid carrier honest 化 ((3.9) 値性質 export)"
created: 2026-06-22
---

# lane-h ask: S15 η-grid carrier honest 化 ((3.9) 値性質 export)

> 宛先 = lane-h (S15_SAndT.lean 所有)。発信 = lane-c (Pf §16)。cross-lane sync は notes/issue 経由。

## 背景

lane-c は §16 char endgame の ungated arithmetic backbone を構築した
(`one_le_norm_signed_paired_sum` = (3.9)/(14.11.3) parity core, commit `2d517956`;
`all_pm_one_and_card_of_odd_sq_sum_le` = (14.11.2) sum-of-squares core, commit `9f17b010`;
両者 sorry-free + axiom-clean)。これらを `betaM_expansion` (14.11.2) /
`generic_character_bound` (14.11.3) / `caseB_character_contradiction_of_gap_inequalities` (14.16)
に wire するには、**S15 の η-grid carrier が honest** でなければならない。

現状 `S15.Hypothesis.eta : Fin q → Fin p → ClassFunction G ℂ` は **free field** で、制約は
`eta_eq_tau_omega : eta i j = tau3 (omega i j)` のみ (tau3/omega も free)。値の性質
((3.9) の整数値・共役ペア・直交正規性) を一切 carry しないため、lane-c は core を適用できない。

正本 = `notes/peterfalvi/s16_nonexistence_gate_map.md` 冒頭「2026-06-22 (lane-c 再開)」セクション。

## やること (lane-h、S15 で η-grid を honest 化 / 性質を export)

§16 char endgame が consume する (3.9) 値性質を S15 に record/export する (signature-first、
producer が sorried でも cite 可 [[feedback-cite-sorried-lemmas-if-signature-correct]]):

- [ ] **(3.9.c) 整数値**: 生成集合 `g ∈ G_0` (位数が pq と素) で `η_ij(g) ∈ ℤ`。
      → parity core の `n : ι → ℤ` (`η_ij(g) = (n i j : ℂ)`) を供給。
- [ ] **(3.9.a) 共役ペア**: involution `(i,j) ↦ (−i,−j)` (Fin q × Fin p の negation、唯一固定点
      `(0,0)`) の下で `η_{(-i,-j)}(g) = conj(η_ij(g))`。整数値ゆえ実値 = `η_ij(g)`。
      `η₀₀(g) = 1`。→ parity core の `ρ`/`hfix`/`hpair`/`hn0` を供給。
- [ ] **η-grid 直交正規性** (Pf 5.x/3.9): `⟨η_ij, η_kl⟩ = δ`。これにより係数
      `a_ij = ⟨β_M^τ, η_ij⟩` を射影として取り出し展開 `β_M^τ = Σ a_ij η_ij − χ` を出せる。
      → sum-of-squares core の `a` + `Σa²≤e−1` を供給。
- [ ] **(13.19.c) odd parity の betaM 側 analog**: `⟨β_M^τ, η_ij⟩` が奇整数
      (`OddIntegerInner`)。S15 に betaL 側 (`caseC2_eta0j_odd` 等) は既存 — betaM/V-side analog。

## 完了条件

S15 が上記 η-値性質を faithful signature (sorried 可) で export し、lane-c が
`betaM_expansion`/`generic_character_bound` を core 経由で sorry-free engine + 名前付き
η-obligation skeleton として組める状態になる。

## 参照

- `notes/peterfalvi/s16_nonexistence_gate_map.md` (冒頭セクション = 正本)
- issue 4001 (lane-c §16 frontier)、issue 4002 (hub feedback: §13-14 char は連結 hard chunk)
- commit `2d517956` / `9f17b010` (foundational cores)
- `S15_SAndT.lean:135` (`eta` free field)、`:1748` (`OddIntegerInner`)、`:1833`
  (`typeI_orthogonality_dichotomy`, sorried)

## 🧾 注記 (2026-07-02 hub 全体レビュー): 宛先消滅 — lane c intra-lane 化

- **宛先 (lane-h) は退役済で消滅** (3 レーン再編、正本
  `notes/meta/ft_lane_reallocation_2026_06_28.md`)。`S15_SAndT.lean` は現在 **lane c 所有**
  ゆえ、本 issue の「lane-h ask」は **lane c の intra-lane 作業**に変わった
  (cross-lane 手渡しは不要)。
- η-grid の性質 carry は issue **3002** (grid property carrier enrichment) と同系 —
  **3002 との統合を検討** (S15.Hypothesis への性質 field 追加はどちらも lane c 自己所有)。
