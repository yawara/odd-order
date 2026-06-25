# Pf §16 POLE-2 char cascade — W4 (lane-h, 2026-06-25 relane #9)

> lane-h = **W4 = POLE-2 `field_normalizer_structure` (Pf 14.2) char cascade + §15 setup**
> (正本 `notes/meta/ft_frontier_remap_2026_06_25.md` §2 W4、issue 0083)。Arm B = 最終矛盾の
> 独立アーム。W1 (lane-f) と upstream gate を共有しない。

## 全体構造 (2026-06-25 調査確定)

`field_normalizer_structure` **本体は sorry-free assembly**。§16 の**算術/数値スケルトンは網羅的に
完成済み** (sorry-free): `all_pm_one_and_card_of_odd_sq_sum_le` (14.11.2 parity core) /
`one_le_norm_signed_paired_sum` (14.11.3/3.9 parity core) / cyclotomic facts (13.14) / m-bounds
(13.11) / norm-cascade consumer chain / `norm_error_terms_lt_inv_q` / `norm_cascade_contradiction`。

残 sorry は全て **genuine character theory** で、共通の foundation に interlock している:
**concrete §3/§4 Dade-isometry 構成** (abstract §16 carrier `ω`/`η`/`tau3`/`betaM` を pin する
「残り §3/§4 layer」) + **(7.5) Frobenius/TI norm formula (repo 未実装)**。

### 残 sorry の bottom-out 先

| 種別 | sorries (S16_NonExistenceG 他) | gate |
|---|---|---|
| Dade η-grid 基盤 | `betaM_expansion` (14.11.2), `normCascadeBound_of_charData` (14.11.4), `orthogonality_switch` (14.14), `caseB_character_contradiction_of_gap_inequalities` (14.16), `exists_MHypothesis` (14.10) | §3/§4 Dade 構成 + (7.5) norm |
| §9/§11 char | `c_eq_one` (13.12), `U_cyclic_and_Q_elemAbelian`, `V_cyclic`, `T_side_caseB_facts`, `caseB_order_u` (13.15) | §9/§11 character theory |
| BG §14 σ | `basic_structure_gated` (P_order), `card_Q_eq` | σ-structure (lane-f/W1) |
| BG Thm E / 深 §13 | `card_LF_coprime_pq`, `normalizer_W1` (13.16), `complement_inf_Q_structure` | lane-f/F or 深 §13 (`s13_17_structural_program.md`) |

## アプローチ (ユーザー裁可 Option A、2026-06-25)

「基盤を lane-h で構築」: opaque endpoint を **done 算術コア + faithful Dade producer** による honest
assembly に de-opacify し、不足する Dade 基盤 ((3.9) integrality / (7.5) norm) を reusable lemma /
faithful producer として lane-h で実装。repo の established pattern (lane-c §16 de-opacification)。
**doneness = carrier/仮説の構成可能性で判定** ([[scaffold-sorry-free-not-done]])。

## 進捗

### ✅ generic_character_bound (14.11.3) — honest assembly (commit `483a5716`)

opaque `sorry` を honest assembly に置換。**直接 sorry 不使用**。新規:

- **`finNeg` / `finNeg_val` / `finNeg_involutive` / `finNeg_eq_self_iff`** (sorry-free, reusable):
  `Fin n` (n>0) 上の negation involution `i ↦ (n−i) mod n`。odd n で一意固定点 `0`。(3.9.a) の
  共役 `(i,j) ↦ (−i,−j)` を表す index map。
- **`one_le_norm_eta_grid_signed_sum`** (sorry-free, reusable): (14.11.3) parity core を η-grid
  (`Fin q × Fin p`, product-negation involution) に特化。`one_le_norm_signed_paired_sum` (既存
  done) に product 共役を供給。`generic_character_bound` が消費。
- **`classFunction_sum_apply`** (sorry-free, reusable): ClassFunction 有限和の点別評価
  (hoistable to `ClassFunction.lean`)。
- **`EtaGenericData` / `eta_generic_data`** (faithful producer, `:= sorry`): (3.9.c) `η_ij(g)∈ℤ`
  on G₀ / (3.9.a) conjugation 対称 + `η₀₀(g)=1` / (14.10) `β_M^τ(g)=0` on G₀。**結論の言い換えでない
  genuine 制約**。concrete 構成は §3/§4 Dade-isometry 層。

assembly: `betaM_expansion` (cite) の β_M 展開を点別評価 → `β_M(g)=0` で `χ(g)=Σε_ij η_ij(g)` →
η 整数性で `Σε_ij(n_ij:ℂ)` → `one_le_norm_eta_grid_signed_sum` で `‖·‖≥1` → `‖χ‖=‖ψ^τ₁‖`。
`generic_character_bound` に `hne` (K≠V) 追加 (唯一の消費者 `normCascadeBound_of_charData` は hne 保持)。

## ⚠ 真の foundation = §7 Dade ρ-machinery (7.1)–(7.8)（原文確認 2026-06-25）

`normCascadeBound_of_charData` (14.11.4) と `betaM_expansion` (14.11.2) は、いずれも Pf **§7 の
Dade ρ-machinery** に bottom-out する。原文 (mmd `04.9` pp.38-43) で確認:

- **(7.5)** (`normCascadeBound` の核): Hyp (7.4)（subgroup 族 `L_i`・isometry `τ_i`・supports
  `A_i^{τ_i}` 互いに disjoint・`G₀ = G − ∪A_i^{τ_i}`）の下、`χ∈Irr G` に対し
  `(1/|G|)(Σ_{g∈G₀}|χ(g)|² − |G₀|) + Σ_i(‖χ^{ρ_i}‖² − |A_i|/|L_i|) ≤ 0`。証明は norm 分解 (7.3) +
  (7.2.b)。= **CF(L,A) / ρ map / Hyp 7.1-7.4 の framework が前提**。pure-arithmetic でない。
- **(7.8)** (`betaM_expansion` の抽象版): coherent `S` の下、`β = 1_G − ζ^ν + a·Σ φ(1)/(e‖φ‖²)φ^ν + Γ`
  (`Γ ⊥ S^ν∪{1_G}`)、`e≤(h−1)/2 ⟹ ‖Γ‖²≤e−1` (7.8.b)。`betaM` の η-展開 + `Σa_ij²≤e−1` はこの
  instance。±1 は (7.8) の `a∈ℤ` + Dade 合同。

### ✅✅ 重要訂正 (2026-06-25): §7 ρ-machinery は S09 に既に形式化済み・cite 可能

当初「§7 ρ-machinery を新規形式化要・lane-c §7 重複」と評価したが**誤り**。**`S09_NonexistenceCertain.lean`
に (7.1)-(7.8) がほぼ完全 sorry-free で実在** (全ファイル実 sorry 1 個): `Hypothesis71`/`chiRho` (ρ map,
7.1-7.3) / `FamilyHypothesis71`/**`family_inequality` (7.5, sorry-free)** / `Hypothesis76` (7.6-7.7) /
`Hypothesis78`/**`beta` (7.8, sorry-free)**。S09 は S10→…→S16 で推移 import 済 ⟹ **S16 から cite 可能**。
lane-c の §7 は coherence (S07_*) で**別ファイル = 衝突なし**。

⟹ **W4 の genuine 残作業 = §16 MHypothesis → S09 bridge** (lane-c 協調不要な lane-h §16 work):
`Hypothesis71`/`Hypothesis78` は concrete `S04.Hypothesis`+`S04.DadeMap` を要求 / MHypothesis は abstract
`tau` のみ ⟹ type-I M の Dade extension (14.10) から faithful に bridge carrier を供給 (S04 concrete 構成
=§3/§4 が discharge)。本セッションの貢献 (parity-core 特化 + `generic_character_bound`) はこの上に乗る。
詳細手順 = issue 2024。

## 次手候補 (優先順・未着手) — 全て lane-h §16 work (lane-c 協調不要)

正本手順 = **issue 2024**。共通の鍵 = MHypothesis → S09 bridge carrier (faithful `Hypothesis71`/`Hypothesis78`)。

1. **bridge carrier** (最上流): MHypothesis に `Hypothesis71 G (A M) M` / `FamilyHypothesis71 G 1` /
   `Hypothesis78 G (A M) M` を faithful 供給 (type-I M の Dade extension 14.10 から)。`eta_generic_data`
   と同パターン。これが揃えば 2/3/4 は S09 cite + 算術で de-opacify 可。
2. **`normCascadeBound_of_charData` (14.11.4)**: `family_inequality` (7.5, S09 cite) +
   `generic_character_bound` (本セッション) + (7.7) 内積式 → `normCascadeBound`。(14.11.4) 算術が intricate。
3. **`betaM_expansion` (14.11.2)**: `Hypothesis78.beta`/(7.8.a) (S09 cite) を η-grid 形に identify +
   `all_pm_one_and_card_of_odd_sq_sum_le` (done) で ±1。⚠ full-grid vs non-principal の index split。
4. **(14.16) dual** `caseB_character_contradiction_of_gap_inequalities`: β_L の (7.8) expansion で同様。
   axes parity (`TypeIOrthogonalityData.caseC2_eta0j_odd`) は citeable・既 proven。

## cross-lane (lane-c / §3-owner 宛)

lane-h は §16 (lane-h owned) 内で **§3/§4 Dade obligation を faithful producer として isolate** 中
(`eta_generic_data` = (3.9) integrality/symmetry + (14.10) support vanish)。これらは将来 §3/§4
Dade-isometry concrete 構成 (lane-c §5/§7 coherence 機構と連続) で discharge される。**現状 §3-§7
ファイル未編集ゆえ衝突なし**。(7.5) norm を §7 に置く場合は事前に notes で調整。
[[cross-lane-sync-via-notes]] [[feedback-cite-sorried-lemmas-if-signature-correct]]
