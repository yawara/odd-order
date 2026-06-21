# FT frontier の機能分割分析 — hub deep-dive (2026-06-22)

> 背景: lane-c issue 4002 + S11 handoff 衝突 ×2 を受け、ユーザー指示「hub が深掘りしてから決定」。
> §-区間分割 (F=BG§14-16 / B=§10-13 / H=§14-15 / C=§16) が連結 char chunk を横断分割している
> という lane-c の批判を、実地調査で検証。正本データ = lane-c `s16_nonexistence_gate_map.md` +
> lane-h `s10_13_maximal_structure.md` + sorry 分布 + import DAG。

## 結論: FT frontier (102 sorry) は 3 機能に分かれる。fan-out は Dade 指標計算に集中。

| 機能 | 内容 | sorry 所在 | 並列幅 |
|---|---|---|---|
| **① 群構造 / 型分類** | BG §16 Thm A-I / Prop 16.1 (F) + Wielandt §9.1-9.6 chief-factor (Maschke/Frattini/Wielandt、純群論) + §8 型 taxonomy + (9.3) order relation | BG §14-16 (18) + S11 の §9.1-9.6 部分 + S10 構造部 | 中 (BG / Wielandt の 2 sub) |
| **② Dade 指標計算 (fan-out 本体)** | §3-9 char API (済) + §10-13 grids (ω/μ/τ, (10.5) Dade-image) + coherence + §13 Dade data + `section16CharacterData` (issue 1004) + §14 β_M norm cascade (14.11) + orthogonality (14.14/14.16) + §9.7-9.11 char | S12(7) + S13(8) + S15 char 部 + S16 char endpoint 部 + S11 の §9.7-9.11 | **大 (producer/consumer で 2 分割可)** |
| **③ 最終 assembly** | §14-15 S&T 構造 dispatch (exists_LHypothesis/MHypothesis) + §16 非存在 wiring + POLE-2 | S14(14 構造部) + S15 構造部 + S16 dispatch | 小 (thin consumer) |

## §-区間分割がこの 3 機能を散乱させている (lane-c の批判は正しい)

- **機能① (Wielandt §9) が B と H に分裂** → S11 衝突 ×2 の直接原因。H が Wielandt §9.1-9.6 を端から端まで構築
  (連結 chunk) しているのに、§-split が S11 を「B の §10-13」に割当 → B も §11 (9.3) を触り衝突。
- **機能② (Dade char) が B (§12-13) と C (§16 opaque Props) に分裂** → C の §16 sorry 13 本中 10 本が
  B の §13 char に bottom-out (lane-c gate map)。§14 の opaque Props (betaM_expansion / generic_bound /
  norm cascade) は「§16 のファイルにあるが中身は §13-14 Dade char」= 機能② が §13(B)/§14/§16(C) を跨ぐ。
- **機能③ が H (§15) と C (§16) に分裂**。

## 障害: ファイルが機能を混在させている

clean な機能分割には**ファイルの機能別分割が必要**:
- `S11_MaximalII_III_IV.lean`: Wielandt §9.1-9.6 (機能①, H) + §9.7-9.11 Clifford/char-count (機能②, B) が同居。
- `S15_SAndT.lean` (22 sorry): `basic_structure` 等 (機能③ 構造) + `character_degree_analysis`/`caseB_order_u`/
  `typeI_orthogonality_dichotomy`/`TypeIOrthogonalityData` (機能② char endpoint) が同居。
- `S16_NonExistenceG.lean`: dispatch (機能③) + β_M/orthogonality char endpoints (機能②) が同居。

## 推奨パーティション (機能ベース、3-5 レーン)

```
① 群構造:  F = BG §16  |  H = Wielandt §9 + 型分類 (§11 群論部を H に統合 — 衝突解消)
② Dade char (fan-out): B1 = grids/coherence/section16CharacterData (producer)
                       B2 = β_M norm cascade / orthogonality / char endpoints (consumer, §14-16 char)
③ assembly: (B2 or 専用) = §14-16 構造 dispatch + POLE-2  (thin, ② に従属)
```

- **最小・高価値の即修正**: 機能① の Wielandt §9 を **H に完全集約** (S11 群論部を H 所有に)。§11 B/H 衝突を即解消。
  B は §10-13 の char grid (機能② producer) に専念。
- **fan-out を割るなら機能②**: B を 2 レーン (B1=grid producer / B2=char endpoint consumer) に。C はその B2 に統合 or
  §16 char endpoint を C が所有 (lane-c の「自セグメント §14 de-opacify は自走可」= C は consumer でなく endpoint owner)。
- **③ assembly は thin** ゆえ専用レーン不要、② の consumer 側 (C) に同居。

## トレードオフ

- **長所**: 各レーンが機能的に連結した chunk を所有 → cross-lane gating と衝突が激減。fan-out (機能②) に
  capacity 集中。Wielandt §9 の H 分裂を解消。
- **短所**: ファイル機能別分割 (S11/S15 を split) の前作業が要る (中規模 refactor)。re-org churn。
  現 §-split も実際には生産中 (危機でない)。

## メモ: 線形 spine の本質的制約

§-split でも機能 split でも、**最終 assembly (機能③) は全上流に依存する線形末端**ゆえ完全並列化不可。
signature-first で「下流が sorried upstream を cite」できるのは upstream が**忠実 signature を stated**
している場合のみ (lane-c の audit: 結論一致でも仮説不一致なら cite 不可)。⟹ 並列幅の上限は機能② の
内部 fan-out (~2-3) + 機能① (F + H) + 機能③ (1) ≈ **4-5 レーン**が現実的上限。
