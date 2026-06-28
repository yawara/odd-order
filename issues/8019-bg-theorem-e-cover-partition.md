---
id: 8019
slug: bg-theorem-e-cover-partition
title: "BG Theorem E (Pf 8.17): maximal-subgroup σ-cover/partition — multi-session"
created: 2026-06-28
---

# BG Theorem E (Pf 8.17): maximal-subgroup σ-cover/partition

## 背景 / 位置づけ (lane-f W1 次フロンティア)

Prop 16.1 (`proposition_type_classification`) を完全 sorry-free + axiom-clean 化 (2026-06-28、
issue 8015 CLOSE) した後の lane-f frontier 調査で、**lane-f のクリーンな単一セッション群論 win は
枯渇**、残る on-path 候補は全て深く gated と判明。ユーザー裁可で **BG Theorem E** を次の lane-f
multi-session 目標に選択 (深い群論・lane-f-owned・genuine 上流 prereq)。

**FT 経路上の位置**:
```
bgTheoremE_cover_data (Pf 8.17, S10_MinimalSimpleStructure:570, sorry, owner=F)
  → card_LF_coprime_pq (S15_SAndT:463, 非共役 type-I 極大の |L_F| が pq に coprime)
    → (13.17.b) type-I 枝 → typeII_overNormalizer_frobenius (S15_SAndT)
      → S16_NonExistenceG (field_normalizer_structure / exists_MHypothesis)
        → POLE-2 / nonexistence_of_G → AppC final_contradiction → feitThompson
```
⟹ BG Theorem E は POLE-2 (Arm B) の genuine 上流。CLAUDE.md「上流 prereq を hedge せず淡々と
完遂」対象 (今 consumer は card_LF_coprime_pq 経由で間接、deferred-payoff だが本物)。

## 2 つの形 (BG-side と Pf-side、要 link)

1. **`theoremE_sigma_partition_and_counting`** (`S16_MainResults:1023`, lane-f BG §16): BG Theorem E
   本体。5 conjunct: (1) tildeM cardinality `|conjClass(M̃)| = (|M_σ|−1)·[G:M]` (2) prime cover
   `∀p, p∈π(G) ↔ ∃Mi∈reps, p∈σ(Mi)` (3) **σ-disjoint** (4) tildeM-disjoint (5) G# covering
   (type-P で zTilde 追加)。
2. **`bgTheoremE_cover_data`** (`S10_MinimalSimpleStructure:570`, Pf §8 repackage): `∃ data :
   BGTheoremECoverData G, BGTheoremETypeICovering data ∨ Nonempty (BGTheoremENonTypeICovering data)`。
   consumer (card_LF_coprime_pq) はこちらの `primeFactors_disjoint` を使う。

両者は同内容を別記法で。**Pf-side は BG-side から導く**のが筋 (Coq `FT_Dade_support_partition` が
`BGsummaryE` を repackage するのと同じ構造)。

## Coq 構造 (PFsection8.v:923 `FT_Dade_support_partition`)

**核心**: Pf (8.17) Coq 証明は **`BGsummaryE gT` (BG Theorem E 本体) の repackaging**:
```coq
have [b [a1 a2] [/and3P[_ _ not_PG_set0] _ _]] := BGsummaryE gT.   (* ← BG Theorem E の全 content *)
... (* A1~ / FTsupport 記法へ翻訳 *)
have [c1 c2] := mFT_partition gT.   (* partition は mFT_partition から *)
```
- (a1) prime cover、(a2) σ-coprime、(b) cardinality は **全て `BGsummaryE` 由来**。
- partition (injectivity + disjoint cover) は **`mFT_partition`** 由来。
- ⟹ BG Theorem E は BG local analysis (§1-16) の総決算 = `BGsummaryE`。Lean では BG §14-16 frontier
  の完成が前提。

## 在庫 (使える proven pieces)

- ✅ **conjunct 3 (σ-disjoint) は既に sorry-free**: `sigma_reps_pairwise_disjoint` (S16:999) =
  `S13.sigma_disjoint_of_nonconjugate` (S13_Theorem1310:159) + reps 一意性。**そのまま conjunct 3
  に配線可能**。
- `S13.sigma_disjoint_of_nonconjugate` (非共役極大の σ disjoint、proven)。
- `tildeM` / `RData` / `sigmaSharp` defs (S16:114/127, S14:1145)。
- `Finite.exists_le_maximal` (任意真部分群は極大に含まれる、minimal simple)。
- `S10.alpha_subset_sigma` (α⊆σ)、Sylow-in-maximal 機構 (S12_Theorem127 `map_sylow_E_maximal_in_M`)。
- 極大の共役類 transversal (`mmax_transversalP` 相当) — reps 構成に要、Lean 在庫を要確認。

## 深い gate (残作業、§13-14 BG content)

- **(1) cardinality** `|conjClass(M̃)| = (|M_σ|−1)·[G:M]`: **Lemma 14.5(c)** (R(x) Theorem D
  normal-complement の counting)。Theorem D (`theoremD_msigma_conjugacy_and_centralizers`, S16:961,
  sorry) 依存。
- **(2) prime cover** `∀p∈π(G), ∃Mi, p∈σ(Mi)`: **Theorem 13.9** (σ disjoint union)。「G の各素数は
  或る極大の σ-prime」= 単純群の σ-coverage、非自明 (uniqueness 経由)。
- **(4) tildeM-disjoint**: support disjointness from σ-disjoint + R-data。
- **(5) G# covering**: **Cor 14.9** (final covering)。type-P で zTilde piece 追加。
- **Pf-side 追加**: reps 族 (極大共役類 transversal) 構成 + BGTheoremECoverData 全 field +
  BGTheoremETypeICovering/NonTypeICovering の cover/disjoint。

## 決定した分解プラン (multi-session)

**Phase 0 (理解確立) — DONE (本 issue)**: 統計 + Coq 構造 (`BGsummaryE` repackage) + 在庫/gate マップ。

**Phase 1 (partition core)**: prime cover (conjunct 2) を `sigma_reps_pairwise_disjoint` (conjunct 3)
と合わせて **π(G) partition** を完成。要 = 「∀p∈π(G), ∃ 極大 M, p∈σ(M)」(Theorem 13.9 系)。
最も self-contained な partition piece。

**Phase 2 (gated-endpoint skeleton)**: `theoremE_sigma_partition_and_counting_of_inputs` を組み、
conjunct 3 (proven) を discharge、cardinality/cover/covering を named gate に isolate
([[feedback-gated-endpoint-skeleton-pattern]])。

**Phase 3 (deep gates)**: 14.5(c) cardinality (Theorem D 依存)、13.9 cover、14.9 covering を順に。
Theorem D (S16:961) 自体が sorry ゆえ上流。

**Phase 4 (Pf-side)**: reps 族構成 + `bgTheoremE_cover_data` を BG-side から repackage、
`BGTheoremECoverData` 全 field 供給 → consumer card_LF_coprime_pq を unblock。

## 完了条件

`bgTheoremE_cover_data` (Pf 8.17) が sorry-free で `BGTheoremECoverData` + covering を供給し、
card_LF_coprime_pq の `primeFactors_disjoint` cite が解消。中間は各 phase の named lemma が個別 landing
し、残りが正確に深い §13-14 BG gate (Theorem D / 13.9 / 14.9) を named residual で指す状態を維持。

## 参照

- `theoremE_sigma_partition_and_counting` (S16_MainResults:1023) — BG-side 5-conjunct。
- `bgTheoremE_cover_data` / `BGTheoremECoverData` (S10_MinimalSimpleStructure:570/493) — Pf-side。
- `sigma_reps_pairwise_disjoint` (S16:999, proven) — conjunct 3 供給。
- Coq `FT_Dade_support_partition` (PFsection8.v:923) + `BGsummaryE` (BGsection16.v) — 構造正本。
- mmd `references/peterfalvi/04.11*.mmd` (8.14)-(8.18)、BG Theorem E は BG §16。
- consumer chain: card_LF_coprime_pq (S15_SAndT:463) → (13.17) → S16_NonExistenceG → POLE-2。

## ✅ 2026-06-28 進捗 — Phase 1 完了: 無条件 π(G) partition (Theorem E part a) 達成

partition core (clause a) を **無条件 (reps 仮説なし)** で完成。3 lemma 全て sorry-free + axiom-clean
(AxiomsCheck 登録)、full build green:

- `sigma_reps_prime_cover` (S16, clause a1): p∈π(G) ⟺ ∃Mᵢ∈reps, p∈σ(Mᵢ)。forward =
  `exists_mem_sigma_of_prime_dvd_card` (G の各素数は或る極大の σ-prime) + `sigma_conj`; reverse =
  σ⊆π + Lagrange。
- `sigma_reps_pairwise_disjoint` (S16:999, 既済): clause a2 (非共役代表の σ disjoint)。
- **`exists_maximal_conjugacy_reps` (S16, 新)**: 極大共役類の代表系 reps の存在。`IsConjugateSubgroup`
  setoid (`isConjugateSubgroup_equivalence`) の Quotient + `Quotient.out` で transversal 構成、∃! 一意性
  証明。⟹ `hreps` 仮説を無条件に discharge。
- **`exists_reps_sigma_partition` (S16, 新, capstone)**: 上記 3 を結合 → **∃ reps, (maximal) ∧
  (p∈π(G)⟺∃Mᵢ∈reps p∈σ(Mᵢ)) ∧ (非共役で σ disjoint)** = BG Theorem E part (a) の完全無条件形。

⟹ **Phase 1 (partition core) 完了**。残 = Phase 3 (thickened cardinality 14.5c [Theorem D 依存] /
tilde-disjoint [Theorem D R-data 依存] / G# covering 14.9) + Phase 4 (Pf-side `bgTheoremE_cover_data`
の `BGTheoremECoverData` 全 field 供給 + covering、reps 族は `exists_maximal_conjugacy_reps` の indexed
版で供給可)。Phase 3 は §13-14 (Theorem D `theoremD_msigma_conjugacy_and_centralizers` S16:961 自体
sorry) に gated ゆえ上流。次セッション = Phase 4 の reps→ι 変換 + 浅い field 供給、or Theorem D 着手。
