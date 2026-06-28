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

## ✅ 2026-06-28 進捗 (cont.) — Theorem D(1) M_σ-fusion control 実証明

BG Theorem E の残 cardinality/covering は **Theorem D** (`theoremD_msigma_conjugacy_and_centralizers`
S16:961、sorry) に gated。Theorem D には `_of_inputs` skeleton (S16:897) があり D(1) (fusion upgrade)
は既に実証明、残 input = hfusionMσ (Cor 15.3b) / hD2 (Lem 12.17) / hD3 (RData 存在=signalizer 深い) /
hD4 (deep tail)。

**`msigma_fusion_control` (Theorem D(1)、S16、sorry-free + axiom-clean、AxiomsCheck 登録)**: 「M_σ の
2 元が G で共役 ⟹ M で共役」を実証明。`mf_hall_centralizer_control` (Cor 15.3(b)、lane-c 完遂で
sorry-free+axiom-clean) を **trivial Hall H:=M_σ** (M_σ は自身の piSet-Hall、`subgroupOf_self`+
`IsHallSubgroup.top_iff`) に適用 → N_G(M_σ)-fusion、`normalizer_Msigma_eq_self` (N_G(M_σ)=M) で
M-fusion に upgrade。Theorem D の唯一 unconditional な conjunct。

**残 Theorem D = D(2) (Lem 12.17 cyclic M_σ∩M^g) + D(3)/D(4) (R(x) signalizer normal complement の
存在 + sharply transitive action + 一意 N、deep signalizer functor theory)**。D(3)/D(4) が BG local
analysis の最深部で multi-session。⟹ BG Theorem E の Phase 3 (cardinality 14.5c は Theorem D の R(x)
counting に依存) は D(3)/D(4) 完成待ち。次セッション = D(2) (Lem 12.17 cyclic 化が可能か精査) or
D(3) signalizer 着手。

## 🔬 2026-06-28 — Theorem D 残 conjunct (D2/D3/D4) の精密 deep-scoping (次セッション地図)

Theorem D(1) (msigma_fusion_control) 完了後、残 conjunct を Coq `BGsummaryD` (BGsection16:790) +
`sigma_compl_embedding` (BGsection12:2461) で精査。**全て deep BG §12/signalizer machinery (Lean 未ポート)
に gated と確定** — tractable な断片は binding gate を進めない:

- **D(2) cyclic `M_σ∩M^g`** (hD2): Coq 証明で cyclic は **`sigma_compl_embedding`** (§12) 由来。これは
  σ-uniqueness 機構 `sigma_group_trans` (σ-transitivity) / `norm_noncyclic_sigma` (noncyclic σ-subgroup
  ⟹ N(X)≤M) / `cent_der_sigma_uniq` に依存し、**いずれも Lean 未ポート**。前半 `M_σ∩M^g = M_σ∩M_σ^g`
  (Hall-pcore 論法) は tractable だが cyclic でなく hD2 を満たさない。`Msigma_conj_smul` は S14:2923 に
  private 在庫 (要 de-privatize、但し equality 半分用)。
- **D(3) RData 存在** (hD3): `∀x∈M_σ#, ∃R, RData M x R` = R(x) signalizer normal complement の存在 +
  sharply transitive action。Coq `FT_signalizer_context` (signalizer functor theory) 由来 = **BG local
  analysis の最深部**、multi-session の大型ポート。
- **D(4) tail** (hD4): D(3) + 一意 N + 型構造、最深。

**∴ BG Theorem E Phase 3 (cardinality 14.5c) は Theorem D の R(x) counting = D(3)/D(4) signalizer
待ちが真のボトルネック**。Theorem E partition core (Phase 1) は完了済・FT-path 上の genuine 前進。
次セッションの選択肢 = (i) `sigma_compl_embedding` §12 port (σ-uniqueness 3 補題から、D(2) cyclic 用)、
(ii) signalizer functor theory 着手 (D(3)、最深)、(iii) Pf-side Phase 4 の family/partition field 供給
(cardinality/covering は gate 据置の gated-endpoint)。いずれも fresh 集中セッション推奨。

## ✅ 2026-06-28 進捗 (cont.²) — D(2) σ-uniqueness 第1 gate `norm_noncyclic_sigma` を実証明

Theorem D(2) (cyclic M_σ∩M^g) への σ-uniqueness 機構ポートを開始。Coq `sigma_compl_embedding`
(BGsection12:2461) の cyclic 論法を分解 → 2 つの σ-uniqueness gate に帰着:

**✅ gate 1 `norm_noncyclic_sigma`** (commit 54f1b995、S12_ExceptionalBridge、sorry-free+axiom-clean、
AxiomsCheck 登録): noncyclic σ(M)-p-subgroup P≤M ⟹ N_G(P)≤M。Coq BGsection12:1420 を忠実ポート。
全 dep が repo 在庫だった: `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (rank-2 A⊆P) +
`centralizer_le_of_elemAb_rank_two` (Prop 12.4(a)、C(A)≤M) + `fusion_control_of_mem_sigma` 第3 conjunct
(N_G(P)=(N_G(P)⊓M)·C_G(P))。

**❌ gate 2 `cent_der_sigma_uniq`** (Coq BGsection12:2139、**未ポート・深い**): X∈E_p^1(M),
(p∈β ∨ X⊆M_σ') ⟹ 𝓜(C(X))={M}。D(2) の abelian 部分 (K∩M_σ'=1 ⟹ K' =1) に必須。Coq 証明 ~50 行で
**narrow-group 機構** (`narrow_centP`/`beta_max_pdiv`/`rank3_Uniqueness`/`quotient_isom`) 依存 = §12 の
deep multi-lemma undertaking。

**cyclic M_σ∩M^g (D(2)) の残**: (i) gate 2 `cent_der_sigma_uniq` ポート (narrow/β/rank-3 機構)、
(ii) EpMsMg rank-1 論法 (gate1 + fusion 第1 conjunct `not_sCX_M` で X cyclic; **gate1 で unblock 済**)、
(iii) abelian (gate2 経由 K∩M_σ'=1)、(iv) `abelian_rank1_cyclic` 組立、(v) D(2) を theoremD に wire。
gate 1 完了で (ii) は可能、残は gate 2 (narrow-group、次セッション) が真のボトルネック。

## ✅✅✅ 2026-06-28 進捗 (cont.³) — D(2) cyclic 完成。**gate 2「未ポート」は STALE だった**

**⚠ 訂正 (重要)**: cont.² の「gate 2 `cent_der_sigma_uniq` 未ポート・深い・narrow-group 機構」は **誤り**。
`cent_der_sigma_uniq` = **BG Corollary 12.14** (Coq L2133 のコメントが明記) で、Lean に
**`maximalContaining_centralizer_and_someSylow_eq_singleton`** (`S12_Corollary1214.lean`) として
**既に sorry-free + axiom-clean でポート済み**。前 entry は Coq 名 `cent_der_sigma_uniq` で grep して
descriptive 名のポート (CLAUDE.md 命名規約) を見落とした **stale-pointer**。教訓: 「未ポート」と即断せず
descriptive 名・docstring・BG 番号で grep して実コード状態を確認する ([[lanes-are-equivalent-no-specialty]]
の relane #5/#11 stale-pointer と同根)。同様に narrow 機構 (`narrow_centP`=`narrow_iff_exists_card_prime_centralizer_pRank_le_two`,
`narrow_cent_dprod`=`narrow_centralizer_decomp`, `rank3_Uniqueness`=`isUniquelyMaximal_of_three_le_rank_of_lt_top`,
`mFT_rank2_Sylow_cprod`=`sylow_structure` (public), `beta_max_pdiv`=`derived_msigma_hasNormalPComplement_of_not_mem_beta`)
も全て既存だった。

**∴ D(2) cyclic は短経路で完成** (commit 次、full build 3886 green、3 新補題 axiom-clean+AxiomsCheck 登録):
- **core `centralizer_not_le_of_isPGroup_le_Msigma_inf_conj`** (S12_Lemma1217、Coq `not_sCX_M` 一般 X 版):
  nontrivial p-subgroup X≤M_σ∩M^g (p∈σ(M)) ⟹ C_G(X)⊄M。`fusion_control_of_mem_sigma` σ-fusion 推移性 +
  N_G(M)=M。既存 `Msigma_inf_conj_isBetaCompl` の hCnotM を補題化。
- **TI `Msigma_inf_conj_inf_derived_eq_bot`** (S12_Lemma1217、Coq `tiMsMg_Ms'`): M_σ∩M^g ⊓ M_σ' = ⊥。
  nontrivial 元 ⟹ rank-1 X⊆M_σ' ⟹ Cor 12.14 (Or.inr) で C_G(X)≤M ⟹ core と矛盾。
- **cyclic `Msigma_inf_conj_isCyclic`** (S16_MainResults、Coq `abelian_rank1_cyclic` 経路): g∉M ⟹
  IsCyclic(M_σ∩M^g)。abelian (K'≤K⊓M_σ'=⊥, TI) + odd + rank≤1 (noncyclic elementary abelian A≤K なら
  `norm_noncyclic_sigma` で C_G(A)≤N_G(A)≤M、core と矛盾; `exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank`
  で抽出) ⟹ `isCyclic_of_isMulCommutative_of_rank_le_one` (§15)。
- **theoremD wiring**: `theoremD_msigma_conjugacy_and_centralizers` の hD2 を `Msigma_inf_conj_isCyclic` で供給。
  D(1) `msigma_fusion_control` + D(2) cyclic が honest 化、**残 sorry = D(3)/D(4) のみ** (R(x) signalizer
  normal complement、deep、multi-session)。`refine ⟨msigma_fusion_control, fun g hg => Msigma_inf_conj_isCyclic, ?_, ?_⟩`。

**∴ Theorem D 残 = D(3)/D(4) signalizer functor theory のみ** (BG local analysis 最深部)。これが Theorem E
cardinality (14.5c) の真のボトルネック。次セッション = (i) D(3) signalizer 着手 (最深、大型ポート)、or
(ii) Pf-side Phase 4 (family/partition field 供給、gated-endpoint)。**D(2) は完全 close**。
