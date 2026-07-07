---
id: 9072
slug: typep2-dade-base-missing
title: "Pf 14.9 T-side coherence: construct type-P-generic Dade isometry (ungated σ-sharp engine) — SOUND, buildable by C"
created: 2026-07-07
---

# Pf 14.9 T-side coherence base — construct type-P-generic Dade isometry (SOUND, not a 4001 dead-end)

**起票者**: lane c (ユーザー「C レーン再開」+「見落としタスクは hub に報告」)。**判断者**: hub (裁定済 2026-07-07)。
**種別**: lane c frontier work (char-core §4/§5 Dade 構成、C 実施可)。

## 🧭 HUB VERDICT (2026-07-07, 敵対的検証 workflow `wf_455f8a09`、confidence HIGH)

**結論: (14.9) T-side coherence route は SOUND。verdict 4001 とは矛盾しない。C はこれを build せよ。**
(4 角度 reader = Lean route / 4001 scope / Coq PFsection14 / 教科書 + 3 敵対的 skeptic が全て refute 失敗で収束。)

- **dead-end 懸念は用語衝突による誤報**: 本 issue 旧タイトルの「type-P₂/III Dade base」と、4001 が禁じる
  「`IsTypeP2 T` carrier」は**別物**。「type-P2/III」自体が**圏違い** (type-P2 = Peterfalvi type II、type III と
  disjoint)。必要なのは **type-P-generic** (`of_typeP`) な base であって type-P2 版ではない。
- **4001 が禁じるのは狭く 1 点だけ** (issues/4001:163-181 で逐語確認): sorry-free spine constructor
  `section16TypePStructure_of_isMinimalSimpleOdd` に `IsTypeP2 mp.T := sorry` を注入し `Tdata` field を追加する
  こと (= sorry regression + (14.9) は `TypeIIData mp.T` を**出力**ゆえ type-P2 を**入力**化する設計逆転、かつ
  `IsTypeP2 mp.T` は一般に偽で埋まらない)。**T-side coherence route・Dade 構成・T が type-III であることは
  一切禁じていない** (4001 は V-side helper 構成を genuine と明示保全)。
- **Coq が決定的**: `FTtypeP_coh_base` (PFsection8.v:811-819) は `of_typeP` のみでパラメトライズ (P1/P2 gate 無し)、
  `rmR_T := FTtypeP_coh_base maxT TtypeP` (PFsection14.v:724) は `notTtype2`/`Ttype3` の下 = **type-III の T に対して
  base を構築**、S 側 (`rmR_S` :459) と `of_typeP` レベルで対称。coherence は degree-p uniform subfamily `calT1` に
  `subset_subcoherent` + `uniform_degree_coherence` ((5.7) equal-degree route)。
- **必要な部品は ungated で既存**: `dadeSupportHypothesisData_of_subset_sigmaSharp` (S10:2160、IsTypeP1 不要) が
  全 type で σ-sharp 台上の genuine `DadeSupportHypothesisData` を産する。`dadeSupportHypotheses_typeP` の `hA1`
  branch は既にこれを hP1 無しで使用。**IsTypeP1-gated なのは `typePA` branch のみ**で、それは 9008 で偽と判明、
  かつ T^# coherence が要するものではない。
- **critical path 確認**: `T_typeIII_ratio_le` は feitThompson → … → `T_isTypeP2` (:1147) → 本 sorry (S16:942) で
  **transitively 必要** (vestigial でない)。※ vestigial なのは別 object の `hyp.base.tauT` free field
  (`tauT:=0`、FeitThompson.lean:2562-2571 で off-path)。`T_typeIII_ratio_le` は `tauT` を読まず、局所の
  `hyp07 : S07.Hypothesis calT1_set A` を組む (両者は別物)。

### C への具体 build plan (6 step)

1. **spine を触らない**: `Tdata`/`IsTypeP2 mp.T` field 追加や `section16TypePStructure_of_isMinimalSimpleOdd`
   への sorry 注入は**禁止** (= 4001 の唯一の禁止事項)。T の type-P witness は off-spine の
   `reconciled_typePData_T` を使う。
2. **T-side Dade isometry を構成**: ungated な `dadeSupportHypothesisData_of_subset_sigmaSharp` (S10:2160) から
   `DadeSupportHypothesisData` を得て、`tau := dadeIntegralCharacterMap dadeData.dade` を type-I パターン
   (S14_MaximalI.lean:153-157) に倣って構成。difference-image は `dadeCharacterDifferenceImageOfDiff` (S14:3799)。
3. **`S07.Hypothesis calT1_set A` (= `T_typeIII_calT1_coherent` の局所 `hyp07`、S16:719) を組む**: landed の
   `irrSubcoherent` assembler (S07_Subcoherent.lean:148) に τ + per-member difference image + isometry を threading
   → S16:942 sorry 内の coherence carrier (`horth`) を discharge。
4. 本 issue は**再タイトル済** (「type-P2/III missing」→「type-P-generic 構成、SOUND」)。旧「dead-end/blocks」枠は撤回。
5. **A-set 確定 (build で)**: coherence は T^# 上、σ-sharp datum は A1(T)=T_σ^#、Coq betaT0∈CF(T,A0(T))
   (PFsection14.v:789) は A0(T) を示唆 → `hsuppdiff` を満たす A を build で確定。
6. **残 residual は分離維持**: `T_typeIII_ratio_le` の他の残 (v=|V| via (13.12) d=1 = lane-b gated / S-side Γ
   bridge + norm) は coherence base とは別物ゆえ conflate しない。

## 背景 (2026-07-07 lane c, 徹底調査で root-cause 確定)

C の (14.9) char body `T_typeIII_ratio_le` (`S16_NonExistenceG.lean:906`) の唯一の実質的残 carrier =
**`calT1` coherence**。coherence engine 自体は proven: `T_typeIII_calT1_coherent` (`:704`) は
`S07.coherent_of_constant_degree` に正しく還元し、in-lane part (`hirr`/`hdeg`/`hSfin`/degree-p/count
`T_typeIII_calT1_card_eq`) を全て ungated で discharge 済み。**唯一 sorry ゆえん = 入力
`hyp07 : S07.Hypothesis calT1_set A` (T-side type-P Dade package) の構築**。

### root-cause: T-side type-P Dade isometry base が repo に不在 (char-core gap)

- **`hyp.base.tauT` (`S15_SAndT_Setup.lean:178`) は property 0 個の bare free field**。対照的に `tau3`
  (`:203`) は直後に ~15 property field (`tau3_isometry` 等)。`tauS`/`tauT` は isometry/ZIrr/support 一切なし。
  instantiation site (`FeitThompson.lean:2587`) では **`tauT := 0`** (placeholder) or opaque threading。
  ⟹ `tauT` は Dade map として機能しない。
- **type-P Dade support builder `dadeSupportHypotheses_typeP` (`S10_MinimalSimpleStructure.lean:2451`) は
  `IsTypeP1 M` gated** — type-P₁ (`A(M)=(M')^# =M_σ^#`) のみ扱い、**type-P₂/type-III 版が存在しない**。
  これが docstring の「from-scratch §4/§5 build with no existing type-P Dade base」= Coq `FTtypeP_coh_base`。
- S07.Hypothesis の 7 field (`S07_Coherence.lean:1767`) の内、Dade map に依存する `tau`/`tau_isometry_diff`
  /`difference_image`/`difference_images_orthogonal` + 別 hyp `hZIrr` は**全て concrete Dade map の定理**
  (S14 型-I は `hyp.dadeData.dade` = genuine Dade isometry から `dadeIntegralCharacterMap_*` で discharge)。
  contentless `tauT` では posit するしかなく gated。**在庫 assembler `irrSubcoherent` (`S07_Subcoherent.lean:148`)
  は τ + per-member Rdatum + hiso を与えれば 1-shot で package 可能** ⟹ 欠けているのは **concrete τ とその
  difference-image/isometry data** のみ = type-P₂/III Dade base。

### settled cross-lane verdict と整合

- **issue 4001** (2026-06-30 HUB): base `Hypothesis` は意図的に非対称 (`Sdata : TypePData S` あり、**Tdata
  なし** — T は larger-κ で type-P₂ とは限らない、`FeitThompson.lean:276`)。Tdata 入力 carrier 追加は
  design 違反/dead-end と裁定済み。
- **issue 9013**: T-side residual (v-value + Dade package) = lane-b §13 char cascade gated。
- **note `s16_w4_char_cascade.md`**: common bottom-out = "concrete §3/§4 Dade-isometry construction +
  (7.5) Frobenius/TI norm formula (repo unimplemented)"。

## やること

> ⚠ 下記は起票時の framing。hub verdict (🧭 節) が route を明確化し、**局所 `hyp07` を `tSideDadeMap` で
> 構築する**方針に更新された (`tauT` free-field 供給は不要と判明)。実装は下記でなく hub verdict の 6-step。

- [x] ~~`hyp.base.tauT` に genuine Dade map を供給~~ → **superseded**: `T_typeIII_ratio_le` は `tauT` を
  読まず、局所 `hyp07 : S07.Hypothesis calT1_set A` を `tSideDadeMap` (§10 Dade integral char map) から構築。
- [x] C が `irrSubcoherent` で `hyp07` を構築 → `horth` coherence carrier を discharge (commit `c8875eb2`)。

## 完了条件

char-core lane が type-P Dade base を landing → C が `irrSubcoherent` で `hyp07 : S07.Hypothesis calT1_set A`
を構築 → `T_typeIII_ratio_le` (`:942` sorry) の coherence carrier を close (残 carrier = v=|V| (13.12 d=1) +
S-side βₛ bridge + norm)。

## 参照

- `OddOrder/Peterfalvi/S16_NonExistenceG.lean:704` (`T_typeIII_calT1_coherent`, proven engine),
  `:906`/`:942` (`T_typeIII_ratio_le` + sorry call site)
- `OddOrder/Peterfalvi/S07_Coherence.lean:1767` (`S07.Hypothesis`), `S07_Subcoherent.lean:148` (`irrSubcoherent`)
- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean:178` (`tauT` free field), `:819` (`dadeHypS`, S-side genuine base)
- `OddOrder/Peterfalvi/S14_MaximalI.lean:153` (type-I genuine Dade map pattern)
- `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean:2451` (`dadeSupportHypotheses_typeP`, IsTypeP1-gated)
- 関連: issue 4001 (Tdata 非対称裁定), 9013 (T-side residual), 9000 (typeP_Galois), note `s16_w4_char_cascade.md`

## ✅ 完了 (2026-07-07 lane c、commit `c8875eb2` → hub 統合 `06d5a0cb`)

**完了条件 (coherence carrier の close) 達成**。hub verdict の 6-step build plan (step 2/3/5) を実装し、
`T_typeIII_ratio_le` の `horth` coherence carrier を **posited 仮説から実証明に置換** (de-opacify)。
実装は hub verdict どおり **局所 `hyp07` を `tSideDadeMap` で構築** (旧「やること」の `tauT` free-field
供給案は不採用 = superseded; `T_typeIII_ratio_le` は `tauT` を読まない)。追加した sorry-free 構成:

- `T_typeIII_calT1_family` (S16:677) — coherence assembler の全入力 (`hinertia`/`hne`/`hlinear`/`hconj𝒯`
  + count) を公開。inflated non-principal linear `Irr(QV/Q)` を quotient corestriction `q` で持ち上げ。
- `T_typeIII_sigmaSharp_eq` (S16:979) — 台恒等式 `sigmaSharp T = (derivedInG T)^#` (= `(T')^#`)、
  `A1_eq_sigmaSharp` + `mainSubgroup .III = derivedInG` 経由。member `Ind_{QV}^T θ` が正規 `QV=T'` の外で
  消えることが Dade domain を保証する linchpin。
- `T_typeIII_hyp07` (S16:1017) — landed `S07.irrSubcoherent` に `τ = tSideDadeMap` + family predicates
  + per-member `dadeCharacterDifferenceImageOfDiff` + isometry `tSideDadeMap_isometry_diff` を threading
  して `S07.Hypothesis calT1_set A` を構築 (ungated、S-side βₛ / (13.12) 入力不要)。
- `T_typeIII_calT1_isCoherent` (S16:1312) — end-to-end `hyp07 ∘ T_typeIII_calT1_coherent`。

`T_typeIII_ratio_le` の `horth` は inline で discharge (`IsCoherent.extension_inner_eq` の isometry +
orthonormal irreducible sources)。build green (leaf 3903 / full 3934 jobs)、新 axiom 無し、signature 不変。

**残 residual (別 issue で追跡、本 issue の scope 外)**: `T_typeIII_ratio_le` の `hcard2` (`(|V|−1)/p ≥ 2`、
`|V|` 下界 = lane-b (13.x) gated) + S-side βₛ bridge (`Γ = ∑ x_ζ·τ₁ζ + Γ₁` + norm) = **issue 9013**。
これらは coherence base とは別物 (step 6)。T-side (14.9) route の残り (`hVcomm` 等) は **issue 9000**
(typeP_Galois char body, lane-a owned) に収束 — C の ungated (14.9) coherence work は本 commit で完了。
