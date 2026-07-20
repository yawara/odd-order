---
id: 9163
slug: typepa-mssharp-rescope-for-815-typeii
title: "HUB: (8.15) type-II 完全形式化に向けた typePA の M_s^# 添字化設計確認 (9008 re-open trigger)"
created: 2026-07-19
---

# HUB: (8.15) type-II 完全形式化に向けた typePA の M_s^# 添字化設計確認 (9008 re-open trigger)

lane a → hub。issue 1042 着手順 3 の gate (1042 の gate 注記が「着手時に 9000 issue で
hub に設計確認を出すこと」と指定)。

## 背景

- **9008 裁定 (closed)**: repo の `typePA` は `(M′)^#` 添字固定 (`typePA_eq_sharpSubgroup_derivedInG`)。
  書籍 (8.10) は core `M_s^#` 添字 (`A(M) = ⋃_{x∈M_s^#} C_{M′}(x)^#`) で、type P₂ (= type II,
  `M_s = M_F ⊊ M′`) では書籍の A(M) は真に小さい (`(M′)^# ∩ …`、Frobenius 補元点 `U^#` を除く)。
  9008 は「全 consumer が P₁ 域でのみ使う」ことを根拠に Option B (現状維持 + IsTypeP1 narrow) を
  採用し、「S-side honest 化の設計変更が起きた場合のみ Option A (typePA 訂正) を再検討・re-open」
  と裁定した。
- **trigger 発火**: 全 3 冊フェーズで (8.15) の**番号としての完全形式化** (type II 込み) が
  lane a の割当に入った (issue 1042)。着手順 1 ((5.2) instance, P₁ 域) と 2 ((4.6) instance,
  H = M_F / M_s 両方、P₁ 域) は 2026-07-19 に完了:
  `OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean` / `S10_Hypothesis46TypeP.lean` (axiom-clean)。
  残り = type II での忠実な A(M) を要する部分のみ。

## 設計分岐 (hub 裁定を求める点)

type II で書籍忠実な `A(M)` をどう持つか:

- **Option A (9008 の再検討対項)**: `typePA` 自体を `M_s^#` 添字に訂正
  (`centralizerSupport (sharpSubgroup M_s) (derivedInG M)` 相当へ)。
  - 影響: shared infra。`typePA` の全 consumer (S10/S12/S13/S15 系、lane b の S12/S14 consumer
    含む) に波及。P₁ 域では `M_s = M′` ゆえ値は不変だが、`typePA_eq_sharpSubgroup_derivedInG` が
    「P₁ 仮定つき」へ弱まり、全 rw 箇所に IsTypeP1 仮定が伝播する。
  - 利点: (8.10)/(8.15) が全型で書籍どおり 1 本の def で立つ。
- **Option B′ (新 def 並置)**: `typePA` は現状維持 (P₁ 域専用のまま)、型 II 用に別 def
  (例: `typePACore M data` = `M_s^#` 添字版) を新設し、(8.15) type-II instance はそちらで立てる。
  P₁ 域では `typePACore = typePA` の等式 lemma で接続。
  - 影響: 既存 consumer 無変更 (波及ゼロ)。二重定義の管理コスト + 「どちらが正本か」の
    docstring 明示が必要。
- 前提の追加確認事項: repo に `M_s` (Peterfalvi (8.10) の core; type I/II/V = M_F, III/IV = M′)
  の def が既にあるか (BG 側 `Msigma`/FTcore 系との対応込み) の実測。無ければ M_s def の
  新設から (これ自体は ungated)。

lane a の推奨 = **Option B′** (波及ゼロ、9008 の「P₁ 域は現状維持」裁定と両立、
type II instance が必要とする最小追加)。ただし cross-lane 影響 (lane b の S12/S14) を持つのは
Option A のみなので、hub の裁定対象は「A を再検討するか、B′ で確定するか」。

## 追記 (2026-07-19, lane a): (8.18) も本裁定に gated

(8.15) だけでなく **(8.18) の一般化も同じ gate に当たる** (frontier note 項目 8 の次候補として
実測): 書籍 (8.18) は S, T を型仮定なしの非共役 maximal で述べ、証明中で
「A(T) − A₁(T) ≠ ∅ ⟹ T は type I/II」を導出する (PDF p.49 確認済)。repo の (8.18.a/b/c) は
`TypeIData S/T` 固定 (S10_MinimalSimpleStructure.lean:404/481/575) で、type-II 側へ広げるには
**type II の忠実な A(T)** が要る — つまり P₂ 域の typePA 問題そのもの。type-II consumer が
(8.18.b) を導出せず structure field `cross_zero` として仮定している件も、この gate が解けるまで
解消不能。⟹ 本裁定の scope は (8.15) type-II instance + (8.18) 一般化 + cross_zero 導出の 3 件。

## やること

- [ ] hub: Option A vs B′ を裁定 (必要なら consumer grep で波及を実測)
- [ ] 裁定後 lane a: M_s def の実測 → (無ければ) 新設 → type-II 側 (8.15) instance
      (claim 1 の typeII datum は既存 = `S10_MinimalSimpleBasic` の typeII instance;
      claim 2 は `typePData_toHypothesis46_hallKernel` が H 側は既に忠実 (type II で
      M_s = M_F)、A 側の差し替えのみ; claim 3 は `S10_SubcoherentTypeP` の A パラメータ
      差し替え)

## 完了条件

hub 裁定が本 issue に記録され、lane a が type-II 側 (8.15) instance の実装方針を
一意に決められる状態になること。

## 2026-07-19 追記 (lane a 実測): gate の範囲は (8.15)/(8.18) より広い — (9.11) M 側も同 gate

Pf 本文 frontier の次項目として **(9.11) の type-II 一般化**に着手しようとして実測したところ、
**これも本 issue に gated** と判明した。frontier note を再分類済
(`notes/peterfalvi/frontier_measured_2026_07_19.md` §9 (9.11) 行)。

実測内容 (htype を leaf まで trace):

- `coherent_sOf_H0Cprime` (S13_Orthogonality.lean:1197) の `htype : IsTypeIII ∨ IsTypeIV` は
  **(9.11) の数学に使われていない**。全て `C_eq_cSub_of_noncoherent` (S13_CoreStructure.lean:511)
  へ流れ込む**辞書同一視** (packaging の `H₀C′` ↔ generic `cprimeSub` 層) の artifact。
  そこから (11.7) `H₀ = 1` → `ChiefFactorData.typeIII_IV_p_eq_W2` (`|W₂| = p`) に落ちる。
  この `|W₂| = p` は **type II では偽** (`chiefFactor_basic` docstring に明記:
  `|W₂|^q = |H| = p^q·|H₀|` ゆえ `|W₂| = p` は `H₀ = 1` のときのみ)。
- 生の §9 装置 (`S11_NineEleven*`) は `TypesIIIIIIVSetup` (type_alt は type II 込みの 3 分岐)
  上に書かれており **既に type-agnostic**。
- **type-II を含む honest な (9.11) は既に存在する**:
  `Hypothesis.sSet_coherent_indS_A` (S15_CaseACoherence.lean:713) は**型仮説を一切取らず**、
  support に **本 issue の Option B′ = `honestTypeP2ASet`** を使う。
  `nineElevenEqualityRefutationS` の docstring が明言: 「M 側の `htype`/`hncH0C` は
  packaging を generic 層と同一視するためだけに在り、S-instance では辞書が定義的なので消える」。

⟹ **M 側 (9.11) を type-II へ広げる = §12 hypothesis 層の作り直し**:
1. `S12.Hypothesis.type_alt : IsTypeIII ∨ IsTypeIV ∨ IsTypeV` (S12_MaximalIII_IV_V_Core/
   Hypothesis.lean:353) ゆえ **type-II では文が立たない**。
2. `base.A0 = supportInSubgroup (typePA0 M typeP) M` が誤った `typePA = (M')^#` 上に建つ
   = **まさに本 issue の争点**。
⟹ **裁定 (Option A vs B′) の波及先に (9.11) M 側も加えて評価されたい**。
なお §15 が既に B′ を実装して回っている事実は、B′ 側の実現可能性の証拠になる。

---

## ✅ hub 裁定 (2026-07-19 22:5x) — **Option B′ で確定。Option A は却下し 9008 を re-open しない**

### 1. 判定と実測根拠

| 観点 | Option A (`typePA` を M_s^# 添字へ訂正) | **Option B′ (採用)** |
|---|---|---|
| 波及 | `typePA` は repo 内 **346 hit**。うち `typePA_eq_sharpSubgroup_derivedInG` の **rw が 38 箇所** (S10_MinimalSimpleBasic / S13_MaximalIII_IV ほか)。全てに `IsTypeP1` 仮説が伝播 | **ゼロ** |
| cross-lane | `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Basics.lean` と `.../S16_MainResults/Notation.lean` が `MaximalSubgroupType` を import = **他レーン consumer に波及** | 影響なし |
| 実現可能性 | 未実証 | **既に実装され稼働中** — `honestTypeP2ASet M = centralizerSupport (sharpSubgroup (Msigma M)) (derivedInG M)` (`S15_SAndT_Setup/SubcoherenceInputs.lean:73`) の上で (9.11) S 側 `Hypothesis.sSet_coherent_indS_A` が**型仮説を一切取らずに**通っている |

⟹ Option A は「1 本の def で全型を書籍どおりに立てる」という美点に対し、38 箇所の仮説伝播 +
他レーン波及という代価が釣り合わない。**B′ 確定**。

### 2. ただし「新 def を並置する」のではなく **既存 `honestTypeP2ASet` を正本に昇格**する

9163 本文の B′ 案は「型 II 用に別 def を新設」だが、**それは既に在る**。三つ目の def を作らず、
既存を格上げすること (二重定義の管理コストを避ける):

- **改名**: `honestTypeP2ASet` → **`typePACore`**。現名は「type P₂ 用の一時策」に読めるが、実体は
  書籍 (8.10) の `A(M) = ⋃_{x ∈ M_s^#} C_{M′}(x)^#` **そのもの** (全型で正しい) なので、
  名前をその事実に合わせる。旧名の参照は `S15_NineElevenSteps.lean` ほか **lane a 所有 file 内のみ** ゆえ単純置換でよい。
  `honestTypeP2A0Set` も同様に `typePACore0` へ。
- **置き場所**: **`OddOrder/Peterfalvi/S10_StructureSetup.lean`** (または同レベルの新 leaf)。
  S10 系 consumer と S15 の**共通上流**で、`Msigma` と `typePA` の両方が既に closure にある
  (`S10_MinimalSimpleBasic` は `S10_StructureSetup` のみを import して `Msigma` を 60 箇所使用)。
  ⚠ **`OddOrder/GroupTheory/MaximalSubgroupType.lean` には置かない** — `Msigma` は
  `BG/Ch3_MaximalSubgroups/S10_HallStructureCore.lean:112` にあり、GroupTheory 側から import すると
  層が逆転する (BG/Ch4 が `MaximalSubgroupType` を import している)。
- **橋渡し補題**: `IsTypeP1 M data → typePACore M = typePA M data` (P₁ では `M_s = M′`)。
  これで既存 P₁ consumer は**一切変更不要**のまま、型 II 側は `typePACore` で立つ。
- `typePA` 側の docstring (`MaximalSubgroupType.lean:436` の caveat) に「書籍忠実版は
  `typePACore`、本 def は P₁ 域専用」と相互参照を入れる。

### 3. 本裁定で unblock される範囲 (= lane a の次の割当)

9163 が gate していた 4 件を **B′ 上で順に進める**。着手順は上流優先 + 文書順:

1. **(8.15) type-II instance** (issue 1042 着手順 3) — claim 2 の A 側差し替え + claim 3 の
   `S10_SubcoherentTypeP` A パラメータ差し替え
2. **(8.18) の一般化** — `TypeIData S/T` 固定を外す。併せて type-II consumer が structure field
   `cross_zero` として仮定している分を**導出に置換**
3. **(9.11) M 側の type-II 拡張** — `S12_MaximalIII_IV_V_Core/Hypothesis.lean:353` の
   `type_alt` を type-II 込みに広げ、`base.A0` を `typePACore` 上に建て直す
4. 上記で残る packaging 層の辞書同一視 (`htype`/`hncH0C`) の整理

### 4. lane b への影響

**なし**。b の S12/S14 consumer は `typePA` のまま不変 (P₁ 域専用であることが docstring で明示される
だけ)。b が型 II の A(M) を要する箇所に来たら `typePACore` を cite する。

## 参照

- issues/closed/9008 (Option B 裁定と re-open 条件 — **本裁定で re-open しないことを確定**)
- issues/closed/1043-pf-9-7-full-fidelity.md ((9.7) 完了; 次項目調査で本追記に至った)
- issues/1042-pf-8-15-dade-hypothesis-instances.md (着手順 3 の gate 注記)
- OddOrder/GroupTheory/MaximalSubgroupType.lean:436 (`typePA_eq_sharpSubgroup_derivedInG` の
  caveat docstring = 9008 の要約)
- OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean / S10_Hypothesis46TypeP.lean (P₁ 側完了分)

---

## 2026-07-20 lane a: 裁定に沿った実装記録 + 実測による前提訂正

### ✅ 昇格 (§2) 完了 — commit 92983806b

`honestTypeP2ASet` → `typePACore` / `honestTypeP2A0Set` → `typePACore0` を
`OddOrder/Peterfalvi/S10_StructureSetup.lean` の (8.10)--(8.13) 節へ移設・改名 (2 重定義は作らず)。
初等 API (`mem_typePACore`, `_subset_sharp`, `_one_not_mem`, `_subset_derived`, `_subset`,
`_conj_mem`, `_subset_hatMsigma`) も同時に昇格。橋渡し `typePACore_eq_typePA_of_isTypeP1` /
`typePACore0_eq_typePA0_of_isTypeP1` を追加、既存 `typePA` consumer は無変更。

裁定文書の「lane a 所有 file 内のみ」は**実測では不正確**だった: 改名は 30 files に及び、
`OddOrder/FeitThompson{CharacterData,NuGrid,Section16Core}.lean` と `AxiomsCheck.lean` も含む。
ただし当時 b/c はいずれもこれらに触れていなかった (b = BaseChange/AxiomsCheck、
c = CLAUDE.md/issue のみ) ので衝突なしで完了。

副産物として `centralizerSupport_sharpSubgroup_of_le` (H ≤ K なら
`centralizerSupport (K^#) H = H^#`) を一般形で切り出し、`typePA_eq_sharpSubgroup_derivedInG` を
その 1 行の系にした (証明の重複解消)。`sharpSubgroup_conj_mem` は S10_MinimalSimpleBasic から
S10_StructureSetup へ上げた (同一 namespace ゆえ consumer 無変更)。

### ✅ §3 項目 1 ((8.15) type-II instance) 完了 — commit 106bbe509

- `typePData_toHypothesis46_ofSupport`: support `A` と (4.6.c) の `H` を両方パラメータ化した
  claim-2 の core。既存 `typePData_toHypothesis46` (A = typePA) はその系、signature 不変。
- `typePACore_toHypothesis46` / `_core` / `_hallKernel`: A = typePACore 上の 3 instance。
  `_core` が書籍の H = M_s = M_σ 選択 (Coq `FT_prDade_hyp` 相当)。
- 重複解消: `S13_PrimeTIResidueBridge.hypothesis46OfTypePData` (同じ field 組み立ての
  type-uniform 版) を削除し、唯一の consumer `S15.Hypothesis.hyp46S` を
  `S10.typePACore_toHypothesis46_core` への委譲に置換。
- 全宣言 axiom-clean、AxiomsCheck 登録済。`lake build OddOrder.AxiomsCheck` green (4483 jobs)。

**数学的要点**: (4.6.d) covering の向きが 2 系列で反転する。`typePA` では `A = K^#` ゆえ
covering は任意の `H ≤ K` で自明だが support が P₂ で過大主張。`typePACore` では support が
正確で covering は `H ≤ M_s` に対する support の定義そのもの。書籍が (8.15.2) を core `M_s` を
手にした状態で述べる理由がそのまま形式化に写った。

### ⚠ 前提訂正: `cross_zero` は「仮定」ではなく既に導出済み (item 2 後半は空)

本 issue §3 項目 2 は「type-II consumer が structure field `cross_zero` として仮定している分を
導出に置換」としていたが、**実測では既に導出されている**:

- `S12.TypeIICrossIsometryData.cross_zero` (S12_TypeIIFrobenius.lean:1081) は
  producer `S12.exists_typeIICrossIsometryData_at_pair`
  (S12_TypeIICrossIsometryPair.lean:1390) が
  `tau1_muColumn_sub_zeta_inner_extension_diff_eq_zero_at_pair` から供給。
- その下流 `cross_dade_inner_eq_zero_at_pair` (同 :1023) が (8.18.b) の本体で、
  型一様な (8.12.b) = `BG.Ch4.S16.uniqueMaximal_of_kappaSigmaCompl_element` に落ちている。
- 3 宣言とも `#print axioms` = propext / Classical.choice / Quot.sound のみ。

⟹ item 2 の実体は「cross_zero の導出化」ではなく **(8.18) 全体の一般化** のみ。
現状の (8.18) 導出は canonical pair 固定 (`Section16MaximalPairCore G`; `mp.T` = type P₁、
`mp.S` = type II) で、書籍の「型仮定なしの非共役 maximal ペア」には未一般化 = 特殊化債務。

### item 2 ((8.18) 一般化) の実測した gate — typePA ではなく「型一様な A(M)」

書籍 (8.18) (PDF p.49) は S, T を型仮定なしの非共役 maximal で述べる。証明の型判定ステップ
「Since A(T) − A₁(T) ≠ ∅, T is of Type I or II」は (8.10) 末尾の
「A₁(M) = A(M) = (M')^# if M is of Type III, IV or V」の対偶で、これは
**commit 26f9dd17b で形式化済** (`typePACore_eq_A1_of_isTypeP1` /
`not_isTypeP1_of_mem_typePACore_not_mem_A1`、axiom-clean)。

残る真の gate は **型一様な `A(M)` の def が repo に無いこと**:
- 添字側は既に型一様 (`mainSubgroup M tau = Msigma M`、全 5 型、`mainSubgroup_eq_Msigma`)。
- host 側だけが分岐する: type I は `M` (`typeIA M data = centralizerSupport (M_F^#) M`)、
  type 𝒫 は `M'` (`typePACore M = centralizerSupport (M_σ^#) M'`)。
- ⟹ `A M tau = centralizerSupport (sharpSubgroup (mainSubgroup M tau)) (host M tau)`
  (host: I ↦ M、他 ↦ derivedInG M) を新設し、両既存 def への橋渡しを付けるのが次の一手。
  これは lane a 所有の `MaximalSubgroupType.lean` 内で完結する (claim 不要)。

前提として要る (8.12.b) / (8.17.a) はいずれも**型一様版が既に repo に在る**ことを実測で確認:
- (8.12.b) 型一様: `BG.Ch4.S16.uniqueMaximal_of_kappaSigmaCompl_element`
  (S16_MainResults/TheoremsAE.lean:216)、および部分群版
  `BG.Ch4.S14.typeP_hall_small_subgroup_cyclic_tau2` (S14_TypePCounting/LocalStructure.lean:486)。
  Peterfalvi 側ラッパー `S10.typeI_or_typeII_centralizer_unique_hall` の型仮定は
  `M_F = M_σ` 変換のためだけで、型一様版を直接呼べば外せる。
- (8.17.a) 型一様: `S10.BGTheoremECoverData.primeFactors_cover` / `_disjoint`
  (S10_MinimalSimpleStructure.lean:655/660)、producer `S10.bgTheoremE_cover_data` (同 :886)
  は型仮定ゼロ (`hG` のみ)。

---

## ✅ 2026-07-20 lane a: §3 の 4 項目すべて完了

| 項目 | 結果 |
|---|---|
| 1. (8.15) type-II instance | ✅ commit 106bbe509 (上記) |
| 2. (8.18) の一般化 + `cross_zero` の導出化 | ⚠ `cross_zero` は**既に導出済**と実測 (上記)。(8.18) 一般化の本体は issue 1044 |
| 3. (9.11) M 側の type-II 拡張 | ✅ **完了** — issue 1045 (close 済) |
| 4. packaging 層の辞書同一視 (`htype`/`hncH0C`) の整理 | ✅ **完了** — 下記 |

### 項目 3 の結果 (issue 1045)

- **(9.11) が Hypothesis (9.2)+(9.4)+(9.5) の上で型仮定なしに完全証明された**
  (`S11.nineEleven_coherent` / `_A0`)。case (9.7.a) の最後の producer
  `S13.nineElevenSevenEightRefutation` (~420 行) を §9 へ降ろして `hrefuteEq` を discharge。
- **型 II instance が立った** (`S11.typeII_nineEleven_coherent`)。足りなかったのは carrier の
  producer だけ (`typePNontrivialCore_of_isTypeII` / `typesIIIIIIVSetup_of_isTypeII` /
  `S11.mkSection11CharacterData`); (9.4) `exists_chiefFactorData` は元から型仮定ゼロだった。
- 本裁定の前提「§12 `type_alt` を広げ `base.A0` を `typePACore` 上に建て直す」は**実測で外れ**、
  真の gate は「(9.11) を §9 レベルで述べ直すこと」だった (issue 1045 冒頭に記録)。

### 項目 4 の結果 — 辞書は 1 箇所に収束した

`S13.coherent_sOf_H0Cprime` を `S11.nineEleven_coherent_A0` の系にした
(`coherent_sOf_H0Cprime_of_section9`、signature 不変)。その結果、
**`htype`/`hncH0C` の用途は `hyp.C = cSub s11Setup chief` (`C_eq_cSub_of_noncoherent`) ただ 1 つ**に
なった。§9 の議論自体は型を一度も見ない。

副産物 (いずれも shared infra):
- `S10.inducedNonKernelFamily_mono` — (4.6.c) の `H` の pin を等式から包含へ緩和
- `S10.DadeSupportHypothesisData.restrict` + `ftSupportKernel_congr_of_subset` — (8.15) datum を
  `A₀(M)` から `A(M)` へ制限 (Peterfalvi (2.11) の package 版)
- `S07_UnionPairBridge.lean` (新 leaf) — union-pair coherent extension (5.6.3) と projection budget を
  §13 closure から §5 レベルへ再層化

⟹ 本 issue は close 可。残るのは重複チェーンの棚卸し (issue 1047) で、これは裁定でなく作業。
