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
