---
id: 1045
slug: pf-9-11-section9-level
title: "(9.11) を §9 レベル (Hyp (9.2)+(9.4)+(9.5)) で述べ直して型 II へ拡張"
created: 2026-07-20
---

# (9.11) を §9 レベル (Hyp (9.2)+(9.4)+(9.5)) で述べ直して型 II へ拡張

issue 9163 §3 項目 3 ((9.11) M 側の type-II 拡張) の実体。**hub 裁定が置いた前提
(「§12 hypothesis 層の作り直し = `type_alt` を type-II 込みに広げ、`base.A0` を
`typePACore` 上に建て直す」) は実測で外れていた**ので、本 issue に正しい gate を記録する。

## 書籍 (PDF p.50-51 で確定, 2026-07-20)

- **(9.2) Hypothesis**: M は **Type II, III または IV** の maximal。H, U, W₁, W₂ は (8.4) と同じ、
  q = |W₁|。⟸ 節タイトル自体が "On the Maximal Subgroups of G of Types II, III and IV"。
- **(9.4)**: 正規部分群 H₀ ◁ M と素数 p で (a) H₀ ⊂ H, H̄ = H/H₀ は非自明 elementary abelian
  p-群、(b) **type III/IV なら** p = |W₂| かつ H̄ は U に中心化されない M の chief factor。
- **(9.5) Hypothesis** (§9 の残り全体で仮定): (9.2) + H₀ as in (9.4)。
  **C = C_U(H̄)** ← ⚠ `C_U(H)` **ではない**。Ū = U/C, u = |Ū|, **W̄₂ = C_H̄(W₁)**, U′ = [U,U],
  C′ = [C,C]。τ = (A(M), M, G) に関する Dade isometry。
  𝒳 = {χ ∈ Irr HU | H ⊄ Ker χ}, 𝒮 = Ind^M_{HU} 𝒳, 𝒮(Y) = Ind^M_{HU} 𝒳(Y)。
- **(9.6)**: U ≠ C, H̄ は M の chief factor, **|W̄₂| = p**, |H̄| = p^q。
  ⚠ 証明は「type III/IV なら仮定から。type II のときは (9.3)+[BG] Prop 1.5(d) で C_H̄(U) = 1、
  ゆえに U ≠ C …」と**両方を証明している** = 全型で成立。
- **(9.11)**: 𝒮(H₀C′) is coherent。⟸ (9.5) の下、つまり **型 II 込み**。

## repo の現状と真の gate (2026-07-20 実測)

**§9 の生の装置は既に型一様**:

- `S11.TypesIIIIIIVSetup` (WielandtSetup.lean:57) = Hypothesis (9.2) そのもの
  (`type_alt : IsTypeII ∨ IsTypeIII ∨ IsTypeIV`)。
- `S11.ChiefFactorData` (同 :1388) = (9.4) の carrier (opaque でない)。
- `S11.Section11CharacterData` (ChiefFactorCore.lean:620) = Hypothesis (9.5)。
  **`C = cSub = C_U(H̄)`**, `Cprime = cprimeSub = [C,C]`, `tau`, honest な 𝒳/𝒮/𝒳(Y)/𝒮(Y)
  (free field でなく `xiSet`/`sSet`/`sOf` に pin 済) を持つ。
- ⟹ **(9.11) を述べるべき場所はここ** — `sOf data (chief.H0 ⊔ cprimeSub data chief)` の
  coherence。型仮定は一切要らない。

**現状の (9.11) は §11 packaging の上に建っている**:
`S13.coherent_sOf_H0Cprime` (S13_Orthogonality.lean:1197) は `S13.Hypothesis M`
(= §11 = 書籍 "Maximal Subgroups of Types III and IV"、`type_alt : IsTypeIII ∨ IsTypeIV`) と
`base : S12.Hypothesis M` (= §10、`type_alt : III ∨ IV ∨ V`) を取る。
⟹ **carrier 自体が型 III/IV に固定されている**ので、`htype` を外すだけでは型 II に届かない。

`htype`/`hncH0C` の実際の用途 (実測、issue 9163 の当初分析どおり):
`S11_NineElevenCaseA` / `_AlphaBound` / `_PairAdjoin` では **全て**
`rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]` = **`hyp.C = cSub` の辞書同一視**に消える。
`hyp.C = C_U(H)` と書籍の `C = C_U(H̄)` は **H₀ = 1 のときだけ一致**するので、
§11 packaging は「H₀ = 1」((11.7)、型 III/IV 専用) を経由してこの等式を作っている。
型 II では H₀ ≠ 1 ゆえこの経路は本質的に閉じる。

⟹ **真の gate = 「(9.11) が §9 の C = C_U(H̄) でなく §11 の C = C_U(H) の上に建っている」**。
`typePA`/`typePACore` (9163 の当初の争点) は (9.11) の gate ではなかった。

## ✅ 済 (2026-07-20): (9.6) の型一様化

`chiefFactor_basic` は docstring 自身が「書籍は |W̄₂| = p だが repo は型 III/IV 限定の
|W₂| = p に退避している」と特殊化債務を認めていた。**W̄₂ と C_U(H̄) で述べ直せば退避は不要**:

- `S11.chiefFactor_cSub_ne_U` — (9.6) 第 1 節 `U ≠ C` (C = `cSub` = C_U(H̄))。新規。
  carrier の `U_noncentral_on_quotient` を `card_cSub_eq_card_ker` 経由で読むだけ。
- `S11.chiefFactor_U_not_centralizes_H` — 旧第 1 節 `C_U(H) ≠ U` は上の系
  (`C_U(H) ≤ C_U(H̄)`)。**hG と型分岐が両方不要になった** (旧証明は (9.3) 経由)。
- `S11.chiefFactor_basic` — 書籍どおりの型一様 (9.6): `U ≠ C ∧ |W̄₂| = p ∧ |H̄| = p^q`。
  `|W̄₂| = p` は既存の型一様 `chiefFactor_card_W2bar` がそのまま供給する。
- supporting: `S11.cSub_subgroupOf_U_eq_ker_map` (`cSub_subgroupOf_U_normal` から抽出)。
- 4 宣言とも axiom-clean、AxiomsCheck 登録済。型限定の `|W₂| = p` は carrier field
  `ChiefFactorData.typeIII_IV_p_eq_W2` として残る (そこが本来の居場所)。

## 進捗 (2026-07-20)

### ✅ 上流 prerequisite: (8.15) が全 3 主張とも型一様になった (issue 1042/1046, close 済)

書籍では (9.11) の base subfamily coherence が **(8.15.3) 経由**なので、
`S10.typePACore_subcoherent` (型仮定 `IsTypeP` のみ) が揃ったことで素材ができた。
現状の repo は代わりに §10 engine (`inducedFamily_degreeSubfamily_isCoherent`) を経由している。

### ✅ 着手順 2 の再配置 (§9 の事実を §9 へ戻す)

- `sSet_finite` : `S15_SAndT_Setup/HypothesisBasics` (ns `S15`) → `S11_.../CliffordData` (ns `S11`)
  — commit 998d28af5。
- `sOf_closedUnderConjugate` : `S13_MaximalIII_IVBasic` (ns **`S13.Hypothesis`**) →
  `S11_.../ThetaCountAssembly` (ns `S11`)。
  ⚠ `namespace Hypothesis` の内側に居たので実名は `S13.Hypothesis.sOf_closedUnderConjugate`
  で、consumer は `Hypothesis.sOf_closedUnderConjugate` と書いていた — **§9 の事実が §11 の
  packaging 名を着ていた**。10 ファイルを修飾し直し (残余 0 を grep 確認)。
  ⚠ 置き場は `CliffordData` では**不可**: 証明が `induceHU_eq_induce`
  (`SummandComplementKernel`) を使う。S11 ディレクトリの import 鎖は
  `WielandtSetup → ChiefFactorCore → CliffordData → InertiaLift → CuS0 → CharacterCounts →
  Coherence911 → CaseBXi → InnerCompHom → SummandComplementKernel → ThetaCountAssembly`
  なので最下流の `ThetaCountAssembly` が正しい home。

- `irrCut_conjClosed` : `S13_MaximalIII_IV` (ns `S13`) → `S11_.../ThetaCountAssembly` (ns `S11`)。
  `hyp : S13.Hypothesis M` を `data : TypesIIIIIIVSetup M` へ引数化 (実使用は `s11Setup` のみ、
  `hyp.base.finiteG` も `[Finite G]` binder があるので不要だった)。consumer 2 ファイル。

⟹ **着手順 2 の再配置は完了**。§9 の生の装置はこれで全て §9 に在る。

### ✅ 実測 (2026-07-20): §10 依存を (8.15.3) で外す経路が確定

`sOf_degreeSubfamily_isCoherent` の §10 依存 (`inducedFamily_degreeSubfamily_isCoherent`) は
**(8.15.3) + (5.7) で置換できる**。書籍もその順序:

1. `S10.typePACore_subcoherent` (本 session landed, 型仮定 `IsTypeP` のみ) が
   `S07.Hypothesis S (supportInSubgroup (typePACore M) M)` = **(5.2)** を与える。
2. `S07.coherent_subset_of_constant_degree` (`S07_Subcoherent.lean:259`) が
   (5.2) + 定次数・共役閉・有限・`2 ≤ ncard` などから
   `Nonempty (IsCoherent hyp.tau S' A)` を出す。

**接続に要る 2 つの事実は両方 repo に在る** (実測):

- **`huSub data = (derivedInG M).subgroupOf M`** — `huSub_eq_derivedInG_subgroupOf`。
  ⟹ §9 の族 `sOf` は `M′` から誘導している = (8.15.3) の族と同じ誘導元。
- **`M_F ≤ M_σ`** — `BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma`。
  ⟹ §9 の絞り `H = M_F ⊄ Ker χ` は (8.15.3) の絞り `M_σ ⊄ Ker θ` を**含意する**
  (対偶: `M_σ ⊆ Ker θ` かつ `M_F ≤ M_σ` なら `M_F ⊆ Ker θ`)。

⟹ **`sOf data Y ⊆ S10.inducedNonKernelFamily ((derivedInG M).subgroupOf M) ((Msigma M).subgroupOf M)`**
が成り立つ。これが橋渡し補題。

⚠ 型 III/IV では `M_s = M′` なので (8.15.3) の絞りは `θ ≠ 1` に退化し、§9 の族の方が真に狭い
— それでも `⊆` の向きなので問題ない。

⚠ **置き場**: `inducedNonKernelFamily` は `S10_SubcoherentTypeP.lean`、`sOf` は
`S11_.../ChiefFactorCore.lean` にあり、両者は**兄弟** (どちらも他方を import しない;
`S10_SubcoherentTypeP` を import するのは `AxiomsCheck` のみ)。⟹ 橋渡し補題は
両方を import する新 leaf か、`S10_SubcoherentTypeP` に S11 への import を足すか。
後者は §8 の file が §9 を import することになるので、**新 leaf が素直**
(例 `S11_NineElevenSubcoherentBridge.lean`)。

### ✅ 橋渡し補題 実装完了 (2026-07-20): `S11_NineElevenSubcoherentBridge.lean` 新設

- `S11.hInHu_le_Msigma_subgroupOf` — `M_F ≤ M_σ` を `subgroupOf` で 2 段持ち上げ。
- `S11.sOf_subset_inducedNonKernelFamily` — `𝒮(Y) ⊆ S10.inducedNonKernelFamily M′ M_σ`。
  両方 axiom-clean、AxiomsCheck 登録済。

⚠ **instance で 2 度直した** (レシピに書いていなかった分):
1. `inducedNonKernelFamily` は `[Fintype ↥M]` binder を持つので `[Finite G]` だけでは
   合成できない ⟹ `open scoped OddOrder.Peterfalvi.S12.FiniteInduce in` を付けて
   `Fintype ↥M` / `Invertible` を `Finite G` から一様に供給させる。
   (`huSub data` 側と `(derivedInG M).subgroupOf M` 側で `Invertible` が 2 つ要るが、
   scoped 経由なら同一 source なので `▸` transport が通る。)
2. `open scoped … in` は **docstring の前**に置く (docstring と宣言の間に入れると
   `unexpected token 'open'; expected 'lemma'`)。

`hKeq ▸ hbase` の transport はレシピどおり素直に通った。

### ⛏ 次の一手: §9 レベルの degree-subfamily coherence

橋渡しが landed したので、`sOf_degreeSubfamily_isCoherent` の §10 依存を外す組み立てに入れる。

**⚠ 重要な制約 (実測)**: `S10.typePACore_subcoherent` は
`hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ` を要求する = **族全体が既約**でないと使えない。
§9 の `sOf data Y` は可約メンバー (μ-列) を含むので**そのままでは渡せない**
(`S10_SubcoherentTypeP` の module docstring「Irreducible members only」の scope note どおり)。
⟹ `S := {φ ∈ sOf data Y | IsIrreducibleCharacter φ ∧ φ 1 = d}` (= degree-`d` 既約 cut)
を渡すのが正しい。この cut は
- `⊆ sOf data Y` かつ橋渡しで `⊆ inducedNonKernelFamily M′ M_σ`
- 共役閉 = `S11.irrCut_conjClosed` (本 session で §9 化済)
- 有限 = `S11.sOf_finite` の subset

**`S07.coherent_subset_of_constant_degree` (S07_Subcoherent.lean:259) の義務一覧**
(`S' := S` と取れば `hsub` は `subset_refl`):

| 引数 | 供給元 |
|---|---|
| `hyp : S07.Hypothesis S A` | `S10.typePACore_subcoherent` (橋渡し + irrCut_conjClosed) |
| `hconj'` | `S11.irrCut_conjClosed` |
| `hSfin` | `(S11.sOf_finite data Y).subset` |
| **`hcard : 2 ≤ S'.ncard`** | ⚠ **パラメータとして露出する** (下記 S15 先例) |
| `hirr : ∀ ζ ∈ S', inner ζ ζ = 1` | `IsIrreducibleCharacter.inner_self_eq_one` |
| **`hZIrr : ∀ a b ∈ S', tau (a − b) ∈ ZIrr G`** | Dade 写像の整数性。⚠ 一番重い義務 |
| `hconst` | cut の定義から自明 |
| `hdeg0 : deg ≠ 0` | `d ≠ 0` (既約指標の次数は正) |
| `h1A : (1 : ↥M) ∉ A` | `S10.typePACore_one_not_mem` |
| `hsuppdiff` | `S10.inducedNonKernelFamily_conjDiff_support` の一般化 (今は `φ − φ̄` 専用、任意の 2 元差へ広げるか、Hypothesis の `tau_isometry_diff` 経由) |

### ✅ S 側に完全な先例がある — `S15.Hypothesis.sSetIrrDeg_coherent`

`HypothesisBasics.lean:390` が **同じ (5.7) 組み立てを S-instance で既に完遂している**。
10 引数の discharge をそのまま雛形にできる:

- **`hcard` は パラメータ `h2` として露出する** — 同 docstring が明言:
  「repo に `2 ≤ ncard` の事実は無い ((9.8.d) の数え上げは *存在* `∃ ζ` しか与えない)。
  露出すれば def は sorry-free に保て、真の上流 count は caller に委ねられる —
  **the honest pattern**」。
  ⟹ ⚠ 当初メモの「`χ ≠ χ̄` から導く」は**採らない**。S15 先例に合わせて露出する。
- **`hZIrr`** = `S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported` に
  `hsuppdiff` + `Submodule.sub_mem _ ha.mem_ZIrr hb.mem_ZIrr` を渡すだけ。
- **`hsuppdiff`** = 「等次数 ⟹ `1` で消える」+「`A ∪ {1}` の外で両方消える」。
  ✅ **`S10.inducedNonKernelFamily_diff_support` として実装済** (2026-07-20)。
  conj 版はその特殊化。S 側の対応物は `sSetIrrDeg_member_diff_supported`。

⟹ 3 つの「重い」義務のうち **`hcard` は露出、`hsuppdiff` は実装済、`hZIrr` は既存補題 1 本**。
残り 7 つと合わせて、組み立ては S15 の雛形をなぞるだけになった。

### 設計判断: (5.7) の companion は **§8 レベル**に置く

`inducedNonKernelFamily_subcoherent` (= (5.3.b)) と**同じ一般性**で書く:

```
noncomputable def inducedNonKernelFamily_degreeSubfamily_coherent {A : Set G}
    (hodd) (h46 : S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h46.K : ℂ)]
    (dd : DadeSupportHypothesisData M A)
    {S} (hsub : S ⊆ inducedNonKernelFamily h46.K h46.subH)
    (hirrS) (hconjS) (d : ℂ) (hconst) (hd0) (hSfin) (h2) (h1A) :
    Nonempty (S07.IsCoherent (…).tau S (S04.supportInSubgroup A M))
```

理由:
- `hsuppdiff` = `inducedNonKernelFamily_diff_support` は `h46` を要るので、`h46` を
  パラメータに持つ形が自然 (`typePACore_subcoherent` のように内部で組むと、
  同じ `h46` を 2 度組んで defeq 不一致を招きやすい)。
- §8 に置けば §9 への依存が要らない — 橋渡し leaf を経由するのは §9 側の instantiation だけ。
- ⚠ instance 規律: `typePACore_subcoherent` と同じく `[Finite G]` +
  `open scoped S12.FiniteInduce in` で統一する。

⟹ 順序: (a) §8 に上記 companion、(b) §9 で `sOf` の degree cut に instantiate
(橋渡し + `irrCut_conjClosed` + `sOf_finite`)、(c) それで
`sOf_degreeSubfamily_isCoherent` の §10 依存を置換、(d) (9.11) statement 本体。

### ✅ (a) 完了 (2026-07-20): `S10.inducedNonKernelFamily_degreeSubfamily_coherent`

(5.7)∘(5.3.b) の companion を §8 レベルで landed。axiom-clean、AxiomsCheck 登録済。
一発で通った (S15 雛形どおり)。`h2 : 2 ≤ S.ncard` は先例どおりパラメータ露出。

⚠ `noncomputable def` で書いたら `linter.defProp` に叱られた — `Nonempty _` は `Prop` なので
`theorem` が正しい。(`inducedNonKernelFamily_subcoherent` は `S07.Hypothesis` = データを返すので
`noncomputable def` のままでよい。返り値が `Prop` かどうかで使い分ける。)

### ✅ (b) 完了 (2026-07-20): `S11.sOf_degreeSubfamily_coherent`

`𝒮(Y)` の degree-`d` 既約 cut の coherence を **(8.15.3) → (5.7)** で組んだ
(`S11_NineElevenSubcoherentBridge.lean`)。axiom-clean、AxiomsCheck 登録済。
**これで (9.11) base case が §10 μ-grid engine から独立した** — 経路上に型仮定は一つも無い。

⚠ `h46.K` / `h46.subH` を `M′` / `M_σ` にピンする `hKeq` / `hHeq` は**仮説として取る**。
定義的に一致すると仮定して `Hypothesis46Core` をこの場で組み直すと、
`typePACore_toHypothesis46_core` が作る copy と defeq にならない (本日 1 度踏んだ失敗)。
⟹ 呼び出し側が `typePACore_toHypothesis46_core` の `h46` をそのまま渡し、
`hKeq`/`hHeq` は `rfl` 相当で埋める想定。

### ⚠ (c) は「差し替え」にならない — 実測して方針変更 (2026-07-20)

当初 (c) を「`sOf_degreeSubfamily_isCoherent` (S13_Lemmas113To115.lean:588) の §10 依存を
(b) で置換」と書いていたが、**τ と A₀ が一致しないので drop-in にはできない**:

- §13 版の結論は `S07.IsCoherent hyp.base.tau {cut} hyp.base.A0` で、
  `hyp.base.A0 = supportInSubgroup (typePA0 M typeP) M` (= **A₀(M)**, しかも P₁ 域の `typePA0`)、
  `hyp.base.tau = dadeIntegralCharacterMap hyp.dadeData.dade …`
  (`hyp.dadeData : DadeSupportHypothesisData M (typePA0 M typeP)`)。
- (b) の結論は `A` について一様だが、`h46 : Hypothesis46Core A M` と
  `dd : DadeSupportHypothesisData M A` が**同じ `A`** を共有する形。書籍の (4.6) は
  `A = A(M)` で立つ (`typePACore_toHypothesis46_core` の結論も `Hypothesis46 (typePACore M) M`)
  ので、(b) が自然に落ちるのは **A(M) 上**であって A₀(M) 上ではない。
- `A(M) ⊆ A₀(M)` だが `IsCoherent τ S A` の `A` は単純な単調性を持たないので、
  「小さい台での coherence」から §13 の文が出るわけではない。

⟹ **(c) は削除**。§13 版は §11 packaging 自身の文として現状のまま残し、
**§9 レベルの (9.11) は (b) の τ/A の上で述べる** (= (d) を直接やる) のが正しい。
§13 版との接続が要るなら、それは packaging 層の辞書 (9163 §3 項目 4) の話であって
base coherence の差し替えではない。

### ✅ (d) の部品在庫を実測 (2026-07-20) — **全部 §9 以下に在る**

`caseA_coherent_sOf_H0Cprime_of_refuter` (S11_NineElevenCaseA.lean:70) を §9 へ降ろすのに
要る部品の所在を全部確認した:

| 部品 | 所在 | 判定 |
|---|---|---|
| `caseA_character_count_exact` | `S11_SingleFactorCentralizer` | §9 ✅ |
| `u_odd` / `uprimeSub` | `S11_.../CharacterCounts` | §9 ✅ |
| `u_le_relIndex_uprimeSub_U` | `S11_SingleFactorCentralizer` | §9 ✅ |
| `sOf_antitone` / `cprimeSub` / `cSub_le_U` | `S11_.../ChiefFactorCore` | §9 ✅ |
| `sOf_finite` | `S11_.../CliffordData` | §9 ✅ (本 session 新設) |
| `sOf_closedUnderConjugate` / `irrCut_conjClosed` | `S11_.../ThetaCountAssembly` | §9 ✅ (本 session 移設) |
| `derivedInG_eq_commutator` | `BG/Ch3_.../S10_BetaRadicalCore` | 上流 ✅ |
| `coherent_of_maximal_coherent_pair_refuted` | `S07_Subcoherent` | 上流 ✅ |
| `sOf_degreeSubfamily_isCoherent` | `S13_Lemmas113To115` | ⚠ **これだけ §13** — (b) で置換してパラメータ化する |

⟹ **(d) は unblocked**。§13 に残る唯一の依存 `sOf_degreeSubfamily_isCoherent` は
(b) `S11.sOf_degreeSubfamily_coherent` を**パラメータとして受け取る**形にすれば消える。

**(d) の形**:
```
theorem caseA_coherent_sOf_cprime_of_refuter [Finite G]
    (hG) {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (tau : S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M)
    (caseA : CliffordCaseAData chars)
    (hbase : Nonempty (IsCoherent tau {degree-qa 既約 cut of sOf data (chief.H0 ⊔ chars.Cprime)} A0))
    (hrefute : …) :
    Nonempty (IsCoherent tau (sOf data (chief.H0 ⊔ chars.Cprime)) A0)
```
§11 版からの置換対応: `hyp.C` → `chars.C` (= `cSub data chief`)、
`hyp.H0Cprime` → `chief.H0 ⊔ chars.Cprime`、`hyp.base.tau`/`.A0` → パラメータ `tau`/`A0`、
finiteness → `sOf_finite`、`sOf_degreeSubfamily_isCoherent` → `hbase` パラメータ。

⚠ 置き場: `caseA_character_count_exact` が `S11_SingleFactorCentralizer` に在るので、
そこか、それを import する S11 系 leaf。(b) をパラメータで受けるなら橋渡し leaf は不要。

### ✅ (d) 前半 完了 (2026-07-20): `S11.caseA_coherent_sOf_cprime_of_refuter`

(9.11) case (9.7.a) の §9 レベル版を landed (`S11_NineElevenSubcoherentBridge.lean`、
`S11_SingleFactorCentralizer` を import 追加)。axiom-clean、AxiomsCheck 登録済。
`data`/`chief`/`chars` の上で `tau`/`A0` をパラメータに取り、**型仮定はゼロ**。

置換は記録した対応表どおり機械的に通った。⚠ ただし `open scoped S12.FiniteInduce in` を
付け忘れて `Fintype ↥M` が合成できず 1 度落ちた — このファイルの他 2 定理は付けてあった。
**§9 の `sOf` 系を触る宣言には一律で付ける**と覚えるのが早い。

### ⚠ case B は case A のように機械的には降ろせない (2026-07-20 実測)

`caseB_coherent_sOf_H0Cprime` (S13_CoreStructure.lean:760) を読んだ結果、
**case A と違って §10 依存が本質的**:

- **pivot が μ-column**: 証明は `μ₁ = columnSum (hyp.base.toHypothesis46 …)
  (hyp.base.muColumnChar … ⟨1, hw2⟩)` を anchor に取る。μ-grid は §10 (S12) の装置で、
  §9 の carrier には無い。
- **`htype` が本質的に効く 2 箇所**:
  - `caseB_forall_mem_sOf_H0Cprime_apply_one_eq_qu hG hyp caseB hncH0C htype` (一様次数 `qu`)
  - `columnSum_muColumnChar_mem_sOf_H0Cprime hG hyp ⟨1,hw2⟩ hk1 hncH0C htype` (pivot の所属)
  後者は以前 trace したとおり「`𝒮(⊥)` へ緩めて **H₀ = ⊥** を使う」= (11.7)、型 III/IV 専用。
- 他に `hyp.params.w2_prime`、`hyp.base.tau_inner_eq_of_supported`、
  `hyp.base.one_notMem_A0`、`caseB_sOf_memberRFamily` など §10/§11 の部品を多用。

### ✅ 書籍を読んだ (2026-07-20, PDF p.53-54) — case B は書籍では **2 行**

**(9.11) の証明冒頭**: 「By (8.15), Hypothesis (5.2) holds for `L = M`.
**By (9.9.a) and (5.7), `𝒮(H₀C′)` is coherent in case (9.7.b).**
Suppose that case (9.7.a) holds. …」

⟹ case (9.7.b) は **(9.9.a) + (5.7) の 2 引用だけ**。case (9.7.a) の方が長い議論。

**(9.9.a)** (p.54): 「If `χ ∈ 𝒳(H₀)`, then `χ(1)` is divisible by `u`.
**If `χ ∈ 𝒳(H₀C′)`, then `χ(1) = u`** and χ is induced to `HU` from a linear character of `HC`.」
⟹ case (b) では `𝒮(H₀C′)` の**全メンバーが次数 `qu` の一様**。だから (5.7) が直接効く。
**μ-column pivot は書籍の議論に出てこない** — 予想どおり repo の anchor は packaging 由来。

⚠ ただし単純に §8 companion (`inducedNonKernelFamily_degreeSubfamily_coherent`) は使えない:
**(9.9.b)** が「`𝒮(H₀)` は**可約**指標 `μ_j` (1 ≤ j < p) をちょうど p−1 個含み、
`μ_j ∈ 𝒮(H₀C)`」と言う。`H₀C′ ≤ H₀C` ゆえ `𝒮(H₀C) ⊆ 𝒮(H₀C′)` なので
**`𝒮(H₀C′)` は全既約ではない**。⟹ 既約性を要求する
`S07.coherent_subset_of_constant_degree` ではなく、**norm-general な (5.7) engine**
`S07.uniform_degree_coherence_of_families` (repo に既存、§11 caseB が使っている) が要る。
その pivot は**書籍の `μ_j` そのもの**。

⟹ **前 iteration の「μ-column anchor は packaging 由来」は半分だけ正しかった**:
pivot が要ること自体は書籍どおり (可約メンバーがあるため)。誤っていたのは pivot の**出所**で、
書籍は `μ_j` を **(9.9.b) が (4.7) + Theorem (4.5) から** 構成する — どちらも §6 (S06) の結果で
**§9 レベルで手に入る**。repo が §10 の μ-grid (`muColumnChar`) を使っているのが packaging。

### case B の設計 (書籍準拠)

1. **(9.9.a)** を §9 で: `χ ∈ 𝒳(H₀C′) ⟹ χ(1) = u` ⟹ `𝒮(H₀C′)` の一様次数 `qu`。
2. **(9.9.b)** を §9 で: `𝒮(H₀)` の可約メンバー `μ_j` (p−1 個) を (4.7)+(4.5) から構成し、
   `μ_j ∈ 𝒮(H₀C) ⊆ 𝒮(H₀C′)` を pivot にする。
3. `S07.uniform_degree_coherence_of_families` に流す (§11 caseB と同じ engine、
   ただし pivot と一様次数を §9 由来のものに差し替える)。

### ✅ (9.9) の repo 在庫を実測 (2026-07-20) — **(9.9.a) は既に §9 で型仮定ゼロ**

| 書籍 | repo | 層 |
|---|---|---|
| **(9.9.a)** 一様次数 `qu` | **`S11.caseB_degree_qu`** (CharacterCounts.lean:981) | **§9 ✅ 型仮定ゼロ** |
| (9.9.b) 可約 `μ_j` が p−1 個 | `S06_CertainTypeClifford` :1046/:1108, `S06_CertainTypeSupport`:311 | §6 ✅ |
| (9.9.c) 両半分 | `S11_.../CaseBXi`:803, `S11_.../InnerCompHom`:983 | §9 ✅ |
| (5.7) norm-general engine | `S07.uniform_degree_coherence_of_families` (S07_PivotCoherence) | 上流 ✅ |

⚠ **`caseB_forall_mem_sOf_H0Cprime_apply_one_eq_qu` (S13) の `htype`/`hncH0C` は飾り**:
本体は `S11.caseB_degree_qu hG _ caseB φ` の 1 行で、`htype`/`hncH0C` は
`cprimeSub = derivedInG hyp.C` を `C_eq_cSub_of_noncoherent` で書き換えるためだけに在る
= **本 session 冒頭から繰り返し見ている「`hyp.C = cSub` の辞書同一視」と同じ artifact**。
`caseB_degree_qu` は `chars.SOf (chief.H0 ⊔ chars.Cprime)` の上で直接述べられている。

### ⛏ case B の残り = pivot 周り 3 件を §9 へ

まだ §13 に在るのは以下 3 件だけ (いずれも `S13_MaximalIII_IV.lean`):

- `caseB_sOf_memberRFamily` — メンバーごとの `R`-data 分配 (既約 = signed Dade /
  可約 μ-column = `certainTypeR`)
- `caseB_sOf_memberRFamily_orthogonal` — (5.2.e) の cross-orthogonality
- `sOf_anchor_diff_support` — pivot に対する差の台

⟹ この 3 件を §9 (`data`/`chief`/`chars`) 上へ降ろし、pivot を §10 μ-grid の
`muColumnChar` でなく **(9.9.b) の可約メンバー** (§6 の count 由来) から取れば、
case B も型仮定ゼロで組める見込み。**(9.9.a) と engine は既に揃っている**。

### (旧メモ) case B の §9 化は**転記ではなく書籍の case (b) の議論を §9 で組み直す**作業。
書籍の (9.7)(b) は Galois 分岐 (`Ū` が体乗法群の部分群) で、そこでの (9.11) は一様次数 `qu`
から直接 (5.7) を回す形。repo が μ-column を anchor にしているのは §10 packaging 由来であって
書籍の必然ではない可能性が高い — **(9.7)(b) と (9.9) を PDF で読んでから設計する**こと
(推測で転記しない)。

**現状の (9.11) §9 化の到達点**:

| 部分 | 状態 |
|---|---|
| `clifford_dichotomy` (9.7) 分岐 | ✅ 既に `chars` 上・型仮定なし |
| base subfamily coherence | ✅ (b) `sOf_degreeSubfamily_coherent` ((8.15.3)→(5.7)) |
| case (9.7.a) | ✅ `caseA_coherent_sOf_cprime_of_refuter` (型仮定ゼロ) |
| case (9.7.b) | ⛏ **要設計** (上記) |
| (9.11) 本体 (両 case の合成) | ⛏ case B 待ち |

### (参考) 実装レシピ

```
theorem sOf_subset_inducedNonKernelFamily [Finite G]
    (hG : IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ S10.inducedNonKernelFamily ((derivedInG M).subgroupOf M)
                   ((BG.Ch3.S10.Msigma M).subgroupOf M)
```

定義 (実測):
- `huSub data = (data.H ⊔ data.U).subgroupOf M` (ChiefFactorCore:45)
- `hInHu data = (data.H.subgroupOf M).subgroupOf (huSub data)` (同:72)
- `xiSet data = {χ | ¬ (hInHu data ⊆ Ker χ)}` (同:77)
- `xiOf data Y = {χ ∈ xiSet data | ((Y.subgroupOf M).subgroupOf (huSub data)) ⊆ Ker χ}` (同:83)
- `S10.inducedNonKernelFamily K H' = {φ | ∃ θ : Irr ↥K, ¬(H'.subgroupOf K ⊆ Ker θ) ∧ φ = induce K θ}`

手順:
1. `intro φ ⟨χ, hχ, rfl⟩`。
2. **まず `huSub data` の上で示す**:
   `induceHU data χ ∈ S10.inducedNonKernelFamily (huSub data) ((Msigma M).subgroupOf M)`
   - witness は `χ` 自身、等式は `induceHU_eq_induce data _`。
   - 絞りの含意: 示すのは `¬ (((Msigma M).subgroupOf M).subgroupOf (huSub data) ⊆ Ker χ)`。
     `hχ.1 : ¬ (hInHu data ⊆ Ker χ)` と
     **`hInHu data ≤ ((Msigma M).subgroupOf M).subgroupOf (huSub data)`** から対偶で出る。
     後者は `data.H ≤ Msigma M` (= `M_F ≤ M_σ`,
     `BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM` + `data.typeP.H_eq`) を
     `Subgroup.subgroupOf` の単調性で 2 段持ち上げる。
3. **型の transport**: `huSub data` と `(derivedInG M).subgroupOf M` は
   **命題的に等しいだけ** (`huSub_eq_derivedInG_subgroupOf`) なので、
   `↥(huSub data)` と `↥((derivedInG M).subgroupOf M)` は別の型。
   ⟹ repo 既存の流儀どおり **`hKeq ▸ h`** で運ぶ
   (`S15_SSetMemberRFamily.lean:80-85` が `inducedKernelFamily` で同じことをしている実例)。
   `inducedNonKernelFamily` も `K` が explicit 引数なので同じ形で通るはず。

⚠ 置き場は前述のとおり新 leaf (S10_SubcoherentTypeP と S11_.../ChiefFactorCore は兄弟)。

### ⛏ 残り = 着手順 1 (§9 レベルの (9.11) statement 本体)

形: `(data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)`
`(chars : Section11CharacterData data chief)` の上で
`Nonempty (S07.IsCoherent chars.tau (sOf data (chief.H0 ⊔ chars.Cprime)) A0)`。

⚠ `chars.H0CprimeSupport` は producer によっては `∅` の placeholder
(`S12.Hypothesis.mkSection11CharacterData` / `S15` の counting 用) なので、
support は**明示パラメータ**で取るのが素直 (S15 の honest 版は `A(S) = typePACore` を渡している)。

⚠ chain 本体 (`S11_NineElevenCaseA` 16 / `_AlphaBound` 15 / `_PairAdjoin` 5 の
`S13.Hypothesis` 引数) は `hyp.base`/`hyp.params` を各 130/196/72 箇所使うので、
**どこまでが §10 の μ-grid に真に依存し、どこからが packaging か**の切り分けが先。
`caseA_coherent_sOf_H0Cprime_of_refuter` (S11_NineElevenCaseA.lean:70) を読んだ限りでは
`hyp.base.tau` / `hyp.base.A0` (= パラメータ化可能) と finiteness 橋渡しが主で、
`sOf_degreeSubfamily_isCoherent` だけが §10 engine
(`inducedFamily_degreeSubfamily_isCoherent`) に実依存する。
書籍ではそこが (8.15.3) 経由 ⟹ `S10.typePACore_subcoherent` で置換できる見込み。

## 着手順 (残り)

1. **§9 レベルの (9.11) statement を立てる** — `(data : TypesIIIIIIVSetup M)`
   `(chief : ChiefFactorData data)` `(chars : Section11CharacterData data chief)` 上で
   `Nonempty (S07.IsCoherent chars.tau (sOf data (chief.H0 ⊔ chars.Cprime)) chars.H0CprimeSupport)`。
2. **既存の chain を §9 レベルへ降ろす**。`S11_NineElevenCaseA` (S13.Hypothesis 引数 16 箇所) /
   `_AlphaBound` (15) / `_PairAdjoin` (5) が `S13.Hypothesis` を取っているが、
   `hyp.base`/`hyp.params` 参照が各 130/196/72 箇所あるので、どこまでが §10 の μ-grid に
   真に依存し、どこからが packaging かを先に切り分ける。
   ⚠ `S11_NineElevenTwoSummand` / `_TIWitness` / `_MackeyNorm` / `_Coherence` /
   `_SingleFactorCentralizer` は既に `TypesIIIIIIVSetup` 上 = 降ろす必要なし。
3. §13 側 `coherent_sOf_H0Cprime` を §9 版の系にする (`C_eq_cSub_of_noncoherent` を渡す)。
   signature 不変にできれば下流 (§13/§15) は無変更。
4. 型 II instance。`S15` 側の型一様 (9.11) (`Hypothesis.sSet_coherent_indS_A`,
   S15_CaseACoherence.lean:713) が既に型仮説ゼロ・`H0CprimeSupport := A(S)` で通っている
   = §9 レベルで述べられることの実現可能性の証拠。

## 完了条件

(9.11) が `TypesIIIIIIVSetup` + `ChiefFactorData` + `Section11CharacterData` の上で
型仮定なしに述べられ、型 III/IV 版がその系になること。

## 参照

- issue 9163 (hub 裁定 Option B′ + 実測記録)、issue 1044 ((8.18) 型一様化、同型の作業)
- 書籍 PDF `references/peterfalvi/pdf/04.11_pp_50_57_*.pdf` p.1-3 (= 書籍 p.50-52)
- `notes/peterfalvi/frontier_measured_2026_07_19.md` §9
