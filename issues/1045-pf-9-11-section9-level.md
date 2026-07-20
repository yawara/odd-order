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

### ✅ 3 件を読んだ (2026-07-20) — **どれも `htype` を取らない**

`caseB_sOf_memberRFamily` (:452) / `caseB_sOf_memberRFamily_orthogonal` (:616) /
`sOf_anchor_diff_support` (:723) の signature を確認: **3 件とも型仮説を取らない**。
§13 に縛られているのは次の 3 点だけ:

1. `hyp.base.tau` / `hyp.base.A0` — **パラメータ化すれば済む** (case A と同じ)
2. `[NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]` — §10 経由の instance。
   §9 では `data.q ≠ 0` 相当 (`Nat.card_pos`) で足りるはず
3. **IKF 橋渡し** `sOf … → S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥`
   を `hyp.SOf_eq` / `hyp.sOf_subset_SOf` (= `S13.Hypothesis` 経由) で出している

**3 は本 session の橋渡しで既に §9 で出せる**:
`sOf_subset_inducedNonKernelFamily` (橋渡し) と
`S10.inducedNonKernelFamily_subset_inducedKernelFamily_bot` を合成すればよい。
⟹ `S11.sOf_subset_inducedKernelFamily_bot` として実装した。
これで 3 件が `S08.inducedKernelFamily_*` の suite (支持・非実性・対直交性・`ZIrr` 所属) を
`S13.Hypothesis` 無しで借りられる。

⟹ case B の残作業は **3 件の機械的な引数一般化**に落ちた (case A と同型)。

### ✅ 1/3 完了 + ⚠ 残り 2 件のうち 1 件は機械的でない (2026-07-20 実測)

- ✅ **`S11.sOf_anchor_diff_support`** (§9 版) landed。world-bridge + `hKsupp` パラメータ化で
  そのまま通った。⚠ `((derivedInG M).subgroupOf M).Normal` instance は §13 では import 閉包
  から推移的に来ていたので新 leaf では `haveI` 導出が要る。
- ⚠ **`caseB_sOf_memberRFamily` (:452) は機械転記できない**。2 分岐のうち:
  - **既約分岐**は降ろせる (signed Dade family; `dadeData.dade`/`hconj` をパラメータ化 +
    `inducedKernelFamily_conjDiff_support`)。
  - **column 分岐**が §10 μ-grid そのもの: `S06.certainTypeR` を
    **`hyp.base.toHypothesis46 hG hG.odd`** の上で組み、メンバーを
    `hyp.base.muColumnChar hG hG.odd k` の `columnSum` として同定している。
  - 駆動する **`caseB_sOf_member_dichotomy` (:407) は結論自体が §10 表記**:
    `∃ k : Fin hyp.base.w2, … φ = S06.columnSum (hyp.base.toHypothesis46 …)
    (hyp.base.muColumnChar … k)`。証明でなく **statement が μ-grid に依存**している。

⟹ **ここが case B の真の残り**: 書籍 (9.9.b) は可約メンバー `μ_j` を **(4.7) + Thm (4.5)**
= §6 の結果から作る。§9 で同じことをするには **§9 で使える Hypothesis (4.6)** の上で
`S06.columnSum` / `S06.certainTypeR` を組めばよく、それは
**`S10.typePACore_toHypothesis46_core data.typeP …`** で手に入る
(`data : TypesIIIIIIVSetup M` は `data.typeP : TypePData M` を持つ)。
⟹ 作業 = **(9.9.b) の dichotomy を §9 の Hypothesis (4.6) 上で述べ直す**
(`hHall`/`hW2σ`/`hσK` を入力に取る)。これは引数一般化でなく**述べ直し**。

**case B の到達点**:

| 部品 | 状態 |
|---|---|
| (9.9.a) 一様次数 `qu` | ✅ `S11.caseB_degree_qu` (元から §9・型仮定ゼロ) |
| world-bridge | ✅ `S11.sOf_subset_inducedKernelFamily_bot` |
| `hsuppdiff` | ✅ `S11.sOf_anchor_diff_support` |
| (5.7) engine | ✅ `S07.uniform_degree_coherence_of_families` (上流) |
| `R`-family 既約分岐 | ⛏ 降ろせる (機械的) |
| **`R`-family column 分岐 + dichotomy** | ⛏ **§9 の Hyp (4.6) 上で述べ直しが要る** |

### ✅ column 分岐に新規の数学は要らない — §10 は往復しているだけ (2026-07-20 実測)

`S12.Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (S12_HcBound.lean:587)
の証明を読んだ。核心は **1 行**:

```
obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
    -- h = (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis : S06.Hypothesis
```

⟹ **可約メンバーの分類は `S06.Hypothesis.induce_not_isIrreducible_iff` = §6 の事実**。
残りの ~30 行は §6 の `columnFamily`/`chiRestrict` 形を §10 の `muGrid` 形へ変換する bookkeeping。

しかも **`S06.certainTypeR` が消費するのは §6 形の方** (`columnSum h46 χ₂`)。
⟹ §13 chain は「§6 column → §10 muGrid → §6 certainTypeR」と**往復している**だけで、
§9 では **§6 形に留まればよい**。

⟹ **column 分岐に新規の数学は不要**。dichotomy を
`∃ χ₂ ≠ 1, φ = S06.columnSum h46₉ χ₂` (h46₉ = `typePACore_toHypothesis46_core data.typeP …`
の `toCertainTypeHypothesis`/`toHypothesis` 相当) の形で述べ、
`S06.induce_not_isIrreducible_iff` から直接出せばよい。`certainTypeR` もその形で組める。

✅ **実測 (2026-07-20)**: `structure Hypothesis46 A L extends CertainTypeHypothesis A L`
(S06_CertainHypothesis46.lean:82) なので、`S06.Hypothesis` の取り出しは

```
h46.toCertainTypeHypothesis.toHypothesis   -- : S06.Hypothesis ↥M
```

(`Hypothesis46.toCore` が実際にこの形で `toHypothesis` を作っている)。
⟹ `h46₉ := S10.typePACore_toHypothesis46_core data.typeP hG.odd hHall dade0 hconj hW2σ hσK` から
`h46₉.toCertainTypeHypothesis.toHypothesis` で §6 `Hypothesis` が取れる。
これで `S06.induce_not_isIrreducible_iff` / `S06.columnSum` / `S06.certainTypeR` が §9 で使える。

**⟹ case B は全体として「新規の数学ゼロ、§6 形に留まる述べ直し」に落ちた。**

### ✅ dichotomy landed + ⚠ `certainTypeR` に足りない条件を実測 (2026-07-20)

**landed**: `S11.induce_columnSum_of_not_irreducible` (axiom-clean)。
`h46.K` からの誘導が可約 ⟹ `∃ χ₂, induce h46.K χ = S06.columnSum h46 χ₂`。

⚠ **教訓 (4 回試した)**: statement を `columnSum` 形にすれば statement には transport が
出ないが、**証明側**では source character を `↥h46.K` へ運ぶ必要があり
`rw [h46.K = huSub data]` は **motive が type-correct にならない**
(`_a` が `IrreducibleCharacter ↥_a` と `chiRestrict χ₂ = χ` の両方に出る)。
⟹ 回避でなく**分解**で解いた: 補題全体を `h46.K` の内側で述べ coercion を出さない。
§9 の族との同定は **Set 値の別ステップ**に分ける (そこでは `▸` が効く)。
**依存部分は §6 の持ち物、§9 の部分は set-level** という切り方が型的にも正しい。

⚠ **次に埋める穴**: `S06.certainTypeR` (S06_CertainTypeCoherence.lean:648) は

- `hχ₂ : χ₂ ≠ 1`
- `hdeg : (∑ i, (columnFamily χ₂).mu i) 1 = (∑ i, (columnFamily χ₂⁻¹).mu i) 1`

を要求する。**`χ₂ ≠ 1` を本 dichotomy は返していない**。
§13 版はこれを `hk0 : k ≠ 0` (μ-grid の index) から得ていた。
§9 では **`xiSet` の条件 `H ⊄ Ker χ`** から出るはず (χ₂ = 1 なら column は自明側になり
`H ⊆ Ker χ` に落ちる) — ただし未確認。⟹ dichotomy を
`∃ χ₂ ≠ 1, …` に強めるのが次の一手。`hdeg` は §13 版が
`columnSum_inv_apply_one` で埋めているのでそれを使う。

### (3) R-family dispatch の τ-seam を実測 (2026-07-20) — 一致する

2 分岐の τ が一致しないと dispatch が型付かないので確認した:

| 分岐 | 供給元 | τ |
|---|---|---|
| 既約 | `S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj …` (FamilyBundleDade.lean:694) | `dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)` |
| column | `S06.certainTypeR h46 hχ₂ hdeg` (S06_CertainTypeCoherence.lean:648) | `dadeIntegralCharacterMap h46.dade0 h46.tau` |

⟹ **`hyp := h46.dade0` を取れば一致する**。`Hypothesis46 A L` は ambient `A` (= A(M)) と
`dade0` (= **A₀(M)** の Dade hypothesis) を両方持つ ((4.6) が A と A₀ を両方持つのと同じ)。
`typePACore_toHypothesis46_core` は渡された `dade0`/`hconj` をそのまま field に置くので、
**構成上一致する**。§13 版の docstring が「both land *definitionally* on `hyp.base.tau`
… so no `congrMap` seam」と言っているのと同じ状況。

⚠ ⟹ **case B の τ は自由パラメータにできない** — `h46.dade0`/`h46.tau` に固定される。
(case A の `caseA_coherent_sOf_cprime_of_refuter` は τ を自由パラメータで取れたが、
case B は `certainTypeR` が τ を決めるので同じ形にはできない。)

### (2) dichotomy の実装レシピ (2026-07-20 に signature 実測)

```
S06.Hypothesis.induce_not_isIrreducible_iff (h : S06.Hypothesis ↥M) [NeZero (Nat.card h.W1)]
    (χ : IrreducibleCharacter ↥h.K) :
    ¬ IsIrreducibleCharacter (ClassFunction.induce h.K χ) ↔ ∃ χ₂, h.chiRestrict χ₂ = χ
```

§9 での使い方:
1. `φ ∈ sOf data Y` を分解して `φ = induceHU data χ`、`χ ∈ xiOf data Y`。
2. `induceHU_eq_induce data χ` で `φ = ClassFunction.induce (huSub data) χ`。
3. ⚠ **transport**: `h46₉.K` と `huSub data` はどちらも `(derivedInG M).subgroupOf M` に
   等しいが**命題的に**なので、`↥` を取ると別の型。橋渡し補題と同じ `hKeq ▸ …` の流儀で運ぶ
   (`huSub_eq_derivedInG_subgroupOf` + `h46₉.K` 側の等式)。
4. `induce_not_isIrreducible_iff` を適用 → `∃ χ₂, h.chiRestrict χ₂ = χ`。
5. `h.coe_chiRestrict` + `h.induce_restrict_certainType_eq` で
   `φ = S06.columnSum h46₉' χ₂` に変換 (§10 版 S12_HcBound.lean:611-620 が同じ変換をしている
   ので、そこを雛形にする)。
6. `[NeZero (Nat.card h.W1)]` は `h.one_lt_card_W1` から `⟨by omega⟩` で作る
   (§10 版 :598 と同じ)。

⚠ §10 版はこの後さらに `muGrid` 形へ移すが、**§9 ではその変換を行わない** — `certainTypeR` が
消費するのは `columnSum h χ₂` の形なので、そこで止めるのが正しい。

#### ⚠ 依存型 transport の回避 — statement の書き方が肝

素朴に書くと `induce_not_isIrreducible_iff` は `χ : IrreducibleCharacter ↥h.K` を要求する一方、
§9 側の `χ` は `IrreducibleCharacter ↥(huSub data)` で、`h.K` と `huSub data` は
**命題的にしか等しくない** (`huSub data = (data.H ⊔ data.U).subgroupOf M` は定義的、
`h.K = (derivedInG M).subgroupOf M` は `typePData_toS06Hypothesis` の literal)。
⟹ `χ` の運搬は **`↥` を跨ぐ依存型の書き換え**になり、橋渡し補題で使った
「Set 値関数の explicit 引数を `▸` で書き換える」形では済まない (motive 破綻の危険)。

**回避策 (採用すべき形)**: 結論を

```
∃ χ₂, φ = OddOrder.Peterfalvi.S06.columnSum h χ₂
```

と書く。`S06.columnSum h χ₂` の**終域は `ClassFunction ↥M ℂ`** なので、
**statement には依存型 transport が一切現れない**。transport は証明の内部だけに閉じ込められ、
しかも §10 版 (S12_HcBound.lean:611-620 の `hFk`) が
`muGrid` 和 = `induce h.K (chiRestrict …)` を示す形で**同じ変換を既に実演している**ので、
そこを雛形にできる。

⟹ ⚠ **`∃ χ₂, φ = induce h.K (chiRestrict χ₂)` の形で書かないこと** (依存型が statement に漏れる)。

#### ⚠ §6 には**似た名前の 2 層**がある — 取り違え注意 (2026-07-20 実測)

| 構造 | 引数 | 定義場所 | そこに在るもの |
|---|---|---|---|
| **`S06.Hypothesis (L : Type*)`** | `L` は**型** | `S06_CertainTypeClifford.lean:365` の `variable (h : Hypothesis L)` | `chiRestrict` (:795) / `coe_chiRestrict` (:802) / `induce_restrict_certainType_eq` (:761) / `induce_not_isIrreducible_iff` (:1095) |
| **`S06.Hypothesis46 (A : Set G) (L : Subgroup G)`** | `L` は**部分群** | `S06_CertainHypothesis46.lean:82` (`extends CertainTypeHypothesis`) | **`columnSum` (S06_CertainTypeCoherence.lean:57)** / `certainTypeR` |

⟹ **`columnSum` は `Hypothesis46` を直接取る** (当初 `Hypothesis` だと想定していたが誤り)。
`typePACore_toHypothesis46_core` の返り値をそのまま渡せるので好都合。
一方 Clifford 側の変換補題群は `Hypothesis L` (型引数) の上に在るので、
`Hypothesis46 A L` の内側の `Hypothesis ↥L` を経由する必要がある。

**組み立ての鎖** (両層をまたぐ):
```
φ = induce (huSub data) χ                   -- sOf 所属 + induceHU_eq_induce
  = induce h.K χ'                            -- ⚠ huSub data ↔ h.K の transport
  = induce h.K (h.chiRestrict χ₂)            -- induce_not_isIrreducible_iff  [Hypothesis 層]
  = ∑ i, (h.columnFamily χ₂).mu i            -- coe_chiRestrict + induce_restrict_certainType_eq
  = S06.columnSum h46₉ χ₂                    -- columnSum の定義        [Hypothesis46 層]
```
最後の等式で 2 層が噛み合うことを確認するのが実装の要点。

### ✅ case B 完了 + (9.11) 本体 landed (2026-07-20)

**case B は §9 レベルで閉じた**。landed 分 (すべて axiom-clean / AxiomsCheck 登録済、
`S11_NineElevenSubcoherentBridge.lean` 869 行):

| 宣言 | 内容 |
|---|---|
| `exists_induce_eq_of_subgroup_eq` | `K = K'` を跨ぐ誘導元 transport (両辺変数ゆえ `subst` 可の一般形) |
| `sOf_columnSum_of_not_irreducible` | **(9.9.b) の §9 版** — 可約メンバー = 非自明 §6 column |
| `columnRFamily` | `certainTypeR` を `η = μ_{χ₂}` 上に述べ直し |
| `sOf_memberRFamily` | **(5.2.d) datum** — 既約 = signed Dade / 可約 = column の 2 分岐 |
| `sOf_memberRFamily_imageSet_of_irr` / `_of_col` | dispatch の reduction |
| `dadeICM_apply_eq_zero_of_avoidV` | **(4.6) レベルの V-vanishing anchor** |
| `sOf_memberRFamily_orthogonal` | **(5.2.e)** cross-orthogonality (2×2 場合分け) |
| `sOf_member_inner_self_natCast` | (5.7) engine の `hN` (既約 1 / column w₁) |
| `sOf_caseB_coherent` | **case (9.7.b) の coherence** — (5.7) engine の 15 義務を discharge |
| `caseB_coherent_sOf_cprime` | 上を (9.9.a) `caseB_degree_qu` で特殊化 (残る param = pivot のみ) |
| `sOf_nineEleven_coherent` | **(9.11) 本体** — (9.7) dichotomy で 2 分岐を合成 |
| `derivedInG_subgroupOf_normal` | 5 箇所で使う instance の切り出し |

⚠ **実装上の要点 3 つ** (次に同型の作業をするとき効く):

1. **`certainTypeR` が τ を決める** ので case B の τ は自由パラメータにできない
   (case A は自由に取れた)。既約分岐を
   `htau : h46.tau = h46.dade0.fullDadeIsometryData hconj` で合わせる。
   想定 producer `S10.typePACore_toHypothesis46_core` では `rfl`。
2. **`columnRFamily` は `χ₂` をパラメータに残す**。`Classical.choose` で内部確定させると
   `imageSet` が `η` に依存し `image_eq` の rewrite が motive 不整合になる
   (`Exists.elim` は Type 値の goal に効かないので `obtain` も使えない)。
3. **V-vanishing anchor の台の集合は ambient `A` と分離する**。
   `S13.tau_apply_eq_zero_of_mem_typePV` は台を `A(M) = (M')^#` に固定しているが、
   **型一様な `A(M)` (= `typePACore`) は `(M')^#` より真に小さい**のでそのままでは移らない。

### ✅ case (9.7.b) は入力ゼロで完全に閉じた (2026-07-20)

**書籍 p.54 を PDF ページ画像で確認** (⚠ この章の `pdftotext` は文字がバラバラで使えない):

> **(9.9.b)** By (4.7) and Theorem (4.5), **both** `𝒮(H₀)` **and `𝒮(H₀C)`** contain exactly
> `p − 1` reducible characters `μ_j` (1 ≤ j < p). By (a), `μ_j(1) = qu`.

⟹ `𝒮(H₀C)` の分は `𝒮(H₀)` からの移送ではなく **同じ (4.7)+(4.5) を K = H₀C で回している**。
repo の `reducible_count_sOf_K` がその共通議論そのもので (docstring も両 instantiation に言及)、
**5 入力すべてが K = H₀C で既に揃っていた** (`chiefFactor_{H0supC_subgroupOf_normal,
H0supC_le_derived, W1_inf_H0supC_subgroupOf_eq_bot, W2_not_le_H0supC, card_W2bar_H0supC}`)。

- `S11.reducible_count_sOf_H0supC` — 5 行の instantiation。
- `S11.sOf_cprime_nonempty` — `𝒮(H₀C′) ≠ ∅`。`C′ = [C,C] ≤ C` ⟹ `𝒮(H₀C) ⊆ 𝒮(H₀C′)`
  (`sOf_antitone`)、`p` 素数ゆえ `p − 1 > 0`。
  ⚠ **count を H₀ でなく H₀C で取るのが本質**: `𝒮(H₀)` の可約メンバーがより小さい `𝒮(H₀C′)`
  に入る保証は無い。書籍が (9.9.b) を 2 つの carrier で述べている理由がこれ。

⚠ engine の pivot 要求は「メンバーが 1 つ在る」だけ (`hη₂ := η₁.conj` は共役閉+no-real で自動)
なので、可約性そのものは要らなかった。

### ⛏ 残り = case (9.7.a) の 2 パラメータ

`sOf_nineEleven_coherent` が露出しているのは **case A の 2 つだけ** (どちらも
`CliffordCaseAData` で量化してあるので case B は代償を払わない):

| param | 由来 | 状態 |
|---|---|---|
| `hAbase` | degree-`qa` 既約 cut の coherence | ⚠ **τ/A の seam あり (下記)** |
| `hArefute` | maximality refuter = §9 chain 本体 | ⛏ `S11_NineElevenCaseA`/`_AlphaBound`/`_PairAdjoin` の `S13.Hypothesis` 降ろし |

#### ✅ τ/A の seam は解消した (2026-07-20) — 正しい合流点は **A(M) 側**

書籍 (9.5) は「τ = (A(M), M, G) に関する Dade isometry」なので、**(9.11) は A-level で述べる**のが
正しい (T 側の先例 `S15.Hypothesis.sSet_coherent_indT_A` も台が `supportInSubgroup (typePACore T) T`)。
⟹ 動かすべきは case B の方 (A₀ ⇝ A) で、これは**易しい向き**:

- `S11.sOf_caseB_coherent_restrict` を landed。
  - 台の縮小は `S07.isCoherent_of_supportedSpan_le` (含意は `A ⊆ A₀` の単調性のみ)。
  - 写像の載せ替えは `IsCoherent.congrMap` +
    `S08.dadeIntegralCharacterMap_restrict_eq_of_support`
    (A-Dade = A₀-Dade の制限。`typePData_toHypothesis46_ofSupport` が
    `dade := dade0.restrict Set.subset_union_left hAnorm` と置いているので構成上そう)。
  - witness は `η̄ − η`: 奇数位数ゆえ非零、かつ **(4.7) 評価
    (`S10.inducedNonKernelFamily_diff_support`) で A-supported**。
    ⚠ `sOf_anchor_diff_support` が与える A₀-supported では足りない。この (4.7) の鋭さが要。

⚠ **再層化を 1 件実施**: `isCoherent_of_supportedSpan_le` は `IsCoherent` だけの一般事実なのに
`S13_Lemmas113To115` に在り、§9 の leaf (S13 の上流) から import できなかった。
`S07_PivotCoherence` へ移設し S13 の 2 呼び出しを修飾し直した。

#### ✅ 済 (2026-07-20): `sOf_nineEleven_coherent` を A-level に述べ直した

τ / 台を A₀ → **A(M)** へ移した (commit 645805460)。case (9.7.b) は
`caseB_coherent_sOf_cprime` → `sOf_caseB_coherent_restrict` で供給し**入力ゼロのまま**。
新パラメータは `hHeq` (`h46.subH = M_σ`) と `hAnorm` (A の M-共役不変性) のみ。

#### ✅ 済 (2026-07-20): `hAbase` を供給した

`S11.sOf_degreeSubfamily_coherent_restrict` (commit b7a28937f)。読み通りに一発で通った。
`(inducedNonKernelFamily_subcoherent …).tau` は `irrSubcoherent` が `tau := τ` と置くので
`rfl` で `dadeICM dd.dade (…)` に落ちる。pin は `hdd : dd.dade = h46.dade0.restrict …` だけで、
`FullDadeIsometryData` 同士の一致は**不要**だった (下記の鍵のとおり)。

⟹ **(9.11) の case A 残作業は `hArefute` + count `h2 : 2 ≤ ncard` のみ**
(`h2` は S15 先例どおり露出したまま = the honest pattern)。

#### ✅ 済 (2026-07-20): `hArefute` を §9 へ降ろした

`S11.CaseAPairBound` / `S11.CaseAEqualityRefutation` / `S11.caseA_refuter_of_equality_refutation`
(commit 2d27db2ec)。予測どおり **rename で済んだ** — §13 版の `S13.Hypothesis` 依存は
packaging 別名だけだった。`sOf_nineEleven_coherent` の `hArefute` をこの 2 carrier に置換。

⚠ 2 つの `def` に `open scoped S12.FiniteInduce in` を付け忘れて 1 度落ちた
(`sumnS`/`IsCoherent` が `Fintype ↥M` を要る)。**§9 の `sOf` 系を触る宣言には一律で付ける**。

⟹ **(9.11) の残り = `hbound` / `hrefuteEq` / `hAbase` の count `h2` の 3 つだけ**。
経路上に型仮定は一つも無い。

#### ⚠ `CaseAPairBound` producer の実測 (2026-07-20) — rename では済まない

`S13.nineElevenPairBound` の本体 (270 行) の `hyp.*` 使用を数えた:
`s11Setup` 65 / `base` 22 / `chief` 19 / `H0Cprime` 14 / `C` 8 — ここまでは別名。
残りが本質:

| 使用 | 判定 |
|---|---|
| `hyp.type_alt` (1) → `typePNontrivialCore_of_isTypeIIIorIV` で `hnt` を作る | ✅ **§9 では不要**。`TypesIIIIIIVSetup.nontrivial : TypePNontrivialCore M typeP` が**carrier field そのもの**。§13 が型から再導出しているだけ |
| `hncH0C` + `htype` (1 行) → `C_eq_cSub_of_noncoherent` | ✅ **§9 では消える** (`chars.C` は `cSub data chief` と定義的に等しい) |
| `hyp.base.sixTwoDecompositionData` + `hyp.params_*` (5) | ⛏ **本物の §10 依存** |

#### ✅ 訂正 (2026-07-20): `sixTwoDecompositionData` の §9 化は**不要** — engine を直接叩ける

(5.6) engine `S08.coherentDegreeSqNormBound_of_not_coherentW_k` の signature を実測したところ、
`hyp : S04.Hypothesis G A L` と `Dmem` / `Da` (= `CharacterPsiDecomposition`) を
**すべてパラメータで取る完全に generic な形**だった。μ-grid も `S13.Hypothesis` も出てこない。
⟹ `S13.sixTwoDecompositionData` を §9 で作り直す必要は無く、
本 session の §9 R-family から `CharacterPsiDecomposition.ofProjection` で直接供給すればよい。

- ✅ `S11.sOf_memberPsiDecomposition` — `Dmem` 側 (`ψ = 0`) landed。
  ⚠ **map は `τ` でなく coherent extension**。`ψ = 0` では `ofProjection` の義務
  `tau1 (χ − ψ) ∈ ℤ[Irr G]` が `tau1 χ ∈ ℤ[Irr G]` になり、Dade map では**偽**
  (supported lattice 上でしか isometry でない) が、`IsCoherent.extension_mem_ZIrr` そのもの。
  `FamilyBundleDade` の docstring が `decompositionPair` を避ける理由と同じ。
- ✅ `S11.sOf_breakPsiDecomposition` — `Da` 側 (break `ψ` vs anchor `a • χ₁`) landed。一発で通った。
  ⚠ **こちらは `tau1 = τ` でよい**: 義務が `τ(ψ − a·χ₁) ∈ ℤ[Irr G]` で、次数一致ゆえ
  A₀-supported。member 側 (`ψ = 0`、Dade map 不可 → coherent extension) との**非対称性**が
  `FamilyBundleDade` の記述どおりに出る。

⟹ **engine の `Dmem` / `Da` は両方 §9 で揃った**。

#### ✅ 部品が出揃った (2026-07-20) — `CaseAPairBound` producer の残りは組み立てのみ

| 部品 | 宣言 |
|---|---|
| `Dmem` (ψ = 0、map = coherent extension) | `S11.sOf_memberPsiDecomposition` |
| `Da` (break vs anchor、map = τ) | `S11.sOf_breakPsiDecomposition` |
| engine が要求する形への packaging | `S11.sOf_sixTwoDecompositionData` (= `S13.sixTwoDecompositionData` の代替) |
| 結論の `∃ d, χ(1) = q·d ∧ d ≤ u` | `S11.caseA_break_source_degree` |

⚠ **`caseA_break_source_degree` が型仮定ゼロで通ったことが、前 iteration の実測の裏付け**:
`xiOf_H0Cprime_source_apply_one_le_u chars hζ` が書き換え無しで適用できる
(= §13 の `C_eq_cSub_of_noncoherent` 経由が不要)。

⚠ **leaf を 1500 行手前で分割済** (commit 08b3bace4): base 層を
`S11_NineElevenBridgeBase.lean` (261 行) へ。module 名・namespace・宣言名は不変。

#### ✅ 解決 (2026-07-20): τ 2 系統の seam は `congrTau` + `congrMap` で解ける

engine を触らずに済んだ:

- **`S07.OrthonormalCharacterImageFamily.congrTau`** (新設) — image family の τ 輸送。
  τ に触れるのは `image_eq` だけなので **`imageSet` は定義的に不変**、
  `Orthogonal` (imageSet のみで述べられる) はそのまま移る。
  ⟹ `sOf_{member,break}PsiDecomposition` / `sOf_sixTwoDecompositionData` を
  **engine 形で産出**するように変更。
- coherence 側は **`IsCoherent.congrMap` が `.extension` を定義的に保つ**ので、
  `hDtau : … = cohS₂.extension …` の節がそのまま通る。

⚠ **`have` でなく inline で渡す**こと: `IsCoherent` は data なので
`have cohS₂E := cohS₂.congrMap …` にすると `.extension` が opaque になり
`hDtau` が孤立する (1 度踏んだ)。[[lean-instance-defeq-traps]] の let-vs-have と同型。

✅ **`S11.caseA_pairBound` landed** — §13 `nineElevenPairBound` から `hncH0C`/`htype` が
消えた形。

#### ✅ 完了 (2026-07-20): 両分岐を A₀ で回して一度だけ降ろす形に組み替えた

⭐ **`sOf_nineEleven_coherent` の残パラメータは `hAbase` と `hrefuteEq` の 2 つだけ**になった
(`hbound` は `caseA_pairBound` が内部供給、commit 65720e3e4)。

- `S11.sOf_conj_apply_one` — メンバーと共役の次数は等しい (誘導指標ゆえ次数は自然数)。
- ⟹ 降下を `sOf_caseB_coherent_restrict` → **`sOf_coherent_restrict`** に一般化
  (`d`/`hunif` 削除)。(4.7) 評価は 2 次数の一致だけを要求し `η̄ − η` では全メンバーで
  成り立つので、**一様次数の仮説は不要だった**。

⚠ `refine ⟨sOf_coherent_restrict … ?_⟩` にすると残 goal が Type になり `rcases` が Or を
潰せない (`Or.casesOn` は Prop へしか eliminate できない)。`Nonempty` の中で分岐して
`.some` を渡す。

#### ⭐ 完了 (2026-07-20): `hAbase` も discharge — 未完の数学は carrier 1 つだけ

`S11.sOf_degreeSubfamily_coherent_A0` を配線 (commit a1c10b6ed、一発で通った)。
⟹ **`sOf_nineEleven_coherent` が依存する未完の数学は `hrefuteEq` ただ 1 つ**。

他のパラメータは未完の数学ではない:
- `dd` / `hdd` — (8.15) の Dade datum と「それが (4.6) の制限である」という pin
- `h2` — `2 ≤ ncard`。(9.8.d) は**存在しか与えない**ので露出が honest
  (`S15.Hypothesis.sSetIrrDeg_coherent` と同じ流儀)

前提として landed した de-specialization:
`S08.mem_span_scaledDiff_of_mem_zSupportedSpan` の `SibleyDadeHypothesis` 引数は
**元から未使用** (`_hyp`)、台も固定されていたが、証明が使うのは `1 ∉ A₀` だけ。
任意の `A0` に一般化した (呼び出し 1 箇所修正)。

#### ⚠ 着手順 3 の方針変更 — §13 を §9 の系にすると**残件が後退する** (2026-07-20 実測)

当初計画は「§13 側 `coherent_sOf_H0Cprime` を §9 版の系にする」だったが、§13 側を読むと
**§13 の方が残件の縮小が進んでいる**:

| §13 | 残件 |
|---|---|
| `coherent_sOf_H0Cprime_of_equality_refutation` (S13_Orthogonality:1139) | `hbound` + `hrefuteEq` — **本 session の §9 版と同じ構造** |
| `coherent_sOf_H0Cprime_of_sevenEightRefutation` (同 :1173) | **`h78 : NineElevenSevenEightRefutation` だけ** |

§13 は (9.11.2) TI-witness / (9.11.3) count / (9.11.4) Mackey norm / (9.11.6) dichotomy を
既に landing させ、`hrefuteEq` を **(9.11.7)–(9.11.8) の coherent-pair 構成**まで縮めている。
⟹ §13 を §9 の系にすると、この縮小を捨てることになる。

**正しい次の一手は逆向き**: §9 側を同じ残件まで縮める、すなわち
`S13.nineElevenNormBound_of_sevenEightRefutation` (`S11_NineElevenAlphaBound.lean:848`) と
その carrier `NineElevenSevenEightRefutation` (同 :786) を §9 へ降ろす。

実測 (`hyp.*` の使用回数、848–1000 行):
`s11Setup` 56 / `chief` 21 / `base` 18 / `C` 5 / `H0Cprime` 3 / `SOf` 1 / `setup_typeP_eq` 1 /
`H0C` 1 / `C_le_U` 1 — ⚠ **`type_alt` も `params_*` も無い**。
⟹ `caseA_refuter_of_equality_refutation` と同じく**機械的な rename で降りる**見込み
(`hyp.base.tau`/`.A0` はパラメータ化、`mkSection11CharacterData …` → `chars`)。

#### ⚠⚠ 訂正 (2026-07-20): `CaseAEqualityRefutation` に producer は**在る** — 前回の報告は誤り

本 session で「`NineElevenEqualityRefutation` は repo のどこにも producer が無い」と記録したが、
**誤り**。grep パターンを `: NineElevenEqualityRefutation` にしたため、返り型が行頭に来る
`    NineElevenEqualityRefutation hyp caseA :=` を取りこぼしていた。

実際の §13 の鎖は**完結している**:

```
S13.coherent_sOf_H0Cprime                                  (hnc, htype のみ)
 ← coherent_sOf_H0Cprime_of_sevenEightRefutation
     ← nineElevenSevenEightRefutation            (S11_NineElevenPairAdjoin:893)
     ← nineElevenEqualityRefutation_of_sevenEightRefutation (S11_NineElevenAlphaBound:1124)
         ← nineElevenSTwoExtraction / nineElevenNormBound_of_sevenEightRefutation
     ← nineElevenPairBound                       (S11_NineElevenCaseA:436)
```

⟹ §13 の (9.11) は `hnc`/`htype` 以外に**未完の carrier を持たない**。
issue 9083 の Phase B–E は**既に完了している**。

#### ⭐ ⟹ §9 版も完全証明まで行ける — 残る `htype` は全部あの 1 行

3 ファイル (`_AlphaBound` / `_PairAdjoin` / `_CaseA`) の `htype`/`hncH0C` の実質的使用を
実測したところ、**すべて `rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]` の 1 パターン**
= 本 issue で繰り返し見ている `hyp.C = cSub` の辞書同一視。§9 では**定義的に等しい**。

⟹ 残チェーン (`nineElevenSTwoExtraction` / `nineElevenNormBound_of_sevenEightRefutation` /
`nineElevenSevenEightRefutation` / `nineElevenEqualityRefutation_of_sevenEightRefutation`) を
§9 へ降ろせば、**`hrefuteEq` も discharge され (9.11) の §9 版が完全証明になる**
(`hnc` は §13 でもパラメータのまま)。

⚠ 規模: 4 定理 + carrier 1 個。`caseA_refuter_of_equality_refutation` の降ろしと同型の
機械作業だが、`_PairAdjoin` / `_AlphaBound` の本体は長い。

#### 📋 残チェーンの実測マップ (2026-07-20) — 次 session はここから

`hrefuteEq` を discharge するために §9 へ降ろす必要がある producer と規模:

| 降ろす対象 | 現在地 | 規模 | 備考 |
|---|---|---|---|
| `nineElevenSTwoExtraction` | `S11_NineElevenCaseA:1292` | 8 行 | 下の `caseA_sTwo_subset_degreeQaCut` へ委譲するだけ |
| `caseA_sTwo_subset_degreeQaCut` | `S11_NineElevenCaseA:1190` | ~102 行 | 実体 |
| `nineElevenEqualityRefutation_of_sTwoExtraction_normBound` | `S11_NineElevenCaseA:937` | ~40 行 | |
| `nineElevenNormBound_of_sevenEightRefutation` | `S11_NineElevenAlphaBound:848` | ~270 行 | (9.11.4)–(9.11.6) |
| `nineElevenSevenEightRefutation` | `S11_NineElevenPairAdjoin:893` | ~420 行 | (9.11.7)–(9.11.8) |

合計 ~840 行 + carrier 数個 (`NineElevenSTwoExtraction` / `NineElevenNormBound` の §9 形)。
3 ファイル計 3,795 行のうち該当部分。

⚠ **降ろし方は確立済**: `htype`/`hncH0C` は全て `C_eq_cSub_of_noncoherent` の 1 行に消え、
`hyp.base.tau`/`.A0` はパラメータ化、`hyp.s11Setup`/`chief`/`mkSection11CharacterData …` は
`data`/`chief`/`chars` に置換 — `caseA_refuter_of_equality_refutation` と
`CaseASevenEightRefutation` で 2 度実施した手順そのもの。

⚠ **leaf 分割の見込み**: 現在 3 ファイル (261 / 704 / 937 行)。~840 行を足すので
さらに 1〜2 枚切ることになる (1500 trigger)。

#### ⛏ 残り — 本 issue の本体は完了、あとは issue 9083

`hrefuteEq` = `CaseAEqualityRefutation` は **issue 9083 Phase B–E** の内容で、
repo のどこにも producer が無い (本 session の実測)。算術の鎖
`S11.nineElevenCaseA_equality_refutation` は既に §9・型仮定ゼロで landed 済なので、
残るのは「等号配置 → その入力 (`hclass`/`hn`/`hnorm`/`hK₁`/`hK₂`/`hCinf`/`hle`)」の配線。

⟹ **issue 1045 の目的 ((9.11) を §9 レベルで型仮定なしに述べ、型 III/IV 版をその系にする)
のうち、前半は達成**。§13 版を系にする配線 (着手順 3) と型 II instance (着手順 4) が残る。

#### (旧) 残り 2 つ

| param | 状態 |
|---|---|
| `hAbase` (degree-`qa` cut の coherence、**A₀ レベル**) | `sOf_degreeSubfamily_coherent(_restrict)` は A レベル。cut は一様次数 (`qa`) なので `S07.isCoherent_of_supportedSpan_le` で **A → A₀ に持ち上げられる** (§13 `certainTypeSet_isCoherent_A0` と同じ向き)。加えて `2 ≤ ncard` の count は露出のまま |
| `hrefuteEq` (`CaseAEqualityRefutation`) | **本物の未完部分** (issue 9083 Phase B–E)。repo に producer 無し。算術の鎖 `S11.nineElevenCaseA_equality_refutation` は既に §9・型仮定ゼロ |

#### (旧・解決済) A vs A₀ のレベル差 — case A も case B と同じく descent が要る

`caseA_pairBound` は **A₀ レベル** (engine の `hyp` が `h46.dade0` なので、
`inducedKernelFamily_*` の台の事実が `hKsupp` = `(M')^# ⊆ A₀` 経由になる)。
A レベルで engine を回すには `(M')^# ⊆ A` が要るが、**型一様な `A(M)` = `typePACore`
では偽**。⟹ case A も A₀ で回して結果を降ろすのが正しい (case B と同じ形)。

⟹ 次の一手: `sOf_nineEleven_coherent` を「両分岐とも A₀ で回して最後に降ろす」形に
組み替える。`caseA_coherent_sOf_cprime_of_refuter` は `tau`/`A0` が自由なので
A₀ で呼べる。降下は `sOf_caseB_coherent_restrict` を分岐非依存に一般化すればよい。

#### (旧・解決済) engine 呼び出しは τ の形が 2 つあって噛み合わない

`caseA_pairBound` を一通り書いて build したところ、**τ の表記が 2 系統ある**ことが問題になった:

| | τ |
|---|---|
| 本 issue の §9 部品群 (`sOf_memberRFamily` 以下) | `dadeICM h46.dade0 **h46.tau**` (`certainTypeR` が決める) |
| (5.6) engine `coherentDegreeSqNormBound_of_not_coherentW_k` | `dadeICM hyp (hyp.**fullDadeIsometryData hconj**)` (ハードコード) |

`htau` で両者は等しいが**構文的には別**。素朴に `rw [htau] at cohS₂` すると
`cohS₂` が新しい仮説になり、それ以前に作った `hDtau : … = cohS₂.extension …` が
古い方を指して型が合わなくなる (`IsCoherent.extension` は τ に依存しないのに、
transport がそれを見せない)。`hS₁coh` を書き換える版も、結論が `hS₁coh.extension` を
含むので依存 rewrite になって同じ壁。

⟹ **設計として決める必要がある** (次 iteration の最初の仕事):
- (a) `sOf_memberRFamily` 以下を engine 形 (`fullDadeIsometryData hconj`) で建て直す
  — `certainTypeR` の出力を一度だけ `htau ▸` で運ぶ。`imageSet` の `rfl` 還元
  (`_imageSet_of_irr`/`_of_col`) が壊れないかが焦点。
- (b) engine 側に τ をパラメータ化した variant を用意する
  (`hyp.fullDadeIsometryData hconj` を任意の `FullDadeIsometryData` に緩める)。
  §5 の `dadeIntegralCharacterMap_inner_eq_on_supported_span_of_data` が
  「isometry data に依らない」ことを既に示しているので、engine の証明も通る見込み。

⚠ (b) の方が筋が良さそう (下流全部に効く) が、engine 本体に触るので影響範囲を先に測ること。

#### (旧) 次の一手: engine 呼び出し本体 = `CaseAPairBound` producer

`S08.coherentDegreeSqNormBound_of_not_coherentW_k` の結論は `∑ (deg i)²/mc i ≤ 2a` なので、
`CaseAPairBound` の `sumnS F ≤ 2q²a·d` へは §13 と同じ rescale
(`sumnS_image_eq_anchorSq_mul`) を通す。残る組み立ての中身:

- `s` / `χmem` / `deg` / `mc` / `i₁` を `F ⊆ S₂` から立てる (§13 と同形)
- 格子生成の 2 仮説 `hSgen` / `hgen`
- 源次数 `d ≤ u` の供給 (§13 は `caseA_source_degree_dvd_a` + (9.11.1) preamble)

⟹ §13 `nineElevenPairBound` の本体を、`Dmem`/`Da` だけ §9 版に差し替えて写す作業。

#### (旧・撤回) 真の作業は `S13.sixTwoDecompositionData` の §9 化。実測すると、その μ-grid `params`
(`hmu`/`hδpm`/`hδj`/`hzS`/`hz1`) が効くのは **可約メンバー分岐**
(`sixTwoMemberDatum_of_reducible_member` / `sixTwoDecompositionData_of_reducible_break`) だけで、
これは **本 session で作った `S11.sOf_memberRFamily` (可約 = §6 `certainTypeR`) が果たす役割と同じ**。
⟹ case B の `hRorth` でやった置換を (5.6) engine に対して繰り返す作業になる。規模は大きい。

#### (旧) 次の一手: `CaseAPairBound` の producer を §9 へ (型仮定が消える)

`S13.nineElevenPairBound` (`S11_NineElevenCaseA.lean:436`) が §13 版 producer。
`hncH0C` と `htype : IsTypeIII ∨ IsTypeIV` を取るが、**実測すると使用箇所は 1 行だけ**:

```
rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]
```

= 本 issue で繰り返し見ている **`hyp.C = cSub` の辞書同一視**そのもの。
§9 では `chars.C` が `cSub data chief` **定義的に等しい**ので、この rw ごと消える。
⟹ **`CaseAPairBound` の producer は型仮定ゼロで降りる**見込み。

#### ⚠ `CaseAEqualityRefutation` は repo のどこにも producer が無い (= 本物の未完部分)

grep 実測: `NineElevenEqualityRefutation` は `caseA_refuter_of_equality_refutation` の
**引数としてしか現れない**。issue 9083 の Phase B–E ((9.11.2) の `u ≤ a²` /
(9.11.3) の class 方程式 / (9.11.4) の Mackey norm / (9.11.5)–(9.11.8)) が残っている。

ただし**算術の鎖は既に landed かつ §9 レベル**:
`S11.nineElevenCaseA_equality_refutation` (`S11_NineElevenCoherence.lean:1004`) は
`data`/`chief`/`chars` の上で述べられており**型仮定ゼロ**。
残るのは「等号配置 → その定理の入力 (`hclass`/`hn`/`hnorm`/`hK₁`/`hK₂`/`hCinf`/`hle`)」の
配線であって、算術そのものではない。

#### (旧) 次の一手: `hArefute` の §9 化

`hArefute` は §13 では `S11.caseA_refuter_of_equality_refutation`
(`S11_NineElevenCaseA.lean:254`) が供給していて、そこで**2 つの carrier に落ちている**:

- `NineElevenPairBound hyp caseA` — (5.6) の pair-bound 束
- `NineElevenEqualityRefutation hyp caseA` — (9.11.2)–(9.11.8) の等号配置の否定

本体の議論は (9.11.1) の squeeze で、使っているのは
`hyp.base.tau` / `hyp.base.A0` (**パラメータ化可能**) と
`hyp.s11Setup` → `data` / `hyp.chief` → `chief` / `hyp.C` → `cSub data chief` /
`hyp.H0Cprime` → `chief.H0 ⊔ cprimeSub data chief` という**packaging の別名だけ**。
⟹ case A の降ろしと同型の機械作業になる見込み。

⚠ ただし **2 つの carrier 自体が `S13.Hypothesis` で添字づけられている**ので、
先に carrier の §9 版 (`data`/`chief`/`chars` 上) を作る必要がある。
そこが本 issue に残る最後の実質作業。

#### (旧) 次の一手: `hAbase` を `sOf_degreeSubfamily_coherent` から供給する

両者は**同じ台 (`supportInSubgroup A M`)** になったので、残る差は τ だけ:

- `sOf_degreeSubfamily_coherent` の τ = `dadeICM dd.dade (dd.dade.fullDadeIsometryData dd.hconj)`
- (9.11) の τ = `dadeICM (h46.dade0.restrict …) (h46.tau.restrict …)`

⚠ **鍵**: `dadeIntegralCharacterMap_apply_of_support` は supported な引数上で
`hyp.dadeMap` に落ち、**isometry data に依らない**
(`dadeIntegralCharacterMap_inner_eq_on_supported_span_of_data` の証明がその実演)。
⟹ `dd.dade = h46.dade0.restrict Set.subset_union_left hAnorm` の pin さえ取れば、
2 つの τ は A-supported 上で一致し `IsCoherent.congrMap` で閉じる。
`fullDadeIsometryData` 同士の一致は**要らない**。

⟹ 作業: (a) 上記 τ-agreement 補題、(b) `hAbase` supplier、(c) 残りは `hArefute` のみ。

#### (旧) 次の一手: `sOf_nineEleven_coherent` を A-level に述べ直す

現状の `sOf_nineEleven_coherent` は A₀ 上で述べてあり、case A の `hAbase` を A₀ 側で要求している。
A-level に直せば **`hAbase` は `sOf_degreeSubfamily_coherent` の drop-in になる** (両方 A 上)。
必要な追加入力は `dd : DadeSupportHypothesisData M A` と
`hdd : dd.dade = h46.dade0.restrict Set.subset_union_left hAnorm` の pin
(`typePACore_toHypothesis46_core` 側では `rfl` 相当のはず — 未確認)。

⟹ 残るのは `hArefute` (= §9 chain 本体の `S13.Hypothesis` 降ろし) だけになる見込み。

#### (解決済の記録) 当初の見立て — `hAbase` は `sOf_degreeSubfamily_coherent` の drop-in にならない

- `sOf_degreeSubfamily_coherent` (本 issue で landed) の結論は
  `IsCoherent (inducedNonKernelFamily_subcoherent …).tau {cut} (supportInSubgroup **A** M)`。
  その τ は `dadeIntegralCharacterMap d.dade (d.dade.fullDadeIsometryData d.hconj)` で
  **`d : DadeSupportHypothesisData M A`** = **A 上の Dade**。
- 一方 case B は `certainTypeR` 由来で `dadeIntegralCharacterMap h46.dade0 h46.tau` =
  **A₀ = A ∪ V^M 上の Dade** に固定される。
- (4.6) の構成では `dade := dade0.restrict Set.subset_union_left hAnorm` なので
  **A-Dade は A₀-Dade の制限**。A-supported な関数の上では一致するが、
  `IntegralCharacterMap` としては別物。
- ⟹ 2 分岐を同じ (τ, A₀) で合成するために、`hAbase` は **A₀ 側**で要求してある。
  A 側の `sOf_degreeSubfamily_coherent` から A₀ 側へ移す補題 (restrict と
  `IsCoherent` の台拡大) が次の一手。

書籍側の対応: (9.5) は「τ = (A(M), M, G) に関する Dade isometry」と書き、(4.6.e) は
「A₀ に関する τ」と書く。制限関係ゆえ書籍は区別していないが、形式化では明示的な橋が要る。

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

#### ⭐⭐ 完了 (2026-07-20): (9.11) の §9 版が **case (9.7.a) 込みで完全証明**になった

残っていた最後の producer `S13.nineElevenSevenEightRefutation` (~420 行) を §9 へ降ろし、
`S11.caseA_sevenEightRefutation` として landed。これで `hrefuteEq` が discharge され、
新しい endpoint **`S11.sOf_nineEleven_coherent_of_count`** が立った:

```
sOf_nineEleven_coherent_of_count          ⭐ (9.11) §9 版・型仮定ゼロ
 ← caseA_equalityRefutation                (= hrefuteEq、issue 9083 Phase B–E)
     ← caseA_sTwoExtraction                 (既存)
     ← caseA_normBound                      (新)
         ← caseA_normBound_of_sevenEightRefutation  (前 commit)
         ← caseA_sevenEightRefutation                (本 commit ⭐)
```

残パラメータは `dd`/`hdd` ((8.15) Dade datum の pin) と `h2` (`2 ≤ ncard`) のみ。
どちらも未完の数学ではない ((9.8.d) は存在しか与えないので `h2` の露出は honest で、
`S15.Hypothesis.sSetIrrDeg_coherent` と同じ流儀)。全宣言 axiom-clean、AxiomsCheck 登録済。

**降ろし方は予告どおり**: `htype`/`hncH0C` の実質的使用は `𝒮₄ ⊆ 𝒮₃` のための
`H₀C′ ≤ H₀C` 1 箇所だけで、§9 では `chars.C` が `cSub data chief` と定義的に等しいので消えた。

新規に要した §9 部品 2 本 (`S11_NineElevenRFamily` へ):
- `sOf_coherent_extension_eq_sum_memberRFamily` — (5.5) の coherent extension 版 (stratum-generic)
- `sOf_coherent_extension_cross_orthogonal` — Coq `coherent_ortho`

**設計変更 1 件**: `CaseASevenEightRefutation` に (9.11.4) の norm 値 `N` とその Mackey 等式を
パラメータで追加した。§13 は `𝒮₄ ≠ ∅` を出すためだけに `γ = Ind_{HU₁}^M 1` の文脈を
**2 度目に丸ごと組み直している** (`caseA_nineElevenFour_norm_inputs` ~130 行) が、§9 では唯一の
consumer `caseA_normBound_of_sevenEightRefutation` が呼び出し地点で既に `N`/`hNu` を持っている。
書籍でも (9.11.7) は (9.11.4)–(9.11.6) の文脈の内側の議論なので、渡す方が忠実。

**再層化 1 件 (新 leaf)**: `S11_NineElevenPairAdjoin.lean` (namespace S13) の
`UnionPair` 節 (Pf (5.6.3) の union-pair coherent extension) と `ProjectionBudget` 節
((9.11.7)–(9.11.8) の射影予算) は **群論的構造を一切参照しない** (`{L Γ'}` の直交族と
`IntegralCharacterMap` と整数性だけ) のに §13 の closure に在り、§9 から使えなかった。
新 leaf `OddOrder/Peterfalvi/S07_UnionPairBridge.lean` (namespace S07、640 行) へ移設。
呼び出し 4 箇所 (§13 の Discharge + §15 の S/T ミラー 2 本) と AxiomsCheck 3 件を修飾し直した。
`S11_NineElevenPairAdjoin.lean` は 1314 → 719 行。

⚠ 新 leaf 2 本 (`S07_UnionPairBridge` / 前 commit の `S11_NineElevenCaseAResidual`) を
`OddOrder.lean` に配線した (issue 0135 の規律)。到達性 851/851、orphan ゼロ。
full build green (4566 jobs)、AxiomsCheck OK、sorry 14 (非退行 — 全て他レーン所管の Appendices/BG)。

⟹ 着手順の 1・2 は完了。残りは **3 (§13 側 `coherent_sOf_H0Cprime` を §9 版の系にする)** と
**4 (型 II instance)**。

#### ⭐ 完了 (2026-07-20): 着手順 4 (**型 II instance**) — (9.11) が型 II で使えるようになった

`S11.typeII_sOf_nineEleven_coherent`。実測すると **§9 側に足りなかったのは carrier の producer
だけ**で、(9.11) の中身は既に型仮定ゼロだった:

| 書籍 | repo の状態 | 追加したもの |
|---|---|---|
| (9.2) Hypothesis | `TypesIIIIIIVSetup` は `type_alt : IsTypeII ∨ III ∨ IV` で**既に型一様**。だが producer が `S12.Hypothesis.toTypesIIIIIIVSetup` (htype = III ∨ IV) しか無かった | `GroupTheory.typePNontrivialCore_of_isTypeII` / `_of_isTypeIIorIIIorIV` (`TypeIIData.common` を transfer するだけ) + `S11.typesIIIIIIVSetup_of_type_alt` / `_of_isTypeII` |
| (9.4) chief factor | `exists_chiefFactorData` は**元から型仮定ゼロ** (`ChiefFactorData.typeIII_IV_p_eq_W2` は条件付き field なので型 II で無害) | — |
| (9.5) character data | `S12.Hypothesis.mkSection11CharacterData` のみ = §10 packaging 経由 | `S11.mkSection11CharacterData` (§9 版。`u = |Ū|` は pin 済、`C`/`U'`/`C'`/`𝒳`/`𝒮` は genuine、自由なのは caller が渡す Dade map と (9.11) が明示パラメータで取る 2 placeholder のみ) |
| (9.11) | `sOf_nineEleven_coherent_of_count` (本 session) | — (そのまま instantiate) |

⟹ 型 II の (9.11) は上 3 つを繋ぐだけで立った。残りの入力は型 III/IV 経路と**完全に同じ**
((8.15)/(4.6) の Dade データ `h46`/`dd`/`hdd` とその pin + `h2`)。

⟹ **issue 9163 §3 項目 3 ((9.11) M 側の type-II 拡張) は完了**。

#### ⭐ 完了 (2026-07-20): `h2` (`2 ≤ ncard`) も discharge — 残パラメータは (8.15) の Dade データだけ

`S11.irrCut_two_le_ncard` + `S11.caseA_irrCut_two_le_ncard`。⚠ **本 issue が繰り返し
「honest な露出」と記録してきた `h2` は、実は露出不要だった**:

- 次数 cut は共役閉 (`irrCut_conjClosed`) で、奇数位数ゆえ実指標が無い
  (`S08.inducedKernelFamily_hasNoRealCharacters`) ⟹ `φ ≠ φ̄` が常に成り立つ。
  **共役閉族では「非空」と「2 元以上」は同値**。
- しかも非空自体が (9.8.d) の厳密 count から出る: 下界 `(p−1)·[U:U′]` が正
  (`caseA_character_count_exact`、§9 level)、`sOf_antitone` で `H₀U′ → H₀C′` に降ろす。

これは **§13 が `caseA_coherent_sOf_H0Cprime_of_refuter` の中でやっているのと同じ経路**で、
全ステップ §9 level。§13 が存在 witness だけで base coherence を得るのに §9 の (8.15.3)+(5.7)
経路が `2 ≤ ncard` を要求する、という差は見かけだけだった。

⟹ endpoint を改名・整理: `sOf_nineEleven_coherent_of_count` → **`S11.nineEleven_coherent`**、
`typeII_sOf_nineEleven_coherent` → **`S11.typeII_nineEleven_coherent`**。
**残るパラメータは Hypothesis (8.15) そのものだけ** — Dade datum `dd` と pin `hdd`、
および `h46` と書籍の `K = M′` / `H = M_σ` / `τ` を名指しする pin (`hKeq`/`hHeq`/`hconj`/`htau`)。
未完の数学はゼロ。

#### 📋 着手順 3 (§13 を §9 の系にする) の seam 実測 (2026-07-20) — 次 session はここから

`h2` が消えたので「§13 を §9 の系にすると残件が後退する」という 2026-07-20 前半の判断は**失効**。
改めて seam を実測した結果、**τ と A₀ は定義的に一致する**:

| §13 | §9 | 判定 |
|---|---|---|
| `hyp.base.tau` = `dadeICM hyp.dadeData.dade (…fullDadeIsometryData hyp.hconj)` (S12/Hypothesis.lean:405) | `dadeICM h46.dade0 h46.tau` with `h46 = hyp.base.toHypothesis46 hG hG.odd` (同 :1367-1368 が `dade0 := hyp.dadeData.dade`, `tau := …fullDadeIsometryData hyp.hconj`) | ✅ **rfl** (`htau` も rfl) |
| `hyp.base.A0` = `supportInSubgroup (typePA0 M typeP) M` (同 :390) | `supportInSubgroup (A ∪ conjClassSetIn M h46.tic.V) M`、`A = typePA M typeP`、`tic_V := rfl` | ✅ ほぼ rfl (`typePA0 = typePA ∪ V^M` の展開のみ) |
| `hKsupp` | `hyp.base.mderivSharp_subset_A0` | ✅ 既存 |
| `hVsub` | `typePData_typePV_not_mem_derived` | ✅ 既存 |
| `hKeq` / `hHeq` | `h46.K` / `h46.subH` は `toCertainTypeHypothesis` 由来。型 III/IV では `M_σ = M′` ゆえ両方 `M′` に落ちるはず | ⛏ 要確認 |
| `dd` / `hdd` | ⚠ **本物の残件**。`hyp.base.dadeData : DadeSupportHypothesisData M (typePA0 …)` だが §9 が要るのは **`A = typePA` 上の制限版**。`normalizer_eq` と `H_eq_ftSupportKernel` を制限先で立て直す必要がある | ⛏ |

⟹ 手順:
1. **Stage 1 (無リスク)**: `sOf_nineEleven_coherent` の内部 `hA0` ブロック (A₀ level の結論) を
   独立定理 `sOf_nineEleven_coherent_A0` として切り出す。§13 の結論は A₀ level なので、系にするには
   A₀ 版が要る (`nineEleven_coherent` は A level)。
2. **Stage 2**: `hKeq`/`hHeq` を実測して埋める。
3. **Stage 3**: `A = typePA` 上の `DadeSupportHypothesisData` を (8.15) から構成 (制限版)。
4. **Stage 4**: `S13.coherent_sOf_H0Cprime` を系に置換。`hnc`/`htype` は**未使用パラメータとして残す**
   (signature 不変 ⟹ §13/§15 の下流は無変更)。その後 §13 の重複チェーン
   (`S11_NineElevenCaseA` / `_AlphaBound` / `_PairAdjoin` の (9.11) 部分、計 ~3.8k 行) が dead code
   になるので削除。

#### ⭐⭐ 完了 (2026-07-20): 着手順 3 — **§13 の (9.11) が §9 の系になった**

`S13.coherent_sOf_H0Cprime_of_section9` を新設し、`S13.coherent_sOf_H0Cprime` の証明を
**`S11.nineEleven_coherent_A0` への 1 行の委譲**に置換 (signature 不変 ⟹ 下流無変更)。

4 stage すべて landed:

| Stage | 内容 |
|---|---|
| 1 | `S11.sOf_nineEleven_coherent_A0` / `S11.nineEleven_coherent_A0` — §13 の結論は A₀ level なので A₀ 版の endpoint を切り出した |
| 2 | `S10.inducedNonKernelFamily_mono` — `hHeq` (等式) → `hHle` (包含) へ緩和。§13 の `h46.subH` は `M_σ` でなく `M′` ((4.6.c) を `H := K` で立てている) なので等式は成り立たない |
| 3 | `S10.DadeSupportHypothesisData.restrict` + `ftSupportKernel_congr_of_subset` — §10 は datum を `A₀(M)` 上に持ち、§9 は `A(M)` 上のものを要求する |
| 4 | 配線。`τ`/`A₀` は **rfl**、`hKeq` は `huSub_eq_derivedInG_subgroupOf`、`hHle` は `Msigma_le_derived`、`hdd` は `rfl` |

⚠ **`hnc`/`htype` の唯一の用途は packaging の辞書 `hyp.C = cSub s11Setup chief`**
(`C_eq_cSub_of_noncoherent`)。本 issue が §13 の producer を降ろすたびに底で見つけていた
「1 行の辞書」がそのまま最後に残った形で、§9 の議論自体は型を一度も見ない。

⟹ **issue 1045 の完了条件を満たした**: (9.11) は `TypesIIIIIIVSetup` + `ChiefFactorData` +
`Section11CharacterData` の上で型仮定なしに述べられ、型 III/IV 版 (§13 packaging) はその系。
型 II 版も同様 (`S11.typeII_nineEleven_coherent`)。

### ⛏ 残: §13 の重複チェーンの棚卸し

`coherent_sOf_H0Cprime` が §9 経由になったので、旧 §13 チェーン
(`coherent_sOf_H0Cprime_of_sevenEightRefutation` / `_of_equality_refutation` /
`nineElevenSevenEightRefutation` / `nineElevenEqualityRefutation_of_sevenEightRefutation` /
`nineElevenPairBound` と `S11_NineElevenCaseA` / `_AlphaBound` / `_PairAdjoin` の該当部分、
計 ~3.8k 行) は **同じ命題の 2 本目の証明**になった。削除の可否は
**宣言ごとに外部 consumer を grep してから**判断する (§15 の S/T ミラーが実体を cite している
可能性あり — docstring 参照だけなら削除可)。⚠ 本 session では実施しない。

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

## 🔍 hub 内容監査 (2026-07-20 21:45 tick, merge 9b53260a3) — **健全。STOP なし**

`3b98365cb` / `c28cd6ad1` の内容を doneness 基準 (sorry 数でなく「hard content を実証明したか /
構成不能な仮説へ hoist していないか」) で独立監査した。

**判定: genuine。scaffold 詐称なし・axiom 0・sorry 0・signature 退行なし。**

### 実証明であることの確認

- **`caseA_sThree_coherent`** (`S11_NineElevenCaseAResidual.lean:64-149`) — τ₃ の `Nonempty
  (IsCoherent …)` を**仮定でなく生成**している。(5.7) engine `S07.uniform_degree_coherence_of_
  families` の **14 個の義務をすべて discharge** した上で適用。pivot partner は `χ₀.conj` で、
  `η₂ ≠ η₁` は奇数位数由来の `inducedKernelFamily_hasNoRealCharacters` から導出
  (`2 ≤ ncard` のような仮説を密輸していない)。`IsCoherent` は等長性・τ との一致・`ZIrr` codomain・
  非零 span を要求する**実構造**で、自明には inhabit できない。
- **`caseA_normBound_of_sevenEightRefutation`** (`:167-403`) — **norm bound は導出**。
  γ = `Ind_{H·U₁}^M 1` は TI-witness から**構成**、ψ₁ は (9.8.d) の count 非零から**抽出**、
  `N·u = (a+1)u + (q−1)a²` は `‖α‖² = ‖γ‖² + 1` と Mackey norm から**算出**、
  最後は Bessel count で `|𝒮₄| ≤ N`。posited ではない。
- **free field に hard content は乗っていない**。`Section11CharacterData` の opaque field のうち
  新定理が触るのは `chars.u` だけで、それは `u_eq_card_quotient` で pin 済。
  `chars.tau` / `chars.H0CprimeSupport` は使っていない (τ は `h46.dade0`、A₀ は明示の
  `supportInSubgroup …`)。
- **「type 仮説なし」は検証して真**。`Section11CharacterData.C` が `cSub data chief` と
  **定義的に等しい** (`ChiefFactorCore.lean:647`) ことに乗っている。⚠ setup は書籍 Hyp (9.2) の
  `type_alt : IsTypeII ∨ IsTypeIII ∨ IsTypeIV` を依然担いでおり、外れたのは III∨IV の**制限**
  — 意図した一般化そのもの。
- **Bessel 補題の §13→§07 移設は pure**。両版を抽出して diff → **91 行 byte-identical**
  (binder・証明スクリプトまで同一)。caller 3 箇所 + AxiomsCheck も追従、`S13.card_le` の残存 0。

### 進捗の正確な言い方 (⚠ hub/レーンともここを誤読しないこと)

> **§9 の (9.11) case-(a) 鎖は、開いた carrier がちょうど 1 本 — `CaseASevenEightRefutation` —
> と §9 dictionary パラメータに還元された。§9 の閉じた定理にはまだなっておらず、
> issue 1045 の動機である type-II 拡張には到達していない。**

- `h78 : CaseASevenEightRefutation` は**構成可能性が高い**: §13 側の対応物
  `S13.nineElevenSevenEightRefutation` (`S11_NineElevenPairAdjoin.lean:893`) が
  **sorry-free で証明済** (~420 行、projection-budget 論法)。その証明が使う `hncH0C`/`htype` は
  4 箇所だけで、**4 つとも type-free な §9 counterpart が既にある**
  (`caseA_nineElevenTwo_tiWitness` / `caseA_two_summand_inertia_inputs` /
  `caseA_nineElevenThree_count_inputs` / `C_eq_cSub_of_noncoherent` は §9 で定義的)。
  ⟹ **descent 作業であって未解決数学ではない**。現時点で producer は無い
  (`CaseASevenEightRefutation` の grep hit は def と本仮説の 2 件のみ)。
- §9 dictionary 仮説 (`hKeq`/`hconj46`/`htau`/`hKsupp`/`hVsub`) は本 merge で**新設されたものではなく**、
  既存の `sOf_memberRFamily` / `caseA_pairBound` / `sOf_nineEleven_coherent` が既に担いでいる束。
  どの call site でも discharge されていないのは、`sOf_nineEleven_coherent` 自体の consumer が 0
  (FT の live path は依然 §13 の `coherent_sOf_H0Cprime`) だから — 本 merge 以前からの状態。

⟹ **次の自然な frontier = `CaseASevenEightRefutation` の §9 producer** (§13 の証明を
type-free counterpart 4 本に載せ替える descent)。これを閉じると case-(a) 鎖が §9 で閉じる。

### 些末

- `S11_NineElevenCaseAResidual.lean:404-405` に空行が 2 つ連続 (`end` の直前)。cosmetic。
