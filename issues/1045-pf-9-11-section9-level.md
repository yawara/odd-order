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
