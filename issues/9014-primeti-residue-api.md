---
id: 9014
slug: primeti-residue-api
title: "shared-infra claim: prime-TI residue API (primeTIred/prTIres_irr_cases) — §13 μ_j machinery + (13.3) sS1S の共通基盤"
created: 2026-07-06
---

# shared-infra claim: prime-TI residue API (primeTIred/prTIres_irr_cases) — §13 μ_j machinery + (13.3) sS1S の共通基盤

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## claim (shared infra, lane b, 2026-07-06)

**mathcomp prime-TI residue theory の port** — repo 未形式化と精密確認 (issue 2035 #7)。§13 の
μ_j machinery + (13.3) `induce_H_mem_zSpan_S` (sS1S / Pf (1.5.a)) の共通基盤。全レーンは着手前に本 issue を scan。

## 対象 API (mathcomp character library / Coq PFsection*)

- **`primeTIred`** (`mu_ : Fin p → ClassFunction S ℂ`): prime-TI subgroup `W`(≤ S) の residue reducible
  characters。`cfInd_prTIres` (誘導公式)。
- **`prTIres_irr_cases`**: prime-TI residue の constituent 分類 (各 `Ind_{PU}^S`-constituent は
  `mu_`-type か `𝒮 ∩ Irr S` か)。
- Coq 出典: `coq/theories/PFsection13.v:401-428` (`S1cases`) + mathcomp `character`/`PsGroup` の
  `primeTIhypothesis`/`primeTIres` 系。

## 建設順 (issue 2035 #7)

1. prime-TI setup + `primeTIred` core + reducibility + `prTIres_irr_cases` [substantial、~2-3 session]。
2. forward `FTseqInd_TIred` (mu_j ∈ 𝒮) [~0.5]。
3. `S1cases` dichotomy assembly [~1]。
4. `sS1S` wrapper (S15 の induce_H_mem_zSpan_S を close) [~1h]。

## 配置

新 shared leaf `OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean` (consumer が他レーンでも
in-scope、territorial なのは所有 file のみ)。

## 完了条件

`induce_H_mem_zSpan_S` (S15:629) が本 API から honest に close され、§13 μ_j machinery も cite 可能に。

## 🧭 HUB 統合注記 (2026-07-06, 9014 番号衝突の consolidation)

hub も独立に同基盤の claim (旧 `9014-prime-ti-reducible-coherence.md`) を起票していたが、**本 issue
(b 版) を canonical として統合・旧 hub 版は削除**。b 版が (i) 配置 = RepTheory shared leaf として正確
(prime-TI residue = mathcomp character port ゆえ汎用 RepTheory; hub 旧案の Pf §3/§4 より適切)、(ii)
owner = lane b (ユーザー 2026-07-06 が CLAUDE.md 例として prime-TI port を挙げ b が claim = 承認済)、
(iii) build 計画が具体的、ゆえ。

**⟹ consumer 追記 (hub)**: 本 API の consumer は **b (13.3 `sS1S`/§13 μ_j) だけでなく a も** —
lane a の issue 1017 RE-DIAGNOSIS で **(10.7) `typeII_derived_frobenius` (Coq `Frob_der1_type2`,
PFsection10.v:549-658) が同じ prime-TI 機構 (`primeTIred`/`cyclicTIiso`/`uniform_prTIred_coherent`) に
gated** と確定済。⟹ **a は本 leaf を cite** (10.7)→(10.8) char capstone に、prime-TI core を**再構築しない**
(重複回避)。owner=b が build、a は sorried-cite で並行。hub は a/b の prime-TI leaf 重複を各 tick で監視。
## 進捗 (session 1, 2026-07-06, lane b) — FOUNDATION landed

新 leaf `OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean` を作成。`lake build OddOrder`
GREEN (3930 jobs, 新 axiom なし)。real sorry = **1** (`prTIres_irr_cases` body のみ)。

**設計 (repo idiom = `S06.Hypothesis46` / `SignedIrreducibleDifferenceFamily` に整合)**: `mu2_ i j`
の構成は mathcomp `cyclicTIiso` stack 全体に載る (repo 未 port) ため、residue grid を
`structure PrimeTIResidueData S PU q p` の **field として posit** し (各 field は `primeTIirr_spec` /
`prTIres_spec` が *証明する* 命題)、その上に derived API を **sorry-free** で構築:

- fields: `mu2 : Fin q → Fin p → IrreducibleCharacter S`, `chi : Fin p → IrreducibleCharacter ↥PU`,
  `mu2_orthonormal` (=`cfdot_prTIirr`), `chi_res` (=`cfRes_prTIirr`@i=0), `ind_chi` (=`cfInd_prTIres`),
  `chi_zero` (=`prTIres0`)。
- derived (sorry-free): `primeTIred` (=`μ_j := ∑_i mu2 i j`), `cfInd_prTIres`, `prTIred_char`,
  `cfdot_prTIirr_red`, `cfdot_prTIred`, `cfnorm_prTIred`, `prTIred_neq0`, `prTIred_not_irr`,
  `prTIred_inj`, `prTIres0`, `prTIred_mem_ZIrr`。
- **isolated deep sorry**: `prTIres_irr_cases` (Peterfalvi (4.5.b), Coq PFsection4.v:620-665) —
  inertia `'I_S[θ] = PU` の p-group fixed-point count (`pgroup_fix_mod`)。statement + docstring 完備。

**継続 outline (multi-session)**:

1. **`prTIres_irr_cases` の body を close** — 必要: (a) inertia group `'I_S[θ]` の repo API
   (`OddOrder/.../Inertia.lean` 既存 `inertia_Ind_irr` 系 + 未 port の `inertia_Ind_irr` 十分条件),
   (b) `W1`-action on `Irr(PU)` の `p`-group fixed-point count (mathcomp `sylow.pgroup_fix_mod` 相当;
   repo `PGroupFixedVector.lean` が近い), (c) `Ind θ` irreducible ⟸ `'I_S[θ] = PU` (Clifford
   `InducedIrreducible.lean`)。field 版として posit も可 (mathcomp が theorem として持つため honest)。
2. **`PrimeTIResidueData` の constructor** — genuine `primeTI_hypothesis` (= (4.2)/(13.2), 既存
   `S05.TICyclicHypothesis` + `S = PU ⋊ W1` prime-action) から。`cyclicTIiso` + `primeTIirr_spec`
   (Coq PFsection4.v:288 Theorem 4.3) の Lean port が要 [substantial, ~2-3 session]。既存
   `S06.Hypothesis.columnFamily : SignedIrreducibleDifferenceFamily L (Nat.card W1)` が column
   `i ↦ mu2 i j` に一致するので、これを p 本束ねて grid 化するのが最短路。
3. **`FTseqInd_TIred` (mu_j ∈ 𝒮)** — `S1mu` (PFsection13.v:391) 相当: `μ_j = Ind(chi_j)` かつ
   `chi_j` の kernel が `P` を含まない (j≠0) ゆえ `μ_j ∈ seqIndD H S P 1`。必要: `cfker_prTIres`
   (j≠0 ⟹ ¬(H ⊆ ker chi_j), Coq PFsection4.v:801) を field 追加 + `seqIndD`/`calS1` の repo 対応物。
4. **`S1cases` dichotomy assembly** (PFsection13.v:401-428) — 上記 + `prTIres_irr_cases` を組む。
   `'Z[calSirr]` = `zSpan (calS ∩ irr S)`。
5. **`sS1S` wrapper → `induce_H_mem_zSpan_S` (S15:629) close** — `calS1 ⊆ 'Z[calS]`。

**faithful verdict**: posit した field 群は `S1cases`/`S1mu`/`sS1S` が実際に consume する mathcomp
lemma (`primeTIred`/`cfInd_prTIres`/`prTIres_irr_cases`/`cfdot_prTIred`/`prTIred_char`) と 1:1 対応。
唯一の残欠 `cfker_prTIres` (継続 #3 で field 追加) を除き、setup は S1cases の needs に忠実。

## 進捗 (session 2, 2026-07-06, lane b) — DOWNSTREAM: family `calS` + `FTseqInd_TIred` + `S1cases`

継続 outline #3/#4 を landing。`lake build OddOrder` GREEN、新 axiom なし、**net real sorry = ±0**
(依然 `prTIres_irr_cases` の 1 個のみ; 新規宣言は全て sorry-free)。

**`PrimeTIResidueData` に 2 field 追加** (どちらも genuine mathcomp theorem ゆえ honest posit):

- `P : Subgroup ↥PU` — Sylow `p`-subgroup (`= S_F` を PU 内で realise)、`seqIndD PU S P 1` の
  kernel 条件を担う。継続 outline は「`H`」と書いていたが正しくは PU 内の `P`。
- `cfker_prTIres : ∀ j, j ≠ 0 → ¬(P ⊆ characterKernel (chi j))` (Coq `PFsection4.v:801`) — j≠0 の
  residue が `P`-nonlinear。`chi_zero` (j=0 は trivial=full kernel) と対になる。

**新 derived 宣言 (全 sorry-free、`PrimeTIResidueData` 相対)**:

- `calS : Set (ClassFunction S ℂ)` = `{Ind_{PU}^S ξ | ξ ∈ Irr(PU), P ⊄ ker ξ}` (Coq `seqIndD PU S P 1`)
  + `mem_calS` iff。**repo に generic `seqIndD` は無く** (S11 `sSet` は §9 specific instance) 本 leaf で
  `sSet` idiom に沿い定義。
- `induce_mem_calS (θ) (P⊄ker θ) : Ind_{PU}^S θ ∈ calS` — witness `ξ = θ`。
- `FTseqInd_TIred (j≠0) : primeTIred D j ∈ calS` (Coq `S1mu`, PFsection13.v:391) — `cfInd_prTIres` +
  `cfker_prTIres`。
- `S1cases (θ) (P⊄ker θ) : (∃ j≠0, Ind θ = μ_j) ∨ (IsIrreducibleCharacter (Ind θ) ∧ Ind θ ∈ calS)`
  (Coq PFsection13.v:401-428) — `prTIres_irr_cases` を consume。residue branch で `j≠0` は
  `chi_zero`+`characterKernel_trivialClassFunction`+`hθP` から。
- `induce_mem_zSpan_calS (θ) (P⊄ker θ) : Ind_{PU}^S θ ∈ zSpan calS` — **PU-level `sS1S` engine**。
  両 branch とも `calS` の generator に落ちる (`FTseqInd_TIred` / `induce_mem_calS`) ので単一 generator。

**⚠ 設計上の重要注記 (PU-level vs H-level; S15 が要する差分)**: Coq の本物の `S1cases`/`sS1S` は
`calS1 = seqIndD H S P 1` (**smaller** group `H = PC ⊊ PU` から誘導) を対象にし、`Ind_H^S θ` を
`calS = seqIndD PU S P 1` (PU から誘導) の要素に**分類**する — induction source が違うため dichotomy が
本質的に必要。本 session が landing した `S1cases`/`induce_mem_zSpan_calS` は **PU-level 版** (θ∈Irr(PU))
で、この版では membership は片方向で easy だが、`prTIres_irr_cases` dichotomy 構造を忠実に port し S15
consumer の骨格を与える。**S15 `induce_H_mem_zSpan_S` (S15:629) を実際に close するには H-level 版が要る**:
`Ind_H^S θ = Ind_{PU}^S (Ind_H^{PU} θ)` (`cfIndInd`, transitivity) と分解し、`Ind_H^{PU} θ = ∑ constituents`
の各既約 constituent `s ∈ Irr(PU)` に PU-level `S1cases`/`prTIres_irr_cases` を適用 (Coq `S1cases` 本体の
`cfun_sum_constt`→`rpred_sum` の流れ)。この **cfIndInd 分解 + constituent 和** が次 session の主眼。

**継続 outline (更新)**:

1. **`prTIres_irr_cases` body close** (session 1 #1 のまま) — inertia `'I_S[θ]=PU` の p-group
   fixed-point count。field 版 posit も可。
2. **`PrimeTIResidueData` constructor** (session 1 #2 のまま) — `cyclicTIiso`+`primeTIirr_spec` port。
   今 `P`/`cfker_prTIres` も供給要 (constructor で `P := S_F の PU 内像`、`cfker_prTIres` は
   `PFsection4.v:801` の port)。
3. **H-level `S1cases` / `sS1S`** (NEW, 上記注記) — `cfIndInd` 分解 + `Ind_H^{PU} θ` の constituent 和 →
   各 constituent に PU-level `induce_mem_zSpan_calS` 適用 → `zSpan calS` は加法閉。必要 repo API:
   `cfIndInd` (induction transitivity; `InducedCharacter.lean` に `induce_induce` 系があるか要確認)、
   `cfun_sum_constt` 相当 (既約分解和; repo `Clifford`/`ZIrrFourier` に近いものがあるか)。
4. **`sS1S` wrapper → `induce_H_mem_zSpan_S` (S15:629) close** — H-level `S1cases` から。
   S15 の θ は `↥(H.subgroupOf S)` 上、`P` は `(P.subgroupOf S).subgroupOf (H.subgroupOf S)`。
   `calS` と S15 の `sSet`-family (`mkSection11CharacterDataS_honest ... .S`) の**対応**が要:
   S15 の family は §9 の `sSet = Ind_{HU}^M 𝒳` (M=S, HU=PU 相当) で、本 leaf の `calS = Ind_{PU}^S 𝒳'`
   と **`𝒮 ≈ calS` の同一視** (両者 "PU から誘導した P-nonlinear irr") を橋渡しする glue lemma が S15 側で
   必要 (session 3-4)。

**`sSet ≈ calS` 対応 (S15 が要する)**: S11 `sSet data = {Ind_{HU}^M χ | χ ∈ xiSet}` (kernel 条件は
`H = hInHu ⊄ ker`)、本 leaf `calS = {Ind_{PU}^S ξ | P ⊄ ker ξ}`。type-P setup で `M=S`・`HU=PU`・
`H(の S11 版)` ↔ `P(本 leaf)` が一致すれば両 family は集合として等しい。この identification は S15 側
(`mkSection11CharacterDataS_honest` が `sSet` に pin 済) で `calS D = (…).S` を示す補題として書く。
