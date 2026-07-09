---
id: 9014
slug: primeti-residue-api
title: "shared-infra claim: prime-TI residue API (primeTIred/prTIres_irr_cases) — §13 μ_j machinery + (13.3) sS1S の共通基盤"
created: 2026-07-06
---

# shared-infra claim: prime-TI residue API (primeTIred/prTIres_irr_cases) — §13 μ_j machinery + (13.3) sS1S の共通基盤

## ⚖️ HUB RULING (2026-07-06, 監視 hub + ユーザー裁可) — **KEEP、本 issue は OPEN 維持**

lane-a「(10.7) 用 prime-TI 機構は repo 不在」vs lane-b「S06 が所有ゆえ PrimeTIResidue は重複、削除」の
**食い違いを code-level で調査 (2 subagent + Coq trace) → 両診断とも別の層を指した talking-past と確定**:

- **lane-b「S06 が prime-TI residue を所有」= 誤り**: S06 は certain-type 既約グリッド `{μ_ij}` + 既約側
  coherence (`certainType_isCoherent`, `S06_CertainTypeCoherence:505`) を持つが、**residue 二分律
  `prTIres_irr_cases` も cyclicTIiso ベースの `primeTIred` も持たない** (S06 の column-sum `μ_j` は
  by-product、cyclicTIiso 由来の residue とは別物)。
- **lane-a「grep 0」= 半分誤り**: `primeTIred`(28 refs)・`cyclicTIiso`(9 refs) は**存在する** —
  ただし **`PrimeTIResidue.lean` 1 ファイル内のみ (= b が削除中のファイル)**。真に 0 なのは
  `uniform_prTIred_coherent`/`FTtypeP_coherent_TIred` (§5/§8 coherence upgrade)。
- **Coq 依存連鎖 (確定)**: `cyclicTIiso → primeTIred (§4) → uniform_prTIred_coherent (§4/§5,
  PFsection4.v:902) → FTtypeP_coherent_TIred (§8, PFsection8.v:852) → Frob_der1_type2 = (10.7) §10
  (PFsection10.v:549)`。`Frob_der1_type2` は line 576 で `primeTIred` を直接使用 + 629/656 で
  `FTtypeP_coherent_TIred` を呼ぶ。**residue primitive は coherence upgrade の前提部品 (独立でない)**。

**⟹ 帰結 (両レーンが見落とし)**: `PrimeTIResidue.lean` は §13 専用でなく **§10 (10.7) の coherence
upgrade も build する共有 prime-TI 基盤**。b の §13 consumer (S15:629 `induce_H_mem_zSpan_S`) が
witness 論法で別途 closed (b commit `51751aa3`、独立に妥当・不変) でも、**§10 (10.7) = lane-a の live
frontier が同じ `primeTIred` の consumer**。∴ **b の削除は §13 局所で妥当だが §10 を見落とした点で
globally 時期尚早**。CLAUDE.md が「mathcomp prime-TI residue API の port」を "複数 downstream を
unblock する genuine prerequisite、淡々と build せよ" の実例に明示している通り、これは捨てる scaffold でなく
**完成させる基盤**。

**裁定 (ユーザー 2026-07-06「keep + 9014 再開」)**:
1. **b の PrimeTIResidue.lean 削除は合流しない (KEEP)**。本ファイルは shared prime-TI foundation
   (RepTheory leaf、§13 + §10 両 consumer)。
2. **本 issue 9014 は OPEN 維持** (b の branch は closed へ move するが、その move は合流しない)。
3. **§10 coherence upgrade** (`uniform_prTIred_coherent` / `FTtypeP_coherent_TIred`) は posited
   `primeTIred` 上に signature-contract で build (constructor 完成を待たない)。
4. **S05_SigmaIsometry の mu2Grid** は "orphan dead code" でなく **constructor (mu2 の σ-grounding)
   の down-payment**。lane-a の S05 に居るのが問題ゆえ **削除でなく本 leaf (PrimeTIResidue) へ移設**。
5. **constructor (cyclicTIiso port + primeTIirr_spec、`prTIres_irr_cases` の discharge) 完成が
   優先タスク** — posited field を実構成に置換する genuine な doneness ([[scaffold-sorry-free-not-done]])。

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

## 進捗 (session 3, 2026-07-06, lane b) — H-LEVEL LIFT landed (継続 #3 完了)

継続 outline #3 (H-level `S1cases`/`sS1S`) を landing。`lake build OddOrder` GREEN (3932 jobs)、新 axiom
なし、**net real sorry = ±0** (依然 `prTIres_irr_cases` の 1 個のみ; 新規 2 宣言は全て sorry-free)。

**import 追加** (両方 proven infra、再構築せず reuse): `InducedTransport` (constituent 分解
`induce_eq_sum_inner_restrict_smul` + `induce_induce_subgroupOf`)、`S08_CoherenceCorePart1`
(kernel 3 補題 — `characterKernel_restrict_subgroupOf`, `isCharacter_restrict`,
`characterKernel_subset_of_isCharacter_of_inner_ne_zero`)。cycle 無し確認済。

**新 derived 宣言 (全 sorry-free、`PrimeTIResidueData` 相対)**:

- `constituent_P_not_subset_ker (H : Subgroup ↥PU) [Fintype ↥H] [Invertible …] (θ : ClassFunction ↥H ℂ)
  (hθirr : IsIrreducibleCharacter θ) (hθP : ¬(D.P.subgroupOf H ⊆ ker θ)) (s : IrreducibleCharacter ↥PU)
  (hs : ⟨θ, Res_H s⟩ ≠ 0) : ¬(D.P ⊆ ker s)` — **step 3 kernel 引数** (Coq `S1cases` 内の kernel 部分)。
  contrapositive: `P ⊆ ker s` ⟹ `characterKernel_restrict_subgroupOf` で `Res_H s` は `P.subgroupOf H`
  上 trivial ⟹ θ は `Res_H s` の constituent (`⟨Res_H s,θ⟩≠0`、conj symm) ゆえ
  `characterKernel_subset_of_isCharacter_of_inner_ne_zero` で `P.subgroupOf H ⊆ ker θ`、`hθP` に矛盾。
- `induce_H_mem_zSpan_calS (H : Subgroup ↥PU) [Fintype ↥H] [Invertible …] (θ : ClassFunction ↥H ℂ)
  (hθirr) (hθP : ¬(D.P.subgroupOf H ⊆ ker θ)) : Ind_{PU}^S (Ind_H^{PU} θ) ∈ zSpan D.calS` —
  **H-level `sS1S` lift** (Coq `S1cases`, PFsection13.v:401)。証明 = Coq `cfun_sum_constt`→`rpred_sum`:
  (i) `induce_eq_sum_inner_restrict_smul` で `Ind_H^{PU} θ = ∑_{s∈Irr PU} ⟨θ,Res_H s⟩•s`、
  (ii) `induce_sum`/`induce_smul` で `Ind_{PU}^S` を sum/scalar に通す、
  (iii) 係数 `⟨θ,Res_H s⟩ = (k:ℂ)` (k:ℕ; `inner_conj_symm` + `IsCharacter.exists_natCast_inner_irreducible`)、
  (iv) `k≠0` の項は `constituent_P_not_subset_ker`→`induce_mem_zSpan_calS`→`nsmul_mem`、`k=0` は `0`。

**⚠ H は `Subgroup ↥PU` として framing** (S15 の `Subgroup G`/`subgroupOf S` でなく): `D.P ≤ H` が
両者 `Subgroup ↥PU` で clean になり、`D.P.subgroupOf H` が `↥H` の対応部分群になる。`Ind_H^S θ` は
honest な二段誘導 `Ind_{PU}^S (Ind_H^{PU} θ)` で表現 (単段 `Ind_{H.map PU.subtype}^S` との橋渡しは
`induce_induce_subgroupOf` で S15 側; これで transitivity を本補題内に持ち込まず constituent-sum に集中)。

**継続 outline (更新)**:

1. **`prTIres_irr_cases` body close** (session 1 #1 のまま) — inertia `'I_S[θ]=PU` の p-group
   fixed-point count。field 版 posit も可。
2. **`PrimeTIResidueData` constructor** (session 1 #2 のまま) — `cyclicTIiso`+`primeTIirr_spec` port
   (`P := S_F の PU 内像`、`cfker_prTIres` = PFsection4.v:801 port)。
3. ~~H-level `S1cases`/`sS1S`~~ **✅ session 3 完了** (`induce_H_mem_zSpan_calS`)。
4. **`sS1S` wrapper → `induce_H_mem_zSpan_S` (S15:629) close** — 残 2 glue が要:
   - **(a) 単段↔二段 橋渡し**: S15 の θ は `↥(H.subgroupOf S)` 上、目標は単段 `Ind_{(H.subgroupOf S)}^S θ`。
     `induce_induce_subgroupOf (M:=S) (hHPU : H.subgroupOf S ≤ PU) θ` で
     `Ind_{PU}^S (Ind_{(H.subgroupOf S).subgroupOf PU}^{PU} (θ∘e)) = Ind_{(H.subgroupOf S)}^S θ`。
     本 leaf の H-level 版は `H_leaf := (H.subgroupOf S).subgroupOf PU : Subgroup ↥PU`、
     `θ_leaf := θ∘e` に instantiate。kernel 条件 `hθP` の subgroupOf 連鎖 transport が要
     (`Subgroup.subgroupOf_map_subtype`/`comap_map_eq_self_of_injective` 系、S11:832-833/9266 に前例)。
   - **(b) `calS D = (mkSection11CharacterDataS_honest …).S` (=`sSet`)**: 上記 `sSet ≈ calS` 対応。
     両者 "PU から誘導した P-nonlinear irr"; type-P setup で `M=S`/`HU=PU`/`H(S11)↔P(leaf)` 一致。
   - **(c) `PrimeTIResidueData` instance for `hyp.S`**: constructor (継続 #2) を S15 の type-P2 setup に適用。
   これら (a)(b)(c) が揃えば S15:629 の sorry は本 leaf から honest に close。

## 進捗 (session 4, 2026-07-06, lane b) — `prTIres_irr_cases` を FIELD 化 → LEAF が完全 sorry-free

継続 outline #1 を landing。`prTIres_irr_cases` を **sorried-theorem から `PrimeTIResidueData`
の posited field へ変換** (outcome B(ii))。`lake build OddOrder` GREEN (3932 jobs)、新 axiom なし。
**本 leaf の real sorry = 0** (comment-strip 検証済; session 1-3 の唯一残 sorry が消えた, net -1)。

**判定理由 (なぜ B(ii) が faithful; A/B(i) を退けた根拠)**: Coq (`PFsection4.v:620-665`) の証明は
dichotomy を **inertia count `'I_S[θ] = PU`** に還元し (`inertia_Ind_irr` = repo
`isIrreducibleCharacter_induce_of_inertia_eq` 済) 、その count は **`p`-群 fixed-point 計算**:
`W1`-conjugation action on `Irr(PU)` の `z`-fixed irr = fixed classes
(`card_afix_irr_classes` = repo `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`)
+ `sylow.pgroup_fix_mod` (mathlib `IsPGroup.card_modEq_card_fixedPoints` 済) + coprimality
`p ∤ |PU|` で fixed 集合を residue image `{chi_ j}` (size `p`) に pin。この計算は **cyclic-TI 構造**
(`W1`, `S = PU ⋊ W1`, `W1`-action, `coprime |PU| |W1|`) を consume するが、**これらは
`PrimeTIResidueData` の field でない** (意図的に abstract away、constructor が `cyclicTIiso` 経由で
`mu2`/`chi` と共に供給)。∴ classification は他 field から**決定されない** ⟹ A (現 field からの証明) は不可能。
B(i) (sub-lemma を green で残す) も現 field からは意味ある sub-lemma が無い (全て `W1` を要す) ため
sorry 据え置きで green 前進ゼロ。⟹ **B(ii) が唯一 faithful かつ leaf を sorry-free 化**: 本 field は
genuine mathcomp `Theorem` で、既存の同 provenance field (`mu2_orthonormal`/`chi_res`/`ind_chi`/
`cfker_prTIres`, いずれも cyclicTIiso 由来の mathcomp theorem) と同格。obligation は constructor に
clean に移る。

**変更点**:
- `PrimeTIResidueData` に field `prTIres_irr_cases` 追加 (signature は旧 sorried theorem と同一;
  docstring に inertia/`pgroup_fix_mod` provenance + なぜ field かを完全記載)。
- 旧 sorried theorem `prTIres_irr_cases` を削除。section-doc と module docstring を field-posit 反映に更新。
- **call site 無変更**: `S1cases` の `rcases D.prTIres_irr_cases θ` は dot-notation ゆえ
  field-projection と method-call が同構文 → 一切修正不要。他に call site なし (grep 確認済)。

**継続 outline (更新)**:

1. ~~`prTIres_irr_cases` body close / field 化~~ **✅ session 4 完了** (field 化, B(ii))。
2. **`PrimeTIResidueData` constructor** (session 1 #2 のまま) — `cyclicTIiso`+`primeTIirr_spec` port。
   今 constructor は `prTIres_irr_cases` も供給要 (上記 inertia/`pgroup_fix_mod` 計算を genuine
   `primeTI_hypothesis` から; 建材 = repo `isIrreducibleCharacter_induce_of_inertia_eq` +
   `card_fixedPoints_conjByPermIrr_...` + mathlib `IsPGroup.card_modEq_card_fixedPoints` は既に揃う。
   欠けるのは cyclic-TI setup: `W1`/`S = PU ⋊ W1`/`W1`-action on `Irr(PU)`/coprimality の bundling)。
3. ~~H-level `S1cases`/`sS1S`~~ **✅ session 3 完了**。
4. **`sS1S` wrapper → `induce_H_mem_zSpan_S` (S15:629) close** — session 3 の残 (a)(b)(c) glue のまま。

## 進捗 (session 5, 2026-07-06, lane b) — CONSTRUCTOR reachability を精密確定 (outcome B)

継続 outline #2 (`PrimeTIResidueData` constructor) の reachability を全建材を調べて確定。**verdict:
constructor は今 honest には組めない — `cyclicTIiso` residue theory (Coq PFsection4.v `primeTIirr_spec`
/`prTIres_spec`/`prTIres_irr_cases`) が repo 未 port**。`lake build` GREEN 維持、**net real sorry = ±0**
(leaf は依然 sorry-free、S15:629 の既存 1 sorry も不変。新規宣言なし — sorry-pile を作らない判断)。

**何が repo に有り、何が無いか (精査結果)**:
- ✅ **(3.2) `sigma` = `cyclicTIiso` の *isometry* は port 済** (`S05_SigmaIsometry.lean:948`
  `TICyclicHypothesis.sigma`, `sigma_inner` で `⟨σω,σω'⟩=⟨ω,ω'⟩` 証明済; `sigmaIntegral` が S15
  `tau3` の pin 元)。だが `sigma` は `Module.Basis.constr` で `Irr(W)` 全体を `chiFam`(bare virtual
  char ∈ `ZIrr G`) に送るのみ。
- ✅ **(1.4) per-column `SignedIrreducibleDifferenceFamily` は port 済** (`S06.columnFamily`)。だが
  この structure は **`mu : Fin n → IrreducibleCharacter G` + `sign` + column 内 `injective` のみ**
  (`IsometryDifferencePair.lean:312`)。**cross-column の関係を一切持たない**。
- ❌ **`primeTIirr_spec` (Coq PFsection4.v:288-387, ~100 行) が未 port** — これが `σ(w_ij)=δ_j·mu2_ij`
  (`mu2_ij∈Irr(L)` 単一 signed irreducible; `dirr_dIirr` 経由) を確立し、そこから `prTIirr_inj`→
  **`cfdot_prTIirr` (=`mu2_orthonormal`)** が出る。`vchar_isometry_base`/`equiv_restrict_compl_ortho`/
  `eq_in_cycTIiso`/`dirr_dchi` を consume。
- ❌ **`prTIres_spec` (Coq:563) 未 port** — `chi_j=Res(mu2_0j)` (`chi_res`) と `Ind(chi_j)=μ_j`
  (`ind_chi`)。`cfRes_prTIirr_eq0` (Coq:533, coprime `p∤|PU|` の normal-complement `group_modr` 論法)
  が要。
- ❌ **`prTIres_irr_cases` (Coq:620-665) 未 port** — inertia `'I_L[θ]=K` の p-群 fixed-point count。
  建材 (`isIrreducibleCharacter_induce_of_inertia_eq`, `card_fixedPoints_conjByPermIrr_...`,
  `IsPGroup.card_modEq_card_fixedPoints`) は揃うが、cyclic-TI setup (`W1`-action on `Irr(PU)` の
  bundling) が無い。

**「columnFamily を p 本束ねれば mu2 grid」は FALSE (session 1 note の最短路仮説を棄却)**: `columnFamily χ₂`
は各列 `j` で `IrreducibleCharacter L` の tuple を与えるが、**列を跨ぐ直交性 (`mu2_orthonormal` の `j≠l`
成分) は (1.4) の出力に含まれない**。(1.4) は各列独立に norm-2 difference を分解するだけで、列間の関係は
`primeTIirr_spec` の全 `Irr(W)`-basis isometry 分解 (`σ` 経由) からしか出ない。∴ p 本束ねても grid の
9 field のうち `mu2`(列ごと)しか埋まらず、`mu2_orthonormal`/`chi_res`/`chi_zero`/`prTIres_irr_cases`
は依然 posit のまま。

**S15 `hyp` grid からの partial constructor も棄却 (sorry-pile 回避)**: S15 `Hypothesis`
(`S15_SAndT_Setup.lean:98`) は既に (13.1) grid を posit (`mu`/`mu_irreducible`/`mu_col_injective`/
`mu_definition`/`mu_colSum_eq_induce`/`omega_orthonormal`/`delta`…)。ここから `PrimeTIResidueData` を
組むと `mu2:=hyp.mu`(via `mu_irreducible`)・`chi:=`(`mu_colSum_eq_induce` の `Classical.choose`)・
`ind_chi`(同 field) は緑で埋まるが、**`mu2_orthonormal`/`chi_res`/`chi_zero`/`prTIres_irr_cases` の 4
field は sorry**。これは task 明示の禁止 (「one isolated sorry per field is the max, prefer
characterizing (B) over a sorry-pile」) に抵触し、かつ posit→posit の横流しで genuine な `cyclicTIiso`
obligation を 1 つも discharge しない (CLAUDE.md doneness に反する)。∴ 実装せず。**`PrimeTIResidueData`
は external consumer 0** (grep 確認、target は S15:629 のみ) ゆえ partial 版を置いても誰も使わない。

**最短 honest path to a grounded `PrimeTIResidueData` for `hyp.S`** (build order + 見積り):
1. **`dirr` 抽出 layer** (`sigma(ω_ij) = δ_j·mu2_ij`, `mu2_ij∈Irr`): `sigma`(既) + norm-1 ⟹ 単一 signed
   irr。repo に `exists_irr_of_...`/signed-triple 基盤あり。**~1 session**。ここから `mu2_orthonormal`
   (`cfdot_prTIirr`) が緑化 (isometry + inj)。→ `mu2`/`mu2_orthonormal` 2 field 解消。
2. **residue `chi` = `Res(mu2_0j)`** + `cfRes_prTIirr_eq0` (coprime normal-complement, Coq:533): mathlib
   `IsPGroup`/`coprime`/`group_modr` 相当。**~1 session**。→ `chi`/`chi_res`/`ind_chi`/`chi_zero` 4 field。
3. **`prTIres_irr_cases`**: inertia count。建材既存、cyclic-TI action bundling が要。**~1-1.5 session**。
   → 最後の 1 field。
4. **`cfker_prTIres`** (Coq:801) + constructor 組み立て + `P := S_F の PU 像`。**~0.5 session**。
合計 **~3.5-4 session**。前提は §4 全体の `cyclicTIiso` residue port (issue 2035 #7 の見積りと整合)。
**building block `sigma` は既に有る**ので、issue 冒頭の「cyclicTIiso stack 全体が未 port」は過大 —
isometry 部分は済、残るは residue/dirr/inertia 部分。

**tractability 評価**: 上記 3.5-4 session は clean な近道でなく §4 char body の正面攻略 (norm estimate +
Clifford + p-group count)。deep だが frontier は明確で、CLAUDE.md 方針どおり deep のまま engage 可能。
現時点で最上流の genuine gap は **step 1 の `dirr` 抽出** (`sigma` から単一 signed irr を取り出す)。
これが landing すれば `mu2_orthonormal` が緑化し constructor の骨格が立つ。

## ⚠ HUB doneness 注記 (2026-07-06, posited field 化 commit 167b59d4 に対し)

b が `prTIres_irr_cases` (Pf (4.5.b)、Coq PFsection4.v:620-665) を `PrimeTIResidueData` の **posited
field** 化し leaf を sorry-free 化。**「leaf sorry-free」は doneness を意味しない** ([[scaffold-sorry-free-not-done]])
— 深い prTIres_irr_cases は実証明されず posited field に isolate されただけ。**本 infra の doneness =
posited field の discharge (= `PrimeTIResidueData` を real math から constructor で構成)** で判定する。

- **現状**: derived API は sorry-free だが、`prTIres_irr_cases` field は未 discharge。consumer (a の (10.7) /
  b の (13.3)) が本 structure を cite するときも、structure が構成されなければ vacuous。
- **discharge の残作業 (b 追跡、session 5)**: constructor の到達性 = **dirr extraction が top-frontier**、
  σ (cyclicTIiso 系) は既 port 済。dirr extraction を閉じれば `card_afix_irr_classes` +
  `IsPGroup.card_modEq_card_fixedPoints` から field が実証明され、structure が real に構成される。
- **⟹ hub 監視**: 本 field を permanent free field として放置しない。b は dirr extraction → constructor
  discharge まで進めて **`PrimeTIResidueData` の real 構成**を landing する (それが prime-TI infra の真の完了)。
  sorry-count の −1 は doneness 前進でなく obligation の posit への移動ゆえ、count でなく constructor
  discharge を進捗指標とする。
## 進捗 (session 6, 2026-07-06, lane b) — STEP 1 `dirr` 抽出 landed (mu2 + mu2_orthonormal 接地)

継続 outline #2 の **step 1 (`dirr` 抽出 layer)** を landing。**`lake build OddOrder` GREEN (3932 jobs)、
新 axiom なし** (`#print axioms` で新 3 定理が `[propext, Classical.choice, Quot.sound]` のみ = `sorryAx`
無し確認済)、**net real sorry = ±0** (追加は全て sorry-free; S05 の凍結 sorry-free 状態を保持)。配置は
`S05_SigmaIsometry.lean` (末尾, `namespace TICyclicHypothesis` 内) — `sigma`/`sigma_inner_irreducibleCharacter`/
`sigma_mem_ZIrr`/`chiFam_spec` が全て scope 内、かつ import 済 `InducedIrreducible` に norm-1 classifier が有る
ため bridge file 不要 (import cycle 回避)。124 行追加。

**判定 (step 2 の norm-1⟹signed-irr lemma は既に in-repo)**: task step 2 が要求する「norm-1 の `ZIrr G`
元 ⟹ ± single irreducible」は **`OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one`
(`InducedIrreducible.lean:526`) として既に存在** (Peterfalvi (5.9.a); `exists_single_of_sum_sq_eq_one` +
Parseval)。∴ 新規に整数線形代数を組む必要は無く、これを `σ(ω)` に適用するだけ。

**新宣言 (全 sorry-free、`TICyclicHypothesis` 相対、`hVeq`/`app` 引数)**:
- `exists_sign_smul_irr_of_sigma_omega (ω : Irr W) : ∃ (δ:ℤ)(μ:Irr G), (δ=±1) ∧ σ(ω) = δ•μ` —
  **`dirr` 抽出 existence** (Coq `primeTIirr_spec` via `dirr_dIirr`)。`σ(ω)∈ZIrr G` (`sigma_mem_ZIrr`) +
  `‖σ(ω)‖²=‖ω‖²=1` (`sigma_inner_irreducibleCharacter`) → 上記 classifier。
- `mu2Grid (ω : Irr W) : IrreducibleCharacter G` (= Coq `primeTIirr`, choice of μ) +
  `mu2GridSign (ω) : ℤ` (= δ) + specs `mu2GridSign_eq` (±1), `sigma_omega_eq_mu2GridSign_smul_mu2Grid`
  (`σ(ω)=δ•μ`), `mu2Grid_eq_sign_smul_sigma_omega` (`μ=δ•σ(ω)`, δ²=1)。
- **`mu2Grid_orthonormal (ω ω') : ⟨mu2Grid ω, mu2Grid ω'⟩ = [ω=ω']`** (= Coq `cfdot_prTIirr` =
  `PrimeTIResidueData.mu2_orthonormal`) — diagonal は irreducibility; off-diagonal は
  `mu2Grid ω=mu2Grid ω'` ⟹ `⟨σω,σω'⟩=δ_ω δ_ω'·1=±1≠0` が `⟨σω,σω'⟩=⟨ω,ω'⟩=0` (isometry, ω≠ω') に矛盾。
- `mu2Grid_injective` (mu2Grid は Irr(W) 上単射; 直交性から)。

**これで `PrimeTIResidueData` の 2 field `mu2`/`mu2_orthonormal` が `hyp` の σ から接地可能**になった
(grid は `Irr(W)`-indexed; constructor では `Iirr W1 × Iirr W2 ≃ Irr W` = `omegaIrrEquiv` で `Fin q × Fin p`
に読み替える — bijection は既存)。ただし `PrimeTIResidueData` を丸ごと組むには残 field
(`chi`/`chi_res`/`ind_chi`/`chi_zero`/`cfker_prTIres`/`prTIres_irr_cases`/`P`) が要るため、本 session は
**再利用可能な extraction lemma 群**として landing し、full constructor 組み立ては step 2-4 に残す
(sorry-pile 回避; `PrimeTIResidueData` は依然 external consumer 0 = S15:629 のみ)。

**継続 outline (更新)**:
1. ~~`prTIres_irr_cases` field 化~~ **✅ session 4**。
2. **`PrimeTIResidueData` constructor** の残 step:
   - ~~**step 1 `dirr` 抽出** (`mu2`/`mu2_orthonormal`)~~ **✅ session 6** (`mu2Grid`/`mu2Grid_orthonormal`)。
   - **step 2 residue `chi` = `Res(mu2Grid ω_{0j})`** + `cfRes_prTIirr_eq0` (coprime normal-complement,
     Coq PFsection4.v:533)。→ `chi`/`chi_res`/`ind_chi`/`chi_zero`。**~1 session**。
   - **step 3 `prTIres_irr_cases`** (field 済だが constructor 供給には) inertia count の cyclic-TI bundling。
   - **step 4 `cfker_prTIres`** (Coq:801) + `P := S_F の PU 像` + 全 field 束ね + `Iirr W1×Iirr W2 ≃ Irr W`
     で `mu2Grid` を `Fin q → Fin p → Irr G` grid に読み替え。**~0.5 session**。
3. ~~H-level `S1cases`/`sS1S`~~ **✅ session 3**。
4. **`sS1S` wrapper → `induce_H_mem_zSpan_S` (S15:629) close** — session 3 の残 (a)(b)(c) glue のまま。

## 🛑 進捗 (session 7, 2026-07-06, lane b) — STEP 2 は **既に S06 で ported 済** と判明 → 再構築中止 (outcome B)

継続 outline #2 step 2 (residue `chi`/`chi_res`/`ind_chi`/`chi_zero`, key = `cfRes_prTIirr_eq0`) を
着手する前に **claim-before-build スキャン** (CLAUDE.md「既存を再構築しない」/[[verify-port-state-by-number-not-coq-name]])
を実施した結果、**§4 prime-TI residue theory (4.5.a + 4.5.b) は既に `OddOrder/Peterfalvi/S06_*` に
完全 port 済・sorry-free** と確定。`lake build OddOrder.Peterfalvi.S06_CertainTypeClifford
OddOrder.Peterfalvi.S06_CertainTypeSupport` GREEN (3460 jobs, style linter warn のみ; real sorry=0)。
**本 session は Lean 無変更・net real sorry ±0** (S05 の凍結 sorry-free 状態不変、S15:629 の 1 sorry も不変)。

**決定 (なぜ再構築しない)**: `PrimeTIResidueData` の 4 field が要求する residue 数学は、`S06.Hypothesis`
(= Coq `primeTI_hypothesis` の repo 版; `K ⋊ W1 = L`・`K_normal`・`card_coprime`・`W2 ≤ K` を bundle)
の上で **既に honest に証明されている**。`S = L`・`PU = K` として 1:1 対応 (grep+読解で全数確認):

| `PrimeTIResidueData` field / Coq | S06 の proven 定理 (sorry-free) | file:line |
|---|---|---|
| `chi j` / `primeTIres` | `chiRestrict χ₂ : IrreducibleCharacter ↥K` | S06_CertainTypeClifford:772 |
| **`chi_res` (i 独立) / `cfRes_prTIirr_eq0` (Coq:533)** | **`restrict_certainType_eq`** (`Res_K μ_ij = Res_K μ_0j`) + `certainTypeRestrict_isIrreducible` | :608 / :732 |
| `ind_chi` / `cfInd_prTIres` | `induce_restrict_certainType_eq` (`Ind_K^L χ_j = ∑_i μ_ij`) | :743 |
| `chi_zero` / `prTIres0` | `chiRestrict_one_eq_trivial` (`chiRestrict 1 = 1_K`) | S06_CertainTypeSupport:287 |
| `cfker_prTIres` (Coq:801) | `not_subset_characterKernel_chiRestrict_of_ne_one` (`W₂ ⊄ ker χ_j`, j≠0) | S06_CertainTypeSupport:182 |
| `prTIres_irr_cases` (Coq:620) | `exists_eq_certainType_or_induce` + `induce_isIrreducible_of_forall_chiRestrict_ne` (inertia `I_L(χ)=K` 実証済 via `inertia_eq_K_of_forall_chiRestrict_ne`) | :964 / :913 / :868 |
| `mu2_orthonormal` / `cfdot_prTIirr` | `columnFamily` (`.mu i` = μ_ij) + `columnFamily_mu_ne`/cross-orth 群 | S06_CertainTypeCharacters:432+ |

- **key の `cfRes_prTIirr_eq0` (i-independence) は proved**: `restrict_certainType_eq` が Coq 論法
  (`Ind_W^L(ω_ij−ω_0j)` の support が `W−W₂` の conjugate に限られ `K` を外す ⟹ `μ_ij−μ_0j` は `K` 上 0)
  を **`induce_chiColumnDiff_eq_zero_of_mem_K` (:560) + `mem_W2_of_mem_sup_of_mem_K` (`W⊓K=W₂`, :371)**
  で忠実に実証。engine `cfInd_sub_prTIirr` (=`Ind(ω_ij−ω_0j)=δ_j•(μ_ij−μ_0j)`) は **`columnFamily_spec`**
  として在る (S05 `mu2Grid` route には無い; 下記)。
- **既に FT spine が consume**: `FeitThompson.lean:2726/2731`・`S08_CaseB*`・`S12`・`S15.mu_definition`
  が上記 S06 定理群を直接 cite。§13/§15 は `mu_definition` (Coq shape `Ind(ω_ij−ω_0j)=δ_j•(μ_ij−μ_0j)`,
  = `S06_MuColumnBridge.induce_chiColumn_diff_mu_diff`) 経由で residue を得ており、`PrimeTIResidueData`
  は経由しない。

**なぜ `mu2Grid` route (本 issue の leaf) では step 2 を green に組めないか (技術的核心)**:
`PrimeTIResidueData`/`mu2Grid` は `TICyclicHypothesis G` レベルで、**`PU=K` を持たない** (構造に normal
subgroup field が無い)。かつ `cfRes_prTIirr_eq0` の engine は **column-uniform sign `δ_j`** を要すが、
session 6 の `mu2Grid` は per-`ω` sign (`mu2GridSign ω`) しか持たず **column-uniform 性は未証明**
(= Coq `primeTIirr_spec`, 未 port)。S06 は sign uniformity を **別 route** = (1.4) `columnFamily` +
degree-congruence (4.3.d) `certainType_sign_eq_of_degree_eq` で得ている。`mu2Grid ↔ columnFamily` の
bridge は **repo に存在しない** (grep: `mu2Grid` は S05 + 本 leaf のみ) 上、両者は ambient group
(`G` vs `L`)・V-set (`W−(W₁∪W₂)` vs `W−W₂`)・induction 方向が異なり、bridge 自体が大きな独立 port。
∴ `mu2Grid` からの step 2 は「clean な近道が無い」でなく **正しい層でない** (S06 が正しい層)。

**⟹ 結論・handoff**:
1. **step 2 は再実装しない** (S06 に proven 済; 再構築は CLAUDE.md 違反の重複)。本 issue の `PrimeTIResidue.lean`
   leaf (sessions 1-6) は S06 residue theory の **parallel re-derivation** で、`S1cases`/`induce_H_mem_zSpan_calS`
   等の下流 skeleton は有用だが、`mu2`/`chi`/... の field-grounding は S06 定理で置換すべき。
2. **真の残作業 = S15:629 `induce_H_mem_zSpan_S` の close** は、`PrimeTIResidueData` 構成 (from `mu2Grid`)
   ではなく、**S06 の proven residue 定理 (上表) を S15 の type-P2 setup に instantiate** して行うのが
   honest かつ非重複な path。session 3 の H-level lift (`induce_H_mem_zSpan_calS`) は
   `PrimeTIResidueData` を hypothesis に取る engine ゆえ、その `D` を **S06 由来で構成** (or S06 定理で
   直接 `zSpan` membership を組む) すればよい。次 session はこの「S06 residue → S15:629」glue に注力する。
3. `PrimeTIResidueData` の constructor を作るなら **source は `mu2Grid` でなく `columnFamily`/`chiRestrict`**
   (index は `Ŵ₂ × Fin |W₁|`; `Fin q × Fin p` への読み替えは `card_charGroup_W2` 等で bijection)。
   ただし `PrimeTIResidueData` は external consumer 0 ゆえ、S15:629 を S06 定理で直接閉じるなら
   `PrimeTIResidueData` 構成自体が不要になる可能性が高い (次 session が判断)。

## ✅ 進捗 (session 8, 2026-07-06, lane b) — S15:629 を **S06-grounded で sorry-free close** → leaf REDUNDANT 確定

継続 outline #4 (`sS1S` wrapper → `induce_H_mem_zSpan_S`) を **honest かつ非重複に landing**。
`lake build OddOrder` **GREEN (3932 jobs, 新 axiom なし)**、S15 real sorry **20→19 (net −1)**。
`#print axioms Hypothesis.induce_H_mem_zSpan_S` = `[propext, Classical.choice, Quot.sound]` (**sorryAx 無**)。

**核心的発見 (session 7 の悲観 + 本 issue 全体の前提を訂正)**: S15:629 の close に **prime-TI residue
dichotomy (`S1cases`/`prTIres_irr_cases`) も `PrimeTIResidueData` も一切不要**。理由 = 目標族
`𝒮 = sSet = {Ind_{S'}^S χ | χ ∈ Irr(S'), P ⊄ ker χ}` は「S' から誘導した P-nonlinear irreducible の
induction 全体」で、**membership は witness で即座に成立**する (`mem_sSet`; induction の可約/既約や
`μ_j`-type かは問われない)。∴ Coq `S1cases` の dichotomy は `seqIndD` の定義形状 (可約 or family-member)
ゆえに必要だったが、repo の `sSet` は最初から「全 P-nonlinear induction」なので dichotomy 不要。leaf の
`induce_mem_calS` (witness membership, sorry 無) が本質で、`S1cases`/`prTIres_irr_cases` 経路は
**over-engineered だった**。

**実際の証明 (S15_SAndT_Setup.lean:668 `Hypothesis.induce_H_mem_zSpan_S`, sorry-free)**:
1. `Ind_{PC}^S θ = Ind_{S'}^S (Ind_{PC'}^{S'} θ')` — 二段誘導 `induce_induce_subgroupOf` (`PC ≤ S' = HU`,
   `θ' = θ ∘ subgroupOfEquivOfLe`)。
2. `Ind_{PC'}^{S'} θ' = ∑_{s∈Irr(S')} ⟨θ', Res s⟩ • s` — `induce_eq_sum_inner_restrict_smul`、
   `Ind_{S'}^S` を sum/scalar に通す。
3. 係数 `⟨θ', Res s⟩ = (k:ℕ)` (`exists_natCast_inner_irreducible` + `inner_conj_symm`)。
4. `k≠0` の各 `s`: `P ⊄ ker s` (新 generic helper `constituent_P_not_subset_characterKernel` =
   S08 kernel 3 補題の contrapositive、leaf `constituent_P_not_subset_ker` の generic 版)、ゆえ
   `Ind_{S'}^S s ∈ sSet` (witness `s`) → `zSpan sSet`、`nsmul_mem` で ℕ 倍も残る。`k=0` は `0`。
- 使用建材: **すべて既存 proven** — `InducedTransport` (`induce_induce_subgroupOf`,
  `induce_eq_sum_inner_restrict_smul`)、S08 kernel 補題、S11 `sSet`/`huSub_eq_derivedInG_subgroupOf`/
  `mem_sSet`、`typePData_toS06Hypothesis` (S12; type-P Hypothesis 供給は S' 族形状の grounding 用、ただし
  本証明では `sSet` 定義が既に S' 族なので S06 dichotomy は呼ばず)。**`PrimeTIResidue.lean` を import せず**。
- 下流 consumer (`tau1S_ofHonest_inner_induce`/`_induce_mem_ZIrr`) は本 theorem を cite; それらの残 sorryAx は
  §14 `sibleyTarget_H0C` gate (別件、本 task scope 外) のみ。

**⟹ LEAF-FATE 裁定: `OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean` は REDUNDANT**:
- **importer 0 / code consumer 0** (grep 確認; S05/S15 の `PrimeTIResidueData` 言及は全て docstring のみ)。
- (b) S15:629 は本 leaf 無しで close 済 (上記)。
- (a) lane a issue 1017 の (10.7) `typeII_derived_frobenius` は、issue 1017 本文の精密診断では
  **§5 `uniform_degree_coherence`/`subcoherent` (Coq PFsection5) が blocker** で、**prime-TI residue の
  dichotomy ではない** (issue 1017: 「(10.7) は §9 counts 不使用、`uniform_degree_coherence` で local
  partner coherence」)。9014 hub 注記の「a も prime-TI に gated」は `uniform_prTIred_coherent` の名前を
  §5 uniform-coherence と混同したもの。⟹ a も本 leaf を必要としない。
- **推奨 = delete** (`PrimeTIResidue.lean` 全体 + `PrimeTIResidueData` structure)。sessions 1-6 の
  `mu2Grid` extraction (S05_SigmaIsometry.lean 内、leaf 外) は S05 の `sigma` 上の再利用可能 lemma 群として
  残せるが、これも現状 external consumer 0。**leaf 削除は本 task scope 外 (fate 決定は保留と明記されたため
  削除せず report のみ)**。9014 は本 session で **実質完了** (S15:629 close 達成); leaf 削除を別 issue 化推奨。

## ✅ RESOLVED / claim 撤回 (2026-07-06, session 8) — leaf 削除、S15:629 は S06 から non-dup 実証明

**結論**: prime-TI residue API leaf は**不要だった**。(1) §4 residue theory は S06 に既存 (session 7)、
(2) さらに target `induce_H_mem_zSpan_S` (S15:629, sS1S) は **sSet の witness 論法**で閉じ、prime-TI
dichotomy 自体が不要 (session 8、commit 51751aa3、sorry-free)。⟹ **`PrimeTIResidue.lean` (6-session leaf)
を削除** (consumer 0、OddOrder.lean import 除去)。lane a (10.7) も §5 uniform_degree_coherence が gate
であり prime-TI residue でない (issue 1017 診断) → a も本 leaf 不要。

**残置**: S05 の `mu2Grid`/`exists_sign_smul_irr_of_sigma_omega` (σ→signed-irr dirr extraction、
sorry-free) は standalone §4 building block として残す (docstring を leaf 非依存に reword、現 unconsumed)。

**教訓** ([[verify-port-state-by-number-not-coq-name]] 強化済): multi-session の新 infra port 前に
概念名 (Coq 名でなく) で S0x を exhaustive grep + 該当 § file 通読。1 scan ミスが 6 session を溶かした。
claim 撤回、本 issue close。

## 2026-07-06 更新 (lane b) — ★restructure (裁定 item 1-4) 完了、held merge unblock

hub 裁定 fcfc0644 の restructure を lane-b が実行完了 (prior commit 4948ff00 の巻き戻し + mu2Grid 移設):

- ✅ **PrimeTIResidue.lean 復元** (528 行、4948ff00^ から) + OddOrder.lean import 復元 (commit 45f610ac)。
- ✅ **9014 を open へ戻す** (closed/ → issues/、commit 45f610ac)。
- ✅ **mu2Grid を S05_SigmaIsometry → PrimeTIResidue へ移設** (124 行、namespace/API 不変、
  `import S05_SigmaIsometry` + variable + open 追加で受け入れ、commit af2a1a23)。external ref 0、
  #print axioms 標準3のみ、full build GREEN 3933 jobs。lane-a の S05 は clean。

⟹ **held merge の restructure 前提は解消**。残 = **item 5 constructor 完成 (優先タスク)**:
`cyclicTIiso` port + `primeTIirr_spec` (mu2Grid の実体) + `prTIres_irr_cases` discharge →
posited field (`primeTIred` の residue 二分律) を実構成に置換 ([[scaffold-sorry-free-not-done]] の
genuine doneness)。これが §10 (10.7) `Frob_der1_type2` = lane-a frontier と §13 μ_j machinery の共通
基盤。次 lane-b iteration はこの constructor に正面着手する (規模大・多 session でも淡々と build、
CLAUDE.md「コスト/規模は着手基準でない」)。

## 2026-07-06 更新 #2 (lane b) — ★★constructor 大幅 de-risk: deep field prTIres_irr_cases は S06 に既存、bridge で discharge 可

constructor (裁定 item 5) を verify-first 精査 → **「6-session cyclicTIiso port」の前提は誤り**。
`PrimeTIResidueData` の唯一の genuinely-deep field `prTIres_irr_cases` (4.5.b constituent classification =
inertia I_S[θ]=PU の p-group fixed-point count) は **S06_CertainTypeClifford に既に完全 port 済**:

- `inertia_eq_K_of_forall_chiRestrict_ne` (S06:907) = 非residue χ の inertia I_L(χ)=K (deep p-group 計算、
  `card_fixedPoints_conjByPermIrr…` + `IsPGroup.card_modEq_card_fixedPoints`)。
- `induce_isIrreducible_of_forall_chiRestrict_ne` (S06:931) = 非residue χ ⟹ Ind χ 既約
  (+ `isIrreducibleCharacter_induce_of_inertia_eq`)。
- `induce_ne_certainType_of_forall_chiRestrict_ne` (S06:943) = Ind χ ≠ μ_{ij}。

**3 discharge primitives (docstring 記載) は全て repo に存在** (前 subagent の「cyclicTIiso 機構 unbuilt」は
S06 の descriptive 名を見落とした Coq 名 grep の罠、[[verify-port-state-by-number-not-coq-name]])。

**landed (PrimeTIResidue.lean、commit 次)**: `S06.Hypothesis.prTIres_irr_dichotomy` — 上記 S06 定理を
組んで dichotomy `(∃ χ₂, chiRestrict χ₂ = χ) ∨ (Ind χ 既約 ∧ ∀ χ₂ i, Ind χ ≠ μ_{ij})` を証明
(sorry-free、#print axioms 標準3のみ)。= `PrimeTIResidueData.prTIres_irr_cases` field の実体。

**⟹ constructor の真の形 = `PrimeTIResidueData.ofS06Hypothesis` bridge** (S06.Hypothesis → PrimeTIResidueData):
- mu2 ← S06 columnFamily grid (or 移設済 mu2Grid)、chi ← h.chiRestrict、
- prTIres_irr_cases ← `prTIres_irr_dichotomy` (landed)、
- mu2_orthonormal/chi_res/ind_chi/chi_zero/cfker_prTIres ← S06 の対応 grid 定理群 (columnFamily 正規直交・
  restrict_certainType_eq 等、大半 S06 に proven)。
これは「from-scratch port」でなく既存 S06 grid 定理の field-mapping ⟹ 規模は当初想定より遥かに小。
次 = ofS06Hypothesis bridge の field 群 (indexing Fin p ↔ Ŵ₂ / Fin q ↔ Fin|W1| + 各 field の S06 定理接続)。

## 2026-07-06 更新 #3 (lane b) — ★constructor は 100% mechanical assembly と確定 (全 field の S06 source 特定)

`ofS06Hypothesis` constructor の全 9 field が S06 に既存 (0 new math、残は Fin-indexing wiring のみ):

| PrimeTIResidueData field | S06 source (file:定理) |
|---|---|
| mu2 | `columnFamily.mu` (S06_CertainTypeCharacters:432) |
| chi | `chiRestrict` (S06_CertainTypeClifford:772) |
| mu2_orthonormal | columnFamily 正規直交 (columnFamily_mu 系) |
| chi_res | `coe_chiRestrict` (:778, rfl) |
| ind_chi | `induce_restrict_certainType_eq` (:743) |
| chi_zero | `chiRestrict_one_eq_trivial` (S06_CertainTypeSupport:287) |
| cfker_prTIres | `not_subset_characterKernel_chiRestrict_of_ne_one` ((4.7)) |
| prTIres_irr_cases | `prTIres_irr_dichotomy` (landed, PrimeTIResidue.lean) |
| card fact |Ŵ₂|=|W₂| | `card_charGroup_W2` |

indexing: p := Nat.card h.W2、q := Nat.card h.W1、`Fin p ≃ Ŵ2` を card_charGroup_W2 + trivial↦0 pin
(chiRestrict_one_eq_trivial で chi_zero)。P field = W2 ⊆ H ≤ K の任意 H (FT app では Fitting)。
⟹ constructor 完成は pure wiring。background subagent に委任 (mechanical、context 節約)。

## 2026-07-06 更新 #4 (lane b) — ★★constructor LANDED: PrimeTIResidueData.ofS06Hypothesis (裁定 item 5 完了)

`PrimeTIResidueData.ofS06Hypothesis` を landed (subagent 実装 + 親 verify)。裁定 item 5「constructor 完成 —
posited field を実構成に置換」達成:

```
ofS06Hypothesis [Fintype ↥h.K] (H : Subgroup ↥h.K) (hW2H : h.W2.subgroupOf h.K ≤ H) :
  PrimeTIResidueData L h.K (Nat.card h.W1) (Nat.card h.W2)
```
(h : S06.Hypothesis L から)。全 9 field を genuine S06 定理で実構成 (更新 #3 の mapping table 通り)、
+ index bridge `charGroupW2Equiv : Fin (Nat.card h.W2) ≃ Ŵ2` (card_charGroup_W2 + trivial↦0 pin)。
**#print axioms = 標準3のみ (sorryAx 無)、leaf GREEN 3486 / full GREEN 3933**。PrimeTIResidueData /
S06 の signature 無改変。posited field は全て実構成に置換済 = PrimeTIResidueData carrier の構成可能性
実証 ([[scaffold-sorry-free-not-done]] の genuine doneness)。

**⟹ 裁定 (fcfc0644) の全 item 完了**: item 1-4 restructure (復元/再open/mu2Grid移設) + item 5 constructor。
9014 の prime-TI residue foundation は honest に構成可能と確定。§10 (10.7、lane-a) が primeTIred を
consume するとき本 constructor + PrimeTIResidueData API が使える。**本 issue は constructor 完了ゆえ
close 候補** (hub 判断; foundation 完成、残 consumer wiring は §10 lane-a 側)。

## 2026-07-06 lane-d closure

Current-state audit: `PrimeTIResidueData.ofS06Hypothesis` is present in
`OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean`, the issue's item 1-5 ruling is
implemented, and the remaining §10 consumer wiring belongs to lane-a's downstream issue rather than
this shared foundation claim. Move to `issues/closed/`.

## ⚖️ HUB 補足 (2026-07-06 夕, レーン分担監査) — **KEEP+OPEN 維持、frontier gate ではない**

上の lane-d closure 提案は hub が却下済 (commit `8167ab01` reopen; codex 越権是正)。分担監査で code-verified:
**`PrimeTIResidue.lean` = 0 bare sorry、`ofS06Hypothesis` constructor 実装済** ⟹ **foundation は build 済、
現 FT frontier の gate ではない**。当セッション冒頭で hub が「prime-TI が a/b の open な bottleneck」と仮説した
のは **stale** (訂正済); 真の gate は BG §15/§16 (issue 9017、lane b owner)。本 9014 が OPEN なのは
**§5/§8/§10 downstream coherence upgrade** (`uniform_prTIred_coherent` / `FTtypeP_coherent_TIred`、posited
`primeTIred` 上に signature-contract で build、(10.7) `typeII_derived_frobenius` feeder = lane-a §10 path)
が未 build ゆえのみ。**新規レーンを本 issue に張り付けない** (9000 型の a-vs-d 重複衝突を招く)。

## ⚖️ HUB carve-out 追記 (2026-07-09 監視 tick — merge dd18fdc5)

**lane c の `S13_PrimeTIResidueBridge.lean` 編集 (426c3ae1) を retroactive carve-out で保全** (軌道修正保全、9076 piece 4c-3 先例と同型)。本 file は 2026-07-08 carve-out で **b 所有**だが、c の編集を hub 検証のうえ受理:

- **内容**: `Hypothesis.residueS` の data instance binder (`[Fintype ↥hyp.S]` / `[Invertible …]` ×4) を scoped `FiniteInduce` 供給 (`finiteSubFintype`/`natCardInvC`) に統一 + 内部 `haveI` 除去。Prop-valued `NeZero` binder のみ維持。動機 = instance 項不一致が `columnFamily` level の defeq unification を破壊し whnf timeout (200k heartbeats 超) — [[lean-instance-defeq-traps]] の既知イディオム準拠の修正。
- **hub 検証**: (i) `residueS` の consumer = repo 全体で S13_PrimeTIResidueBridge + S15_HonestTypeP2A0 (c 所有) のみ = **blast radius 0**; (ii) `git diff main...b` に本 file なし = b の並行編集なし; (iii) 数学的内容 (ofS06Hypothesis 構成) 不変の instance plumbing で「signature 無断改変」STOP の対象 (contract 破壊) に非該当; (iv) merge gates 通過 (sorry 増減なし・新 axiom なし)。
- **⟹ 恒久ルール**: c が本 file の **`Hypothesis.residueS` 周辺 (c の (13.18) engine が consume する S-side bridge 宣言)** を編集しても逸脱でない。b の (13.18) μ-carrier honest source 側 (`Hypothesis.s06S` 等) は従来どおり b。b は次回 main sync で本 refactor を取り込むこと (binder 供給の再変更をしない)。
