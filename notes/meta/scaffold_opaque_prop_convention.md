# Scaffold の opaque `Prop`-field convention (2026-06-01)

BG+Peterfalvi scaffold (codex commits e89971d..cacaadc) で使われる **`foo : Prop; foo_holds : foo`**
および **`_formula : Prop` / `_formula : G → Prop`** という placeholder field の規約と、その traceability・
cleanup path をまとめる。**この note が canonical 参照** (各ファイル docstring からポインタ)。

## 何を / なぜ

- **パターン**: structure に `field_model : Prop`、`betaS_formula : Prop` 等の抽象 `Prop` field を置き、
  必要なら `_holds : field_model` で「成り立つ」証明 field を付ける。
- **理由 (gate #3)**: Peterfalvi (3.2)/(3.3)/(4.3) の指標 index 族 **ω_{ij}/η_{ij}/μ_{ij}/ν_{ij}** と
  補助写像 σ/τ₁/ρ が **S03/S04 に named object として未材料化** (`notes/peterfalvi/scaffold_feasibility_2026_06_01.md`
  の「global gate #3」)。これらを含む文字理論恒等式 (η=τ(ω), norm cascade 等) は faithful に書けないため、
  placeholder で構造だけ通している。plan note は「field carry か `-- TODO`」を推奨し、scaffold は前者を採用。

## どこ (217 opaque field; 文字理論側に集中)

| ファイル | opaque 数 | 備考 |
|---|---|---|
| Peterfalvi S15_SAndT | 41 | ω/η/μ/ν 自体は実型 `Fin q→Fin p→ClassFunction _ ℂ` field。**2026-06-06: `Hypothesis` 本体の (13.1.d,e) 恒等式 3 個 (`eta_eq_tau_omega`/`mu_definition`/`nu_definition`) を materialize** (carried ℂ-linear `tau3`/`indWS`/`indWT` + genuine 等式; commit c724456)。残 opaque は §13 `…Data` carrier 構造 (BasicStructureData/CharacterDegreeData/NormCascadeData/BetaData/TypeIOrthogonalityData) のみ; `Hypothesis` 本体は opaque 0 |
| Peterfalvi S16_NonExistenceG | 37 | FieldNormalizerData/LHypothesis/MHypothesis の恒等式 field。最終矛盾の配線は honest (下記) |
| Peterfalvi S14_MaximalI | 26 | |
| Peterfalvi S12/S13/S11 | 21/14/19 | |
| BG AppE_FurtherResults | 66 | 最低優先 (Further Results); 最も opaque |
| BG AppC/AppD | 17/10 | AppC は HypothesisB/NormSetData の有限体 obligation |
| Peterfalvi Appendices (Suzuki 52 / NearFields 16 / FeitSibley 14 / Huppert 12 / Suzuki2Groups 15) | — | 補助章, 低優先 |

**対照 (opaque を使っていない faithful 側)**: `GroupTheory/MaximalSubgroupType` (Type I–V 塔),
`GroupTheory/MaxNilpotentNormalHall` (M_F), BG `S14_TypePCounting`/`S15_MF`/`S16_MainResults`,
S15 の群構造 field — すべて実構造体 (`IsComplement'`/`IsFrobeniusGroup`/`IsTISubset`/card 等)。

## honesty 状態 (重要)

- **すべて sorry 化済 = 偽証明の laundering は無い**。`#print axioms OddOrder.feitThompson` /
  `noMinimalSimpleOdd_of_section16` はともに **`sorryAx` を含む** (= proved に偽装されていない)。
  AxiomsCheck.lean は不変・green (proved-track の実 sorry 2個=0046/0044 に無影響)。
- **ただし**: 結論に `_formula` rider を含む定理 (例 `∃ data, data.caseB_formula ∧ <real>`) は、
  `_formula` 連言部が **vacuous** (常に充足可能)。つまり statement は教科書版より**弱い/部分的**。
  実制約部 (card 等式・normalizer 包含・D=⊥ 等) は genuine。

## cleanup path (proof フェーズ)

1. **ω/η/μ/ν を S03/S04 に named object 化** (indexed grid `(i,j)↦ω_{ij}` + η=ω^τ 等)。
2. 各 `_formula : Prop` を**実 `ClassFunction` 恒等式**に置換、`_holds` を実証明 (or sorry)。
3. 結論の vacuous rider を実条件に締める。
4. faithful 性監査: opaque が消えるまで「scaffold doneness ≠ build-green」を [[scaffold-sorry-free-not-done]] で判定。

**進捗 (2026-06-06→07)**:
- step 2 (materialize): S15 `Hypothesis` の (13.1.d,e) 恒等式 3 個を opaque `: Prop` → genuine 等式化 (c724456)。
- **μ/ν を canonical induction に pin 完了** (92a99b9): carried `indWS`/`indWT` を撤去し
  `ClassFunction.induce (W.subgroupOf S/T)` (W-grid を W≤S/T で transport) に置換。**ripple 回避の鍵** =
  `[finiteG : Finite G]` を **instance field** で構造体に内包 (消費者は `[Finite G]` 再仮定不要) +
  `noncomputable scoped instance` (`Fintype ↥H` from Finite / `Invertible (Nat.card H : ℂ)`) を
  `scoped namespace FiniteInduce` に置き structure 限定で `open scoped`。これで `induce` が field 型内で
  elaborate し、noncomputable Fintype/Invertible が大域に漏れない。(scratch probe で先に検証)。
- `tau3` を `IntegralCharacterMap ↥W G` (ℤ-linear, tauS/tauT と統一) に retype (0081a9d)。
- **残 = `tau3` の完全 σ-pin** (大): `tau3` を**具体的 (3.2) Dade isometry** にする = W の
  `S05.TICyclicHypothesis` (W1/W2/V TI-subset 〜13 field) を確立 → `S04.dadeIntegralCharacterMap` で σ 構成 →
  ω を (3.3) grid として材料化 → `tau3 = σ`。これは §3/§5 本体の dedicated 形式化 (gate #3 proper)。

grep 手掛かり: `_formula : Prop` / `_formula : G → Prop` / `_holds :` / `: Prop$`。

## 追記 (2026-07-02)

- **σ-pin (`tau3` の完全 σ-pin) は 2026-06-15 完了** (`S05_IntegralSigma`; 上記「残 = `tau3` の完全 σ-pin」は解消済)。
- `noMinimalSimpleOdd_of_section16` は現在 **axiom-clean**(上記「sorryAx を含む」は 2026-06-01 当時の状態)。
- opaque field 数 (S15 41 / S16 37 等の表) は **2026-06-01 snapshot**。
