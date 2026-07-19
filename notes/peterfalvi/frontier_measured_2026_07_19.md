# Peterfalvi 本文 (S01–S16) — 実測 frontier (2026-07-19, lane a)

> **これが Pf 本文の frontier 正本**。2026-07-16 の
> [`three_books_full_survey_2026_07_16.md`](../meta/three_books_full_survey_2026_07_16.md) は
> hub 裁定 9154 §3 で scope 正本から降格済で、Pf 本文についても**実測と食い違う行が複数あった**
> (下表 STALE 行)。着手前は必ず本 note か実測 grep で確認する
> ([[verify-port-state-by-number-not-coq-name]])。

## 測り方

- 実 sorry は必ずコメント除去後に数える (docstring 汚染):
  `perl -0777 -pe 's{/-.*?-/}{}gs; s{--.*$}{}gm' FILE | grep -c '\bsorry\b'`
- **Pf 本文 `OddOrder/Peterfalvi/S*` の実 sorry = 0** (2026-07-19 実測)。
  残 sorry は Appendices のみ (FeitSibley 5 / NearFields 2 / Suzuki2Groups 4 — lane b/c 所管)。
  ⟹ **本文の残作業は sorry でなく「特殊化債務 = 教科書より狭い形」**。
- repo の `S<N>` は**教科書 §(N−2)**。S04=§2, S07=§5, S08=§6, S09=§7, S10=§8, S11=§9,
  S12=§10, S13=§11, S15=§13。

## 実測結果 (書籍 § 順)

| 書籍 | 結果 | 実測判定 | 内容 |
|---|---|---|---|
| §2 | (2.4) | **STALE → 済** | (2.4.c) `N_G(aH(a)) = C_G(a)` は `conj_coset_H_eq_iff_mem_centralizer` (S04_DadeIsometryBasic.lean:880) で実在。§2 は 14/14。 |
| §5 | (5.3)(b) | **✅ 2026-07-19 解消** | (5.2.e) mixed irr×red を `certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV` (S08_CrossOrthogonality.lean) に一般化。3 instance コピー→1 定理。 |
| §5 | (5.8) | **STALE / 債務でない** | 二分岐は既に抽象 (`eq_smul_chiFam_column_of_vanishOnV`, S05_SigmaTrichotomy.lean:461, 素の `TICyclicHypothesis`)。一意性 rider は consumer が符号を `∃ delta'` に吸収するため不要 = 設計選択。 |
| §6 | (6.2) | **STALE → 一般形あり** | `six_two_general` (S08_Theorem62_63_Standalone.lean:349) — Sibley/Frobenius/nilpotent/solvable いずれも不要。survey が指す file が誤り。`h56` 仮説は残る。 |
| §6 | (6.3) | 部分 | `six_three_of_six_two_oracle` (:383) は一般。`h56` には一般 producer `exists_source_index_le_two_psi_of_break` (S08_SixTwoGeneral.lean:987) があり、無条件 consumer `typeV_sixFiveA_bound` (S12_Noncoherence.lean:325, axiom-pinned) で実際に discharge 済。**残: standalone 無条件 (6.3)** — `h56` を (6.1)+(5.6) だけから導く。 |
| §6 | (6.4) | **STALE** | 一般定理群は抽象 (6.1) 三つ組 `(τ, A0, SOf)` で parametrize 済。`SibleyDadeHypothesis` は (6.6)/(6.8) の X/Y-set 用 carrier にすぎない。 |
| §6 | (6.5)(a) | **✅ 2026-07-19 解消** | 「K/H₁ は L の chief factor」節を `isChiefFactor_of_relIndex_le_of_odd_dvd` (S08_CoherenceCorePart1.lean:135) として形式化。旧状況: feeder 3 つは揃っていたが wrapper が無く、`IsChiefFactor` (`OddOrder/GroupTheory/ChiefFactor.lean:50`) は S08*/S12* から参照ゼロだった。 |
| §6 | (6.6) | 部分 | 特徴づけ半分は Z-generic (`Xset_eq_irreducible_not_subset_characterKernel`, S08_DegreeSums/CoherenceGlue.lean:491)。coherence 半分は `Z = hyp.centralCommutator` に固定 + `3 ≤ p` / `IsPGroup p ↥H` / `Coprime H.index p`。 |
| §7 | (7.8) | **STALE → 済** | 一般形は `Hypothesis78` 層に実在 (`BetaDecomp` S09_NonexistenceCertain/QuadraticTerm.lean:916, `betaDecompOfFacts` S09_CertificateDischarge.lean:689, `NormEstimates` CoherenceFormula.lean:75)。FrobeniusFamily は consumer にすぎない。追加引数は本文の「S は coherent」前提そのもので特殊化でない。 |
| §7 | (7.9) | 部分 | `Hypothesis79` + `conclusion_of_…_parity` (TwoFamilies.lean:344) は一般。**Frobenius 専用は `hdelta_even` のみ** (`FrobeniusFamily.hypothesis79_delta_even`, S09_FrobeniusParity.lean:60)。feeder は generic (`cfdot_real_vchar_even` S09_ParityPrimitive.lean:148 ほか)。 |
| §8 | (8.11) | **STALE → 済** | Sylow-normalizer 節 `normalizer_sylow_mainSubgroup_le` (S10_StructureSetup.lean:395) + Hall 節 (:449) が揃う。 |
| §8 | (8.15) | CONFIRMED 特殊化 | 型別 3 インスタンス (typeI / typeP₁ / typeII)。**type-I の (4.6) 版が無く、(5.2) 節は皆無** (S10_StructureSetup.lean:703 に TODO 明記)。⚠ 先に `typePA` を `M_σ^#` 添字へ直す必要 (現状 `(M')^#`; P₂ 版は false-as-stated = issue 9008)。 |
| §8 | (8.18) | CONFIRMED 特殊化 | (a)(b)(c) すべて `TypeIData S/T` 固定 (S10_MinimalSimpleStructure.lean:404/481/575)。隣の (8.17.c) は `IsTypeI ∨ IsTypeII` で書けている (:107) のが対比。type-II consumer は (8.18.b) を導出せず structure field `cross_zero` として**仮定**している。 |
| §9 | (9.7) | 部分 | 二分岐 `clifford_dichotomy` (CuS0.lean:1811) は axiom-clean。狭いのは 2 点: case (a) の埋め込み先が `((𝔽_p)ˣ)^{q−1}` (order-`a` 巡回でない, S11_ImprimitiveUBound.lean:265) / case (b) の **`W₁ ≅ Aut F` 節が repo に皆無** (S11_GaloisFieldModel.lean:31 は体表現のみ)。 |
| §9 | **(9.10)** | 部分 (小) | `exceptional_case_frobenius_realization` (ThetaCountAssembly.lean:1027) が `caseB` を**仮説**に取る。`hno` から case (a) を内部で排除すればよい。**feeder 実在**: `caseA_exists_irreducible_sOf_H0C` (SummandComplementKernel.lean:1368) を `sOf_antitone` (ChiefFactorCore.lean:173) + `Cprime_le_C` (:651) で `𝒮(H₀C′)` へ移す。dispatch は現在 consumer 側 inline (S12_TypeIICrossIsometryPair.lean:1454-1485)。 |
| §9 | (9.11) | CONFIRMED 特殊化 | `coherent_sOf_H0Cprime` (S13_Orthogonality.lean:1197) は `S13.Hypothesis M` + `IsTypeIII ∨ IsTypeIV`。type-II は §15 の S/T instance 別経路。**repo に `Hypothesis (9.5)` オブジェクトが存在しない** (§9 の仮説は S11 の 3 carrier に分散)。 |
| §10 | (10.11) | 部分 | 第 1 主張 (|W1|,|W2| prime) は一般 (`theorem88_caseB_prime_orders`, S12_MaximalIII_IV_V.lean:1682)。type-II 残余は §15 の S/T pair instance のみ。 |
| §11 | (11.8) | CONFIRMED 特殊化 | `exists_zeta_residual_not_orthogonal_H0C_of_refuter` (S13_Orthogonality.lean:1036) — ∃ でなく ∀ が本文形。加えて ζ が**次数 `w₁`** と `S12.inducedFamily M` に固定 + `IsTypeIII ∨ IsTypeIV`。証明本体は既に ζ-generic。 |
| §13 | (13.8) | CONFIRMED 特殊化 | 側非依存エンジンは完備 (`caseB_eta01_norm_core`/`_bound`, S15_SAndT_Setup/Machinery135.lean:908/937)。**T 側 instance のみ** (`eta10_Qsharp_norm_lower_core`, Eta10Correction.lean:361)。S 側 mirror には `exists_caseB_data_eta01_S_core` を 1 本書けばよい (下流は全て側非依存)。 |

## 推奨着手順 (上流優先 + 文書順)

1. ~~(6.5)(a) chief factor 節~~ **✅ 2026-07-19 完了**。
2. **(9.10) の `caseB` 除去** — feeder 実在、dispatch を consumer から定理内へ移すだけ。
3. **(13.8) S 側 mirror** — 下流が全て側非依存ゆえ 1 本で閉じる。
4. (7.9) `hdelta_even` の一般化 → (6.3) standalone 無条件化 → (11.8) ∀ 化。
5. (8.15)/(8.18)/(9.7)/(9.11)/(10.11) は前提の作り直しを伴うので後 (特に (8.15) は
   `typePA` の添字修正 = issue 9008 が先)。

## Lean 側の stale docstring (2026-07-19 に修正済)

- `S12_TypeIICrossIsometryPair.lean` module docstring / `:1347` — 4 フィールドを「sorry で置く」
  → 実際は全て discharge 済・file は sorry-free。
- `S11_MaximalII_III_IV/ThetaCountAssembly.lean:1025` — (9.10) type-II `HU`-Frobenius 節を
  「left `sorry`」→ 実際は本文中で証明済。
- `AxiomsCheck.lean:9906/9925` が (9.11) 系 8 宣言について「upstream `C_eq_cSub` の sorryAx
  債務を引き継ぐ」と注記していた件 → **`#print axioms` で実測し全て allowlist 3 axiom のみと確認**。
  注記を訂正し、8 宣言 (capstone `coherent_sOf_H0Cprime` / `coherent_sOf_H0C` を含む) を pin 済。
