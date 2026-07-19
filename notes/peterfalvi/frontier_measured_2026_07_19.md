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
| §6 | (6.3) | 部分 (**次の frontier / 道筋確定**) | `six_three_of_six_two_oracle` (S08_Theorem62_63_Standalone.lean:383) は一般。`h56` の一般 producer `exists_source_index_le_two_psi_of_break` (S08_SixTwoGeneral.lean:987) も実在し、無条件 consumer `typeV_sixFiveA_bound` (S12_Noncoherence.lean:325, axiom-pinned) で discharge 済。**残るのは producer の 2 仮説 `hanchor` / `hdatum` を文脈依存でなく一般に供給すること**。⚠ うち `hanchor` は債務でない — **教科書 (6.2) の証明が自分で導いている**: p.30「Since `K` is solvable, `K/A` has a non-trivial irreducible character of degree 1, whence `S(A)` contains a character of degree `|L:K|`」。Hypothesis (6.1) は `K` solvable を含むので、**「非自明可解群は非自明な 1 次指標を持つ」+ `inducedKernelFamily` 所属 + 次数計算**の 補題 1 本で `hanchor` は消える。repo の `six_two_general` は `IsSolvable K` すら仮定しない(教科書より広い) ため、その分 `h56` を仮説で受けている構図。`hdatum` は (5.6) 適用側の grid decomposition で、こちらは別途。⚠⚠ **着手前に必ず解消すべき食い違い**: repo の `hanchor` は `IsIrreducibleCharacter χ₁ ∧ χ₁ 1 = K.index` と**既約性を要求**するが、教科書 p.30 の当該文は「`S(A)` contains a **character** of degree `|L:K|`」と言うだけで**既約性を主張していない**。よって「可解 ⟹ 非自明 1 次指標」だけでは repo の `hanchor` は作れない。先に (i) producer 側で既約性が本当に要るのか (使用箇所を読む)、(ii) 要らないなら `hanchor` を弱めて教科書どおりにする、を決めること。材料自体は揃っている: `Nontrivial (Abelianization …)` / `Nontrivial (Abelianization … →* ℂˣ)` のパターンが CaseBXi.lean:690/698 に、`inducedKernelFamily` の定義が S08_SixTwoGeneral.lean:54 に。 |
| §6 | (6.4) | **STALE** | 一般定理群は抽象 (6.1) 三つ組 `(τ, A0, SOf)` で parametrize 済。`SibleyDadeHypothesis` は (6.6)/(6.8) の X/Y-set 用 carrier にすぎない。 |
| §6 | (6.5)(a) | **✅ 2026-07-19 解消** | 「K/H₁ は L の chief factor」節を `isChiefFactor_of_relIndex_le_of_odd_dvd` (S08_CoherenceCorePart1.lean:135) として形式化。旧状況: feeder 3 つは揃っていたが wrapper が無く、`IsChiefFactor` (`OddOrder/GroupTheory/ChiefFactor.lean:50`) は S08*/S12* から参照ゼロだった。 |
| §6 | (6.6) | 部分 | 特徴づけ半分は Z-generic (`Xset_eq_irreducible_not_subset_characterKernel`, S08_DegreeSums/CoherenceGlue.lean:491)。coherence 半分は `Z = hyp.centralCommutator` に固定 + `3 ≤ p` / `IsPGroup p ↥H` / `Coprime H.index p`。 |
| §7 | (7.8) | **STALE → 済** | 一般形は `Hypothesis78` 層に実在 (`BetaDecomp` S09_NonexistenceCertain/QuadraticTerm.lean:916, `betaDecompOfFacts` S09_CertificateDischarge.lean:689, `NormEstimates` CoherenceFormula.lean:75)。FrobeniusFamily は consumer にすぎない。追加引数は本文の「S は coherent」前提そのもので特殊化でない。 |
| §7 | (7.9) | **✅ 2026-07-19 解消** | 唯一 Frobenius 専用だった parity step を `Hypothesis79.delta_even` (S09_TwoFamiliesParity.lean, 新規 leaf) として Hypothesis (7.9) 一般形で証明。`FrobeniusFamily.hypothesis79_delta_even` は その instantiation に縮小 ⟹ (7.9) から `FrobeniusFamily` 依存が消えた。 |
| §8 | (8.11) | **STALE → 済** | Sylow-normalizer 節 `normalizer_sylow_mainSubgroup_le` (S10_StructureSetup.lean:395) + Hall 節 (:449) が揃う。 |
| §8 | (8.15) | CONFIRMED 特殊化 | 型別 3 インスタンス (typeI / typeP₁ / typeII)。**type-I の (4.6) 版が無く、(5.2) 節は皆無** (S10_StructureSetup.lean:703 に TODO 明記)。⚠ 先に `typePA` を `M_σ^#` 添字へ直す必要 (現状 `(M')^#`; P₂ 版は false-as-stated = issue 9008)。 |
| §8 | (8.18) | CONFIRMED 特殊化 | (a)(b)(c) すべて `TypeIData S/T` 固定 (S10_MinimalSimpleStructure.lean:404/481/575)。隣の (8.17.c) は `IsTypeI ∨ IsTypeII` で書けている (:107) のが対比。type-II consumer は (8.18.b) を導出せず structure field `cross_zero` として**仮定**している。 |
| §9 | (9.7) | 部分 | 二分岐 `clifford_dichotomy` (CuS0.lean:1811) は axiom-clean。狭いのは 2 点: case (a) の埋め込み先が `((𝔽_p)ˣ)^{q−1}` (order-`a` 巡回でない, S11_ImprimitiveUBound.lean:265) / case (b) の **`W₁ ≅ Aut F` 節が repo に皆無** (S11_GaloisFieldModel.lean:31 は体表現のみ)。 |
| §9 | (9.10) | **✅ 2026-07-19 解消** | trigger 形 `exceptional_case_frobenius_realization_of_trigger` (ThetaCountAssembly.lean:1146) を追加 — `caseB` carrier を仮説に取らず、`hno` だけから Clifford case (b) を選ぶ (case (a) は自身の (9.8.c) 由来の次数 `q·u` 既約元を `Cprime_le_C` + `sOf_antitone` で `𝒮(H₀C′)` へ移して `hno` と矛盾)。consumer (S12_TypeIICrossIsometryPair) の inline dispatch も解消。 |
| §9 | (9.11) | CONFIRMED 特殊化 | `coherent_sOf_H0Cprime` (S13_Orthogonality.lean:1197) は `S13.Hypothesis M` + `IsTypeIII ∨ IsTypeIV`。type-II は §15 の S/T instance 別経路。**repo に `Hypothesis (9.5)` オブジェクトが存在しない** (§9 の仮説は S11 の 3 carrier に分散)。 |
| §10 | (10.11) | 部分 | 第 1 主張 (|W1|,|W2| prime) は一般 (`theorem88_caseB_prime_orders`, S12_MaximalIII_IV_V.lean:1682)。type-II 残余は §15 の S/T pair instance のみ。 |
| §11 | (11.8) | CONFIRMED 特殊化 | `exists_zeta_residual_not_orthogonal_H0C_of_refuter` (S13_Orthogonality.lean:1036) — ∃ でなく ∀ が本文形。加えて ζ が**次数 `w₁`** と `S12.inducedFamily M` に固定 + `IsTypeIII ∨ IsTypeIV`。証明本体は既に ζ-generic。 |
| §13 | (13.8) | CONFIRMED 特殊化 (**規模大**) | 側非依存エンジンは完備 (`caseB_eta01_norm_core`/`_bound`, S15_SAndT_Setup/Machinery135.lean:908/937)。**T 側 instance のみ** (`eta10_Qsharp_norm_lower_core`, Eta10Correction.lean:361)。⚠ **「S 側 producer を 1 本書けば閉じる」は誤り (2026-07-19 実測で訂正)** — carrier 上に **`eta01` という関数がそもそも存在しない** (`grep eta01` は Machinery135 の **側非依存エンジン名/docstring** にしか当たらない; carrier が持つのは `hyp.eta10` のみ)。T 側 producer `exists_caseB_data_eta10_T_core` が依存する 4 ピース (`exists_muT_index_caseB_core` / `exists_etaT_alphaFun_one_int_core` / `Q_sharp_hypothesis76_base` / `reconciled_typePData_T`) は**いずれも S 側版が未存在**。⟹ 着手すると (i) `eta01` の定義、(ii) `P^#` 上の Hypothesis76 base、(iii) S 側 μ index core、(iv) S 側 α 関数、(v) mirror 組み立て、の 5 段になる。 |

## 推奨着手順 (上流優先 + 文書順)

1. ~~(6.5)(a) chief factor 節~~ **✅ 2026-07-19 完了**。
2. ~~(9.10) の `caseB` 除去~~ **✅ 2026-07-19 完了**。
3. ~~(7.9) `hdelta_even` の一般化~~ **✅ 2026-07-19 完了**。
4. **(6.3) standalone 無条件化 → (11.8) ∀ 化 → (6.6) の Z-generic 化** (次の frontier)。
5. **(13.8) S 側 mirror は上記より後**。上表のとおり 5 段構成で、`eta01` の定義から始める必要がある。
6. (8.15)/(8.18)/(9.7)/(9.11)/(10.11) は前提の作り直しを伴うので最後 (特に (8.15) は
   `typePA` の添字修正 = issue 9008 が先)。

## Lean 側の stale docstring (2026-07-19 に修正済)

- `S12_TypeIICrossIsometryPair.lean` module docstring / `:1347` — 4 フィールドを「sorry で置く」
  → 実際は全て discharge 済・file は sorry-free。
- `S11_MaximalII_III_IV/ThetaCountAssembly.lean:1025` — (9.10) type-II `HU`-Frobenius 節を
  「left `sorry`」→ 実際は本文中で証明済。
- `AxiomsCheck.lean:9906/9925` が (9.11) 系 8 宣言について「upstream `C_eq_cSub` の sorryAx
  債務を引き継ぐ」と注記していた件 → **`#print axioms` で実測し全て allowlist 3 axiom のみと確認**。
  注記を訂正し、8 宣言 (capstone `coherent_sOf_H0Cprime` / `coherent_sOf_H0C` を含む) を pin 済。
