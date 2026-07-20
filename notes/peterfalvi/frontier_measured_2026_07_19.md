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
| §6 | (6.2) `hanchor` | **✅ 2026-07-19 解消** | 下表の (6.3) 行にあった「`inertia θ = K` をどう供給するか」という gap は**存在しなかった** — repo 側の (5.6) エンジンが anchor の既約性を要求していたのが**特殊化債務**だった。Peterfalvi (5.6) の仮説は `S₁` coherent / `χ₁(1) ∣ χ(1)` / `2χ(1)χ₁(1) < ∑ χᵢ(1)²/‖χᵢ‖²` の 3 つのみで、証明は `‖χ₁‖²` を**記号のまま担ぐ** ((5.6.1) の `(Y, χ₁^τ₁) = (a − λ/‖χ₁‖²)‖χ₁‖² = a‖χ₁‖² − λ`)。エンジンを norm-general 化して `hanchorNorm : mc i₁ = 1` を全廃 → `hanchor` は教科書どおり「`S(A')` は次数 `|L:K|` の character を含む」に弱まり、**既存の `exists_inducedKernelFamily_member_degree_index` (S08_SixTwoGeneral.lean:143) がそのまま discharge**。詳細は下記「(5.6) エンジンの norm 一般化」節。 |
| §6 | (6.3) | **✅ 2026-07-19 決着** (下記 2 節参照) | `six_three_of_six_two_oracle` (S08_Theorem62_63_Standalone.lean:383) は一般。`h56` の producer `exists_source_index_le_two_psi_of_break` (S08_SixTwoGeneral.lean) の 2 仮説のうち **`hanchor` は解消** ((5.6) エンジンの norm 一般化 → 既存 `exists_inducedKernelFamily_member_degree_index` で discharge)。**`hdatum` は債務でない** — Peterfalvi (5.2.d)+(5.2.e) そのもので、教科書も Hypothesis (5.2) の**仮説として担いでいる** (導出していない)。⟹ repo が `h56`/`hdatum` をパラメータで受けるのは忠実。⚠ 旧記述にあった「本当の gap は `inertia θ = K` の供給」は**誤診** — 撤回済 ([[repo-stronger-hypothesis-is-specialization-not-gap]])。真の未形式化は **(5.3) の一般 producer**。 |
| §6 | (6.4) | **STALE** | 一般定理群は抽象 (6.1) 三つ組 `(τ, A0, SOf)` で parametrize 済。`SibleyDadeHypothesis` は (6.6)/(6.8) の X/Y-set 用 carrier にすぎない。 |
| §6 | (6.5)(a) | **✅ 2026-07-19 解消** | 「K/H₁ は L の chief factor」節を `isChiefFactor_of_relIndex_le_of_odd_dvd` (S08_CoherenceCorePart1.lean:135) として形式化。旧状況: feeder 3 つは揃っていたが wrapper が無く、`IsChiefFactor` (`OddOrder/GroupTheory/ChiefFactor.lean:50`) は S08*/S12* から参照ゼロだった。 |
| §6 | (6.6) | **✅ 2026-07-19 解消 (Z-generic 化)** | (a) は既に Z-generic (`Xset_eq_irreducible_not_subset_characterKernel`)。(b) の coherence engine を Z-generic 化: `Xset_centralCommutator_isCoherent_of_irreducible_X` → **`Xset_isCoherent_of_irreducible_X`** (S08_CoherenceBasic) — 任意の `Z ⊴ L`, `Z ≤ H`, `Z.subgroupOf H ≤ Z(H)` (= 教科書の `Z ⊆ Z(K)`) で `X(Z) = S − S(Z)` が coherent。`hX` (全 X-member 既約) は**教科書 (6.6) 自身の仮説** `𝒳 ⊆ Irr L` に対応、`hXne` は `Z ≠ 1` から Z-generic に導出可 (`Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X`)。`hp`/`hp3`/`hHp`/`hidxp` は教科書証明自身の (6.5) 還元後の形 (還元は capstone `sibleySetup_is_coherent` に配線済)。着手時判定の答: `centralCommutator_ne_bot` / `isIrreducibleCharacter_of_mem_Xset_c2_caseA` は**一般化不要** — (6.6) の一部でなく、応用文脈 (Frobenius/c2-caseA) が Zc で仮説 `hX`/`hXne` を生産する側の補題。`_of_frobenius`/`_of_c2_caseA` は Zc 特殊化 producer として存続 (これは教科書 (6.8) 側の適用)。 |
| §7 | (7.8) | **STALE → 済** | 一般形は `Hypothesis78` 層に実在 (`BetaDecomp` S09_NonexistenceCertain/QuadraticTerm.lean:916, `betaDecompOfFacts` S09_CertificateDischarge.lean:689, `NormEstimates` CoherenceFormula.lean:75)。FrobeniusFamily は consumer にすぎない。追加引数は本文の「S は coherent」前提そのもので特殊化でない。 |
| §7 | (7.9) | **✅ 2026-07-19 解消** | 唯一 Frobenius 専用だった parity step を `Hypothesis79.delta_even` (S09_TwoFamiliesParity.lean, 新規 leaf) として Hypothesis (7.9) 一般形で証明。`FrobeniusFamily.hypothesis79_delta_even` は その instantiation に縮小 ⟹ (7.9) から `FrobeniusFamily` 依存が消えた。 |
| §8 | (8.11) | **STALE → 済** | Sylow-normalizer 節 `normalizer_sylow_mainSubgroup_le` (S10_StructureSetup.lean:395) + Hall 節 (:449) が揃う。 |
| §8 | (8.15) | **✅ 2026-07-19 ungated 分解消 (issue 1042)** | 主張 3 ((5.2) instance) = `S10_SubcoherentTypeP.lean` (既約部分家族の `S07.Hypothesis`、A₀ 形 + M^# 字義形; 可約 μ 列は S07_Subcoherent note どおり certainType 側が正本)。主張 2 ((4.6) instance) = `S10_Hypothesis46TypeP.lean` (H パラメータ化一般形 + `_hallKernel`/`_derived` 両選択、hHall 明示化で axiom-clean)。**残 = type-II の忠実 A(M) を要する部分のみ → hub issue 9163** (typePA M_s^# 添字化 Option A vs 新 def B′)。 |
| §8 | (8.18) | CONFIRMED 特殊化 (**9163 に gated**, 2026-07-19 実測) | (a)(b)(c) すべて `TypeIData S/T` 固定 (S10_MinimalSimpleStructure.lean:404/481/575)。書籍 (8.18) は S, T 型仮定なし (PDF p.49 確認; 「A(T)−A₁(T) ≠ ∅ ⟹ T type I/II」は証明中で導出)。type-II 側へ広げるには **type II の忠実 A(T)** が要る = P₂ 域 typePA 問題 → **(8.15) type-II 残と同じ hub issue 9163 に gated**。`cross_zero` 導出も同gate。 |
| §9 | (9.7) | **✅ 2026-07-19 解消 (issue 1043, (a)(b) とも)** | 二分岐 `clifford_dichotomy` (CuS0.lean:1811) は元から axiom-clean。狭かった 2 点を両方解消: **(a)** order-`a` 埋め込み `caseA_exists_blockScalarRatioEmbedding_orderA` + per-block cyclic rider (S11_ImprimitiveUBound.lean)。**(b)** `W₁ ≅ Aut F` 節 = `caseB_exists_galoisField_repr_withAut` (S11_GaloisFieldModel.lean) — H̄ ↔ F (加法)・Ū ↔ U* (乗法)・W₁ ↔ Aut F (全単射 η, 自然作用)。連鎖: base point `s ∈ W̄₂^#` (`chiefFactor_exists_fixedByE_ne_one`, `|C_H̄(W₁)| = p` から) で Singer 模型を `φ(s) = 1` に正規化 → `U*` の加法生成 (既約性を e で F の AddSubgroup へ transport) → twist 恒等式 `η(w)(μu) = μ(w u w⁻¹)` (`φ(s)=1` と `s^w=s` が displayed identity を潰す) → 共有抽象層 `ringAutHomOfAddAutHom` で **環**自己同型に着地 → 単射 (`w1ActionHom_injective`: 核は `\|W₁\|=q` 素数の部分群、⊤ なら `p = p^q` で矛盾) + `\|Aut F\| = q` (`natCard_ringAut_galoisField`) で onto。共有抽象層は新設 `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean`。全宣言 axiom-clean・AxiomsCheck 登録済。⚠ 系 (`u ⊥ (p−1)` / `u ∣ (p^q−1)/(p−1)`) は**着手前から完了済**だった (`chiefFactor_caseB_image_coprime`/`_dvd_norm`, InertiaLift.lean:680/874 — 仮説は case (b) 既約性のみ)。⚠ **§9 の pdftotext 抽出は文字バラけで使用不能** → 原文は PDF 画像 (書籍 p.52 = 章 PDF p.3)。⚠ 書籍は右作用・repo は左作用。 |
| §9 | (9.10) | **✅ 2026-07-19 解消** | trigger 形 `exceptional_case_frobenius_realization_of_trigger` (ThetaCountAssembly.lean:1146) を追加 — `caseB` carrier を仮説に取らず、`hno` だけから Clifford case (b) を選ぶ (case (a) は自身の (9.8.c) 由来の次数 `q·u` 既約元を `Cprime_le_C` + `sOf_antitone` で `𝒮(H₀C′)` へ移して `hno` と矛盾)。consumer (S12_TypeIICrossIsometryPair) の inline dispatch も解消。 |
| §9 | (9.11) | **⚠ 再分類 2026-07-19: 数学は完備・M 側一般化は 9163 に gated** (旧「CONFIRMED 特殊化 → 次の ungated frontier」は**誤り**) | 実測 (htype の依存を leaf まで trace): **(9.11) の議論そのものに type-III/IV の leaf は無い**。M 側 `coherent_sOf_H0Cprime` (S13_Orthogonality.lean:1197) の `htype` は全て `C_eq_cSub_of_noncoherent` (S13_CoreStructure.lean:511) へ流れ込む**辞書同一視**の artifact で、そこから (11.7) `H₀ = 1` → `ChiefFactorData.typeIII_IV_p_eq_W2` (= `\|W₂\| = p`、**type II では偽**) に落ちる。**type-II を含む honest な (9.11) は既に存在する**: `Hypothesis.sSet_coherent_indS_A` (S15_CaseACoherence.lean:713) は**型仮説を一切取らず**、`clifford_dichotomy` で case A/B に分岐して同一の generic (9.11) 装置を回す (T 側 = `sSet_coherent_indT_A`)。しかも support は 9163 の Option B′ = `honestTypeP2ASet` (`A(M) = ⋃_{x∈M_σ^#} C_{M'}(x)^#`) を使う正しい形。`nineElevenEqualityRefutationS` の docstring が明言: 「M 側の `htype`/`hncH0C` は packaging の `H₀C′` を generic `cprimeSub` 層と同一視するためだけに在り、S-instance では辞書が定義的なので消える」。⟹ **M 側を type-II へ広げる作業は (9.11) 内部の問題ではなく §12 の hypothesis 層の作り直し**: `S12.Hypothesis.type_alt : IsTypeIII ∨ IsTypeIV ∨ IsTypeV` (Hypothesis.lean:353) ゆえ type-II では**文が立たない**上、`base.A0` が誤った `typePA = (M')^#` 上に建っている → **hub issue 9163 に gated ((8.15)/(8.18) と同一 gate)**。生 §9 装置 (`S11_NineEleven*`) は `TypesIIIIIIVSetup` (type_alt は 3 分岐で type II 込み) 上に書かれており既に type-agnostic。なお「repo に `Hypothesis (9.5)` オブジェクトが無い」のは事実だが、3 carrier (`TypesIIIIIIVSetup`/`ChiefFactorData`/`Section11CharacterData`) が**合わせて** (9.5) を成し全て構成可能ゆえ、単なる bundling であって数学的債務ではない。 |
| §10 | (10.11) | 部分 (**2026-07-20 訂正**) | 第 1 主張 (|W1|,|W2| prime) は一般 (`theorem88_caseB_prime_orders`, S12_MaximalIII_IV_V.lean:1673)。⚠ 旧記述「type-II 残余は §15 の S/T pair instance のみ」は **stale**: 書籍の第 2 主張は「M が型 II なら Hypotheses (9.2)/(9.5) の記法で `H` は位数 `p^q` (`p = |W₂|`) の elementary abelian、かつ `𝒮` は coherent」で、証明は `H₀ = 1` → `C′ = 1` → `𝒮(H₀C′) = 𝒮` → **(9.11)**。(9.11) の型 II 版は 2026-07-20 に landed (`S11.typeII_nineEleven_coherent`, issue 1045) したので、§15 経由でなく (9.2)/(9.5) のまま直接述べられる。⟹ **issue 1048** に分離。部品は全て実測済で在る。 |
| §11 | (11.8) | **✅ 2026-07-19 解消 (∀ 化)** | 教科書形は ∀ ζ (PDF p.65-67: 任意の `ζ ∈ S(HC)` に対し直交性を仮定して (11.8.4)-(11.8.6) で (11.3) と矛盾)。`zeta_residual_not_orthogonal_H0C_of_refuter` (S13_Orthogonality.lean) として ∀ 形を主定理化し、旧 `exists_zeta_...` は witness packaging の系に降格 (consumer 3 箇所は無変更)。鍵は新規 `S12.Hypothesis.exists_charParameters_full_of_zeta` — parameters を**与えられた ζ の周りで**組む。⚠ 次数 `ζ(1) = w₁` は**特殊化でない**: `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` の台条件 (`alpha_support`) がまさにそれを要求する (`n·w₁ = d − δ` + `μ_{i0}(1) = 1` ⟹ `α_{ij}(1) = 0`)。残る狭さは `S12.inducedFamily M` 固定 + `IsTypeIII ∨ IsTypeIV` のみ。S16 側の同文重複 (`member_residual_not_orthogonal_H0C_of_refuter` + member-pinned producer 2 件) は issue 1040 で削除済 (consumer 2 件は S13 版 cite に置換)。 |
| §13 | (13.8) | **✅ 2026-07-19 解消 (S 側 mirror 完成, issue 1041)** | 書籍 (13.8) 本体 = S 側 `∑_{H^#}|η₀₁|² ≥ |S′|−u²` を `eta01_Hsharp_norm_lower_core` (S15_CaseBEndgameSupply/Eta01Correction.lean) として実証明 (仮定 hG のみ、sorry 0、axiom-clean 実測済)。distinguished index (`exists_muS_index_eta01_core`) は T 側 550 行の完全 mirror (2 段 constituent 展開 + ℕ-係数直交カウント)。「applied to T」instance (`eta10_Qsharp_norm_lower_core`) と両輪が揃った。 |

## ⚠ 訂正 (2026-07-20, lane a): §9 行の結論は誤り — gate は 9163 ではなかった

上表 §9 行は「(9.11) M 側の type-II 化 = §12 hypothesis 層の作り直し (`base.A0` が誤った
`typePA = (M')^#` 上に建つ) → **9163 に gated**」と結論していたが、**書籍 p.50-51 を読んで実測した
結果、gate はそこではない**。正しい診断は issue **1045** (詳細) に記録。要点:

- **書籍 (9.5) の `C` は `C_U(H̄)`** (chief factor の中心化群) であって `C_U(H)` **ではない**。
  repo の §9 carrier `S11.Section11CharacterData` は既にこれ (`C = cSub = C_U(H̄)`) を持ち、
  `TypesIIIIIIVSetup` (= Hyp (9.2)) は `IsTypeII ∨ IsTypeIII ∨ IsTypeIV` で**既に型一様**。
- gate の実体は「repo の (9.11) が §9 carrier でなく **§11 packaging** (`S13.Hypothesis`,
  `type_alt : III ∨ IV` + `base : S12.Hypothesis` = §10) の上に建っている」こと。
  §11 が `hyp.C = C_U(H)` と書籍の `C_U(H̄)` を同一視するのに (11.7) `H₀ = 1` を使うので、
  `H₀ ≠ 1` の型 II では**この経路が閉じる**。`typePA`/`typePACore` は (9.11) の gate ではない。
- ⟹ 正しい作業 = **(9.11) を §9 レベル (`TypesIIIIIIVSetup` + `ChiefFactorData` +
  `Section11CharacterData`) で述べ直す**。`sOf_closedUnderConjugate` は既に §9 レベル、
  `sSet_finite` も §9 レベル (置き場が S15) で、大半は**再配置と引数一般化**であり新規の数学は薄い。

**副産物 (同日実装済)**: (9.6) の型一様化。`chiefFactor_basic` の docstring が自認していた
「書籍は `|W̄₂| = p` だが repo は型 III/IV 限定の `|W₂| = p` に退避」という特殊化債務は、
**`W̄₂` と `C_U(H̄)` で述べ直せば消える** (書籍の (9.6) 自体が型 II を証明している)。
`chiefFactor_cSub_ne_U` / `chiefFactor_U_not_centralizes_H` / `chiefFactor_basic` /
`cSub_subgroupOf_U_eq_ker_map`、いずれも axiom-clean。型限定の `|W₂| = p` は carrier field
`ChiefFactorData.typeIII_IV_p_eq_W2` に残る (本来の居場所)。

## (5.6) エンジンの norm 一般化 (2026-07-19, lane a)

**発端**: (6.3) の frontier 調査で「repo の `hanchor` が anchor の既約性を要求するが、教科書 p.30 は
"`S(A)` contains a **character** of degree `|L:K|`" としか言わない」という食い違いを flag していた。
前回の追調査は「本当の gap は `inertia θ = K` (= θ が L-不変でない) の供給」と結論したが、
**これは誤りだった**。

**教科書の実測 (PDF p.26-27, p.30)**: Theorem (5.6) の仮説は
(a) `S₁` coherent, (b) `χ₁(1) ∣ χ(1)`, (c) `2χ(1)χ₁(1) < ∑ χᵢ(1)²/‖χᵢ‖²` の **3 つだけ**で、
anchor `χ₁` の既約性も norm 1 も**要求していない**。証明は `‖χ₁‖²` を記号のまま担ぐ:
- (5.6.1): `λᵢ = λ·aᵢ/‖χᵢ‖²` (`λ = λ₁‖χ₁‖²`)、`(Y, χ₁^τ₁) = (a − λ/‖χ₁‖²)‖χ₁‖² = a‖χ₁‖² − λ ∈ ℤ`
  ⟹ `λ ∈ ℤ` (`a‖χ₁‖² ∈ ℤ` を使う)。
- (5.6.2): `(λ/‖χ₁‖² − a)²‖χ₁‖² + λ²∑_{i≥2}(aᵢ²/‖χᵢ‖⁴)‖χᵢ‖² + ‖Z‖² ≤ a²‖χ₁‖²`
  ⟹ `λ²∑aᵢ²/‖χᵢ‖² − 2λa + ‖Z‖² ≤ 0` — `‖χ₁‖²` は完全に相殺される。

⟹ repo 側の `hanchorNorm : mc i₁ = 1` は**特殊化債務**であって教科書要件ではなかった。

**実施した一般化** (`mc i₁` を記号のまま担ぐ):
| 宣言 | 変更 |
|---|---|
| `inner_Y_extension_member_eq` (S08_CoherenceCorePart1/CoherentAdjoin.lean) | `hchi1chi1 : ⟨χ₁,χ₁⟩ = m₁`、結論を `a·⟨χ₁,cⱼ⟩ − (a·m₁ + μ)·aⱼ` へ (λ = `a·m₁ + μ`)。 |
| `crux1_of_memberFamilyW` (S08_CoherenceWeighted.lean) | `hanchorNorm` 廃止、結論 `μ = −a·mc i₁`。**λ の整数性は `mc i₁ = ⟨νχ₁,νχ₁⟩` が `ν χ₁ ∈ ℤ[Irr G]` ゆえ整数**という事実で供給 (`inner_mem_ZIrr_int`) — これが `mc i₁ = 1` の norm-general な代替。 |
| `retarget_isCoherent_of_extensionImage` / `_k` | `m₁` 化。`huu = 1 + a²·m₁`、`hvv = m₁`、`hvu = −a·m₁` のみ変化し、`‖X‖² = 1`・`‖X̄‖² = 1`・`⟨X,X̄⟩ = 0` は `a²·m₁` が相殺して不変。 |
| `lambda_eq_zero_and_Z_eq_zero` (S07) | **変更不要** — 元から norm-general (`hψ : ‖ψ‖² = a²·mc i₁`, `hr₁ : rc i₁·mc i₁ = 1` は `deg i₁ = 1` から従う)。 |
| `xAdjoinStepW` / `_k`、`XAdjoinStepInputW`、`coherentDegreeSqNormBound_of_not_coherentW` / `_k` | `hanchorNorm` フィールド・仮説を全廃。 |
| `inducedKernelFamily_SA_sum_le_two_psi_k` 系 (S08_SixTwoGeneral) | `hχ₁irr : IsIrreducibleCharacter χ₁` を**削除**。 |
| `exists_source_index_le_two_psi_of_break` | `hanchor` を教科書形 `∃ χ₁ ∈ S(A'), χ₁ 1 = |L:K|` へ弱化。 |
| `S13_SixTwoBridge.exists_anchor` | `hG`/`hyp`/(8.4.d) `inertia_eq_derived_of_linear` 依存を**除去**し、既存の `exists_inducedKernelFamily_member_degree_index` (S08_SixTwoGeneral.lean:143) 一本で discharge。 |

**帰結**: (6.2) の `hanchor` は**閉じた**。教科書の "K solvable ⟹ K/A は非自明 1 次指標を持つ
⟹ S(A) は次数 |L:K| の character を含む" がそのまま Lean 側の discharge になる
(`commutator (K ⧸ X.subgroupOf K) ≠ ⊤` が入力)。⚠ **副次的に `caseB` 側の `hanchorNorm` 導出
(S08_CaseBEnumeration の 2 箇所、`η` の既約性経由) も dead code になり削除**。
残る (6.3) の未充足仮説は **`hdatum` のみ** ((5.6) 適用側の grid decomposition)。

## ⚠ 「(6.3) 無条件化」の再定義 — `hdatum` は債務でなく教科書の standing hypothesis

`hanchor` を閉じた後、(6.3) に残る `hdatum` を調べた結果、**「一般に供給する」は
そもそも達成すべき目標ではない**ことが判明した (PDF p.25 実測)。

- `hdatum` = **Peterfalvi (5.2.d) + (5.2.e)**:
  (d) `χ ∈ S` に対し `(χ − χ̄)^τ = ∑_{α ∈ R(χ)} α` (`R(χ)` は `ℤ[Irr G]` の正規直交部分集合)、
  (e) `φ` が `{χ, χ̄}` に直交するなら `R(φ) ⊥ R(χ)`。
- これらは **Hypothesis (5.2) の仮説そのもの**で、教科書も導出していない。Theorem (5.6) は
  Hypothesis (5.2) の下で証明される。
- 教科書が (5.2) を**供給する**のは **(5.3) の 2 経路だけ**:
  - **(5.3.a)** (5.2.a)+(5.2.b)+`S ⊆ Irr L` ⟹ (5.2)。(`‖(χ−χ̄)^τ‖² = 2` ゆえ `|R(χ)| = 2`、
    (5.2.e) は (4.1) から)
  - **(5.3.b)** Hypothesis (4.6)+(5.2.a)+`S ⊆ {Ind_K^L θ | H ⊄ Ker θ}` ⟹ (5.2)。可約 member は
    `μ_j` (0 < j < w₂) で、(4.9) より `R(μ_j) = {δ_j ω^σ_{ij}, −δ_j ω^σ_{ik} | 0 ≤ i < w₁}`。
- ⟹ repo が `six_two_general` / `six_three_of_six_two_oracle` / `exists_source_index_le_two_psi_of_break`
  で `hdatum` (と `h56`) を**パラメータとして担いでいるのは教科書に忠実**であって特殊化債務でない。
  「(6.3) standalone 無条件化」は `hanchor` の分で**完了**とみなす。

### ⚠ 「(5.3) が未形式化」は誤り — 自己訂正 (同日、着手前に実測して撤回)

上記から「次の上流仕事は (5.3.a)/(5.3.b) の一般 producer を書くこと」と一旦書いたが、
**着手前の実測で誤りと判明した**。`S07.Hypothesis` の producer を `ofIrreducible` /
`Hypothesis.of` 等の名前で grep して 0 件だったための false negative
([[verify-port-state-by-number-not-coq-name]] そのもの)。実際は:

- **(5.3.a) は実在** = `OddOrder.Peterfalvi.S07.irrSubcoherent`
  (`S07_Subcoherent.lean:151`)。`τ`/`A`/per-member `Rdatum`/(5.2.a,c) 述語/差の台条件/
  格子 isometry から `S07.Hypothesis` を組む**抽象一般形**。(5.2.e) は
  `orthogonal_of_signedDifference_inner_eq_zero` + isometry + `inner_conjugateDifference_eq_zero`
  で導出済。consumer 実在 (例 `sSetIrrDegT_subcoherent`, S15_TSetMemberRFamily.lean:799)。
- **(5.3.b) = Coq `prDade_subcoherent` は「作らない」が既定裁定** (`S07_Subcoherent.lean:280-300`,
  2026-07-06 CORRECTED 注記)。理由 2 点: (i) `S07.Hypothesis.difference_image` は
  **2 元の `CharacterDifferenceImage` を固定**するが Coq `subcoherent` の `R` は可変長
  (既約 2 / 可約 `μ_j` は `2w₁`) ゆえ `prDade` 形の `S07.Hypothesis` は**構成不能**、
  (ii) **consumer ゼロ** — 可約列の coherence は `S07.IsCoherent` として直接
  (`certainType_isCoherent`, S06:505) 消費される。可約 R-datum の中身自体は
  `S06.certainTypeR` / `columnImageFamilyCohFree` / `sixTwoDecompositionData` として
  **既に sorry-free で存在**。

⟹ **§5 (5.2)/(5.3) 層に未形式化は無い**。同 note の「Multi-session build outline」
(`S07_Subcoherent.lean:278-345`) が §5→§9 の live な残作業の正本で、そこが指す残りは
**(9.11) の pair-adjoining induction の `hstep` データ** (S15 に局在) であって §5 ではない。

## 推奨着手順 (上流優先 + 文書順)

1. ~~(6.5)(a) chief factor 節~~ **✅ 2026-07-19 完了**。
2. ~~(9.10) の `caseB` 除去~~ **✅ 2026-07-19 完了**。
3. ~~(7.9) `hdelta_even` の一般化~~ **✅ 2026-07-19 完了**。
4. ~~(6.2) `hanchor` の一般供給~~ **✅ 2026-07-19 完了** ((5.6) エンジンの norm 一般化)。
   `hdatum` 側は上記のとおり教科書 (5.2) の仮説ゆえ「無条件化」対象外。
5. ~~(5.3.a)/(5.3.b) の一般 producer~~ **着手不要** — (5.3.a) は `irrSubcoherent` で実在、
   (5.3.b) は構成不能かつ consumer ゼロで「作らない」が既定裁定 (上記自己訂正節)。
6. ~~(11.8) ∀ 化~~ **✅ 2026-07-19 完了**。~~(6.6) の Z-generic 化~~ **✅ 2026-07-19 完了** (issue 1040 の dedup も同日完了)。→ **(13.8) S 側 mirror** (次の frontier)。
7. ~~(13.8) S 側 mirror~~ **✅ 2026-07-19 完了** (issue 1041)。
8. (8.15)/(8.18)/(9.7)/(9.11)/(10.11) は前提の作り直しを伴うので最後 (特に (8.15) は
   `typePA` の添字修正 = issue 9008 が先)。
   **2026-07-19 更新**: (8.15) の ungated 分 (主張 2+3 の P₁ 域) は完了 (issue 1042、上表)。
   (8.15) type-II 残 + (8.18) 一般化は **hub issue 9163** (typePA 設計裁定) に gated。
   ⟹ 次の ungated frontier = **(9.7)** (case (a) の embedding 巡回化 + case (b) の
   `W₁ ≅ Aut F` 節新設) → (9.11) hstep → (10.11)。
   **2026-07-19 追記 (実測による再分類)**:
   - ~~(9.7)~~ **✅ 完了** (issue 1043、(a)(b) とも)。
   - **(9.11) も 9163 に gated だった** — 上表の再分類参照。「次の ungated frontier」に
     挙げていたのは**誤り**。(9.11) の数学は完備で、type-II 込みの honest 版は
     `sSet_coherent_indS_A` (型仮説なし・`honestTypeP2ASet` 使用) として既に在る。
     M 側一般化は §12 hypothesis 層 (`type_alt` が type-II を許さない + `A0` が
     誤 `typePA` 上) の作り直しで、(8.15)/(8.18) と同じ 9163 gate。
   - ⟹ **Pf 本文の ungated frontier は (10.11) 型-II 残余のみ**。
   **2026-07-20 更新**: 9163 gate は全て解消 ((8.15) 型 II / (8.18) 一般化 / (9.11) §9 化 +
   型 II instance、issues 1042/1044/1045 close)。実測の結果 (10.11) 第 2 主張は
   **§15 経由でなく (9.2)/(9.5) の記法で直接述べるのが書籍どおり**で、その最後の一歩が
   まさに本日 landed した (9.11) 型 II 版 ⟹ **issue 1048** に分離して着手する。
   ⚠ §10 章の `pdftotext` は §9 と同じく文字バラけして使用不能 — 原文は PDF 画像で読むこと。

## Lean 側の stale docstring (2026-07-19 に修正済)

- `S12_TypeIICrossIsometryPair.lean` module docstring / `:1347` — 4 フィールドを「sorry で置く」
  → 実際は全て discharge 済・file は sorry-free。
- `S11_MaximalII_III_IV/ThetaCountAssembly.lean:1025` — (9.10) type-II `HU`-Frobenius 節を
  「left `sorry`」→ 実際は本文中で証明済。
- `AxiomsCheck.lean:9906/9925` が (9.11) 系 8 宣言について「upstream `C_eq_cSub` の sorryAx
  債務を引き継ぐ」と注記していた件 → **`#print axioms` で実測し全て allowlist 3 axiom のみと確認**。
  注記を訂正し、8 宣言 (capstone `coherent_sOf_H0Cprime` / `coherent_sOf_H0C` を含む) を pin 済。
