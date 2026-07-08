---
id: 9075
slug: s07-pivot-coherence-norm-general
title: "S07 (5.7) norm-general uniform coherence: pivot_coherence port (lane-a claim)"
created: 2026-07-08
---

# S07 (5.7) norm-general uniform coherence: pivot_coherence port (lane-a claim)

## claim (lane-a, 2026-07-08)

**lane a が build する** (caseB (9.11) の唯一の残 gap を閉じる shared S07 infra)。
重複防止のための claim。b の caseA (S11_NineElevenCoherence) は irr-only 版
(`coherent_subset_of_constant_degree`, landed) + weighted adjoin を使う設計で非衝突
(base S1 = deg-qa 既約)。

## 背景 (発見 2026-07-08, 1019 update⁸⁵)

- Coq (9.11) `Ptype_core_coherence` の **Galois(=caseB) 枝は
  `apply: uniform_degree_coherence scohS0` — 家族 𝒮(H₀C′) 全体 (可約 μ 込み) に一発**
  (PFsection9.v:1510-1513)。count・pair-chain・anchor 不要。
- Coq `uniform_degree_coherence` (PFsection5.v:1234) は **norm N 一般**
  (N = ⟨χ₁,χ₁⟩、R-datum size 2N、:1256-1264)。
- Lean 港 `coherent_of_constant_degree` / `coherent_subset_of_constant_degree` は
  **norm-1 (irr) 限定** (`hirr : ⟨ζ,ζ⟩ = 1`) — 制限 port。
- ⟹ lane-a の caseB fold が要求する **hDeg (2 < |irr-cut|) は route 人工物**
  (Coq/教科書が証明しない count; |cut| = 2 corner で偽の恐れ)。§9 count で埋めるのは誤り。
  正 = norm-general (5.7) を port して全族適用。

## やること

1. **`pivotCoherence`** (Coq `pivot_coherence` PFsection5.v:588 の S07 版):
   pairwise-orthogonal S + pivot η₁ ∈ S + ζ₁ ∈ ℤ[Irr G] + (∀ η ∈ S∖{η₁}: η(1) = η₁(1)
   [uniform 特化 a≡1] ∧ ⟨τ(η−η₁), ζ₁⟩ = −⟨η₁,η₁⟩) + ⟨ζ₁,ζ₁⟩ = ⟨η₁,η₁⟩ → IsCoherent。
   **明示式で構成** (基底 freeness 不要): `ν φ := s(φ) • ζ₁ + τ(φ − s(φ) • η₁)`、
   `s(φ) := ∑ᵢ ⟨φ,ηᵢ⟩/Nᵢ` (pairwise 直交で ℤ[S] 上 ℤ-値 = 係数和)。
   - extends: φ ∈ ℤ[S,A] → φ(1)=0 → s(φ)=0 → νφ = τφ (即)。
   - inner_eq: 展開 + pivot 条件 + supported-span isometry。
   - ZIrr: ζ₁ ∈ ℤ[Irr G] + hZIrr (τ(a−b) ∈ ℤ[Irr G])。
2. **(5.7) norm-general 版** `coherent_of_constant_degree_normGeneral`:
   ζ₁ の構成 (Coq :1265-1330 haveX = subcoherent_split/norm (5.4) minimality、
   X = R(χ₁) の半分和、⟨X⟩=N、XDspec ∀ξ ⟨X, τ(χ₁−ξ)⟩=N)。
   degenerate case S = {χ₁,χ̄₁}: X := take N (R χ₁)。
3. caseB 適用: 𝒮(H₀C′) 全体 (hunif [landed] + pairwise-orthogonal
   [inducedKernelFamily_pairwise_orthogonal] + conj-closed [sOf_closedUnderConjugate] +
   no-real [odd] + R-datum [S06.certainTypeR (μ) / Dade decomposition (irr)]) →
   `caseB_coherent_sOf_H0Cprime` を rewire (hDeg 引数を撤去)。

## 完了条件

caseB (9.11) `caseB_coherent_sOf_H0Cprime` が hDeg 無しで閉じ、fold 版は下流互換のため
残置 or 撤去 (assembly 差し替え)。#print axioms で §13 core gate 以外 sorry-free。

## ✅ ENGINE 完成 (2026-07-08、S07_PivotCoherence、全 sorry-free)

part 1–2 (= issue step 1–2) 完了。norm-general (5.7) engine が丸ごと landed:

- **`pivotCoherence`** (part 1, prior commit): pivot η₁ + partner ζ₁ → IsCoherent。
- **`exists_pivotPartner_spec`** (part 2a): 単一 ξ の haveX step (norm squeeze
  ‖Y₁‖²≤⟨ξ⟩≤‖X₂‖²≤‖Y₁‖² → Y₁=X₂ + (5.4.b) subset-sum)。
- **`exists_pivotPartner`** (part 2b): common-X 完成 (anchor ξ₁ 固定、member 4 場合分け
  χ̄₁/ξ₁/ξ̄₁/generic、‖X−X'‖²=0 で X 一意)。raw per-member R-family を取る。
- **`uniform_degree_coherence_of_families`** (part 2c 主): raw family データ →
  Nonempty (IsCoherent)。**任意長 R(η) を受理** (既約=2, 可約 μ=2q)。nonzero ノルムは
  hnr から導出。← **caseB entry point**。
- `uniform_degree_coherence_of_subcoherent`: 全既約 S07.Hypothesis 用の薄ラッパー
  (2元 difference_image → norm 1 強制ゆえ caseB には不使用)。

全て #print axioms = [propext, Classical.choice, Quot.sound]。

## 🔧 残 = step 3 caseB rewire (in progress)

`caseB_coherent_sOf_H0Cprime` (S13_CoreStructure:1467、lane-a 所有、consumer 0 の gated
endpoint、hDeg 未供給) を `uniform_degree_coherence_of_families` 一発適用に置換して hDeg 撤去。
要 assemble (𝒮(H₀C′) on hyp.base.tau):
- R-family dispatcher: member dichotomy (caseB_sOf_member_dichotomy: 既約 d or μ-column k)
  → 既約=Dade decomposition / μ-column=certainTypeR-on-tau (columnImageFamilyCohFree 系)。
- cross-ortho 3 combo: μμ (certainTypeR_imageSet_orthogonal_certainTypeR) /
  μ-irr (certainTypeR_imageSet_orthogonal_dadeOfDiff) / irr-irr
  (memberExtensionDecomposition/inducedKernelFamily 系)。
- isometry = hyp.base.tau on A₀-supported / ZIrr diffs / supported diffs / hunif (degree) /
  pivot = 既約 member (norm 1 ⟹ hN 自明) / second member (card ≥ 2)。

### 🔬 feasibility 調査 (2026-07-08、直接確認) — GO、ただし multi-lemma assembly

rewire は **mixed corner のみ**が対象 (all-reducible corner は既に `coherent_sOf_H0Cprime_of_allReducible`
で hDeg 不要、S13_CoreStructure:1500)。mixed corner の既約 pivot χ₁ (norm 1、
`IsIrreducibleCharacter.inner_self_eq_one` CharacterProduct:195 で hN 自明)、η₂ = χ₁.conj。

**crux = μ-column R-family の CharacterParameters threading (既存 chain-fold とは別データ)**:
- 既存 `caseB_coherent_sOf_H0Cprime_of_mixed` は `sixTwoDecompositionData` の **pair-adjoining**
  データ (Da for break + per-member D) を使い、CharacterParameters を**回避**して chain 折込。
- norm-general engine は **flat per-member R-family** を要求 → μ-column には
  `Hypothesis.columnImageFamilyCohFree` (S12_MaximalIII_IV_V_Core:5661、on hyp.tau、sorry-free) が
  必要で、これは `params : CharacterParameters` + 具体 column index j,j' + conjugate pairing
  `hconj : (∑ᵢ μ_ij).conj = ∑ᵢ μ_ij'` + hδpm/hδj/hzS/hz1/hzconj を要求。
- **CharacterParameters は `Hypothesis.exists_charParameters` (S12:3057) で hG+hyp から構成可能**
  (params.mu = muGrid、params.zeta = (10.2) degree-w₁ irr)。← go/no-go = GO。
- 既約 R-family + isometry + ZIrr + supported は `sOf_degreeSubfamily_isCoherent`
  (S13_MaximalIII_IV:1967) 内で既に hyp.base.tau 上で使用済 (landed)。

**残 impedance**: (i) 抽象 `columnSum (muColumnChar k)` ↔ 具体 `∑ᵢ muGrid i j` 形の同定 +
conjugate column j' の取得 (caseBPair は μ̄_k = μ_{k⁻¹} を使用、exists_conj_column 系)。
(ii) params.delta ↔ muColumnSign の接続 (hδj)。(iii) params.zeta ∈ Sset ↔ inducedFamily 橋 (hzS)。
(iv) cross-ortho 3-combo の hyp.base.tau 版 (μμ/μ-irr は S06 に σ 版、transport 要確認;
irr-irr は inducedKernelFamily 系)。→ several 中間補題として段階 land 予定。

### 🎯 EXACT WIRING MAP (subagent survey 2026-07-08 — 全部品確定、`columnImageFamilyCohFree` 不要)

**決定的**: `hyp.base.tau` = `dadeIntegralCharacterMap h.dade0 h.tau` が**定義的一致**
(toHypothesis46 の dade0/tau field 展開、S12:1109-1110)。→ `certainTypeR` も
`dadeOrthonormalCharacterImageFamilyOfDiff` も **seam なしで hyp.base.tau に直接 land**。
`.Orthogonal` = `∀α∈R,∀β∈R', inner=0` (定義的) ゆえ imageSet_orthogonal 系が直接 hRorth。
**pivot = μ₁ = columnSum(muColumnChar ⟨1,_⟩) を採用すれば corner 分割不要・全族一発**
(μ₁ 常在、self-norm w₁ ∈ ℕ ⟹ hN)。

| engine 入力 | 部品 (file:line) | 備考 |
|---|---|---|
| R(μ-col) | `S06.certainTypeR` (S06_CertainTypeCoherence:639) | χ₂:=muColumnChar k。hχ₂=muColumnChar_ne_one、hdeg=columnSum_inv_apply_one.symm |
| R(irr) | `S07.dadeOrthonormalCharacterImageFamilyOfDiff` (S07_Coherence:5837) | hyp:=base.dadeData.dade、hconj:=base.hconj。template=`irrFamilyMemberOrthoDatum` (S13:2761) |
| pairwise | `S08.inducedKernelFamily_pairwise_orthogonal` (S08_SixTwoGeneral:166) | sOf→SOf 橋 (sOf_subset_SOf S13:361 + SOf_eq) |
| conj-closed | `S13.sOf_closedUnderConjugate` (S13_MaximalIII_IV:378) | ✓ |
| no-real | `S08.inducedKernelFamily_hasNoRealCharacters` (S08_SixTwoGeneral:207) | Odd M |
| isometry | `S12.Hypothesis.tau_inner_eq_of_supported` (S12_Core:3628) | support_subset_of_mem_zSupportedSpan (S07:59) |
| τ(a−b)∈ZIrr | `dadeIntegralCharacterMap_mem_ZIrr_of_supported` (S07_Coherence:5633) + `inducedKernelFamily_mem_ZIrr` (S08:238) / `columnSum_mem_ZIrr` (S12_Counts:1945) | compose |
| supp diff | `S13.sOf_anchor_diff_support` (S13_MaximalIII_IV:3001) | (a−χ₁)=(a−μ₁)−(b−μ₁) |
| μ×μ ⊥ | `S06.certainTypeR_imageSet_orthogonal_certainTypeR` (S06:685) | χ₂≠χ₂', χ₂≠χ₂'⁻¹ glue |
| μ×irr ⊥ | `S13.certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP` (S13_MaximalIII_IV:2622) | conj-swap for irr×μ |
| irr×irr ⊥ | `S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` (S08_CoherenceCorePart1:1650) | 4 inner=0 from pairwise |
| degree | `S13.caseB_forall_mem_sOf_H0Cprime_apply_one_eq_qu` (S13_CoreStructure:1432) | **d=q·u** |
| h1A | `S12.one_notMem_A0 hyp.base` (S13_SixTwoBridge:63) | ✓ |
| pivot/2nd | `S13.columnSum_muColumnChar_mem_sOf_H0Cprime` (S13_CoreStructure:1391) + μ₁.conj | ~3 line glue |

唯一の新規 = **hRorth の 3-way dispatch** (μ×μ/μ×irr/irr×irr、member の ⟨·,·⟩=0 で branch 選択)
+ R-family dispatcher (dichotomy で irr/μ-col 判定、μ-col は φ=columnSum(k) transport)。

## 参照

- issues/1019 update⁸⁵ / Coq PFsection5.v:588 (pivot), :1234 (5.7), :863/:881 ((5.4))
- PFsection9.v:1510-1513 (Galois 枝)

## 🔬 part 2 実装 plan (2026-07-08 在庫確認済 — 全 (5.4) 部品 landed、route (a) 採用)

### 在庫 (S07_Coherence、全て sorry-free)
- `CharacterPsiDecomposition τ χ ψ` (:1212) = (5.4) setup (R(χ) family + τ₁ + split
  τ₁(χ−ψ) = X−Y、X ∈ ℤ[R(χ)] coeff 付き、Y ⊥ R(χ)、直交 scalar 3 本)。
- **`CharacterPsiDecomposition.ofProjection`** (:1290 付近) = subcoherent_split の port:
  `htau1_mem : (χ−ψ)^{τ₁} ∈ ZIrr G` から X/Y/coeff を射影で**計算** (posit しない)。
- `inner_self_chi_re_le_inner_self_X` = (5.4.a) ‖X‖² ≥ ‖χ‖²。
- **`norm_eq_and_X_eq_sum_of_norm_Y_ge`** (:1571) = (5.4.b): ‖Y‖²≥‖ψ‖² → 等号 +
  **X = ∑_{α∈E} α、E ⊆ R(χ)、|E| = ‖χ‖²** (coeff ∈ {0,1} tightness)。
- `eq_sum_of_psi_eq_zero` (:1624) = (5.5) (ψ=0: Y=0, τ₁χ = X = E-sum)。
- 生射影: `exists_intProjection_of_orthonormal_ZIrr` (residual 二次 split 用)。
- subcoherent `Hypothesis` (S07 :定義): fields = tau_isometry_diff / conjugate_closed /
  no_real_characters / pairwise_orthogonal / difference_image (per-member
  CharacterDifferenceImage = R-datum) / difference_images_orthogonal ((5.2.e))。

### step 1: `exists_pivot_partner` (S07_PivotCoherence 追記)
statement: hyp : S07.Hypothesis S A + hSfin + 等次数 + h1A + (χ₁ ∈ S) →
`∃ ζ₁ ∈ ZIrr G, ⟨ζ₁,ζ₁⟩ = ⟨χ₁,χ₁⟩ ∧ ∀ η ∈ S, η ≠ χ₁ → ⟨τ(η−χ₁), ζ₁⟩ = −⟨χ₁,χ₁⟩`
(Coq haveX/XDspec :1265-1330 mirror; D ξ := τ(χ₁−ξ)、⟨τ(η−χ₁),X⟩ = −⟨D η, X⟩)。
- (o) N := ⟨χ₁,χ₁⟩ ∈ ℕ (genuine character norm; hyp から Num.nat — inner_self 自然数性は
  `Cnat_cfdot_char` 対応の repo 補題を確認)。|R(χ₁)| = 2N (dotD + orthonormal)。
- (a) **χ̄₁ 条件は X ⊆ R(χ₁)-部分和なら自動**: ⟨τ(χ̄₁−χ₁), X⟩ = −⟨∑R, ∑E⟩ = −|E| = −N。
- (b) degenerate S ⊆ {χ₁, χ̄₁}: X := 任意の N-元部分集合の和 (Finset.exists_subset_card?
  |R|=2N ≥ N)。
- (c) haveX (ξ ∈ S∖{χ₁,χ̄₁}): D₁ := ofProjection (R(χ₁), τ₁:=τ, iso from
  tau_isometry_diff [ℤ[χ₁−χ̄₁, χ₁−ξ] ⊆ ℤ[S,A]: 等次数差 supported]、直交 scalar =
  pairwise_orthogonal) → split D ξ = X_ξ − Y₁。Y₁ を R(ξ) へ生射影 → X₁ − Y。
  norm 勘定: ⟨Y₁⟩ = ⟨X₁⟩+⟨Y⟩ ≥ ⟨ξ⟩ ((5.4.a) 第 2 instance via ofProjection (ξ, χ₁) 型
  or 直接) → (5.4.b) D₁ → ⟨X_ξ⟩=N ∧ X_ξ = E_ξ-sum ∧ ⟨X_ξ, D ξ⟩ = N (tau1_image 展開 +
  Y₁ ⊥ X_ξ)。
- (d) common X: ξ₁ 固定、X := X_{ξ₁}; 他 ξ: ⟨X − X_ξ⟩ = 0 (Coq :1315-1330 の
  dotD/oR 計算 — R(χ₁)⊥R(ξ) は difference_images_orthogonal、dotD =
  N + ⟨ξ₁,ξ⟩ は tau_isometry_diff)。
- 結論 ∀η: η = χ̄₁ → (a); else Xi_spec (c-d)。

### step 2: `uniform_degree_coherence_of_subcoherent` (norm-general (5.7) 完成)
hyp subcoherent + hSfin + 等次数 + h1A + hsuppdiff + (∃ η₂ ∈ S, η₂ ≠ η₁ 用の
nonempty/conj-closed/no-real から pair) → Nonempty (IsCoherent τ S A)
:= exists_pivot_partner + pivotCoherence (hiso := tau_isometry_diff 変換、
hZdiff := 差の ZIrr [isometry→ZIrr field?  hyp の tau_isometry_diff は isometry のみ —
ZIrr 像は `difference_image`.image_eq 経由 or 別 field — 要確認: Coq IZtau = isometry+to
ℤ[Irr]; Lean Hypothesis に Ztau 対応 field があるか grep)。

### step 3: caseB rewire (S13_CoreStructure)
𝒮(H₀C′) 上の S07.Hypothesis 構築: R-datum = μ: S06.certainTypeR / irr:
dadeOrthonormalCharacterImageFamilyOfDiff (landed)、cross-ortho =
certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP (S13:2828 landed) + irr-irr 側
(memberExtensionDecomposition 系)、isometry = Dade (dadeICM_inner_eq...)。
→ `caseB_coherent_sOf_H0Cprime` から hDeg/∃-irr 分岐を撤去し全族一発に置換
(all-reducible corner も統合可; fold は landed 資産として残置)。
