---
id: 1024
slug: pf-11-9-typep-galois-type-three
title: "Pf (11.9): typeP_Galois + Type III 判定 (W2 char body) — 非Galois 矛盾 route"
created: 2026-07-12
---

# Pf (11.9): typeP_Galois + Type III 判定 (W2 char body) — 非Galois 矛盾 route

## 背景

lane-a、1023 ((11.8.6) capstone) 完遂後の R1 pivot (HUB RULING 0101 点3 +
`ft_endgame_plan_2026_07_07.md` R1)。**W2 = 9000 typeP_Galois instance tail** の残り:
u_bound engine (`u_le_cyclotomicQuotient`, 2026-07-09 完) の先の **(11.9) char body**。

**Pf (11.9)** (mmd 04.13 p.66-67、Coq `FTtype34_structure` PFsection11.v:1001-1198):
Hypothesis (11.2) (M maximal, type III/IV)、ζ ∈ 𝒮(HC):
- (a) `(μ₀−ζ)^τ − Σ_{j<p} ω_{0j}^σ ⊥ (Irr W)^σ` (**行0** 射影 pin; (11.8) は列0射影の否定)
- (b) `q > p` — ✅ **repo 済** (`w2_lt_w1_of_hypothesis_H0C_unconditional`, S13_TypeDetermination)
- (c) **(9.7) case (b) = typeP_Galois が成立し M は Type III** ← 本 issue の本体

### Consumer (これが W2 の multi-consumer root gate)

- **c (T-side)**: `T_not_isTypeIV_of_isTypeP1` / `hVcomm : IsMulCommutative V`
  (S16_NonExistenceG/TTypeII.lean:784) — (11.9.c) の「U cyclic → abelian → ¬IV」を T に instantiate。
- **b (S-side, 13.12/13.13/13.15)**: §9 case-(a) 構造 export (a>1, a∣p−1, a∣u) + case-(b) Singer 値。
  ⚠ S は type II ゆえ (11.9.c) は S に直接適用不可 — S-side は §9 export を numeric に使う
  (13.12: p=5 ⟹ a∣4 odd>1 不能 ⟹ case b)。
- 普遍 Type-IV 排除 (`no_typeIV_maximal` 相当) が (c) から従う。

## 証明構造 (Coq mirror、材料の repo 状態 = 2026-07-12 survey 済)

**Route (contrapositive)**: 非Galois (= Clifford case (a)) と仮定 → q ≤ p−1 を導出 → (b) p<q と矛盾
→ Galois → Ū cyclic → U cyclic → U abelian → Type III (¬IV)。

非Galois → q<p の鎖:
1. **(9.8.d)-existence**: λ = Ind_{M'}^M Ind_{HC₁}^{HU} θ̃ irreducible, λ(1)=qa, C≤ker, H⊄ker
   (θ₁ ≠ 1 on block H₁ のみ、C₁ = C_U(H₁) 上自明拡張)。count 不要・単一構成。
2. ψ = μ_j − (u/a)λ (degree 0: μ_j(1)=qu)。⟨τ(μ₀−ζ), τψ⟩ = 0 (Dade 等長 + M-直交)。
3. (9.11) coherence (`coherent_sOf_H0C` ✅) の拡張 c で τψ = c(ψ); (5.8) pin
   (`coherent_sOF_H0C_extension_muColumnSum_pin_of_irr` ✅、ξ:=λ) で c(μ_j) = Ω-col。
4. (11.9.a) 行0射影で ⟨τ(μ₀−ζ), Ω-col k⟩ = ±1 → (u/a)·|⟨τφ, c λ⟩| = 1 → 整数性 → **u = a**。
5. W̄₁ fpf on Ū (`uActionHom_eq_one_of_commute_mulAut` 内部の fixedSubgroup=⊥ を抽出) →
   **q ∣ u−1** → q ≤ u−1 < u = a ≤ p−1 < p。∎

### 材料マップ (survey 2026-07-12)

| piece | 状態 |
|---|---|
| (11.9.b) p<q | ✅ `w2_lt_w1_of_hypothesis_H0C_unconditional` |
| (11.6) C=U′ / (11.7) H₀=⊥ | ✅ `core_structure` / `chief_H0_eq_bot` (S13_CoreStructure、0 sorry) |
| (9.7) dichotomy | ✅ `chiefFactor_clifford_U_dichotomy` |
| (9.11) 𝒮(H₀C) coherent | ✅ `coherent_sOf_H0C` (S13_Orthogonality、unconditional) |
| (5.8) μ-column pin | ✅ `coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` |
| 𝒮(HC) coherent ((11.8)) | ✅ S13_Lemmas113To115:461 |
| ζ 存在 (irr, deg q) + (11.8) 非直交 | ✅ `exists_zeta_residual_not_orthogonal_H0C_of_refuter` |
| Galois → Ū cyclic | ✅ SingerField (`isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm` 系) |
| a ∣ p−1 (generic) | ✅ `card_dvd_sub_one_of_faithful_line` (LineScalarCharacter) |
| **(9.8.d)-existence λ** | ❌ **新規** (単一 Clifford 構成; Coq typeP_nonGalois_characters (d) の存在部) |
| **(11.9.a) 行0射影** | ❌ **新規** (a₀₀=1 Dade 逆数 + Galois 定数性 (3.9.b) + (3.7) 分離 + norm≤q + case 分析) |
| (3.7) 分離性 | ✅ 形あり (`sigmaCoeff_add_eq`、S05_SigmaTrichotomy) — τφ への適用形は要確認 |
| a>1 / a∣u | 容易 (C=U′<U nilpotent / C≤C₁ index) |
| q∣u−1 fpf | 抽出 (S11_ImprimitiveUBound の fixedSubgroup=⊥ + orbit count) |
| nilpotent + U/U′ cyclic → U cyclic | 要確認 (mathlib/Isaacs; Coq cyclic_nilpotent_quo_der1_cyclic) |
| U abelian → ¬TypeIV | ✅ 定義 (TypeIVData.U_not_commutative) |

## やること (上流優先 + 文書順)

- [x] **P1 (9.8.d)-existence** (§9、最上流): ✅ **既 landed と判明** (survey 訂正) —
      `caseA_character_counts` (ThetaCountAssembly:724、sorry-free) の conjunct 4 が
      (9.8.d) count `((p−1)/a)·(|U|/(a|U′|)) ≤ #{qa-irreducibles in 𝒮(H₀U′)}`。
      λ 存在は正値性 ((p−1)/a ≥ 1 ⟸ a∣p−1、|U|/(a|U′|) ≥ 1 ⟸ a∣[U:U′]) から。
      (9.8.b) μ_j 度数 qu / (9.8.c) も同 theorem。CliffordCaseAData が a_pos/a_dvd_p_sub_one 持ち。
- [x] **P2 (11.9.a)** 行0射影 (§11): ✅ **DONE** (S13_TypeIIIGalois、
      `inner_tau_muColumnZero_sub_zeta_rowZero_of_residual_not_orthogonal`、AxiomsCheck 登録済)。
      ⚠ (3.8) trichotomy は転置方向で NC 境界不成立 (NC≤w₁+1 は列 w₁ 本/行 w₂ 本双方を許す) —
      書籍通りの **Galois 定数性 (3.9.b) + (3.7) 分離 + norm≤q + case 分析**が必要。
      case 分析: all-zero は a₀₀=1 で、列枝は h118 ((11.8) refuter) で排除 → 行0枝。
      部品: a₀₀=1/ψ∈ZIrr/‖ψ‖²=w₁+1/vanish-on-V は (10.9)
      `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` (S12_Prop109:369) と同一
      pattern。SHC-coherence 直交 (τ₁(ζ−ζ̄)⊥grid 系) = S12_Prop109:798-993 の SHC_extension 群。

  ### P2 実装計画 (2026-07-12 iteration 2 survey — 材料名 code-level 確定済)

  **Galois toolbox は大部分既存**:
  - ν 存在 (ζ↦ζ^k 実現の ℂ≃+*ℂ): `exists_complexRingEquiv_pow_of_rootsOfUnity` /
    **`exists_complexRingEquiv_pow_and_fixed`** (a-側固定+b-側 k 乗 = CRT 形、行/列の片側固定に使う)
    / `exists_pow_forall_rootsOfUnity` (CyclotomicGaloisAction.lean)。
  - **τ∘ν=ν∘τ**: `dadeIntegralCharacterMap_mapRingEquiv_comm` (S07_CoherenceGalois:51)。
  - **σ∘ν=ν∘σ**: `sigma_mapRingEquiv_comm` (S05_SigmaIsometry:885) +
    `exists_mapRingEquiv_sigma_omega_pow` (:936) + galoisMap-omega-power bridge
    (`exists_intCast_sigma_omega_apply` :1097 の hbridge パターン = (3.9)(c) 実装)。
  - Adams=Galois: `mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr` (CyclotomicGaloisAction:186)。
  - (5.3.b) τ₁ζ⊥grid: **`SHC_extension_inner_alignedOmegaSigma_eq_zero`**
    (S12_Props109To1011:367、coh : IsCoherent tau SHCSet A0 で)。SHC coherence 供給 =
    `SHC_isCoherent` (S12_Prop109:629)。τ(ζ−ζ̄) 橋 = `tau_zeta_sub_conj_eq_SHC_extension` (:968)。
  - ZIrr 内積の ℤ 値: `inner_mem_ZIrr_int` (InducedCharacter.lean、shared ✓)。
  - SHCSet = {ζ ∈ inducedFamily | irr ∧ ζ1=w1} (membership tuple ⟨hζS,hζirr,hζ1⟩ で span cite)。

  **新規に要る sub-lemma 4 本**:
  - [x] **(G1) DONE**: `Hypothesis.mapRingEquiv_muColumnZero_sum` (S12_Prop109、sorry-free) —
    μ₀ = Ind_K^M 1_K route (induce_restrict_certainType_eq @ χ₂=1 + chiRestrict_one_eq_trivial +
    mapRingEquiv_induce)。S06 一般σ版 mu_conj_eq は不要だった。
  - [x] **(G2) DONE (bb79851d)**: shared leaf `GaloisInnerTransport.lean` (等長 + 定数性 engine の
    2 本、sorry-free)。9085 で claim + c 側 dedup を hub へ依頼。旧記述: `inner_mapRingEquiv_eq_of_mem_ZIrr` は
    S16_NonExistenceG/TGapGalois.lean (c 所有、S16-deep import) に在り S13 から import 不可 —
    GaloisCharacter.lean へ hoist (proof は c 版 mirror、`apply_inv_eq_star_of_mem_ZIrr` +
    `inner_mem_ZIrr_int` cite、~30 行)。9000 scan 済 (claim 衝突なし)。hub へ dedup note。
  - [x] **(G3) DONE (iter5)**: `exists_mapRingEquiv_chiFam_left_move` / `_right_move` +
    bridge `sigma_omega_omegaProdChar` (S05_SigmaIsometry、sorry-free)。素数位数 char 群の
    生成性 (zpowers=⊤ + zpow_mod_orderOf) + orderOf ξ = orderOf p (wFst/wSnd 全射 +
    MonoidHom.cancel_right) + exists_mapRingEquiv_sigma_omega_pow で実現。旧設計メモ:
    一般 index-作用は不要 — 必要なのは
    **行0/列0 上の pair-move のみ** (分離性が残りを埋める):
    `∃ σ, mapRingEquiv σ (chiFam (p, κ₀)) = chiFam (p', κ₀)` (p,p' 非自明 W₁-char、κ₀ = 自明
    W₂-char は全 σ 固定 ⟹ **exists_complexRingEquiv_pow_and_fixed 不要**、
    `exists_complexRingEquiv_pow_of_rootsOfUnity` で足りる) + 行0 対称版。
    部品: (i) char-group 素数位数巡回transitivity (p'=p^k, k coprime — w₁ 素数で自動)、
    (ii) chiFam pair の冪 = pair の成分冪 (κ₀ 自明側は固定)、
    (iii) `exists_mapRingEquiv_sigma_omega_pow` (S05:936) で σ 実現。
    定数性本体は **G2 engine `inner_eq_intCast_of_mapRingEquiv_eq_add`** に
    φ=ψ (hφ: mapRingEquiv σ ψ = ψ + τ(ζ−ζ^σ) ⟸ τ-comm (supp 要) + G1 + additivity)、
    correction⊥η' = `SHC_extension_inner_alignedOmegaSigma_eq_zero` ×2 (ζ, ζ^σ ∈ SHCSet ⟸ G4 +
    galoisMap irr + deg σ-固定) を渡すだけ。
  - [x] **(G4) DONE**: `inducedFamily_closedUnderMapRingEquiv` (S12_Core/Hypothesis.lean、
    galoisMap + `ClassFunction.mapRingEquiv_induce` (S08_CaseBCoherence 既存) で ~30 行、sorry-free)。
  - **(G1 補足)**: c の `primeTIred_zero_mapRingEquiv` (TGapGalois:71) が「prTIred 0 = Ind 1 は
    σ-固定」を T-side で実証済 — M-side μ₀ 列も同 route (列0和 = induce of trivial 形に還元 →
    mapRingEquiv_induce + trivial σ-固定) が本命。S06 一般σ版 mu_conj_eq は不要の可能性大。
    c の `inner_eq_intCast_of_mapRingEquiv_eq_add` 相当は G2 leaf に hoist 済 — c は
    `tSideDadeMap_mapRingEquiv_bridge` で (11.9)(a) の T-side Galois bridge を並行構築中
    (M-side とは world 別、重複なし)。

  ### C-層進捗 (iter5-6、2026-07-12)

  - [x] **C0 DONE (66719f45)**: S13_TypeIIIGalois.lean 新設 — mapRingEquiv_mem_SHC_stratum /
    tau_zeta_sub_mapRingEquiv_eq_SHC_extension / 補正⊥grid。
  - [x] **C0b/C1/C2 DONE (462659c1)**: w1_prime_of_typeIIIorIV (TypeV は common 欠落ゆえ III/IV
    限定) / bridge σ(τφ)=τφ+τ(ζ−σζ) / **列0 定数性 a_{i'0}=a_{i0}** / **行0 定数性 a_{0j'}=a_{0j}**。
    (ρ0,κ0)=(1,1) anchor は orthonormal 単射性で。
  - [ ] **残 = (11.9.a) 最終組立**: a₀₀=1 (既存 pattern) + 分離性 sigmaCoeff_add_eq (3.7) を
    aligned-grid 形へ + Bessel (Σa²+‖χ‖²=w₁+1、χ≠0 は ⟨ψ,τ(ζ−ζ̄)⟩=−1) + 整数 case 分析
    (a₁₁=0 → a₀₁=1−a₁₀ → a₁₀≠0 ⟹ 列0形 ⟹ h118 矛盾 → a₁₀=0,a₀₁=1) → 行0射影 conclusion。
    その後 P3 (c)-組立へ。

  **a_aut + 組立** (書籍 (a) mirror):
  ν(τφ) = τφ + τ(ζ−ζ^ν)、τ(ζ−ζ^ν) = τ₁ζ−τ₁ζ^ν ⊥ grid ⟹
  a(νη) = ⟨ν(τφ), νη⟩ (G2) = ⟨τφ + ⊥grid 項, νη⟩ = a(η) ⟹ 行/列定数性
  a_i0 = a₁₀ (i≠0)、a_0j = a₀₁ (j≠0)。分離 (`sigmaCoeff_add_eq`) で a_ij = a_i0+a_0j−1。
  Bessel: Σa² + ‖χ‖² = ‖ψ‖² = w₁+1、χ≠0 (⟨ψ,τ(ζ−ζ̄)⟩=−1≠0 + τ(ζ−ζ̄)⊥grid) + ‖χ‖²∈ℕ ⟹
  Σa² ≤ w₁。Σa² = 1+(w₁−1)a₁₀²+(w₂−1)a₀₁²+(w₁−1)(w₂−1)a₁₁² (a∈ℤ)。
  case: a₁₁≠0 ⟹ (w₁−1)(w₂−1)≤w₁−1 ⟹ w₂≤2 ✗ (w₂≥3 奇素数)。a₁₁=0 ⟹ a₀₁=1−a₁₀。
  a₁₀≠0 ⟹ (w₁−1)a₁₀²≥w₁−1 ⟹ a₀₁=0 ⟹ a₁₀=1 ⟹ X=列0 ⟹ h118 矛盾。∴ a₁₀=0、a₀₁=1 = 行0 形。∎
  新 leaf = `S13_TypeIIIGalois.lean` (import: S13_Orthogonality + S12_Props109To1011 +
  S07_CoherenceGalois + S06_CertainTypeConjugation)。着手順 = G2 (shared hoist) → G4 → G1 → G3 →
  本体。
- [x] **P3 (c) 組立**: ✅ **DONE (2026-07-12、commits 775f2d86/678b6826/29b08747/700ba71f+)** —
      下記「納品 (P3 完了)」参照。
  - [x] **q∣u−1 部品 landed (2026-07-12)**: `card_uActionHom_range_modEq_one` (u ≡ 1 mod q、
        S11_ImprimitiveUBound、sorry-free・build 一発 green) + 抽出補題
        `fixedSubgroup_quotient_uActionKer_eq_bot` (C_Ū(W̄₁)=1)。AxiomsCheck 登録。
  - 残: nilpotent + U/U′ cyclic → U cyclic (mathlib/Isaacs 確認 — Coq
        cyclic_nilpotent_quo_der1_cyclic 対応)、u=a pin 議論 (S11↔S13 world bridge)、組立。
- [x] consumer への配線 note = 下記納品 section (2026-07-12)。AxiomsCheck 登録は **deferred**:
      P3 組立群は `coherent_sOf_H0C` (lane-b (9.11.2) refuter) +
      `exists_zeta_residual_not_orthogonal_H0C_of_refuter` (§14 Sibley glue (6.7)/(5.8)) を
      推移 cite するため sorry-free でなく、**trigger = これら上流の sorry-free 化着地時**に
      keystone とまとめて登録 (sorried-cite 規約)。

## u=a pin 設計 (iter10 確定 — 実装は次 iteration)

**⟨τφ, c μ_j⟩ = ±1 は一般 (5.8) port 不要** — b の (5.5) `coherent_extension_eq_sum_memberRFamily`
(S11_NineElevenPairAdjoin:342、cite 可) で:
1. ζ ∈ SOf HC: refuter 内 pattern 再利用 (`SOf_secondDerived_eq` + `secondDerived_eq_HC` —
   deg-w1 irr ⟹ M″=HC kernel)。
2. λ 家族橋: chars.SOf (H0⊔U′) → sOf s11Setup H0C (H0C = H₀⊔C、C=U′ (11.6)、def 揃え)。
3. c := coherent_sOf_H0C; T := sOf H0C ⊆ sOf H0Cprime (kernel antitone) で (5.5):
   c μ_j = Σ_{α∈E} α、E ⊆ R(μ_j).imageSet = certainTypeR imageSet
   (`sOf_H0Cprime_memberRFamily_imageSet_of_col`、S11_NineElevenAlphaBound:285)。
4. ‖c μ_j‖² = w₁ = |imageSet| ⟹ E = 全体; imageSet ↔ aligned 列
   (`certainTypeOmegaSigma_muColumnChar_eq_aligned` — 所在確認要) ⟹
   ⟨τφ, c μ_j⟩ = Σ_α ±δ_{row0} = ±1 ((11.9.a) 行0形)。
5. ⟨φ,ψ⟩=0 (SOf_HC_inner_sOf_H0C_eq_zero + μ₀⊥λ irr-distinct)、ψ = μ_j − (u/a)•λ
   supported ⟹ τψ = cψ ⟹ ±1 = (u/a)⟨τφ,cλ⟩ ⟹ **u = a** (整数性)。
6. a>1: u=a=1 ⟹ U=C=U′ nilpotent ⟹ U=⊥ ✗ (nontrivial)。q∣u−1 (landed) ⟹
   q ≤ u−1 < a ≤ p−1 < p、(11.9.b) p<q ✗ ⟹ **caseB (typeP_Galois)**。
7. 帰結: Ubar_cyclic (caseB field) + C=U′ ⟹ U/U′ cyclic + U nilpotent ⟹ U cyclic
   (**gap: nilpotent+cyclic-abelianization⟹cyclic** — mathlib/Isaacs 確認 or 新規 ~30 行:
   Frattini H = U′·Φ... 標準: G' ≤ Φ(G) nilpotent + G/G' cyclic ⟹ G/Φ cyclic ⟹ G cyclic)
   ⟹ IsMulCommutative U ⟹ ¬TypeIV。⚠ TypeIVData.typeP ≠ hyp.typeP — U の conjugacy
   独立性 bridge 要 (MaximalSubgroupTypeConj の TypePData.conj 機構を確認)。

### ★ u=a pin 完全証明 (iter12, 2026-07-12): `caseA_u_eq_a_of_residual_not_orthogonal`

**landed** (S13_NonGaloisExclusion.lean 新 leaf、sorry-free、build green): caseA + ζ/h118 下で
`(mkSection11CharacterData …).u = caseA.a`。設計は iter10-11 の (5.5)+conj-対合 route を
**dichotomy trick で強化**したもの:
- **J3 の解決**: `extension_mapRingEquiv_comm` は S⊆既約を要求し μ (可約) に不適用 — 代わりに
  `by_contra u≠a` (→ m := u/a ≥ 2) 分岐で **conj-等変性が整除からタダで出る**:
  次数-0 の ζd := qa•μ − qu•λ は A₀-supported → c は τ に一致 → `tau_mapRingEquiv_comm` で
  qa·D = qu·D′ (D := conj(cμ)−c(μ̄)、D′ := conj(cλ)−c(λ̄))。D の R-grid 係数 ∈ {−1,0,1}、
  右辺は m≥2 の倍数 (D′∈ZIrr の整数係数) ⟹ **全係数 0**。μ̄-側の (5.5)/dispatcher/columnSum
  単射性は一切不要 (相補性 f_p = e_p−1 は μ-側 image_eq から)。
- **J4**: certainTypeRImage_conj (J0/J2) + rowInv_zero + J∘J=id で
  [R(Jp)∈E]+[R p∈E]=1 → p=(false,0) で exactly-one。
- **t=±1**: (11.9.a) 行0射影 + 世界橋 certainTypeOmegaSigma_muColumnChar_eq_aligned
  (χ₂⁻¹-列は新 helper `exists_muColumnChar_inv` の kinv 経由) → t = ±δ = ±1。
- **pin**: ψ = μ − m•λ (deg 0) の Dade pairing 0 = t − m·s → m ∣ 1 ✗ m≥2。∎
- 新 helper (S12、axiom-clean・AxiomsCheck 登録済): `muColumnChar_zero`、
  `exists_muColumnChar_inv`。keystone 本体は `coherent_sOf_H0C` 経由で lane-b (9.11.2)
  refuter sorry を推移 cite (sorried-cite 規約; 着地時に AxiomsCheck 登録)。
- P1 の λ existence/a∣u は前 iteration で landed (`caseA_exists_irreducible_qa`/`caseA_a_dvd_u`)。

**残り (P3 続き)**: u=a → 非Galois 矛盾の組立 (q∣u−1 landed + a∣p−1 + u=a ⟹ q≤p−2<p vs
(11.9.b) p<q) → caseB 帰結 → Ū cyclic + C=U′ ⟹ U cyclic (nilpotent+cyclic-ab gap) →
IsMulCommutative U → ¬TypeIV → `isTypeIII_of_isTypeIIIorIV`。

### iter11 深掘り (歴史): (5.5) 単独では不足 — t=0 退化の排除が要

`certainTypeR.imageSet` = **2w₁ 員** (χ₂-半分 ±δ·ω^σ_{χ₂,i} と χ₂⁻¹-半分、
`certainTypeRImage`、image_eq: τ(μ−μ̄) = Σ 全体)。(5.5) は c μ_j = Σ_E (|E|=w₁) までで、
E が行0 対 {f0,t0} を 0 or 2 個含むと t := ⟨τφ, c μ_j⟩ = 0 に退化 (u=a 出ず)。
確定済: ⟨τφ,f0⟩ + ⟨τφ,t0⟩ = ⟨φ, μ−μ̄⟩ = 0 ⟹ 両者 = ±1 逆符号 ⟹
**E∩{f0,t0} = ちょうど1 ⟺ t = ±1**。u=a への整数論は t=±1,±2 どちらでも OK
(a·t = u·x、a∣u、u/a 奇 ⟹ u=a; u odd/a odd は u_odd + a∣u)。

**t≠0 排除 route (conj-対合)**: c の conj-等変性 (`IsCoherent.extension_mapRingEquiv_comm`
@ conjAe、family conj-closed ✓) ⟹ Σ_E conj α = c μ̄_j = c μ_j − τ(μ−μ̄) = −Σ_{Eᶜ} α。
conj は 2 半分を交換し行 0 ↔ 行 0 (−0=0) ⟹ conj f0 = ±t0 ⟹ E の f0/t0 選択が
Eᶜ 側と結ばれ exactly-one が出る (符号 bookkeeping は certainTypeRImage の δ-規約次第 —
要精査; 破綻時 fallback = Coq PFsection5 coherent_prDade_TIred (no-mix 完全版) port)。
grid-conj 部品: `certainType_columnSum_conj` / mapRingEquiv conj 系 (S06_CertainTypeConjugation)。

## 納品 (P3 完了、2026-07-12 lane a)

S13_NonGaloisExclusion.lean (1035 行、leaf 内 sorry 0) に (11.9.c) 全チェーン:

| theorem | 内容 |
|---|---|
| `not_cliffordCaseA_of_hypothesis` | 非Galois 排除 (keystone u=a + u≡1 mod q + a∣p−1 + (11.9.b); u=1 枝は U_noncentral_on_quotient) |
| `U_isCyclic_of_hypothesis` | caseB Ū cyclic (Singer) + ker=cSub=C=U′ ((11.6)/(11.7)、C_eq_cSub) + U nilpotent + **9086 engine** |
| `U_isMulCommutative_of_hypothesis` | IsMulCommutative ↥hyp.base.typeP.U |
| `isMulCommutative_typePData_U_of_typePData_U` | TypePData witness 間 U-可換性 transfer (Schur–Zassenhaus 共役) |
| `not_isTypeIV_of_hypothesis` / `isTypeIII_of_hypothesis` | Hypothesis (11.2) 下の Type III 判定 (Coq FTtype34_structure (c)) |
| **`not_isTypeIV_of_mem_maximalSubgroups`** | **普遍 Type-IV 排除 per-M 形 (前提 = hG + M maximal のみ)** |
| `no_typeIV_maximal` | 同 ∃-形 (no_typeV_maximal の対、FT spine 用) |

shared infra: `OddOrder/GroupTheory/NilpotentAbelianization.lean` (issue 9086、sorry-free、
AxiomsCheck 登録済) — nilpotent + cyclic abelianization ⟹ cyclic。

### consumer 配線

- **c (T-side, S16 TTypeII:784 hVcomm)**: `T_not_isTypeIV_of_isTypeP1` の結論は
  **`not_isTypeIV_of_mem_maximalSubgroups hG hyp.base.T_maximal` の直 cite で丸ごと discharge**
  (hVcomm sorry・V-可換性・isMulCommutative_typePData_U_of_V 経由は不要になる;
  import + S13_NonGaloisExclusion は S16 から cycle-safe)。T-side instantiate 作業消滅。
- **b (S-side 13.12/13.13)**: §9 case 構造 export は従来通り (S は type II ゆえ本定理の対象外、
  numeric export = caseA_character_counts 系を直接使う)。
- 推移 sorry の所在: `coherent_sOf_H0C` ← lane-b (9.11.2) refuter;
  refuter core ← §14 Sibley glue (6.7)/(5.8)。これらが埋まれば (11.9.c) は端から端まで sorry-free。

## 完了条件

`isTypeIII_of_isTypeIIIorIV` (または同等の普遍 Type-IV 排除) が S13 で sorry-free、
c の hVcomm が cite 可能な signature で供給される。

## 参照

- 書籍: mmd 04.13 (11.9); Coq PFsection11.v:990-1198 (`FTtype34_structure`)、
  PFsection9.v:845- (`typeP_nonGalois_characters`)
- repo: S13_Orthogonality (pin/refuter)、S13_CoreStructure ((11.6)/(11.7))、
  S13_TypeDetermination ((11.9.b))、S11_ImprimitiveUBound (fpf 部品)、issue 9000 (σ-theory engine)
- issues: 1012 ((9.8) counts — P1 と同根、B1 quotient bridge は §11 では H₀=⊥ で不要)、
  0101 (R1 pivot)、`notes/meta/ft_endgame_plan_2026_07_07.md` W2

## 🧭 hub フォローオン (2026-07-12 監視 tick, 9077 RULING #3) — Type-IV 補題を S16 下 leaf へ抽出

a が landing した `not_isTypeIV_of_mem_maximalSubgroups` 等の低レベル Type-IV/U-abelian 補題を
lane c が TTypeII (S16) の `hVcomm` discharge に cite したいが、`S13_NonGaloisExclusion` が S16 を
transitively import (S13_TypeDetermination 経由) するため **file-level cycle** で cite 不可
(hub 検証済)。**hub 裁定 = 選択肢 (A): 当該 5 補題を S16-free な新 leaf (例 `S13_TypeIVExclusionCore.lean`,
import は S13_TypeIIIGalois + S11_MaximalII_III_IV + NilpotentAbelianization のみ = closure に S16 無し)
へ抽出。** 詳細タスク・要検証点 (proof が S13_TypeDetermination 固有内容を使うか) = issues/9077
「HUB RULING #3」節。**割当 = lane a** (territory 内)。landing で c の hVcomm sorry が 1 本消える。
