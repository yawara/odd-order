---
id: 1009
slug: pf-10-6-summed-isometry-norm-bound
title: "Pf (10.6): summed isometry μ_j^τ₁=δ∑ω_ij^σ + ζ^τ₁ norm bound (gated on §5 (5.8))"
created: 2026-06-22
---

# Pf (10.6): summed isometry + ζ^τ₁ norm bound

## 背景

(10.5) Dade-image identity 締結 (issue 1007/1008 CLOSED) に続く文書順次ターゲット。
`tau1_values_and_norm_bound` (`S12_MaximalIII_IV_V.lean:3521`, sorry) が (10.6) の Lean 化で、
2 つの conjunct を持つ:
1. **(10.6.a) summed isometry**: `∀ j ≠ 0, coh.tau1 (∑_i μ_ij) = δ • ∑_i ω_ij^σ`。
2. **(10.6.b) norm bound** (= opaque `CharacterParameters.zeta_tau1_norm_bound : Prop`, 現 `True`):
   `g ∈ G − Ã(M)` で位数 prime to w₁ ⟹ `|ζ^τ₁(g)| ≥ 1`。

原文 = `references/peterfalvi/04.12_*.mmd` (10.6) (pp. 58-63)。

## ⚠ gate: Peterfalvi (5.8) が未形式化

**(10.6.a) は Peterfalvi (5.8) [§5 Coherence, `references/peterfalvi/04.7_pp_25_29_Coherence.mmd:119`]
に gated**。原文証明:
```
1 = (α_ij, μ_j − dζ̄) = (α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = (δ(ω_ij^σ − ω_i0^σ), μ_j^τ₁)   [by (10.5)]
→ by (5.8), μ_j^τ₁ = δ ∑_i ω_ij^σ.
```
(5.8) は coherence isometry τ₁ の下で column-character μ_k の像を決定する §5 結果 (2 ケース、複雑な
statement)。**S07_Coherence.lean に未形式化** — 本 issue の真の prerequisite。

**(10.6.b)** は (10.6.a) の第2関係式 `(μ_0 − ζ)^τ = ∑_i ω_i0^σ − ζ^τ₁` + parity 論証:
- τ の定義より `(μ_0 − ζ)^τ` は G − Ã(M) で消える ⟹ `ζ^τ₁(g) = ∑_i ω_i0^σ(g)`。
- (3.9.c): `ω_i0^σ(g) ∈ ℤ`。i≠0 で `ω̄_i0 ≠ ω_i0` + (3.9.a) `ω̄_i0^σ = conj(ω_i0^σ)` ⟹ `∑_{i>0} ω_i0^σ(g) ∈ 2ℤ`。
- (3.2.b) `ω_00^σ = 1_G` ⟹ `ζ^τ₁(g) ≡ 1 (mod 2)` ⟹ `|ζ^τ₁(g)| ≥ 1`。
(10.6.b) も (10.6.a) 経由ゆえ (5.8) に gated。(3.9.a)/(3.9.c)/(3.2.b) は §5 (repo S05) に在庫見込み。

## やること

- [x] **(5.8) abstract combinatorial core DONE** (2026-06-22, `grid_eq_const_column_of_two_col`,
  `S05_GridTrichotomy.lean`, **axiom-clean** `[propext, Classical.choice, Quot.sound]`)。
  norm-w₁ full-column endgame の純代数核: separable grid `a:ι×κ→ℂ` + 2-column support {j,k} +
  係数 {0,δ}/{0,−δ} (δ=±1) + `∑(a)²=|ι|` ⟹ **単一 full column** (column k=δ / column j=−δ)。
  既存 norm-2 `eq_smul_chiFam_diff_of_vanishOnV` は constant-column を**排除**するが、これは逆に
  **採用** (separability+零列 q₀ で column-constant → Parseval mass → `a(i₀,j)²+a(i₀,k)²=1` →
  {0,±1} で片方のみ ±1)。= (5.8) proof step 4 を忠実に capture、reusable。
- [x] **(5.8) σ-level wrapper の (a) Parseval + (d) sigmaCoeff↔core 配線 DONE** (2026-06-22,
  `S05_SigmaTrichotomy.lean`, 両 **axiom-clean** `[propext, Classical.choice, Quot.sound]`, full build
  3881 green):
  - **(a) Fourier 復元** `eq_sum_sigmaCoeff_smul_chiFam_of_inner_self_eq`: Parseval *等式*
    `⟨X,X⟩ = ∑_pq sigmaCoeff(X) pq · conj(sigmaCoeff(X) pq)` (= X が Im σ ⊥ 成分を持たない、β=0)
    ⟹ `X = ∑_pq sigmaCoeff(X) pq • χ_pq`。chiFam 直交性のみ依存。`span(chiFam)` を定義せず Parseval-等式を
    仮説化したのが鍵 (norm-2 endgame は ‖·‖²=0 で coeff を消すが、(5.8) は復元が必要)。
    ⚠ 設計知見: index 積型に global Fintype 無 (codebase は局所 `Fintype.ofFinite`) → 文の `∑ pq`
    が Fintype を metavar 化 ⟹ 両 W1/W2 char-group の `[Fintype …]` を**instance 引数**に取る。
  - **(d) σ-level full-column endgame** `eq_smul_chiFam_column_of_vanishOnV`: X が V で消え、sigmaCoeff が
    2-column {jcol,kcol} support + {0,δ}/{0,−δ} entries + ⟨X,X⟩=w₁ + Parseval-等式 ⟹
    `X = δ•∑_p χ_{(p,kcol)}` ∨ `X = −δ•∑_p χ_{(p,jcol)}`。abstract core `grid_eq_const_column_of_two_col`
    (係数 grid → full column) + Fourier 復元 (full column → class-function 等式) を合成。
    separability は `sigmaCoeff_add_eq` (V-消失) で供給、entries 実数性で `∑ s² = ∑ s·conj s` を橋渡し。
    = norm-w₁ 版 `eq_smul_chiFam_diff_of_vanishOnV`。**(10.6.a) を (5.5) の出力に honest 還元**。
- [x] **(5.8) endgame 仮説 2/4 DONE (2026-06-22 lane-b 再開セッション)** — §5-gate 回避経路を確立:
  - **`OrthonormalCharacterImageFamily` (S07) は 2 元限定でなく汎用**と判明 (`imageSet : Finset`、
    `image_eq : τ(χ−χ̄)=∑_{α∈R} α` のみ要求) ⟹ column μ_k に直接適用可。これが (5.5)-for-column の正路。
  - **column-difference DONE** (`tau_muGrid_column_diff` + `tau_muGrid_columnSum_diff`, commit `bd4c8340`,
    axiom-clean=§10 upstream gate のみ): `τ(μ_ij−μ_ik)=δ(ω_ij^σ−ω_ik^σ)` + summed `τ(μ_j−μ_k)=δ∑(...)`。
    `alpha_tau_image` の系 (α tail 相殺)。= column image family の `image_eq` (R={δω_ij^σ}∪{−δω_ik^σ})。
  - **μ_k^τ₁ vanishes on V DONE** (`muColumn_tau1_vanishes_on_typePV`, commit `02ec7e03`, axiom-clean):
    (5.8) χ=ζ̄ ルート。(4.7)`muColumn_sub_conj_support` + `tau_apply_of_mem_typePV` + 誘導指標 vanishing
    + `tau_muColumn_sub_conj_eq_tau1` + 完成済 `tau1_zeta_vanishes_on_typePV`(ζ̄)。
  - 🔑 **§5-gate 回避が確定**: `tau1_zeta_vanishes_on_typePV` が honest 完成 (norm-1 NC≤2 トリック) ゆえ
    column 経路は直接 reduction が要する §5-gated `ζ̄^τ₁⊥Imσ` を**通らない** — (5.5) が μ_k^τ₁ を直接決定し
    V-vanishing は単一指標 vanishing + (4.7) で出る。‖μ_k^τ₁‖²=w₁ も既存 (`muColumn_tau1_inner_self`)。
  - **残 = sigmaCoeff 2-column 構造** ((5.8) 仮説 4/4 のうち最後): column `OrthonormalCharacterImageFamily`
    本体構築 (要 conjugate-column `conj(μ_k)=μ_{k'}` + orthonormality) → `CharacterPsiDecomposition.ofProjection`
    (ψ=0, tau1=coh.tau1) → (5.5)`eq_sum_of_psi_eq_zero` → sigmaCoeff 翻訳 → σ-endgame 適用。
  - **🗺 次セッション設計 (§6 `certainTypeR` を雛形に)**: §6 は **column 用 `OrthonormalCharacterImageFamily`
    の完全な雛形** `certainTypeR` (`S06_CertainTypeCoherence.lean:639`) を既に持つ — `imageSet =
    image (certainTypeRImage χ₂ χ₂⁻¹)` (signed σ-image `±δ·ω^σ`)、`mem_ZIrr`/`orthonormal`
    (`certainTypeRImage_inner`/`_injective`)、`image_eq` (`columnSum_conj_eq` + `dadeICM_columnDiff_eq_sum`)。
    ⚠ これは §6 Hypothesis46 (dade0=W\W2) ベースゆえ §10 (hyp.tau=typePV) に**直流用不可** — §10 版を
    mirror 構築する: (i) **conjugate-column** `conj(∑_i muGrid i k)=∑_i muGrid i k'` (§10 μ_k は §6
    `columnSum χ₂(k)` に一致 → `columnSum_conj_eq`(`(columnSum χ₂).conj=columnSum χ₂⁻¹`) → k'=
    `finCardEquivCharacterGroup⁻¹(χ₂(k)⁻¹)`; k≠k' は `column_inv_ne_self` 相当 = 奇位数で非実)、
    (ii) signed §10 σ-image 族 (alignedOmegaSigmaGrid 由来) + orthonormality (chiFam 直交性)、
    (iii) `image_eq` = `tau_muGrid_columnSum_diff` (本セッション済) + (i)、(iv) ofProjection の
    `htau1_agrees` = column-diff + `coherent.extends_on_supported`、`htau1_mem` = `extension_mem_ZIrr`。
    sigmaCoeff 翻訳は `exists_alignedOmegaSigmaGrid_chiFam_family` (R(μ_k) 元 ↔ chiFam 元) 経由。
- [ ] **残 linchpin = (5.8) wrapper の (b)(5.5)**: sigmaCoeff 2-column structure (上記「残」)。
  - (b) **(5.5)** `χ^τ₁ = ∑_{α∈R(χ)} α` を certain-type column μ_k に適用し R(μ_k)=2-column σ-構造を出す。
  - (c) ✅ **(4.7) A-support + μ_k^τ₁ vanishes on V DONE** (上記)。
  - ⚠ **真の gate は §6 certain-type μ ↔ §5 sigmaCoeff grid の reconcile** (deep §6↔§5、multi-session)。
    `IsCoherent` は abstract isometry で (5.5) を carry しない (2026-06-22 確認) — (5.5) を coherence
    isometry に対し別途立てる必要。`S07_RetargetScaled.lean:451`/`CharacterDifferenceImage`
    (`S07_Coherence.lean:395`) が R(χ) 機構の候補だが、§6 columnFamily R(μ_k) との reconcile が crux。
  - ⚠ Explore 監査 (2026-06-22) は「400-500 行・blocker 無」と評価したが item B (μ_k 2-column 分解) を
    「implicit」と認めており、これが linchpin。over-optimism に注意 ([[scaffold-sorry-free-not-done]] audit 版)。
- [x] **(10.6.a) M→G→τ₁ reduction chain DONE** (2026-06-22, commits `88a95a70`/`3d9eb887`/`a2ff9e18`):
  - M-side diagonal IP `(α_ij, μ_j − dζ̄) = 1` (`muGridAlpha_inner_muColumn_self_sub_conj`)
  - G-side diagonal IP `(α_ij^τ, (μ_j − dζ̄)^τ) = 1` (`muGridAlpha_tau_inner_muColumn_self_sub_conj`)
  - τ/τ₁ split `(α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = 1` (`muGridAlpha_tau1_inner_muColumn_self_sub_conj`)
  ⟹ (10.6.a) reduction opening 確立。
- **⊥落とし isometry orthogonality 2/3 DONE** (2026-06-22, S12, isometry pattern of `zeta_tau1_inner_self`):
  - `zeta_tau1_inner_conj`: `(ζ^τ₁, ζ̄^τ₁)=0` (**完全 axiom-clean**; isometry + (ζ,ζ̄)=0, ζ̄≠ζ irr)。
  - `zeta_tau1_inner_muColumn`: `(ζ^τ₁, μ_k^τ₁)=0` (sorryAx=upstream muGrid gate のみ=§10 全 muGrid lemma と同一、自前 sorry 0; isometry + ∑_i (ζ,μ_ik)=0 degree mismatch)。
- ⚠ **訂正 (audit over-optimism)**: ⊥落とし の残 3 番目 orthogonality `ζ̄^τ₁⊥Imσ` は **in-stock でない**。
  旧記述「tau1_zeta_vanishes 経由」は誤り — Pf (5.8) 原文では `χ^τ₁⊥Imσ ⟹ vanish on V (by 3.2.d)`
  であって**逆ではない**。vanish-on-V から ⊥Imσ は出ず、これは **§5 (5.3.b)/(5.5) gated** (5.8 σ-wrapper
  と同じゲート)。∴ ⊥落とし全体 = §5 gated; in-stock な 2 orthogonality のみ先行着地。
  残 (10.6.a) = `ζ̄^τ₁⊥Imσ` (§5) + (5.8) σ-wrapper。
- [ ] (10.6.a): diagonal IP + τ/τ₁ transfer (既存 `muGridAlpha_tau_inner_muColumn_sub_conj` 類比) +
      (5.8) → `μ_j^τ₁ = δ∑ω_ij^σ`。
- [ ] `zeta_tau1_norm_bound` Prop を (10.6.b) の genuine 主張に materialize + 証明。
- [ ] `tau1_values_and_norm_bound` を sorry-free に。

## 📋 (5.8) 詳細スコープ (2026-06-22 lane-b 精読) — multi-session piece

(5.8) [`04.7:119`] = coherence isometry τ₁ 下での certain-type column-char μ_k の像決定。原文証明の依存:
1. **(5.5)** `χ^τ₁ = ∑_{α∈E} α (E⊆R(χ))` ← (5.4) with ψ=0。**(5.4) は repo S07 在庫**。R(μ_j)=
   `{δ_j ω_ij^σ, −δ_j ω_ik^σ}` (2-column σ-構造, k=conj(j) 列) ← (5.3.b)/(4.9)。⟹ μ_k^τ₁ = ∑_i a_ik ω_ik^σ
   + ∑_i a_ij ω_ij^σ, a_ik∈{0,δ_k}, a_ij∈{0,−δ_k}。
2. **μ_k^τ₁ vanishes on V** (crux) ← χ∈S∩Irr(L)(=ζ deg w₁) + **(4.7)** `χ(1)μ_k−μ_k(1)χ ∈ ℤ[S,A]`
   + **ζ^τ₁ vanishes on V (✅ `tau1_zeta_vanishes_on_typePV`)** + A∩V=∅ + τ 定義。
3. **(3.7) separability** ⟹ a_ik=a_0k, a_ij=a_0j (row-constant)。repo S05 `sigmaCoeff_add_eq` 在庫。
4. **‖μ_k^τ₁‖²=w₁** + coeffs∈{0,±1} ⟹ a_0k²+a_0j²=1 ⟹ 一方のみ ±1 ⟹ **full column** δ∑ω_ik^σ or −δ∑ω_ij^σ。
5. uniqueness ("j,k のみ") ← Theorem (4.9) summed isometry (repo S06 `certainType_diff_dade_sum_eq` 在庫)。

**在庫**: (5.4) [S07]、(4.9) summed isometry [S06]、(3.7)/(3.8) [S05]、ζ^τ₁/ζ̄^τ₁ vanish on V [S12]、
diagonal IP `(α_ij,μ_j−dζ̄)=1` [✅本 issue]。**要新規**: (5.5) を certain-type column R(μ_j) で適用する形 +
**(4.7) A-support of `w₁μ_j−dζ`** + **(5.8) combinatorial core** (2-column separable + norm-w₁ → full column,
= 私の (10.5) `eq_smul_chiFam_diff_of_vanishOnV` の full-column 類比、grid 機構流用可) + assembly。

**(10.6.a) §10-specialized route** (full (5.8) より tractable な可能性): reduction
`(α_ij^τ, μ_j^τ₁−dζ̄^τ₁) = (δ(ω_ij^σ−ω_i0^σ), μ_j^τ₁)` は my infra (diagonal IP + ζ^τ₁⊥σ + isometry) で provable
だが、最終 `= δ∑ω_ij^σ` は (5.8) core 必須。⟹ (5.8) combinatorial core (full-column trichotomy) が真の linchpin。

**評価: (5.8) は §5-§8 coherence 機構に深く絡む multi-session piece** (上記 4 新規部品 + assembly、~数百行)。
単発でなく focused 複数セッションで攻めるべき。次着手の clean entry = **(5.8) combinatorial core を S05 一般補題化**
(my (10.5) trichotomy の full-column 類比、§5 σ-machinery のみ依存、reusable)。

## 完了条件

`tau1_values_and_norm_bound` (S12) が sorry-free。axiom footprint = §10 muGrid 系上流 gate のみ。
full build + AxiomsCheck green。

## 参照

- issue 1007/1008 (closed): (10.5) Dade-image identity + (10.3) n-even。
- `tau1_values_and_norm_bound` (S12:3521)、`CharacterParameters.zeta_tau1_norm_bound`。
- (5.8) = `references/peterfalvi/04.7_pp_25_29_Coherence.mmd:119`。
- 上位: [[ft-endgame-two-poles]] / `notes/peterfalvi/s12_s10_character_bridge.md`。
