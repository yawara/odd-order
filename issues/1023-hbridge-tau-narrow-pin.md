---
id: 1023
slug: hbridge-tau-narrow-pin
title: "(11.8.6) hbridge_τ discharge — (5.5)/(5.8) μ-column pin の X-generic 化 + narrow 𝒮(H₀C) 適用"
created: 2026-07-12
---

# hbridge_τ discharge — μ-column pin の X-generic 化

**lane a。2026-07-12 調査完了、実装待ち。** 対象 = `S13_Orthogonality.lean` の
`coherent_SOf_H0C_of_column_identities` 内 `hbridge_τ` sorry (現 :325 近傍)。
(11.9.b)-unconditional → (13.2.a) → spine の残 residual の 1 つ。

## 数学 (確定)

hbridge_τ の goal は ν-線形性で **`hsofC.extension (∑ᵢ μ_{i1}) = ∑ᵢ ω^σ_{i1}`**
(narrow 𝒮(H₀C)-coherent extension の μ-column image pin、Pf (5.8) = mmd 04.7:119) に帰着:
- bridge = ∑ᵢμ_{i1} − dζ は 𝒮(H₀C)-span 元 − S(HC)-span 元、ν は両 span で各 extension に一致
  → ν(bridge) = hsofC.ext(μcol) − d·coh.ext ζ。RHS = hcol (j=1) = ∑ω^σ_{i1} − d·coh.ext ζ。
- **δ = 1 は hcol から導出可能**: hcol の 2 本 (j,k≠0, j≠k; w₂ ≥ 3 ✓ w2_prime) を引き算 →
  τ(μcol_j − μcol_k) = ω_j − ω_k。cohFree grid 恒等式 τ(μcol_j − μcol_k) = δ(ω_j − ω_k)
  (tau_muGrid_columnSum_diff 系) と比較、δ = −1 なら ω_j = ω_k で直交性に矛盾。

## 実装 (2 phase)

**Phase A — DadeCalculations の X-generic 化** (S12_MaximalIII_IV_V_Core/DadeCalculations.lean、
a 所有)。wide `coh : CoherentHypothesis hyp params` を消費する chain を
`(cohX : S07.IsCoherent hyp.tau X hyp.A0)` + 所属仮説
`(hcolX : ∀ j ≠ 0, (∑ᵢ muGrid i j) ∈ X)` に一般化 (書籍の (5.8) が抽象 τ₁ で述べる形に忠実化)。
coh の実消費は 4 点のみと実測済: `.tau1` / `.coherent.extension_inner_eq` (span {χ−χ̄, χ}) /
`.extends_on_supported` (χ−χ̄, μ_j−μ_k = A₀-supported) / `.extension_mem_ZIrr` (χ)。
対象 decls (行番号は 2026-07-12 時点):
1. `tau_muGrid_columnSum_diff` (:~340 で使用) — cohFree 変種既在 (`_cohFree`)、入力差を確認し
   可能なら cohFree に寄せる。
2. `columnImageFamily` (:~100-176、coh 使用は tau_muGrid_columnSum_diff 経由) —
   `columnImageFamilyCohFree` 既在! (5.5) 側を CohFree family に差し替えられるか確認。
3. `exists_muColumn_tau1_eq_sum_R` (:211) → X-generic core `exists_muColumn_coherent_eq_sum_R`。
4. `muColumn_tau1_diff_eq` (:296) → X-generic core。
5. `omegaSigmaDiff_inner_muColumn_tau1` (pin tail :463 で使用) → X-generic core。
6. `muColumn_tau1_pin` (:396) → X-generic core `muColumn_coherent_pin`。
旧 wide 版は全て thin 実体化として保存 (X := Sset、hcolX := muGrid_column_sum_mem_inducedFamily
∘ hd1; 下流 DadeCalculations:550/:1209 + Isometry106 無変更)。refuter-factoring
(73dec37f) と同パターン。

**Phase B — S13_Orthogonality capstone 内 discharge**:
capstone 内で params 取得 (hyp.base.exists_charParameters_full) → hcol から δ=1 導出 (上記) →
narrow 所属 `columnSum_muColumnChar_mem_sOf_H0C` (S13、既在 — capstone :275 で使用中) で
hcolX を供給 → `muColumn_coherent_pin` (X := sOf s11Setup H0C、cohX := hsofC) → ν-線形性
計算で hbridge_τ 完了。⚠ hzconj (`ζ̄ ≠ ζ`) 等 params 系 hypothesis の在庫確認
(capstone signature に無い分は内部導出 or 上流 caller から thread)。

## 残り (本 issue 外)

hmixed (:304、(6.7) b≡0 congruence、image-side 直交) は別 issue — こちらは §6 Dade congruence
の genuine 新規内容 (Coq PFsection6/11 の対応を精読してから)。

## 2026-07-12 tick² — Phase A 縮小 (cohFree drop-in 判明)

- `tau_muGrid_columnSum_diff_cohFree` (Isometry106:775) は coh 版 (:1006) と同結論で
  coh/hos/hzconj 不要 (+ hjk : j ≠ k のみ追加; j = k は両辺 0 で trivial case-split)。
- `columnImageFamilyCohFree` (DadeCalculations:137) 既在 — (5.5) :268 の coh 版
  `columnImageFamily` を CohFree に差し替えれば columnImageFamily 系の coh 依存は消える見込み
  (signature 照合が Step 1)。
- ⟹ X-generic 化の真の対象 = **4 decls の extension-fact 触点のみ**:
  exists_muColumn_tau1_eq_sum_R / muColumn_tau1_diff_eq / omegaSigmaDiff_inner_muColumn_tau1 /
  muColumn_tau1_pin。generic interface 案:
  `{X : Set _} (cohX : S07.IsCoherent hyp.tau X hyp.A0) (hXcol : ∀ jj ≠ 0, columnSum jj ∈ X)`、
  `coh.tau1` → `cohX.extension` (CoherentHypothesis.tau1 の定義 = coherent.extension を確認)。
- omegaSigmaDiff_inner_muColumn_tau1 の proof 内 coh 触点は未読 (Step 2 で確認)。

## 2026-07-12 tick³ — ⚠ 単純 X-generic 化の障害と 2 route

`omegaSigmaDiff_inner_muColumn_tau1` (Isometry106:878、pin tail の唯一の外部 inner 供給) の
proof は **`coh.tau1 params.zeta.conj` を使用** (α_{ij} = μ_{ij} − δμ_{i0} − nζ の nζ tail 経由で
ζ̄ の extension image が必要)。ζ̄ ∉ 𝒮(H₀C) ゆえ X := 𝒮(H₀C) の単純パラメータ化は**この 1 本で破綻**。
capstone 文脈では ζ ∈ S(HC) (hζHC) + coh (S(HC)-coherence) があるので ζ̄ 側は coh.extension で
賄えるが、すると ⟨coh.ext ζ̄, cohX.ext μ_j⟩ 型の **cross-family inner** が現れ、これは hmixed
((6.7) b≡0) と同根の内容 — 両 sorry は共通 core を持つ可能性が高い。

**route (α)**: 2-coherence generic 化 (cohX for μ-columns + cohY for ζ,ζ̄) + cross-inner を
仮説化 → capstone で cross-inner を (6.7) congruence 機構から供給 (hmixed と同時に閉じる)。
**route (β)**: S-side T2 pin (S12_TypeIIColumnPin) の Parseval/V-vanishing endgame
(`eq_smul_chiFam_column_of_vanishOnV` S05) を M-side narrow に mirror — family-size 非依存の
(5.5)+V-vanishing+norm 論法。V(M)-vanishing of hsofC.ext(μcol) の供給法を要精査
(S-side は zeta1-trick + (8.16) anchor)。

次 tick: (β) の実現可能性 (M-side V-vanishing の入手経路) を S12_TypeIIColumnPin :551-668 と
S05 `eq_smul_chiFam_column_of_vanishOnV` の仮定から判定 → route 確定。
(α)/(β) いずれも hmixed ((6.7)) 側の Coq 対応 (PFsection11 の b≡0) 精読が有益 —
`coq/theories/PFsection11.v` の該当 congruence を併読すること。
