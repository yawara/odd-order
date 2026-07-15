---
id: 2036
slug: g0-dichotomy-assembly
title: "(13.9.a) G0_nonvanishing_dichotomy 組立 — F1 field + F2 four-corner + F3 Galois-power threading"
created: 2026-07-05
---

# (13.9.a) G0_nonvanishing_dichotomy 組立 — F1 field + F2 four-corner + F3 Galois-power threading

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 設計 (07-05 it.48-49、Pf (13.9.a) 証明の完全解剖)

証明骨格 (Pf p.79):
1. F1 で ∃ j δ: τ₁(μⱼ) = δΣᵢηᵢ₁、μⱼ = Ind_{PC}(linear) (13.3.a: **列和 μⱼ = Σᵢμᵢⱼ 自身が
   Ind-PC-linear**)。
2. (μⱼ−λ) は零次数 (両方 degree uq) の PC-台差 → Ind_S^G(μⱼ−λ) は (H^#)^G 外で 0
   (`IsTISubset.induce_apply_of_not_mem_conjClassSet` ✓ proven) — τ₁(μⱼ−λ) =
   Ind(μⱼ−λ) は `tau1S_apply_induce_sub` field ✓。x ∈ G₀ ⊆ (H^#)^G-外 →
   **λ^{τ₁}(x) = δΣᵢ ηᵢ₁(x)**。
3. x が W-regular 共役 → η₁₀(x) = ω₁₀(w) ≠ 0 ((3.2.c) `tau3_apply_of_regular` ✓ +
   ω-値は q-乗根 ≠ 0 `omega_pow_q_of_mem_W1` ✓ + class-fn 共役不変) → 右枝。
4. さもなくば背理: λ^{τ₁}(x) = η₁₀(x) = 0 と仮定。
   - **F3 (Galois-power, (3.9.b))**: ηᵢ₀(x) = 0 (i > 0) — η₁₀(x) = 0 から Galois 軌道で。
     供給 = S05 `exists_mapRingEquiv_sigma_omega_pow` (:1837 ✓ proven) +
     ω-grid の row-power 構造 (ωᵢ₀ = ω₁₀^i — hom-grid で真、2033-族 field)。
   - **F2 (four-corner, (3.4)/(3.5))**: regular-飽和外の x で
     0 = 1 − ηᵢ₀(x) − η₀ⱼ(x) + ηᵢⱼ(x)。
     供給 = S05 `sigma_alphaCF` + `chiFam_spec` (Ind αᵢⱼ = 1 − χᵢ₀ − χ₀ⱼ + χᵢⱼ ✓) +
     V-台の Ind は飽和外 0 (TI-lemma ✓) + σ↔tau3W 同定 (it.42 exhaustion ✓)。
   - 合成: ηᵢ₁(x) = η₀₁(x) − 1 (i>0 一様) → 0 = δ⁻¹λ^{τ₁}(x) = Σᵢηᵢ₁(x) = qη₁₁(x) + 1
     → η₁₁(x) = −1/q は代数的整数でない → 矛盾 (η-値の整性: eta ∈ ZIrr + 値は整 —
     `IsIntegral` 導出は ZIrr-値の標準補題)。

## 状態

- [x] F1 field `mu_col_tau1_eta_col_one` を CharacterDegreeData に追加 (it.49、supply は
      sorried (13.3) producer 内 = 追加義務なし)
- [x] F2: hyp-level field `eta_fourcorner_vanish` + spine supply (chiFam_spec 経由、
      2033-パターン; tau3W(omegaS-combo) と chiFam の橋は it.42 の exhaustion 流用)
- [x] F3: hyp-level field (ωᵢ₀ = ω₁₀^i の row-power + Galois) or 直接
      `eta_row_zero_of_eta10_zero` 形 — S05 :1837 + 位数条件の設計
- [x] assembly: `G0_nonvanishing_dichotomy` 本体 (07-05 it.55 完了) (G0Finset-membership → 飽和外の抽出、
      `mem_G0_iff` ✓ 在庫)

## 参照

Pf 04.15 p.79 (13.9)、04.5 (3.9.b)/(3.4)/(3.5)。issues/closed/2035 (13.3-producer、F1 の供給元)。

## 完了 (07-05 it.49-55)

全 4 項目着地 — `G0_nonvanishing_dichotomy` は sorry なしの実証明
(残仮定 = CharacterDegreeData fields、supply = sorried (13.3) producer)。
regular 枝: ω-値 ≠ 0 (omega_mul + apply_one)。背理枝: helper (λ = δΣηᵢ₁) +
F3 (Galois row-vanish) + F2 (four-corner) → q·η₀₁(x) = q−1 →
isIntegral + int_dvd_of_intCast_eq_mul_isIntegral で q ∣ 1 矛盾。issue close。
