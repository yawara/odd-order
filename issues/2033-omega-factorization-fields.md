---
id: 2033
slug: omega-factorization-fields
title: "ω-grid の W₁×W₂ 因子分解 field threading — (1.10) 合同 atom の gate 解消 (3002 後続)"
created: 2026-07-05
---

# ω-grid の W₁×W₂ 因子分解 field threading — (1.10) 合同 atom の gate 解消 (3002 後続)

## 背景

(13.6)/(13.7) package (S15_SAndT_Setup、07-05 loop で実 assembly 化) の残 atom のうち
(1.10)-合同系 2 本:

- `eta10_alphaCF_one_ne_zero`: α(1) ≠ 0 ⟸ α(1) = η₁₀(x) (x ∈ W₂#) ≡ ω₁₀-値 ≡ 1 (mod 1−ε)
- `exists_lambda_alphaFun_one_qb`: α(1) = qb ⟸ 同型の W₂-値合同

**real 到達済の部分**: α(1) = α(x) = η₁₀(x) for x ∈ W₂# は `H_sharp_alphaFun_const_on_P`
(P-定数性) + W₂ ≤ P + point formula で実証明可能。
**gate**: η₁₀(x·y) = ω₁₀(x·y) までは `tau3_apply_of_regular` (3002 threading 済) で届くが、
**ω₁₀(xy) の値の計算には ω の W = W₁×W₂ 因子分解構造 (Pf (3.3): ωᵢⱼ = ξᵢ⊗χⱼ 型) が
Hypothesis に無い** (現 fields: omega_orthonormal / omega_apply_one / omega_mem_ZIrr のみ)。

## やること (3002 と同じ enrichment パターン)

- [ ] `S15.Hypothesis` に ω-因子分解 field を追加 (候補: `omega_mul_decomp :
      ∀ i j (x ∈ W₁) (y ∈ W₂), omega i j ⟨x*y,…⟩ = omega i 0 ⟨x,…⟩-型 · omega 0 j`
      — 正確な形は Pf (3.3)/(13.1) と spine 構成 (FeitThompson omegaS ← TICyclicHypothesis)
      が supply できる形で確定)
- [ ] FeitThompson.lean の構成箇所で supply (lane-a 所有 file への additive 編集 —
      2026-07-05 ユーザー裁定の追加編集権に基づき self-flag で)
- [ ] (1.10.a/b) 合同 (`CyclotomicCharacterCongruence` 在庫確認) と接続して両 atom を実証明

## 調査ログ (07-05 loop it.27)

- **`TICyclicHypothesis.omega` は monoid hom `χ : W →* ℂˣ` でパラメータ化**
  (S05_TICyclic:326、`omega_apply : (ω χ) w = χ w`) — 乗法性は hom 構造から自由。
- 必要 field は当初想定より簡素な 3 本に縮小:
  1. `omega_mul : ∀ i j w w', omega i j (w*w') = omega i j w * omega i j w'` (linear 性)
  2. `omega_col_zero_on_W2 : ∀ i y ∈ W₂, omega i 0 y = 1` (col-0 は W₂ 上自明)
  3. `omega_pow_q_on_W1 : ∀ i j x ∈ W₁, (omega i j x)^q = 1` (W₁-値は q-乗根)
  → (13.7) の η₁₀(xy) = ω₁₀(x)·ω₁₀(y) ≡ 1 (mod 1−ε) が導出可能に。
- **supply 経路**: FeitThompson `omegaS i j = compHom (gridEquivE) (chiColumn (chi2enum j)
  (eqQ i))` (FeitThompson:1355) — S06 certainType の `chiColumn` の hom-性 (Pf (3.3): ω は
  W の pq 個の線形指標) を遡って supply。次: chiColumn の定義 (S06) を精査し、
  hom-性を propositional に取り出せるか確認。

## 参照

- issues/3002 (親パターン)、notes/peterfalvi/s15_s_and_t.md LIVE STATUS (07-05)
- S15_SAndT_Setup: `eta10_alphaCF_one_ne_zero` / `exists_lambda_alphaFun_one_qb` /
  `tau3_apply_of_regular` field
