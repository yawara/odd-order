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

- [ ] **P1 (9.8.d)-existence** (§9、最上流): 非Galois block data から λ 構成 (S11 世界)。
- [ ] **P2 (11.9.a)** 行0射影 (§11): S13 新 leaf で grid 係数解析。
- [ ] **P3 (c) 組立**: u=a → q<p 矛盾 → Galois → `U_cyclic` → `isTypeIII_of_isTypeIIIorIV`
      (普遍 Type-IV 排除) + T-side 供給形 (c が cite する signature)。
- [ ] AxiomsCheck 登録 + consumer への配線 note (1016/9013/2018 参照)。

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
