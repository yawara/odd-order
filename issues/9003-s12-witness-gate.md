---
id: 9003
slug: s12-witness-gate
title: "β-lane §12 witness path gated on §8-§11 structural + §10 support_mutual_exclusion"
created: 2026-07-02
---

# β-lane §12 witness path gated on §8-§11 structural + §10 support_mutual_exclusion

## 背景

β-lane の cleanly-ownable §12 character-theory work = (12.6) coherence tower は **DONE**
(case (b) `frobenius_typeI_coherent_of_abelianKernel` + case (c) `frobenius_typeI_coherent_of_cyclicQuotient`
共 sorry-free/axiom-clean; commit chain 〜c43881d4)。§12 witness path の**下流**は全て他レーン領域
(§8/§9/§10/§11/§14) または未形式化な upstream に gated。この issue は gate を map して hub が upstream
を優先付けできるようにする (loop⁹¹ 調査)。

## 2 つの gate クラスタ

### Cluster A — 構造的、(12.10)/(12.11) 経由
`witness_L_frobenius` (12.10, S14:3960, **sorry**) が linchpin。証明 (Pf §12 mmd p.72) は
type P/II/III/IV/V を排除 → (8.2.b) 適用、以下の**未形式化** §8-§11 を要す:
- (8.16) type II で C_G(y)⊆L
- (10.10)+(11.9.c) type III / (9.7) case (b)
- (11.6) C_U(H)=1、(9.7.b) U cyclic、(8.6.a) C_G(y)⊆L (y∈H^#)
- minimality-of-p ⟹ Sylow_q cyclic ⟹ (8.2.b) Frobenius

(8.16)/(8.6.a)/(9.7.b)/(10.10)/(11.9.c)/(11.6) はいずれも S10/S11 に grep で不在。
`intersection_complement_structure` (12.11, S14:〜3971, **sorry**) は (12.10)+(8.13.c1)+(8.1.b/c)+(9.1)[有]。
下流: (12.12) `complement_cyclic_order_dvd` は (12.10)+(12.11) 要。witness `hxH` (x∈H) は今 (12.11)
を clean に cite 済 (c43881d4)。

### Cluster B — 幾何的、(8.18.c) 経由
`nonconjugate_diffImage_inner_zero` (8.18.c, S14:665, **sorry**) → (12.3) → (12.14)/(12.15)/(12.16)。
還元: supp(τ₁(φ₁−φ̄₁))⊆Ã(L₁)、supp(τ₂(...))⊆Ã₁(L₂) が nonconjugate で disjoint ⟹ inner=0。
disjoint 性 = **`S10.support_mutual_exclusion` (S10:853, sorry)** — §10 thickened-support 幾何 (lane-d/f)。
BG piece `conjClassSet_Mtilde_disjoint` (BG S14_TypePCounting:8042)・`conjClassSet_T_Mtilde_disjoint` (:8171)
は**証明済**; 欠けている bridge = A1(S)↔𝒞_G(M̃) (`A1_eq_sigmaSharp_of_typeI_or_II` S10_BGInterface:113
+ sigmaSharp↔M̃)。`inner_eq_zero_of_disjoint_support` (ClassFunction:383) +
`dadeIntegralCharacterMap_apply_of_support` は有。

## やること (最高レバレッジ unblock = 次 β target 候補)

- [x] **`S10.support_mutual_exclusion`** (Cluster B): **DONE** (commit 65a2be52, axiom-clean)。type-I +
  nonconjugacy 仮説を追加 (旧 statement は conjugate S=T で偽) → conjClassSet_Mtilde_disjoint で証明。
- [ ] **(8.18.c) `nonconjugate_diffImage_inner_zero` assembly** (S14:665): support_mutual_exclusion +
  Dade-image support (supp(τ(φ−φ̄))⊆𝒞_G(A(L))) + `inner_eq_zero_of_disjoint_support`。Ã/A1/𝒞_G の
  対応に注意 (mutual-support 形 → conjClassSet-disjoint 形が要る)。→ (12.3)→(12.16) FT chain を閉じる。
- [ ] Cluster A ((12.10) type-analysis) は §8-§11 の大きな multi-theorem effort。§-owning lane に割当?

## 完了条件

hub が裁定: (a) β が `support_mutual_exclusion` (§10, policy A/B で cross-lane) を pick up、または
(b) §8-§11 structural (8.16/8.6.a/9.7.b/10.10/11.x) を §-owning lane に割当。
(12.6) coherence deliverable はどちらでも完了済; これは §12 *下流*の話。

## 参照

- commit c43881d4 (mainSubgroup_le + hxH←12.11)、b04c306f ((12.10) 非-TI decoupling)、4753cd14 ((12.6)c)
- notes/peterfalvi/s14_maximalI.md (loop⁷⁷-⁹¹)
- Pf §12 mmd: references/peterfalvi/04.14_pp_69_74_Maximal_Subgroups_of_Type_I.mmd
