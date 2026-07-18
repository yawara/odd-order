---
id: 3018
slug: isaacs-appendix-x-gaps
title: "Isaacs Appendix X 残ギャップ (X.1/X.4/X.5/X.11/X.12/X.22) — 独立・elementary・非衝突"
created: 2026-07-18
---

# Isaacs Appendix X 残ギャップ

## 背景

lane c は BG §1-§4 完成 + §6 substantial 済。次の高価値 in-scope pivot を探索したところ:
- Isaacs Ch.3 = **active (別 lane)**、Ch.8 = **完了 (別 lane, "Ch.8 完了")**、Ch.9 = lane a、
  Peterfalvi = lane b。⟹ numbered chapters は他 lane が積極的に closing 中 (survey は激しく stale)。
- **Isaacs Appendix (X.1-X.23)** = elementary group theory compendium、17/23 済、残 6 は
  inessential clause の S-gap。**active work 無 (git 確認)** = 独立・非衝突の lane-c 適地。

## 残ギャップ (survey L248-) — ✅ 全済 (2026-07-18)

- **X.1** ✅ **済** (DirectDiamond.lean `coe_sup_eq_mul_iff_mul_comm`): HK subgroup ⟺ ↑H*↑K=↑K*↑H。public 化。
- **X.4** ✅ **済** (DirectDiamond.lean `directDiamond_bijOn`): direct-diamond correspondence。
- **X.5** ✅ **済** (SubgroupBasics.lean): converse = `mem_frattini_of_nongenerating` (finiteness 不要)、
  full iff = `mem_frattini_iff_nongenerating [IsCoatomic]`。forward half は mathlib `frattini_nongenerating`。
- **X.11** ✅ **済** (SubgroupBasics.lean `relIndex_eq_index_iff_mul_eq_univ [Finite G]`):
  |K:H∩K| = |G:H| ⟺ ↑H*↑K=univ。⚠ **hint 訂正**: "HK=G" = set product `↑H*↑K = univ` は
  `H⊔K=⊤` より真に強い (S₃ 反例; 元 issue の "HK=G" を join と読むと誤り)。inequality は mathlib
  `relIndex_le_of_le_right`。証明は repo Lem X.2 (`Ch02.card_set_mul_card_inf`) 経由。
- **X.12** ✅ **既済** (repo): set-product 形 = `Ch03.set_mul_eq_univ_of_coprime_index`
  (Theorem315.lean)、join 形 = `Ch03.sup_eq_top_of_coprime_index`。SubgroupBasics で docstring 注記のみ。
- **X.22** ✅ **済** (SubgroupBasics.lean `iSupIndep_iff_disjoint_biSup_lt [Finite ι]`):
  正規族の iSupIndep ⟺ prefix-disjoint。hard 方向 = `supIndep_of_prefix` (strong induction)、
  modular law の必要 instance = `disjoint_sup_of_normal` (subgroup lattice は非 modular ゆえ正規性経由)。

**⟹ Isaacs Appendix 完成** (X.1-X.23 全済 or mathlib/repo 被覆)。全 SubgroupBasics 宣言 axiom-clean
`[propext, Classical.choice, Quot.sound]` (直接 #print axioms 検証)、full build green 4387 jobs。
AxiomsCheck 非登録 (appendix elementary、FT spine 非消費、DirectDiamond と同方針 — mathlib upstream candidate)。
commit `7b8d175a1` (SubgroupBasics)。

## X.4 statement (Isaacs mmd L5953)

> H, K ≤ G, HK も subgroup、D = H∩K。`X = {X : H≤X≤HK}`, `Y = {Y : D≤Y≤K}`。
> θ : X → Y, θ(X) = X∩K は **injective**、image = `W = {W∈Y : WH is a subgroup}`
> (W permutes with H)。

**証明** (mmd L5965): θ well-defined (X∩K ∈ Y)。injective: X = X∩HK = H(X∩K) = Hθ(X) (Dedekind、
H⊆X ゆえ)。image ⊆ W: Hθ(X)=X subgroup ⟹ X.1 で θ(X)H = Hθ(X) subgroup。surjective onto W:
W∈W ⟹ WH subgroup (X.1)、W⊆K ゆえ WH∈X、θ(WH)=WH∩K=W(H∩K)=W (Dedekind + H∩K⊆W)。

## 既存 infra

- Dedekind's lemma (mathlib `Subgroup.mul_inf_assoc` / `inf_mul_assoc` 系)。
- Lemma X.1 (permutable): Ch02 Basic.lean:1168- に private forward。mathlib
  `Subgroup.Pointwise`/`mul_comm` 系。X.4 は X.1 を要するので X.1 の public 化 or 再証明が先。

## 完了条件

各 X-gap を book strength・sorry-free・axiom-clean。document 順 (X.1 → X.4 → X.5 → X.11 → X.12
→ X.22)。AxiomsCheck 登録は要判断 (appendix は mathlib upstream candidate、`OddOrder/Mathlib/Subgroup.lean`
が自然な home)。survey 更新。

## 参照

- Isaacs mmd `references/isaacs/finite-group-theory.mmd` L5915-6253 (appendix)、survey L248-
- ⚠ 他 lane が chapters を aggressively closing 中、survey stale。着手前に必ず verify-port-state-by-number。
