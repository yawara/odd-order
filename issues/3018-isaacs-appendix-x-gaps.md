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

## 残ギャップ (survey L248-)

- **X.1** (部分): HK is a subgroup iff HK=KH。forward (HK=KH ⟹ ↑(H⊔K)=HK as sets) は Ch02 Basic に
  private。converse + public 化。
- **X.4** (未): direct-diamond correspondence (下記)。
- **X.5** (部分): Frattini = nongenerators。forward = mathlib `frattini_nongenerating`、converse。
- **X.11** (部分): |K:H∩K| ≤ |G:H|, 等号 ⟺ HK=G。inequality は mathlib、等号 iff clause。
- **X.12** (部分): coprime index ⟹ HK=G (join 形は済)、set-product 形 (∀g=hk)。
- **X.22** (部分): internal direct product criterion (prefix-intersection iff)。

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
