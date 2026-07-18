---
id: 3016
slug: lem63b-derived-hall
title: "BG Lem 6.3(b): G' nilpotent, |G/G'| prime ⟹ G' Hall + G'=[G,K]"
created: 2026-07-18
---

# BG Lem 6.3(b)

## 背景

BG §6 の document 順最上流の残ギャップ (survey L346: 6.3(a) 両結論は済 (L307, L394)、(b) が未)。
BG §1-§4 完成後、§5・§7 も済 (survey table)、§6 に着手。

## statement (BG mmd L2000)

> G solvable。(b) `G'` nilpotent かつ `|G/G'|` prime ⟹ `G'` は G の Hall subgroup、かつ
> `G' = [G,K]` for every complement K of G' in G。

## 証明 (BG mmd L2013)

p = |G/G'| (prime)。`G/O_{p'}(G')` は p-群 (order p·|O_p(G')|) で derived subgroup の index が p。
ゆえ cyclic of order p、`G' = O_{p'}(G')` (= G' は p'-群)。残りは (a) から。
- **G' = O_{p'}(G')**: G' nilpotent = O_p(G') × O_{p'}(G')。`G/O_{p'}(G')` は p-群、その derived
  subgroup = image of G' = O_p(G')、[G/O_{p'} : O_p(G')] = p。p-群で [Q:Q']=p ⟹ [Q:Φ(Q)]=p ⟹
  cyclic (FrattiniPGroup)。cyclic ⟹ Q'=1 ⟹ O_p(G')=1 ⟹ G'=O_{p'}(G') (p'-群)。
- **G' Hall**: |G'| coprime to p = [G:G'] ⟹ Hall。
- **G' = [G,K]**: complement K は Schur-Zassenhaus (G' Hall、|G'|⊥|G/G'|=p)。Lem 6.3(a)
  (`commutator_eq_self_of_isComplement'_le_commutator`) を H=G' に ⟹ ⁅G',K⁆ = G'。
  [G,K] = ⁅⊤,K⁆ ⊇ ⁅G',K⁆ = G'、かつ [G,K] ⊆ G' (G/G' abelian) ⟹ G' = [G,K]。

## 既存 infra (reuse)

- **Lem 6.3(a)** `commutator_eq_self_of_isComplement'_le_commutator [IsSolvable G] {H K}[H.Normal]
  (hHK : H.IsComplement' K) (hH : H ≤ commutator G) : ⁅H,K⁆ = H` (S06_Additional:307)。
- G' nilpotent ⟹ Sylow direct product / `Ch01.fitting` 系、FrattiniPGroup (`OddOrder/GroupTheory/FrattiniPGroup.lean`、[Q:Φ(Q)]=p ⟹ cyclic)。
- Schur-Zassenhaus (mathlib `Subgroup.exists_left_complement'_of_coprime` 等)、Hall subgroup 定義。
- `commutator G` (= G'), `Subgroup.IsComplement'`。

## 完了条件

BG Lem 6.3(b) を book strength・sorry-free・axiom-clean。AxiomsCheck 登録、survey 正本 Lem 6.3「済」。

## 参照

- BG mmd L1996-2015、既存 S06_Additional (6.3(a))、survey L346

## ✅ 完了 (2026-07-18)

`S06_Lem63b.{commutator_isHall_of_nilpotent_prime_index, commutator_eq_commutator_top_of_isComplement', lemma63b}`、
sorry-free・axiom-clean・AxiomsCheck 登録・full build green (4312 jobs)。⟹ BG Lem 6.3 全 (a)(b) 済。
Hall part は [IsSolvable G] 不要 (mild 強化)。BG §6 残 = Thm 6.2 特殊化 + Thm 6.4 (missing, 低優先)。
