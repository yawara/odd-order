---
id: 1028
slug: pf-10-7-typeii-cross-isometry
title: "Pf (10.7) exists_typeIICrossIsometryData 形式化 (Coq Frob_der1_type2、3 items)"
created: 2026-07-13
---

# (10.7) type-II cross-isometry — lane-a frontier (hub RULING #2 割当)

> hub RULING #2 (9087、2026-07-13): 型III/IV char-core 完遂後の lane-a 次 frontier =
> `exists_typeIICrossIsometryData`。**localize 済 = genuine gap** (clean-heir rewire でない;
> S12_TypeIIFrobenius:1206 docstring が 3 items の未形式化数学を明示)。1020 (10.7)' cluster の続き。

## 対象

`exists_typeIICrossIsometryData` (`S12_TypeIIFrobenius.lean:1206`、bare sorry :1221)。
Peterfalvi **(10.7)** = Coq **`Frob_der1_type2`**。consumer = `TypeIICrossIsometryData.elim`
(:1235、**既に proven**、M-side pin `muColumn_tau1_pin` 使用) → `typeII_HU_frobenius_of_coherent`
(§10/§14 type-II 構造、S12_MaximalBasic 経由で spine 隣接)。⟹ gap は package (`TypeIICrossIsometryData`)
の**生成**のみ; その elimination (contradiction 導出) は済。

## 3 items (docstring S12_TypeIIFrobenius:1195-1204、全て genuine 未形式化)

1. **τ₂ 構成** (S-side cross-isometry map)。
2. **ν^{τ₂} の pin**: (5.8) (Coq `coherent_prDade_TIred`) via (3.7) 係数 rigidity + (3.2.d)
   V-vanishing → ν^{τ₂} を signed row sum に。**typeP_pair sphere (issue 0098 item 1)**。
3. **support disjointness** ((8.18.b) via (8.13.c4)): `Ã₁(M) ∩ Ã(S) = ∅` — M が kernel M_F の
   Frobenius でない (Hyp (10.1)) ゆえ S の共役が M を support しない; (8.10)/(8.15)/(4.7) で
   `cross_zero` + (共役 pair 差 trick で) `zeta_lam_ortho`。**§8 support geometry (S10)**。

## 進め方 (次 iteration、fresh context)

1. **Coq `Frob_der1_type2` (PFsection10.v 付近) 精読** — 3 items の証明構造・依存を把握
   (`coq/theories/PFsection10.v`、コメントで行間補完; [[feedback-ask-chatgpt-for-elided-gaps]] 可)。
   関連 PFsection3 (coefficient rigidity 3.7 / V-vanishing 3.2.d)、PFsection5 (5.8 coherent_prDade_TIred)、
   PFsection8 (8.18.b/8.13.c4 support)。
2. **上流優先**: item 3 (§8 support geometry、S10) が最も self-contained な可能性 → 先に精査。
   item 2 は typeP_pair (0098) に依存 — その state を先に確認。
3. `TypeIICrossIsometryData` structure (S12_TypeIIFrobenius 上方) の field を確認し、各 item が
   どの field を埋めるか map。
4. build-green + #print axioms 検証 (authoritative のみ、自作 metaprogram 不可 —
   [[verify-which-sorry-via-print-axioms-not-metaprogram]])。

## 参照

hub RULING #2 = 9087。1020 ((10.7)' axiom-clean chain)、0098 (typeP_pair、item 2)、
S12_TypeIIFrobenius:1206 (target) / :1235 (elim、proven)。Coq PFsection10.v `Frob_der1_type2`。
本 session 完遂 = 型V (6.5) 9089 + card_kappaHall 1025。
