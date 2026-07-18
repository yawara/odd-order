---
id: 3017
slug: thm62-js-general
title: "BG Thm 6.2 一般形 J(S): Z(J(S))·O_{p'}(G)◁G — O_{p'} reduction + ZJ hypothesis discharge"
created: 2026-07-18
---

# BG Thm 6.2 一般形 (literal Thompson J(S))

## 背景

BG §6 の特殊化債務 (survey L351)。**BG Thm 6.2** (mmd L1990): G solvable odd, p prime, S∈Syl_p
⟹ `Z(J(S))·O_{p'}(G) ◁ G`。book の **Remark** (L1994): 「A substitute (Thm B.4) is proved in
App.B using L(S) (Puig) instead of J(S)」。

現状:
- **L(S) 一般形は済** = `AppB_Thm62.zCenter_lOdd_sup_oPiCore_normal` (`Z(L(S))·O_{p'}(G)◁G`、全 G、
  O_{p'} 商 → `zCenter_lOdd_normal_of_oPiCore_eq_bot` (O_{p'}=1 case) via Ḡ=G/O_{p'}, S̄=mk(S)≅S)。
  **book の推奨代替はこれで満たされている。**
- **J(S) は reduced case のみ** = `S06_Additional.normalJ_normal_of_odd` (odd solvable, p≠2, P Syl,
  `O_{p'}(G)=⊥`, **`C_G(Z(P))=P`** ⟹ J(P)◁G)、via `Ch07.normal_J` (Isaacs Thm 7.6 = ZJ)。

downstream FT (§8/§9, mmd L2471/2495/2528) は **J(S) 形** (Z(J(P))◁M) を cite。FT は完成済ゆえ
FT の使用は reduced J(S) or L(S) で満たされている。

## 一般化の課題 (M-sized, 不確実)

literal J(S) 一般形 `Z(J(S))·O_{p'}(G)◁G` を全 odd solvable G で:
1. **O_{p'} reduction**: L(S) と同じく Ḡ=G/O_{p'}(G) へ商、S̄=mk(S)≅S。tractable (L(S) mirror)。
2. **⚠ ZJ hypothesis discharge (crux)**: `normalJ_normal_of_odd` は `C_G(Z(P))=P` (P self-centralizing)
   を要求。これは L(S) 形が要らない強い条件。一般 odd solvable G (O_{p'}=1) で `C_G(Z(P))=P` は
   **自動でない**。標準 Glauberman ZJ は G p-stable (odd ⟹ 成立) + p-constrained (C_G(O_p(G))≤O_p(G)、
   solvable+O_{p'}=1 で成立) を要求だが、repo の `Ch07.normal_J` の hypothesis `C_G(Z(P))=P` とは別。
   ⟹ **Ch.7 に p-constrained 版 ZJ entry point があるか、`C_G(Z(P))=P` を discharge する route が
   あるか要調査**。

## 判断メモ

book 自身が L(S) を推奨代替として提示 (Remark)、L(S) 一般形は済。J(S) 一般形は genuine numbered
result だが FT gate 無 + ZJ hypothesis 不確実。**subagent が ZJ discharge を tractable と判断すれば
形式化、intractable なら (a) Ch.7 の p-constrained ZJ を先に整備 or (b) L(S) 形が role を満たす旨を
docstring 注記して pending 化** (feedback-generalize-specialized-fully の「一般化が数学的に無意味」
判定 = book が L(S) を推奨、要検討)。

## 参照

- BG mmd L1990-1994 (Thm 6.2 + Remark)、App.B (B.4/L(S))、既存 AppB_Thm62 / S06_Additional /
  Isaacs Ch07 (normal_J, ZJ)、survey L351
