---
id: 2002
slug: bg-appb-b4a-factorization
title: "BG App.B Theorem B.4(a) G=O_{p'}·N_G(Z(L(S))) (異群iso共変が前提)"
created: 2026-05-30
---

# BG App.B Theorem B.4(a) `G = O_{p'}(G)·N_G(Z(L(S)))`

## 背景

issue 2001 の **B.4(b)** (`O_{p'}(G)=1 ⇒ Z(L(S)) ⊴ G`) から **(a)** を導く部分を分離。
分離理由 (`bg-appb-b3b4-design` workflow の adversarial 検証で BLOCKED 判定):

(b)⇒(a) は `Ḡ = G/O_{p'}(G)` で `O_{p'}(Ḡ)=1`, `S̄ ∈ Syl_p(Ḡ)`, `S̄ ≅ S` を使い (b) を `Ḡ` に
適用して引き戻す (mmd L4695-4703)。だが **`Z(L(S̄)) = Z(L(S))·O_{p'}/O_{p'}`** を得るには
`lRelIn`/`lNIn`/`lOddIn` が **異群 iso `φ : G ≃* H`** で共変であることが必須。現状の
`lRelIn_map_equiv` (`AppB_Puig.lean`) は `φ : G ≃* G` のみ。

## やること

- [ ] **`lRelIn_map_equiv` の異群一般化** `(φ : G ≃* H) (K X : Subgroup G) :
      (lRelIn K X).map φ = lRelIn (K.map φ) (X.map φ)`。証明本体は cross-group 対応:
      `map_equiv_normalizer_eq` (Basic L705 は既に `f : G ≃* N` で cross-group), `map_isMulCommutative`,
      `map_mono` が全て cross-group ⇒ 既存 same-group 証明 (hAB/hBA 往復) とほぼ同型で書ける。
      → `lNIn_map_equiv` / `lOddIn` も `G ≃* H` 版に持ち上げ。
- [ ] `S̄ ≅ ↥S` の制限 iso (`O_{p'} ∩ S = 1` coprime; `QuotientGroup` の Sylow 対応) で
      `Z(L(S̄)) ↦ Z(L(S))·O_{p'}` を push。
- [ ] **Theorem B.4(a)**: `G = O_{p'}(G) ⊔ N_G(Z(L(S)))` (積/Frattini 形)。
      `normalizer_zCenter_lOdd_sup_oPiCore_eq_top` (issue 2001 設計の最終 lemma)。
- [ ] **`.map e` vs `.map e.toMonoidHom` の coe 統一**: `oPiCore.map_eq_of_mulEquiv` (Ch03 Main L1762) は
      `.map e`, `lRelIn_map_equiv` は `.map e.toMonoidHom`。`MulEquiv.coe_toMonoidHom`/simp で bookkeeping。

## 完了条件

- B.4(a) sorry-free, `lake build OddOrder` green, AxiomsCheck 登録, 標準 3 公理のみ。
- (a)+(b) を合わせて BG Thm 6.2 一般形 `Z(L(S))·O_{p'}(G) ⊴ G` の statement を用意 (別 issue でも可)。

## 参照

- 前提: issue 2001 (B.4(b) `zCenter_lOdd_normal_of_oPiCore_eq_bot`)。
- `bg-appb-b3b4-design` workflow 出力 (run wf_06198d42-7bc): 最終 lemma `normalizer_zCenter_lOdd_sup_oPiCore_eq_top` の BLOCKED 解析 + FIX 候補。
- `OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot` / `oPiCore.map_eq_of_mulEquiv` (Ch03 Main)。
- 原文 `references/bg/local-analysis.mmd` L4688, L4695-4703。
