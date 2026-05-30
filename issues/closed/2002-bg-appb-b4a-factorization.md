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

> **2026-05-30 完成 (commit 9f2d888)**: **BG Thm 6.2 一般形 `Z(L(S))·O_{p'}(G) ⊴ G` を
> sorry-free / 標準3公理で完成** (`OddOrder/BG/AppB_Thm62.lean`,
> `zCenter_lOdd_sup_oPiCore_normal`, `lake build OddOrder` green, AxiomsCheck 登録)。
> **設計変更**: 当初の「異群 iso `φ:G≃*H` 共変性」は不要 — 代わりに **`mk:G→G/O_{p'}` が
> `S` 上単射** (`S∩O_{p'}=⊥`) を使う **injOn-hom 共変性** (`lOddIn_map_of_injOn` =
> bridge `lOddIn_eq_map_subtype` + 像への iso `MonoidHom.ofInjective` + cross-group iso 共変性
> `lOddIn_map_equiv'`) で `mk(Z(L(S)))=Z(L(S̄))` を得た。B.4(a) (積/Frattini 形) は経由せず
> 直接 `Z(L(S))·O_{p'}=mk⁻¹(Z(L(S̄)))` (comap) で正規性を引き戻し。

## やること

- [x] **cross-group iso 共変性** `lRelIn/lNIn/lOddIn_map_equiv' (φ : G ≃* G')` —
      既存 same-group 証明を `map_equiv_normalizer_eq` (cross-group) で一般化。
- [x] **bridge** `lRelIn/lNIn/lOddIn_eq_map_subtype` — 相対 `L(H)` = 絶対 `L(↥H)` の subtype 像
      (`subgroupOf_normalizer_eq` 利用)。
- [x] **injOn-hom 共変性** `lOddIn_map_of_injOn` + `map_zCenterLOdd_of_injOn`
      (`map_centralizer_inf` 経由) で `S̄ ≅ S` の push を実現。
- [x] **BG Thm 6.2 一般形** `zCenter_lOdd_sup_oPiCore_normal : (Z(L(S)) ⊔ O_{p'}(G)).Normal`。

## 完了条件

- [x] BG Thm 6.2 一般形 sorry-free, `lake build OddOrder` green, AxiomsCheck 登録, 標準 3 公理のみ。

> **未着手 (任意)**: B.4(a) の **積/Frattini 形** `G = O_{p'}(G)·N_G(Z(L(S)))` 単独 statement は
> 本ルートでは不要だったため作らず。必要なら `normalizer_zCenter_lOdd_sup_oPiCore_eq_top` を別途。

## 参照

- 前提: issue 2001 (B.4(b) `zCenter_lOdd_normal_of_oPiCore_eq_bot`)。
- `bg-appb-b3b4-design` workflow 出力 (run wf_06198d42-7bc): 最終 lemma `normalizer_zCenter_lOdd_sup_oPiCore_eq_top` の BLOCKED 解析 + FIX 候補。
- `OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot` / `oPiCore.map_eq_of_mulEquiv` (Ch03 Main)。
- 原文 `references/bg/local-analysis.mmd` L4688, L4695-4703。
