---
id: 3015
slug: cor419-general
title: "BG Cor 4.19 一般形: G* general の chief-factor centralizing (O_{p'}(G*)=1 reduction)"
created: 2026-07-18
---

# BG Cor 4.19 一般形

## 背景

BG §4 の最後の残 (特殊化債務、survey L338)。§4 numbered 結果 + Thm 4.12 一般化は完成。
現状 = S04g_Thm418.lean に **reduced form** (normal p-subgroup R with pRank ≤ 2, U ≤ R⊔V)。
full 形は O_{p'}(G*)=1 reduction が要る。

## statement (BG mmd L1758)

> p prime, G solvable, G* ◁ G, r_p(G*) ≤ 2 and |G| odd ⟹ G' が、U ⊆ G* かつ U/V が p-群である
> 全ての chief factor U/V of G を中心化する。

## 証明 (BG mmd)

O_{p'}(G*)=1 に帰着 (Thm 4.18 proof 同様、`core418` 相当)。R = O_p(G*) は Thm 4.18 で G* の
Sylow-p。ゆえ U ⊆ RV。C = C_G(U/V)。Lemma 4.17 で (G/C_G(R))' は p-群 ⟹ (G/C)' p-群。G/C が
U/V に faithful irreducible 作用ゆえ O_p(G/C)=1 ⊇ (G/C)' = G'C/C ⟹ G' ⊆ C。

## 既存 reduced endpoint (reuse)

- `commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup` (S04g_Thm418:326):
  `(hodd : Odd |G|) (hp_odd : Odd p) {R U V}[R.Normal][V.Normal][(U.map mk' V).Normal]
   (hChief : IsChiefFactor U V) (hUbar_pg : IsPGroup p ↥(U.map mk' V)) (hR_pg : IsPGroup p ↥R)
   (hR_rank : pRank ↥R p ≤ 2) (hU_le_RV : U ≤ R ⊔ V) : commutator G ≤ chiefFactorCentralizer U V`。
- `core418` (private, S04g_Thm418:470) = O_{p'}=1 reduction。Thm 4.18 (`opCore` が Sylow) も同 file。

## やること (general wrapper)

- [ ] R := O_p(G*) (`Ch01.opCore p G*` を G の subgroup として; O_p(G*) char G* ◁ G ⟹ R ◁ G)。
      pRank R ≤ r_p(G*) ≤ 2。
- [ ] **O_{p'}(G*)=1 reduction** (crux): general G* から、U ≤ R⊔V を確立。O_{p'}(G*)≠1 なら
      商 or core418 相当の argument。**このステップが主 friction** — Thm 4.18 の O_{p'}(G*)=1 版
      (R=O_p(G*) が G* の Sylow-p、U⊆RV) を normal-subgroup G* 版に。
- [ ] reduced endpoint 適用で `commutator G ≤ chiefFactorCentralizer U V`。

## 完了条件

BG Cor 4.19 一般形 (general G*, U⊆G*, U/V p-chief factor ⟹ G' centralizes) を book strength・
sorry-free・axiom-clean。AxiomsCheck 登録、survey 正本 Cor 4.19「済」⟹ **BG §4 完全完成**。
⚠ specialization debt ゆえ FT gate 無 (reduced form が FT で使われる); reduction が真に困難なら
sticking point を報告して §6 へ移ってもよい。

## 参照

- BG mmd L1758-1770、既存 S04g_Thm418 (reduced form, Thm 4.18, core418)
- survey L338
