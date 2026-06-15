---
id: 8007
slug: mf-hall-gate-cor155
title: "M_F (maxNilpotentNormalHall) の Hall 性 — Cor 15.5 conjunct 5 ⊆ の gate"
created: 2026-06-15
---

# M_F の Hall 性 — Cor 15.5 conjunct 5 ⊆ の gate

## 背景

`fitting_decomposition` (BG Cor 15.5, `S15_MF.lean`) は 10.5/11 conjunct 完成
(`ec348bc3`)。残る唯一の孤立 sorry = **conjunct 5 の ⊆ 方向** (`S15_MF.lean:1472`):
`F(M) ⊆ (C_G(M_F) ⊓ M) ⊔ M_F`  (mmd 15.2(g) "F(M) = C_M(M_F)·M_F")。

⊇ は強化 Thm 15.2(g) (`F(M) = Q ⊔ (C_M(Q))`) で証明済。⊆ は
`F(M) = M_F × O_{π(M_F)'}(F(M))` (Hall-π(M_F) 分解) を要し、それには
**`O_{π(M_F)}(F(M)) = M_F`、すなわち M_F が F(M) の full Hall π(M_F)-part = M_F が Hall** が必要。

## ブロッカー

`maxNilpotentNormalHall` (= `MF M`) の **Hall 性は §15 で deferred** (file docstring
lines 65-69: `M_F ≤ M` / `M_F ⊴ M` / `M_F` nilpotent のみ available、Hall は未)。
`maxNilpotentNormalHall_isHall_of_typeI_or_II` は Peterfalvi S10 (downstream, import 不可) に在り、
かつ **type I/II 限定**の懸念 (Cor 15.5 conjunct 5 の Case II は type P1 = type P ゆえ要確認)。

## やること (選択肢)

- [ ] **(A)** §15 で `maxNilpotentNormalHall` の well-definedness「M_F は Hall」を landing
  (sSup of 冪零正規 Hall が再び Hall)。type P1 でも成立するか要確認。foundational。
- [ ] **(B)** Case II で `F(M) = M_F` を M_F Hall 経由せず示せるか精査 (Thm 15.2(g)
  `F(M)=Q C_M(Q)` から `C_M(Q) ⊆ M_F` が言えれば F(M)⊆M_F)。
- [ ] **(C)** conjunct 5 を等式のまま保持しつつ ⊆ を別補題に hoist (skeleton 化)。

## 完了条件

`fitting_decomposition` の conjunct 5 ⊆ sorry (`S15_MF.lean:1472`) が消え、Cor 15.5 が
cite 先 (Lemma 15.1/Thm 15.2/Cor 15.3) の sorry のみに gated な本体になる。

## 参照

- `notes/bg/s15_5_chatgpt_answer.md` (検証済証明 + 2 fixes)。
- mmd Cor 15.5 (L4225)、Thm 15.2(g) (F(M)=Q C_M(Q) ⊂ M_σ)。
- conjunct 5 は現状 **downstream 未消費** (Cor 15.6 は conjunct 11 のみ使用) ゆえ FT 経路を
  即座にはブロックしない (優先度: 中)。
