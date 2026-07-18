---
id: 1038
slug: thompson-wielandt-9-24
title: "Theorem 9.24 general Thompson-Wielandt (+ 9.23)"
created: 2026-07-18
---

# Theorem 9.24 general Thompson-Wielandt (+ 9.23)

## 背景

Isaacs §9C の主結果 (p. 283, mmd L5155)。§9C の tool 群は 2026-07-18 に全 landed:
- 9.25 (`LayerRestriction.lean` `map_layer_eq_layer_of_fitting_eq_bot`): F(G)=1 ⇒ E(G)=E(H)。
- 9.26/9.27 + O^p core (`PResidual.lean`): O^p(SP)=O^p(S) / O^p(S)◁G。
- 9.18 (`SubnormalSocle.lean`), 9.8 (`GeneralizedFitting.lean`) も既 landed。

9.24 の deps は全て揃っている (9.24 は 9.27 を使い 9.26 は不使用)。

## 9.24 の statement (要 core_H(D) infra)

`H, K` 相異なる部分群, `D = H∩K`。仮説: **D の非自明部分群は H または K を真に含む
どの部分群にも normal でない**。`M = core_H(D)`, `N = core_K(D)`, `E = M∩N`,
`U = core_H(E)`, `V = core_K(E)`。結論: **ある素数 p で U または V が p-群**。

`core_H(D)` = D に含まれ H に normal な最大部分群 = `((D.subgroupOf H).normalCore).map H.subtype`
(mathlib `Subgroup.normalCore` の相対版; transport infra を新設)。

## やること

- [ ] `core_H(D)` (relative normalCore) の infra: 定義 + `≤ D`, `◁ H`, 最大性,
      `map`/`subgroupOf` transport。mathlib `normalCore` を ↥H で使い subtype で戻す。
- [ ] 9.24 statement の形式化 (上記仮説を Prop で; "H または K を真に含む部分群" の量化)。
- [ ] 9.24 proof (書籍 p. 283–284, ~40 行, 2 ケース):
      - F(H)=F(K)=1: E(H),E(K)>0, 9.18 で E(H)⊆N_G(V^∞)=K, 9.25 で E(H)=E(D)=E(K),
        H=N_G(E(H))=K 矛盾 → U or V trivial (p-群)。
      - F(H)>1 (or F(K)): O_p(H)=P>1, 9.27 で P normalizes O^p(V)=Y, cores で
        P ⊆ O_p(H)=O_p(K), H=N_G(P)=K 矛盾。
      使用: F*/9.8 (C_G(F*)⊆F*), 9.18, 9.25, 9.27, `core`, `O_p` (repo `opPi`), N_G。
- [ ] **Theorem 9.23** (Thompson corefree bound): 9.24 の系。corefree maximal H,
      K=H^g, a=b=m で `|H:O_p(H)| ≤ ((m!)²)!`。index bounds は 9.14 (n!-thm) 経由。

## 完了条件

9.24 + 9.23 を sorry-free/axiom-clean で landing。full build green + AxiomsCheck OK。

## 参照

- references/isaacs/finite-group-theory.mmd L5151–5188 (§9C); PDF p. 283–284
- OddOrder/Isaacs/Ch09_MoreSubnormality/{PResidual,LayerRestriction,SubnormalSocle,
  GeneralizedFitting}.lean
- notes/isaacs/ch09_more_subnormality.md §9C 節
