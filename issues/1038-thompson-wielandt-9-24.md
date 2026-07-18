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

## 進捗 (2026-07-18)

**landed groundwork (全 sorry-free/axiom-clean, `ThompsonWielandt.lean` / `PResidual.lean`)**:
- `relCore H D` (core_H(D)) infra: `relCore_le` (≤D), `relCore_le_left` (≤H),
  `le_normalizer_relCore` (H≤N_G(core)), `le_relCore` (最大性)。
- `NoNormalInSupergroup H K D` (9.24 の仮説 predicate)。
- `normalizer_eq_left/right_of_noNormal`: 仮説から nonidentity N≤D が H(resp K) に normal
  なら N_G(N)=H(resp K)。proof の「H=N_G(U^∞)」deduction 用。
- `pResidual_eq_bot_iff_isPGroup`: O^p(U)=⊥ ⟺ U は p-群 (Case 2 結論用)。

## ⚠ proof body の要検討事項 (原文精読で確定した subtlety)

書籍 proof (p.283–284) を精読して判明した、着手前に解決すべき点:

1. **normal / subnormal**: `V = core_K(E)` は `K` に normal だが `H` には
   **subnormal のみ** (`V ◁ M ◁ H`, M=core_H(D))。書籍は "V◁H" と書くが:
   - Case 1 の 9.18 適用 (E(H)⊆N_G(V^∞)) は 9.18 が subnormal 版なので **OK**
     (`layer_le_normalizer_nilpotentResidual` は `S.IsSubnormal`)。要: V.subgroupOf H が
     ↥H で subnormal (V◁M◁H の chain を IsSubnormal で構成)。
   - Case 2 の 9.27 適用 (P normalizes O^p(V)) は現行 `pResidual_map_subtype_normal` が
     **V ◁ H (normal) を要求**。V subnormal では O^p(V)◁H が言えない可能性。
     → **subnormal 版 9.27 (V◁◁H, P◁H p-群 ⇒ P≤N_G(O^p(V))) が要るか要検討**
     (O^p の 9.16/9.18 相当 = 「F(G),E(G)≤N_G(S^∞) の O^p 版」)。
2. **nested transport**: Case 1 は 9.18/9.25/Fitting を `↥H`,`↥K`,`↥D` 内で適用し
   ambient に戻す必要 (E(↥H) と E(D) の関係、F(↥H)=⊥ from F(H)=1 等)。深い多段 subtype。
3. **Fitting**: F(H)=1 ⇔ Fitting ↥H = ⊥; nilpotent normal ≤ Fitting (Ch01) を ↥H で。

→ 9.24 本体は上記 (特に 1 の subnormal-9.27) を確定してから着手する dedicated effort。
deps (relCore/N_G/O^p/9.18/9.25/9.8) は landed。

## やること

- [x] `core_H(D)` (relative normalCore) の infra。
- [x] 仮説 predicate + N_G 補題 + pResidual_eq_bot_iff。
- [ ] 上記 subtlety 1 (subnormal-9.27) を確定 (原文/再構成)。
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
