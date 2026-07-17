---
id: 2005
slug: huppert-schur-decomposition
title: "Pf App.B: Huppert pGroup_cyclic_fixedPointFree の non-cyclic sorry 残り (Schur⟹field⟹Z(P) cyclic + coprime 分解)"
created: 2026-07-18
---

# Pf App.B: `Huppert.pGroup_cyclic_fixedPointFree` non-cyclic sorry の残り

## 背景

`OddOrder/Peterfalvi/Appendices/Huppert.lean` の `pGroup_cyclic_fixedPointFree`
(Peterfalvi Appendix B Lemma, p.135–136) は唯一の sorry を残す = **irreducible
non-cyclic case** (`Huppert.lean` ≈L556–576)。

第一 prerequisite だった **Gorenstein 5.4.10 (odd p) = BG Lemma 4.5(a)** =「p odd 非
cyclic p-群 ⟹ 正規 type-(p,p)」は **2026-07-18 に証明済** (issue 2004 完了、
`OddOrder.BG.Ch1.S04.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic`)。

本 issue は**残りの Peterfalvi Appendix B 側の議論** (p.136) を追跡する。

## やること (Peterfalvi の non-cyclic case 議論の残り)

前提: `P` non-cyclic p-群 (p odd) が elementary abelian q-群 `E` に faithful かつ
irreducible に作用、constant point-stabilizer。正規 type-(p,p) `R ⊴ P` は取得済。

- [ ] **(i) Schur ⟹ Z(P) cyclic**: `End_{𝔽_q[P]}(E)` は Schur の補題 ([Is] 1.5) で
      division ring = 有限体 (Wedderburn)。`Z(P)` はその単元群の部分群ゆえ cyclic。
- [ ] **(ii) |R ∩ Z(P)| = p**: `Z(P)` cyclic + `R` 正規 type-(p,p) ⟹ `R ∩ Z(P)` は
      `R` (2 次元 F_p 空間) の高々 1 次元部分空間 = 位数 p (非自明: `R ⊴ P` は中心と交わる)。
      `P` は `R` の他の p 個の位数 p 部分群 `Tᵢ` を可移に置換。
- [ ] **(iii) coprime Z_p×Z_p 分解**: `E = ⊕ C_E(Tᵢ)` (`R ≅ Z_p×Z_p` の E への coprime
      作用) は `P`-permuted な直和分解 (≥ 2 parts)。
- [ ] **(iv) assembly**: part (1) `fpf_of_constant_stabilizer_of_permuted_decomp` を
      適用 ⟹ `P` cyclic を強制、non-cyclic 仮定と矛盾 ⟹ この case は空 (fpf 成立)。

## 完了条件

`Huppert.pGroup_cyclic_fixedPointFree` が sorry-free になり、下流の
`fitting_cyclic_fixedPointFree` (Appendix I Prop 1) が axiom-clean になる。
⟹ Pf Suzuki §2 Prop 2 の App I Prop 1 gate
(`Suzuki.Hypothesis.fitting_Dbar_cyclic_fpf_abelian`) も axiom-clean。

## 参照

- `OddOrder/Peterfalvi/Appendices/Huppert.lean` `pGroup_cyclic_fixedPointFree`
  (non-cyclic sorry, ≈L576) — STATUS コメントに残り 3 項 (i)(ii)(iii) を明記済。
- 既存 engine: `fpf_of_constant_stabilizer_of_permuted_decomp` (part 1),
  `fpf_of_reducible`, `fpf_of_abelian_of_irreducible` (同ファイル)。
- `references/peterfalvi/06.0_pp_135_136_*.mmd` (Appendix B 原文; p.136)。
- 完了済 prerequisite: `BG/Ch1_Preliminary/S04_SmallRankBasic.lean` §4E
  (`exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic`),
  `GroupTheory/NormalElementaryAbelianPrimeSq.lean`.
- 下流 gate: `Peterfalvi/Appendices/Suzuki/KCyclic.lean`
  `fitting_Dbar_cyclic_fpf_abelian`.
