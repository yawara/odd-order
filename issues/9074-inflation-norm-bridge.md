---
id: 9074
slug: inflation-norm-bridge
title: "shared infra CLAIM (lane c): surjective inflation isometry + trivial-char induction-inflation commute (Pf 13.18.b P-inflation norm bridge)"
created: 2026-07-07
---

# shared infra CLAIM (lane c): P-inflation norm bridge for Pf (13.18.b)

**claim-before-build (CLAUDE.md (C))**. Lane c claims the following generic representation-theory
infra, needed to close `indPW1_inner_self` / `indPW1_inner_mu` (the (13.18.b) `(A)`-tractable facts,
issue 0098 item 3). Grep confirmed **none of these exist** in repo as of 2026-07-07 (only the
MulEquiv-restricted `inner_compHom_mulEquiv` / `inner_compHom_of_mulEquiv` are present).

## やること (new lemmas, generic; home = `OddOrder/GroupTheory/RepresentationTheory/`)

- [ ] **P1 `innerSum_compHom_of_surjective` / `inner_compHom_of_surjective`**: for a surjective
  group hom `f : H →* G` (resp. quotient `mk' N`), the class-function inner product is preserved by
  pullback: `⟨compHom f φ, compHom f ψ⟩_H = ⟨φ, ψ⟩_G`. (Fibers of a surjective group hom all have
  card `|ker f|`; the `⅟|H|·|ker f| = ⅟|G|` normalization cancels.) Generalizes the existing
  MulEquiv version `inner_compHom_of_mulEquiv` (`InducedTransport.lean`).
- [ ] **P2 `induce_one_eq_compHom_induce_one_quotient`** (working name): for `N ⊴ G`, `N ≤ A ≤ G`,
  the induced trivial character commutes with inflation:
  `Ind_A^G 1_A = compHom (mk' N) (Ind_{A.map (mk' N)}^{G/N} 1)`. Pointwise via `induce_one_apply`
  (`S15_SAndT_Setup.lean:2564`) + the fiber-count `A = mk'⁻¹(A/N)`, `#{x : x⁻¹gx∈A} = |N|·#{x̄ : …}`.
  This is Peterfalvi's "(1.6.b): `Ind_{PW₁}^S 1` can be identified with `γ = Ind_{W̄₁}^{S̄} 1`".

## 完了条件

- `indPW1_inner_self` (`S15_SAndT.lean:3661`) と `indPW1_inner_mu` (:3673) が sorry-free 化。
- P1/P2 は sorry-free で `lake build` green。既存 sorry-free spine に sorry を混入しない。

## Consumers / route

- c-owned carve-out `betaGrid_norm` (Pf (13.18.b), `S15_SAndT.lean:3686`), via `indPW1_inner_self`
  + `indPW1_inner_mu`. Route: P2 + P1 + `norm_induce_one_frobenius` (`S15_SAndT_Setup.lean:2646`)
  on `S̄ = S/P` (Frobenius via `isFrobeniusGroup_map_equiv` on `BasicStructureData.UW1_frobenius`
  transported across `IsComplement'.QuotientMulEquiv`; complement/normal data already local in
  `coprime_card_P_card_UW1`, `S15_SAndT.lean:264`).
- Potentially reusable by any lane needing inflation-norm identities. If another lane needs P1/P2
  before this lands, coordinate here.

## 参照

- issue 0098 (lane c package, item 3), commit a1f14f98 (item 3 de-opacify), 93c2867a (betaData_of_grid).
- target `(u−1)/q+1` confirmed correct via `c_eq_one` (Pf 13.12, `|U| = uc = u`; `S15_SAndT.lean:196`).
- 既存 API: `inner_compHom_of_mulEquiv` / `induce_induce_subgroupOf` (`InducedTransport.lean`),
  `isFrobeniusGroup_map_equiv` (`Isaacs/Ch06_FrobeniusActions/FrobeniusGroupQuotient.lean:61`),
  mathlib `Subgroup.IsComplement'.QuotientMulEquiv` (`Complement.lean:639`).
