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

## やること — ✅ 全完了 (2026-07-07)

- [x] **P1 `inner_compHom_mk'_eq`**: quotient inflation isometry `⟨φ∘mk', ψ∘mk'⟩_G = ⟨φ,ψ⟩_{G⧸N}`。
  fiber-card `card_filter_mk_eq` (= `QuotientGroup.card_preimage_mk` singleton) 経由。commit `8c14199c`。
- [x] **P2 `induce_one_eq_compHom_induce_one_of_le`**: trivial-char induction-inflation commute
  `Ind_A^G 1 = (Ind_{A/N}^{G/N} 1) ∘ mk'`。pointwise + fiber-count。commit `8c14199c`。
- [x] **P3 `inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker`**: inflated ⊥ irreducible with
  `N ⊄ ker`。Fourier + inflate 直交。commit `fbc983fd`。
  (すべて `InflationInduction.lean`、sorry-free = 標準 3 公理のみ。)

## 完了条件 — ✅

- [x] `indPW1_inner_self` (commit `cc01d946`) + `indPW1_inner_mu` (commit `dcda9592`) 実証明。
  ⟹ **Peterfalvi (13.18.b) `betaGrid_norm` 実証明** (両 half 完了)。
- [x] P1/P2/P3 sorry-free、`lake build OddOrder` green (3935 jobs)。既存 spine に sorry 非混入。
- [x] `indPW1_inner_mu` / `uW1_isComplement_P` / P1/P2/P3 は **完全 clean** (標準 3 公理)。
  `indPW1_inner_self` / `betaGrid_norm` の残 `sorryAx` は **`c_eq_one` (Pf (13.12)) のみ経由** —
  target `(u−1)/q+1` が必然的に要する既存上流 gate (spurious な §16 `basic_structure` 依存は
  commit `52a72f66` で除去し `typeP_uW1_frobenius` 直接化)。honest cite-of-sorried-upstream。

## 次 (この issue の外、0098 item 3 (B))

- (13.18.a)/(13.18.c,d) の Γ-facts (`betaGrid_support` / `gammaGrid_{independent,orthogonal_one,
  real,norm_bound}`) = **(5.3) S↔W Dade cross-relation** `τ_S(μ_{ij}−μ_{0j}) = δ_j(η_{ij}−η_{0j})`。

## Consumers / route

- c-owned carve-out `betaGrid_norm` (Pf (13.18.b), `S15_SAndT.lean:3686`), via `indPW1_inner_self`
  + `indPW1_inner_mu`. Route: P2 + P1 + `norm_induce_one_frobenius` (`S15_SAndT_Setup.lean:2646`)
  on `S̄ = S/P` (Frobenius via `isFrobeniusGroup_map_equiv` on `BasicStructureData.UW1_frobenius`
  transported across `IsComplement'.QuotientMulEquiv`; complement/normal data already local in
  `coprime_card_P_card_UW1`, `S15_SAndT.lean:264`).
- Potentially reusable by any lane needing inflation-norm identities. If another lane needs P1/P2
  before this lands, coordinate here.

## ✅ CLOSED (2026-07-07)

P1/P2/P3 実装 + (13.18.b) `betaGrid_norm` 実証明で完了。commits `8c14199c` (P1/P2), `fbc983fd` (P3),
`cc01d946` (indPW1_inner_self + uW1_isComplement_P), `dcda9592` (indPW1_inner_mu +
P_not_subset_characterKernel_mu), `52a72f66` (spurious §16 gate 除去)。full build green (3935 jobs)。
残 sorryAx = (13.12) `c_eq_one` のみ (既存上流 gate, honest cite)。次 = 0098 item 3 (B) = (5.3) cross-relation。

## 参照

- issue 0098 (lane c package, item 3), commit a1f14f98 (item 3 de-opacify), 93c2867a (betaData_of_grid).
- target `(u−1)/q+1` confirmed correct via `c_eq_one` (Pf 13.12, `|U| = uc = u`; `S15_SAndT.lean:196`).
- 既存 API: `inner_compHom_of_mulEquiv` / `induce_induce_subgroupOf` (`InducedTransport.lean`),
  `isFrobeniusGroup_map_equiv` (`Isaacs/Ch06_FrobeniusActions/FrobeniusGroupQuotient.lean:61`),
  mathlib `Subgroup.IsComplement'.QuotientMulEquiv` (`Complement.lean:639`).
