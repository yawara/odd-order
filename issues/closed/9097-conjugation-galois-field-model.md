---
id: 9097
slug: conjugation-galois-field-model
title: "shared-infra claim: elementary-abelian conjugation action to norm-one Galois field model"
created: 2026-07-14
---

# Shared conjugation-to-field model for the `(9.7.b)` branch

> **CLAIM (lane a, 2026-07-14)**: build the missing generic bridge from an elementary-abelian
> kernel and a faithful abelian conjugation complement to the concrete norm-one Galois-field
> representation consumed by the semilinear field-model embedding. Other lanes should cite this
> leaf rather than duplicate the `S`/`T` module plumbing.

## Scope and non-dup audit

Existing infrastructure already proves the two adjacent layers:

- `SingerField.exists_galoisField_repr` constructs the additive field isomorphism and injective
  multiplicative character from an abstract faithful module action;
- `SemilinearFieldModel.fieldModelEmbedding` turns such a representation, once its image is the
  norm-one subgroup, into the required semidirect-product embedding.

The missing layer is the reusable adapter between them. The current `S`-side proof
`S16.exists_pu_field_repr` repeats the conjugation representation and group-algebra module setup,
while the `T`-side gate in `S16_NonExistenceG/SubgroupM.lean` still asks for the same data as a bare
existence obligation. Search found no generic theorem providing this adapter or the norm-one image
equality.

## Deliverable

- [x] Add a topic-coherent shared leaf under `OddOrder/GroupTheory/RepresentationTheory/` proving:
  1. an injective character of cyclotomic order has image exactly `normOneUnits`;
  2. an elementary-abelian subgroup `E` of order `r^s`, normalized faithfully by a commutative
     subgroup `C` of cyclotomic order, admits the full `(e, μ, injective, range, equivariance)`
     Galois-field model.
- [x] Register both endpoints in `AxiomsCheck` and build the leaf/full import closure.

Completed in `ConjugationFieldModel.lean`. The leaf build and the `OddOrder.AxiomsCheck`
import-closure build both pass; the two public endpoints are individually checked against the
repository's allowed-axiom set.

## Consumers

- Peterfalvi `(14.2)(a)`, `S`-side `P/U` field normalizer;
- Peterfalvi `(14.4)`, `T`-side `Q/V` field model and Frobenius-kernel centralizer bound.

This is the A-owned `(9.7.b)` Singer/field body identified by issues 9000 and 9078. It does not
edit lane B's active §13/§15 character assembly or lane C's Section 16 consumer files.
