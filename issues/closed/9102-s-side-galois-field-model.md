---
id: 9102
slug: s-side-galois-field-model
title: "shared: (14.6) S-side Clifford dichotomy to the Galois-field model"
created: 2026-07-15
---

# Shared S-side Galois-field model for Peterfalvi (14.6)

> **CLAIM (lane a, 2026-07-15)**: build the remaining upstream assembly between the
> completed (9.7.b) Singer realization (issues 9097/9100) and the completed case-(9.7.a)
> prime contradiction (issue 1038).  The c-owned consumer
> `S16.s_side_field_repr` remains untouched until hub/c performs the final proof-only cite.

## Non-dup audit

- `S11.caseB_exists_galoisField_repr_of_cSub_eq_bot` already realizes the faithful-image
  action on the chief quotient.
- `S15.Hypothesis.toTypesIIIIIIVSetupS_chief_N_eq_bot`,
  `toTypesIIIIIIVSetupS_cSub_eq_C`, `Sdata_U_eq`, and `Sdata.H_eq` identify that quotient
  with the named `P`/`U` S-instance.
- `S15.caseA_false_of_parameters_and_typeIOverNormalizerData` already eliminates the
  alternative Clifford branch at the explicit (13.12)/(13.13) parameters.
- No equivalent S-instance dispatcher or unmerged c implementation exists (repo and
  `main...c` scan on 2026-07-15).

## Deliverable

- [x] Add a topic leaf under `OddOrder/Peterfalvi/` which transports the case-(b) chief-factor
      field model to `Additive P` and the named `U` conjugation action.
- [x] Add the downstream-facing (14.6) dispatcher: Clifford case (a) requests its sharp
      parameter equalities from the actual case-(a) certificate and is refuted by the
      prime contradiction; case (b) returns the transported field model.  Retain an
      explicit-parameter specialization for callers that already have both equalities.
- [x] Register the public endpoints in `AxiomsCheck`; leaf/full builds green.
- [x] Notify hub/c that `S16.s_side_field_repr` can be a thin cite once its canonical
      `TypeIOverNormalizerData` and (13.12)/(13.13) parameters are supplied.

## Soundness and layering

The downstream-facing dispatcher keeps `c = 1`, the case-(a)-conditional producer of
`q = 3` and `u = (p-1)^2/4`, and `TypeIOverNormalizerData` explicit.  It therefore does
not hide the issue-0116 analytic producer or strengthen the generic S15 hypothesis.  In
particular, it does not incorrectly demand the case-(a) equalities in case (b).  The new
leaf is additive and consumed downstream by S16; no b/c-owned declaration is modified.

## References

- Peterfalvi (9.7.b), (14.6); `coq/theories/PFsection{9,14}.v`
- issues 9097, 9100, 1038, 0115, 0116

## Completion (lane a, 2026-07-15)

- Added `OddOrder/Peterfalvi/S15_SSideGaloisFieldModel.lean`.
- `S15.caseB_exists_sSide_galoisField_repr_of_c_eq_one` transports the honest
  §9 Singer realization through `H₀ = ⊥`, `H = P`, and the named `U`.
- `S15.sSide_galoisField_repr_of_c_eq_one_and_caseA_parameters` dispatches the proven
  Clifford dichotomy.  Its parameter producer is conditional on the case-(a)
  certificate, exactly as (13.13) is; case (a) is eliminated by issue 1038, while case
  (b) returns the transported model without demanding those equalities.
- `S15.sSide_galoisField_repr_of_parameters_and_typeIOverNormalizerData` is the
  specialization for callers that already have both sharp equalities.
- A direct probe of the existing c-owned `S16.s_side_field_repr` target succeeds with
  `simpa using S15.sSide_galoisField_repr_of_c_eq_one_and_caseA_parameters ...`.
  Hub/c therefore only needs to supply `c = 1`, the existing case-(a)-conditional
  (13.13) parameter producer, and the canonical `TypeIOverNormalizerData`; no target or
  proof-term adaptation is needed.
- Validation: leaf build, direct leaf elaboration, consumer thin-cite probe,
  `lake build OddOrder.AxiomsCheck`, and `lake build OddOrder` all green.
