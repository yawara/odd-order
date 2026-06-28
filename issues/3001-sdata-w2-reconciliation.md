---
id: 3001
slug: sdata-w2-reconciliation
title: "Section16 carrier should expose Sdata.W2 = W2 (mirror of Sdata_U_eq/W1_eq)"
created: 2026-06-29
---

# Section16 carrier should expose Sdata.W2 = W2 (mirror of Sdata_U_eq/W1_eq)

**Lane:** c (γ POLE-2 §15/§16) raising; owner of fix = **lane d** (`Section16TypePStructure`) + FT spine assembly.

## 背景

`OddOrder.Peterfalvi.S15.Hypothesis` (Peterfalvi (13.1)) carries the intrinsic type-`P` data of `S`
as `Sdata : TypePData S`, reconciled to the abstract hypothesis fields by `Sdata_U_eq : Sdata.U = U`
and `Sdata_W1_eq : Sdata.W1 = W1` — but **not** for the `W₂` factor (no `Sdata_W2_eq`).

This blocks deriving `Nat.card Sdata.W2 = p` from the bare hypothesis, the only input (beyond
`IsTypeII S`) needed to read off Peterfalvi (13.2.b)'s order claim `|S_F| = p^q` from §11's Wielandt
relation `typeII_III_IV_order_relations`.

`S15.Hypothesis.card_P_eq` (S15_SAndT_Setup.lean) currently proves `|P| = p^q` **conditional on**
an explicit `hSdataW2 : Sdata.W2 = W2`. Supplying it from the carrier makes the order unconditional
and lets `basic_structure_gated`'s `P_order` field be discharged honestly (leaving only
`P_elementaryAbelian` + `u_bound` = genuine §10/§11/§9 content).

## やること

- [ ] lane d: `Section16TypePStructure` expose `Sdata.W2 = W2` next to `Sdata_U_eq`/`Sdata_W1_eq`
      (intrinsic `TypePData.W2 = C_{M'}(W₁#)` ↔ abstract `W₂` = `W₁`-complement in cyclic `W = S∩T`;
      may be `sorry`'d at carrier per no-gates policy).
- [ ] add `Sdata_W2_eq : Sdata.W2 = W2` field to `S15.Hypothesis`; thread through `Section16Inputs`
      / `sectionSixteenHypothesis_of_inputs` (FeitThompson.lean).
- [ ] drop the explicit `hSdataW2` hypothesis from `card_P_eq`; use the field.

## 完了条件

`S15.Hypothesis.card_P_eq` usable unconditionally; `basic_structure_gated.P_order` discharged.

## 参照

- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean` — `Hypothesis.card_P_eq`, `basic_structure_gated`
- `OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean:618` — `typeII_III_IV_order_relations`
- `OddOrder/FeitThompson.lean:1828` — `sectionSixteenHypothesis_of_inputs`
