/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_SixTwoImageData
import OddOrder.Peterfalvi.S13_Orthogonality

/-!
# The §13 column `R`-family is the (5.3)(b) certain-type family

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §5, p. 26.

The §13 packaging of clause (5.2.d) for a *reducible* member — `S12.Hypothesis.colRFamily`, built
from the §10 `alignedOmegaSigmaGrid` with the sign pinned to `params.delta` — has the **same
underlying set** as the abstract (5.3)(b) family `S06.certainTypeR`, which uses the raw §6
`certainTypeOmegaSigma` grid and the sign `(columnFamily χ₂).sign`.

## Why this is a bridge and not a replacement (issue 0160)

The obvious move — rewrite `colRFamily` as the abstract family — is **wrong**: the §13 form is not
a duplicate but carries strictly more, namely the `params.delta` alignment that the downstream
(5.5)/(9.11) column-pair machinery reads off `columnRImage`.  Replacing it would discard that.

What *is* true, and is what this file records, is that the two `imageSet`s coincide.  That is all
the (5.2.e) clause ever needs (`OrthonormalCharacterImageFamily.Orthogonal` is stated on
`imageSet`), so the abstract (5.3)(b) orthogonality lemmas apply to the §13 families through this
equality without touching a single downstream consumer.

## The four identifications

* **signs** — `muColumnSign_eq_columnFamily_sign` (definitional) plus the alignment `hδj`;
* **`σ`-grids** — `certainTypeOmegaSigma_muColumnChar_eq_aligned`;
* **row index** — the reindex `finCongr hcw1 : Fin w₁ ≃ Fin (card W₁)`;
* **conjugate column** — `muColumnChar_conj_eq_inv`, i.e. `j' ↔ χ₂⁻¹`
  (`columnSum_conj_eq` + `columnSum_injective`).

The first three are packaged as `columnRImage_image_eq_certainTypeRImage_image`
(`S13_Orthogonality`); this file supplies the fourth at the member's own columns and assembles.

Reference: issue 0160 (the follow-up of issue 0159, where the abstract (5.3)(b) landed).
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory
open OddOrder.GroupTheory
open scoped FiniteInduce

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

open scoped Classical in
/-- **The §13 reducible-member `R`-family is the (5.3)(b) certain-type family**, as sets.

`colRFamily` is `columnImageFamilyCohFree` transported to the member (`congrChi`), so its
`imageSet` is the image of `columnRImage δ j j'` over `Bool × Fin w₁`.  Rewriting by
`columnRImage_image_eq_certainTypeRImage_image` moves it into the §6 world at the duals
`(muColumnChar j, muColumnChar j')`, and `muColumnChar_conj_eq_inv` — fed the member's own
conjugate-column identity `columnSum_memberColumn_conj` — turns the second dual into
`(muColumnChar j)⁻¹`, which is exactly the pair `certainTypeR` is built from.

The sign hypothesis is discharged from the family's alignment datum `hδj` at the member's column,
which is nonzero by `memberColumn_ne_zero`. -/
theorem colRFamily_imageSet_eq_certainTypeR_imageSet
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    [NeZero (Nat.card ↥(hyp.toHypothesis46 hG hG.odd).W1)]
    (hcw1 : Nat.card ↥(hyp.toHypothesis46 hG hG.odd).W1 = hyp.w1)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    (hyp.colRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ hred).imageSet
      = (OddOrder.Peterfalvi.S06.certainTypeR (hyp.toHypothesis46 hG hG.odd)
          (hyp.muColumnChar_ne_one hG hG.odd (hyp.memberColumn_ne_zero hG hχ hred))
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.toHypothesis46 hG hG.odd)
            (hyp.muColumnChar hG hG.odd (hyp.memberColumn hG hχ hred))).symm).imageSet := by
  rw [Hypothesis.colRFamily,
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily.congrChi_imageSet]
  change Finset.univ.image (hyp.columnRImage hG hG.odd params.delta
      (hyp.memberColumn hG hχ hred) (hyp.memberColumnConj hG hχ hred)) = _
  rw [OddOrder.Peterfalvi.S13.columnRImage_image_eq_certainTypeRImage_image hG hyp hcw1
      (hδj _ (hyp.memberColumn_ne_zero hG hχ hred)),
    OddOrder.Peterfalvi.S13.muColumnChar_conj_eq_inv hG hyp
      (hyp.columnSum_memberColumn_conj hG hχ hred)]
  rfl

open scoped Classical in
/-- **The §13 (5.2.d) dispatch agrees with the abstract (5.3)(b) one on the reducible branch.**

`memberRFamily` reduces to `colRFamily` off the irreducible case (`memberRFamily_of_red`), so the
previous theorem transfers verbatim.  On the irreducible branch both dispatches produce the very
same `dadeOrthonormalCharacterImageFamilyOfDiff` (proof arguments are propositions, hence
irrelevant), so nothing is left to check there. -/
theorem memberRFamily_imageSet_eq_certainTypeR_imageSet
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    [NeZero (Nat.card ↥(hyp.toHypothesis46 hG hG.odd).W1)]
    (hcw1 : Nat.card ↥(hyp.toHypothesis46 hG hG.odd).W1 = hyp.w1)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    (hyp.memberRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ).imageSet
      = (OddOrder.Peterfalvi.S06.certainTypeR (hyp.toHypothesis46 hG hG.odd)
          (hyp.muColumnChar_ne_one hG hG.odd (hyp.memberColumn_ne_zero hG hχ hred))
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.toHypothesis46 hG hG.odd)
            (hyp.muColumnChar hG hG.odd (hyp.memberColumn hG hχ hred))).symm).imageSet := by
  rw [hyp.memberRFamily_of_red hG hmu hδpm hδj hzS hz1 hzconj hχ hred]
  exact colRFamily_imageSet_eq_certainTypeR_imageSet hG hyp hmu hδpm hδj hzS hz1 hzconj hcw1
    hχ hred

end OddOrder.Peterfalvi.S12
