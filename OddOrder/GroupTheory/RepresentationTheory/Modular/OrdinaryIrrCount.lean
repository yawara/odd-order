/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis
import OddOrder.GroupTheory.RepresentationTheory.CenterSplitting
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryOrthogonality

/-!
# The character table over a splitting field is square

`|Irr(G)| = |cl(G)|`.  Over a splitting field `K` the ordinary irreducibles are the Wedderburn
blocks of `K[G]` (`OrdinaryIrreducibles`), so the statement is that the number of blocks equals the
number of conjugacy classes — and both are the `K`-dimension of the centre `Z(K[G])`:

* the **class sums** are a basis of `Z(K[G])`, indexed by `cl(G)`
  (`CenterClassSum.centerBasis`);
* the Wedderburn isomorphism carries `Z(K[G])` to `∏_i Z(M_{m_i}(K)) = ∏_i K`, indexed by the
  blocks (`AlgEquiv.centerCongr`, `CenterSplitting.centerPiEquiv`,
  `CenterSplitting.matrixCenterEquiv`).

Squareness is exactly what upgrades the *first* orthogonality relation
(`sum_character_mul_character_inv`) to the *second*: a one-sided inverse of a square matrix is
two-sided.

## Main results

* `OddOrder.RepresentationTheory.Modular.centerAlgEquivPi` — `Z(K[G]) ≃ₐ[K] (Irr(G) → K)`
* `OddOrder.RepresentationTheory.Modular.card_eq_card_conjClasses`
* `OddOrder.RepresentationTheory.Modular.equivConjClasses` — the resulting bijection
-/

namespace OddOrder.RepresentationTheory.Modular

open Module OddOrder.GroupTheory

variable {K G : Type*} [Field K] [Group G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-- **The centre of `K[G]` is the function space on the Wedderburn blocks.**  The centre of a
product is the product of the centres, and the centre of a full matrix algebra over a field is the
scalars. -/
noncomputable def centerAlgEquivPi :
    Subalgebra.center K (MonoidAlgebra K G) ≃ₐ[K] (ι' → K) :=
  e.centerCongr.trans (CenterSplitting.centerPiEquiv.trans
    (AlgEquiv.piCongrRight fun _ => CenterSplitting.matrixCenterEquiv))

variable [Finite G] [Fintype (ConjClasses G)] [Fintype ι']

include e in
/-- **The character table over a splitting field is square**: the number of Wedderburn blocks of
`K[G]` — that is, of ordinary irreducible characters — is the number of conjugacy classes.  Both
count a basis of `Z(K[G])`. -/
theorem card_eq_card_conjClasses : Fintype.card ι' = Fintype.card (ConjClasses G) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h1 : finrank K (Subalgebra.center K (MonoidAlgebra K G)) = Fintype.card ι' := by
    rw [(centerAlgEquivPi e).toLinearEquiv.finrank_eq, Module.finrank_pi]
  have h2 : finrank K (Subalgebra.center K (MonoidAlgebra K G))
      = Fintype.card (ConjClasses G) :=
    finrank_eq_card_basis (CenterClassSum.centerBasis (k := K) (G := G))
  rw [← h1, h2]

/-- The bijection between the ordinary irreducibles and the conjugacy classes supplied by
`card_eq_card_conjClasses`.  It is not canonical — only its existence matters, and only in order
to view the character table as a square matrix. -/
noncomputable def equivConjClasses : ι' ≃ ConjClasses G :=
  Fintype.equivOfCardEq (card_eq_card_conjClasses e)

end OddOrder.RepresentationTheory.Modular
