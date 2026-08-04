/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionNumber

/-!
# `IBr(G)` is indexed by the `p`-regular classes

Brauer's count (`BrauerCount`) says the number of Wedderburn blocks of `kG ⧸ J(kG)` — that is,
`|IBr(G)|` — is the number of `p`-regular classes.  This file repackages it for the `π : →+*`
form in which the decomposition matrix is stated, and turns the equality of cardinalities into a
concrete indexing: an equivalence `ι ≃ cl(G°)` together with a `p`-regular representative
`pRegularRep j ∈ G` of each class.

That indexing is what makes the "column" side of Navarro (2.13) a *square* matrix problem: the
relation `∑_φ Φ_φ(x) φ(y⁻¹) = |C_G(y)| δ_{y ~ x}` becomes `A · B = 1` with `A`, `B` square, so a
one-sided inverse is two-sided and `[Φ_θ, φ]⁰ = δ_{θφ}` follows.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_eq_card_pRegularClass`
* `OddOrder.RepresentationTheory.Modular.equivPRegularClass`
* `OddOrder.RepresentationTheory.Modular.pRegularRep` and its two characterising lemmas
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Finite ι] [∀ i, Nonempty (nn i)]
variable (hp : p.Prime)
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))

include hp hπ hlin hkerJ in
/-- **Brauer's count in the form the decomposition matrix uses**: `|IBr(G)| = #cl(G°)`. -/
theorem card_eq_card_pRegularClass :
    Nat.card ι = Nat.card {C : ConjClasses G // IsPRegularClass p C} := by
  obtain ⟨N, hN⟩ := exists_pow_eq_zero_of_ker_eq_jacobson hkerJ
  have hk : ((p : ℕ) : ResidueField 𝒪) = 0 := CharP.cast_eq_zero _ p
  exact card_split_blocks_eq_card_pRegularClass hp hk (AlgHom.mk' π hlin) hπ hN AlgEquiv.refl

include hp hπ hlin hkerJ in
/-- **`IBr(G)` is indexed by the `p`-regular classes.**  Not canonical — only its existence
matters, and only so that the character-table-like matrices of Navarro (2.13) are square. -/
noncomputable def equivPRegularClass : ι ≃ {C : ConjClasses G // IsPRegularClass p C} := by
  haveI : Finite {C : ConjClasses G // IsPRegularClass p C} := Subtype.finite
  haveI : Fintype {C : ConjClasses G // IsPRegularClass p C} := Fintype.ofFinite _
  haveI : Fintype ι := Fintype.ofFinite ι
  refine Fintype.equivOfCardEq ?_
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact card_eq_card_pRegularClass hp hπ hlin hkerJ

/-- A `p`-regular representative of the class matched with `j : ι`. -/
noncomputable def pRegularRep (j : ι) : G :=
  ((equivPRegularClass hp hπ hlin hkerJ j : {C : ConjClasses G // IsPRegularClass p C}) :
    ConjClasses G).out

include hp hπ hlin hkerJ in
theorem isPRegular_pRegularRep (j : ι) : IsPRegular p (pRegularRep hp hπ hlin hkerJ j) :=
  isPRegular_out (equivPRegularClass hp hπ hlin hkerJ j).2

include hp hπ hlin hkerJ in
theorem mk_pRegularRep (j : ι) :
    ConjClasses.mk (pRegularRep hp hπ hlin hkerJ j)
      = (equivPRegularClass hp hπ hlin hkerJ j : ConjClasses G) := by
  rw [pRegularRep, ← ConjClasses.quotient_mk_eq_mk]
  exact Quotient.out_eq _

include hp hπ hlin hkerJ in
/-- Two indices give conjugate representatives only if they are equal. -/
theorem pRegularRep_isConj_iff (j j' : ι) :
    IsConj (pRegularRep hp hπ hlin hkerJ j) (pRegularRep hp hπ hlin hkerJ j') ↔ j = j' := by
  rw [← ConjClasses.mk_eq_mk_iff_isConj, mk_pRegularRep, mk_pRegularRep]
  exact ⟨fun h => (equivPRegularClass hp hπ hlin hkerJ).injective (Subtype.ext h),
    fun h => by rw [h]⟩

end OddOrder.RepresentationTheory.Modular
