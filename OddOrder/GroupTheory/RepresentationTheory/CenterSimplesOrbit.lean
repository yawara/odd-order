/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterSplitting
import OddOrder.GroupTheory.RepresentationTheory.PiAlgebraAut

/-!
# The `MulAut G`-action on the simples, and its compatibility with `centerRep`

For Peterfalvi (9.1)'s orbit-count Brauer lemma (simples side), fix a splitting
`φ : Z(k[G]) ≃ₐ[k] (Fin N → k)` (from `exists_center_algEquiv_pi`).  `MulAut G` acts on the
"simples" `Fin N` by transporting `centerRep` through `φ` and reading off the coordinate
permutation:
`simplesAction φ = algAutPerm ∘ (autCongr φ) ∘ centerCongrHom ∘ domCongrAut`.

The key compatibility — the `hρ` the cornerstone needs — is
`centerRep g (φ.symm (Pi.single i 1)) = φ.symm (Pi.single (simplesAction φ g i) 1)`:
`centerRep g` is `domCongr g` restricted to the centre, so `φ ∘ centerRep g ∘ φ.symm` is the algebra
automorphism `autCongr φ (...)` of `Fin N → k`, which permutes the standard idempotents by
`simplesAction φ g` (`algAutPerm_apply_single`).
-/

open OddOrder.GroupTheory.CenterClassSum (centerRep centerEnd CenterCarrier centerRep'
  finrank_centerRep_invariants_eq_card_orbits)
open OddOrder.GroupTheory.PiAlgebraAut (algAutPerm algAutPerm_apply_single)
open OddOrder.GroupTheory.PermutationInvariants (finrank_invariants_eq_card_orbits)
open Module MulAction

namespace OddOrder.GroupTheory.CenterSimplesOrbit

variable {k G : Type*} [Field k] [Group G] {N : ℕ}
  (φ : Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin N → k))

/-- `centerRep g` is `domCongr g` restricted to the centre, as an algebra automorphism. -/
theorem centerRep_eq_centerCongr (g : MulAut G) (z : Subalgebra.center k (MonoidAlgebra k G)) :
    centerRep g z = (MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr z :=
  Subtype.ext (by rw [CenterSplitting.centerCongr_apply]; rfl)

/-- The action of `MulAut G` on the simples `Fin N`, via the splitting `φ`:
`MulAut G →* Aut k[G] →* Aut Z →* Aut (Fin N → k) →* Perm (Fin N)`. -/
noncomputable def simplesAction : MulAut G →* Equiv.Perm (Fin N) :=
  algAutPerm.comp ((AlgEquiv.autCongr φ).toMonoidHom.comp
    (AlgEquiv.centerCongrHom.comp
      (MonoidAlgebra.domCongrAut (R := k) (A := k) (M := G))))

/-- **Compatibility for the cornerstone (simples side).**  `centerRep g` permutes the idempotent
basis `i ↦ φ.symm (Pi.single i 1)` according to the `simplesAction`. -/
theorem centerRep_apply_symm_single (g : MulAut G) (i : Fin N) :
    centerRep g (φ.symm (Pi.single i 1)) = φ.symm (Pi.single (simplesAction φ g i) 1) := by
  apply φ.injective
  rw [AlgEquiv.apply_symm_apply, centerRep_eq_centerCongr]
  have key :
      φ ((MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr (φ.symm (Pi.single i 1)))
        = (AlgEquiv.autCongr φ ((MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr))
            (Pi.single i 1) := by
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  rw [key, algAutPerm_apply_single]
  rfl

/-! ### The idempotent basis and the simples-side orbit count -/

/-- The **primitive-idempotent (coordinate) basis** of `Z(k[G])`, transported from the standard
basis of `Fin N → k` through the splitting `φ : Z(k[G]) ≃ₐ[k] (Fin N → k)`:
`idemBasis φ i = φ.symm (Pi.single i 1)`.  Retyped over the `CenterCarrier` synonym (as for the
class-sum basis) so the cornerstone application stays clear of the `Module k` instance-diamond
blowup. -/
noncomputable def idemBasis : Basis (Fin N) k (CenterCarrier k G) :=
  (Pi.basisFun k (Fin N)).map φ.symm.toLinearEquiv

/-- `centerRep'` permutes the idempotent basis according to `simplesAction φ`:
`centerRep' g (idemBasis φ i) = idemBasis φ (simplesAction φ g i)`.  This is the simples-side `hρ`
that the cornerstone needs (compare `centerRep'_apply_centerBasis'` on the class-sum side); it
repackages `centerRep_apply_symm_single`. -/
theorem centerRep'_apply_idemBasis (g : MulAut G) (i : Fin N) :
    centerRep' (k := k) g (idemBasis φ i) = idemBasis φ (simplesAction φ g i) := by
  have e : ∀ j : Fin N, idemBasis φ j = (φ.symm (Pi.single j 1) : CenterCarrier k G) := by
    intro j
    change ((Pi.basisFun k (Fin N)).map φ.symm.toLinearEquiv) j = _
    rw [Basis.map_apply, Pi.basisFun_apply]
    rfl
  rw [e i, e (simplesAction φ g i)]
  exact centerRep_apply_symm_single φ g i

/-- **Orbit count via the idempotent basis** (the simples-side companion of
`finrank_centerRep_invariants_eq_card_orbits`).  Given the splitting `φ` and any
`MulAut G`-action on the simples `Fin N` that agrees with `simplesAction φ`, the dimension of the
`MulAut G`-invariants of `Z(k[G])` equals the number of `MulAut G`-orbits on `Fin N`. -/
theorem finrank_centerRep_invariants_eq_card_orbits_simples [MulAction (MulAut G) (Fin N)]
    (hact : ∀ (g : MulAut G) (i : Fin N), g • i = simplesAction φ g i) :
    finrank k ↥(Representation.invariants (centerRep' (k := k) (G := G)))
      = Nat.card (orbitRel.Quotient (MulAut G) (Fin N)) := by
  apply finrank_invariants_eq_card_orbits (idemBasis φ) centerRep'
  intro g i
  rw [hact g i]
  exact centerRep'_apply_idemBasis φ g i

-- The `Fintype`/`DecidableEq` instances feed the class-sum capstone via `centerBasis`: used in the
-- proof but not the statement type, so suppress the in-type linters (cf. `CenterClassSumBasis`).
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The orbit-count Brauer equality** (Peterfalvi (9.1), step 3 payoff).  Over the splitting `φ`,
the number of `MulAut G`-orbits on conjugacy classes equals the number on the simples `Fin N`.
Both compute `dim Z(k[G])^{MulAut G}` — in the class-sum basis and the idempotent basis
respectively — so the two orbit counts agree, with no characteristic-0 / Teichmüller input. -/
theorem card_orbits_classes_eq_card_orbits_simples
    [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]
    [MulAction (MulAut G) (Fin N)]
    (hact : ∀ (g : MulAut G) (i : Fin N), g • i = simplesAction φ g i) :
    Nat.card (orbitRel.Quotient (MulAut G) (ConjClasses G))
      = Nat.card (orbitRel.Quotient (MulAut G) (Fin N)) := by
  rw [← finrank_centerRep_invariants_eq_card_orbits (k := k) (G := G)]
  exact finrank_centerRep_invariants_eq_card_orbits_simples φ hact

end OddOrder.GroupTheory.CenterSimplesOrbit
