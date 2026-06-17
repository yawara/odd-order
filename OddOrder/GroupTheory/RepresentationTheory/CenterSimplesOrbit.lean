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

open OddOrder.GroupTheory.CenterClassSum (centerRep centerEnd)
open OddOrder.GroupTheory.PiAlgebraAut (algAutPerm algAutPerm_apply_single)

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
  have key : φ ((MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr (φ.symm (Pi.single i 1)))
      = (AlgEquiv.autCongr φ ((MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr))
          (Pi.single i 1) := by
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  rw [key, algAutPerm_apply_single]
  rfl

end OddOrder.GroupTheory.CenterSimplesOrbit
