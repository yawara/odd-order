/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupIdentification
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionThree

/-!
# Peterfalvi Part II, Ch. IV §3: `Q` in the unitary coordinates of `PSU(3, q)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4), p. 131.

Stage (4) of §3 is stated in the book's unitary coordinates: `ρ = (ρ̄, y)` with
`y + y^q = ρ̄^{1+q}`, and the assertion is `f(ρ) = (ρ̄/y, 1/y)`.  The development so
far presents `Q` instead as the model `S₁` of Ch. III §3, that is as
`BilinearTwistedProduct φ`, whose second coordinate ranges over the *subfield* `F`
freely.  The two are different presentations of one group, and this file identifies
them.

The identification is not a change of coordinates in `Q` alone: it also has to move
`E` onto the standard field of order `q²`, since `RootGroup` is built on the latter.
Both halves are supplied by
`ProjectiveUnitary.nonempty_mulEquiv_rootGroup_of_anisotropic`; what this file adds is
that its hypotheses are exactly what Ch. III §3 and §3 (3) have already produced —
`φ` anisotropic and, because `θ = 1`, `F`-bilinear.

## Main results

* `Hypothesis.nonempty_mulEquiv_rootGroup` — `Q ≅ RootGroup q`, the unipotent group of
  `PSU(3, q)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω)

include hyp in
/-- **`Q` is the unipotent group of `PSU(3, q)`** (Peterfalvi Part II, Ch. IV §3 (4),
p. 131): the coordinates in which stage (4) is stated.

The input is the model of Ch. III §3 — an isomorphism `Φ : Q ≃ BilinearTwistedProduct φ`
with `φ` anisotropic and `F`-semilinear with twist `θ` — together with `θ = 1` on `F`,
which is §3 (3) (`stepThree`, wired to the model's twist by
`thetaModel_eq_id_on_frobFixed`).

`θ` is taken as a bare function because the two forms in which it arrives — the
`ZMod 2`-algebra equivalence of `exists_standardModel` and the ring homomorphism of
`thetaModel_eq_id_on_frobFixed` — differ only by their bundling, and only its values on
`F` are used. -/
theorem nonempty_mulEquiv_rootGroup {m : ℕ} (M : hyp.QuotientFieldModel m) (hm : 0 < m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (θm : M.E → M.E)
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hθ : ∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, θm a = a)
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ) :
    Nonempty (↥hyp.Q ≃* RootGroup m) := by
  refine (nonempty_mulEquiv_rootGroup_of_anisotropic hm M.card φ ?_ haniso).map
    fun e => Φ.trans e
  intro a ha b hb x y
  rw [hsemi a ha b hb x y, hθ b hb]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
