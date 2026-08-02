/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.RankOneSetup
import OddOrder.Peterfalvi.Appendices.Suzuki.StandardModelHypothesis

/-!
# The mappings `f`, `g`, `h` of the standard `PSU(3, q)` model

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §1 (p. 122) and §3 (4)–(5) (pp. 130–131).

`standardHypothesis` puts the standing hypothesis on `standardPermGroup n`, so Ch. IV §1
supplies mappings `f`, `g`, `h` there too, characterised by

  `t x t = g(x) h(x) t f(x)`   (`x ∈ Q^#`).

In the standard model that equation is already available as a *computation*: it is the
nontrivial Bruhat relation

  `w R(u) w = R(JFJ(u)) · T(u₂/ū₂²) · w · R(F(u))`

of `Unital.weylPerm_mul_rootPerm_mul_weylPerm_eq_bruhat`, whose right-hand side is
literally of the shape `p · d · t · q` with `p, q` root elements and `d` a torus element.
The read-off lemma `fgh_eq_of_canonical` therefore identifies all three mappings at once,
and in particular

  `f(R u) = R(u₁/u₂, 1/u₂)`,

which is exactly the formula the Proposition of §3 proves for an abstract `G`.  That
coincidence is what Corollary 1 of §3 (p. 132) runs on: the Lemma of §1 compares `G` with
the standard model through `Q` and `f` alone.

## Main results

* `standardModel_canonical` — the Bruhat relation read as a canonical factorization in
  `standardPermGroup n`.
* `standardModel_fgh_rootHom` — all three mappings at a root element.
* `standardModel_f_rootHom` — `f(R u) = R(F u)`: the standard model's `f` is the
  reciprocal `(ρ̄/y, 1/y)` of §3 (4).
* `exists_standardModel_fgh` — the mappings themselves, normalized at `1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
open OddOrder.GroupTheory.RankOneBNPair

section /- Ch. IV §1: the mappings of the standard model (p. 122) -/

variable {n : ℕ}

/-- **The Bruhat relation is a canonical factorization** (Peterfalvi Part II, Ch. IV §1,
p. 122).

`Unital.weylPerm_mul_rootPerm_mul_weylPerm_eq_bruhat` is an identity of permutations of
the unital; all four factors lie in `standardPermGroup n`, so it is equally an identity
there. -/
theorem standardModel_canonical (hn : 0 < n) (u : RootGroup n) (hu : u ≠ 1) :
    weylElement n * rootHom n u * weylElement n
      = rootHom n (RootGroup.weylReciprocal u hu) *
          psuTorusHom n (bruhatTorus u hu hn) * weylElement n *
            rootHom n (RootGroup.reciprocal u hu) := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_rootHom, coe_psuTorusHom, coe_weylElement]
  exact Unital.weylPerm_mul_rootPerm_mul_weylPerm_eq_bruhat u hu hn

/-- A root element is trivial only at the identity of the root group. -/
theorem rootHom_ne_one (u : RootGroup n) (hu : u ≠ 1) : rootHom n u ≠ 1 := fun hc =>
  hu (rootHom_injective n (by rw [hc, map_one]))

/-- **The three mappings of Ch. IV §1 at a root element of the standard model.**

`fgh_eq_of_canonical` turns the Bruhat relation into the values of `f`, `g`, `h`, since
its right-hand side is of the canonical shape: the two outer factors lie in the root
subgroup `Q` and the middle one in the determinant-one torus `D`. -/
theorem standardModel_fgh_rootHom (hn : 1 < n)
    {f g h : standardPermGroup n → standardPermGroup n}
    (H : IsFGH (standardBorel n) (standardRootSubgroup n) (psuTorusHom n).range
      (weylElement n) f g h) (u : RootGroup n) (hu : u ≠ 1) :
    f (rootHom n u) = rootHom n (RootGroup.reciprocal u hu) ∧
      g (rootHom n u) = rootHom n (RootGroup.weylReciprocal u hu) ∧
        h (rootHom n u)
          = psuTorusHom n (bruhatTorus u hu (Nat.zero_lt_one.trans hn)) :=
  fgh_eq_of_canonical (standardHypothesis n hn).rankOneSetup H ⟨u, rfl⟩
    (rootHom_ne_one u hu) ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩
    (standardModel_canonical (Nat.zero_lt_one.trans hn) u hu)

/-- **The standard model's `f` is the reciprocal `(ρ̄/y, 1/y)`** (Peterfalvi Part II,
Ch. IV §3 (4), p. 131).

This is the conclusion the Proposition of §3 establishes for an abstract `G`; here it is a
direct computation in the standard coordinates, which is what makes Corollary 1's
comparison possible. -/
theorem standardModel_f_rootHom (hn : 1 < n)
    {f g h : standardPermGroup n → standardPermGroup n}
    (H : IsFGH (standardBorel n) (standardRootSubgroup n) (psuTorusHom n).range
      (weylElement n) f g h) (u : RootGroup n) (hu : u ≠ 1) :
    f (rootHom n u) = rootHom n (RootGroup.reciprocal u hu) :=
  (standardModel_fgh_rootHom hn H u hu).1

/-- **The mappings of the standard model exist**, normalized so that they fix `1`.

`Setup.exists_fgh_one` applied to `(standardHypothesis n hn).rankOneSetup`; the
normalization is what §3's Corollary 2 asks for (`f ρ ∈ Q` for *every* `ρ ∈ Q`). -/
theorem exists_standardModel_fgh (hn : 1 < n) :
    ∃ f g h : standardPermGroup n → standardPermGroup n,
      IsFGH (standardBorel n) (standardRootSubgroup n) (psuTorusHom n).range
          (weylElement n) f g h ∧ f 1 = 1 ∧ g 1 = 1 ∧ h 1 = 1 :=
  (standardHypothesis n hn).rankOneSetup.exists_fgh_one

end

end OddOrder.Peterfalvi.Appendices.Suzuki
