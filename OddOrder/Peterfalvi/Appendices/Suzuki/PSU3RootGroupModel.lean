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

include hyp in
/-- **The cocycle is invariant under the norm-one scalars `μ(W)`** (Peterfalvi Part II,
Ch. III §3, p. 120: `K₁ W₁` acts by `(x, y)^a = (a x, a^{1+σ} y)`, and `a^{1+σ} = 1` on
`W₁`).

This is the `W`-half of `cocycle_scale_of_diagScale`: the constant by which the central
coordinate is scaled involves only the `K`-component (`centreQuadraticMap_smul_KW`), so
it is `1` on `W`. -/
theorem cocycle_invariant_W {m : ℕ} (M : hyp.QuotientFieldModel m)
    (sfive : hyp.LemmaFiveSetup m)
    (ι' : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d' : ℤ)
    (hequiv' : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι' (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d' : M.Eˣ) : M.E) *
          ((ι' (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hdiagscale : ∀ a b : M.E,
      (∀ x : M.E,
        ((hyp.centreQuadraticMap sfive M ι' (a * x) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((hyp.centreQuadraticMap sfive M ι' x :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) →
      ∀ x y : M.E,
        ((φ (a * x) (a * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((φ x y :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (v : ↥hyp.W) (x y : M.E) :
    ((φ (((M.mu (1, v) : M.Eˣ) : M.E) * x) (((M.mu (1, v) : M.Eˣ) : M.E) * y) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
  have h := hdiagscale _ _
    (fun z => hyp.centreQuadraticMap_smul_KW sfive M ι' d' hequiv' (1, v) z) x y
  have hone : M.mu ((1 : ↥hyp.actualKActor), (1 : ↥hyp.W)) = 1 := map_one M.mu
  rw [hone] at h
  simpa using h

include hyp in
/-- **The model's square map is the Hermitian norm, up to the scalar `φ(1,1)`**
(Peterfalvi Part II, Ch. IV §3, p. 130: the coordinates in which stage (4) is stated).

The scalars `μ(W)` have norm `1` and leave the cocycle invariant, and `W ≠ 1` with `|W|`
odd supplies one of order at least three; that is all
`cocycle_diag_eq_norm_smul_of_normOne_invariant` needs.  Unlike the general
classification, this keeps `E` and its scalar action fixed, which is what the
computations of §3 use. -/
theorem cocycle_diag_eq_norm {m : ℕ} (M : hyp.QuotientFieldModel m) (hm : m ≠ 0)
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
    (hW : ∀ (v : ↥hyp.W) (x y : M.E),
      ((φ (((M.mu (1, v) : M.Eˣ) : M.E) * x) (((M.mu (1, v) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hmu : Function.Injective M.mu) {ζ : ↥hyp.W} (hζ : ζ ≠ 1) :
    ∀ x : M.E, ((φ x x : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        * x ^ (2 ^ m + 1) := by
  -- the scalar attached to `ζ`
  have hne : ((M.mu (1, ζ) : M.Eˣ) : M.E) ≠ 1 := by
    intro hval
    have hmu1 : M.mu (1, ζ) = 1 := Units.ext hval
    exact hζ (congrArg Prod.snd (hmu (hmu1.trans (map_one M.mu).symm)))
  have hnorm : ((M.mu (1, ζ) : M.Eˣ) : M.E) ^ (2 ^ m + 1) = 1 := by
    have h := congrArg (fun u : M.Eˣ => (u : M.E)) (M.mu_W_normOne ζ)
    simpa using h
  -- its square is the scalar attached to `ζ²`
  have hprod : ((1 : ↥hyp.actualKActor), ζ) * ((1 : ↥hyp.actualKActor), ζ)
      = ((1 : ↥hyp.actualKActor), ζ * ζ) := by
    rw [Prod.mk_mul_mk, one_mul]
  have hsq : ((M.mu (1, ζ) : M.Eˣ) : M.E) ^ 2
      = ((M.mu (1, ζ * ζ) : M.Eˣ) : M.E) := by
    rw [← hprod, map_mul]
    push_cast
    ring
  refine OddOrder.FiniteField.cocycle_diag_eq_norm_smul_of_normOne_invariant m hm M.card
    φ ?_ hnorm hne ?_ ?_
  · intro a ha b hb x y
    rw [hsemi a ha b hb x y, hθ b hb]
  · have h := hW ζ 1 1
    rwa [mul_one] at h
  · have h := hW (ζ * ζ) 1 1
    rw [mul_one] at h
    rw [hsq]
    exact h

include hyp in
/-- **`Q` in the unitary coordinates of `PSU(3, q)`** (Peterfalvi Part II, Ch. IV §3,
p. 130, the coordinate change between stages (3) and (4)).

Given the model of Ch. III §3 whose square map is `c` times the Hermitian norm
(`cocycle_diag_eq_norm`), write `c = e²` with `e ∈ F` and rescale the quotient
coordinate by `e`: the square map becomes the norm exactly, so the model and the
Hermitian twisted product are the same central extension of `F` by `E`
(`exists_mulEquiv_of_diag`).

The rescaling is multiplication by a scalar, hence `E`-linear; that is what makes the
computations of §2 and §3 — which use the `E`-multiplication of the quotient
coordinate and the action of `KW` by scalars — survive the change.  The centre is not
moved at all. -/
theorem exists_unitaryModel {m : ℕ} (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (hnorm : ∀ x : M.E,
      ((φ x x : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          * x ^ (2 ^ m + 1))
    (hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ) :
    ∃ (e : M.E) (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
        (OddOrder.FiniteField.hermitianCocycle m M.card hu)),
      e ≠ 0 ∧ e ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient) ∧
      ∀ w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
        Ψ (Φ.symm ⟨0, w⟩) = ⟨0, w⟩ := by
  classical
  -- the square root of the leading coefficient, inside `F`
  obtain ⟨e, he⟩ := (frobeniusEquiv
    ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) 2).surjective (φ 1 1)
  have heval : ((e : M.E)) ^ 2
      = ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) :=
    congrArg Subtype.val he
  have hene : ((e : M.E)) ≠ 0 := by
    intro h
    exact hone (by rw [← heval, h]; ring)
  have heq : ((e : M.E)) ^ 2 ^ m = (e : M.E) :=
    OddOrder.FiniteField.mem_frobFixedSubfield.mp e.2
  -- rescaling the quotient coordinate by `e` matches the two diagonals
  have hdiag : ∀ x : M.E,
      OddOrder.FiniteField.hermitianCocycle m M.card hu ((e : M.E) * x)
          ((e : M.E) * x) = φ x x := by
    intro x
    refine Subtype.ext ?_
    rw [OddOrder.FiniteField.hermitianCocycle_diag, hnorm x, ← heval, mul_pow, heq,
      pow_succ]
    ring
  obtain ⟨Ξ, hΞq, hΞc⟩ :=
    Suzuki2Groups.BilinearTwistedProduct.exists_mulEquiv_of_diag
      (AddEquiv.mk' (Equiv.mulLeft₀ (e : M.E) hene) (mul_add (e : M.E)))
      (AddEquiv.refl _) hdiag
  refine ⟨(e : M.E), Φ.trans Ξ, hene, e.2, fun ρ => ?_, fun w => ?_⟩
  · exact hΞq (Φ ρ)
  · have h := hΞc w
    simpa using h

include hyp in
/-- **The unitary coordinate system on `Q`, tied to the book's `α : Q / Q₀ → E`**
(Peterfalvi Part II, Ch. IV §3, p. 130).

This is the interface §3 (4) works in.  Its hypotheses are exactly the output of the
Proposition of Ch. III §3 (`exists_standardModel`: `hsemi`, `haniso`, `hquot`, `hW`)
together with `θ = 1` from §3 (3), and its conclusion is a presentation of `Q` as the
unitary group of pairs `(a, y)` with `Tr y = a ā` in which

* the first coordinate is `e` times the book's `α` — a *scalar* multiple, so the
  equations of §2 and §3, which are stated in `α` and use the `E`-multiplication and
  the scalar action of `KW`, translate by multiplying by `e`;
* the centre is not moved.

The scalar `e` is a square root in `F` of `φ(1,1)`; it is `1` exactly when the model's
square map is the norm on the nose. -/
theorem exists_unitaryModel_coord {m : ℕ} (M : hyp.QuotientFieldModel m) (hm : m ≠ 0)
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
    (hW : ∀ (v : ↥hyp.W) (x y : M.E),
      ((φ (((M.mu (1, v) : M.Eˣ) : M.E) * x) (((M.mu (1, v) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hmu : Function.Injective M.mu) {ζ : ↥hyp.W} (hζ : ζ ≠ 1)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ e : ↥hyp.Q, (Φ e).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)))
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1) :
    ∃ (e : M.E) (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
        (OddOrder.FiniteField.hermitianCocycle m M.card hu)),
      e ≠ 0 ∧ e ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).quotient =
        e * M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ))) ∧
      ∀ w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
        Ψ (Φ.symm ⟨0, w⟩) = ⟨0, w⟩ := by
  have hnorm := hyp.cocycle_diag_eq_norm M hm θm hsemi hθ hW hmu hζ
  have hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      ≠ 0 := by
    intro hc
    exact haniso 1 one_ne_zero (Subtype.ext hc)
  obtain ⟨e, Ψ, hene, heF, hΨq, hΨc⟩ :=
    hyp.exists_unitaryModel M hu hnorm hone Φ
  refine ⟨e, Ψ, hene, heF, fun ρ => ?_, hΨc⟩
  rw [hΨq ρ, hquot ρ]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
