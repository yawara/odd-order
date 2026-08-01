/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupIdentification
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionThree
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.UnitaryCoordinates

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
(`cocycle_diag_eq_norm`), `exists_hermitianCocycle_eq` identifies the *cocycle* with
`c` times a Hermitian one: `φ x y = c · H_u(x, y)` for a suitable `u` of trace one.
Rescaling the quotient coordinate by `e` and the central one by `ν` therefore matches
the cocycles on the nose as soon as `e² = ν c`, since `H_u(e x, e y) = e^{1+q} H_u(x, y)`
(`e` lies in `F`).  The comparison is then the plain `congrEquiv`

  `(x, w) ↦ (e x, ν w)`.

This is stronger than matching the diagonals: the isomorphism is *given* on both
coordinates, and — both coordinates being rescaled by scalars — it commutes with the
`E`-scalar action of `KW`.  That is what stages (4) and (5) compute with.

The central factor `ν` is left free precisely so that a caller can impose the book's
normalization `s = (0, 1)`: taking `ν` to be the inverse of the central coordinate of
the distinguished involution puts it at `1`.  Every `ν ≠ 0` in `F` is admissible
because squaring is onto `F` — which is the Hermitian norm there. -/
theorem exists_unitaryModel {m : ℕ} (M : hyp.QuotientFieldModel m) (hm : m ≠ 0)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hbil : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hnorm : ∀ x : M.E,
      ((φ x x : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          * x ^ (2 ^ m + 1))
    (hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)} (hν : ν ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ) :
    ∃ (u : M.E) (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1) (e : M.E)
      (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
        (OddOrder.FiniteField.hermitianCocycle m M.card hu)),
      e ≠ 0 ∧ e ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient) ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central) := by
  classical
  -- the cocycle *is* `φ(1,1)` times a Hermitian one
  obtain ⟨u, hu, hφ⟩ := OddOrder.FiniteField.exists_hermitianCocycle_eq m hm M.card φ
    hbil hone hnorm
  -- the square root of `ν · φ(1,1)`, inside `F`
  obtain ⟨e, he⟩ := (frobeniusEquiv
    ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) 2).surjective (ν * φ 1 1)
  have heval : ((e : M.E)) ^ 2
      = (ν : M.E) *
        ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) :=
    congrArg Subtype.val he
  have hνne : (ν : M.E) ≠ 0 := fun h => hν (Subtype.ext h)
  have hene : ((e : M.E)) ≠ 0 := by
    intro h
    exact (mul_ne_zero hνne hone) (by rw [← heval, h]; ring)
  have heq : ((e : M.E)) ^ 2 ^ m = (e : M.E) :=
    OddOrder.FiniteField.mem_frobFixedSubfield.mp e.2
  have hesq : ((e : M.E)) ^ 2 ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
    pow_mem e.2 2
  -- rescaling by `(e, ν)` matches the two cocycles exactly
  have hcompat : ∀ x y : M.E,
      OddOrder.FiniteField.hermitianCocycle m M.card hu ((e : M.E) * x)
          ((e : M.E) * y)
        = AddEquiv.mk' (Equiv.mulLeft₀ ν hν) (mul_add ν) (φ x y) := by
    intro x y
    refine Subtype.ext ?_
    have hsplit : ((e : M.E) * x) * ((e : M.E) * y) ^ 2 ^ m
        = ((e : M.E)) ^ 2 * (x * y ^ 2 ^ m) := by
      rw [mul_pow, heq]
      ring
    rw [OddOrder.FiniteField.hermitianCocycle_apply, hsplit,
      OddOrder.FiniteField.frobTrace_mul_of_mem m hesq, heval]
    change _ = (ν : M.E) *
      ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
    rw [hφ x y]
    ring
  refine ⟨u, hu, (e : M.E),
    Φ.trans (Suzuki2Groups.BilinearTwistedProduct.congrEquiv
      (AddEquiv.mk' (Equiv.mulLeft₀ (e : M.E) hene) (mul_add (e : M.E)))
      (AddEquiv.mk' (Equiv.mulLeft₀ ν hν) (mul_add ν)) hcompat),
    hene, e.2, fun _ => rfl, fun _ => rfl⟩

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
* the centre is rescaled by the chosen `ν` (`(Ψ ρ).central = ν · (Φ ρ).central`), which
  is how the book's normalization `s = (0, 1)` is imposed.

The scalar `e` is a square root in `F` of `ν · φ(1,1)`. -/
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
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)} (hν : ν ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ e : ↥hyp.Q, (Φ e).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e))) :
    ∃ (u : M.E) (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1) (e : M.E)
      (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
        (OddOrder.FiniteField.hermitianCocycle m M.card hu)),
      e ≠ 0 ∧ e ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).quotient =
        e * M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ))) ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central) ∧
      ∀ w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
        Ψ (Φ.symm ⟨0, w⟩) = ⟨0, ν * w⟩ := by
  have hnorm := hyp.cocycle_diag_eq_norm M hm θm hsemi hθ hW hmu hζ
  have hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      ≠ 0 := by
    intro hc
    exact haniso 1 one_ne_zero (Subtype.ext hc)
  have hbil : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
    intro a ha b hb x y
    rw [hsemi a ha b hb x y, hθ b hb]
  obtain ⟨u, hu, e, Ψ, hene, heF, hΨq, hΨc⟩ :=
    hyp.exists_unitaryModel M hm hbil hnorm hone hν Φ
  refine ⟨u, hu, e, Ψ, hene, heF, fun ρ => ?_, hΨc, fun w => ?_⟩
  · rw [hΨq ρ, hquot ρ]
  · refine Suzuki2Groups.BilinearTwistedProduct.ext ?_ ?_
    · rw [hΨq, Φ.apply_symm_apply]
      exact mul_zero _
    · rw [hΨc, Φ.apply_symm_apply]

include hyp in
/-- **The unitary coordinate of a central element is its `ι`-coordinate, rescaled**
(Peterfalvi Part II, Ch. IV §3, p. 131: the elements `s^a = (0, a)`).

`Ψ` multiplies the quotient coordinate by `e` and the central one by `ν`, so on the
centre — where the quotient coordinate is `0` and the unitary correction `u a ā`
vanishes — it reads the centre coordinate `ι` scaled by `ν`.

Choosing `ν = ι(s)⁻¹` is the book's normalization `s = (0, 1)`; then `s^a` has unitary
coordinate `ι(s^a)/ι(s) = μ(a,1)²`, which is the book's `a` on p. 131 (its parameter
being the square of stage (1)'s). -/
theorem unitaryCoord_center {m : ℕ} (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hΨc : ∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central)
    (z : ↥(Subgroup.center hyp.Q)) :
    Suzuki2Groups.unitaryCoord m u (Ψ (z : ↥hyp.Q))
      = (ν : M.E) *
        ((ι (Additive.ofMul z) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
  have hq : (Ψ (z : ↥hyp.Q)).quotient = 0 := by
    rw [hΨq, hker z]
    exact mul_zero e
  rw [Suzuki2Groups.unitaryCoord_of_quotient_eq_zero m u hq, hΨc, hker z]
  rfl

include hyp in
/-- **`μ(1, ζ)` lies outside `F` for `ζ ≠ 1`** (Peterfalvi Part II, Ch. IV §3, p. 131:
the book's `ζ⁻¹ ∉ F`, which is what makes `a + ζ⁻¹` invertible for `a ∈ F`).

`μ(W)` consists of norm-one elements (`mu_W_normOne`), and a norm-one element of `F`
squares to `1`, hence is `1` in characteristic two; `μ` injective transfers `ζ ≠ 1` to
`μ(1, ζ) ≠ 1`. -/
theorem mu_W_notMem_frobFixed {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hmu : Function.Injective M.mu) {ζ : ↥hyp.W} (hζ : ζ ≠ 1) :
    ((M.mu (1, ζ) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
  have hnorm : ((M.mu (1, ζ) : M.Eˣ) : M.E) ^ (2 ^ m + 1) = 1 := by
    have h := congrArg (fun u : M.Eˣ => (u : M.E)) (M.mu_W_normOne ζ)
    simpa using h
  refine OddOrder.FiniteField.notMem_frobFixedSubfield_of_normOne m hnorm ?_
  intro hval
  have hmu1 : M.mu ((1 : ↥hyp.actualKActor), ζ) = 1 := Units.ext hval
  exact hζ (congrArg Prod.snd (hmu (hmu1.trans (map_one M.mu).symm)))

include hyp in
/-- **`μ((a⁻¹)²) = μ(a²)⁻¹`** — the scalar of the opposite shift along `Q₀`.

Stage (5)'s second case moves along the fibre by `s^{a⁻¹}` while §2 (2) conjugates by
`a²`, so the two parameters are inverse to each other; this is the identity that lets
`stepFive_secondCase_compose` be read at the element `ρ s^{a⁻¹}`. -/
theorem mu_kActor_sq_inv {m : ℕ} (M : hyp.QuotientFieldModel m) {a : G}
    (haK : a ∈ hyp.K) :
    ((M.mu (hyp.kActor (pow_mem (hyp.K.inv_mem haK) 2), 1) : M.Eˣ) : M.E)
      = ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹ := by
  have hk : hyp.kActor (pow_mem (hyp.K.inv_mem haK) 2)
      = (hyp.kActor (pow_mem haK 2))⁻¹ :=
    hyp.kActor_eq_inv (pow_mem haK 2) (pow_mem (hyp.K.inv_mem haK) 2) (by group)
  rw [hk, show ((hyp.kActor (pow_mem haK 2))⁻¹, (1 : ↥hyp.W))
      = ((hyp.kActor (pow_mem haK 2), (1 : ↥hyp.W)))⁻¹ from
    Prod.ext rfl (inv_one (G := ↥hyp.W)).symm, map_inv, Units.val_inv_eq_inv_val]

include hyp in
/-- **The `t`-twist of `K W` is `d ↦ d^{-q}` on scalars**: `μ(k⁻¹, v) = (μ(k, v)^q)⁻¹`
(Peterfalvi Part II, Ch. IV §3 (5), p. 131, the exponent `d^{-q}` in the display).

`t` inverts `K` (`mul_t_eq_of_mem_KSet`) and centralizes `W` (`conj_t_pow_eq`), so on
`K × W` the twist `d ↦ d^t` is `(k, v) ↦ (k⁻¹, v)`.  On scalars that is `A Z ↦ A⁻¹ Z`,
and — `μ(K)` lying in `F` and `μ(W)` having norm one — `(A Z)^q = A Z⁻¹`, whose inverse
is `A⁻¹ Z`.

This is what makes (H3) usable in stage (5): the `K W`-orbit of a solved point is again
solved. -/
theorem mu_t_twist {m : ℕ} (M : hyp.QuotientFieldModel m)
    (k : ↥hyp.actualKActor) (v : ↥hyp.W) :
    ((M.mu (k⁻¹, v) : M.Eˣ) : M.E)
      = (((M.mu (k, v) : M.Eˣ) : M.E) ^ 2 ^ m)⁻¹ := by
  have hKZ : ∀ k' : ↥hyp.actualKActor,
      ((M.mu (k', v) : M.Eˣ) : M.E)
        = ((M.mu (k', (1 : ↥hyp.W)) : M.Eˣ) : M.E)
          * ((M.mu ((1 : ↥hyp.actualKActor), v) : M.Eˣ) : M.E) := by
    intro k'
    rw [show ((k', v) : ↥hyp.actualKActor × ↥hyp.W)
        = (k', (1 : ↥hyp.W)) * ((1 : ↥hyp.actualKActor), v) from
      Prod.ext (mul_one _).symm (one_mul _).symm, map_mul, Units.val_mul]
  have hZ0 : ((M.mu ((1 : ↥hyp.actualKActor), v) : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
  have hZ : ((M.mu ((1 : ↥hyp.actualKActor), v) : M.Eˣ) : M.E) ^ 2 ^ m
      = ((M.mu ((1 : ↥hyp.actualKActor), v) : M.Eˣ) : M.E)⁻¹ := by
    have hn : ((M.mu ((1 : ↥hyp.actualKActor), v) : M.Eˣ) : M.E) ^ (2 ^ m + 1) = 1 := by
      have h := congrArg (fun x : M.Eˣ => (x : M.E)) (M.mu_W_normOne v)
      simpa using h
    field_simp
    rw [← pow_succ]
    exact hn
  have hinvK : ((M.mu (k⁻¹, (1 : ↥hyp.W)) : M.Eˣ) : M.E)
      = ((M.mu (k, (1 : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    rw [show ((k⁻¹, (1 : ↥hyp.W)) : ↥hyp.actualKActor × ↥hyp.W)
        = ((k, (1 : ↥hyp.W)) : ↥hyp.actualKActor × ↥hyp.W)⁻¹ from
      Prod.ext rfl (inv_one (G := ↥hyp.W)).symm, map_inv, Units.val_inv_eq_inv_val]
  rw [hKZ k⁻¹, hKZ k, mul_pow, M.mu_K_frobFixed k, hZ, hinvK, mul_inv, inv_inv]

include hyp in
/-- **`μ(1, ζ) ≠ μ(1, ζ)⁻¹`** for `ζ ≠ 1` — the book's `ζ + 1 ≠ ζ⁻¹ + 1`, which is what
closes stage (4) (Peterfalvi Part II, p. 131, last line).

Stage (4) run at `ω` leaves out one point of the fibre, and run at `ω⁻¹` (with `ζ⁻¹`)
leaves out another; the two coincide only if `μ(1, ζ)² = 1`, hence — squaring being
injective in characteristic two — only if `ζ = 1`. -/
theorem mu_W_ne_inv {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hmu : Function.Injective M.mu) {ζ : ↥hyp.W} (hζ : ζ ≠ 1) :
    ((M.mu (1, ζ) : M.Eˣ) : M.E) ≠ ((M.mu (1, ζ) : M.Eˣ) : M.E)⁻¹ := by
  intro hc
  have hZ0 : ((M.mu (1, ζ) : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
  have hsq : ((M.mu (1, ζ) : M.Eˣ) : M.E) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hc]
    exact mul_inv_cancel₀ hZ0
  have hval : ((M.mu (1, ζ) : M.Eˣ) : M.E) = 1 :=
    OddOrder.FiniteField.eq_one_of_sq_eq_one hsq
  have hmu1 : M.mu ((1 : ↥hyp.actualKActor), ζ) = 1 := Units.ext hval
  exact hζ (congrArg Prod.snd (hmu (hmu1.trans (map_one M.mu).symm)))

include hyp in
/-- **`μ(k, 1) + μ(1, ζ) ≠ 0`** for `ζ ≠ 1` — the denominator `a + ζ⁻¹` of stages (2)
and (4) never vanishes, `μ(K)` lying in `F` and `μ(1, ζ)` not.

This is both what lets stage (2) be solved for `f(ω s^a)‾` and the hypothesis `w ∉ S`
of `eq_and_inv_of_star`. -/
theorem mu_K_add_mu_W_ne_zero {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hmu : Function.Injective M.mu) {ζ : ↥hyp.W} (hζ : ζ ≠ 1)
    (k : ↥hyp.actualKActor) :
    ((M.mu (k, 1) : M.Eˣ) : M.E) + ((M.mu (1, ζ) : M.Eˣ) : M.E) ≠ 0 := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  intro hc
  refine hyp.mu_W_notMem_frobFixed M hmu hζ ?_
  have hval : ((M.mu (1, ζ) : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) := by
    linear_combination hc - ((M.mu (k, 1) : M.Eˣ) : M.E) * h2
  rw [hval]
  exact OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k)

include hyp in
/-- **The unitary coordinate of an element of `Q₀`** — `unitaryCoord_center` phrased in
the `centerCoord` of Ch. IV §2, which is the form §2 and §3 state their equations in. -/
theorem unitaryCoord_toCenter {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hΨc : ∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central)
    {x : G} (hx : x ∈ hyp.Q0) :
    Suzuki2Groups.unitaryCoord m u
        (Ψ ((hyp.toCenter sfive hx : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q))
      = (ν : M.E) * hyp.centerCoord sfive M ι hx :=
  hyp.unitaryCoord_center M Φ ι hker hu Ψ hΨq hΨc (hyp.toCenter sfive hx)

include hyp in
/-- **The `K`-action on the centre is squaring the scalar**: `c^a = μ(a²) · c`
(Peterfalvi Part II, p. 119, with `θ = 1`).

`centerCoord_conj` carries the opaque power `μ(a)^d`; `mu_K_zpow_eq_sq` evaluates it as
`μ(a)²`, which is `μ(a²)` (`mu_kActor_sq`).

This is what makes `s^a` the book's `(0, a)` on p. 131 once the centre is normalized so
that `s = (0, 1)`: the parameter there is the *square* of stage (1)'s. -/
theorem centerCoord_conj_eq_mu_sq {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    {a : G} (ha : a ∈ hyp.K) {x : G} (hx : x ∈ hyp.Q0) :
    hyp.centerCoord sfive M ι (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D ha) hx)
      = ((M.mu (hyp.kActor (pow_mem ha 2), 1) : M.Eˣ) : M.E) *
        hyp.centerCoord sfive M ι hx := by
  rw [hyp.centerCoord_conj sfive M ι d hequiv ha hx, hdsq, ← hyp.mu_kActor_sq M ha]

include hyp in
/-- **The norm of `μ(k, v)` is `μ(k, 1)²`** (Peterfalvi Part II, Ch. III §3, p. 120).

`μ` is multiplicative and `(k, v) = (k, 1)(1, v)`, so the norm splits; the `W`-half is
`1` (`mu_W_normOne`) and the `K`-half is a square, `μ(K)` lying in `F`
(`mu_K_frobFixed`).

So the scalar by which `K W` acts on the second unitary coordinate involves only the
`K`-component — the book's `d^{1+q}` for `d ∈ K W`. -/
theorem mu_norm_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (k : ↥hyp.actualKActor) (v : ↥hyp.W) :
    ((M.mu (k, v) : M.Eˣ) : M.E) ^ (2 ^ m + 1)
      = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2 := by
  have hsplit : (k, v) = (k, (1 : ↥hyp.W)) * ((1 : ↥hyp.actualKActor), v) :=
    Prod.ext (mul_one _).symm (one_mul _).symm
  have hW : ((M.mu ((1 : ↥hyp.actualKActor), v) : M.Eˣ) : M.E) ^ (2 ^ m + 1) = 1 := by
    have h := congrArg (fun x : M.Eˣ => (x : M.E)) (M.mu_W_normOne v)
    simpa using h
  have hK : ((M.mu (k, (1 : ↥hyp.W)) : M.Eˣ) : M.E) ^ (2 ^ m + 1)
      = ((M.mu (k, (1 : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 := by
    rw [pow_succ, M.mu_K_frobFixed k, ← pow_two]
  have hmu : ((M.mu (k, v) : M.Eˣ) : M.E)
      = ((M.mu (k, (1 : ↥hyp.W)) : M.Eˣ) : M.E)
        * ((M.mu ((1 : ↥hyp.actualKActor), v) : M.Eˣ) : M.E) := by
    rw [← Units.val_mul, ← map_mul, ← hsplit]
  rw [hmu, mul_pow, hW, mul_one, hK]

include hyp in
/-- **The centre exponent is squaring on `μ(K)`**: `μ(k,1)^d = μ(k,1)²` (Peterfalvi
Part II, Ch. IV §3 (3), p. 130 — this is the concrete content of `θ = 1`).

`exists_center_coordinate_equiv` produces the `K`-action on the centre as an opaque
integer power `μ(k,1)^d` — the book's `a^{1+θ}`.  Once the cocycle's diagonal is known
to be a multiple of the norm, `centralScale_eq_norm_of_quotientScale` evaluates that
power as the norm `μ(k,1)^{1+q}`, and `μ(K) ⊆ F` makes the norm a square.

So every statement of §2 carrying `μ(k,1)^d` — `centerCoord_conj`, `stepTen_coord` —
can be read with the explicit scalar `μ(k,1)²`. -/
theorem mu_K_zpow_eq_sq {m : ℕ} (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hnorm : ∀ x : M.E,
      ((φ x x : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          * x ^ (2 ^ m + 1))
    (hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) ≠ 0)
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient)
    {d : ℤ}
    (hΘc : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (((Θ kv p).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) *
            ((p.central :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (k : ↥hyp.actualKActor) :
    ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2 := by
  have h := Suzuki2Groups.centralScale_eq_norm_of_quotientScale m hone hnorm
    (Θ (k, 1)) (hΘq (k, 1)) (hΘc (k, 1))
  rw [h, pow_succ, M.mu_K_frobFixed k, ← pow_two]

include hyp in
/-- **Conjugation by `K W` in the unitary coordinates** (Peterfalvi Part II, Ch. IV §3,
p. 131): writing an element of `Q` as `(a, y)` with `Tr y = a ā`,

  `(a, y)^{kv} = (μ(kv) a, μ(kv)^{1+q} y)`.

Both halves come out of the model action of Ch. III §3.  The quotient coordinate is
scaled by `μ(kv)` there already; the central coordinate is scaled by the opaque power
`μ(k,1)^d`, and `centralScale_eq_norm_of_quotientScale` identifies that power with the
norm `μ(kv)^{1+q}` — the cocycle's diagonal is a nonzero multiple of the norm, and an
automorphism scaling both coordinates has to respect it.  Since the correction
`y = z + u a ā` is itself norm-shaped, the same scalar then governs the unitary
coordinate (`unitaryCoord_of_scaled`). -/
theorem exists_unitaryModel_conj {m : ℕ} (M : hyp.QuotientFieldModel m) (hm : m ≠ 0)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hbil : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hnorm : ∀ x : M.E,
      ((φ x x : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          * x ^ (2 ^ m + 1))
    (hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)} (hν : ν ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient)
    (κ : ↥hyp.actualKActor × ↥hyp.W → M.E)
    (hΘc : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (((Θ kv p).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = κ kv * ((p.central :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hconj : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Φ (hyp.conjQHom kv ρ) = Θ kv (Φ ρ)) :
    ∃ (u : M.E) (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1) (e : M.E)
      (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
        (OddOrder.FiniteField.hermitianCocycle m M.card hu)),
      e ≠ 0 ∧ e ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient) ∧
      (∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central) ∧
      (∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
        (Ψ (hyp.conjQHom kv ρ)).quotient
          = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient) ∧
      ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
        Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
          = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
            Suzuki2Groups.unitaryCoord m u (Ψ ρ) := by
  classical
  obtain ⟨u, hu, e, Ψ, hene, heF, hΨq, hΨc⟩ :=
    hyp.exists_unitaryModel M hm hbil hnorm hone hν Φ
  -- the central scalar of `Θ kv` is the norm of its quotient scalar
  have hκ : ∀ kv : ↥hyp.actualKActor × ↥hyp.W,
      κ kv = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) := fun kv =>
    Suzuki2Groups.centralScale_eq_norm_of_quotientScale m hone hnorm (Θ kv)
      (hΘq kv) (hΘc kv)
  refine ⟨u, hu, e, Ψ, hene, heF, hΨq, hΨc, fun kv ρ => ?_, fun kv ρ => ?_⟩
  · rw [hΨq, hconj kv ρ, hΘq, hΨq, mul_left_comm]
  · rw [show ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1)
        = ((M.mu kv : M.Eˣ) : M.E) * ((M.mu kv : M.Eˣ) : M.E) ^ 2 ^ m by
      rw [pow_succ]; ring]
    refine Suzuki2Groups.unitaryCoord_of_scaled m ((M.mu kv : M.Eˣ) : M.E) ?_ ?_
    · rw [hΨq, hconj kv ρ, hΘq, hΨq, mul_left_comm]
    · have hc : ((Ψ (hyp.conjQHom kv ρ)).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
          = ν * (Θ kv (Φ ρ)).central := by rw [hΨc, hconj kv ρ]
      rw [show (((Ψ (hyp.conjQHom kv ρ)).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((ν * (Θ kv (Φ ρ)).central :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) from
        congrArg Subtype.val hc]
      rw [Submonoid.coe_mul, hΘc, hκ kv, hΨc, Submonoid.coe_mul, pow_succ]
      ring

include hyp in
/-- **Conjugation by `KW` is the scalar action, pointwise** (Peterfalvi Part II,
Ch. III §3, p. 121, step (4) — the Zassenhaus step, read on elements).

The Proposition of Ch. III §3 matches the conjugation action with the scalar action
only as *subgroups* of `MulAut`, after conjugating by an element `u` of `U`.  Two
observations turn that into a pointwise statement:

* `u` can be absorbed into the coordinate map: `Φ' := Φ ∘ u` satisfies
  `MulAut.congr Φ' α = u (MulAut.congr Φ α) u⁻¹`, so the equality of images becomes
  `MulAut.congr Φ' ∘ conjQHom` landing in `Θ.range`.  Since `u` induces the identity
  on both ends of the extension, `Φ'` has the same quotient coordinate as `Φ` and
  still sends the centre to the centre coordinate unchanged.
* the index is then pinned by the *quotient* action: `Θ kv'` scales it by `μ(kv')`
  and conjugation by `μ(kv)`, so `μ` injective forces `kv' = kv`.

This is what §3 (4) needs: the conjugations appearing in stages (1) and (2) act on
both coordinates by the explicit scalars of `Θ`. -/
theorem exists_modelEquiv_conj {m : ℕ} (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (u : MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hquot : ∀ e : ↥hyp.Q, (Φ e).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient)
    (hu : u ∈ (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts)
    (hconj : (((MulAut.congr Φ).toMonoidHom.comp (hyp.conjQHom)).range).map
      (MulAut.conj u).toMonoidHom = Θ.range)
    (hmu : Function.Injective M.mu) :
    ∃ Φ' : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ,
      (∀ e : ↥hyp.Q, (Φ' e).quotient =
        M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e))) ∧
      (∀ w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
        Φ' (Φ.symm ⟨0, w⟩) = ⟨0, w⟩) ∧
      ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
        Φ' (hyp.conjQHom kv ρ) = Θ kv (Φ' ρ) := by
  classical
  obtain ⟨huinl, huright⟩ := hu
  -- `u` does not move either coordinate of the centre or the quotient
  have huq : ∀ p : Suzuki2Groups.BilinearTwistedProduct φ,
      (u p).quotient = p.quotient := by
    intro p
    exact congrArg Multiplicative.toAdd (huright p)
  set Φ' : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ := Φ.trans u with hΦ'
  have hquot' : ∀ e : ↥hyp.Q, (Φ' e).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)) := by
    intro e
    rw [hΦ']
    change (u (Φ e)).quotient = _
    rw [huq, hquot]
  -- absorbing `u` turns the conjugated image into the plain one
  have hcongr : ∀ kv : ↥hyp.actualKActor × ↥hyp.W,
      MulAut.congr Φ' (hyp.conjQHom kv)
        = (MulAut.conj u) (MulAut.congr Φ (hyp.conjQHom kv)) :=
    fun kv => rfl
  refine ⟨Φ', hquot', fun w => ?_, fun kv ρ => ?_⟩
  · rw [hΦ']
    change u (Φ (Φ.symm ⟨0, w⟩)) = _
    rw [Φ.apply_symm_apply]
    exact huinl (Multiplicative.ofAdd w)
  · -- the conjugation lands in the image of `Θ`
    have hmem : MulAut.congr Φ' (hyp.conjQHom kv) ∈ Θ.range := by
      rw [← hconj, hcongr kv]
      exact ⟨MulAut.congr Φ (hyp.conjQHom kv), ⟨kv, rfl⟩, rfl⟩
    obtain ⟨kv', hkv'⟩ := hmem
    -- the quotient action pins the index
    have hact : ∀ σ : ↥hyp.Q,
        (Φ' (hyp.conjQHom kv σ)).quotient
          = ((M.mu kv : M.Eˣ) : M.E) * (Φ' σ).quotient := by
      intro σ
      rw [hquot' (hyp.conjQHom kv σ), hquot' σ, ← M.coord_act kv]
      rfl
    have hone : ((M.mu kv' : M.Eˣ) : M.E) = ((M.mu kv : M.Eˣ) : M.E) := by
      have hq : (Φ' (Φ'.symm (⟨1, 0⟩ :
          Suzuki2Groups.BilinearTwistedProduct φ))).quotient = 1 := by
        rw [Φ'.apply_symm_apply]
      have h1 := congrArg (fun α : MulAut (Suzuki2Groups.BilinearTwistedProduct φ) =>
        (α (Φ' (Φ'.symm (⟨1, 0⟩ : Suzuki2Groups.BilinearTwistedProduct φ)))).quotient)
        hkv'
      rw [hΘq kv' _, hq, mul_one] at h1
      have h2 : (MulAut.congr Φ' (hyp.conjQHom kv)
          (Φ' (Φ'.symm (⟨1, 0⟩ : Suzuki2Groups.BilinearTwistedProduct φ)))).quotient
          = ((M.mu kv : M.Eˣ) : M.E) := by
        have : MulAut.congr Φ' (hyp.conjQHom kv) (Φ' (Φ'.symm
            (⟨1, 0⟩ : Suzuki2Groups.BilinearTwistedProduct φ)))
            = Φ' (hyp.conjQHom kv (Φ'.symm
              (⟨1, 0⟩ : Suzuki2Groups.BilinearTwistedProduct φ))) := by
          change Φ' (hyp.conjQHom kv (Φ'.symm (Φ' (Φ'.symm _)))) = _
          rw [Φ'.symm_apply_apply]
        rw [this, hact, hq, mul_one]
      exact h1.trans h2
    have hkveq : kv' = kv := hmu (Units.ext hone)
    rw [hkveq] at hkv'
    have hval := congrArg (fun α : MulAut (Suzuki2Groups.BilinearTwistedProduct φ) =>
      α (Φ' ρ)) hkv'
    rw [hval, show (MulAut.congr Φ') (hyp.conjQHom kv) (Φ' ρ)
      = Φ' (hyp.conjQHom kv (Φ'.symm (Φ' ρ))) from rfl, Φ'.symm_apply_apply]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
