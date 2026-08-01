/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3RootGroupModel

/-!
# Peterfalvi Part II, Ch. IV §3 (4): `f` is inversion in the unitary coordinates

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4)–(5), pp. 130–131.

Stage (4) says that on the fibre of `ω̄` — the elements `(ω̄, y)` of `Q` with
`y + y^q = ω̄^{1+q}` — the map `f` is

  `f(ω̄, y) = (ω̄/y, 1/y)`,

and stage (5) removes the restriction to that one fibre.  The proof of (4) reads
stage (1) in the unitary coordinates: writing `ω = (ω̄, x)` and
`f(ω̄, x + a) = (ω̄/(a + ζ⁻¹), γ(a))` (the first coordinate being stage (2)),
comparison of the *second* entries of

  `f(ω̄, x+a)^{ζ⁻¹ a} (0, a) = f(ω̄, x+a)^{ζ⁻²} (ω̄, x)^{ζ⁻¹}`

gives the book's

  `(∗∗)   (a² + 1) γ(a) = x + a + (1 + ζ⁻²)/(a + ζ⁻¹)`   for `a ∈ F − {0}`,

whose `a = 1` instance pins `x = ζ⁻¹` and whose remaining instances then collapse to
`γ(a) = 1/(a + ζ⁻¹)`.

This file carries the arithmetic of that argument, which is where all of its content
sits: once the two coordinate formulas are in hand, `(∗∗)` and its consequences are
statements about the field `E` alone.

## Main results

* `star_of_secondEntry` — the second-entry comparison *is* `(∗∗)`.
* `eq_and_inv_of_star` — `(∗∗)` forces `x = ζ⁻¹` and `γ(a) = 1/(a + ζ⁻¹)`.
* `gamma_eq_inv_of_secondEntry` — the two combined, in the form stage (4) consumes:
  the second unitary coordinate of `f(ω̄, x + a)` is `1/(x + a)`, for `a ∈ F − {0, 1}`.
* `secondEntry_of_chain`, `star_of_chain` — the bridge from a two-factor identity in
  the twisted product to `(∗∗)`, which is how stage (1) enters.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section StepFourArithmetic

variable {E : Type*} [Field E]

/-- **The second-entry comparison of stage (4) is the book's `(∗∗)`** (Peterfalvi
Part II, p. 131).

The left-hand entry is `a² γ(a) + a`: conjugating by `ζ⁻¹ a` scales the unitary
coordinate by the norm `(ζ⁻¹ a)^{1+q} = a²` (`ζ` has norm one, `a` lies in `F`), and
right multiplication by the central `(0, a)` adds `a`.  The right-hand entry is
`γ(a) + x + A C̄`, where `A = ζ⁻² ω̄/(a + ζ⁻¹)` and `C = ζ⁻¹ ω̄` are the two quotient
coordinates — the cocycle term of the unitary multiplication rule.

That cocycle term is where `ζ` and `ω̄` disappear: `A C̄ = ζ⁻² ζ ω̄^{1+q}/(a + ζ⁻¹)`,
using `ζ^{-q} = ζ`, and `ω̄^{1+q} = ζ + ζ⁻¹` by stage (3), leaving
`(1 + ζ⁻²)/(a + ζ⁻¹)`. -/
theorem star_of_secondEntry (h2 : (2 : E) = 0) {m : ℕ} {ζ ω x a γa : E}
    (hζ : ζ ≠ 0) (hζnorm : ζ * ζ ^ 2 ^ m = 1) (hω : ω * ω ^ 2 ^ m = ζ + ζ⁻¹)
    (hchain : a ^ 2 * γa + a
      = γa + x + (ζ⁻¹ ^ 2 * ω / (a + ζ⁻¹)) * (ζ⁻¹ * ω) ^ 2 ^ m) :
    (a ^ 2 + 1) * γa = x + a + (1 + ζ⁻¹ ^ 2) / (a + ζ⁻¹) := by
  have hζinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ
  have hζq : ζ ^ 2 ^ m = ζ⁻¹ := by
    field_simp
    linear_combination hζnorm
  have hζinvq : (ζ⁻¹) ^ 2 ^ m = ζ := by rw [inv_pow, hζq, inv_inv]
  -- the cocycle term collapses to `(1 + ζ⁻²)/(a + ζ⁻¹)`
  have hnum : ζ⁻¹ ^ 2 * ω * (ζ * ω ^ 2 ^ m) = 1 + ζ⁻¹ ^ 2 :=
    calc ζ⁻¹ ^ 2 * ω * (ζ * ω ^ 2 ^ m)
        = ζ⁻¹ ^ 2 * ζ * (ω * ω ^ 2 ^ m) := by ring
      _ = ζ⁻¹ ^ 2 * ζ * (ζ + ζ⁻¹) := by rw [hω]
      _ = (ζ * ζ⁻¹) ^ 2 + (ζ * ζ⁻¹) * ζ⁻¹ ^ 2 := by ring
      _ = 1 + ζ⁻¹ ^ 2 := by rw [hζinv]; ring
  have hcoc : (ζ⁻¹ ^ 2 * ω / (a + ζ⁻¹)) * (ζ⁻¹ * ω) ^ 2 ^ m
      = (1 + ζ⁻¹ ^ 2) / (a + ζ⁻¹) := by
    rw [mul_pow, hζinvq, div_mul_eq_mul_div, hnum]
  rw [hcoc] at hchain
  linear_combination hchain + (γa - a) * h2

/-- **`(∗∗)` forces `x = w` and `γ(a) = 1/(a + w)`** (Peterfalvi Part II, p. 131,
with `w = ζ⁻¹`).

Only two features of `w` are used: it lies outside the subfield `S = F` (so that `a + w`
never vanishes for `a ∈ S`), and `1 ∈ S`.  Both steps are the same manipulation,
`(a + w)² = a² + w²` in characteristic two:

* at `a = 1` the left side vanishes and `(1 + w²)/(1 + w) = 1 + w`, giving `x = w`;
* at `a ∉ {0, 1}` the right side becomes `[(a + w)² + 1 + w²]/(a + w) = (a² + 1)/(a + w)`,
  and `a² + 1 = (a + 1)²` is invertible.

The excluded value `a = 1` is exactly the one the book recovers at the end of (4) by
replacing `ω` with `ω⁻¹` and `ζ` with `ζ⁻¹`. -/
theorem eq_and_inv_of_star (h2 : (2 : E) = 0) (S : Subfield E) {w x : E} {γ : E → E}
    (hw : w ∉ S)
    (hstar : ∀ a ∈ S, a ≠ 0 → (a ^ 2 + 1) * γ a = x + a + (1 + w ^ 2) / (a + w)) :
    x = w ∧ ∀ a ∈ S, a ≠ 0 → a ≠ 1 → γ a = (a + w)⁻¹ := by
  have hne : ∀ a ∈ S, a + w ≠ 0 := by
    intro a ha hc
    refine hw ?_
    have hwa : w = a := by linear_combination hc - a * h2
    rw [hwa]
    exact ha
  have hone : (1 : E) ∈ S := S.one_mem
  -- the instance `a = 1` pins `x`
  have hx : x = w := by
    have h := hstar 1 hone one_ne_zero
    have h1w : (1 : E) + w ≠ 0 := hne 1 hone
    have hsq : (1 : E) + w ^ 2 = (1 + w) * (1 + w) := by linear_combination (-w) * h2
    have hzero : ((1 : E) ^ 2 + 1) * γ 1 = 0 := by
      rw [show ((1 : E) ^ 2 + 1) = 0 by linear_combination h2, zero_mul]
    rw [hsq, mul_div_assoc, div_self h1w, mul_one, hzero] at h
    linear_combination -h + (-w - 1) * h2
  refine ⟨hx, fun a ha ha0 ha1 => ?_⟩
  have haw : a + w ≠ 0 := hne a ha
  have hsq : a ^ 2 + 1 ≠ 0 := by
    intro hc
    refine ha1 ?_
    have hfac : (a + 1) * (a + 1) = 0 := by linear_combination hc + a * h2
    rcases mul_eq_zero.mp hfac with h | h <;>
      exact (by linear_combination h - h2 : a = 1)
  -- the right-hand side is `(a² + 1)/(a + w)`
  have hnum : (a ^ 2 + 1 : E) = (w + a) * (a + w) + (1 + w ^ 2) := by
    linear_combination (-(a * w) - w ^ 2) * h2
  have hrhs : (a ^ 2 + 1) / (a + w) = w + a + (1 + w ^ 2) / (a + w) := by
    rw [hnum, add_div, mul_div_assoc, div_self haw, mul_one]
  have h := hstar a ha ha0
  rw [hx, ← hrhs, div_eq_mul_inv] at h
  exact mul_left_cancel₀ hsq h

/-- **Stage (4), as an identity between the unitary coordinates** (Peterfalvi Part II,
p. 131).

Combining the two previous lemmas: the second entry of `f(ω̄, x + a)` is `1/(x + a)`,
since `x = ζ⁻¹` turns `a + ζ⁻¹` into `x + a`.  Together with stage (2)'s first entry
`ω̄/(a + ζ⁻¹) = ω̄/(x + a)` this is the book's `f(ω̄, y) = (ω̄/y, 1/y)`, for
`y = x + a` with `a ∈ F − {0, 1}`. -/
theorem gamma_eq_inv_of_secondEntry (h2 : (2 : E) = 0) {m : ℕ} (S : Subfield E)
    {ζ ω x : E} {γ : E → E} (hζ : ζ ≠ 0) (hζnorm : ζ * ζ ^ 2 ^ m = 1)
    (hω : ω * ω ^ 2 ^ m = ζ + ζ⁻¹) (hζS : ζ⁻¹ ∉ S)
    (hchain : ∀ a ∈ S, a ≠ 0 → a ^ 2 * γ a + a
      = γ a + x + (ζ⁻¹ ^ 2 * ω / (a + ζ⁻¹)) * (ζ⁻¹ * ω) ^ 2 ^ m) :
    x = ζ⁻¹ ∧ ∀ a ∈ S, a ≠ 0 → a ≠ 1 → γ a = (x + a)⁻¹ := by
  obtain ⟨hx, hγ⟩ := eq_and_inv_of_star h2 S (w := ζ⁻¹) (x := x) (γ := γ) hζS
    fun a ha ha0 => star_of_secondEntry h2 hζ hζnorm hω (hchain a ha ha0)
  exact ⟨hx, fun a ha ha0 ha1 => by rw [hγ a ha ha0 ha1, hx, add_comm a ζ⁻¹]⟩

end StepFourArithmetic

section ChainBridge

open OddOrder.FiniteField Suzuki2Groups

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]

/-- **Reading a two-factor identity on its second unitary entries** — the shape stage
(1) arrives in (Peterfalvi Part II, p. 131).

Both sides of the chain are products of two elements, and the multiplication rule of the
unitary coordinates contributes a cocycle term `p̄ q̄^q` to each.  On the left that term
vanishes, the second factor being central; on the right it survives, and it is the term
the book evaluates using `ω̄^{1+q} = ζ + ζ⁻¹`. -/
theorem secondEntry_of_chain (m : ℕ) (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    {L₁ L₂ R₁ R₂ : BilinearTwistedProduct (hermitianCocycle m hcard hu)}
    (hL₂ : L₂.quotient = 0) (heq : L₁ * L₂ = R₁ * R₂) :
    unitaryCoord m u L₁ + unitaryCoord m u L₂
      = unitaryCoord m u R₁ + unitaryCoord m u R₂
        + R₁.quotient * R₂.quotient ^ 2 ^ m := by
  have hL := unitaryCoord_mul m hcard hu L₁ L₂
  rw [heq, unitaryCoord_mul m hcard hu R₁ R₂, hL₂, zero_pow (by positivity),
    mul_zero, add_zero] at hL
  exact hL.symm

/-- **Stage (1), read in the unitary coordinates, is `(∗∗)`** (Peterfalvi Part II,
p. 131).

The hypotheses are the coordinates of the four factors of the chain

  `f(ω̄, x+a)^{ζ⁻¹ a} · (0, a) = f(ω̄, x+a)^{ζ⁻²} · (ω̄, x)^{ζ⁻¹}`,

each obtained from `exists_unitaryModel_conj` (the conjugations scale the two
coordinates by `μ` and its norm) together with stage (2) for the quotient coordinate of
`f(ω̄, x+a)`.  The three norms involved are `(ζ⁻¹a)^{1+q} = a²` and
`(ζ⁻²)^{1+q} = (ζ⁻¹)^{1+q} = 1`. -/
theorem star_of_chain (m : ℕ) (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (h2 : (2 : E) = 0)
    {L₁ L₂ R₁ R₂ : BilinearTwistedProduct (hermitianCocycle m hcard hu)}
    {ζ ω x a γa : E} (hζ : ζ ≠ 0) (hζnorm : ζ * ζ ^ 2 ^ m = 1)
    (hω : ω * ω ^ 2 ^ m = ζ + ζ⁻¹)
    (hL₂q : L₂.quotient = 0)
    (hL₁y : unitaryCoord m u L₁ = a ^ 2 * γa) (hL₂y : unitaryCoord m u L₂ = a)
    (hR₁y : unitaryCoord m u R₁ = γa)
    (hR₁q : R₁.quotient = ζ⁻¹ ^ 2 * ω / (a + ζ⁻¹))
    (hR₂y : unitaryCoord m u R₂ = x) (hR₂q : R₂.quotient = ζ⁻¹ * ω)
    (heq : L₁ * L₂ = R₁ * R₂) :
    (a ^ 2 + 1) * γa = x + a + (1 + ζ⁻¹ ^ 2) / (a + ζ⁻¹) := by
  have h := secondEntry_of_chain m hcard hu hL₂q heq
  rw [hL₁y, hL₂y, hR₁y, hR₂y, hR₁q, hR₂q] at h
  exact star_of_secondEntry h2 hζ hζnorm hω h

end ChainBridge

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **Stage (2) in the unitary coordinate system**: `f(ω s^a)‾ = ω̄/(μ(a²) + μ(ζ))`
(Peterfalvi Part II, p. 130 — the first entry of `f(ω̄, x + a)` on p. 131).

`stepTwo_linear` states this as the linear equation `(μ(a²) + μ(ζ)) · X̄ = ω̄` in the
coordinate `M.coord` of `Q ⧸ Z(Q)`.  `Ψ` reads that coordinate scaled by `e`, so the
equation survives verbatim, and `mu_K_add_mu_W_ne_zero` divides. -/
theorem stepTwo_quotient (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    {ζ ω a : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (haK : a ∈ hyp.KSet) (ha2 : a ^ 2 ∈ hyp.K)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q) :
    (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩).quotient
      = (Ψ ⟨ω, hωQ⟩).quotient /
        (((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
          + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)) := by
  have hne := hyp.mu_K_add_mu_W_ne_zero M hmu hζ1 (hyp.kActor ha2)
  have hlin := hyp.stepTwo_linear H hC2 M hZ hmu hVW hζ hωQ hωQ0 haK ha2 hf hXQ
  rw [eq_div_iff hne, mul_comm]
  rw [hΨq, hΨq, hquot, hquot]
  rw [show M.coord (Additive.ofMul (QuotientGroup.mk'
        (Subgroup.center hyp.Q)
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q))) from rfl,
    show M.coord (Additive.ofMul (QuotientGroup.mk'
        (Subgroup.center hyp.Q) (⟨ω, hωQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) from rfl]
  linear_combination e * hlin

/-- **Stage (3) in the unitary coordinate system**: `ω̄^{1+q} = ν · c(ω²)`
(Peterfalvi Part II, p. 130: `ω² = (0, ζ + ζ⁻¹)`).

The cocycle being Hermitian, the square of an element of `Q` is central with unitary
coordinate the norm of its quotient coordinate (`unitaryCoord_sq`); reading the same
element through the centre gives `ν` times its `centerCoord`.  With the book's
normalization `ν · c(s) = 1` the right-hand side is `c(ω²)/c(s)`, which is exactly the
`α` that `stepThree` evaluates as `μ(ζ) + μ(ζ)⁻¹`. -/
theorem stepThree_quotient_norm {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
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
    {ω y : G} (hωQ : ω ∈ hyp.Q) (hyQ0 : y ∈ hyp.Q0) (hsq : ω * ω = y) :
    (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = (ν : M.E) * hyp.centerCoord sfive M ι hyQ0 := by
  have hval : (⟨ω, hωQ⟩ : ↥hyp.Q) ^ 2
      = ((hyp.toCenter sfive hyQ0 : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) := by
    refine Subtype.ext ?_
    rw [pow_two]
    exact hsq
  calc (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = (Ψ ⟨ω, hωQ⟩).quotient * (Ψ ⟨ω, hωQ⟩).quotient ^ 2 ^ m := by
        rw [pow_succ]; ring
    _ = Suzuki2Groups.unitaryCoord m u ((Ψ ⟨ω, hωQ⟩) ^ 2) :=
        (Suzuki2Groups.unitaryCoord_sq m M.card hu _).symm
    _ = Suzuki2Groups.unitaryCoord m u
          (Ψ ((hyp.toCenter sfive hyQ0 : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q)) := by
        rw [← map_pow, hval]
    _ = (ν : M.E) * hyp.centerCoord sfive M ι hyQ0 :=
        hyp.unitaryCoord_toCenter sfive M Φ ι hker hu Ψ hΨq hΨc hyQ0

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
