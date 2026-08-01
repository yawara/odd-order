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
* `eq_of_star_at_one`, `inv_of_star` — `(∗∗)` forces `x = ζ⁻¹`, and then
  `γ(a) = 1/(a + ζ⁻¹)` one `a` at a time.
* `secondEntry_of_chain`, `star_of_chain` — the bridge from a two-factor identity in
  the twisted product to `(∗∗)`, which is how stage (1) enters.
* `Hypothesis.stepFour_base`, `Hypothesis.stepFour_pointwise`,
  `Hypothesis.stepFour_at_omega`, `Hypothesis.stepFour_elem`,
  `Hypothesis.stepFour_cover` — stage (4) itself.
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

That cocycle term is where `w` and `ω̄` disappear: `A C̄ = w² w^{-1} ω̄^{1+q}/(a + w)`,
and `ω̄^{1+q} = w + w⁻¹` by stage (3), leaving `(1 + w²)/(a + w)`.

The book's `ζ⁻¹` is carried as a single letter `w`, a norm-one element — that is how it
arrives from the model, as the scalar `μ(1, ζ)`. -/
theorem star_of_secondEntry (h2 : (2 : E) = 0) {m : ℕ} {w ω x a γa : E}
    (hw : w ≠ 0) (hwnorm : w * w ^ 2 ^ m = 1) (hω : ω * ω ^ 2 ^ m = w + w⁻¹)
    (hchain : a ^ 2 * γa + a
      = γa + x + (w ^ 2 * ω / (a + w)) * (w * ω) ^ 2 ^ m) :
    (a ^ 2 + 1) * γa = x + a + (1 + w ^ 2) / (a + w) := by
  have hwinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  have hwq : w ^ 2 ^ m = w⁻¹ := by
    field_simp
    linear_combination hwnorm
  -- the cocycle term collapses to `(1 + w²)/(a + w)`
  have hnum : w ^ 2 * ω * (w⁻¹ * ω ^ 2 ^ m) = 1 + w ^ 2 :=
    calc w ^ 2 * ω * (w⁻¹ * ω ^ 2 ^ m)
        = w ^ 2 * w⁻¹ * (ω * ω ^ 2 ^ m) := by ring
      _ = w ^ 2 * w⁻¹ * (w + w⁻¹) := by rw [hω]
      _ = (w * w⁻¹) * w ^ 2 + (w * w⁻¹) * (w * w⁻¹) := by ring
      _ = 1 + w ^ 2 := by rw [hwinv]; ring
  have hcoc : (w ^ 2 * ω / (a + w)) * (w * ω) ^ 2 ^ m = (1 + w ^ 2) / (a + w) := by
    rw [mul_pow, hwq, div_mul_eq_mul_div, hnum]
  rw [hcoc] at hchain
  linear_combination hchain + (γa - a) * h2

/-- **`(∗∗)` at `a = 1` pins `x`** (Peterfalvi Part II, p. 131: "For `a = 1`, this
becomes `0 = x + 1 + (1 + ζ⁻¹) = x + ζ⁻¹`").

The left side vanishes in characteristic two, and `(1 + w²)/(1 + w) = 1 + w`. -/
theorem eq_of_star_at_one (h2 : (2 : E) = 0) {w x v : E} (hw : (1 : E) + w ≠ 0)
    (hstar : ((1 : E) ^ 2 + 1) * v = x + 1 + (1 + w ^ 2) / (1 + w)) :
    x = w := by
  have hsq : (1 : E) + w ^ 2 = (1 + w) * (1 + w) := by linear_combination (-w) * h2
  have hzero : ((1 : E) ^ 2 + 1) * v = 0 := by
    rw [show ((1 : E) ^ 2 + 1) = 0 by linear_combination h2, zero_mul]
  rw [hsq, mul_div_assoc, div_self hw, mul_one, hzero] at hstar
  linear_combination -hstar + (-w - 1) * h2

/-- **`(∗∗)` away from `a ∈ {0, 1}` gives the value** (Peterfalvi Part II, p. 131:
"Thus, for `a ∈ F − {0,1}`, `γ(a) = 1/(a + ζ⁻¹)`").

Once `x = w` is known the right side collapses:
`w + a + (1 + w²)/(a + w) = [(a + w)² + 1 + w²]/(a + w) = (a² + 1)/(a + w)`, and
`a² + 1 = (a + 1)²` is invertible.

Stated for one `a` at a time — the value `v` is whatever the group side produces there,
so no indexing function is needed. -/
theorem inv_of_star (h2 : (2 : E) = 0) {w x a v : E} (haw : a + w ≠ 0) (ha1 : a ≠ 1)
    (hx : x = w) (hstar : (a ^ 2 + 1) * v = x + a + (1 + w ^ 2) / (a + w)) :
    v = (a + w)⁻¹ := by
  have hsq : a ^ 2 + 1 ≠ 0 := by
    intro hc
    refine ha1 ?_
    have hfac : (a + 1) * (a + 1) = 0 := by linear_combination hc + a * h2
    rcases mul_eq_zero.mp hfac with h | h <;>
      exact (by linear_combination h - h2 : a = 1)
  have hnum : (a ^ 2 + 1 : E) = (w + a) * (a + w) + (1 + w ^ 2) := by
    linear_combination (-(a * w) - w ^ 2) * h2
  have hrhs : (a ^ 2 + 1) / (a + w) = w + a + (1 + w ^ 2) / (a + w) := by
    rw [hnum, add_div, mul_div_assoc, div_self haw, mul_one]
  rw [hx, ← hrhs, div_eq_mul_inv] at hstar
  exact mul_left_cancel₀ hsq hstar

/-- **The computation closing stage (5)'s second case** (Peterfalvi Part II, p. 131, the
last display).

When `ρ̄` is *not* in the `K W`-orbit of `ω̄`, the book instead arranges that `f(ρ)` is,
and reads the formula backwards: from `ρ = (ρ̄, x) = f(ω̄', x') = (ω̄'/x', 1/x')` it gets
`ω̄' = ρ̄/x` and `x' = 1/x`.  Stage (2) of §2 then expresses `f(ρ̄, x + a)` as
`f(ω̄', x' + a⁻¹)^{a⁻¹} (0, a⁻¹)`, and substituting the known value of the inner `f`
gives, coordinate by coordinate,

  `a⁻¹ ω̄'/(x' + a⁻¹) = ρ̄/(x + a)`,
  `a⁻² /(x' + a⁻¹) + a⁻¹ = 1/(x + a)`,

the conjugation by `a⁻¹` scaling the second coordinate by the norm `a⁻²` (`a ∈ F`) and
the central factor `(0, a⁻¹)` adding `a⁻¹`.  The second identity is where characteristic
two enters: `x + a + x = a`. -/
theorem stepFive_secondCase (h2 : (2 : E) = 0) {r x a : E}
    (ha : a ≠ 0) (hx : x ≠ 0) (hxa : x + a ≠ 0) :
    a⁻¹ * ((r / x) / (x⁻¹ + a⁻¹)) = r / (x + a) ∧
      (a⁻¹) ^ 2 * (1 / (x⁻¹ + a⁻¹)) + a⁻¹ = (x + a)⁻¹ := by
  have hinv : x⁻¹ + a⁻¹ ≠ 0 := by
    intro hc
    refine hxa ?_
    field_simp at hc
    linear_combination hc
  have hsum : x⁻¹ + a⁻¹ = (x + a) / (x * a) := by
    field_simp
    ring
  rw [hsum]
  constructor
  · rw [div_div_eq_mul_div, eq_div_iff hxa]
    field_simp
  · rw [one_div_div, inv_eq_one_div (x + a), eq_div_iff hxa]
    field_simp
    linear_combination x * h2

/-- **The inversion formula is self-inverse** (Peterfalvi Part II, p. 131: "Then
`(ρ̄, x) = f(ω̄', x') = (ω̄'/x', 1/x')` and so `ω̄' = ρ̄/x` and `x' = 1/x`").

If `f` carries `(r_σ, y_σ)` to `(r_ρ, y_ρ)` by the formula, then it carries
`(r_ρ, y_ρ)` back to `(r_σ, y_σ)` by the same formula.  Stage (5) uses this in the
direction the book does: knowing `f` at `f(ρ)` — which is where the orbit argument puts
one — determines `f(ρ)` from `ρ`, since `f` is an involution (H2). -/
theorem inverseFormula_symm {rρ yρ rσ yσ : E} (hyσ : yσ ≠ 0)
    (h1 : rρ = rσ / yσ) (h2 : yρ = yσ⁻¹) :
    rσ = rρ / yρ ∧ yσ = yρ⁻¹ := by
  subst h1
  subst h2
  exact ⟨by field_simp, (inv_inv yσ).symm⟩

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
    {w ω x a γa : E} (hw : w ≠ 0) (hwnorm : w * w ^ 2 ^ m = 1)
    (hω : ω * ω ^ 2 ^ m = w + w⁻¹)
    (hL₂q : L₂.quotient = 0)
    (hL₁y : unitaryCoord m u L₁ = a ^ 2 * γa) (hL₂y : unitaryCoord m u L₂ = a)
    (hR₁y : unitaryCoord m u R₁ = γa)
    (hR₁q : R₁.quotient = w ^ 2 * ω / (a + w))
    (hR₂y : unitaryCoord m u R₂ = x) (hR₂q : R₂.quotient = w * ω)
    (heq : L₁ * L₂ = R₁ * R₂) :
    (a ^ 2 + 1) * γa = x + a + (1 + w ^ 2) / (a + w) := by
  have h := secondEntry_of_chain m hcard hu hL₂q heq
  rw [hL₁y, hL₂y, hR₁y, hR₂y, hR₁q, hR₂q] at h
  exact star_of_secondEntry h2 hw hwnorm hω h

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

/-- **§3 (4)'s `(∗∗)`** (Peterfalvi Part II, p. 131), assembled.

Stage (1), pushed through `Ψ` and read on the second unitary entries, is

  `(A² + 1) γ = x + A + (1 + Z²)/(A + Z)`,   `A = μ(a²)`,  `Z = μ(ζ)`,

`γ` and `x` being the unitary coordinates of `f(ω s^a)` and of `ω`.  The four factors'
coordinates come from the scalar action: conjugation by `kv` multiplies the quotient
coordinate by `μ(kv)` and the unitary one by `μ(kv)^{1+q} = μ(kv₁, 1)²` (`mu_norm_eq`),
so the `ζ`-conjugations leave the second entry alone and only `a²` survives.  The
central factor `s^a` contributes `A` on the nose, given the book's normalization
`ν · c(s) = 1`; and stage (2) (`stepTwo_quotient`) supplies the quotient coordinate of
`f(ω s^a)`.

The identification `Z = μ(1, ζ)` of the book's `ζ⁻¹` is why `hstage3` reads
`ω̄^{1+q} = Z + Z⁻¹`. -/
theorem stepFour_star (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
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
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    {ζ ω a : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (haK : a ∈ hyp.K) (ha2 : a ^ 2 ∈ hyp.K)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hstage3 : (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹) :
    (((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E) ^ 2 + 1) *
        Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩)
      = Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
        + ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
        + (1 + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2)
          / (((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
            + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)) := by
  classical
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have haKSet : a ∈ hyp.KSet := by rw [← hyp.coe_K]; exact haK
  have hzQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haK) hyp.distinguishedInvolution_mem_Q0
  -- ### the chain of stage (1), transported by `Ψ`
  have hchain0 := hyp.stepOne_conjQHom H hC2 M hZc hmu hVW hζ hωQ hωQ0 haKSet ha2 hf hXQ
  rw [hyp.kActor_one hyp.K.one_mem] at hchain0
  have heq := congrArg Ψ hchain0
  rw [map_mul, map_mul] at heq
  -- ### the scalars
  have hZ0 : ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ≠ 0 :=
    Units.ne_zero _
  have hZnorm :
      ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ (2 ^ m + 1)
        = 1 := by
    have h := congrArg (fun x : M.Eˣ => (x : M.E)) (M.mu_W_normOne (⟨ζ, hζ⟩ : ↥hyp.W))
    simpa using h
  have hZmul :
      ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) *
        ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 ^ m
      = 1 := by
    rw [← pow_succ']
    exact hZnorm
  have hone : ((M.mu ((1 : ↥hyp.actualKActor), (1 : ↥hyp.W)) : M.Eˣ) : M.E) = 1 := by
    rw [show ((1 : ↥hyp.actualKActor), (1 : ↥hyp.W)) = 1 from rfl, map_one, Units.val_one]
  have hζsq : (⟨ζ ^ 2, hyp.W.pow_mem hζ 2⟩ : ↥hyp.W) = (⟨ζ, hζ⟩ : ↥hyp.W) ^ 2 :=
    Subtype.ext (SubmonoidClass.coe_pow (⟨ζ, hζ⟩ : ↥hyp.W) 2).symm
  have hmuZ2 : ((M.mu ((1 : ↥hyp.actualKActor),
        (⟨ζ ^ 2, hyp.W.pow_mem hζ 2⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 := by
    rw [hζsq, show ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W) ^ 2)
        = ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) ^ 2 from
      Prod.ext (one_pow 2).symm rfl, map_pow, Units.val_pow_eq_pow_val]
  -- ### the four coordinates
  have hL₁y : Suzuki2Groups.unitaryCoord m u
      (Ψ (hyp.conjQHom (hyp.kActor ha2, (⟨ζ, hζ⟩ : ↥hyp.W))
        ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩))
      = ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E) ^ 2 *
        Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩) := by
    rw [hconjy, hyp.mu_norm_eq M]
  have hSaeq : (⟨a * hyp.distinguishedInvolution * a⁻¹, hyp.Q0_le_Q hzQ0⟩ : ↥hyp.Q)
      = ((hyp.toCenter sfive hzQ0 : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) := rfl
  have hL₂q : (Ψ ⟨a * hyp.distinguishedInvolution * a⁻¹,
      hyp.Q0_le_Q hzQ0⟩).quotient = 0 := by
    rw [hSaeq, hΨq, hker]
    exact mul_zero e
  have hL₂y : Suzuki2Groups.unitaryCoord m u
      (Ψ ⟨a * hyp.distinguishedInvolution * a⁻¹, hyp.Q0_le_Q hzQ0⟩)
      = ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E) := by
    rw [hSaeq, hyp.unitaryCoord_toCenter sfive M Φ ι hker hu Ψ hΨq hΨc hzQ0,
      hyp.centerCoord_conj_eq_mu_sq sfive M ι d hequiv hdsq haK
        hyp.distinguishedInvolution_mem_Q0]
    linear_combination ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E) * hs
  have hR₁y : Suzuki2Groups.unitaryCoord m u
      (Ψ (hyp.conjQHom ((1 : ↥hyp.actualKActor),
          (⟨ζ ^ 2, hyp.W.pow_mem hζ 2⟩ : ↥hyp.W))
        ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩))
      = Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩) := by
    rw [hconjy, hyp.mu_norm_eq M, hone, one_pow, one_mul]
  have hR₂y : Suzuki2Groups.unitaryCoord m u
      (Ψ (hyp.conjQHom ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) ⟨ω, hωQ⟩))
      = Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) := by
    rw [hconjy, hyp.mu_norm_eq M, hone, one_pow, one_mul]
  have hR₂q : (Ψ (hyp.conjQHom ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W))
      ⟨ω, hωQ⟩)).quotient
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) *
        (Ψ ⟨ω, hωQ⟩).quotient := hconjq _ _
  have hR₁q : (Ψ (hyp.conjQHom ((1 : ↥hyp.actualKActor),
      (⟨ζ ^ 2, hyp.W.pow_mem hζ 2⟩ : ↥hyp.W))
      ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩)).quotient
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 *
          (Ψ ⟨ω, hωQ⟩).quotient
        / (((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
          + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)) := by
    rw [hconjq, hmuZ2,
      hyp.stepTwo_quotient H hC2 M hZc hmu hVW Φ hquot hu Ψ hΨq hζ hζ1 hωQ hωQ0
        haKSet ha2 hf hXQ, mul_div_assoc]
  -- ### stage (3), as the norm of the quotient coordinate
  have hω : (Ψ ⟨ω, hωQ⟩).quotient * (Ψ ⟨ω, hωQ⟩).quotient ^ 2 ^ m
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    rw [← pow_succ']
    exact hstage3
  exact star_of_chain m M.card hu h2 hZ0 hZmul hω hL₂q hL₁y hL₂y hR₁y hR₁q hR₂y hR₂q heq

/-- **§3 (4), the base point**: `ω = (ω̄, ζ⁻¹)` (Peterfalvi Part II, p. 131: "For
`a = 1`, this becomes `0 = x + 1 + (1 + ζ⁻¹) = x + ζ⁻¹`, whence `x = ζ⁻¹`").

One instance of `(∗∗)` suffices, the one at the `a ∈ K` whose scalar `μ(a²)` is `1`;
`exists_mem_K_mu_sq_eq` provides it. -/
theorem stepFour_base (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
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
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hstage3 : (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hfQ : ∀ a : G, a ∈ hyp.K →
      f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q) :
    Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  obtain ⟨a, haK, hAeq⟩ := hyp.exists_mem_K_mu_sq_eq hm hQ0card sfive M
    (one_mem _) one_ne_zero
  have hval := hyp.stepFour_star H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu Ψ hΨq hΨc
    hconjq hconjy d hequiv hdsq hs hζ hζ1 hωQ hωQ0 haK (pow_mem haK 2) hf
    (hfQ a haK) hstage3
  have hne := hyp.mu_K_add_mu_W_ne_zero M hmu hζ1 (hyp.kActor (pow_mem haK 2))
  rw [hAeq] at hval hne
  exact eq_of_star_at_one h2 hne hval

/-- **§3 (4), the value at one point of the fibre**: the second unitary coordinate of
`f(ω s^a)` is `1/(μ(a²) + ζ⁻¹)` (Peterfalvi Part II, p. 131).

`stepFour_star` gives `(∗∗)` at this `a`, and `inv_of_star` solves it once the base
point is known (`stepFour_base`).  The excluded `μ(a²) = 1` is the book's `a = 1`. -/
theorem stepFour_pointwise (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
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
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hstage3 : (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹)
    (hx : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E))
    {a : G} (haK : a ∈ hyp.K)
    (ha1 : ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) ≠ 1)
    (hfQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q) :
    Suzuki2Groups.unitaryCoord m u
        (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hfQ⟩)
      = (((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E))⁻¹ := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  exact inv_of_star h2 (hyp.mu_K_add_mu_W_ne_zero M hmu hζ1 _) ha1 hx
    (hyp.stepFour_star H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu Ψ hΨq hΨc
      hconjq hconjy d hequiv hdsq hs hζ hζ1 hωQ hωQ0 haK (pow_mem haK 2) hf
      hfQ hstage3)

/-- **Stage (4) at the excluded point `A = 0`**, that is at `ω` itself (Peterfalvi
Part II, p. 131: "For `y = ζ⁻¹`, `(ω̄, y) = ω` and again we obtain
`f(ω) = ω^{-ζ} = (ω̄, ζ)^ζ = (ω̄/y, 1/y)`").

There is nothing to solve here — the standing hypothesis `f(ω) = ζ⁻¹ ω⁻¹ ζ` already
gives `f(ω)` as a conjugate of `ω⁻¹`, and the two coordinates come out directly:
inversion `q`-powers the unitary coordinate (`unitaryCoord_inv`) and the conjugation
multiplies it by the norm of `μ(1, ζ⁻¹)`, which is `1`.  With `y = Z` the answer
`(Z⁻¹ ω̄, Z⁻¹)` is `(ω̄/y, 1/y)`.

Note the direction: the book's `x^d` is `d⁻¹ x d`, so its `ζ` is conjugation by `ζ⁻¹`
here, whose scalar is `μ(1, ζ)⁻¹ = Z⁻¹`. -/
theorem stepFour_at_omega {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hfωQ : f ω ∈ hyp.Q)
    (hx : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)) :
    (Ψ ⟨f ω, hfωQ⟩).quotient
        = (Ψ ⟨ω, hωQ⟩).quotient / Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ω, hfωQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩))⁻¹ := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hZ0 : ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ≠ 0 :=
    Units.ne_zero _
  have hZnorm :
      ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ (2 ^ m + 1)
        = 1 := by
    have h := congrArg (fun x : M.Eˣ => (x : M.E)) (M.mu_W_normOne (⟨ζ, hζ⟩ : ↥hyp.W))
    simpa using h
  have hZq :
      ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 ^ m
        = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    field_simp
    rw [← pow_succ]
    exact hZnorm
  -- the scalar of the conjugation is `Z⁻¹`
  have hkv : ((M.mu (hyp.kActor hyp.K.one_mem,
        (⟨ζ⁻¹, hyp.W.inv_mem hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    rw [hyp.kActor_one hyp.K.one_mem,
      show ((1 : ↥hyp.actualKActor), (⟨ζ⁻¹, hyp.W.inv_mem hζ⟩ : ↥hyp.W))
        = ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W))⁻¹ from
      Prod.ext (inv_one (G := ↥hyp.actualKActor)).symm (Subtype.ext rfl),
      map_inv, Units.val_inv_eq_inv_val]
  have hnorm1 : ((M.mu (hyp.kActor hyp.K.one_mem,
      (⟨ζ⁻¹, hyp.W.inv_mem hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ (2 ^ m + 1) = 1 := by
    rw [hyp.mu_norm_eq M, hyp.kActor_one hyp.K.one_mem,
      show ((1 : ↥hyp.actualKActor), (1 : ↥hyp.W)) = 1 from rfl, map_one,
      Units.val_one, one_pow]
  -- `f(ω)` is the conjugate of `ω⁻¹` by `ζ⁻¹`
  have hfeq : (⟨f ω, hfωQ⟩ : ↥hyp.Q)
      = hyp.conjQHom (hyp.kActor hyp.K.one_mem,
          (⟨ζ⁻¹, hyp.W.inv_mem hζ⟩ : ↥hyp.W)) (⟨ω, hωQ⟩ : ↥hyp.Q)⁻¹ := by
    refine Subtype.ext ?_
    rw [hyp.conjQHom_kActor_apply_val hyp.K.one_mem (hyp.W.inv_mem hζ)]
    change f ω = 1 * ζ⁻¹ * ω⁻¹ * (1 * ζ⁻¹)⁻¹
    rw [hf]
    group
  constructor
  · have hneg : -(Ψ (⟨ω, hωQ⟩ : ↥hyp.Q)).quotient
        = (Ψ (⟨ω, hωQ⟩ : ↥hyp.Q)).quotient := by
      linear_combination (-(Ψ (⟨ω, hωQ⟩ : ↥hyp.Q)).quotient) * h2
    rw [hfeq, hconjq, map_inv, Suzuki2Groups.BilinearTwistedProduct.quotient_inv, hkv,
      hx, hneg, div_eq_mul_inv, mul_comm]
  · rw [hfeq, hconjy, map_inv,
      Suzuki2Groups.unitaryCoord_inv m M.card hu, hnorm1, one_mul, hx, hZq]

/-- **Moving along the fibre adds `μ(a²)` to the unitary coordinate**: `ω s^a` is the
book's `(ω̄, x + a)` (Peterfalvi Part II, p. 131).

Right multiplication by a central element shifts the unitary coordinate by that
element's own coordinate (the cocycle term drops out, the quotient coordinate of a
central element being `0`), and that coordinate is `μ(a²)` once the centre is
normalized so that `s = (0, 1)`. -/
theorem unitaryCoord_mul_conj {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
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
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    {ω a : G} (hωQ : ω ∈ hyp.Q) (haK : a ∈ hyp.K)
    (hprodQ : ω * (a * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q) :
    Suzuki2Groups.unitaryCoord m u
        (Ψ ⟨ω * (a * hyp.distinguishedInvolution * a⁻¹), hprodQ⟩)
      = Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
        + ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) := by
  have hzQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haK) hyp.distinguishedInvolution_mem_Q0
  have hSaeq : (⟨a * hyp.distinguishedInvolution * a⁻¹, hyp.Q0_le_Q hzQ0⟩ : ↥hyp.Q)
      = ((hyp.toCenter sfive hzQ0 : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) := rfl
  have hcq : (Ψ ⟨a * hyp.distinguishedInvolution * a⁻¹,
      hyp.Q0_le_Q hzQ0⟩).quotient = 0 := by
    rw [hSaeq, hΨq, hker]
    exact mul_zero e
  have hcy : Suzuki2Groups.unitaryCoord m u
      (Ψ ⟨a * hyp.distinguishedInvolution * a⁻¹, hyp.Q0_le_Q hzQ0⟩)
      = ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) := by
    rw [hSaeq, hyp.unitaryCoord_toCenter sfive M Φ ι hker hu Ψ hΨq hΨc hzQ0,
      hyp.centerCoord_conj_eq_mu_sq sfive M ι d hequiv hdsq haK
        hyp.distinguishedInvolution_mem_Q0]
    linear_combination ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) * hs
  have hmul : (⟨ω * (a * hyp.distinguishedInvolution * a⁻¹), hprodQ⟩ : ↥hyp.Q)
      = (⟨ω, hωQ⟩ : ↥hyp.Q) *
        ⟨a * hyp.distinguishedInvolution * a⁻¹, hyp.Q0_le_Q hzQ0⟩ := Subtype.ext rfl
  rw [hmul, map_mul, Suzuki2Groups.unitaryCoord_mul m M.card hu, hcq, hcy,
    zero_pow (by positivity), mul_zero, add_zero]

/-- **The fibre of `ω̄` is `{ω} ∪ {ω s^a : a ∈ K}`** (Peterfalvi Part II, p. 131: the
elements `(ω̄, y)` over which stage (4) quantifies).

Elements of `Q` with the same quotient coordinate differ by an element of `Q₀`
(`exists_mem_Q0_mul_of_quotient_eq`), and `K` is transitive on `Q₀^#`
(`exists_mem_KSet_conj_eq_of_mem_Q0`), so the fibre is swept by `a ↦ ω s^a` together
with `ω` itself. -/
theorem eq_or_exists_conj_mul_of_quotient_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} (hene : e ≠ 0)
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    {ρ ω : G} (hρQ : ρ ∈ hyp.Q) (hωQ : ω ∈ hyp.Q)
    (h : (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient) :
    ρ = ω ∨ ∃ (a : G) (_ : a ∈ hyp.K),
      ρ = ω * (a * hyp.distinguishedInvolution * a⁻¹) := by
  -- the two coordinates agree, hence the two classes
  have hcoord : M.coord (Additive.ofMul
        (QuotientGroup.mk' (Subgroup.center hyp.Q) (⟨ρ, hρQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul
        (QuotientGroup.mk' (Subgroup.center hyp.Q) (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
    rw [← hquot, ← hquot]
    exact mul_left_cancel₀ hene (by rw [← hΨq, ← hΨq]; exact h)
  have hmk : (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q) :
      ↥hyp.Q ⧸ Subgroup.center hyp.Q) = QuotientGroup.mk ⟨ρ, hρQ⟩ :=
    (M.coord.injective hcoord).symm
  obtain ⟨w, hwQ0, hw⟩ := hyp.exists_mem_Q0_mul_of_quotient_eq hZc hωQ hρQ hmk
  by_cases hw1 : w = 1
  · exact Or.inl (by rw [hw, hw1, mul_one])
  · obtain ⟨k, hkSet, hk⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hwQ0 hw1
    have hkK : k ∈ hyp.K := by rw [← hyp.coe_K] at hkSet; exact hkSet
    refine Or.inr ⟨k⁻¹, hyp.K.inv_mem hkK, ?_⟩
    rw [hw, ← hk]
    group

/-- **§3 (4), on elements**: `f(ω̄, y) = (ω̄/y, 1/y)` for every element of the fibre of
`ω̄` other than the one excluded point (Peterfalvi Part II, p. 131).

The pointwise conclusions of `stepFour_pointwise`, `stepTwo_quotient` and
`stepFour_at_omega` are transported to elements by the parametrization of the fibre: an
element with the same quotient coordinate as `ω` is `ω` itself or `ω s^a`, and its
unitary coordinate is `x + μ(a²)` (`unitaryCoord_mul_conj`).  The excluded point is
`y = x + 1`, i.e. `μ(a²) = 1`; the book recovers it by re-running the argument with
`ω⁻¹` and `ζ⁻¹`, which moves the exclusion to `x⁻¹ + 1 ≠ x + 1` (`mu_W_ne_inv`). -/
theorem stepFour_elem {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} (hene : e ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hΨc : ∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central)
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    {ω : G} (hωQ : ω ∈ hyp.Q)
    (hpt : ∀ (a : G) (haK : a ∈ hyp.K)
      (hfQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q),
      ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) ≠ 1 →
      Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hfQ⟩)
        = (((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)
          + Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩))⁻¹)
    (hquotf : ∀ (a : G) (haK : a ∈ hyp.K)
      (hfQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q),
      (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hfQ⟩).quotient
        = (Ψ ⟨ω, hωQ⟩).quotient
          / (((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)
            + Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)))
    (homega : ∀ hfωQ : f ω ∈ hyp.Q,
      (Ψ ⟨f ω, hfωQ⟩).quotient
          = (Ψ ⟨ω, hωQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ω, hfωQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩))⁻¹)
    {ρ : G} (hρQ : ρ ∈ hyp.Q) (hfρQ : f ρ ∈ hyp.Q)
    (hfib : (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient)
    (hne : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
      ≠ Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) + 1) :
    (Ψ ⟨f ρ, hfρQ⟩).quotient
        = (Ψ ⟨ω, hωQ⟩).quotient / Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfρQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  obtain hcase | ⟨a, haK, hρ⟩ :=
    hyp.eq_or_exists_conj_mul_of_quotient_eq M hZc Φ hquot hu Ψ hene hΨq hρQ hωQ hfib
  · subst hcase
    exact homega hfρQ
  · subst hρ
    have hy := hyp.unitaryCoord_mul_conj sfive M Φ ι hker hu Ψ hΨq hΨc d hequiv hdsq
      hs hωQ haK hρQ
    have hA1 : ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) ≠ 1 := by
      intro hc
      exact hne (by rw [hy, hc])
    refine ⟨?_, ?_⟩
    · rw [hquotf a haK hfρQ, hy]
      congr 1
      exact add_comm _ _
    · rw [hpt a haK hfρQ hA1, hy]
      congr 1
      exact add_comm _ _

/-! ### The second half of stage (4): re-running the argument at `ω⁻¹` -/

/-- **Inversion does not move the quotient coordinate** (characteristic two). -/
theorem quotient_inv_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωinvQ : ω⁻¹ ∈ hyp.Q) :
    (Ψ ⟨ω⁻¹, hωinvQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have heq : (⟨ω⁻¹, hωinvQ⟩ : ↥hyp.Q) = (⟨ω, hωQ⟩ : ↥hyp.Q)⁻¹ := Subtype.ext rfl
  rw [heq, map_inv, Suzuki2Groups.BilinearTwistedProduct.quotient_inv]
  linear_combination (-(Ψ (⟨ω, hωQ⟩ : ↥hyp.Q)).quotient) * h2

/-- **Inversion `q`-powers the unitary coordinate**: `(a, y)⁻¹ = (a, ȳ)`. -/
theorem unitaryCoord_inv_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωinvQ : ω⁻¹ ∈ hyp.Q) :
    Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω⁻¹, hωinvQ⟩)
      = Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) ^ 2 ^ m := by
  have heq : (⟨ω⁻¹, hωinvQ⟩ : ↥hyp.Q) = (⟨ω, hωQ⟩ : ↥hyp.Q)⁻¹ := Subtype.ext rfl
  rw [heq, map_inv, Suzuki2Groups.unitaryCoord_inv m M.card hu]

/-- **Stage (4) on the whole fibre** (Peterfalvi Part II, p. 131: "all of these results
remain valid if we replace `ω` by `ω⁻¹` and `ζ` by `ζ⁻¹` … this completes the proof as
`ζ + 1 ≠ ζ⁻¹ + 1`").

Each run of `stepFour_elem` leaves out one point — the one whose unitary coordinate is
`1` more than that of its base point.  The two base points `ω` and `ω⁻¹` have distinct
unitary coordinates (`x` and `x^q = x⁻¹`, distinct by `mu_W_ne_inv`), so the two
excluded points differ and the two runs together cover the fibre.

That `ω⁻¹` may be used as a base point at all is `f_inv_eq`: `f(ω⁻¹) = ζ ω ζ⁻¹` is
exactly the standing hypothesis `f(ω') = ζ'⁻¹ ω'⁻¹ ζ'` for `(ω', ζ') = (ω⁻¹, ζ⁻¹)`. -/
theorem stepFour_cover {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωinvQ : ω⁻¹ ∈ hyp.Q)
    (hxne : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
      ≠ Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω⁻¹, hωinvQ⟩))
    (h1 : ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q) (hfρQ : f ρ ∈ hyp.Q),
      (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient →
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
          ≠ Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) + 1 →
        (Ψ ⟨f ρ, hfρQ⟩).quotient
            = (Ψ ⟨ω, hωQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfρQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹)
    (h2 : ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q) (hfρQ : f ρ ∈ hyp.Q),
      (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ω⁻¹, hωinvQ⟩).quotient →
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
          ≠ Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω⁻¹, hωinvQ⟩) + 1 →
        (Ψ ⟨f ρ, hfρQ⟩).quotient
            = (Ψ ⟨ω⁻¹, hωinvQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfρQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹) :
    ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q) (hfρQ : f ρ ∈ hyp.Q),
      (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient →
        (Ψ ⟨f ρ, hfρQ⟩).quotient
            = (Ψ ⟨ω, hωQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfρQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  have hq := hyp.quotient_inv_eq M hu Ψ hωQ hωinvQ
  intro ρ hρQ hfρQ hfib
  by_cases hy : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
      = Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) + 1
  · -- the point `ω` misses; the run at `ω⁻¹` catches it
    have hy2 : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
        ≠ Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω⁻¹, hωinvQ⟩) + 1 := by
      rw [hy]
      exact fun hc => hxne (add_right_cancel hc)
    obtain ⟨hA, hB⟩ := h2 ρ hρQ hfρQ (hfib.trans hq.symm) hy2
    exact ⟨hA.trans (by rw [hq]), hB⟩
  · exact h1 ρ hρQ hfρQ hfib hy

/-! ### Stage (5): the formula is `K W`-equivariant -/

/-- **(H3) for the `K W`-action, in the shape `conjQHom` uses**:
`f(ρ^{(k,v)}) = f(ρ)^{(k⁻¹, v)}`.

(H3) reads `f(x^a) = f(x)^{a^t}`, and on `K W` the twist `a ↦ a^t` is `(k, v) ↦
(k⁻¹, v)`: `t` inverts `K` (`mul_t_eq_of_mem_KSet`, whose content is exactly the
defining property of `KSet`) and centralizes `W` (`conj_t_pow_eq`).

Together with `mu_t_twist` this is what feeds `stepFive_equivariant`. -/
theorem f_conjQHom (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {k v : G} (hk : k ∈ hyp.KSet) (hkK : k ∈ hyp.K) (hv : v ∈ hyp.W)
    {x : G} (hxQ : x ∈ hyp.Q) (hx1 : x ≠ 1) (hfxQ : f x ∈ hyp.Q)
    (hfconjQ : f (k * v * x * (k * v)⁻¹) ∈ hyp.Q) :
    (⟨f (k * v * x * (k * v)⁻¹), hfconjQ⟩ : ↥hyp.Q)
      = hyp.conjQHom (hyp.kActor (hyp.K.inv_mem hkK), ⟨v, hv⟩) ⟨f x, hfxQ⟩ := by
  have htinv : hyp.t⁻¹ = hyp.t := inv_eq_of_mul_eq_one_right hyp.rankOneSetup.invol
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  have hvD : v ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hv)
  have hcD : k * v ∈ hyp.D := hyp.D.mul_mem (hyp.K_le_D hkK) hvD
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hxQ hx1 (hyp.D.inv_mem hcD)
  rw [inv_inv] at h3
  -- the `t`-twist of `k v` is `k⁻¹ v`
  have htv : hyp.t * v * hyp.t = v := by
    have hp := hyp.conj_t_pow_eq hv 1
    rwa [pow_one] at hp
  have hsplit : hyp.t * (k * v) * hyp.t = k⁻¹ * v := by
    have e : (hyp.t * k * hyp.t) * (hyp.t * v * hyp.t) = hyp.t * (k * v) * hyp.t := by
      calc (hyp.t * k * hyp.t) * (hyp.t * v * hyp.t)
          = hyp.t * k * (hyp.t * hyp.t) * v * hyp.t := by group
        _ = hyp.t * (k * v) * hyp.t := by rw [htt]; group
    rw [← e, hk.2, htv]
  have hprod : (hyp.t * (k * v) * hyp.t) * (hyp.t * (k * v)⁻¹ * hyp.t) = 1 := by
    calc (hyp.t * (k * v) * hyp.t) * (hyp.t * (k * v)⁻¹ * hyp.t)
        = hyp.t * (k * v) * (hyp.t * hyp.t) * (k * v)⁻¹ * hyp.t := by group
      _ = hyp.t * (k * v) * 1 * (k * v)⁻¹ * hyp.t := by rw [htt]
      _ = hyp.t * hyp.t := by group
      _ = 1 := htt
  have hstep : hyp.t * (k * v)⁻¹ * hyp.t = (k⁻¹ * v)⁻¹ := by
    rw [← hsplit]
    symm
    rw [inv_eq_iff_mul_eq_one]
    exact hprod
  rw [hstep, inv_inv] at h3
  refine Subtype.ext ?_
  rw [hyp.conjQHom_kActor_apply_val (hyp.K.inv_mem hkK) hv]
  exact h3

/-- **The inversion formula propagates along `K W`-orbits** (Peterfalvi Part II, §3 (5),
p. 131, the opening display):

  `f(d ρ̄, d^{1+q} y) = f(ρ̄, y)^{d^t} = (ρ̄/y, 1/y)^{d^{-q}} = (ρ̄/(d^q y), 1/(d^{1+q} y))`.

The hypotheses are the coordinates of the two conjugates: `ρ' = ρ^d` scales by `d` and
its norm, and `σ' = f(ρ') = f(ρ)^{d^t}` scales by the twisted scalar `(d^q)⁻¹` and *its*
norm (`mu_t_twist` identifies that twisted scalar).  The conclusion is that the shape
`(ρ̄/y, 1/y)` is preserved, and it is pure arithmetic: `((d^q)⁻¹)^{1+q} = (d^{1+q})⁻¹`
because `d^{q²} = d`. -/
theorem stepFive_equivariant {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {ρ ρ' σ σ' : ↥hyp.Q} {c : M.E} (hc : c ≠ 0)
    (hy : Suzuki2Groups.unitaryCoord m u (Ψ ρ) ≠ 0)
    (hρq : (Ψ ρ').quotient = c * (Ψ ρ).quotient)
    (hρy : Suzuki2Groups.unitaryCoord m u (Ψ ρ')
      = c ^ (2 ^ m + 1) * Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (hσq : (Ψ σ').quotient = (c ^ 2 ^ m)⁻¹ * (Ψ σ).quotient)
    (hσy : Suzuki2Groups.unitaryCoord m u (Ψ σ')
      = ((c ^ 2 ^ m)⁻¹) ^ (2 ^ m + 1) * Suzuki2Groups.unitaryCoord m u (Ψ σ))
    (h1 : (Ψ σ).quotient
      = (Ψ ρ).quotient / Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (h2 : Suzuki2Groups.unitaryCoord m u (Ψ σ)
      = (Suzuki2Groups.unitaryCoord m u (Ψ ρ))⁻¹) :
    (Ψ σ').quotient
        = (Ψ ρ').quotient / Suzuki2Groups.unitaryCoord m u (Ψ ρ') ∧
      Suzuki2Groups.unitaryCoord m u (Ψ σ')
        = (Suzuki2Groups.unitaryCoord m u (Ψ ρ'))⁻¹ := by
  have hcq : (c ^ 2 ^ m) ^ 2 ^ m = c :=
    OddOrder.FiniteField.frobPow_frobPow m M.card c
  have hcq0 : c ^ 2 ^ m ≠ 0 := pow_ne_zero _ hc
  have hcn0 : c ^ (2 ^ m + 1) ≠ 0 := pow_ne_zero _ hc
  have hkey : (c ^ 2 ^ m) ^ (2 ^ m + 1) = c ^ (2 ^ m + 1) := by
    rw [pow_succ, pow_succ, hcq]
    ring
  constructor
  · rw [hσq, hρq, hρy, h1, pow_succ]
    field_simp
  · rw [hσy, hρy, h2, inv_pow, hkey, mul_inv]

/-- **Stage (5)'s first half**: the inversion formula holds at every `K W`-translate of
a point where it holds (Peterfalvi Part II, p. 131).

`f_conjQHom` turns (H3) into the statement that `f` intertwines the `K W`-action with
its `t`-twist, `mu_t_twist` evaluates that twist on scalars as `d ↦ (d^q)⁻¹`, and
`stepFive_equivariant` checks that the shape `(ρ̄/y, 1/y)` survives.

So stage (4) plus this covers every `ρ` whose quotient coordinate lies in the
`K W`-orbit of `ω̄` — which is the first case of the book's proof. -/
theorem stepFive_orbit (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    {k v : G} (hk : k ∈ hyp.KSet) (hkK : k ∈ hyp.K) (hv : v ∈ hyp.W)
    {ρ : G} (hρQ : ρ ∈ hyp.Q) (hρ1 : ρ ≠ 1) (hfρQ : f ρ ∈ hyp.Q)
    (hρ'Q : k * v * ρ * (k * v)⁻¹ ∈ hyp.Q)
    (hfρ'Q : f (k * v * ρ * (k * v)⁻¹) ∈ hyp.Q)
    (hy : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ≠ 0)
    (h1 : (Ψ ⟨f ρ, hfρQ⟩).quotient
      = (Ψ ⟨ρ, hρQ⟩).quotient / Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))
    (h2 : Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfρQ⟩)
      = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹) :
    (Ψ ⟨f (k * v * ρ * (k * v)⁻¹), hfρ'Q⟩).quotient
        = (Ψ ⟨k * v * ρ * (k * v)⁻¹, hρ'Q⟩).quotient /
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨k * v * ρ * (k * v)⁻¹, hρ'Q⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f (k * v * ρ * (k * v)⁻¹), hfρ'Q⟩)
        = (Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨k * v * ρ * (k * v)⁻¹, hρ'Q⟩))⁻¹ := by
  have hkinv : hyp.kActor (hyp.K.inv_mem hkK) = (hyp.kActor hkK)⁻¹ :=
    hyp.kActor_eq_inv hkK (hyp.K.inv_mem hkK) rfl
  have hρeq : (⟨k * v * ρ * (k * v)⁻¹, hρ'Q⟩ : ↥hyp.Q)
      = hyp.conjQHom (hyp.kActor hkK, ⟨v, hv⟩) ⟨ρ, hρQ⟩ :=
    Subtype.ext (hyp.conjQHom_kActor_apply_val hkK hv ⟨ρ, hρQ⟩).symm
  have hfeq := hyp.f_conjQHom H hk hkK hv hρQ hρ1 hfρQ hfρ'Q
  refine hyp.stepFive_equivariant M hu Ψ
    (c := ((M.mu (hyp.kActor hkK, (⟨v, hv⟩ : ↥hyp.W)) : M.Eˣ) : M.E))
    (Units.ne_zero _) hy ?_ ?_ ?_ ?_ h1 h2
  · rw [hρeq, hconjq]
  · rw [hρeq, hconjy]
  · rw [hfeq, hconjq, hkinv, hyp.mu_t_twist M]
  · rw [hfeq, hconjy, hkinv, hyp.mu_t_twist M]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
