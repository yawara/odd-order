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
since `x = w` turns `a + w` into `x + a`.  Together with stage (2)'s first entry
`ω̄/(a + w) = ω̄/(x + a)` this is the book's `f(ω̄, y) = (ω̄/y, 1/y)`, for
`y = x + a` with `a ∈ F − {0, 1}`. -/
theorem gamma_eq_inv_of_secondEntry (h2 : (2 : E) = 0) {m : ℕ} (S : Subfield E)
    {w ω x : E} {γ : E → E} (hw : w ≠ 0) (hwnorm : w * w ^ 2 ^ m = 1)
    (hω : ω * ω ^ 2 ^ m = w + w⁻¹) (hwS : w ∉ S)
    (hchain : ∀ a ∈ S, a ≠ 0 → a ^ 2 * γ a + a
      = γ a + x + (w ^ 2 * ω / (a + w)) * (w * ω) ^ 2 ^ m) :
    x = w ∧ ∀ a ∈ S, a ≠ 0 → a ≠ 1 → γ a = (x + a)⁻¹ := by
  obtain ⟨hx, hγ⟩ := eq_and_inv_of_star h2 S (w := w) (x := x) (γ := γ) hwS
    fun a ha ha0 => star_of_secondEntry h2 hw hwnorm hω (hchain a ha ha0)
  exact ⟨hx, fun a ha ha0 ha1 => by rw [hγ a ha ha0 ha1, hx, add_comm a w]⟩

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

/-- **§3 (4)** (Peterfalvi Part II, p. 131): *`f(ω̄, y) = (ω̄/y, 1/y)`* on the fibre of
`ω̄`, in the two halves the book proves it in —

* `ω = (ω̄, ζ⁻¹)`: the second unitary coordinate of `ω` is `Z = μ(ζ)`;
* `f(ω̄, x + A) = (ω̄/(x + A), 1/(x + A))` for `A ∈ F − {0, 1}`.

The first coordinate is stage (2) (`stepTwo_quotient`, whose denominator `A + Z` is
`x + A` once `x = Z` is known); this theorem supplies the second.

`(∗∗)` holds for one `a ∈ K` at a time (`stepFour_star`); `exists_mem_K_mu_sq_eq` says
the resulting scalars `μ(a²)` are *all* of `F^×`, which is what lets
`eq_and_inv_of_star` run over the whole subfield.  The two excluded values are the
book's: `A = 0` is `ω` itself, and `A = 1` is the point it recovers at the end of (4) by
replacing `ω` with `ω⁻¹` and `ζ` with `ζ⁻¹`.

`γ` is the caller's name for `a ↦` the unitary coordinate of `f(ω s^a)`, indexed by the
scalar rather than by the group element. -/
theorem stepFour (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
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
    (hfQ : ∀ a : G, a ∈ hyp.K →
      f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (γ : M.E → M.E)
    (hγ : ∀ (a : G) (haK : a ∈ hyp.K),
      γ ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)
        = Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hfQ a haK⟩)) :
    Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
        = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ∧
      ∀ A ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, A ≠ 0 → A ≠ 1 →
        γ A = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) + A)⁻¹ := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hstar : ∀ A ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, A ≠ 0 →
      (A ^ 2 + 1) * γ A
        = Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) + A
          + (1 + ((M.mu ((1 : ↥hyp.actualKActor),
              (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2)
            / (A + ((M.mu ((1 : ↥hyp.actualKActor),
              (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)) := by
    intro A hA hA0
    obtain ⟨a, haK, hAeq⟩ := hyp.exists_mem_K_mu_sq_eq hm hQ0card sfive M hA hA0
    rw [← hAeq, hγ a haK]
    exact hyp.stepFour_star H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu Ψ hΨq hΨc
      hconjq hconjy d hequiv hdsq hs hζ hζ1 hωQ hωQ0 haK (pow_mem haK 2) hf
      (hfQ a haK) hstage3
  obtain ⟨hx, hginv⟩ := eq_and_inv_of_star h2
    (OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (hyp.mu_W_notMem_frobFixed M hmu hζ1) hstar
  exact ⟨hx, fun A hA hA0 hA1 => by
    rw [hginv A hA hA0 hA1, hx, add_comm A _]⟩

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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
