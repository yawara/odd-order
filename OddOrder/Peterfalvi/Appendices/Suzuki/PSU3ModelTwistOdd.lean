/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionThree

/-!
# The odd order of the model's twist

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. III §3, pp. 120–121, into Ch. IV §3 (3), p. 130.

Stage (3) of Ch. IV §3 argues by

> since `θ` is of odd order, `|F| ≥ 8` …

and Appendix III Definition 3 carries "`θ` of odd order" as part of the definition of a
type-`B` Suzuki `2`-group.  This file shows the standard model *proves* it, so nothing has
to be transported from the type-`B` datum.

The whole content is that `K` is **regular** on `Z(Q)^#`.  In the central coordinate `ι`
the action of `K` is `z ↦ μ(k)^d z` (`hequiv`) and `μ(K)` is all of `F^×`
(`exists_actualKActor_mu_eq`), so regularity says exactly that

> `a ↦ a^d` is onto `F^×`.

The model's own cocycle relation `a^d = a · θ(a)` (`zpow_eq_mul_thetaModel`) turns that
into "`a ↦ a · θ(a)` is onto `F^×`", and for an automorphism of `𝐅_{2^m}` that forces odd
order (`odd_orderOf_of_mul_self_surjective`): writing `θ|_F = Frob^r`, an even
`orderOf θ|_F = m / gcd(m, r)` would make `2^{gcd(m,r)} + 1 > 1` divide both `2^r + 1` and
`2^m − 1`, giving a second preimage of `1`.

## Main results

* `Hypothesis.exists_zpow_eq_of_mem_frobFixed` — `a ↦ a^d` is onto `F^×`, from the
  regularity of `K` on `Z(Q)^#`.
* `Hypothesis.odd_orderOf_thetaModel_restrict` — the model's twist `θ` has odd order
  on `F`.
* `Hypothesis.odd_orderOf_scalingPair_of_model` — hence so does the twist `σ⁻¹τ` of the
  type-`B` scaling pair, which is what Ch. IV §3 (3) consumes.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp

/-- **`a ↦ a^d` is onto `F^×`** (Peterfalvi Part II, Ch. III §3, p. 120).

`K` is transitive on `Z(Q)^#` (`LemmaFiveSetup.transCenter`) and acts there by
multiplication by `μ(k)^d` in the coordinate `ι` (`hequiv`); so, `ι` being onto `F`,
every `a ∈ F^×` is `μ(k)^d` for some `k`, and `μ(k)` lies in `F^×` as well.

This is the regularity of `K` on `Z(Q)^#` in the form Ch. III §3 needs it: the exponent
`d` is invertible modulo `|F^×|`. -/
theorem exists_zpow_eq_of_mem_frobFixed {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) {d : ℤ}
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    {a : M.E} (ha : a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (ha0 : a ≠ 0) :
    ∃ b ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, b ≠ 0 ∧ b ^ d = a := by
  classical
  -- a base point of the action, and its coordinate
  haveI : Nontrivial ↥(Subgroup.center hyp.Q) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr sfive.centerNeBot
  obtain ⟨x₀, hx₀⟩ := exists_ne (1 : ↥(Subgroup.center hyp.Q))
  have hc₀0 : ((ι (Additive.ofMul x₀) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) ≠ 0 := by
    intro h
    refine hx₀ ?_
    have h1 : ι (Additive.ofMul x₀) = 0 := Subtype.ext h
    have h2 : Additive.ofMul x₀ = 0 := by
      have := congrArg ι.symm h1
      simpa using this
    simpa using congrArg Additive.toMul h2
  -- the central element whose coordinate is `a · ι(x₀)`
  set w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
    (⟨a, ha⟩ : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) *
      ι (Additive.ofMul x₀) with hw
  have hwval : ((w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = a * ((ι (Additive.ofMul x₀) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := rfl
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hwval
    exact (mul_ne_zero ha0 hc₀0) hwval.symm
  set z : ↥(Subgroup.center hyp.Q) := Additive.toMul (ι.symm w) with hz
  have hzcoord : ι (Additive.ofMul z) = w := by
    rw [hz]
    simp
  have hz1 : z ≠ 1 := by
    intro h
    refine hw0 ?_
    rw [← hzcoord, h]
    simp
  -- transitivity of `K` on `Z(Q)^#` moves the base point to it
  obtain ⟨k, hk⟩ := sfive.transCenter (x₀ : ↥hyp.Q) (z : ↥hyp.Q) x₀.2
    (fun hc => hx₀ (Subtype.ext hc)) z.2 (fun hc => hz1 (Subtype.ext hc))
  have hkz : hyp.centerKHom k x₀ = z :=
    Subtype.ext ((hyp.centerKHom_apply_val k x₀).trans hk)
  -- read the coordinate equation
  have heq := hequiv k x₀
  rw [hkz, hzcoord, hwval] at heq
  refine ⟨((M.mu (k, 1) : M.Eˣ) : M.E),
    OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k),
    (M.mu (k, 1)).ne_zero, ?_⟩
  rw [← Units.val_zpow_eq_zpow_val]
  exact mul_right_cancel₀ hc₀0 heq.symm

/-- **The scaling pair, for the model's own coordinate** (Peterfalvi Part II, Ch. III §3,
p. 121, step (2)).

`exists_scalingPair_of_lemmaFiveSetup` produces a pair together with *its own* exponent,
which need not be the `d` a given coordinate `ι` exhibits (replacing `ι` by `Frobⁱ ∘ ι`
replaces `d` by `2ⁱ d`).  Here the coordinate is the input, so the pair comes out for that
`ι`'s exponent — which is the shape Ch. IV §3 (3) needs, `hequiv` being the model's own
central clause.

Nothing changes in the argument: the quadratic map `χ = ι ∘ (squaring)` is anisotropic,
hence nonzero, so the Lemma 2(c) expansion has a surviving coefficient, and the
corresponding pair converts every scaling law of `χ` into an identity `σ(a) τ(a) = b`.
The two laws used are `χ(μ(k) x) = μ(k)^d χ(x)` and `χ(μ(v) x) = χ(x)` for `v ∈ W`. -/
theorem exists_scalingPair_of_centerCoordinate {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) :
    ∃ σ τ : M.E ≃+* M.E,
      (∀ k : ↥hyp.actualKActor,
        σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
          = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E)) ∧
      ∀ v : ↥hyp.W,
        σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1 := by
  classical
  have hχ : hyp.centreQuadraticMapE sfive M ι ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : M.E)
    refine hx (hyp.centreQuadraticMap_anisotropic sfive M ι x (Subtype.ext ?_))
    have hx0 : hyp.centreQuadraticMapE sfive M ι x = 0 := by rw [h]; rfl
    simpa using hx0
  obtain ⟨σ, τ, hpair⟩ :=
    OddOrder.RepresentationTheory.exists_algAut_pair_scaling_of_ne_zero M.E
      (hyp.centreQuadraticMapE sfive M ι) hχ
  refine ⟨σ.toRingEquiv, τ.toRingEquiv,
    fun k => hpair _ _ fun x => hyp.centreQuadraticMap_smul sfive M ι d hequiv k x,
    fun v => hpair _ _ fun x => ?_⟩
  have h := hyp.centreQuadraticMap_smul_KW sfive M ι d hequiv (1, v) x
  rw [show M.mu ((1 : ↥hyp.actualKActor), (1 : ↥hyp.W)) = 1 from map_one M.mu] at h
  simpa using h

/-- **The model's twist has odd order on `F`** (Peterfalvi Part II, Ch. III §3, p. 121;
Appendix III Definition 3).

`zpow_eq_mul_thetaModel` says the product map `a ↦ a · θ(a)` *is* `a ↦ a^d` on `F^×`, and
`exists_zpow_eq_of_mem_frobFixed` says the latter is onto — that is the regularity of `K`
on `Z(Q)^#`.  An automorphism of `𝐅_{2^m}` whose product map is onto has odd order
(`odd_orderOf_of_mul_self_surjective`).

So the odd order of Appendix III Definition 3's `θ` is a *theorem* about the standard
model, not an extra hypothesis to be transported from the type-`B` datum. -/
theorem odd_orderOf_thetaModel_restrict {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (θm : M.E ≃+* M.E) {d : ℤ}
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (hscaleQ0 : ∀ k : ↥hyp.actualKActor, ∀ x y : M.E,
      ((φ (((M.mu (k, 1) : M.Eˣ) : M.E) * x) (((M.mu (k, 1) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) :
    Odd (orderOf (OddOrder.FiniteField.restrictToFrobFixed (m := m) θm)) := by
  refine OddOrder.FiniteField.odd_orderOf_restrictToFrobFixed_of_mul_self_surjective hm
    M.card θm fun a ha ha0 => ?_
  obtain ⟨b, hb, hb0, hbd⟩ := hyp.exists_zpow_eq_of_mem_frobFixed sfive M ι hequiv ha ha0
  refine ⟨b, hb, hb0, ?_⟩
  rw [← hbd]
  exact (hyp.zpow_eq_mul_thetaModel hm hQ0card sfive M (θm : M.E → M.E) hsemi haniso
    hscaleQ0 b hb hb0).symm

/-- **The scaling pair's twist has odd order** (Peterfalvi Part II, Ch. IV §3 (3), p. 130).

The last hypothesis of stage (3) — the book's "`θ` is of odd order" — discharged from the
standard model alone.  `odd_orderOf_thetaModel_restrict` gives it for the model's own
twist, and `odd_orderOf_scalingPair_restrict_of_model` transfers it to `σ⁻¹τ` through the
book's `{σ|_F, τ|_F} = {1_F, θ}`.

`θF` is presented as in `stepThree_model`: an automorphism of `F` agreeing with `σ⁻¹τ`
pointwise. -/
theorem odd_orderOf_scalingPair_of_model {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (θm : M.E ≃+* M.E) {d : ℤ}
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (hscaleQ0 : ∀ k : ↥hyp.actualKActor, ∀ x y : M.E,
      ((φ (((M.mu (k, 1) : M.Eˣ) : M.E) * x) (((M.mu (k, 1) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (σ τ : M.E ≃+* M.E)
    (hscale : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (θF : RingAut ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hθF : ∀ a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
      ((θF a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = σ.symm (τ (a : M.E))) :
    Odd (orderOf θF) := by
  have hodd := hyp.odd_orderOf_scalingPair_restrict_of_model hm hQ0card sfive M θm hsemi
    haniso hscaleQ0 σ τ hscale
    (hyp.odd_orderOf_thetaModel_restrict hm hQ0card sfive M θm hsemi haniso hscaleQ0 ι
      hequiv)
  have hEq : θF = (OddOrder.FiniteField.restrictToFrobFixed (m := m) σ)⁻¹ *
      OddOrder.FiniteField.restrictToFrobFixed (m := m) τ := by
    refine RingEquiv.ext fun a => Subtype.ext ?_
    rw [hθF a, OddOrder.FiniteField.coe_restrictToFrobFixed_inv_mul]
  rw [hEq]
  exact hodd

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
