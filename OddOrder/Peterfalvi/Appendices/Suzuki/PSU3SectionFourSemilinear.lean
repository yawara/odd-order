/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourCoordinate
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourSetup
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourArithmetic
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelIsomorphism

/-!
# Peterfalvi Part II, Ch. IV §4: `η` acts semilinearly on `E`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, p. 133:

> In the following calculations, we again identify `Q ⋊ KW` with the group `S₁ ⋊ K₁W₁` of
> Chapter III, §3.  Then, by Proposition 2 of Appendix I, `η` acts as a semilinear mapping
> on `Q/Q₀ ≅ E`.  Let `μ` denote the automorphism of the field `E` associated with `η`.
> Thus, for `x ∈ E`, `x^η` is given by the action of `η` on `Q/Q₀` and the isomorphism
> `Q/Q₀ ≅ E`, while `x^μ` is given by the action of `η` on `KW` and the isomorphism
> `KW ≅ K₁W₁`.

This file supplies the *first* half of that paragraph: conjugation by an element `d ∈ D`
is an additive automorphism `coordConjD` of `E`, and it intertwines the scalar action of
`K W` with the scalar action of the conjugated pair.  That is the semilinearity, with the
"associated automorphism" still in the form "conjugate the pair `(κ, v)` by `d`" rather
than as a field automorphism of `E`.

The `μ` of the book — an honest `E ≃+* E` — is built on top of this; the point of
separating the two is that the intertwining relation below is pure group theory (`D`
normalizes both `K` and `W`, and conjugation is a homomorphism), needing neither the
irreducibility input of Appendix I, Proposition 2, nor the identification of the abstract
endomorphism field it returns with the model's `E`.

## Main results

* `Hypothesis.conj_mem_K_of_mem_D`, `Hypothesis.conj_mem_W_of_mem_D` — `D` normalizes `K`
  (Ch. I §2 Proposition 2) and `W`.
* `Hypothesis.quotientDHom` — the action of `D` on `Q ⧸ Z(Q)` by conjugation.
* `Hypothesis.coordConjD` — the same, read in the coordinate `Q ⧸ Z(Q) ≅ E`; an additive
  automorphism of `E`.
* `Hypothesis.coordConjD_coord_val` — its defining property on coordinates of elements.
* `Hypothesis.coordConjD_mu_smul` — **semilinearity over the scalars of `K W`**:
  `(μ(κ, v) · e)^d = μ(κ^{d⁻¹}, v^{d⁻¹}) · e^d`.
* `Hypothesis.coordConjD_fixed_of_conj_eq` — `d` fixes the coordinate of anything it
  centralizes; in §4 that is the book's `ω̄^η = ω̄`.
* `addEquiv_mul_mul_eq_of_span`, `scaledRingEquiv` — the purely algebraic core of "a
  semilinear additive bijection is a field automorphism times a constant".
* `Hypothesis.exists_frobFixed_repr` — `E = F + F z` for any `z ∈ E − F`.  The `z ∉ F`
  it is applied at is the existing `mu_W_notMem_frobFixed` (Ch. IV §3, p. 131).
* `Hypothesis.coordFieldAut` — **the book's `μ`**, an `E ≃+* E`, and
  `Hypothesis.coordConjD_eq_coordFieldAut_mul` — the semilinearity
  `x^η = x^μ · 1^η` in the form (5)–(9) consume.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

/-! ### A semilinear additive bijection is a scaled field automorphism

Let `E` be a field, `F` a subfield and `z ∈ E` with `E = F + F z`, and let `Ψ` be an
additive bijection of `E` which is "multiplicative up to the constant `Ψ 1`" on the
scalars `F ∪ {z}`.  Then it is multiplicative up to that same constant *everywhere*, so
that `x ↦ Ψ x / Ψ 1` is a field automorphism `σ` and `Ψ x = σ x · Ψ 1`.

This is the elementary substitute, in the situation of Ch. IV §4, for the general
Appendix I, Proposition 2: there the semilinearity comes out of the irreducibility of the
`K W`-action, and its field is an abstract endomorphism algebra which then has to be
identified with the model's `E`.  Here the model's field is *given*, and the scalars for
which the intertwining relation is already known — `μ(K) = F^×` together with `μ(1, ζ)` —
happen to span `E`, so multiplicativity extends by a two-line computation. -/

section ScaledRingEquiv

variable {E : Type*} [Field E]

/-- **Multiplicativity up to `Ψ 1` extends from a spanning pair of scalars to all of `E`.**

Writing `x = a + b z` with `a, b ∈ F` and expanding `x y = a y + b (z y)`, the two
hypotheses turn every term into `Ψ(·) Ψ(·)`, and the constants match up. -/
theorem addEquiv_mul_mul_eq_of_span {F : Subfield E} {z : E} (Ψ : E ≃+ E) (h1 : Ψ 1 ≠ 0)
    (hF : ∀ a ∈ F, ∀ x : E, Ψ (a * x) * Ψ 1 = Ψ a * Ψ x)
    (hz : ∀ x : E, Ψ (z * x) * Ψ 1 = Ψ z * Ψ x)
    (hspan : ∀ x : E, ∃ a ∈ F, ∃ b ∈ F, x = a + b * z)
    (x y : E) : Ψ (x * y) * Ψ 1 = Ψ x * Ψ y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hspan x
  have hxy : (a + b * z) * y = a * y + b * (z * y) := by ring
  rw [hxy, map_add, map_add]
  have e1 : Ψ (a * y) * Ψ 1 = Ψ a * Ψ y := hF a ha y
  have e2 : Ψ (b * (z * y)) * Ψ 1 = Ψ b * Ψ (z * y) := hF b hb (z * y)
  have e3 : Ψ (z * y) * Ψ 1 = Ψ z * Ψ y := hz y
  have e5 : Ψ (b * z) * Ψ 1 = Ψ b * Ψ z := hF b hb z
  have key : Ψ (b * (z * y)) * Ψ 1 * Ψ 1 = Ψ (b * z) * Ψ y * Ψ 1 := by
    linear_combination Ψ 1 * e2 + Ψ b * e3 - Ψ y * e5
  have key2 : Ψ (b * (z * y)) * Ψ 1 = Ψ (b * z) * Ψ y := mul_right_cancel₀ h1 key
  linear_combination e1 + key2

/-- **The field automorphism underlying a semilinear additive bijection**: `x ↦ Ψ x / Ψ 1`.

This is the book's `μ` (Peterfalvi Part II, Ch. IV §4, p. 133), once `Ψ` is the action of
`η` on `E`. -/
noncomputable def scaledRingEquiv (Ψ : E ≃+ E) (h1 : Ψ 1 ≠ 0)
    (hmul : ∀ x y : E, Ψ (x * y) * Ψ 1 = Ψ x * Ψ y) : E ≃+* E where
  toFun x := Ψ x * (Ψ 1)⁻¹
  invFun y := Ψ.symm (y * Ψ 1)
  left_inv x := by
    dsimp only
    rw [mul_assoc, inv_mul_cancel₀ h1, mul_one, AddEquiv.symm_apply_apply]
  right_inv y := by
    dsimp only
    rw [AddEquiv.apply_symm_apply, mul_assoc, mul_inv_cancel₀ h1, mul_one]
  map_add' x y := by rw [map_add, add_mul]
  map_mul' x y := by
    have h := hmul x y
    field_simp
    linear_combination h

@[simp] theorem scaledRingEquiv_apply (Ψ : E ≃+ E) (h1 : Ψ 1 ≠ 0)
    (hmul : ∀ x y : E, Ψ (x * y) * Ψ 1 = Ψ x * Ψ y) (x : E) :
    scaledRingEquiv Ψ h1 hmul x = Ψ x * (Ψ 1)⁻¹ := rfl

/-- **The semilinearity in its final shape**: `Ψ (c x) = σ(c) Ψ(x)` for *every* `c ∈ E`,
with `σ` the field automorphism.  This is `(c x)^η = c^μ x^η`. -/
theorem addEquiv_mul_eq_scaledRingEquiv_mul (Ψ : E ≃+ E) (h1 : Ψ 1 ≠ 0)
    (hmul : ∀ x y : E, Ψ (x * y) * Ψ 1 = Ψ x * Ψ y) (c x : E) :
    Ψ (c * x) = scaledRingEquiv Ψ h1 hmul c * Ψ x := by
  rw [scaledRingEquiv_apply]
  refine mul_right_cancel₀ h1 ?_
  rw [hmul c x]
  field_simp

/-- `Ψ x = x^μ · Ψ 1`. -/
theorem addEquiv_eq_scaledRingEquiv_mul_one (Ψ : E ≃+ E) (h1 : Ψ 1 ≠ 0)
    (hmul : ∀ x y : E, Ψ (x * y) * Ψ 1 = Ψ x * Ψ y) (x : E) :
    Ψ x = scaledRingEquiv Ψ h1 hmul x * Ψ 1 := by
  rw [scaledRingEquiv_apply, mul_assoc, inv_mul_cancel₀ h1, mul_one]

/-- The intertwining hypothesis of `addEquiv_mul_mul_eq_of_span`, in the form the group
theory delivers it: `Ψ (c x) = ν c · Ψ x` for a *constant* `ν c`. -/
theorem mul_apply_one_eq_of_smul (Ψ : E ≃+ E) {c ν : E}
    (h : ∀ x : E, Ψ (c * x) = ν * Ψ x) (x : E) :
    Ψ (c * x) * Ψ 1 = Ψ c * Ψ x := by
  have hc : Ψ c = ν * Ψ 1 := by
    have h1 := h 1
    rwa [mul_one] at h1
  rw [h x, hc]
  ring

end ScaledRingEquiv

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ### `D` normalizes `K` and `W` -/

include hyp in
/-- **`D` normalizes `W`** (`D_le_normalizer_W`), in element form.  Its `K`-companion is
the existing `conj_mem_K_of_mem_D` (Ch. I §2, Proposition 2). -/
theorem conj_mem_W_of_mem_D {d w : G} (hd : d ∈ hyp.D) (hw : w ∈ hyp.W) :
    d * w * d⁻¹ ∈ hyp.W :=
  (Subgroup.mem_normalizer_iff.mp (hyp.D_le_normalizer_W hd) w).mp hw

include hyp in
/-- Conjugation by an element of `D` maps `Q` to `Q`. -/
theorem conj_mem_Q_of_mem_D {d x : G} (hd : d ∈ hyp.D) (hx : x ∈ hyp.Q) :
    d * x * d⁻¹ ∈ hyp.Q := by
  have hm := hyp.rankOneSetup.DQ d⁻¹ (hyp.D.inv_mem hd) x hx
  rwa [inv_inv] at hm

/-! ### The `D`-action on the coordinate -/

/-- The action of `D` on the central quotient `Q ⧸ Z(Q)` induced by conjugation.  The
centre is characteristic, so no fixed-point information is needed; this is the `D`-version
of `quotientWHom` and `quotientKHom`. -/
@[reducible] noncomputable def quotientDHom :
    ↥hyp.D →* MulAut (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
  quotientMulAutHom (IsAInvariant.of_characteristic hyp.conjQByD)

/-- **Conjugation by `d ∈ D`, read in the coordinate `Q ⧸ Z(Q) ≅ E`.**

This is the book's `x ↦ x^d` on `E` (p. 133 writes it for `d = η`).  It is only *additive*:
for `d ∈ K W` it is multiplication by the scalar `μ(d)`, but a general `d ∈ D` — such as
§4's `η ∈ P`, which lies outside `K W` precisely because `V ≠ W` there — moves the scalars
too, and `coordConjD_mu_smul` records how. -/
noncomputable def coordConjD {m : ℕ} (M : hyp.QuotientFieldModel m) (d : ↥hyp.D) :
    M.E ≃+ M.E :=
  (M.coord.symm.trans (MulEquiv.toAdditive (hyp.quotientDHom d))).trans M.coord

theorem coordConjD_apply_coord {m : ℕ} (M : hyp.QuotientFieldModel m) (d : ↥hyp.D)
    (x : ↥hyp.Q) :
    hyp.coordConjD M d (M.coord (Additive.ofMul (QuotientGroup.mk x)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (hyp.conjQByD d x))) := by
  simp only [coordConjD, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rfl

include hyp in
/-- `coordConjD` on the coordinate of a named element of `Q`, in the shape `coord_conj_eq`
is stated in. -/
theorem coordConjD_coord_val {m : ℕ} (M : hyp.QuotientFieldModel m) {d x w : G}
    (hd : d ∈ hyp.D) (hxQ : x ∈ hyp.Q) (hwQ : w ∈ hyp.Q) (hval : d * x * d⁻¹ = w) :
    hyp.coordConjD M ⟨d, hd⟩
        (M.coord (Additive.ofMul (QuotientGroup.mk (⟨x, hxQ⟩ : ↥hyp.Q))))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨w, hwQ⟩ : ↥hyp.Q))) := by
  have hstep : hyp.conjQByD ⟨d, hd⟩ (⟨x, hxQ⟩ : ↥hyp.Q) = (⟨w, hwQ⟩ : ↥hyp.Q) :=
    Subtype.ext (by rw [hyp.conjQByD_apply_val]; exact hval)
  rw [hyp.coordConjD_apply_coord M ⟨d, hd⟩ ⟨x, hxQ⟩, hstep]

include hyp in
/-- **Semilinearity of `coordConjD` over the scalars of `K W`** (Peterfalvi Part II,
Ch. IV §4, p. 133).

Conjugation by `d` carries the action of `κ v` into the action of `κ^{d⁻¹} v^{d⁻¹}`,
because `d ((κ v) x (κ v)⁻¹) d⁻¹ = (d κ v d⁻¹) (d x d⁻¹) (d κ v d⁻¹)⁻¹` and `D`
normalizes both `K` and `W`.  Read in the coordinate, "the action of `κ v`" *is*
multiplication by `μ(κ, v)`, so this says exactly

  `(μ(κ, v) · e)^d = μ(κ^{d⁻¹}, v^{d⁻¹}) · e^d`,

the book's `(c x)^η = c^μ x^η`.  Note that no property of the model beyond `coord_act` is
used, and that the "field automorphism `μ`" of the book is here still in its
group-theoretic form: `(κ, v) ↦ (κ^{d⁻¹}, v^{d⁻¹})`. -/
theorem coordConjD_mu_smul {m : ℕ} (M : hyp.QuotientFieldModel m) {d κ v : G}
    (hd : d ∈ hyp.D) (hκ : κ ∈ hyp.K) (hv : v ∈ hyp.W)
    (hκ' : d * κ * d⁻¹ ∈ hyp.K) (hv' : d * v * d⁻¹ ∈ hyp.W) (e : M.E) :
    hyp.coordConjD M ⟨d, hd⟩ (((M.mu (hyp.kActor hκ, ⟨v, hv⟩) : M.Eˣ) : M.E) * e)
      = ((M.mu (hyp.kActor hκ', ⟨d * v * d⁻¹, hv'⟩) : M.Eˣ) : M.E)
        * hyp.coordConjD M ⟨d, hd⟩ e := by
  obtain ⟨y, rfl⟩ := M.coord.surjective e
  obtain ⟨⟨x, hxQ⟩, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
  have hy : y = Additive.ofMul (QuotientGroup.mk (⟨x, hxQ⟩ : ↥hyp.Q)) := by rw [hx]; rfl
  subst hy
  have hκD : κ ∈ hyp.D := hyp.K_le_D hκ
  have hvD : v ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hv)
  have h1 : (κ * v) * x * (κ * v)⁻¹ ∈ hyp.Q :=
    hyp.conj_mem_Q_of_mem_D (mul_mem hκD hvD) hxQ
  have h2 : d * ((κ * v) * x * (κ * v)⁻¹) * d⁻¹ ∈ hyp.Q := hyp.conj_mem_Q_of_mem_D hd h1
  have h3 : d * x * d⁻¹ ∈ hyp.Q := hyp.conj_mem_Q_of_mem_D hd hxQ
  rw [← hyp.coord_conj_eq M hκ hv hxQ h1 rfl,
    hyp.coordConjD_coord_val M hd h1 h2 rfl,
    hyp.coordConjD_coord_val M hd hxQ h3 rfl]
  exact hyp.coord_conj_eq M hκ' hv' h3 h2 (by group)

include hyp in
/-- **`coordConjD` fixes what `d` centralizes.**

In §4 this is the book's `ω̄^η = ω̄`: step (1) produces `ω ∈ C_Q(P)` and `η` lies in `P`. -/
theorem coordConjD_fixed_of_conj_eq {m : ℕ} (M : hyp.QuotientFieldModel m) {d x : G}
    (hd : d ∈ hyp.D) (hxQ : x ∈ hyp.Q) (hfix : d * x * d⁻¹ = x) :
    hyp.coordConjD M ⟨d, hd⟩
        (M.coord (Additive.ofMul (QuotientGroup.mk (⟨x, hxQ⟩ : ↥hyp.Q))))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨x, hxQ⟩ : ↥hyp.Q))) :=
  hyp.coordConjD_coord_val M hd hxQ hxQ hfix

/-! ### The field automorphism `μ` -/

variable {m : ℕ}

include hyp in
/-- Every element of the actual `K`-actor comes from an element of `K`. -/
theorem exists_kActor_eq (k : ↥hyp.actualKActor) :
    ∃ (κ : G) (hκ : κ ∈ hyp.K), hyp.kActor hκ = k := by
  have hmem : (k : MulAut ↥hyp.Q) ∈ hyp.conjQByK.range := k.2
  obtain ⟨⟨κ, hκ⟩, hk⟩ := hmem
  exact ⟨κ, hκ, Subtype.ext hk⟩

include hyp in
/-- `coordConjD_mu_smul` at `v = 1`: the `K`-scalars. -/
theorem coordConjD_muK_smul (M : hyp.QuotientFieldModel m) {d κ : G} (hd : d ∈ hyp.D)
    (hκ : κ ∈ hyp.K) (e : M.E) :
    hyp.coordConjD M ⟨d, hd⟩ (((M.mu (hyp.kActor hκ, 1) : M.Eˣ) : M.E) * e)
      = ((M.mu (hyp.kActor (hyp.conj_mem_K_of_mem_D hd hκ), 1) : M.Eˣ) : M.E)
        * hyp.coordConjD M ⟨d, hd⟩ e := by
  have h := hyp.coordConjD_mu_smul M hd hκ hyp.W.one_mem (hyp.conj_mem_K_of_mem_D hd hκ)
    (hyp.conj_mem_W_of_mem_D hd hyp.W.one_mem) e
  have e1 : (⟨(1 : G), hyp.W.one_mem⟩ : ↥hyp.W) = 1 := rfl
  have e2 : (⟨d * 1 * d⁻¹, hyp.conj_mem_W_of_mem_D hd hyp.W.one_mem⟩ : ↥hyp.W) = 1 :=
    Subtype.ext (by simp)
  rw [e1, e2] at h
  exact h

include hyp in
/-- `coordConjD_mu_smul` at `κ = 1`: the `W`-scalars. -/
theorem coordConjD_muW_smul (M : hyp.QuotientFieldModel m) {d v : G} (hd : d ∈ hyp.D)
    (hv : v ∈ hyp.W) (e : M.E) :
    hyp.coordConjD M ⟨d, hd⟩ (((M.mu (1, ⟨v, hv⟩) : M.Eˣ) : M.E) * e)
      = ((M.mu (1, ⟨d * v * d⁻¹, hyp.conj_mem_W_of_mem_D hd hv⟩) : M.Eˣ) : M.E)
        * hyp.coordConjD M ⟨d, hd⟩ e := by
  have h := hyp.coordConjD_mu_smul M hd hyp.K.one_mem hv
    (hyp.conj_mem_K_of_mem_D hd hyp.K.one_mem) (hyp.conj_mem_W_of_mem_D hd hv) e
  have e0 : hyp.kActor (hyp.conj_mem_K_of_mem_D hd hyp.K.one_mem) = 1 := by
    refine Subtype.ext ?_
    change hyp.conjQByK ⟨d * 1 * d⁻¹, hyp.conj_mem_K_of_mem_D hd hyp.K.one_mem⟩ = 1
    rw [show (⟨d * 1 * d⁻¹, hyp.conj_mem_K_of_mem_D hd hyp.K.one_mem⟩ : ↥hyp.K) = 1 from
      Subtype.ext (by simp), map_one]
  rw [hyp.kActor_one hyp.K.one_mem, e0] at h
  exact h

include hyp in
/-- **`E = F + F z` for `z ∉ F`** (Peterfalvi Part II, Ch. IV §4, p. 134, used through
`sectionFour_lambda_eq_one`).

`|F| = q` and `|E| = q²`, and `1`, `z` are independent over `F` because `z ∉ F`
(`eq_zero_of_add_mul_eq_zero`), so `(a, b) ↦ a + b z` is an injection `F × F → E` between
sets of the same size. -/
theorem exists_frobFixed_repr (M : hyp.QuotientFieldModel m) (hm : m ≠ 0) {z : M.E}
    (hz : z ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (x : M.E) :
    ∃ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      ∃ b ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, x = a + b * z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := OddOrder.FiniteField.frobFixedSubfield M.E 2 m with hFdef
  have hFcard : Nat.card ↥F = 2 ^ m :=
    OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm
  set φ : ↥F × ↥F → M.E := fun p => (p.1 : M.E) + (p.2 : M.E) * z with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hEq
    have h0 : ((a : M.E) - (a' : M.E)) + ((b : M.E) - (b' : M.E)) * z = 0 := by
      simp only [hφ] at hEq
      linear_combination hEq
    obtain ⟨h1, h2⟩ := eq_zero_of_add_mul_eq_zero hz
      (F.sub_mem a.2 a'.2) (F.sub_mem b.2 b'.2) h0
    have ha : (a : M.E) = (a' : M.E) := by linear_combination h1
    have hb : (b : M.E) = (b' : M.E) := by linear_combination h2
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hcard : Nat.card (↥F × ↥F) = Nat.card M.E := by
    rw [Nat.card_prod, hFcard, M.card, sq]
  obtain ⟨⟨a, b⟩, hab⟩ :=
    ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).surjective x
  exact ⟨a, a.2, b, b.2, hab.symm⟩

include hyp in
/-- **Conjugation by `d ∈ D` is multiplicative up to the constant `1^d`** — the hypothesis
`scaledRingEquiv` needs, verified on the model.

The scalars for which the intertwining relation is already known are `μ(K) = F^×`
(`coordConjD_muK_smul`, `exists_actualKActor_mu_eq`) and `μ(1, ζ)`
(`coordConjD_muW_smul`), and the latter is assumed to lie outside `F` — which for a
nontrivial `ζ` is the existing `mu_W_notMem_frobFixed`.  So the two together span `E` over
`F` (`exists_frobFixed_repr`) and `addEquiv_mul_mul_eq_of_span` applies. -/
theorem coordConjD_mul_mul_eq (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) {d ζ : G} (hd : d ∈ hyp.D)
    (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (x y : M.E) :
    hyp.coordConjD M ⟨d, hd⟩ (x * y) * hyp.coordConjD M ⟨d, hd⟩ 1
      = hyp.coordConjD M ⟨d, hd⟩ x * hyp.coordConjD M ⟨d, hd⟩ y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ψ := hyp.coordConjD M ⟨d, hd⟩ with hΨ
  set z : M.E := ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) with hzdef
  have h1 : Ψ 1 ≠ 0 := fun hc =>
    one_ne_zero (Ψ.injective (by rw [hc, map_zero]))
  refine addEquiv_mul_mul_eq_of_span (F := OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (z := z) Ψ h1 ?_ ?_ (fun w => hyp.exists_frobFixed_repr M hm hznot w) x y
  · intro a ha w
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq s M hm hQ0card ha ha0
    obtain ⟨κ, hκ, hkκ⟩ := hyp.exists_kActor_eq k
    subst hkκ
    subst hk
    exact mul_apply_one_eq_of_smul Ψ (hyp.coordConjD_muK_smul M hd hκ) w
  · intro w
    exact mul_apply_one_eq_of_smul Ψ (hyp.coordConjD_muW_smul M hd hζ) w

/-- **🎯 The book's `μ`** (Peterfalvi Part II, Ch. IV §4, p. 133): the field automorphism
of `E` associated with `d ∈ D`.

`coordConjD` is the action `x ↦ x^d` on `E`; dividing it by `1^d` makes it multiplicative
(`coordConjD_mul_mul_eq`), hence a field automorphism.  In §4, `d = η` and this is the
`μ` of (5)–(10). -/
noncomputable def coordFieldAut (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) {d ζ : G} (hd : d ∈ hyp.D)
    (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) : M.E ≃+* M.E :=
  scaledRingEquiv (hyp.coordConjD M ⟨d, hd⟩)
    (fun hc => one_ne_zero ((hyp.coordConjD M ⟨d, hd⟩).injective (by rw [hc, map_zero])))
    (hyp.coordConjD_mul_mul_eq s M hm hQ0card hd hζ hznot)

include hyp in
/-- **The semilinearity in the shape (5)–(9) use it**: `(c x)^d = c^μ · x^d`. -/
theorem coordConjD_mul_eq_coordFieldAut_mul (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {d ζ : G} (hd : d ∈ hyp.D) (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (c x : M.E) :
    hyp.coordConjD M ⟨d, hd⟩ (c * x)
      = hyp.coordFieldAut s M hm hQ0card hd hζ hznot c * hyp.coordConjD M ⟨d, hd⟩ x :=
  addEquiv_mul_eq_scaledRingEquiv_mul _ _ _ c x

include hyp in
/-- `x^d = x^μ · 1^d`. -/
theorem coordConjD_eq_coordFieldAut_mul (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {d ζ : G} (hd : d ∈ hyp.D) (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (x : M.E) :
    hyp.coordConjD M ⟨d, hd⟩ x
      = hyp.coordFieldAut s M hm hQ0card hd hζ hznot x * hyp.coordConjD M ⟨d, hd⟩ 1 :=
  addEquiv_eq_scaledRingEquiv_mul_one _ _ _ x

/-! ### `μ` on the scalars of `K W`

The book (p. 133) describes `μ` twice over: as "the automorphism of `E` associated with
`η`", and as "the action of `η` on `K W` under `K W ≅ K₁ W₁`".  These lemmas are that
second description: on the scalars, `μ` *is* conjugation of the pair. -/

include hyp in
/-- `μ` is pinned on a scalar by its intertwining constant. -/
theorem coordFieldAut_eq_of_smul (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) {d ζ : G} (hd : d ∈ hyp.D)
    (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) {c ν : M.E}
    (h : ∀ x : M.E, hyp.coordConjD M ⟨d, hd⟩ (c * x) = ν * hyp.coordConjD M ⟨d, hd⟩ x) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot c = ν := by
  have h1 : hyp.coordConjD M ⟨d, hd⟩ 1 ≠ 0 := fun hc =>
    one_ne_zero ((hyp.coordConjD M ⟨d, hd⟩).injective (by rw [hc, map_zero]))
  refine mul_right_cancel₀ h1 ?_
  rw [← hyp.coordConjD_mul_eq_coordFieldAut_mul s M hm hQ0card hd hζ hznot c 1]
  exact h 1

include hyp in
/-- **`μ` on a `K`-scalar is the `K`-scalar of the conjugated element**: `(κ₁)^μ = (κ^{d⁻¹})₁`. -/
theorem coordFieldAut_muK (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) {d ζ : G} (hd : d ∈ hyp.D)
    (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) {κ : G} (hκ : κ ∈ hyp.K) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot ((M.mu (hyp.kActor hκ, 1) : M.Eˣ) : M.E)
      = ((M.mu (hyp.kActor (hyp.conj_mem_K_of_mem_D hd hκ), 1) : M.Eˣ) : M.E) :=
  hyp.coordFieldAut_eq_of_smul s M hm hQ0card hd hζ hznot (hyp.coordConjD_muK_smul M hd hκ)

include hyp in
/-- **`μ` on a `W`-scalar**: `(v₁)^μ = (v^{d⁻¹})₁`. -/
theorem coordFieldAut_muW (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) {d ζ : G} (hd : d ∈ hyp.D)
    (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) {v : G} (hv : v ∈ hyp.W) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot ((M.mu (1, ⟨v, hv⟩) : M.Eˣ) : M.E)
      = ((M.mu (1, ⟨d * v * d⁻¹, hyp.conj_mem_W_of_mem_D hd hv⟩) : M.Eˣ) : M.E) :=
  hyp.coordFieldAut_eq_of_smul s M hm hQ0card hd hζ hznot (hyp.coordConjD_muW_smul M hd hv)

include hyp in
/-- **`μ` fixes the scalar of a `W`-element that `d` centralizes** — the book's `ζ^μ = ζ`,
which holds in §4 because `ζ ∈ C_W(P)` and `η ∈ P`.  It is what turns the substitution of
(3) into (4) into the book's (5). -/
theorem coordFieldAut_muW_eq_self (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) {d ζ : G} (hd : d ∈ hyp.D)
    (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) {v : G} (hv : v ∈ hyp.W)
    (hfix : d * v * d⁻¹ = v) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot ((M.mu (1, ⟨v, hv⟩) : M.Eˣ) : M.E)
      = ((M.mu (1, ⟨v, hv⟩) : M.Eˣ) : M.E) := by
  have hv' : (⟨d * v * d⁻¹, hyp.conj_mem_W_of_mem_D hd hv⟩ : ↥hyp.W) = ⟨v, hv⟩ :=
    Subtype.ext hfix
  rw [hyp.coordFieldAut_muW s M hm hQ0card hd hζ hznot hv, hv']

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
