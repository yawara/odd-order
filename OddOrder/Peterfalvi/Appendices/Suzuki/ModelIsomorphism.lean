/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CenterFieldExponent
import OddOrder.GroupTheory.CentralExtensionAutomorphisms
import OddOrder.GroupTheory.CentralElementaryExtension
import OddOrder.GroupTheory.RepresentationTheory.SemilinearBilinearLift
import OddOrder.Algebra.FrobeniusExponentPairs
import OddOrder.Algebra.QuadraticTraceCorrection

/-!
# Step (3) of the Ch. III §3 Proposition: `S ≅ S₁`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §3, p. 121, step (3) of the Proposition:

> Put `φ(x,y) = x y^q` (if `θ = 1`) and `φ(x,y) = λ₁ x y^σ + λ̄₁ x̄ ȳ^σ`
> otherwise.  One checks that with the operation of the statement `S₁` is a
> group and that `F ↪ S₁ ↠ E` is a central extension with quadratic map `χ`.
> By Appendix III Lemma 1(c) this extension is equivalent to `F → S → E`.

The book's `S₁` is the twisted product `E × F` with cocycle `φ`, i.e.
`Suzuki2Groups.BilinearTwistedProduct φ`, and the last sentence is
`GroupExtension.exists_mulEquiv_of_comp_squareMap_eq`.  So step (3) is the
assembly of

* the central extension `Z(Q) → Q → Q ⧸ Z(Q)` in the coordinates produced by
  steps (1) and (2) — `M.coord` on the quotient and the centre coordinate
  `ι : Additive Z(Q) ≃+ F` of `exists_center_coordinate_equiv`;
* the quadratic map `χ : E → F` of the extension, here obtained by transporting
  the descended squaring map (Appendix III Lemma 1(a)) along those coordinates;
* the model side, for *any* bilinear `φ` whose diagonal is `χ`.

The statement is given for an arbitrary such `φ` because that is how the book
uses it: it writes down an explicit `φ` and checks `φ(x,x) = χ(x)`.  The
canonical choice `φ = χ.toBilin basis` is recorded as
`exists_mulEquiv_quadraticExtension`, which is unconditional.

## Main results

* `Hypothesis.exists_actualKActor_mu_eq` — `K₁ = F^×`.
* `Hypothesis.centreQuadraticMap` — the quadratic map `χ : E → F` of the
  central extension, in the coordinates of steps (1)–(2).
* `Hypothesis.exists_mulEquiv_bilinearTwistedProduct` — for any bilinear lift `φ`
  of `χ`, an isomorphism `Q ≃* (E ×_φ F)` carrying the centre coordinate to the
  kernel coordinate and `M.coord` to the quotient coordinate.
* `Hypothesis.exists_mulEquiv_quadraticExtension` — the same with the canonical
  lift, so that the model exists unconditionally.
* `Hypothesis.exists_bilinear_lift_semilinear` /
  `Hypothesis.exists_bilinear_lift_normalized` — the book's cocycle, obtained from
  the pinned Lemma 2(c) expansion and then normalized.
* `Hypothesis.exists_mulEquiv_bookCocycle` — **step (3) in the book's form**:
  `S ≅ S₁` with a cocycle satisfying the Proposition's semilinearity and
  anisotropy, plus the diagonal scaling that step (4) needs.

The `K₁W₁`-action on the model is in `ModelAction.lean`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

variable {m : ℕ} (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)

/-! ## `K₁ = F^×`: the scalars exhaust the nonzero elements of `F` -/

include s in
/-- **`K₁ = F^×`** (Peterfalvi Part II, Ch. III §3, p. 120).  The scalars `μ(K)`
are *all* the nonzero elements of the subfield `F`.

`μ` is injective on `K` and lands in `F` (`QuotientFieldModel.mu_K_injective`,
`mu_K_frobFixed`), so its image has `|K| = |Z(Q)| − 1 = q − 1` elements inside the
`(q − 1)`-element set `F ∖ {0}`; equal finite cardinalities force equality.

Step (3) needs this to turn the `K`-indexed scaling law of `χ` into one indexed by
all of `F^×`, which is what the Lemma 2(c) pinning consumes. -/
theorem exists_actualKActor_mu_eq (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {a : M.E} (ha : a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (ha0 : a ≠ 0) :
    ∃ k : ↥hyp.actualKActor, ((M.mu (k, 1) : M.Eˣ) : M.E) = a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥hyp.actualKActor → M.E := fun k => ((M.mu (k, 1) : M.Eˣ) : M.E) with hf
  have hinj : Function.Injective f := fun k k' h => M.mu_K_injective (Units.ext h)
  have hsub : Set.range f ⊆
      ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k),
      (M.mu (k, 1) : M.Eˣ).ne_zero⟩
  have hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
    rw [s.cardActorCenter, s.centerEqQ0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv, hQ0card]
  have hrange : (Set.range f).ncard = 2 ^ m - 1 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, hKcard]
  have hT : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}).ncard
      = 2 ^ m - 1 := by
    have hcardF : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E)).ncard
        = 2 ^ m := by
      rw [← Nat.card_coe_set_eq]
      exact OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm
    rw [Set.ncard_sdiff_singleton_of_mem
      (OddOrder.FiniteField.frobFixedSubfield M.E 2 m).zero_mem, hcardF]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hrange, hT]) (Set.toFinite _)
  have hmem : a ∈ Set.range f := by
    rw [heq]
    exact ⟨ha, ha0⟩
  exact hmem

/-! ## The quadratic map of the extension, in the coordinates of steps (1)–(2) -/

open scoped Classical in
/-- **The quadratic map `χ : E → F` of the central extension `F → S → E`**
(Peterfalvi Part II, Ch. III §3, p. 121, step (3)), for a given centre
coordinate `ι`.

Squaring descends to `Q ⧸ Z(Q) → Z(Q)` as a genuine `𝔽₂`-quadratic map
(Appendix III Lemma 1(a), `Suzuki2Groups.centralSquareQuadraticMap`);
transporting it along `M.coord` on the quotient and along `ι` on the centre puts
it on `E` with values in the subfield `F`.

Unlike `exists_quadraticMap_of_lemmaFiveSetup`, which lands in `E` and is what
the Lemma 2(c) expansion of step (2) needs, this version lands in `F` — the
kernel of the model extension `S₁`. -/
noncomputable def centreQuadraticMap
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) :
    QuadraticMap (ZMod 2) M.E ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
  letI hW : IsElementaryAbelian 2 ↥(Subgroup.center hyp.Q) :=
    hyp.isElementaryAbelian_center_of_lemmaFiveSetup s
  letI hV : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    s.isplit.split.quotientEA
  letI : IsMulCommutative (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    IsMulCommutative.of_comm hV.comm
  letI : IsMulCommutative ↥(Subgroup.center hyp.Q) := IsMulCommutative.of_comm hW.comm
  letI : Module (ZMod 2) (Additive (↥hyp.Q ⧸ Subgroup.center hyp.Q)) := hV.zmodModule
  letI : Module (ZMod 2) (Additive ↥(Subgroup.center hyp.Q)) := hW.zmodModule
  let fL : M.E →ₗ[ZMod 2] Additive (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    { toFun := M.coord.symm
      map_add' := M.coord.symm.map_add
      map_smul' := fun a x => ZMod.map_smul M.coord.symm a x }
  let gL : Additive ↥(Subgroup.center hyp.Q) →ₗ[ZMod 2]
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
    { toFun := ι
      map_add' := ι.map_add
      map_smul' := fun a x => ZMod.map_smul ι a x }
  gL.compQuadraticMap
    ((Suzuki2Groups.centralSquareQuadraticMap
      (le_refl (Subgroup.center ↥hyp.Q)) hW hV).comp fL)

/-- The defining formula for `centreQuadraticMap`: it is the descended square map
read in the two coordinates. -/
theorem centreQuadraticMap_apply
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (x : M.E) :
    hyp.centreQuadraticMap s M ι x =
      ι (Additive.ofMul (Suzuki2Groups.centralSquare
        (le_refl (Subgroup.center ↥hyp.Q))
        (hyp.isElementaryAbelian_center_of_lemmaFiveSetup s)
        s.isplit.split.quotientEA (M.coord.symm x).toMul)) :=
  rfl

/-- **The square map of `Q` in the coordinates of steps (1)–(2)**: reading a
square `e²` through the centre coordinate `ι` gives `χ` applied to the class of
`e`.  This is the hypothesis `hsqS` of Appendix III Lemma 1(c). -/
theorem toMul_symm_centreQuadraticMap
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (e : ↥hyp.Q) :
    ((Additive.toMul (ι.symm (hyp.centreQuadraticMap s M ι
        (M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e))))) :
      ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) = e ^ 2 := by
  rw [hyp.centreQuadraticMap_apply s M ι, M.coord.symm_apply_apply]
  rw [ι.symm_apply_apply]
  rfl

/-- `χ` is **anisotropic** (`χ x = 0 → x = 0`): an element of `Q` whose square is
central-trivial is itself central (`LemmaFiveSetup.invMem`). -/
theorem centreQuadraticMap_anisotropic
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (x : M.E) (hx : hyp.centreQuadraticMap s M ι x = 0) : x = 0 := by
  classical
  rw [hyp.centreQuadraticMap_apply s M ι] at hx
  have hz : Suzuki2Groups.centralSquare (le_refl (Subgroup.center ↥hyp.Q))
      (hyp.isElementaryAbelian_center_of_lemmaFiveSetup s)
      s.isplit.split.quotientEA (M.coord.symm x).toMul = 1 := by
    have h0 : ι (Additive.ofMul (1 : ↥(Subgroup.center hyp.Q))) = 0 := ι.map_zero
    exact Additive.ofMul.injective (ι.injective (hx.trans h0.symm))
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (M.coord.symm x).toMul
  have hsq : (y : ↥hyp.Q) ^ 2 = 1 := by
    rw [← hy, Suzuki2Groups.centralSquare_mk] at hz
    exact congrArg (Subtype.val (p := fun z => z ∈ Subgroup.center ↥hyp.Q)) hz
  have hone : (M.coord.symm x).toMul = 1 := by
    rw [← hy]
    exact (QuotientGroup.eq_one_iff y).mpr (s.invMem y hsq)
  have hzero : M.coord.symm x = 0 := Additive.toMul.injective hone
  have := congrArg M.coord hzero
  rwa [M.coord.apply_symm_apply, map_zero] at this

include s in
/-- **The `K`-scaling law of `χ`, for a given centre coordinate `ι`.**

`exists_quadraticMap_of_lemmaFiveSetup` proves the same law, but for the
coordinate it chooses internally; step (3) needs it for the *same* `ι` that
`centreQuadraticMap` is built from, so that the `E`-valued and `F`-valued forms of
`χ` share one coordinate.

The content is the `K`-equivariance of the descended square map
(`centralSquare_quotientKHom`: conjugation commutes with squaring) transported
along the two coordinates. -/
theorem centreQuadraticMap_smul
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (k : ↥hyp.actualKActor) (x : M.E) :
    ((hyp.centreQuadraticMap s M ι (((M.mu (k, 1) : M.Eˣ) : M.E) * x) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
        ((hyp.centreQuadraticMap s M ι x :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
  classical
  rw [hyp.centreQuadraticMap_apply s M ι, hyp.centreQuadraticMap_apply s M ι]
  have hact : M.coord.symm (((M.mu (k, 1) : M.Eˣ) : M.E) * x)
      = Additive.ofMul (hyp.quotientKHom k (M.coord.symm x).toMul) := by
    refine M.coord.injective ?_
    rw [M.coord.apply_symm_apply]
    have h := M.coord_act (k, 1) (M.coord.symm x).toMul
    have hkw : hyp.quotientKWHom (k, 1) = hyp.quotientKHom k := by
      rw [hyp.quotientKWHom_apply, map_one, mul_one]
    rw [hkw] at h
    rw [h]
    congr 1
    exact (M.coord.apply_symm_apply x).symm
  rw [hact]
  simp only [toMul_ofMul]
  rw [hyp.centralSquare_quotientKHom]
  exact hequiv k _

include s in
/-- **The scaling law of `χ` indexed by all of `F^×`**, in the form the Lemma 2(c)
pinning consumes: for every nonzero `a ∈ F` there is a `b` with
`χ (a x) = b χ (x)`.

The `b` is left existential on purpose — the pinning only ever *compares* two
surviving pairs through it, so its explicit value `a^d` is never needed. -/
theorem exists_scaling_of_mem_frobFixed (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (χ : QuadraticMap (ZMod 2) M.E M.E) (d : ℤ)
    (hscale : ∀ (k : ↥hyp.actualKActor) (x : M.E),
      χ (((M.mu (k, 1) : M.Eˣ) : M.E) * x)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) * χ x)
    {a : M.E} (ha : a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (ha0 : a ≠ 0) :
    ∃ b : M.E, ∀ x : M.E, χ (a * x) = b * χ x := by
  obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq s M hm hQ0card ha ha0
  exact ⟨((M.mu (k, 1) ^ d : M.Eˣ) : M.E), fun x => by rw [← hk]; exact hscale k x⟩

include s in
/-- **`W` fixes `χ`** (Peterfalvi Part II, Ch. III §3): `w` acts trivially on
`Q₀ = Z(Q)`, so the descended square map is `W`-invariant.  Together with
`centreQuadraticMap_smul` this gives a scaling relation for every element of
`K₁W₁`, which is what makes the whole of `K₁W₁` act on the model `S₁`. -/
theorem centreQuadraticMap_W_invariant
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (v : ↥hyp.W) (x : M.E) :
    hyp.centreQuadraticMap s M ι (((M.mu (1, v) : M.Eˣ) : M.E) * x)
      = hyp.centreQuadraticMap s M ι x := by
  classical
  rw [hyp.centreQuadraticMap_apply s M ι, hyp.centreQuadraticMap_apply s M ι]
  have hact : M.coord.symm (((M.mu (1, v) : M.Eˣ) : M.E) * x)
      = Additive.ofMul (hyp.quotientWHom v (M.coord.symm x).toMul) := by
    refine M.coord.injective ?_
    rw [M.coord.apply_symm_apply]
    have h := M.coord_act (1, v) (M.coord.symm x).toMul
    have hkw : hyp.quotientKWHom (1, v) = hyp.quotientWHom v := by
      rw [hyp.quotientKWHom_apply, map_one, one_mul]
    rw [hkw] at h
    rw [h]
    congr 1
    exact (M.coord.apply_symm_apply x).symm
  rw [hact]
  simp only [toMul_ofMul]
  rw [hyp.centralSquare_quotientWHom s]

include s in
/-- **The scaling constant of `χ` for the whole of `K W`**: it is `μ(k,1)^d`, and in
particular **does not depend on the `W`-component**, because `W` fixes `χ`.

This is what makes the scaling constants into a homomorphism on `K × W`, hence the
action of `K₁W₁` on the model `S₁` into a homomorphism (Peterfalvi Part II,
Ch. III §3, p. 121, step (4)). -/
theorem centreQuadraticMap_smul_KW
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (kv : ↥hyp.actualKActor × ↥hyp.W) (x : M.E) :
    ((hyp.centreQuadraticMap s M ι (((M.mu kv : M.Eˣ) : M.E) * x) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) *
        ((hyp.centreQuadraticMap s M ι x :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
  have hsplit : M.mu kv = M.mu (kv.1, 1) * M.mu (1, kv.2) := by
    rw [← map_mul]
    congr 1
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  rw [hsplit, Units.val_mul, mul_assoc,
    hyp.centreQuadraticMap_smul s M ι d hequiv kv.1,
    hyp.centreQuadraticMap_W_invariant s M ι kv.2]

include s in
/-- **Step (5) of the Ch. III §3 Proposition** (Peterfalvi Part II, p. 121):
the isomorphism can be normalized so that a chosen nonidentity central element goes
to `(0, 1)`.

> `K` is transitive on `Q₀^#`, so composing with an inner automorphism of
> `S₁ ⋊ K₁W₁` sends `s` to `(0,1)`.

Here the centre coordinate `ι` is a free parameter rather than a fixed
identification, so the normalization is simply a rescaling: replacing `ι` by
`ι(s)⁻¹ · ι` sends `s` to `1`.  The rescaling is by a constant, so it preserves the
`K`-scaling law — and hence every property of `χ` and of the cocycle that depends
on it.  Neither the transitivity of `K` on `Q₀^#` nor an inner automorphism is
needed. -/
theorem exists_center_coordinate_normalized (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (x₀ : ↥(Subgroup.center hyp.Q)) (hx₀ : x₀ ≠ 1) :
    ∃ (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ),
      ι (Additive.ofMul x₀) = 1 ∧
      ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
        ((ι (Additive.ofMul (hyp.centerKHom k z)) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
            ((ι (Additive.ofMul z) :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
  classical
  obtain ⟨ι, d, hequiv⟩ := hyp.exists_center_coordinate_equiv hm hQ0card s M
  set c := ι (Additive.ofMul x₀) with hc
  have hc0 : c ≠ 0 := by
    intro h
    refine hx₀ (Additive.ofMul.injective (ι.injective ?_))
    rw [← hc, h]
    exact (map_zero ι).symm
  -- rescale the coordinate by `c⁻¹`
  refine ⟨ι.trans (AddEquiv.mk' (Equiv.mulLeft₀ c⁻¹ (inv_ne_zero hc0))
    (mul_add c⁻¹)), d, ?_, fun k z => ?_⟩
  · change c⁻¹ * ι (Additive.ofMul x₀) = 1
    rw [← hc]
    exact inv_mul_cancel₀ hc0
  · change ((c⁻¹ * ι (Additive.ofMul (hyp.centerKHom k z)) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) = _
    change _ = _ * ((c⁻¹ * ι (Additive.ofMul z) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
    rw [Submonoid.coe_mul, Submonoid.coe_mul, hequiv k z]
    ring

/-! ## The book's cocycle: a semilinear bilinear lift of `χ` -/

/-- The `E`-valued form of `χ`, built from the *same* centre coordinate `ι` as the
`F`-valued `centreQuadraticMap`.  The Lemma 2(c) expansion lives on `E`, so the
pinning machinery needs this form; the model `S₁` needs the `F`-valued one. -/
noncomputable def centreQuadraticMapE
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) :
    QuadraticMap (ZMod 2) M.E M.E :=
  (((OddOrder.FiniteField.frobFixedSubfield M.E 2 m).subtype :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) →+* M.E).toAddMonoidHom.toZModLinearMap
    2).compQuadraticMap (hyp.centreQuadraticMap s M ι)

@[simp] theorem centreQuadraticMapE_apply
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (x : M.E) :
    hyp.centreQuadraticMapE s M ι x =
      ((hyp.centreQuadraticMap s M ι x :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) :=
  rfl

include s in
/-- **The book's cocycle `φ`, before normalization** (Peterfalvi Part II, Ch. III §3,
p. 121, step (3)).

Chaining the pinned Lemma 2(c) expansion (`exists_scaling_pinned_expansion`), the
comparison of surviving pairs on `F` (`restrict_pair_eq_of_mul_eq_on_frobFixed`)
and the reordered lift (`exists_bilinear_lift_of_pinned_restriction`): `χ` has a
bilinear lift `φ` obeying `φ (a x) (b y) = α(a) β(b) φ(x, y)` for `a, b ∈ F`.

The book gets `α = 1` by choosing coordinates so that `d = 1 + 2^t`; here `α` and
`β` come out of the expansion and the normalization `α = 1` is applied afterwards,
by replacing `ι` with `α⁻¹ ∘ ι`. -/
theorem exists_bilinear_lift_semilinear (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) :
    ∃ (φ : LinearMap.BilinMap (ZMod 2) M.E M.E) (α β : M.E ≃ₐ[ZMod 2] M.E),
      (∀ x : M.E, φ x x = hyp.centreQuadraticMapE s M ι x) ∧
      (∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
        ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
          ∀ x y : M.E, φ (a * x) (b * y) = α a * β b * φ x y) ∧
      ∀ a b : M.E,
        (∀ x : M.E, hyp.centreQuadraticMapE s M ι (a * x)
          = b * hyp.centreQuadraticMapE s M ι x) →
        ∀ x y : M.E, φ (a * x) (a * y) = b * φ x y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype (M.E ≃ₐ[ZMod 2] M.E) := Fintype.ofFinite _
  have hcardE : Nat.card M.E = 2 ^ (m * 2) := by rw [M.card, ← pow_mul]
  have hN : m * 2 ≠ 0 := by positivity
  -- the pinned expansion of the `E`-valued `χ`
  obtain ⟨c, hexp, hpin⟩ :=
    OddOrder.RepresentationTheory.exists_scaling_pinned_expansion M.E
      (hyp.centreQuadraticMapE s M ι)
  -- the scaling law, for every nonzero `a ∈ F`
  have hscaleE : ∀ (k : ↥hyp.actualKActor) (x : M.E),
      hyp.centreQuadraticMapE s M ι (((M.mu (k, 1) : M.Eˣ) : M.E) * x)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) * hyp.centreQuadraticMapE s M ι x :=
    fun k x => hyp.centreQuadraticMap_smul s M ι d hequiv k x
  -- some pair survives, else `χ` would be zero
  have hsurv : ∃ στ : (M.E ≃ₐ[ZMod 2] M.E) × (M.E ≃ₐ[ZMod 2] M.E), c στ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := exists_ne (0 : M.E)
    refine hx (hyp.centreQuadraticMap_anisotropic s M ι x ?_)
    refine Subtype.ext ?_
    have := hexp x
    rw [Finset.sum_congr rfl (fun στ _ => by rw [hcon στ, zero_mul]), Finset.sum_const_zero]
      at this
    exact this
  obtain ⟨στ₀, hστ₀⟩ := hsurv
  -- surviving pairs induce the same product map on `F`
  have hsame : ∀ στ : (M.E ≃ₐ[ZMod 2] M.E) × (M.E ≃ₐ[ZMod 2] M.E), c στ ≠ 0 →
      ∀ a : M.E, a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m →
        στ.1 a * στ.2 a = στ₀.1 a * στ₀.2 a := by
    intro στ hne a ha
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    · obtain ⟨b, hb⟩ :=
        hyp.exists_scaling_of_mem_frobFixed s M hm hQ0card _ d hscaleE ha ha0
      rw [hpin a b hb στ hne, hpin a b hb στ₀ hστ₀]
  -- every automorphism of `E` is a Frobenius power
  have hpow : ∀ ρ : M.E ≃ₐ[ZMod 2] M.E, ∃ i : ℕ, ∀ x : M.E, ρ x = x ^ 2 ^ i := by
    intro ρ
    obtain ⟨i, hi⟩ := OddOrder.FiniteField.exists_pow_eq_of_ringAut
      (K := M.E) (p := 2) (n := m * 2) hcardE hN
      ((OddOrder.RepresentationTheory.ringAutMulEquivAlgAut M.E 2).symm ρ)
    exact ⟨i, fun x => hi x⟩
  -- hence the restriction of every surviving pair to `F` matches `στ₀`
  have hres : ∀ στ : (M.E ≃ₐ[ZMod 2] M.E) × (M.E ≃ₐ[ZMod 2] M.E), c στ ≠ 0 →
      (∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
          στ.1 a = στ₀.1 a ∧ στ.2 a = στ₀.2 a) ∨
        (∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
          στ.1 a = στ₀.2 a ∧ στ.2 a = στ₀.1 a) := by
    intro στ hne
    obtain ⟨i, hi⟩ := hpow στ.1
    obtain ⟨j, hj⟩ := hpow στ.2
    obtain ⟨i', hi'⟩ := hpow στ₀.1
    obtain ⟨j', hj'⟩ := hpow στ₀.2
    have hmul : ∀ a : M.E, a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m →
        a ^ 2 ^ i * a ^ 2 ^ j = a ^ 2 ^ i' * a ^ 2 ^ j' := by
      intro a ha
      rw [← hi, ← hj, ← hi', ← hj']
      exact hsame στ hne a ha
    rcases OddOrder.FiniteField.restrict_pair_eq_of_mul_eq_on_frobFixed
      (E := M.E) hm M.card i j i' j' hmul with h | h
    · exact Or.inl fun a ha => by
        rw [hi, hj, hi', hj']
        exact ⟨(h a ha).1, (h a ha).2⟩
    · exact Or.inr fun a ha => by
        rw [hi, hj, hi', hj']
        exact ⟨(h a ha).1, (h a ha).2⟩
  obtain ⟨φ, hdiag, hsemi, hdiagscale⟩ :=
    OddOrder.RepresentationTheory.exists_bilinear_lift_of_pinned_restriction M.E
      (hyp.centreQuadraticMapE s M ι) c hexp
      ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E)) στ₀.1 στ₀.2 hres
  exact ⟨φ, στ₀.1, στ₀.2, hdiag, hsemi,
    fun a b hb x y => hdiagscale a b (fun στ hne => hpin a b hb στ hne) x y⟩

/-- Moving the centre coordinate by an automorphism of `E` moves `χ` the same way:
`centreQuadraticMap` is `ι` post-composed with the descended square map. -/
theorem centreQuadraticMap_trans
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (j : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (x : M.E) :
    hyp.centreQuadraticMap s M (ι.trans j) x = j (hyp.centreQuadraticMap s M ι x) :=
  rfl

include s in
/-- **The book's cocycle `φ`, normalized** (Peterfalvi Part II, Ch. III §3, p. 121,
step (3)): `φ (a x) (b y) = a · θ(b) · φ(x, y)` for `a, b ∈ F`, which with
`θ|_F` the book's `θ` is exactly the Proposition's requirement on the cocycle.

`exists_bilinear_lift_semilinear` produces the law with a general `α` in the first
slot; post-composing everything with `α⁻¹` normalizes `α` to the identity.  On the
quadratic map that is the substitution `ι ↦ α⁻¹ ∘ ι` of the centre coordinate —
the intrinsic version of the book's "choose coordinates so that `d = 1 + 2^t`". -/
theorem exists_bilinear_lift_normalized (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) :
    ∃ (ι' : Additive ↥(Subgroup.center hyp.Q) ≃+
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
      (φ : LinearMap.BilinMap (ZMod 2) M.E M.E) (θ : M.E ≃ₐ[ZMod 2] M.E),
      (∀ x : M.E, φ x x = hyp.centreQuadraticMapE s M ι' x) ∧
      (∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
        ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
          ∀ x y : M.E, φ (a * x) (b * y) = a * θ b * φ x y) ∧
      (∀ z : Additive ↥(Subgroup.center hyp.Q), ι z = 1 → ι' z = 1) ∧
      (∃ d' : ℤ, ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
        ((ι' (Additive.ofMul (hyp.centerKHom k z)) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (k, 1) ^ d' : M.Eˣ) : M.E) *
            ((ι' (Additive.ofMul z) :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) ∧
      ∀ a b : M.E,
        (∀ x : M.E, hyp.centreQuadraticMapE s M ι' (a * x)
          = b * hyp.centreQuadraticMapE s M ι' x) →
        ∀ x y : M.E, φ (a * x) (a * y) = b * φ x y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₀, α, β, hdiag, hsemi, hdiagscale⟩ :=
    hyp.exists_bilinear_lift_semilinear s M hm hQ0card ι d hequiv
  have hχ' : ∀ x : M.E,
      hyp.centreQuadraticMapE s M
          (ι.trans (OddOrder.FiniteField.frobFixedRestrict (m := m) α.symm.toRingEquiv)) x
        = α.symm (hyp.centreQuadraticMapE s M ι x) := by
    intro x
    rw [hyp.centreQuadraticMapE_apply, hyp.centreQuadraticMapE_apply,
      hyp.centreQuadraticMap_trans s M ι]
    rfl
  refine ⟨ι.trans (OddOrder.FiniteField.frobFixedRestrict (m := m) α.symm.toRingEquiv),
    φ₀.compr₂ α.symm.toLinearMap, β.trans α.symm, fun x => ?_, fun a ha b hb x y => ?_,
    fun z hz => ?_, ?_, fun a b hb x y => ?_⟩
  · -- the diagonal, read through the moved coordinate
    simp only [LinearMap.compr₂_apply, AlgEquiv.toLinearMap_apply]
    rw [hdiag x, hyp.centreQuadraticMapE_apply, hyp.centreQuadraticMapE_apply,
      hyp.centreQuadraticMap_trans s M ι]
    rfl
  · -- `α⁻¹ (α a · β b · φ₀ x y) = a · (α⁻¹ β) b · α⁻¹ (φ₀ x y)`
    change α.symm (φ₀ (a * x) (b * y)) = _
    rw [hsemi a ha b hb x y, map_mul, map_mul, α.symm_apply_apply]
    rfl
  · -- the normalization `ι z = 1` survives: `α⁻¹` is a ring automorphism
    refine Subtype.ext ?_
    change α.symm ((ι z : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) = _
    rw [hz]
    change α.symm (1 : M.E) = (1 : M.E)
    exact map_one α.symm
  · -- the `K`-scaling for the moved coordinate: `α⁻¹` is a Frobenius power, so the
    -- twisted constant is again a power of `μ(k,1)`
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcardE : Nat.card M.E = 2 ^ (m * 2) := by rw [M.card, ← pow_mul]
    have hN : m * 2 ≠ 0 := by positivity
    obtain ⟨j, hj0⟩ := OddOrder.FiniteField.exists_pow_eq_of_ringAut
      (K := M.E) (p := 2) (n := m * 2) hcardE hN
      ((OddOrder.RepresentationTheory.ringAutMulEquivAlgAut M.E 2).symm α.symm)
    have hj : ∀ x : M.E, α.symm x = x ^ 2 ^ j := fun x => hj0 x
    refine ⟨d * 2 ^ j, fun k z => ?_⟩
    change α.symm ((ι (Additive.ofMul (hyp.centerKHom k z)) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) = _
    change _ = _ * α.symm ((ι (Additive.ofMul z) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
    rw [hequiv k z, map_mul α.symm, hj, hj]
    congr 1
    rw [← Units.val_pow_eq_pow_val]
    congr 1
    rw [← zpow_natCast (M.mu (k, 1) ^ d) (2 ^ j), ← zpow_mul]
    norm_cast
  · -- the diagonal scaling, with the constant read through `α`
    have hsc : ∀ x : M.E, hyp.centreQuadraticMapE s M ι (a * x)
        = α b * hyp.centreQuadraticMapE s M ι x := by
      intro x
      have := congrArg (fun z : M.E => α z) (hb x)
      simp only [hχ'] at this
      rwa [α.apply_symm_apply, map_mul α, α.apply_symm_apply] at this
    change α.symm (φ₀ (a * x) (a * y)) = _
    rw [hdiagscale a (α b) hsc x y, map_mul α.symm, α.symm_apply_apply]
    rfl

/-! ## Step (3): the isomorphism with the model -/

open scoped Classical in
/-- **Step (3) of the Ch. III §3 Proposition** (Peterfalvi Part II, p. 121):
`S ≅ S₁`.

The book's `S₁` is the set of pairs `(x, y) ∈ E × F` with the operation
`(x,z)(y,u) = (x+y, z+u+φ(x,y))`, i.e. `BilinearTwistedProduct φ`, and the
proposition's requirement on `φ` — that `F ↪ S₁ ↠ E` be a central extension
whose quadratic map is `χ` — is exactly `φ(x,x) = χ(x)`.  Appendix III Lemma 1(c)
(`GroupExtension.exists_mulEquiv_of_comp_squareMap_eq`) then makes the two
extensions equivalent.

The isomorphism is compatible with both coordinates: it carries the centre of `Q`
onto the kernel coordinate by `ι`, and induces `M.coord` on the quotient. -/
theorem exists_mulEquiv_bilinearTwistedProduct
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hφ : ∀ x : M.E, φ x x = hyp.centreQuadraticMap s M ι x) :
    ∃ Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ,
      (∀ z : ↥(Subgroup.center hyp.Q),
        Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩) ∧
      ∀ e : ↥hyp.Q, (Φ e).quotient =
        M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)) := by
  classical
  -- The extension `Z(Q) → Q → Q ⧸ Z(Q)` in the coordinates of steps (1)–(2),
  -- compared with the model `E ×_φ F` by Appendix III Lemma 1(c).
  obtain ⟨Φ, hinl, hquot⟩ :=
    GroupExtension.exists_mulEquiv_of_comp_squareMap_eq
      (GroupExtension.ofNormalSubgroupCoordinates (Subgroup.center hyp.Q)
        (AddEquiv.toMultiplicativeLeft ι.symm) (AddEquiv.toMultiplicativeRight M.coord))
      (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ)
      (le_of_eq (GroupExtension.ofNormalSubgroupCoordinates_range_inl _ _ _))
      Suzuki2Groups.BilinearTwistedProduct.centralEmbedding_range_le_center
      ⇑(hyp.centreQuadraticMap s M ι) (fun x => φ x x)
      (Module.finBasis (ZMod 2) M.E)
      (fun e => (hyp.toMul_symm_centreQuadraticMap s M ι e).symm)
      (fun e => Suzuki2Groups.BilinearTwistedProduct.sq_eq_inl_diag φ e)
      (AddEquiv.refl M.E) (AddEquiv.refl _) (fun v => (hφ v).symm)
  refine ⟨Φ, fun z => ?_, fun e => ?_⟩
  · have hz : (GroupExtension.ofNormalSubgroupCoordinates (Subgroup.center hyp.Q)
        (AddEquiv.toMultiplicativeLeft ι.symm)
        (AddEquiv.toMultiplicativeRight M.coord)).inl
        (Multiplicative.ofAdd (ι (Additive.ofMul z))) = (z : ↥hyp.Q) := by
      change ((Additive.toMul (ι.symm (ι (Additive.ofMul z))) :
        ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) = _
      rw [ι.symm_apply_apply]
      rfl
    calc Φ (z : ↥hyp.Q)
        = Φ ((GroupExtension.ofNormalSubgroupCoordinates (Subgroup.center hyp.Q)
              (AddEquiv.toMultiplicativeLeft ι.symm)
              (AddEquiv.toMultiplicativeRight M.coord)).inl
              (Multiplicative.ofAdd (ι (Additive.ofMul z)))) := congrArg Φ hz.symm
      _ = _ := hinl (ι (Additive.ofMul z))
  · exact hquot e

include s in
/-- **Step (3) of the Ch. III §3 Proposition, in the book's form** (Peterfalvi
Part II, p. 120–121).

`S ≅ S₁ = E ×_φ F` where the cocycle `φ : E × E → F` is bi-additive and satisfies

* `φ (a x) (b y) = a · b^θ · φ (x, y)` for `a, b ∈ F` — the Proposition's
  semilinearity, with `θ` the automorphism produced by the Lemma 2(c) expansion;
* `x ≠ 0 ⟹ φ (x, x) ≠ 0` — the Proposition's anisotropy, which is the anisotropy
  of `χ` since `φ` lifts it.

The isomorphism carries `Z(Q)` onto the kernel coordinate by `ι'` and induces
`M.coord` on the quotient.

The chain is: pinned Lemma 2(c) expansion → all surviving pairs restrict to `F` the
same way → reordered bilinear lift → normalize the first automorphism to the
identity → correct the values into `F` by the relative trace. -/
theorem exists_mulEquiv_bookCocycle (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) :
    ∃ (ι' : Additive ↥(Subgroup.center hyp.Q) ≃+
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
      (φ : LinearMap.BilinMap (ZMod 2) M.E
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
      (θ : M.E ≃ₐ[ZMod 2] M.E)
      (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ),
      (∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
        ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
          ∀ x y : M.E,
            ((φ (a * x) (b * y) :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
              = a * θ b *
                ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) ∧
      (∀ x : M.E, x ≠ 0 → φ x x ≠ 0) ∧
      (∀ z : Additive ↥(Subgroup.center hyp.Q), ι z = 1 → ι' z = 1) ∧
      (∃ d' : ℤ, ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
        ((ι' (Additive.ofMul (hyp.centerKHom k z)) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (k, 1) ^ d' : M.Eˣ) : M.E) *
            ((ι' (Additive.ofMul z) :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) ∧
      (∀ a b : M.E,
        (∀ x : M.E,
          ((hyp.centreQuadraticMap s M ι' (a * x) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
            = b * ((hyp.centreQuadraticMap s M ι' x :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) →
        ∀ x y : M.E,
          ((φ (a * x) (a * y) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
            = b * ((φ x y :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) ∧
      (∀ z : ↥(Subgroup.center hyp.Q),
        Φ (z : ↥hyp.Q) = ⟨0, ι' (Additive.ofMul z)⟩) ∧
      ∀ e : ↥hyp.Q, (Φ e).quotient =
        M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι', φ₀, θ, hdiag, hsemi, hone, hequiv', hdiagscale⟩ :=
    hyp.exists_bilinear_lift_normalized s M hm hQ0card ι d hequiv
  -- the diagonal already lies in `F`
  have hdiagF : ∀ x : M.E,
      φ₀ x x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
    intro x
    rw [hdiag x, hyp.centreQuadraticMapE_apply]
    exact (hyp.centreQuadraticMap s M ι' x).2
  -- correct the off-diagonal values into `F`
  obtain ⟨u, ψ, hform, hval, hdiagψ⟩ :=
    OddOrder.FiniteField.exists_bilinear_frobFixed_of_diag (E := M.E) m hm M.card φ₀ hdiagF
  have hdiagφ : ∀ x : M.E,
      OddOrder.FiniteField.bilinCodRestrict m ψ hval x x
        = hyp.centreQuadraticMap s M ι' x := by
    intro x
    refine Subtype.ext ?_
    rw [OddOrder.FiniteField.bilinCodRestrict_apply, hdiagψ x, hdiag x]
    rfl
  obtain ⟨Φ, hker, hquot⟩ :=
    hyp.exists_mulEquiv_bilinearTwistedProduct s M ι' _ hdiagφ
  refine ⟨ι', OddOrder.FiniteField.bilinCodRestrict m ψ hval, θ, Φ, ?_, ?_, hone,
    hequiv', ?_, hker, hquot⟩
  · -- the semilinearity survives the correction, since `a · θ b` lies in `F`
    intro a ha b hb x y
    rw [OddOrder.FiniteField.bilinCodRestrict_apply,
      OddOrder.FiniteField.bilinCodRestrict_apply, hform, hform, hsemi a ha b hb x y]
    have hab : a * θ b ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
      Subfield.mul_mem _ ha
        (OddOrder.FiniteField.map_mem_frobFixedSubfield θ.toRingEquiv hb)
    rw [OddOrder.FiniteField.frobTrace_mul_of_mem m hab]
    ring
  · -- anisotropy, inherited from `χ`
    intro x hx h0
    refine hx (hyp.centreQuadraticMap_anisotropic s M ι' x ?_)
    refine Subtype.ext ?_
    have := congrArg (fun z : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) => (z : M.E)) h0
    rw [OddOrder.FiniteField.bilinCodRestrict_apply, hdiagψ x, hdiag x] at this
    exact this
  · -- the *diagonal* scaling, which is what makes the `K₁W₁`-action an automorphism
    intro a b hb x y
    -- the scaling constant lies in `F`, since `χ` is `F`-valued and anisotropic
    have hbF : b ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
      obtain ⟨x₀, hx₀⟩ := exists_ne (0 : M.E)
      have hval0 : ((hyp.centreQuadraticMap s M ι' x₀ :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) ≠ 0 := fun h =>
        hx₀ (hyp.centreQuadraticMap_anisotropic s M ι' x₀ (Subtype.ext h))
      have hbeq : b = ((hyp.centreQuadraticMap s M ι' (a * x₀) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) *
          (((hyp.centreQuadraticMap s M ι' x₀ :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))⁻¹ := by
        rw [hb x₀, mul_assoc, mul_inv_cancel₀ hval0, mul_one]
      rw [hbeq]
      exact Subfield.mul_mem _ (hyp.centreQuadraticMap s M ι' (a * x₀)).2
        (Subfield.inv_mem _ (hyp.centreQuadraticMap s M ι' x₀).2)
    rw [OddOrder.FiniteField.bilinCodRestrict_apply,
      OddOrder.FiniteField.bilinCodRestrict_apply, hform, hform,
      hdiagscale a b hb x y, OddOrder.FiniteField.frobTrace_mul_of_mem m hbF]
    ring

open scoped Classical in
/-- **The model `S₁` exists**: taking the canonical bilinear lift of `χ` supplied
by a basis (Appendix III Lemma 1(b)) gives an unconditional form of step (3).

The book's explicit cocycle `φ(x,y) = λ₁ x y^σ + λ̄₁ x̄ ȳ^σ` is a different lift of
the same `χ`; `exists_mulEquiv_bilinearTwistedProduct` covers it once that `φ` is
written down. -/
theorem exists_mulEquiv_quadraticExtension (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) :
    ∃ (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
      (Φ : ↥hyp.Q ≃* Suzuki2Groups.QuadraticExtension
        (hyp.centreQuadraticMap s M ι) (Module.finBasis (ZMod 2) M.E)),
      (∀ x : M.E, hyp.centreQuadraticMap s M ι x = 0 → x = 0) ∧
      (∀ z : ↥(Subgroup.center hyp.Q),
        Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩) ∧
      ∀ e : ↥hyp.Q, (Φ e).quotient =
        M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)) := by
  classical
  obtain ⟨ι, _d, _hequiv⟩ := hyp.exists_center_coordinate_equiv hm hQ0card s M
  obtain ⟨Φ, hker, hquot⟩ :=
    hyp.exists_mulEquiv_bilinearTwistedProduct s M ι
      ((hyp.centreQuadraticMap s M ι).toBilin (Module.finBasis (ZMod 2) M.E))
      (fun x => Suzuki2Groups.QuadraticExtension.toBilin_self _ _ x)
  exact ⟨ι, Φ, hyp.centreQuadraticMap_anisotropic s M ι, hker, hquot⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
