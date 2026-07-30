/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CenterFieldExponent
import OddOrder.GroupTheory.CentralExtensionAutomorphisms
import OddOrder.GroupTheory.CentralElementaryExtension

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

* `Hypothesis.centreQuadraticMap` — the quadratic map `χ : E → F` of the
  central extension, in the coordinates of steps (1)–(2).
* `Hypothesis.exists_mulEquiv_bilinearTwistedProduct` — **step (3)**: for any
  bilinear lift `φ` of `χ`, an isomorphism `Q ≃* (E ×_φ F)` carrying the centre
  coordinate to the kernel coordinate and `M.coord` to the quotient coordinate.
* `Hypothesis.exists_mulEquiv_quadraticExtension` — the same with the canonical
  lift, so that the model exists unconditionally.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

/-- The subfield `F = {x : x^q = x}` of `E` carries a `ZMod 2`-algebra structure,
just as `E` does (`QuotientFieldModel.instAlgebraZModTwo`); it is not derivable by
instance search because `ZMod.algebra` is deliberately a `def`. -/
noncomputable instance instAlgebraZModTwoFrobFixed {E : Type*} [Field E] [Finite E]
    [CharP E 2] (n : ℕ) :
    Algebra (ZMod 2) ↥(OddOrder.FiniteField.frobFixedSubfield E 2 n) :=
  ZMod.algebra _ 2

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

variable {m : ℕ} (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)

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
