/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Irreducible
import OddOrder.GroupTheory.Homocyclic
import OddOrder.GroupTheory.PRank
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups
import OddOrder.GroupTheory.SpecificGroups.Suzuki2Group.Basic

/-!
# Higman Lemma 1: successive Agemo layers

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 1,
p. 83; used in Peterfalvi, Appendix III.

For a homocyclic abelian `2`-group, the power map identifies every successive
Agemo quotient with the last nontrivial Agemo layer.  This identification is
equivariant for every automorphism action.  Consequently, an action transitive
on the involutions is transitive on the nonidentity elements of every
successive quotient.  This is the precise Lean form of Higman's sentence that
the power mappings are linear and all these quotients are irreducible.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory.Suzuki2Group

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- The action on an Agemo layer obtained by restricting the ambient action. -/
def agemoRestrictAction
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (s : ℕ) : X →* MulAut ↥(Agemo A 2 s) :=
  (IsAInvariant.of_characteristic φ).restrict

/-- The induced action on two successive Agemo layers. -/
noncomputable def agemoSuccQuotientAction
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (s : ℕ) :
    X →* MulAut
      (↥(Agemo A 2 s) ⧸
        (Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)) := by
  let hHs : IsAInvariant φ (Agemo A 2 s) :=
    IsAInvariant.of_characteristic φ
  let hHnext : IsAInvariant φ (Agemo A 2 (s + 1)) :=
    IsAInvariant.of_characteristic φ
  exact (hHs.subgroupOf hHnext).quotientMulAutHom

/-- The `s`-th successive Agemo quotient. -/
abbrev AgemoSuccQuotient (A : Type*) [CommGroup A] (s : ℕ) :=
  ↥(Agemo A 2 s) ⧸
    (Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)

/-! ## Power maps from the zeroth factor -/

/-- The `2 ^ s`-power map from the zeroth Agemo term to the `s`-th term.

This is the representative-level map underlying Higman's comparison of
successive `ξ`-composition factors. -/
def agemoZeroToLayerPowHom
    {A : Type*} [CommGroup A] (s : ℕ) :
    ↥(Agemo A 2 0) →* ↥(Agemo A 2 s) where
  toFun x := ⟨x.1 ^ (2 ^ s), Agemo.mem_of_eq_pow x.1⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_pow]

/-- The actual power map from `A / A²` onto the `s`-th successive Agemo
factor.  No homocyclicity assumption is needed for surjectivity; injectivity
will only be used later when irreducibility or a homocyclic model supplies it. -/
def agemoZeroQuotientToSuccPowHom
    {A : Type*} [CommGroup A] (s : ℕ) :
    (↥(Agemo A 2 0) ⧸
        (Agemo A 2 1).subgroupOf (Agemo A 2 0)) →*
      (↥(Agemo A 2 s) ⧸
        (Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)) := by
  apply QuotientGroup.map
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0))
    ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s))
    (agemoZeroToLayerPowHom s)
  intro x hx
  change x.1 ^ (2 ^ s) ∈ Agemo A 2 (s + 1)
  obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hx
  have hy' : (x : A) = y ^ 2 := by simpa using hy
  apply mem_agemo_iff_of_comm.mpr
  refine ⟨y, ?_⟩
  rw [hy', ← pow_mul]
  congr 1
  simp [pow_succ, mul_comm]

@[simp] theorem agemoZeroQuotientToSuccPowHom_mk
    {A : Type*} [CommGroup A] (s : ℕ) (x : ↥(Agemo A 2 0)) :
    agemoZeroQuotientToSuccPowHom s (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (agemoZeroToLayerPowHom s x) :=
  rfl

/-- Every successive Agemo factor is an actual quotient of the zeroth factor
under the corresponding power map. -/
theorem agemoZeroQuotientToSuccPowHom_surjective
    {A : Type*} [CommGroup A] (s : ℕ) :
    Function.Surjective (agemoZeroQuotientToSuccPowHom (A := A) s) := by
  intro q
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
    ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)) q
  obtain ⟨x, hx⟩ := mem_agemo_iff_of_comm.mp z.2
  let x₀ : ↥(Agemo A 2 0) :=
    ⟨x, by rw [agemo_zero_eq_top]; exact Subgroup.mem_top x⟩
  refine ⟨QuotientGroup.mk' _ x₀, ?_⟩
  rw [agemoZeroQuotientToSuccPowHom_mk]
  apply congrArg (QuotientGroup.mk'
    ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)))
  apply Subtype.ext
  exact hx.symm

/-- The quotient power map intertwines every ambient automorphism action. -/
theorem agemoZeroQuotientToSuccPowHom_equivariant
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (s : ℕ) (g : X)
    (q : ↥(Agemo A 2 0) ⧸
      (Agemo A 2 1).subgroupOf (Agemo A 2 0)) :
    agemoZeroQuotientToSuccPowHom s
        (agemoSuccQuotientAction φ 0 g q) =
      agemoSuccQuotientAction φ s g
        (agemoZeroQuotientToSuccPowHom s q) := by
  refine QuotientGroup.induction_on q ?_
  intro x
  apply congrArg (QuotientGroup.mk'
    ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)))
  apply Subtype.ext
  simp [agemoZeroToLayerPowHom, map_pow]

/-! ## Elementary-abelian and linear-representation bridge -/

/-- Every successive Agemo quotient has exponent two. -/
theorem agemoSuccQuotient_two_nsmul_eq_zero
    {A : Type*} [CommGroup A] (s : ℕ)
    (q : Additive (AgemoSuccQuotient A s)) : 2 • q = 0 := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q.toMul
  apply Additive.toMul.injective
  change q.toMul ^ 2 = 1
  rw [← hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    agemo_succ_subgroupOf_eq_agemo_one]
  exact Agemo.mem_of_eq_pow x

/-- Each successive Agemo quotient is an elementary abelian `2`-group. -/
theorem agemoSuccQuotient_isElementaryAbelian
    {A : Type*} [CommGroup A] (s : ℕ) :
    IsElementaryAbelian 2 (AgemoSuccQuotient A s) := by
  refine ⟨fun x y ↦ mul_comm x y, ?_⟩
  intro q
  apply Additive.ofMul.injective
  simpa [ofMul_pow] using
    agemoSuccQuotient_two_nsmul_eq_zero s (Additive.ofMul q)

/-- Canonical `F₂`-module structure on a successive Agemo quotient. -/
noncomputable instance agemoSuccQuotientModTwoModule
    {A : Type*} [CommGroup A] (s : ℕ) :
    Module (ZMod 2) (Additive (AgemoSuccQuotient A s)) :=
  AddCommGroup.zmodModule (agemoSuccQuotient_two_nsmul_eq_zero s)

/-- A multiplicative automorphism of an elementary abelian `2`-group as a
linear equivalence of its additive copy. -/
noncomputable def mulAutToZModTwoLinearEquiv
    {M : Type*} [CommGroup M] [Module (ZMod 2) (Additive M)] :
    MulAut M ≃* (Additive M ≃ₗ[ZMod 2] Additive M) :=
  (AddEquiv.toMultiplicativeLeft (AddAutAdditive (G := M))).symm.trans
    AddAut.toZModLinearEquiv

/-- The action on a successive Agemo quotient, viewed as an `F₂`
representation. -/
noncomputable def agemoSuccQuotientRepresentation
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (s : ℕ) :
    Representation (ZMod 2) X (Additive (AgemoSuccQuotient A s)) where
  toFun g :=
    (mulAutToZModTwoLinearEquiv
      (agemoSuccQuotientAction φ s g)).toLinearMap
  map_one' := by
    rw [map_one]
    exact Module.End.one_eq_id.symm
  map_mul' g h := by
    simp [mulAutToZModTwoLinearEquiv, agemoSuccQuotientAction]

/-- Linear form of the actual zeroth-to-`s`-th power homomorphism. -/
noncomputable def agemoZeroToSuccLinearMap
    {A : Type*} [CommGroup A] (s : ℕ) :
    Additive (AgemoSuccQuotient A 0) →ₗ[ZMod 2]
      Additive (AgemoSuccQuotient A s) :=
  (agemoZeroQuotientToSuccPowHom s).toAdditive.toZModLinearMap 2

@[simp] theorem agemoZeroToSuccLinearMap_apply
    {A : Type*} [CommGroup A] (s : ℕ)
    (q : Additive (AgemoSuccQuotient A 0)) :
    agemoZeroToSuccLinearMap s q =
      Additive.ofMul (agemoZeroQuotientToSuccPowHom s q.toMul) :=
  rfl

/-- The linear power map is surjective. -/
theorem agemoZeroToSuccLinearMap_surjective
    {A : Type*} [CommGroup A] (s : ℕ) :
    Function.Surjective (agemoZeroToSuccLinearMap (A := A) s) := by
  intro q
  obtain ⟨r, hr⟩ :=
    agemoZeroQuotientToSuccPowHom_surjective s q.toMul
  refine ⟨Additive.ofMul r, ?_⟩
  apply Additive.toMul.injective
  exact hr

/-- The linear power map intertwines the zeroth and `s`-th quotient
representations. -/
theorem agemoZeroToSuccLinearMap_equivariant
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (s : ℕ) (g : X)
    (q : Additive (AgemoSuccQuotient A 0)) :
    agemoZeroToSuccLinearMap s
        (agemoSuccQuotientRepresentation φ 0 g q) =
      agemoSuccQuotientRepresentation φ s g
        (agemoZeroToSuccLinearMap s q) := by
  apply Additive.toMul.injective
  exact agemoZeroQuotientToSuccPowHom_equivariant φ s g q.toMul

/-- If the zeroth Agemo factor is irreducible, every nontrivial successive
factor is equivariantly linearly equivalent to it.  This is the precise
power-factor step used in Higman's `ξ`-composition-factor argument. -/
theorem exists_agemoZero_linearEquiv_succ_of_irreducible
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (s : ℕ)
    (hirr : Representation.IsIrreducible
      (agemoSuccQuotientRepresentation φ 0))
    [Nontrivial (AgemoSuccQuotient A s)] :
    ∃ e : Additive (AgemoSuccQuotient A 0) ≃ₗ[ZMod 2]
        Additive (AgemoSuccQuotient A s),
      ∀ g q,
        e (agemoSuccQuotientRepresentation φ 0 g q) =
          agemoSuccQuotientRepresentation φ s g (e q) := by
  let f : Representation.IntertwiningMap
      (agemoSuccQuotientRepresentation φ 0)
      (agemoSuccQuotientRepresentation φ s) :=
    (agemoZeroToSuccLinearMap s).intertwiningMap_of_isIntertwiningMap
      (agemoSuccQuotientRepresentation φ 0)
      (agemoSuccQuotientRepresentation φ s)
      (agemoZeroToSuccLinearMap_equivariant φ s)
  letI : Representation.IsIrreducible
      (agemoSuccQuotientRepresentation φ 0) := hirr
  have hsurj : Function.Surjective f := by
    change Function.Surjective (agemoZeroToSuccLinearMap (A := A) s)
    exact agemoZeroToSuccLinearMap_surjective s
  have hfne : f ≠ 0 := by
    intro hf
    have hlin : f.toLinearMap = 0 :=
      congrArg Representation.IntertwiningMap.toLinearMap hf
    exact LinearMap.ne_zero_of_surjective hsurj hlin
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hfne
  let e : Additive (AgemoSuccQuotient A 0) ≃ₗ[ZMod 2]
      Additive (AgemoSuccQuotient A s) :=
    LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro g q
  exact agemoZeroToSuccLinearMap_equivariant φ s g q

/-- The power-map equivalence from a successive Agemo quotient to the last
nontrivial layer intertwines the induced and restricted actions. -/
theorem agemoSuccQuotientEquivLast_equivariant
    {A X ι : Type*} [CommGroup A] [Group X] {e s : ℕ}
    (φ : X →* MulAut A)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (hs : s < e)
    (g : X)
    (q : ↥(Agemo A 2 s) ⧸
      (Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)) :
    agemoSuccQuotientEquivLast ε hs
        ((agemoSuccQuotientAction φ s g) q) =
      (agemoRestrictAction φ (e - 1) g)
        (agemoSuccQuotientEquivLast ε hs q) := by
  refine QuotientGroup.induction_on q ?_
  intro x
  apply Subtype.ext
  simp [agemoSuccQuotientAction, agemoRestrictAction,
    agemoSuccQuotientEquivLast_mk,
    agemoLayerPowHom, map_pow]

/-- A nonidentity element of the last nontrivial Agemo layer of a homocyclic
`2`-group is an involution of the ambient group. -/
theorem lastAgemoLayer_val_mem_involutions
    {A ι : Type*} [CommGroup A] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (he : 0 < e)
    (x : ↥(Agemo A 2 (e - 1))) (hx : x ≠ 1) :
    (x : A) ∈ involutions A := by
  constructor
  · obtain ⟨y, hy⟩ := (mem_agemo_iff_of_comm).mp x.2
    change x.1 ^ 2 = 1
    rw [hy, ← pow_mul]
    have hmul : 2 ^ (e - 1) * 2 = 2 ^ e := by
      calc
        2 ^ (e - 1) * 2 = 2 ^ ((e - 1) + 1) := by simp [pow_add]
        _ = 2 ^ e := by congr 1; omega
    rw [hmul]
    exact pow_two_pow_eq_one_of_equiv_pi_zmod ε y
  · intro hx1
    apply hx
    apply Subtype.ext
    exact hx1

/-- **Higman, Suzuki 2-groups, Lemma 1 — successive-layer irreducibility**:
transitivity on the involutions induces transitivity on the nonidentity
elements of every successive Agemo quotient. -/
theorem agemoSuccQuotientAction_transitive_on_nonidentity
    {A X ι : Type*} [CommGroup A] [Group X] {e s : ℕ}
    (φ : X →* MulAut A)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (htrans : ∀ x ∈ involutions A, ∀ y ∈ involutions A,
      ∃ g : X, (φ g) x = y)
    (hs : s < e)
    (q r : ↥(Agemo A 2 s) ⧸
      (Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s))
    (hq : q ≠ 1) (hr : r ≠ 1) :
    ∃ g : X, (agemoSuccQuotientAction φ s g) q = r := by
  let E := agemoSuccQuotientEquivLast ε hs
  have he : 0 < e := by omega
  have hEq : E q ≠ 1 := by
    intro h
    apply hq
    apply E.injective
    simpa using h
  have hEr : E r ≠ 1 := by
    intro h
    apply hr
    apply E.injective
    simpa using h
  have hqInv : ((E q : ↥(Agemo A 2 (e - 1))) : A) ∈ involutions A :=
    lastAgemoLayer_val_mem_involutions ε he (E q) hEq
  have hrInv : ((E r : ↥(Agemo A 2 (e - 1))) : A) ∈ involutions A :=
    lastAgemoLayer_val_mem_involutions ε he (E r) hEr
  obtain ⟨g, hg⟩ := htrans (E q).1 hqInv (E r).1 hrInv
  refine ⟨g, ?_⟩
  apply E.injective
  rw [agemoSuccQuotientEquivLast_equivariant]
  apply Subtype.ext
  exact hg

end OddOrder.Higman.Suzuki2Groups
