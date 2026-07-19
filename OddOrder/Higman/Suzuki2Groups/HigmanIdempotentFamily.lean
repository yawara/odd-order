/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentAction

/-!
# Higman Lemma 3: a chosen commuting idempotent family on `A / A²`

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
pp. 83--84.

This file formalizes the following part of the argument on p. 84:

* choose, simultaneously for every `u ∈ C`, an endomorphism `ν(u)` such that
  inverse conjugation is `1 - 2ν(u)` and `4(ν(u)² - ν(u)) = 0`;
* pass the chosen family to the actual quotient `A / A²` and prove that it
  turns multiplication in `C` into addition of idempotents;
* package the additive product law as a monoid homomorphism and prove that
  the resulting idempotents commute pairwise.

Actor covariance, the kernel of this homomorphism, and the final
exponent-at-most-four conclusion of Higman's Lemma 3 are not claimed here.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- **Higman Lemma 3** (pp. 83--84), chosen-lift data.

This structure records one coherent choice of a one-minus-two lift `ν(u)`
for every member of an inverse-conjugation family. -/
structure HigmanEndomorphismFamily
    {A C : Type*} [CommGroup A] [Group C]
    (conjInv : C → MulAut A) where
  ν : C → AddMonoid.End (Additive A)
  conj_eq_one_sub_two : ∀ u : C,
    (conjInv u).toMonoidHom.toAdditive =
      (1 : AddMonoid.End (Additive A)) - 2 • ν u
  four_relation : ∀ u : C, 4 • (ν u * ν u - ν u) = 0

/-- **Higman Lemma 3** (pp. 83--84): Frattini equality chooses all of the
one-minus-two lifts simultaneously. -/
noncomputable def chosenHigmanEndomorphismFamily
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} [A.Normal]
    (hAC : A ≤ C) (hAcomm : IsMulCommutative A)
    (hΦ : (frattini C).map C.subtype = (frattini A).map A.subtype)
    {ι : Type*} [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    HigmanEndomorphismFamily
      (fun u : C ↦ MulAut.conjNormal (H := A) (u : P)⁻¹) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  classical
  have hex (u : C) :
      ∃ ν : AddMonoid.End (Additive A),
        (MulAut.conjNormal (H := A) (u : P)⁻¹).toMonoidHom.toAdditive =
            (1 : AddMonoid.End (Additive A)) - 2 • ν ∧
          4 • (ν * ν - ν) = 0 :=
    exists_addEnd_eq_one_sub_two_and_four_nsmul_of_frattini_map_eq
      hP hAC hAcomm hΦ ε u.2
  choose ν hν using hex
  exact
    { ν := ν
      conj_eq_one_sub_two := fun u ↦ (hν u).1
      four_relation := fun u ↦ (hν u).2 }

/-- The chosen lift indexed by `u`, induced on the actual quotient `A / A²`.
-/
noncomputable def HigmanEndomorphismFamily.modTwo
    {A C : Type*} [CommGroup A] [Group C]
    {conjInv : C → MulAut A}
    (F : HigmanEndomorphismFamily conjInv) (u : C) :
    Module.End (ZMod 2) (Additive (A ⧸ Agemo A 2 1)) :=
  actualModTwoEnd (F.ν u)

/-- **Higman Lemma 3** (p. 84): every chosen lift induces an idempotent on
the actual quotient `A / A²`. -/
theorem HigmanEndomorphismFamily.modTwo_idempotent
    {A C ι : Type*} [CommGroup A] [Group C] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e) (u : C) :
    IsIdempotentElem (F.modTwo u) :=
  actualModTwoEnd_idempotent ε he (F.ν u) (F.four_relation u)

/-- **Higman Lemma 3** (p. 84), cancellation on `A / A²`.

If the one-minus-two expressions compose, their chosen lifts become additive
after passing directly to the actual quotient. -/
theorem actualModTwoEnd_eq_add_of_one_sub_two_mul
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (he : 3 ≤ e)
    (νu νv νuv : AddMonoid.End (Additive A))
    (hcomp :
      (1 : AddMonoid.End (Additive A)) - 2 • νuv =
        ((1 : AddMonoid.End (Additive A)) - 2 • νu) *
          ((1 : AddMonoid.End (Additive A)) - 2 • νv)) :
    actualModTwoEnd νuv = actualModTwoEnd νu + actualModTwoEnd νv := by
  let k := νuv - νu - νv + 2 • (νu * νv)
  have hzero :
      ((1 : AddMonoid.End (Additive A)) - 2 • νuv) -
        (((1 : AddMonoid.End (Additive A)) - 2 • νu) *
          ((1 : AddMonoid.End (Additive A)) - 2 • νv)) = 0 :=
    sub_eq_zero.mpr hcomp
  have hdouble :
      ((2 • νu : AddMonoid.End (Additive A)) *
        (2 • νv : AddMonoid.End (Additive A))) =
          (4 • (νu * νv) : AddMonoid.End (Additive A)) := by
    simp only [two_nsmul, add_mul, mul_add]
    abel
  have hexpand :
      ((1 : AddMonoid.End (Additive A)) - 2 • νu) *
          ((1 : AddMonoid.End (Additive A)) - 2 • νv) =
        (1 : AddMonoid.End (Additive A)) - 2 • νu - 2 • νv +
          4 • (νu * νv) := by
    calc
      _ = (1 : AddMonoid.End (Additive A)) - 2 • νu - 2 • νv +
          (-(2 • νu)) * (-(2 • νv)) := by noncomm_ring
      _ = (1 : AddMonoid.End (Additive A)) - 2 • νu - 2 • νv +
          (2 • νu) * (2 • νv) := by
        congr 1
        exact neg_mul_neg (2 • νu : AddMonoid.End (Additive A))
          (2 • νv : AddMonoid.End (Additive A))
      _ = _ := by rw [hdouble]
  have hk2 : 2 • k = 0 := by
    calc
      2 • k = 2 • νuv - 2 • νu - 2 • νv + 4 • (νu * νv) := by
        dsimp [k]
        abel
      _ = -(
          ((1 : AddMonoid.End (Additive A)) - 2 • νuv) -
            (((1 : AddMonoid.End (Additive A)) - 2 • νu) *
              ((1 : AddMonoid.End (Additive A)) - 2 • νv))) := by
        rw [hexpand]
        abel
      _ = 0 := by rw [hzero, neg_zero]
  apply LinearMap.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  apply Additive.toMul.injective
  change (QuotientGroup.mk (addEndToMonoidEnd νuv a) :
      A ⧸ Agemo A 2 1) =
    (QuotientGroup.mk (addEndToMonoidEnd νu a) : A ⧸ Agemo A 2 1) *
      QuotientGroup.mk (addEndToMonoidEnd νv a)
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
  let x : Additive A := Additive.ofMul a
  have hk2x : 2 • k x = 0 := by
    simpa using DFunLike.congr_fun hk2 x
  have hk4x : 4 • k x = 0 := by
    calc
      4 • k x = 2 • (2 • k x) := by abel
      _ = 0 := by rw [hk2x, nsmul_zero]
  have hk_mem : Additive.toMul (k x) ∈ Agemo A 2 1 :=
    toMul_mem_agemo_one_of_four_nsmul_eq_zero ε he hk4x
  have htwo_mem :
      Additive.toMul
        ((2 • (νu * νv) : AddMonoid.End (Additive A)) x) ∈
          Agemo A 2 1 := by
    change Additive.toMul (2 • (νu * νv) x) ∈ Agemo A 2 1
    simpa using (Agemo.mem_of_eq_pow (G := A) (p := 2) (n := 1)
      (Additive.toMul ((νu * νv) x)))
  have hsub : Additive.toMul
      (k x - (2 • (νu * νv) : AddMonoid.End (Additive A)) x) ∈
        Agemo A 2 1 := by
    change Additive.toMul (k x) /
      Additive.toMul ((2 • (νu * νv) : AddMonoid.End (Additive A)) x) ∈
        Agemo A 2 1
    exact (Agemo A 2 1).div_mem hk_mem htwo_mem
  change Additive.toMul (νuv x - (νu x + νv x)) ∈ Agemo A 2 1
  rw [show νuv x - (νu x + νv x) =
      k x - (2 • (νu * νv) : AddMonoid.End (Additive A)) x by
    have hend : νuv - νu - νv = k - 2 • (νu * νv) := by
      dsimp [k]
      abel
    have hpoint := DFunLike.congr_fun hend x
    change νuv x - νu x - νv x =
      k x - (2 • (νu * νv) : AddMonoid.End (Additive A)) x at hpoint
    calc
      νuv x - (νu x + νv x) = νuv x - νu x - νv x := by abel
      _ = k x - (2 • (νu * νv) : AddMonoid.End (Additive A)) x := hpoint]
  exact hsub

/-- **Higman Lemma 3** (p. 84): the chosen quotient family is additive on
products whenever its inverse-conjugation family reverses products. -/
theorem HigmanEndomorphismFamily.modTwo_mul
    {A C ι : Type*} [CommGroup A] [Group C] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (hconjMul : ∀ u v : C, conjInv (u * v) = conjInv v * conjInv u)
    (u v : C) :
    F.modTwo (u * v) = F.modTwo u + F.modTwo v := by
  let αuv : AddMonoid.End (Additive A) :=
    (conjInv (u * v)).toMonoidHom.toAdditive
  let αv : AddMonoid.End (Additive A) :=
    (conjInv v).toMonoidHom.toAdditive
  let αu : AddMonoid.End (Additive A) :=
    (conjInv u).toMonoidHom.toAdditive
  have hmul : αuv = αv * αu := by
    apply AddMonoidHom.ext
    intro x
    change Additive.ofMul (conjInv (u * v) (Additive.toMul x)) =
      Additive.ofMul (conjInv v (conjInv u (Additive.toMul x)))
    exact congrArg Additive.ofMul
      (DFunLike.congr_fun (hconjMul u v) (Additive.toMul x))
  have hcomp :
      (1 : AddMonoid.End (Additive A)) - 2 • F.ν (u * v) =
        ((1 : AddMonoid.End (Additive A)) - 2 • F.ν v) *
          ((1 : AddMonoid.End (Additive A)) - 2 • F.ν u) := by
    calc
      _ = αuv := (F.conj_eq_one_sub_two (u * v)).symm
      _ = αv * αu := hmul
      _ = _ := congrArg₂
        (fun x y : AddMonoid.End (Additive A) ↦ x * y)
        (F.conj_eq_one_sub_two v) (F.conj_eq_one_sub_two u)
  have h := actualModTwoEnd_eq_add_of_one_sub_two_mul
    ε he (F.ν v) (F.ν u) (F.ν (u * v)) hcomp
  simpa [HigmanEndomorphismFamily.modTwo, add_comm] using h

/-- Package a function which turns multiplication into addition as a monoid
homomorphism to the multiplicative type synonym. The value at `1` follows
from the product law by additive cancellation. -/
def additiveMulMapToMultiplicative
    {C E : Type*} [Group C] [AddCommGroup E]
    (f : C → E) (hmul : ∀ u v, f (u * v) = f u + f v) :
    C →* Multiplicative E where
  toFun u := Multiplicative.ofAdd (f u)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change f 1 = 0
    have h := hmul 1 1
    simp only [one_mul] at h
    apply add_left_cancel (a := f 1)
    simpa using h.symm
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    exact hmul u v

@[simp]
theorem additiveMulMapToMultiplicative_apply
    {C E : Type*} [Group C] [AddCommGroup E]
    (f : C → E) (hmul : ∀ u v, f (u * v) = f u + f v) (u : C) :
    Multiplicative.toAdd (additiveMulMapToMultiplicative f hmul u) = f u :=
  rfl

/-- **Higman Lemma 3** (p. 84): the additive product law, packaged as a
monoid homomorphism. -/
noncomputable def HigmanEndomorphismFamily.modTwoHom
    {A C ι : Type*} [CommGroup A] [Group C] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (hconjMul : ∀ u v : C, conjInv (u * v) = conjInv v * conjInv u) :
    C →* Multiplicative
      (Module.End (ZMod 2) (Additive (A ⧸ Agemo A 2 1))) :=
  additiveMulMapToMultiplicative F.modTwo (F.modTwo_mul ε he hconjMul)

/-- In characteristic two, idempotence of `f`, `g`, and `f + g` forces
`f` and `g` to commute. -/
theorem commute_of_idempotent_add
    {R : Type*} [Ring R]
    (h2 : ∀ x : R, x + x = 0)
    {f g : R}
    (hf : IsIdempotentElem f)
    (hg : IsIdempotentElem g)
    (hfg : IsIdempotentElem (f + g)) :
    Commute f g := by
  have hcross : f * g + g * f = 0 := by
    calc
      f * g + g * f =
          (f + g) * (f + g) - f * f - g * g := by
        noncomm_ring
      _ = (f + g) - f - g := by rw [hfg.eq, hf.eq, hg.eq]
      _ = 0 := by abel
  calc
    f * g = -(g * f) := eq_neg_of_add_eq_zero_left hcross
    _ = g * f := neg_eq_iff_add_eq_zero.mpr (h2 (g * f))

/-- **Higman Lemma 3** (p. 84): two members of the chosen idempotent family
commute on the actual quotient `A / A²`. -/
theorem HigmanEndomorphismFamily.modTwo_commute
    {A C ι : Type*} [CommGroup A] [Group C] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (hconjMul : ∀ u v : C, conjInv (u * v) = conjInv v * conjInv u)
    (u v : C) :
    Commute (F.modTwo u) (F.modTwo v) := by
  apply commute_of_idempotent_add
  · intro f
    apply LinearMap.ext
    intro x
    change f x + f x = 0
    simpa [two_nsmul] using
      (actualQuotient_two_nsmul_eq_zero (A := A) (f x))
  · exact F.modTwo_idempotent ε he u
  · exact F.modTwo_idempotent ε he v
  · rw [← F.modTwo_mul ε he hconjMul u v]
    exact F.modTwo_idempotent ε he (u * v)

/-- **Higman Lemma 3** (p. 84): pairwise form of commutativity for the chosen
idempotent family. -/
theorem HigmanEndomorphismFamily.modTwo_pairwise_commute
    {A C ι : Type*} [CommGroup A] [Group C] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (hconjMul : ∀ u v : C, conjInv (u * v) = conjInv v * conjInv u) :
    Pairwise fun u v : C ↦ Commute (F.modTwo u) (F.modTwo v) := by
  intro u v _
  exact F.modTwo_commute ε he hconjMul u v

/-- Inverse conjugation by subgroup elements reverses products. -/
theorem subgroupConjInv_mul
    {P : Type*} [Group P] {A C : Subgroup P} [A.Normal] [CommGroup A]
    (u v : C) :
    MulAut.conjNormal (H := A) ((u * v : C) : P)⁻¹ =
      MulAut.conjNormal (H := A) (v : P)⁻¹ *
        MulAut.conjNormal (H := A) (u : P)⁻¹ := by
  change MulAut.conjNormal (H := A) ((u : P) * (v : P))⁻¹ =
    MulAut.conjNormal (H := A) (v : P)⁻¹ *
      MulAut.conjNormal (H := A) (u : P)⁻¹
  exact conjNormal_mul_inv (A := A) (u := (u : P)) (v := (v : P))

end OddOrder.Higman.Suzuki2Groups
