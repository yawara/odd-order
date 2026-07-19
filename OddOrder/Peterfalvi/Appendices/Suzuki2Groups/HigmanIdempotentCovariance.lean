/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanIdempotentFamily

/-!
# Higman Lemma 3: covariance and the zero-or-one conclusion

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
p. 84.

This file formalizes the actor-covariance and common-eigenvector terminal
steps of Higman's argument:

* compatible actions conjugate the chosen idempotent family on the actual
  quotient `A / A²`;
* a finite commuting family of idempotents permuted by an actor transitive on
  nonzero vectors consists only of zero and identity endomorphisms;
* these statements are connected for `HigmanEndomorphismFamily.modTwo`, with
  covariance accepted either as a hypothesis or derived from compatible
  actions on `A` and `C`.

The kernel of the resulting homomorphism, the calculation of `C / A`, and the
final exponent-at-most-four conclusion are not claimed here.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- Restricting an ambient actor to invariant subgroups `A` and `C` gives
the compatibility identity needed for chosen-family covariance. -/
theorem subgroupConjInv_actor_compatible
    {P X : Type*} [Group P] [Group X]
    {A C : Subgroup P} [A.Normal]
    (act : X →* MulAut P)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    (x : X) (u : C) :
    MulAut.conjNormal (H := A)
        (((hCinv.restrict x) u : C) : P)⁻¹ =
      hAinv.restrict x *
        MulAut.conjNormal (H := A) (u : P)⁻¹ *
          (hAinv.restrict x)⁻¹ := by
  change MulAut.conjNormal (H := A) (act x (u : P))⁻¹ =
    hAinv.restrict x * MulAut.conjNormal (H := A) (u : P)⁻¹ *
      (hAinv.restrict x)⁻¹
  exact conjNormal_actor_apply_inv act hAinv x (u : P)

/-- Transitivity of an ambient actor on the involutions of `P` restricts to
transitivity on the involutions of every invariant subgroup `A`. -/
theorem restricted_involutions_transitive
    {P X : Type*} [Group P] [Group X]
    (act : X →* MulAut P) {A : Subgroup P}
    (hAinv : IsAInvariant act A)
    (htrans : ∀ a ∈ involutions P, ∀ b ∈ involutions P,
      ∃ x : X, act x a = b) :
    ∀ a ∈ involutions A, ∀ b ∈ involutions A,
      ∃ x : X, hAinv.restrict x a = b := by
  intro a ha b hb
  have haP : (a : P) ∈ involutions P := by
    constructor
    · exact congrArg Subtype.val ha.1
    · intro ha1
      exact ha.2 (Subtype.ext ha1)
  have hbP : (b : P) ∈ involutions P := by
    constructor
    · exact congrArg Subtype.val hb.1
    · intro hb1
      exact hb.2 (Subtype.ext hb1)
  obtain ⟨x, hx⟩ := htrans (a : P) haP (b : P) hbP
  refine ⟨x, Subtype.ext ?_⟩
  rw [IsAInvariant.restrict_apply_val]
  exact hx


/-- The quotient representation of an automorphism agrees with the
endomorphism obtained by applying `actualModTwoEnd` to its additive copy. -/
theorem actualAgemoOneQuotientRepresentation_eq_actualModTwoEnd
    {A X : Type*} [CommGroup A] [Group X]
    (actA : X →* MulAut A) (x : X) :
    actualAgemoOneQuotientRepresentation actA x =
      actualModTwoEnd
        ((actA x).toMonoidHom.toAdditive :
          AddMonoid.End (Additive A)) := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  rfl

/-- An additive endomorphism killed by two induces zero on `A / A²` when
`A` is homocyclic of exponent at least eight. -/
theorem actualModTwoEnd_eq_zero_of_two_nsmul_eq_zero
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (he : 3 ≤ e)
    (k : AddMonoid.End (Additive A)) (hk : 2 • k = 0) :
    actualModTwoEnd k = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  rw [actualModTwoEnd_mk]
  apply Additive.toMul.injective
  change QuotientGroup.mk (addEndToMonoidEnd k a) = 1
  rw [QuotientGroup.eq_one_iff]
  apply toMul_mem_agemo_one_of_four_nsmul_eq_zero ε he
  have hk2x : 2 • k (Additive.ofMul a) = 0 := by
    simpa using DFunLike.congr_fun hk (Additive.ofMul a)
  calc
    4 • k (Additive.ofMul a) =
        2 • (2 • k (Additive.ofMul a)) := by abel
    _ = 0 := by rw [hk2x, nsmul_zero]

/-- `actualModTwoEnd` respects additive inverses. -/
theorem actualModTwoEnd_neg
    {A : Type*} [CommGroup A]
    (ν : AddMonoid.End (Additive A)) :
    actualModTwoEnd (-ν) = -actualModTwoEnd ν := by
  apply eq_neg_of_add_eq_zero_left
  rw [← actualModTwoEnd_add, neg_add_cancel, actualModTwoEnd_zero]

/-- **Higman Lemma 3** (p. 84): generic actor covariance of the chosen
idempotent family on the actual quotient `A / A²`. -/
theorem HigmanEndomorphismFamily.modTwo_covariant
    {A C X ι : Type*} [CommGroup A] [Group C] [Group X] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (actA : X →* MulAut A) (actC : X →* MulAut C)
    (hcompat : ∀ x : X, ∀ u : C,
      conjInv (actC x u) =
        actA x * conjInv u * (actA x)⁻¹)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e) (x : X) (u : C)
    (q : Additive (A ⧸ Agemo A 2 1)) :
    actualAgemoOneQuotientRepresentation actA x (F.modTwo u q) =
      F.modTwo (actC x u)
        (actualAgemoOneQuotientRepresentation actA x q) := by
  let α : AddMonoid.End (Additive A) :=
    (actA x).toMonoidHom.toAdditive
  let αinv : AddMonoid.End (Additive A) :=
    ((actA x)⁻¹).toMonoidHom.toAdditive
  let β : AddMonoid.End (Additive A) :=
    (conjInv u).toMonoidHom.toAdditive
  let β' : AddMonoid.End (Additive A) :=
    (conjInv (actC x u)).toMonoidHom.toAdditive
  have hβ : β' = α * β * αinv := by
    apply AddMonoidHom.ext
    intro a
    change Additive.ofMul (conjInv (actC x u) (Additive.toMul a)) =
      Additive.ofMul
        (actA x (conjInv u ((actA x)⁻¹ (Additive.toMul a))))
    exact congrArg Additive.ofMul
      (DFunLike.congr_fun (hcompat x u) (Additive.toMul a))
  have hinv : αinv * α = 1 := by
    apply AddMonoidHom.ext
    intro a
    change Additive.ofMul ((actA x)⁻¹ (actA x (Additive.toMul a))) = a
    simp
  have honeMinusTwo :
      (1 : AddMonoid.End (Additive A)) - 2 • F.ν (actC x u) =
        α * ((1 : AddMonoid.End (Additive A)) - 2 • F.ν u) * αinv := by
    calc
      _ = β' := (F.conj_eq_one_sub_two (actC x u)).symm
      _ = α * β * αinv := hβ
      _ = _ := congrArg
        (fun z : AddMonoid.End (Additive A) ↦ α * z * αinv)
        (F.conj_eq_one_sub_two u)
  have hright :
      ((1 : AddMonoid.End (Additive A)) - 2 • F.ν (actC x u)) * α =
        α * ((1 : AddMonoid.End (Additive A)) - 2 • F.ν u) := by
    calc
      _ = (α * ((1 : AddMonoid.End (Additive A)) - 2 • F.ν u) *
          αinv) * α := congrArg
        (fun z : AddMonoid.End (Additive A) ↦ z * α) honeMinusTwo
      _ = α * ((1 : AddMonoid.End (Additive A)) - 2 • F.ν u) *
          (αinv * α) := by simp only [mul_assoc]
      _ = _ := by rw [hinv, mul_one]
  let k : AddMonoid.End (Additive A) :=
    F.ν (actC x u) * α - α * F.ν u
  have hk : 2 • k = 0 := by
    have hzero :
        ((1 : AddMonoid.End (Additive A)) - 2 • F.ν (actC x u)) * α -
          α * ((1 : AddMonoid.End (Additive A)) - 2 • F.ν u) = 0 :=
      sub_eq_zero.mpr hright
    have htwo_left :
        2 • (F.ν (actC x u) * α) =
          (2 • F.ν (actC x u)) * α := by
      simp only [two_nsmul, add_mul]
    have htwo_right :
        2 • (α * F.ν u) = α * (2 • F.ν u) := by
      simp only [two_nsmul, mul_add]
    calc
      2 • k = 2 • (F.ν (actC x u) * α) -
          2 • (α * F.ν u) := by
        dsimp [k]
        abel
      _ = (2 • F.ν (actC x u)) * α -
          α * (2 • F.ν u) := by rw [htwo_left, htwo_right]
      _ = -(
          ((1 : AddMonoid.End (Additive A)) - 2 • F.ν (actC x u)) * α -
            α * ((1 : AddMonoid.End (Additive A)) - 2 • F.ν u)) := by
        rw [sub_mul, one_mul, mul_sub, mul_one]
        abel
      _ = 0 := by rw [hzero, neg_zero]
  have hkmod : actualModTwoEnd k = 0 :=
    actualModTwoEnd_eq_zero_of_two_nsmul_eq_zero ε he k hk
  have hmapk :
      actualModTwoEnd k =
        actualModTwoEnd (F.ν (actC x u)) * actualModTwoEnd α -
          actualModTwoEnd α * actualModTwoEnd (F.ν u) := by
    dsimp [k]
    rw [sub_eq_add_neg, actualModTwoEnd_add, actualModTwoEnd_neg,
      actualModTwoEnd_mul, actualModTwoEnd_mul, sub_eq_add_neg]
  have hend :
      actualModTwoEnd α * actualModTwoEnd (F.ν u) =
        actualModTwoEnd (F.ν (actC x u)) * actualModTwoEnd α := by
    symm
    apply sub_eq_zero.mp
    rw [← hmapk, hkmod]
  have hpoint := DFunLike.congr_fun hend q
  rw [actualAgemoOneQuotientRepresentation_eq_actualModTwoEnd actA x]
  simpa [HigmanEndomorphismFamily.modTwo, Module.End.mul_apply, α] using hpoint

/-- The common-eigenvector terminal theorem without a `Nontrivial V`
assumption. If `V` is subsingleton, every endomorphism is zero; otherwise
the existing transitive-conjugates theorem applies. -/
theorem all_end_eq_zero_or_one_of_transitive_conjugates_general
    {R V ι X : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    [Group X] [MulAction X ι] [Finite ι]
    (ρ : Representation R X V)
    (f : ι → Module.End R V)
    (hidem : ∀ i, IsIdempotentElem (f i))
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hperm : ∀ x i v, ρ x (f i v) = f (x • i) (ρ x v))
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x : X, ρ x v = w) :
    ∀ i, f i = 0 ∨ f i = 1 := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl hV =>
      letI : Subsingleton V := hV
      intro i
      left
      ext v
      exact Subsingleton.elim _ _
  | inr hV =>
      letI : Nontrivial V := hV
      exact all_end_eq_zero_or_one_of_transitive_conjugates
        ρ f hidem hcomm hperm htrans

/-- A covariance identity in the endomorphism ring, together with transitivity
on nonzero vectors, forces every member of a finite commuting idempotent
family to be zero or the identity. -/
theorem all_end_eq_zero_or_one_of_transitive_covariance
    {R V C X : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    [Group X] [MulAction X C] [Finite C]
    (ρ : Representation R X V)
    (f : C → Module.End R V)
    (hidem : ∀ u, IsIdempotentElem (f u))
    (hcomm : Pairwise fun u v ↦ Commute (f u) (f v))
    (hcov : ∀ x u, ρ x * f u = f (x • u) * ρ x)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x : X, ρ x v = w) :
    ∀ u, f u = 0 ∨ f u = 1 := by
  apply all_end_eq_zero_or_one_of_transitive_conjugates_general
    ρ f hidem hcomm
  · intro x u v
    exact DFunLike.congr_fun (hcov x u) v
  · exact htrans

/-- **Higman Lemma 3** (p. 84), specialized to the actual representation on
`A / A²`. The family and its actor covariance remain explicit hypotheses. -/
theorem actualQuotient_all_end_eq_zero_or_one_of_transitive_covariance
    {A C X ι : Type*} [CommGroup A] [Group X] [MulAction X C] [Finite C]
    {e : ℕ}
    (φ : X →* MulAut A)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (hinv : ∀ a ∈ involutions A, ∀ b ∈ involutions A,
      ∃ x : X, (φ x) a = b)
    (he : 0 < e)
    (f : C → Module.End (ZMod 2) (Additive (A ⧸ Agemo A 2 1)))
    (hidem : ∀ u, IsIdempotentElem (f u))
    (hcomm : Pairwise fun u v ↦ Commute (f u) (f v))
    (hcov : ∀ x u,
      actualAgemoOneQuotientRepresentation φ x * f u =
        f (x • u) * actualAgemoOneQuotientRepresentation φ x) :
    ∀ u, f u = 0 ∨ f u = 1 := by
  apply all_end_eq_zero_or_one_of_transitive_covariance
    (actualAgemoOneQuotientRepresentation φ) f hidem hcomm hcov
  exact actualAgemoOneQuotientRepresentation_transitive_on_nonzero
    φ ε hinv he

/-- **Higman Lemma 3** (p. 84): the chosen idempotent family consists only
of zero and identity once covariance under the actual actor representation
is supplied. Covariance itself is deliberately an input to this theorem. -/
theorem HigmanEndomorphismFamily.modTwo_eq_zero_or_one
    {A C X ι : Type*} [CommGroup A] [Group C] [Finite C]
    [Group X] [MulAction X C] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (hconjMul : ∀ u v : C, conjInv (u * v) = conjInv v * conjInv u)
    (φ : X →* MulAut A)
    (hinv : ∀ a ∈ involutions A, ∀ b ∈ involutions A,
      ∃ x : X, (φ x) a = b)
    (hcov : ∀ x u,
      actualAgemoOneQuotientRepresentation φ x * F.modTwo u =
        F.modTwo (x • u) * actualAgemoOneQuotientRepresentation φ x) :
    ∀ u, F.modTwo u = 0 ∨ F.modTwo u = 1 := by
  apply actualQuotient_all_end_eq_zero_or_one_of_transitive_covariance
    φ ε hinv (by omega) F.modTwo
  · exact F.modTwo_idempotent ε he
  · exact F.modTwo_pairwise_commute ε he hconjMul
  · exact hcov


/-- **Higman Lemma 3** (p. 84): compatible actions on `A` and `C` supply
the covariance needed to conclude that every chosen quotient idempotent is
zero or the identity. -/
theorem HigmanEndomorphismFamily.modTwo_eq_zero_or_one_of_compatible_actions
    {A C X ι : Type*} [CommGroup A] [Group C] [Finite C]
    [Group X] [Finite ι]
    {conjInv : C → MulAut A} {e : ℕ}
    (F : HigmanEndomorphismFamily conjInv)
    (actA : X →* MulAut A) (actC : X →* MulAut C)
    (hcompat : ∀ x : X, ∀ u : C,
      conjInv (actC x u) = actA x * conjInv u * (actA x)⁻¹)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (hconjMul : ∀ u v : C, conjInv (u * v) = conjInv v * conjInv u)
    (hinv : ∀ a ∈ involutions A, ∀ b ∈ involutions A,
      ∃ x : X, (actA x) a = b) :
    ∀ u, F.modTwo u = 0 ∨ F.modTwo u = 1 := by
  letI : MulAction X C :=
    { smul := fun x u ↦ actC x u
      one_smul := fun u ↦ by
        change actC 1 u = u
        rw [map_one]
        rfl
      mul_smul := fun x y u ↦ by
        change actC (x * y) u = actC x (actC y u)
        rw [map_mul]
        rfl }
  apply F.modTwo_eq_zero_or_one ε he hconjMul actA hinv
  intro x u
  apply LinearMap.ext
  intro q
  exact F.modTwo_covariant actA actC hcompat ε he x u q

/-- **Higman Lemma 3** (p. 84): for an ambient actor preserving `A` and
`C`, every member of the actual inverse-conjugation idempotent family is zero
or the identity. Covariance is derived from the restricted ambient actions,
not required as an additional hypothesis. -/
theorem subgroupConjFamily_all_modTwo_eq_zero_or_one
    {P X ι : Type*} [Group P] [Group X]
    {A C : Subgroup P} [A.Normal]
    [Finite C] [Finite ι] {e : ℕ}
    (hAcomm : IsMulCommutative A)
    (act : X →* MulAut P)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    (htrans : ∀ a ∈ involutions P, ∀ b ∈ involutions P,
      ∃ x : X, act x a = b)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∀ (F : HigmanEndomorphismFamily
      (fun u : C ↦ MulAut.conjNormal (H := A) (u : P)⁻¹)),
      ∀ u : C, F.modTwo u = 0 ∨ F.modTwo u = 1 := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  intro F
  exact F.modTwo_eq_zero_or_one_of_compatible_actions
    hAinv.restrict hCinv.restrict
    (subgroupConjInv_actor_compatible act hAinv hCinv)
    ε he subgroupConjInv_mul
    (restricted_involutions_transitive act hAinv htrans)

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
