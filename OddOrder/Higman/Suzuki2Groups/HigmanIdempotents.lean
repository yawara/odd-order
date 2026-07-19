/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.NoncommRing
import OddOrder.Higman.Suzuki2Groups.HigmanEndomorphismLift

/-!
# Higman Lemma 3: commuting idempotents modulo two

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
pp. 83--84.

This file formalizes only the endomorphism calculation in the middle of
Higman's proof:

* expanding an involution written as `1 - 2ν` gives `4(ν² - ν) = 0`;
* on a homocyclic group of exponent at least eight, reduction modulo `2M`
  makes `ν` idempotent;
* a finite commuting family of idempotents has a common nonzero `0`/`1`
  eigenvector, and transitivity plus conjugation invariance makes every
  member zero or the identity.

The later homomorphism, kernel, and exponent-at-most-four arguments of
Higman Lemma 3 are not claimed here.
-/

set_option autoImplicit false

open Function

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory

section FourNuCalculation

/-- Expanding an involutory endomorphism written as one minus twice `ν`. -/
theorem four_nsmul_mul_sub_self_eq_zero
    {M : Type*} [AddCommGroup M]
    {α ν : AddMonoid.End M}
    (hαν : α = (1 : AddMonoid.End M) - 2 • ν)
    (hαsq : α * α = 1) :
    4 • (ν * ν - ν) = 0 := by
  calc
    4 • (ν * ν - ν) =
        ((1 : AddMonoid.End M) - 2 • ν) *
          ((1 : AddMonoid.End M) - 2 • ν) - 1 := by
      noncomm_ring
    _ = α * α - 1 := by rw [← hαν]
    _ = 0 := by rw [hαsq]; simp

/-- Conjugation by `u⁻¹` on an abelian normal subgroup is involutory when
`u²` belongs to that subgroup. -/
theorem conjNormal_inv_sq_eq_one_of_sq_mem
    {P : Type*} [Group P] {A : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A) {u : P} (hu2 : u ^ 2 ∈ A) :
    (MulAut.conjNormal (H := A) u⁻¹) *
        (MulAut.conjNormal (H := A) u⁻¹) = 1 := by
  ext a
  rw [MulAut.mul_apply, MulAut.conjNormal_apply,
    MulAut.conjNormal_apply, MulAut.one_apply]
  have hcomm : u ^ 2 * (a : P) = (a : P) * u ^ 2 :=
    congrArg A.subtype
      (hAcomm.is_comm.comm (⟨u ^ 2, hu2⟩ : A) a)
  simp only [inv_inv]
  calc
    u⁻¹ * (u⁻¹ * (a : P) * u) * u =
        (u ^ 2)⁻¹ * (a : P) * u ^ 2 := by
      rw [pow_two]
      group
    _ = (u ^ 2)⁻¹ * (u ^ 2 * (a : P)) := by
      rw [mul_assoc, ← hcomm]
    _ = (a : P) := by simp

/-- Transport an involutory multiplicative automorphism to the endomorphism
ring of the additive copy. -/
theorem addEnd_mul_self_eq_one_of_mulAut_mul_self_eq_one
    {A : Type*} [CommGroup A] (α : MulAut A)
    (hαsq : α * α = 1) :
    let αAdd : AddMonoid.End (Additive A) := α.toMonoidHom.toAdditive
    αAdd * αAdd = 1 := by
  dsimp only
  apply AddMonoidHom.ext
  intro x
  change Additive.ofMul (α (α (Additive.toMul x))) = x
  have hx := DFunLike.congr_fun hαsq (Additive.toMul x)
  exact congrArg Additive.ofMul hx

/-- Higman's `4(ν² - ν) = 0` consequence for conjugation by `u⁻¹`.
The hypothesis `hmod` says exactly that this conjugation is the identity
modulo the square subgroup. -/
theorem exists_four_nsmul_mul_sub_self_eq_zero_of_conjNormal_inv
    {P : Type*} [Group P] {A : Subgroup P} [A.Normal]
    {ι : Type*} [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (hAcomm : IsMulCommutative A)
    {u : P} (hu2 : u ^ 2 ∈ A)
    (hmod : ∀ a : A,
      MulAut.conjNormal (H := A) u⁻¹ a * a⁻¹ ∈ Agemo A 2 1) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∃ ν : AddMonoid.End (Additive A),
      4 • (ν * ν - ν) = 0 := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  let α : MulAut A := MulAut.conjNormal (H := A) u⁻¹
  obtain ⟨ν, hαν⟩ := exists_addEnd_eq_one_sub_two ε α hmod
  refine ⟨ν, four_nsmul_mul_sub_self_eq_zero hαν ?_⟩
  apply addEnd_mul_self_eq_one_of_mulAut_mul_self_eq_one
  exact conjNormal_inv_sq_eq_one_of_sq_mem hAcomm hu2

end FourNuCalculation

section ModTwoReduction

/-- A scalar killed by four in `ZMod (2^e)`, for `e ≥ 3`, is divisible by two. -/
theorem exists_two_mul_of_four_nsmul_eq_zero
    {e : ℕ} (he : 3 ≤ e) (x : ZMod (2 ^ e)) (hx : 4 • x = 0) :
    ∃ y : ZMod (2 ^ e), x = 2 * y := by
  have hpow : 2 ^ e ∣ 4 * x.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    simpa [ZMod.natCast_zmod_val] using hx
  have h8 : 2 ^ 3 ∣ 4 * x.val := (Nat.pow_dvd_pow 2 he).trans hpow
  have h42 : 4 * 2 ∣ 4 * x.val := by
    norm_num at h8 ⊢
    exact h8
  have h2 : 2 ∣ x.val := Nat.dvd_of_mul_dvd_mul_left (by decide) h42
  obtain ⟨y, hy⟩ := h2
  refine ⟨(y : ZMod (2 ^ e)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hy]
  norm_num

abbrev CoefficientRing (e : ℕ) := ZMod (2 ^ e)

abbrev HomocyclicModel (ι : Type*) (e : ℕ) := ι → CoefficientRing e

/-- The submodule `2M` used for reduction modulo two. -/
def twoMultiples (ι : Type*) (e : ℕ) :
    Submodule (CoefficientRing e) (HomocyclicModel ι e) :=
  LinearMap.range ((2 : CoefficientRing e) • LinearMap.id)

theorem exists_two_smul_of_four_nsmul_eq_zero
    {ι : Type*} {e : ℕ}
    (he : 3 ≤ e) (x : HomocyclicModel ι e) (hx : 4 • x = 0) :
    ∃ y : HomocyclicModel ι e, x = (2 : CoefficientRing e) • y := by
  classical
  have hcoord : ∀ i, ∃ y : CoefficientRing e, x i = 2 * y := by
    intro i
    apply exists_two_mul_of_four_nsmul_eq_zero he
    simpa only [Pi.smul_apply, Pi.zero_apply] using congrFun hx i
  choose y hy using hcoord
  refine ⟨y, funext fun i ↦ ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul] using hy i

theorem mem_twoMultiples_of_four_nsmul_eq_zero
    {ι : Type*} {e : ℕ}
    (he : 3 ≤ e) {x : HomocyclicModel ι e} (hx : 4 • x = 0) :
    x ∈ twoMultiples ι e := by
  obtain ⟨y, hy⟩ := exists_two_smul_of_four_nsmul_eq_zero he x hx
  rw [twoMultiples]
  refine ⟨y, ?_⟩
  simpa using hy.symm

theorem twoMultiples_le_comap
    {ι : Type*} {e : ℕ}
    (ν : Module.End (CoefficientRing e) (HomocyclicModel ι e)) :
    twoMultiples ι e ≤ (twoMultiples ι e).comap ν := by
  rintro _ ⟨y, rfl⟩
  refine ⟨ν y, ?_⟩
  simp

theorem quotient_two_nsmul_eq_zero
    {ι : Type*} {e : ℕ}
    (q : HomocyclicModel ι e ⧸ twoMultiples ι e) : 2 • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (twoMultiples ι e) q
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [twoMultiples]
  refine ⟨x, ?_⟩
  change (2 : CoefficientRing e) • x = 2 • x
  exact Nat.cast_smul_eq_nsmul (CoefficientRing e) 2 x

local instance quotientModTwoModule {ι : Type*} {e : ℕ} :
    Module (ZMod 2) (HomocyclicModel ι e ⧸ twoMultiples ι e) :=
  AddCommGroup.zmodModule quotient_two_nsmul_eq_zero

/-- The endomorphism induced by `ν` on `M / 2M`. -/
def modTwoEnd {ι : Type*} {e : ℕ}
    (ν : Module.End (CoefficientRing e) (HomocyclicModel ι e)) :
    Module.End (ZMod 2) (HomocyclicModel ι e ⧸ twoMultiples ι e) :=
  ((twoMultiples ι e).mapQ (twoMultiples ι e) ν
    (twoMultiples_le_comap ν)).toAddMonoidHom.toZModLinearMap 2

@[simp] theorem modTwoEnd_mk
    {ι : Type*} {e : ℕ}
    (ν : Module.End (CoefficientRing e) (HomocyclicModel ι e))
    (x : HomocyclicModel ι e) :
    modTwoEnd ν (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ν x) := by
  simp [modTwoEnd, Submodule.mapQ_apply]

/-- If `4(ν² - ν) = 0`, then the endomorphism induced by `ν` on `M / 2M`
is idempotent. -/
theorem modTwoEnd_idempotent
    {ι : Type*} {e : ℕ}
    (he : 3 ≤ e) (ν : Module.End (CoefficientRing e) (HomocyclicModel ι e))
    (h4 : 4 • (ν * ν - ν) = 0) :
    modTwoEnd ν * modTwoEnd ν = modTwoEnd ν := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (twoMultiples ι e) q
  simp only [Module.End.mul_apply]
  apply (Submodule.Quotient.eq (twoMultiples ι e)).2
  change (ν * ν - ν) x ∈ twoMultiples ι e
  apply mem_twoMultiples_of_four_nsmul_eq_zero he
  have hx := LinearMap.congr_fun h4 x
  simpa using hx

end ModTwoReduction

section CommutingIdempotents

variable {R V ι : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- A finite commuting family of idempotents has a common nonzero vector on
which every member acts as zero or the identity. -/
theorem exists_common_zero_one_vector_finset
    (f : ι → Module.End R V)
    (hidem : ∀ i, IsIdempotentElem (f i))
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    {s : Finset ι} (v₀ : V) (hv₀ : v₀ ≠ 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ i ∈ s, f i v = 0 ∨ f i v = v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨v₀, hv₀, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨v, hv, hvs⟩ := ih
      by_cases hzero : f i v = 0
      · exact ⟨v, hv, by
          intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact Or.inl hzero
          · exact hvs j hj⟩
      · refine ⟨f i v, hzero, ?_⟩
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact Or.inr <| by
            rw [← Module.End.mul_apply, (hidem j).eq]
        · have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
          have hc : Commute (f j) (f i) := hcomm hji
          rcases hvs j hj with hjzero | hjone
          · exact Or.inl <| by
              rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hjzero, map_zero]
          · exact Or.inr <| by
              rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hjone]

theorem exists_common_zero_one_vector [Finite ι] [Nontrivial V]
    (f : ι → Module.End R V)
    (hidem : ∀ i, IsIdempotentElem (f i))
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, f i v = 0 ∨ f i v = v := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  simpa using
    exists_common_zero_one_vector_finset f hidem hcomm
      (s := Finset.univ) v₀ hv₀

end CommutingIdempotents

/-- An endomorphism which sends every vector either to zero or to itself is
zero or the identity. -/
theorem end_eq_zero_or_one_of_apply_eq_zero_or_self
    {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    (f : Module.End R V) (h : ∀ v, f v = 0 ∨ f v = v) :
    f = 0 ∨ f = 1 := by
  classical
  by_cases hf : f = 0
  · exact Or.inl hf
  · right
    have hex : ∃ v, f v ≠ 0 := by
      contrapose! hf
      ext v
      simpa using hf v
    obtain ⟨v, hv⟩ := hex
    have hfv : f v = v := (h v).resolve_left hv
    ext w
    rw [Module.End.one_apply]
    rcases h w with hw | hw
    · have hvw := h (v + w)
      rw [map_add, hfv, hw, add_zero] at hvw
      rcases hvw with hvzero | hvself
      · exact (hv (hfv.trans hvzero)).elim
      · have hwzero : w = 0 := by
          apply add_left_cancel (a := v)
          simpa using hvself
        subst w
        exact map_zero f
    · exact hw

section TransitiveActor

variable {R V ι X : Type*} [Semiring R] [AddCommGroup V] [Module R V]
variable [Group X] [MulAction X ι]

/-- A finite commuting family of idempotents permuted by an actor transitive
on nonzero vectors consists only of zero and identity endomorphisms. -/
theorem all_end_eq_zero_or_one_of_transitive_conjugates
    [Finite ι] [Nontrivial V]
    (ρ : Representation R X V)
    (f : ι → Module.End R V)
    (hidem : ∀ i, IsIdempotentElem (f i))
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hperm : ∀ x i v, ρ x (f i v) = f (x • i) (ρ x v))
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x : X, ρ x v = w) :
    ∀ i, f i = 0 ∨ f i = 1 := by
  obtain ⟨v, hv, heigen⟩ := exists_common_zero_one_vector f hidem hcomm
  intro i
  refine end_eq_zero_or_one_of_apply_eq_zero_or_self (f i) ?_
  intro w
  by_cases hw : w = 0
  · subst w
    exact Or.inl (map_zero (f i))
  · obtain ⟨x, hx⟩ := htrans v w hv hw
    have hp := hperm x (x⁻¹ • i) v
    simp only [smul_smul, mul_inv_cancel, one_smul, hx] at hp
    rcases heigen (x⁻¹ • i) with hz | ho
    · left
      rw [hz, map_zero] at hp
      exact hp.symm
    · right
      rw [ho, hx] at hp
      exact hp.symm

end TransitiveActor

end OddOrder.Higman.Suzuki2Groups
