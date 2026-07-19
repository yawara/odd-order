/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.StdBasis
import OddOrder.GroupTheory.Homocyclic

/-!
# Higman Lemma 3: the one-minus-two endomorphism lift

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
pp. 83--84.

For a homocyclic abelian 2-group, an automorphism equal to the identity
modulo the square subgroup has the form one minus twice a genuine
endomorphism. The square root is chosen only on a ZMod basis and extended
linearly, so no incompatible elementwise choice is made.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory

theorem exists_half_linearMap
    {R ι : Type*} [CommRing R] [Finite ι]
    (f : (ι → R) →ₗ[R] (ι → R))
    (hf : ∀ x, ∃ y, f x = (2 : R) • y) :
    ∃ ν : (ι → R) →ₗ[R] (ι → R), f = (2 : R) • ν := by
  classical
  let b := Pi.basisFun R ι
  choose y hy using fun i => hf (b i)
  let ν : (ι → R) →ₗ[R] (ι → R) := b.constr R y
  refine ⟨ν, b.ext fun i => ?_⟩
  simpa [ν] using hy i

/-- Untag a pointwise product of multiplicative copies of an additive group. -/
def additivePiMultiplicativeEquiv
    {R ι : Type*} [AddGroup R] :
    Additive (ι → Multiplicative R) ≃+ (ι → R) where
  toFun x i := (Additive.toMul x i).toAdd
  invFun x := Additive.ofMul (fun i => Multiplicative.ofAdd (x i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem additivePiMultiplicativeEquiv_apply
    {R ι : Type*} [AddGroup R]
    (x : Additive (ι → Multiplicative R)) (i : ι) :
    additivePiMultiplicativeEquiv x i = (Additive.toMul x i).toAdd :=
  rfl

/-- A homomorphism of a homocyclic group whose values are squares admits a
homomorphic square root.  This is the honest lifting step behind Higman's
notation `1 - 2ν`. -/
theorem exists_monoidHom_square_root_of_homocyclic
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (f : A →* A) (hf : ∀ a, f a ∈ Agemo A 2 1) :
    ∃ ν : A →* A, ∀ a, f a = (ν a) ^ 2 := by
  classical
  let E : Additive A ≃+ (ι → ZMod (2 ^ e)) :=
    (MulEquiv.toAdditive ε).trans additivePiMultiplicativeEquiv
  let gAdd : (ι → ZMod (2 ^ e)) →+ (ι → ZMod (2 ^ e)) :=
    E.toAddMonoidHom.comp (f.toAdditive.comp E.symm.toAddMonoidHom)
  let g : (ι → ZMod (2 ^ e)) →ₗ[ZMod (2 ^ e)] (ι → ZMod (2 ^ e)) :=
    gAdd.toZModLinearMap (2 ^ e)
  have hg : ∀ x, ∃ y, g x = (2 : ZMod (2 ^ e)) • y := by
    intro x
    obtain ⟨y, hy⟩ := (mem_agemo_iff_of_comm.mp (hf (Additive.toMul (E.symm x))))
    refine ⟨E (Additive.ofMul y), ?_⟩
    change E (Additive.ofMul (f (Additive.toMul (E.symm x)))) = _
    rw [hy]
    ext i
    simp [E, two_smul]
    ring
  obtain ⟨νlin, hνlin⟩ := exists_half_linearMap g hg
  let νAdd : Additive A →+ Additive A :=
    E.symm.toAddMonoidHom.comp (νlin.toAddMonoidHom.comp E.toAddMonoidHom)
  let ν : A →* A := νAdd.toMultiplicative
  refine ⟨ν, fun a => ?_⟩
  apply_fun fun z : A => E (Additive.ofMul z)
  have happ := LinearMap.congr_fun hνlin (E (Additive.ofMul a))
  change g (E (Additive.ofMul a)) =
    ((2 : ZMod (2 ^ e)) • νlin) (E (Additive.ofMul a)) at happ
  change E (Additive.ofMul (f a)) = E (Additive.ofMul ((ν a) ^ 2))
  rw [show E (Additive.ofMul (f a)) = g (E (Additive.ofMul a)) by
    simp [g, gAdd]]
  rw [happ]
  have hνapply : E (Additive.ofMul (ν a)) = νlin (E (Additive.ofMul a)) := by
    change E (νAdd (Additive.ofMul a)) = _
    simp [νAdd]
  rw [show Additive.ofMul ((ν a) ^ 2) = 2 • Additive.ofMul (ν a) by rfl,
    map_nsmul, hνapply]
  ext i
  simp [two_smul]


/-- Multiplicative form of Higman’s `α = 1 - 2ν`: an automorphism which is
the identity modulo the square subgroup differs from the identity by twice a
genuine endomorphism. -/
theorem exists_one_sub_two_endomorphism
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (α : MulAut A) (hα : ∀ a, α a * a⁻¹ ∈ Agemo A 2 1) :
    ∃ ν : A →* A, ∀ a, α a = a * ((ν a) ^ 2)⁻¹ := by
  let d : A →* A := (MonoidHom.id A) * α.toMonoidHom⁻¹
  have hd : ∀ a, d a ∈ Agemo A 2 1 := by
    intro a
    have ha := (Agemo A 2 1).inv_mem (hα a)
    simpa [d, mul_comm] using ha
  obtain ⟨ν, hν⟩ := exists_monoidHom_square_root_of_homocyclic ε d hd
  refine ⟨ν, fun a => ?_⟩
  have h := hν a
  dsimp [d] at h
  calc
    α a = a * (a * (α a)⁻¹)⁻¹ := by simp
    _ = a * ((ν a) ^ 2)⁻¹ := by rw [h]


/-- Endomorphism-ring form of the same lift, ready for Higman’s subsequent
calculation with composition squares. -/
theorem exists_addEnd_eq_one_sub_two
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (α : MulAut A) (hα : ∀ a, α a * a⁻¹ ∈ Agemo A 2 1) :
    ∃ ν : AddMonoid.End (Additive A),
      α.toMonoidHom.toAdditive =
        (1 : AddMonoid.End (Additive A)) - 2 • ν := by
  obtain ⟨ν, hν⟩ := exists_one_sub_two_endomorphism ε α hα
  let νAdd : AddMonoid.End (Additive A) := ν.toAdditive
  refine ⟨νAdd, AddMonoidHom.ext fun x => ?_⟩
  have hx := congrArg Additive.ofMul (hν (Additive.toMul x))
  calc
    α.toMonoidHom.toAdditive x = x - 2 • νAdd x := by
      change Additive.ofMul (α (Additive.toMul x)) =
        x - 2 • Additive.ofMul (ν (Additive.toMul x))
      simpa [sub_eq_add_neg, two_nsmul] using hx
    _ = ((1 : AddMonoid.End (Additive A)) -
        (2 • νAdd : AddMonoid.End (Additive A))) x := by
      have hsub := AddMonoidHom.sub_apply
        (1 : AddMonoid.End (Additive A))
        (2 • νAdd : AddMonoid.End (Additive A)) x
      have hone : (1 : AddMonoid.End (Additive A)) x = x :=
        AddMonoid.End.one_apply x
      have hn : (2 • νAdd : AddMonoid.End (Additive A)) x = 2 • νAdd x :=
        AddMonoidHom.nsmul_apply νAdd 2 x
      calc
        x - 2 • νAdd x =
            (1 : AddMonoid.End (Additive A)) x -
              (2 • νAdd : AddMonoid.End (Additive A)) x := by
          rw [hone, hn]
        _ = ((1 : AddMonoid.End (Additive A)) -
            (2 • νAdd : AddMonoid.End (Additive A))) x := hsub.symm

end OddOrder.Higman.Suzuki2Groups
