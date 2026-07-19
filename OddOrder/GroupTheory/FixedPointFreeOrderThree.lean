/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Group

/-!
# Fixed-point-free automorphisms of order three

This file develops the elementary commutator calculus behind the theorem of
B. H. Neumann that a finite group admitting a fixed-point-free automorphism of
order three has nilpotency class at most two.

The first layer is Burnside's holomorph argument.  Burnside, *Theory of Groups
of Finite Order* (2nd ed., 1911), §160, observes that if an automorphism `J`
fixes no nonidentity element, then every element of the nontrivial holomorph
coset is conjugate to `J`.  For order three, the norm identity
`x * φ x * φ² x = 1` first gives `Commute x (φ x)`.  Conjugating `φ` inside
`MulAut G` and using surjectivity of the displacement map `x ↦ x / φ x` then
gives the right 2-Engel identity `⁅⁅x,y⁆,y⁆ = 1`.

The remaining Hopkins--Levi step (triple commutators have exponent dividing
three) is treated below using the identities recorded in Gallego--Hauck--
Pérez-Ramos, *2-Engel Relations between Subgroups*, Proposition 3.3 and
Corollary 3.5.  Combining it with the orbit congruence `3 ∤ |G|` yields the
class-two conclusion used by Higman, *Suzuki 2-groups*, Lemma 6.
-/

namespace OddOrder.GroupTheory

open Function
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- If `φ` is fixed-point-free and has order three, every element commutes with
its image under `φ`.

Apply the fixed-point-free norm identity to `x` and `x⁻¹`.  Inverting the
second identity reverses the two non-`x` factors, so `φ x` commutes with
`φ² x`; applying `φ⁻¹` gives the stated relation. -/
theorem commute_apply_of_fixedPointFree_orderOf_eq_three
    (φ : MulAut G) (hφ : MonoidHom.FixedPointFree φ)
    (horder : orderOf φ = 3) (x : G) :
    Commute x (φ x) := by
  have hpow : φ ^ 3 = 1 := by
    simpa [horder] using pow_orderOf_eq_one φ
  have h3 : (φ : G → G)^[3] = _root_.id := by
    have hpow' : φ.toEquiv ^ 3 = 1 := congrArg MulEquiv.toEquiv hpow
    exact congrArg DFunLike.coe hpow'
  have hnorm : x * (φ x * φ^[2] x) = 1 := by
    simpa [List.range_succ, Function.iterate_succ_apply] using
      hφ.prod_pow_eq_one h3 x
  have hnorm_inv : x⁻¹ * ((φ x)⁻¹ * (φ^[2] x)⁻¹) = 1 := by
    simpa [List.range_succ, Function.iterate_succ_apply] using
      hφ.prod_pow_eq_one h3 x⁻¹
  have hab : φ x * φ^[2] x = x⁻¹ :=
    eq_inv_of_mul_eq_one_right hnorm
  have hba : φ^[2] x * φ x = x⁻¹ := by
    have hinv := congrArg Inv.inv hnorm_inv
    have hrev : φ^[2] x * (φ x * x) = 1 := by
      simpa [mul_inv_rev, mul_assoc] using hinv
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using hrev)
  have hc : Commute (φ x) (φ^[2] x) := hab.trans hba.symm
  simpa [Function.iterate_succ_apply] using hc.map φ⁻¹

/-- Every conjugate of `φ y` commutes with `y`.

Surjectivity of `x ↦ x / φ x` writes the conjugating element as a displacement.
Conjugating `φ` by the corresponding inner automorphism produces an order-three
fixed-point-free automorphism whose value at `y` is the required conjugate. -/
theorem commute_conjugate_apply_of_fixedPointFree_orderOf_eq_three
    (φ : MulAut G) (hφ : MonoidHom.FixedPointFree φ)
    (horder : orderOf φ = 3) (x y : G) :
    Commute y (x * φ y * x⁻¹) := by
  obtain ⟨g, hg⟩ := hφ.commutatorMap_surjective x
  let c : MulAut G := MulAut.conj g
  let ψ : MulAut G := c * φ * c⁻¹
  have hsemi : SemiconjBy c φ ψ := by
    simp [SemiconjBy, ψ, mul_assoc]
  have hψorder : orderOf ψ = 3 :=
    (SemiconjBy.orderOf_eq c hsemi).symm.trans horder
  have hψ : MonoidHom.FixedPointFree ψ := by
    intro z hz
    have hz' : φ (c⁻¹ z) = c⁻¹ z := by
      simpa [ψ] using congrArg (fun w ↦ c⁻¹ w) hz
    have hcz : c⁻¹ z = 1 := hφ _ hz'
    simpa using congrArg (fun w ↦ c w) hcz
  have hyψ : Commute y (ψ y) :=
    commute_apply_of_fixedPointFree_orderOf_eq_three ψ hψ hψorder y
  rw [← hg]
  simpa [ψ, c, MulAut.conj_apply, MonoidHom.commutatorMap_apply,
    division_def, map_inv, mul_assoc] using hyψ

/-- Every conjugate of `φ⁻¹ y` also commutes with `y`. -/
theorem commute_conjugate_inv_apply_of_fixedPointFree_orderOf_eq_three
    (φ : MulAut G) (hφ : MonoidHom.FixedPointFree φ)
    (horder : orderOf φ = 3) (x y : G) :
    Commute y (x * φ⁻¹ y * x⁻¹) := by
  have h :=
    (commute_conjugate_apply_of_fixedPointFree_orderOf_eq_three
      φ hφ horder x⁻¹ (φ⁻¹ y)).map (MulAut.conj x)
  simpa [MulAut.conj_apply, mul_assoc] using h.symm

/-- **Burnside's right 2-Engel bridge.**  In a finite group admitting a
fixed-point-free automorphism of order three, `y` commutes with every conjugate
`x⁻¹ * y * x`.

Both `φ z` and `φ⁻¹ z` commute with `y`, where `z = x⁻¹ * y * x`.  The norm
identity expresses `z` as the product of their inverses. -/
theorem commute_conjugate_self_of_fixedPointFree_orderOf_eq_three
    (φ : MulAut G) (hφ : MonoidHom.FixedPointFree φ)
    (horder : orderOf φ = 3) (x y : G) :
    Commute y (x⁻¹ * y * x) := by
  let z : G := x⁻¹ * y * x
  have hplus : Commute y (φ z) := by
    have h := commute_conjugate_apply_of_fixedPointFree_orderOf_eq_three
      φ hφ horder (φ x)⁻¹ y
    simpa [z, map_mul, map_inv, mul_assoc] using h
  have hminus : Commute y (φ⁻¹ z) := by
    have h := commute_conjugate_inv_apply_of_fixedPointFree_orderOf_eq_three
      φ hφ horder (φ⁻¹ x)⁻¹ y
    simpa [z, map_mul, map_inv, mul_assoc] using h
  have hpow : φ ^ 3 = 1 := by
    simpa [horder] using pow_orderOf_eq_one φ
  have h3 : (φ : G → G)^[3] = _root_.id := by
    have hpow' : φ.toEquiv ^ 3 = 1 := congrArg MulEquiv.toEquiv hpow
    exact congrArg DFunLike.coe hpow'
  have htwo (w : G) : φ^[2] w = φ⁻¹ w := by
    apply φ.injective
    have hw := congrFun h3 w
    simpa [Function.iterate_succ_apply] using hw
  have hsecond : Commute y (φ^[2] z) := by
    rw [htwo]
    exact hminus
  have hnorm : z * (φ z * φ^[2] z) = 1 := by
    simpa [List.range_succ, Function.iterate_succ_apply] using
      hφ.prod_pow_eq_one h3 z
  have hz : z = (φ^[2] z)⁻¹ * (φ z)⁻¹ := by
    have hz' := eq_inv_of_mul_eq_one_left hnorm
    simpa [mul_inv_rev] using hz'
  change Commute y z
  rw [hz]
  exact hsecond.inv_right.mul_right hplus.inv_right

omit [Finite G] in
/-- The conjugate-commuting form of the right 2-Engel law implies the usual
left-normed commutator equation `⁅⁅x,y⁆,y⁆ = 1`. -/
theorem rightTwoEngel_of_commute_conjugate
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x)) :
    ∀ x y : G, ⁅⁅x, y⁆, y⁆ = 1 := by
  intro x y
  have hconj : Commute (x * y * x⁻¹) y := by
    simpa only [inv_inv] using (h x⁻¹ y).symm
  apply Commute.commutator_eq
  simpa only [commutatorElement_def, mul_assoc] using
    hconj.mul_left (Commute.refl y).inv_left

/-!
## The Hopkins--Levi exponent-three calculation

We use mathlib's convention `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`.  This is the
opposite of the convention in Gallego--Hauck--Pérez-Ramos, Proposition 3.3
and Corollary 3.5, so the identities below are proved directly in mathlib's
convention.  The argument is the same linearization of the right 2-Engel law,
followed by the Hall--Witt identity.
-/

omit [Finite G] in
private theorem commute_conjugates_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a x y : G) :
    Commute (x⁻¹ * a * x) (y⁻¹ * a * y) := by
  have hz := (h (y * x⁻¹) a).map (MulAut.conj x⁻¹)
  simpa [MulAut.conj_apply, mul_assoc] using hz

omit [Finite G] in
private theorem commute_commutators_same_left_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b c : G) :
    Commute ⁅a, b⁆ ⁅a, c⁆ := by
  have haa : Commute a a := Commute.refl a
  have hab : Commute a (b * a⁻¹ * b⁻¹) := by
    simpa [mul_assoc] using (h b⁻¹ a).inv_right
  have hac : Commute a (c * a⁻¹ * c⁻¹) := by
    simpa [mul_assoc] using (h c⁻¹ a).inv_right
  have hbc : Commute (b * a⁻¹ * b⁻¹) (c * a⁻¹ * c⁻¹) := by
    simpa [mul_assoc] using
      (commute_conjugates_of_commute_conjugate_self h a⁻¹ b⁻¹ c⁻¹)
  rw [commutatorElement_def, commutatorElement_def]
  simpa [mul_assoc] using
    (haa.mul_left hab.symm).mul_right (hac.mul_left hbc)

omit [Finite G] in
private theorem commutator_commute_right_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b : G) :
    Commute ⁅a, b⁆ b := by
  have hconj : Commute (a * b * a⁻¹) b := by
    simpa only [inv_inv] using (h a⁻¹ b).symm
  apply commutatorElement_eq_one_iff_commute.mp
  apply Commute.commutator_eq
  simpa only [commutatorElement_def, mul_assoc] using
    hconj.mul_left (Commute.refl b).inv_left

omit [Finite G] in
private theorem commutator_commute_left_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b : G) :
    Commute ⁅a, b⁆ a := by
  have he := commutator_commute_right_of_commute_conjugate_self h b a
  rw [← commutatorElement_inv] at he
  simpa using he.inv_left

omit [Finite G] in
private theorem triple_commutator_swap_last_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b c : G) :
    ⁅⁅a, c⁆, b⁆ = ⁅⁅a, b⁆, c⁆⁻¹ := by
  let A : G := ⁅a, b⁆
  let C : G := ⁅a, c⁆
  have hAb : Commute A b :=
    commutator_commute_right_of_commute_conjugate_self h a b
  have hCc : Commute C c :=
    commutator_commute_right_of_commute_conjugate_self h a c
  have hAC : Commute A C :=
    commute_commutators_same_left_of_commute_conjugate_self h a b c
  have hE : Commute (A * b * C * b⁻¹) (b * c) := by
    simpa [A, C, commutatorElement_mul_right_eq_mul_conj, mul_assoc] using
      commutator_commute_right_of_commute_conjugate_self h a (b * c)
  have hEq := hE.eq
  group at hEq
  have hbA : b⁻¹ * A * b = A := by
    calc
      b⁻¹ * A * b = b⁻¹ * (A * b) := by group
      _ = b⁻¹ * (b * A) := by rw [hAb.eq]
      _ = A := by group
  have hIso : b * C * b⁻¹ = A⁻¹ * c⁻¹ * A * c * C := by
    calc
      b * C * b⁻¹ =
          A⁻¹ * c⁻¹ * b⁻¹ * (b * c * A * b * C * b⁻¹) := by group
      _ = A⁻¹ * c⁻¹ * b⁻¹ * (A * b * C * c) := by
        simpa only [zpow_neg_one] using
          congrArg (fun w : G ↦ A⁻¹ * c⁻¹ * b⁻¹ * w) hEq.symm
      _ = A⁻¹ * c⁻¹ * A * C * c := by
        calc
          A⁻¹ * c⁻¹ * b⁻¹ * (A * b * C * c) =
              A⁻¹ * c⁻¹ * (b⁻¹ * A * b) * C * c := by group
          _ = A⁻¹ * c⁻¹ * A * C * c := by rw [hbA]
      _ = A⁻¹ * c⁻¹ * A * c * C := by
        simpa only [mul_assoc] using
          congrArg (fun w : G ↦ A⁻¹ * c⁻¹ * A * w) hCc.eq
  let T : G := ⁅A, c⁆
  have hTA : Commute T A :=
    commutator_commute_left_of_commute_conjugate_self h A c
  have hTc : Commute T c :=
    commutator_commute_right_of_commute_conjugate_self h A c
  have hAc : A * c = T * c * A := by
    simp only [T, commutatorElement_def]
    group
  have hK : A⁻¹ * c⁻¹ * A * c = T := by
    have hcT : c⁻¹ * T * c = T := by
      calc
        c⁻¹ * T * c = c⁻¹ * (T * c) := by group
        _ = c⁻¹ * (c * T) := by rw [hTc.eq]
        _ = T := by group
    have hAT : A⁻¹ * T * A = T := by
      calc
        A⁻¹ * T * A = A⁻¹ * (T * A) := by group
        _ = A⁻¹ * (A * T) := by rw [hTA.eq]
        _ = T := by group
    calc
      A⁻¹ * c⁻¹ * A * c = A⁻¹ * c⁻¹ * (T * c * A) := by
        simpa only [mul_assoc] using
          congrArg (fun w : G ↦ A⁻¹ * c⁻¹ * w) hAc
      _ = A⁻¹ * (c⁻¹ * T * c) * A := by group
      _ = A⁻¹ * T * A := by rw [hcT]
      _ = T := hAT
  have hbC : ⁅b, C⁆ = T := by
    rw [commutatorElement_def, hIso, hK]
    group
  change ⁅C, b⁆ = T⁻¹
  calc
    ⁅C, b⁆ = ⁅b, C⁆⁻¹ := (commutatorElement_inv b C).symm
    _ = T⁻¹ := congrArg Inv.inv hbC

omit [Finite G] in
private theorem triple_commutator_swap_first_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b c : G) :
    ⁅⁅b, a⁆, c⁆ = ⁅⁅a, b⁆, c⁆⁻¹ := by
  let A : G := ⁅a, b⁆
  let T : G := ⁅A, c⁆
  have hTA : Commute T A :=
    commutator_commute_left_of_commute_conjugate_self h A c
  change ⁅⁅b, a⁆, c⁆ = T⁻¹
  rw [← commutatorElement_inv a b]
  rw [commutatorElement_inv_left A c]
  rw [← commutatorElement_inv A c]
  change A⁻¹ * T⁻¹ * A = T⁻¹
  calc
    A⁻¹ * T⁻¹ * A = A⁻¹ * (T⁻¹ * A) := by group
    _ = A⁻¹ * (A * T⁻¹) := by rw [(hTA.inv_left).eq]
    _ = T⁻¹ := by group

omit [Finite G] in
private theorem triple_commutator_cyclic_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b c : G) :
    ⁅⁅a, b⁆, c⁆ = ⁅⁅b, c⁆, a⁆ := by
  calc
    ⁅⁅a, b⁆, c⁆ = (⁅⁅a, b⁆, c⁆⁻¹)⁻¹ := (inv_inv _).symm
    _ = ⁅⁅b, a⁆, c⁆⁻¹ :=
      congrArg Inv.inv
        (triple_commutator_swap_first_of_commute_conjugate_self h a b c).symm
    _ = ⁅⁅b, c⁆, a⁆ :=
      (triple_commutator_swap_last_of_commute_conjugate_self h b a c).symm

omit [Finite G] in
private theorem triple_commutator_commute_second_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b c : G) :
    Commute ⁅⁅a, b⁆, c⁆ b := by
  rw [triple_commutator_cyclic_of_commute_conjugate_self h a b c,
    triple_commutator_cyclic_of_commute_conjugate_self h b c a]
  exact commutator_commute_right_of_commute_conjugate_self h ⁅c, a⁆ b

omit [Finite G] in
private theorem triple_commutator_conjugated_last_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b c : G) :
    ⁅⁅a, b⁆, b * c * b⁻¹⁆ = ⁅⁅a, b⁆, c⁆ := by
  let A : G := ⁅a, b⁆
  let T : G := ⁅A, c⁆
  have hAb : Commute A b :=
    commutator_commute_right_of_commute_conjugate_self h a b
  have hTb : Commute T b :=
    triple_commutator_commute_second_of_commute_conjugate_self h a b c
  have hbA : b * A * b⁻¹ = A := by
    calc
      b * A * b⁻¹ = (b * A) * b⁻¹ := by group
      _ = (A * b) * b⁻¹ := by rw [hAb.eq.symm]
      _ = A := by group
  have hbT : b * T * b⁻¹ = T := by
    calc
      b * T * b⁻¹ = (b * T) * b⁻¹ := by group
      _ = (T * b) * b⁻¹ := by rw [hTb.eq.symm]
      _ = T := by group
  change ⁅A, b * c * b⁻¹⁆ = T
  calc
    ⁅A, b * c * b⁻¹⁆ =
        ⁅b * A * b⁻¹, b * c * b⁻¹⁆ := by rw [hbA]
    _ = b * T * b⁻¹ := (conjugate_commutatorElement A c b).symm
    _ = T := hbT

omit [Finite G] in
/-- **Hopkins--Levi exponent-three identity.**  If every element commutes with
all of its conjugates, every left-normed triple commutator has cube one.

This is the `A = B = G` specialization of Gallego--Hauck--Pérez-Ramos,
Corollary 3.5.  The proof linearizes the right 2-Engel identity and then
specializes the Hall--Witt identity. -/
theorem tripleCommutator_cube_of_commute_conjugate_self
    (h : ∀ x y : G, Commute y (x⁻¹ * y * x))
    (a b c : G) :
    ⁅⁅a, b⁆, c⁆ ^ 3 = 1 := by
  have hHW := commutatorElement_commutatorElement_conj_mul a b c
  rw [triple_commutator_conjugated_last_of_commute_conjugate_self h a b c,
    triple_commutator_conjugated_last_of_commute_conjugate_self h b c a,
    triple_commutator_conjugated_last_of_commute_conjugate_self h c a b] at hHW
  have h2 : ⁅⁅b, c⁆, a⁆ = ⁅⁅a, b⁆, c⁆ :=
    (triple_commutator_cyclic_of_commute_conjugate_self h a b c).symm
  have h3 : ⁅⁅c, a⁆, b⁆ = ⁅⁅a, b⁆, c⁆ :=
    ((triple_commutator_cyclic_of_commute_conjugate_self h a b c).trans
      (triple_commutator_cyclic_of_commute_conjugate_self h b c a)).symm
  rw [h2, h3] at hHW
  simpa [pow_succ] using hHW

omit [Finite G] in
/-- If all triple commutators have cube one and three does not divide the
cardinality, then the lower central series stops after the commutator subgroup.

The order of each triple commutator divides both `3` and `|G|`, hence is
one.  The statement deliberately does not assume `Finite G`: the cardinality
hypothesis itself excludes mathlib's infinite-cardinality value `0`. -/
theorem lowerCentralSeries_two_eq_bot_of_tripleCommutator_cube
    (hcard : ¬ 3 ∣ Nat.card G)
    (hCube : ∀ x y z : G, ⁅⁅x, y⁆, z⁆ ^ 3 = 1) :
    (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥ := by
  apply Subgroup.lowerCentralSeries_succ_eq_bot
  rw [Subgroup.top_lowerCentralSeries_one, commutator_eq_closure,
    Subgroup.closure_le]
  rintro _ ⟨x, y, rfl⟩
  refine Subgroup.mem_center_iff.mpr ?_
  intro z
  have htriple : ⁅⁅x, y⁆, z⁆ = 1 := by
    apply orderOf_eq_one_iff.mp
    have hord3 : orderOf ⁅⁅x, y⁆, z⁆ ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (hCube x y z)
    have hordcard : orderOf ⁅⁅x, y⁆, z⁆ ∣ Nat.card G :=
      orderOf_dvd_natCard _
    have hcop : Nat.Coprime 3 (Nat.card G) :=
      (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hcard
    exact Nat.eq_one_of_dvd_coprimes hcop hord3 hordcard
  exact (commutatorElement_eq_one_iff_mul_comm.mp htriple).symm

/-- A fixed-point-free automorphism of order three makes the finite group
right 2-Engel. -/
theorem rightTwoEngel_of_fixedPointFree_orderOf_eq_three
    (φ : MulAut G) (hφ : MonoidHom.FixedPointFree φ)
    (horder : orderOf φ = 3) :
    ∀ x y : G, ⁅⁅x, y⁆, y⁆ = 1 :=
  rightTwoEngel_of_commute_conjugate
    (commute_conjugate_self_of_fixedPointFree_orderOf_eq_three φ hφ horder)

/-- A finite group admitting a fixed-point-free automorphism of order three
has cardinality prime to three.

Indeed, the cyclic subgroup `⟨φ⟩` is a `3`-group acting on `G`.  If `3`
divided `|G|`, the p-group fixed-point congruence would produce a second fixed
point besides `1`, contradicting fixed-point-freeness. -/
theorem three_not_dvd_natCard_of_fixedPointFree_orderOf_eq_three
    (φ : MulAut G) (hφ : MonoidHom.FixedPointFree φ)
    (horder : orderOf φ = 3) :
    ¬ 3 ∣ Nat.card G := by
  intro hthree
  let P : Subgroup (MulAut G) := Subgroup.zpowers φ
  have hP : IsPGroup 3 P := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card (Subgroup.zpowers φ) = 3 ^ 1
    rw [Nat.card_zpowers, horder, pow_one]
  have h1 : (1 : G) ∈ MulAction.fixedPoints P G := by
    rw [MulAction.mem_fixedPoints]
    intro p
    change (p : MulAut G) 1 = 1
    exact map_one _
  obtain ⟨b, hb, hbne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := G) hthree h1
  have hbφ := (MulAction.mem_fixedPoints.mp hb)
    (⟨φ, Subgroup.mem_zpowers φ⟩ : P)
  have hfix : φ b = b := hbφ
  exact hbne (hφ b hfix).symm

/-- **B. H. Neumann's order-three theorem (finite-group form).**  A finite
group admitting a fixed-point-free automorphism of order three has nilpotency
class at most two.

The conclusion is expressed as `γ₃(G) = 1`, avoiding the junk value of
`nilpotencyClass` for a nonnilpotent group.  This is the result invoked by
Higman, *Suzuki 2-groups*, Lemma 6. -/
theorem lowerCentralSeries_two_eq_bot_of_fixedPointFree_orderOf_eq_three
    (φ : MulAut G) (hφ : MonoidHom.FixedPointFree φ)
    (horder : orderOf φ = 3) :
    (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥ := by
  apply lowerCentralSeries_two_eq_bot_of_tripleCommutator_cube
    (three_not_dvd_natCard_of_fixedPointFree_orderOf_eq_three φ hφ horder)
  exact tripleCommutator_cube_of_commute_conjugate_self
    (commute_conjugate_self_of_fixedPointFree_orderOf_eq_three φ hφ horder)

end OddOrder.GroupTheory
