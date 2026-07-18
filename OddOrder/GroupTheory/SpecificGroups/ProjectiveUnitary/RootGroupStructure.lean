/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.GeneratedAction

/-!
# Structural properties of the unitary root group

For `q = 2 ^ n`, this file proves the structural facts about the standard
Hermitian root group used in the unitary case of Peterfalvi's induction:

* an element `(a, b)` has square `(0, a * star a)`, so the square-one line is
  exactly the subgroup with first coordinate zero;
* this line is central, is parametrized by the fixed field, and has order `q`;
* the full root group has order `q³` and is noncommutative;
* the canonical central involution `s = (0, 1)` and the Weyl element `t`
  satisfy `tst = sts`, and `st` has order three.

These are the concrete unitary-root calculations required by **Peterfalvi,
Part II, Chapter I §3, Proposition 1(c)** (pp. 104–106).  The coordinates
and Weyl action come from Peterfalvi, Part II, Chapter III §3 (pp. 119–121).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

noncomputable section

section /- Part II, Chapter III §3: the root group's square-one line -/

namespace RootGroup

variable {n : ℕ}

/-- The first coordinate of every square in the Hermitian root group is zero. -/
@[simp]
theorem sq_fst (x : RootGroup n) : (x ^ 2).fst = 0 := by
  rw [pow_two, fst_mul]
  exact CharTwo.add_self_eq_zero x.fst

/-- The second coordinate of a square is the Hermitian norm of the first
coordinate. -/
@[simp]
theorem sq_snd (x : RootGroup n) :
    (x ^ 2).snd = x.fst * star x.fst := by
  rw [pow_two, snd_mul, CharTwo.add_self_eq_zero, zero_add]

/-- A Hermitian root element has square one exactly when its first coordinate
vanishes. -/
theorem sq_eq_one_iff_fst_eq_zero (x : RootGroup n) :
    x ^ 2 = 1 ↔ x.fst = 0 := by
  constructor
  · intro hx
    have hsnd := congrArg RootGroup.snd hx
    rw [sq_snd, snd_one] at hsnd
    exact (mul_eq_zero.mp hsnd).elim id (fun h => star_eq_zero.mp h)
  · intro hx
    ext
    · simp
    · rw [sq_snd, hx, zero_mul, snd_one]

/-- The central square-one line in the Hermitian root group. -/
noncomputable def centerLine (n : ℕ) : Subgroup (RootGroup n) where
  carrier := {x | x.fst = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    simpa using congrArg₂ (· + ·) hx hy
  inv_mem' := by
    intro x hx
    exact hx

@[simp]
theorem mem_centerLine (x : RootGroup n) :
    x ∈ centerLine n ↔ x.fst = 0 := Iff.rfl

/-- Membership in the central line is equivalent to having square one. -/
theorem mem_centerLine_iff_sq_eq_one (x : RootGroup n) :
    x ∈ centerLine n ↔ x ^ 2 = 1 := by
  rw [mem_centerLine, sq_eq_one_iff_fst_eq_zero]

/-- The square-one line is contained in the center of the Hermitian root
group. -/
theorem centerLine_le_center :
    centerLine n ≤ Subgroup.center (RootGroup n) := by
  intro z hz
  change z.fst = 0 at hz
  rw [Subgroup.mem_center_iff]
  intro x
  ext
  · simp [hz]
  · simp [hz, add_comm]

/-- The central line is parametrized by the fixed field of quadratic
conjugation. -/
noncomputable def centerLineEquivFixed (n : ℕ) :
    centerLine n ≃ {b : Field n // star b = b} where
  toFun x := ⟨x.1.snd, by
    have h := x.1.condition
    rw [x.2, zero_mul] at h
    exact (CharTwo.add_eq_zero.mp h).symm⟩
  invFun b := ⟨⟨0, b.1, by rw [b.2, CharTwo.add_self_eq_zero, zero_mul]⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    ext
    · exact x.2.symm
    · rfl
  right_inv _ := rfl

/-- The central square-one line has exact order `q = 2 ^ n`. -/
theorem natCard_centerLine (n : ℕ) (hn : 0 < n) :
    Nat.card (centerLine n) = 2 ^ n := by
  rw [Nat.card_congr (centerLineEquivFixed n), natCard_fixedByConjugation n hn]

/-- For positive `n`, the Hermitian root group is noncommutative. -/
theorem not_isMulCommutative (n : ℕ) (hn : 0 < n) :
    ¬ IsMulCommutative (RootGroup n) := by
  intro hcomm
  obtain ⟨c, hc⟩ := exists_not_fixed_conjugation n hn
  let x := withFirst n 1
  let y := withFirst n c
  have hxy := congrArg RootGroup.snd (isMulCommutative_iff.mp hcomm x y)
  apply hc
  simp only [snd_mul, x, y, withFirst_fst, one_mul, star_one, mul_one] at hxy
  linear_combination hxy

/-- The canonical nontrivial element `s = (0, 1)` of the central line. -/
def centralInvolution (n : ℕ) : RootGroup n where
  fst := 0
  snd := 1
  condition := by
    simpa using CharTwo.add_self_eq_zero (1 : Field n)

@[simp]
theorem centralInvolution_fst (n : ℕ) :
    (centralInvolution n).fst = 0 := rfl

@[simp]
theorem centralInvolution_snd (n : ℕ) :
    (centralInvolution n).snd = 1 := rfl

theorem centralInvolution_mem_centerLine (n : ℕ) :
    centralInvolution n ∈ centerLine n := rfl

/-- The canonical central involution is nontrivial. -/
theorem centralInvolution_ne_one (n : ℕ) : centralInvolution n ≠ 1 := by
  rw [ne_one_iff_snd_ne_zero]
  simp

/-- The canonical central involution has square one. -/
@[simp]
theorem centralInvolution_sq (n : ℕ) : centralInvolution n ^ 2 = 1 := by
  exact (sq_eq_one_iff_fst_eq_zero (centralInvolution n)).2 rfl

@[simp]
theorem centralInvolution_mul_fst (u : RootGroup n) :
    (centralInvolution n * u).fst = u.fst := by
  simp

@[simp]
theorem centralInvolution_mul_snd (u : RootGroup n) :
    (centralInvolution n * u).snd = u.snd + 1 := by
  simp only [snd_mul, centralInvolution_snd, centralInvolution_fst,
    zero_mul, add_zero]
  exact add_comm 1 u.snd

@[simp]
theorem weylReciprocal_centralInvolution (n : ℕ) :
    weylReciprocal (centralInvolution n) (centralInvolution_ne_one n) =
      centralInvolution n := by
  ext <;> simp

end RootGroup

end

section /- Part II, Chapter I §3: the standard involution-Weyl pair -/

open RootGroup

/-- For the canonical root involution `s` and Weyl element `t`, the standard
unitary action satisfies the braid relation `tst = sts`. -/
theorem standard_braid (n : ℕ) :
    weylElement n * rootHom n (centralInvolution n) * weylElement n =
      rootHom n (centralInvolution n) * weylElement n *
        rootHom n (centralInvolution n) := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro p
  cases p with
  | none =>
      change Unital.weylPerm n
          (Unital.rootPerm (centralInvolution n)
            (Unital.weylPerm n (Unital.infinity n))) =
        Unital.rootPerm (centralInvolution n)
          (Unital.weylPerm n
            (Unital.rootPerm (centralInvolution n) (Unital.infinity n)))
      rw [Unital.weylPerm_infinity, Unital.rootPerm_affine, mul_one,
        Unital.weylPerm_affine_of_ne_one _ (centralInvolution_ne_one n),
        RootGroup.weylReciprocal_centralInvolution,
        Unital.rootPerm_infinity, Unital.weylPerm_infinity,
        Unital.rootPerm_affine, mul_one]
  | some u =>
      by_cases hu0 : u = 1
      · subst u
        have hzz : centralInvolution n * centralInvolution n = 1 := by
          simpa only [pow_two] using centralInvolution_sq n
        change Unital.weylPerm n
            (Unital.rootPerm (centralInvolution n)
              (Unital.weylPerm n (Unital.affine 1))) =
          Unital.rootPerm (centralInvolution n)
            (Unital.weylPerm n
              (Unital.rootPerm (centralInvolution n) (Unital.affine 1)))
        rw [Unital.weylPerm_origin, Unital.rootPerm_infinity,
          Unital.weylPerm_infinity, Unital.rootPerm_affine, mul_one,
          Unital.weylPerm_affine_of_ne_one _ (centralInvolution_ne_one n),
          RootGroup.weylReciprocal_centralInvolution,
          Unital.rootPerm_affine, hzz]
      · by_cases huz : u = centralInvolution n
        · subst u
          have hzz : centralInvolution n * centralInvolution n = 1 := by
            simpa only [pow_two] using centralInvolution_sq n
          change Unital.weylPerm n
              (Unital.rootPerm (centralInvolution n)
                (Unital.weylPerm n (Unital.affine (centralInvolution n)))) =
            Unital.rootPerm (centralInvolution n)
              (Unital.weylPerm n
                (Unital.rootPerm (centralInvolution n)
                  (Unital.affine (centralInvolution n))))
          rw [Unital.weylPerm_affine_of_ne_one _ (centralInvolution_ne_one n),
            RootGroup.weylReciprocal_centralInvolution,
            Unital.rootPerm_affine, hzz, Unital.weylPerm_origin,
            Unital.rootPerm_infinity]
        · have hb0 : u.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero u).mp hu0
          have hb1 : u.snd + 1 ≠ 0 := by
            intro h
            have hsnd : u.snd = 1 := by
              calc
                u.snd = (u.snd + 1) + 1 := by
                  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
                _ = 0 + 1 := by rw [h]
                _ = 1 := zero_add (1 : Field n)
            apply huz
            ext
            · have hprod : u.fst * star u.fst = 0 := by
                rw [← u.condition, hsnd, star_one, CharTwo.add_self_eq_zero]
              exact (mul_eq_zero.mp hprod).elim id (fun h => star_eq_zero.mp h)
            · exact hsnd
          have hrec : 1 / u.snd + 1 ≠ 0 := by
            rw [show 1 / u.snd + 1 = (1 + u.snd) / u.snd by field_simp]
            exact div_ne_zero (by simpa [add_comm] using hb1) hb0
          have hzu : centralInvolution n * u ≠ 1 := by
            rw [RootGroup.ne_one_iff_snd_ne_zero]
            simpa only [RootGroup.centralInvolution_mul_snd] using hb1
          have hzw : centralInvolution n * RootGroup.weylReciprocal u hu0 ≠ 1 := by
            rw [RootGroup.ne_one_iff_snd_ne_zero]
            simpa only [RootGroup.centralInvolution_mul_snd,
              RootGroup.weylReciprocal_snd] using hrec
          change Unital.weylPerm n
              (Unital.rootPerm (centralInvolution n)
                (Unital.weylPerm n (Unital.affine u))) =
            Unital.rootPerm (centralInvolution n)
              (Unital.weylPerm n
                (Unital.rootPerm (centralInvolution n) (Unital.affine u)))
          rw [Unital.weylPerm_affine_of_ne_one u hu0,
            Unital.rootPerm_affine,
            Unital.weylPerm_affine_of_ne_one _ hzw,
            Unital.rootPerm_affine,
            Unital.weylPerm_affine_of_ne_one _ hzu,
            Unital.rootPerm_affine]
          rw [Unital.affine_inj]
          have hsb0 : star u.snd ≠ 0 :=
            (star_ne_zero (R := Field n)).2 hb0
          have hsb1 : star (u.snd + 1) ≠ 0 :=
            (star_ne_zero (R := Field n)).2 hb1
          ext
          · simp only [RootGroup.weylReciprocal_fst,
              RootGroup.weylReciprocal_snd,
              RootGroup.centralInvolution_mul_fst,
              RootGroup.centralInvolution_mul_snd, star_add, star_one,
              star_div₀]
            field_simp [hb0, hb1, hsb0, hsb1]
            exact congrArg (fun x : Field n => u.fst / x)
              (add_comm 1 (star u.snd))
          · simp only [RootGroup.weylReciprocal_snd,
              RootGroup.centralInvolution_mul_snd]
            have hsum : 1 + u.snd ≠ 0 := by
              simpa [add_comm] using hb1
            calc
              1 / (1 / u.snd + 1) = u.snd / (1 + u.snd) := by
                field_simp [hb0, hsum]
              _ = u.snd / (u.snd + 1) := by rw [add_comm 1 u.snd]
              _ = (1 + (u.snd + 1)) / (u.snd + 1) := by
                congr 1
                calc
                  u.snd = u.snd + (1 + 1) := by
                    rw [CharTwo.add_self_eq_zero, add_zero]
                  _ = 1 + (u.snd + 1) := by ring
              _ = 1 / (u.snd + 1) + (u.snd + 1) / (u.snd + 1) := by
                rw [add_div]
              _ = 1 / (u.snd + 1) + 1 := by rw [div_self hb1]

/-- In the standard unitary action, the product of the canonical root
involution and the Weyl element has exact order three. -/
theorem standard_st_order (n : ℕ) :
    orderOf (rootHom n (RootGroup.centralInvolution n) * weylElement n) = 3 := by
  apply orderOf_eq_prime
  · rw [show (3 : ℕ) = 2 + 1 by omega, pow_succ, pow_two]
    have hbraid := standard_braid n
    have hs2 : rootHom n (RootGroup.centralInvolution n) *
        rootHom n (RootGroup.centralInvolution n) = 1 := by
      rw [← map_mul]
      have hzz : RootGroup.centralInvolution n *
          RootGroup.centralInvolution n = 1 := by
        simpa only [pow_two] using RootGroup.centralInvolution_sq n
      rw [hzz, map_one]
    have ht2 : weylElement n ^ 2 = 1 := weylElement_sq_eq_one n
    rw [pow_two] at ht2
    calc
      (rootHom n (RootGroup.centralInvolution n) * weylElement n) *
          (rootHom n (RootGroup.centralInvolution n) * weylElement n) *
          (rootHom n (RootGroup.centralInvolution n) * weylElement n) =
        rootHom n (RootGroup.centralInvolution n) *
          (weylElement n * rootHom n (RootGroup.centralInvolution n) *
            weylElement n) *
          rootHom n (RootGroup.centralInvolution n) * weylElement n := by
            group
      _ = rootHom n (RootGroup.centralInvolution n) *
          (rootHom n (RootGroup.centralInvolution n) * weylElement n *
            rootHom n (RootGroup.centralInvolution n)) *
          rootHom n (RootGroup.centralInvolution n) * weylElement n := by
            rw [hbraid]
      _ = (rootHom n (RootGroup.centralInvolution n) *
            rootHom n (RootGroup.centralInvolution n)) * weylElement n *
          (rootHom n (RootGroup.centralInvolution n) *
            rootHom n (RootGroup.centralInvolution n)) * weylElement n := by
            group
      _ = weylElement n * weylElement n := by
        rw [hs2]
        simp only [one_mul, mul_one]
      _ = 1 := ht2
  · intro h
    have hp := congrArg (fun g : standardPermGroup n =>
      g • Unital.infinity n) h
    simp [mul_smul, Unital.origin] at hp

end

end

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
