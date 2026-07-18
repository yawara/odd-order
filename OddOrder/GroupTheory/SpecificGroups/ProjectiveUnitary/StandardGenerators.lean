/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroup
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Standard root, torus, and Weyl generators for `PSU(3,q)`

For `q = 2 ^ n`, this file constructs the standard permutation generators on
the Hermitian unital of size `q³ + 1`:

* the root group acts regularly on the affine points and fixes infinity;
* a diagonal parameter `c` acts by `(x,y) |-> (c*x, c*star(c)*y)`;
* the determinant-one torus consists of the parameters
  `c = star(t)^2 / t = t^(2q-1)`;
* the Weyl element interchanges infinity and the affine origin and, in the
  left-translation convention used here, sends a non-origin point `(x,y)` to
  `(x/star(y), 1/y)`.

Peterfalvi uses right actions and writes the reciprocal map as
`F(x,y) = (x/y, 1/y)`. Lean uses left actions and the root translations below
are left multiplications. Identifying the Lean affine coordinate with the
inverse of Peterfalvi's coordinate therefore transports the Weyl map to
`J ∘ F ∘ J(x,y) = (x/star(y), 1/y)`, where `J(u) = u⁻¹`. This is an
inversion-conjugate realization of the same standard action.

The formulas are from Peterfalvi, Part II, Chapter III §3 (pp. 119–121) and
Chapter IV §3. They provide the concrete group-action target needed for
Part II, Chapter I §3, Lemma 1 and Proposition 1(c) (pp. 104–106).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

noncomputable section

section /- Part II, Chapter III §3: root translations and diagonal torus -/

namespace RootGroup

/-- A root element with prescribed first coordinate. -/
noncomputable def withFirst (n : ℕ) (a : Field n) : RootGroup n :=
  ⟨a, Classical.choose (exists_add_star_eq_mul_star n a),
    Classical.choose_spec (exists_add_star_eq_mul_star n a)⟩

@[simp] theorem withFirst_fst (n : ℕ) (a : Field n) : (withFirst n a).fst = a := rfl

end RootGroup

namespace Unital

@[simp] theorem affine_inj {n : ℕ} {u v : RootGroup n} : affine u = affine v ↔ u = v := by
  simp [affine]

/-- Left root translations fix infinity and act regularly on affine points. -/
noncomputable def rootPerm {n : ℕ} (u : RootGroup n) : Equiv.Perm (Unital n) :=
  Equiv.optionCongr (Equiv.mulLeft u)

@[simp] theorem rootPerm_infinity {n : ℕ} (u : RootGroup n) :
    rootPerm u (infinity n) = infinity n := rfl

@[simp] theorem rootPerm_affine {n : ℕ} (u v : RootGroup n) :
    rootPerm u (affine v) = affine (u * v) := rfl

noncomputable def rootPermHom (n : ℕ) : RootGroup n →* Equiv.Perm (Unital n) where
  toFun := rootPerm
  map_one' := by
    apply Equiv.ext
    intro p
    cases p with
    | none => rfl
    | some v =>
        change affine (1 * v) = affine v
        rw [one_mul]
  map_mul' u v := by
    apply Equiv.ext
    intro p
    cases p with
    | none => rfl
    | some w =>
        change affine ((u * v) * w) = affine (u * (v * w))
        rw [mul_assoc]

theorem rootPermHom_injective (n : ℕ) : Function.Injective (rootPermHom n) := by
  intro u v huv
  have hp := congrArg (fun e : Equiv.Perm (Unital n) => e (affine 1)) huv
  change affine (u * 1) = affine (v * 1) at hp
  simpa only [mul_one, affine_inj] using hp

theorem existsUnique_rootPerm_affine {n : ℕ} (u v : RootGroup n) :
    ∃! g : RootGroup n, rootPermHom n g (affine u) = affine v := by
  refine ⟨v * u⁻¹, ?_, ?_⟩
  · change affine ((v * u⁻¹) * u) = affine v
    simp [mul_assoc]
  · intro g hg
    have hgu : g * u = v := by
      change affine (g * u) = affine v at hg
      exact affine_inj.mp hg
    calc
      g = (g * u) * u⁻¹ := by simp
      _ = v * u⁻¹ := by rw [hgu]

end Unital

/-- The full diagonal parameter group in `PGU(3,q)`. -/
abbrev GeneralTorusParameter (n : ℕ) := (Field n)ˣ

/-- Quadratic conjugation lifted to the unit group. -/
noncomputable def conjugateUnitHom (n : ℕ) :
    GeneralTorusParameter n →* GeneralTorusParameter n :=
  Units.map (conjugation n).toRingEquiv.toMonoidHom

@[simp] theorem coe_conjugateUnitHom {n : ℕ} (c : GeneralTorusParameter n) :
    ((conjugateUnitHom n c : GeneralTorusParameter n) : Field n) =
      star (c : Field n) := rfl

/-- The root-scaling weight induced by the determinant-one diagonal matrix
`diag(t, star(t) / t, star(t)⁻¹)`. -/
noncomputable def specialTorusWeightHom (n : ℕ) :
    GeneralTorusParameter n →* GeneralTorusParameter n where
  toFun t := (conjugateUnitHom n t) ^ 2 * t⁻¹
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, mul_pow, mul_inv_rev]
    ac_rfl

@[simp]
theorem specialTorusWeightHom_apply (n : ℕ) (t : GeneralTorusParameter n) :
    specialTorusWeightHom n t = (conjugateUnitHom n t) ^ 2 * t⁻¹ := rfl

/-- On a positive-degree quadratic finite field, conjugation on units is the
`2 ^ n`-power map. -/
theorem conjugateUnitHom_eq_pow (n : ℕ) (hn : 0 < n)
    (t : GeneralTorusParameter n) :
    conjugateUnitHom n t = t ^ (2 ^ n) := by
  apply Units.ext
  change conjugation n (t : Field n) = (t : Field n) ^ (2 ^ n)
  exact conjugation_apply n hn (t : Field n)

/-- The determinant-one diagonal weight is exactly the `(2q - 1)`-power map,
where `q = 2 ^ n`. -/
theorem specialTorusWeightHom_eq_powMonoidHom (n : ℕ) (hn : 0 < n) :
    specialTorusWeightHom n =
      (powMonoidHom (2 * 2 ^ n - 1) :
        GeneralTorusParameter n →* GeneralTorusParameter n) := by
  apply MonoidHom.ext
  intro t
  change (conjugateUnitHom n t) ^ 2 * t⁻¹ = t ^ (2 * 2 ^ n - 1)
  rw [conjugateUnitHom_eq_pow n hn t, ← pow_mul]
  have hle : 1 ≤ 2 * 2 ^ n :=
    Nat.one_le_two_pow.trans (Nat.le_mul_of_pos_left _ Nat.zero_lt_two)
  rw [pow_sub t hle, pow_one]
  simp only [mul_comm]

/-- The Weyl action on a root-scaling parameter: `a |-> star(a)⁻¹`. -/
noncomputable def weylParameterHom (n : ℕ) :
    GeneralTorusParameter n →* GeneralTorusParameter n where
  toFun c := (conjugateUnitHom n c)⁻¹
  map_one' := by simp
  map_mul' c d := by simp [mul_comm]

@[simp] theorem coe_weylParameterHom {n : ℕ} (c : GeneralTorusParameter n) :
    ((weylParameterHom n c : GeneralTorusParameter n) : Field n) =
      (star (c : Field n))⁻¹ := by
  simp [weylParameterHom]

/-- Hermitian norm, the second-coordinate weight of a diagonal parameter. -/
noncomputable def torusWeight {n : ℕ} (c : GeneralTorusParameter n) : Field n :=
  (c : Field n) * star (c : Field n)

theorem torusWeight_ne_zero {n : ℕ} (c : GeneralTorusParameter n) :
    torusWeight c ≠ 0 :=
  mul_ne_zero (Units.ne_zero c) ((star_ne_zero (R := Field n)).2 (Units.ne_zero c))

@[simp] theorem torusWeight_one (n : ℕ) :
    torusWeight (1 : GeneralTorusParameter n) = 1 := by
  simp [torusWeight]

@[simp] theorem torusWeight_mul {n : ℕ}
    (c d : GeneralTorusParameter n) :
    torusWeight (c * d) = torusWeight c * torusWeight d := by
  simp only [torusWeight, Units.val_mul, star_mul]
  ring

/-- Peterfalvi's action `(x,y)^a = (a*x, a^(1+q)*y)` in Hermitian coordinates. -/
noncomputable def scalePoint {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) : RootGroup n :=
  { fst := (c : Field n) * u.fst
    snd := torusWeight c * u.snd
    condition := by
      simp only [torusWeight, star_mul, star_star]
      linear_combination ((c : Field n) * star (c : Field n)) * u.condition }

@[simp] theorem scalePoint_fst {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) :
    (scalePoint c u).fst = (c : Field n) * u.fst := rfl

@[simp] theorem scalePoint_snd {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) :
    (scalePoint c u).snd = torusWeight c * u.snd := rfl

@[simp] theorem scalePoint_one_parameter {n : ℕ} (u : RootGroup n) :
    scalePoint (1 : GeneralTorusParameter n) u = u := by
  ext <;> simp

theorem scalePoint_mul_parameter {n : ℕ}
    (c d : GeneralTorusParameter n) (u : RootGroup n) :
    scalePoint (c * d) u = scalePoint c (scalePoint d u) := by
  ext
  · simp [mul_assoc]
  · simp [mul_assoc]

theorem scalePoint_mul_root {n : ℕ}
    (c : GeneralTorusParameter n) (u v : RootGroup n) :
    scalePoint c (u * v) = scalePoint c u * scalePoint c v := by
  ext
  · simp [mul_add]
  · simp only [RootGroup.snd_mul, scalePoint_snd, scalePoint_fst, star_mul]
    dsimp only [torusWeight]
    ring

/-- The full diagonal torus action by root-group automorphisms. -/
noncomputable def torusScale {n : ℕ}
    (c : GeneralTorusParameter n) : RootGroup n ≃* RootGroup n where
  toFun := scalePoint c
  invFun := scalePoint c⁻¹
  left_inv u := by
    rw [← scalePoint_mul_parameter]
    simp
  right_inv u := by
    rw [← scalePoint_mul_parameter]
    simp
  map_mul' := scalePoint_mul_root c

@[simp] theorem torusScale_apply {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) :
    torusScale c u = scalePoint c u := rfl

noncomputable def torusScaleHom (n : ℕ) :
    GeneralTorusParameter n →* MulAut (RootGroup n) where
  toFun := torusScale
  map_one' := by
    ext u <;> simp
  map_mul' c d := by
    apply MulEquiv.ext
    intro u
    exact scalePoint_mul_parameter c d u

theorem torusScaleHom_injective (n : ℕ) : Function.Injective (torusScaleHom n) := by
  intro c d hcd
  have hp := congrArg (fun e : MulAut (RootGroup n) => e (RootGroup.withFirst n 1)) hcd
  apply Units.ext
  have hfst := congrArg RootGroup.fst hp
  simpa only [torusScaleHom, MonoidHom.coe_mk, OneHom.coe_mk, torusScale_apply,
    scalePoint_fst, RootGroup.withFirst_fst, mul_one] using hfst

namespace Unital

private def optionPermHom (α : Type*) : Equiv.Perm α →* Equiv.Perm (Option α) where
  toFun := Equiv.optionCongr
  map_one' := Equiv.optionCongr_one
  map_mul' e f := by
    ext p
    cases p <;> rfl

noncomputable def torusPerm (n : ℕ) :
    GeneralTorusParameter n →* Equiv.Perm (Unital n) :=
  (optionPermHom (RootGroup n)).comp
    ((MulAut.toPerm (RootGroup n)).comp (torusScaleHom n))

@[simp] theorem torusPerm_infinity {n : ℕ} (c : GeneralTorusParameter n) :
    torusPerm n c (infinity n) = infinity n := rfl

@[simp] theorem torusPerm_affine {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) :
    torusPerm n c (affine u) = affine (scalePoint c u) := rfl

theorem torusPerm_injective (n : ℕ) : Function.Injective (torusPerm n) := by
  intro c d hcd
  have hp := congrArg (fun e : Equiv.Perm (Unital n) =>
    e (affine (RootGroup.withFirst n 1))) hcd
  have hroot : scalePoint c (RootGroup.withFirst n 1) =
      scalePoint d (RootGroup.withFirst n 1) :=
    Option.some_injective _ hp
  apply Units.ext
  have hfst := congrArg RootGroup.fst hroot
  simpa using hfst

/-- Torus conjugation carries a root translation to the scaled translation. -/
theorem torusPerm_mul_rootPerm_mul_inv {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) :
    torusPerm n c * rootPermHom n u * (torusPerm n c)⁻¹ =
      rootPermHom n (scalePoint c u) := by
  apply Equiv.Perm.ext
  intro p
  cases p with
  | none => rfl
  | some v =>
      change affine (torusScale c (u * (torusScale c).symm v)) =
        affine (torusScale c u * v)
      rw [map_mul, MulEquiv.apply_symm_apply]

end Unital

/-- Root-scaling parameters arising from determinant-one diagonal matrices.
The exponent `2q-1` is the map `t |-> star(t)^2 / t`. -/
abbrev PSUTorusParameter (n : ℕ) :=
  (powMonoidHom (2 * 2 ^ n - 1) :
    GeneralTorusParameter n →* GeneralTorusParameter n).range

/-- The conjugate-inverse Weyl action preserves the determinant-one torus image. -/
theorem weylParameter_mem_psuTorus {n : ℕ} (c : PSUTorusParameter n) :
    weylParameterHom n c.1 ∈ PSUTorusParameter n := by
  rcases c.2 with ⟨d, hd⟩
  refine ⟨weylParameterHom n d, ?_⟩
  change (weylParameterHom n d) ^ (2 * 2 ^ n - 1) = weylParameterHom n c.1
  rw [← hd]
  simpa only [powMonoidHom_apply] using
    ((weylParameterHom n).map_pow d (2 * 2 ^ n - 1)).symm

theorem gcd_unitary_exponent (q : ℕ) (hq : 0 < q) :
    (q ^ 2 - 1).gcd (2 * q - 1) = (q + 1).gcd 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have hsq : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    rw [show (k + 1) ^ 2 = k * (k + 2) + 1 by ring, Nat.add_sub_cancel]
  have hexp : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [hsq, hexp]
  have hcop : Nat.Coprime k (2 * k + 1) :=
    (Nat.coprime_mul_right_add_right k 1 2).2 (by simp)
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hgA := Nat.gcd_dvd_left (k * (k + 2)) (2 * k + 1)
      have hgB := Nat.gcd_dvd_right (k * (k + 2)) (2 * k + 1)
      exact ((hcop.coprime_dvd_right hgB).symm).dvd_of_dvd_mul_left hgA
    · have hgA := Nat.gcd_dvd_left (k * (k + 2)) (2 * k + 1)
      have hgB := Nat.gcd_dvd_right (k * (k + 2)) (2 * k + 1)
      have hrel : 3 + 4 * (k * (k + 2)) = (2 * k + 3) * (2 * k + 1) := by ring
      have hleft : (k * (k + 2)).gcd (2 * k + 1) ∣ 4 * (k * (k + 2)) :=
        dvd_mul_of_dvd_right hgA 4
      have hsum : (k * (k + 2)).gcd (2 * k + 1) ∣ 3 + 4 * (k * (k + 2)) := by
        rw [hrel]
        exact dvd_mul_of_dvd_right hgB (2 * k + 3)
      exact (Nat.dvd_add_iff_left hleft).mpr hsum
  · apply Nat.dvd_gcd
    · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (k + 2) 3) k
    · have hrel : (2 * k + 1) + 3 = 2 * (k + 2) := by ring
      apply (Nat.dvd_add_iff_left (Nat.gcd_dvd_right (k + 2) 3)).mpr
      rw [hrel]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (k + 2) 3) 2

theorem natCard_generalTorus (n : ℕ) (hn : 0 < n) :
    Nat.card (GeneralTorusParameter n) = 2 ^ (2 * n) - 1 := by
  rw [Nat.card_units, natCard_field n hn]

theorem natCard_psuTorus (n : ℕ) (hn : 0 < n) :
    Nat.card (PSUTorusParameter n) =
      (2 ^ (2 * n) - 1) / (2 ^ (2 * n) - 1).gcd (2 * 2 ^ n - 1) := by
  rw [IsCyclic.card_powMonoidHom_range, natCard_generalTorus n hn]

theorem natCard_psuTorus_standard (n : ℕ) (hn : 0 < n) :
    Nat.card (PSUTorusParameter n) =
      (2 ^ (2 * n) - 1) / (2 ^ n + 1).gcd 3 := by
  rw [natCard_psuTorus n hn]
  have hpow : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
    calc
      2 ^ (2 * n) = 2 ^ (n * 2) := by congr 1; omega
      _ = (2 ^ n) ^ 2 := by rw [pow_mul]
  rw [hpow, gcd_unitary_exponent (2 ^ n) (by positivity)]

end

section /- Part II, Chapter IV §3: the standard Weyl permutation -/

namespace RootGroup

/-- A root point is the affine origin exactly when its second coordinate vanishes. -/
theorem eq_one_iff_snd_eq_zero {n : ℕ} (u : RootGroup n) :
    u = 1 ↔ u.snd = 0 := by
  constructor
  · rintro rfl
    exact snd_one
  · intro hb
    have ha_prod : u.fst * star u.fst = 0 := by
      rw [← u.condition, hb, star_zero, add_zero]
    have ha : u.fst = 0 := by
      by_contra ha
      exact (mul_ne_zero ha ((star_ne_zero (R := Field n)).2 ha)) ha_prod
    ext
    · simpa only [fst_one] using ha
    · simpa only [snd_one] using hb

/-- Away from the origin, the reciprocal-coordinate denominator is nonzero. -/
theorem ne_one_iff_snd_ne_zero {n : ℕ} (u : RootGroup n) :
    u ≠ 1 ↔ u.snd ≠ 0 :=
  not_congr (eq_one_iff_snd_eq_zero u)

/-- Peterfalvi's reciprocal affine point in the source's right-action coordinates. -/
noncomputable def reciprocal {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    RootGroup n :=
  { fst := u.fst / u.snd
    snd := 1 / u.snd
    condition := by
      have hb : u.snd ≠ 0 := (ne_one_iff_snd_ne_zero u).mp hu
      have hsb : star u.snd ≠ 0 :=
        (star_ne_zero (R := Field n)).2 hb
      simp only [star_div₀, star_one]
      field_simp [hb, hsb]
      linear_combination u.condition }

@[simp]
theorem reciprocal_fst {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    (reciprocal u hu).fst = u.fst / u.snd := rfl

@[simp]
theorem reciprocal_snd {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    (reciprocal u hu).snd = 1 / u.snd := rfl

theorem reciprocal_snd_ne_zero {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    (reciprocal u hu).snd ≠ 0 := by
  rw [reciprocal_snd]
  exact one_div_ne_zero (ne_one_iff_snd_ne_zero u |>.mp hu)

theorem reciprocal_ne_one {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    reciprocal u hu ≠ 1 :=
  (ne_one_iff_snd_ne_zero (reciprocal u hu)).mpr
    (reciprocal_snd_ne_zero u hu)

/-- Reciprocal affine coordinates are involutive away from the origin. -/
@[simp]
theorem reciprocal_reciprocal {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    reciprocal (reciprocal u hu) (reciprocal_ne_one u hu) = u := by
  have hb : u.snd ≠ 0 := (ne_one_iff_snd_ne_zero u).mp hu
  ext
  · simp only [reciprocal_fst, reciprocal_snd]
    field_simp
  · simp only [reciprocal_snd]
    field_simp

/-- The Weyl reciprocal adapted to left root translations. Under the affine
dictionary “Lean `u` = Peterfalvi `x⁻¹`”, Peterfalvi's right-action reciprocal
`F` is transported to `J ∘ F ∘ J`, where `J` is root inversion. -/
noncomputable def weylReciprocal {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    RootGroup n :=
  (reciprocal u⁻¹ (inv_ne_one.mpr hu))⁻¹

@[simp]
theorem weylReciprocal_fst {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    (weylReciprocal u hu).fst = u.fst / star u.snd := by
  simp only [weylReciprocal, fst_inv, reciprocal_fst, snd_inv_eq_star]

@[simp]
theorem weylReciprocal_snd {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    (weylReciprocal u hu).snd = 1 / u.snd := by
  have hb : u.snd ≠ 0 := (ne_one_iff_snd_ne_zero u).mp hu
  have hsb : star u.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hb
  change 1 / u⁻¹.snd + (u⁻¹.fst / u⁻¹.snd) *
      star (u⁻¹.fst / u⁻¹.snd) = 1 / u.snd
  rw [snd_inv_eq_star, fst_inv, star_div₀, star_star]
  field_simp
  calc
    u.snd + u.fst * star u.fst =
        u.snd + (u.snd + star u.snd) := by rw [u.condition]
    _ = star u.snd := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem weylReciprocal_ne_one {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    weylReciprocal u hu ≠ 1 := by
  rw [weylReciprocal]
  exact inv_ne_one.mpr (reciprocal_ne_one u⁻¹ (inv_ne_one.mpr hu))

/-- The left-translation reciprocal coordinate map is involutive. -/
@[simp]
theorem weylReciprocal_weylReciprocal {n : ℕ}
    (u : RootGroup n) (hu : u ≠ 1) :
    weylReciprocal (weylReciprocal u hu) (weylReciprocal_ne_one u hu) = u := by
  have hb : u.snd ≠ 0 := (ne_one_iff_snd_ne_zero u).mp hu
  have hsb : star u.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hb
  ext
  · simp only [weylReciprocal_fst, weylReciprocal_snd, star_div₀, star_one]
    field_simp
  · simp only [weylReciprocal_snd]
    field_simp

end RootGroup

namespace Unital

/-- The point function of the standard unitary Weyl element. -/
noncomputable def weylPoint (n : ℕ) : Unital n → Unital n
  | none => affine 1
  | some u =>
      @dite _ (u = 1) (Classical.propDecidable _)
        (fun _ => infinity n)
        (fun hu => affine (RootGroup.weylReciprocal u hu))

/-- The standard unitary Weyl point function is an involution. -/
theorem weylPoint_involutive (n : ℕ) : Function.Involutive (weylPoint n) := by
  classical
  intro p
  cases p with
  | none => simp [weylPoint, infinity, affine]
  | some u =>
      by_cases hu : u = 1
      · subst u
        simp [weylPoint, infinity, affine]
      · have hrec : RootGroup.weylReciprocal u hu ≠ 1 :=
          RootGroup.weylReciprocal_ne_one u hu
        simp [weylPoint, affine, hu, hrec]

/-- The actual unitary Weyl permutation: it swaps infinity and the affine origin. -/
noncomputable def weylPerm (n : ℕ) : Equiv.Perm (Unital n) where
  toFun := weylPoint n
  invFun := weylPoint n
  left_inv := weylPoint_involutive n
  right_inv := weylPoint_involutive n

@[simp]
theorem weylPerm_infinity (n : ℕ) :
    weylPerm n (infinity n) = affine (1 : RootGroup n) := by
  rfl

@[simp]
theorem weylPerm_origin (n : ℕ) :
    weylPerm n (affine (1 : RootGroup n)) = infinity n := by
  simp [weylPerm, weylPoint, infinity, affine]

@[simp]
theorem weylPerm_affine_of_ne_one {n : ℕ} (u : RootGroup n) (hu : u ≠ 1) :
    weylPerm n (affine u) = affine (RootGroup.weylReciprocal u hu) := by
  classical
  simp [weylPerm, weylPoint, affine, hu]

theorem weylPerm_affine_of_snd_ne_zero {n : ℕ} (u : RootGroup n)
    (hu : u.snd ≠ 0) :
    weylPerm n (affine u) =
      affine (RootGroup.weylReciprocal u
        ((RootGroup.ne_one_iff_snd_ne_zero u).mpr hu)) := by
  exact weylPerm_affine_of_ne_one u ((RootGroup.ne_one_iff_snd_ne_zero u).mpr hu)

@[simp]
theorem weylPerm_apply_self (n : ℕ) (p : Unital n) :
    weylPerm n (weylPerm n p) = p :=
  weylPoint_involutive n p

end Unital

namespace RootGroup

@[simp]
theorem scalePoint_one_point {n : ℕ} (c : GeneralTorusParameter n) :
    scalePoint c (1 : RootGroup n) = 1 := by
  ext <;> simp

theorem scalePoint_ne_one {n : ℕ} (c : GeneralTorusParameter n)
    (u : RootGroup n) (hu : u ≠ 1) : scalePoint c u ≠ 1 := by
  apply (ne_one_iff_snd_ne_zero (scalePoint c u)).mpr
  rw [scalePoint_snd]
  exact mul_ne_zero (torusWeight_ne_zero c) ((ne_one_iff_snd_ne_zero u).mp hu)

/-- Conjugating a diagonal scaling by reciprocal coordinates gives conjugate-inverse scaling. -/
theorem reciprocal_scalePoint_reciprocal {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) (hu : u ≠ 1) :
    reciprocal (scalePoint c (reciprocal u hu))
        (scalePoint_ne_one c (reciprocal u hu) (reciprocal_ne_one u hu)) =
      scalePoint (weylParameterHom n c) u := by
  have hc : (c : Field n) ≠ 0 := Units.ne_zero c
  have hsc : star (c : Field n) ≠ 0 :=
    (star_ne_zero (R := Field n)).2 hc
  have hb : u.snd ≠ 0 := (ne_one_iff_snd_ne_zero u).mp hu
  ext
  · simp only [reciprocal_fst, reciprocal_snd, scalePoint_fst, scalePoint_snd,
      coe_weylParameterHom, torusWeight]
    field_simp
  · simp only [reciprocal_snd, scalePoint_snd, coe_weylParameterHom, torusWeight,
      star_inv₀, star_star]
    field_simp

/-- Conjugating a diagonal scaling by the left-translation reciprocal map
still gives conjugate-inverse scaling. -/
theorem weylReciprocal_scalePoint_weylReciprocal {n : ℕ}
    (c : GeneralTorusParameter n) (u : RootGroup n) (hu : u ≠ 1) :
    weylReciprocal (scalePoint c (weylReciprocal u hu))
        (scalePoint_ne_one c (weylReciprocal u hu)
          (weylReciprocal_ne_one u hu)) =
      scalePoint (weylParameterHom n c) u := by
  have hc : (c : Field n) ≠ 0 := Units.ne_zero c
  have hsc : star (c : Field n) ≠ 0 :=
    (star_ne_zero (R := Field n)).2 hc
  have hb : u.snd ≠ 0 := (ne_one_iff_snd_ne_zero u).mp hu
  have hsb : star u.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hb
  ext
  · simp only [weylReciprocal_fst, weylReciprocal_snd, scalePoint_fst,
      scalePoint_snd, coe_weylParameterHom, torusWeight, star_mul, star_div₀,
      star_one, star_star]
    field_simp
  · simp only [weylReciprocal_snd, scalePoint_snd, coe_weylParameterHom,
      torusWeight, star_inv₀, star_star]
    field_simp

end RootGroup

namespace Unital

/-- The determinant-one torus action, restricted from the full diagonal torus. -/
noncomputable def psuTorusPerm (n : ℕ) :
    PSUTorusParameter n →* Equiv.Perm (Unital n) :=
  (torusPerm n).comp (PSUTorusParameter n).subtype

@[simp]
theorem psuTorusPerm_apply {n : ℕ} (c : PSUTorusParameter n) (p : Unital n) :
    psuTorusPerm n c p = torusPerm n c.1 p := rfl

theorem psuTorusPerm_injective (n : ℕ) : Function.Injective (psuTorusPerm n) := by
  intro c d hcd
  apply Subtype.ext
  exact torusPerm_injective n hcd

/-- The conjugate-inverse parameter action restricted to the determinant-one torus. -/
noncomputable def psuWeylParameterHom (n : ℕ) :
    PSUTorusParameter n →* PSUTorusParameter n where
  toFun c := ⟨weylParameterHom n c.1, weylParameter_mem_psuTorus c⟩
  map_one' := by
    apply Subtype.ext
    exact (weylParameterHom n).map_one
  map_mul' c d := by
    apply Subtype.ext
    exact (weylParameterHom n).map_mul c.1 d.1

@[simp]
theorem coe_psuWeylParameterHom {n : ℕ} (c : PSUTorusParameter n) :
    (psuWeylParameterHom n c : GeneralTorusParameter n) = weylParameterHom n c.1 := rfl

/-- The unitary Weyl element conjugates the full torus by conjugate-inverse parameters. -/
theorem weylPerm_mul_torusPerm_mul_weylPerm {n : ℕ}
    (c : GeneralTorusParameter n) :
    weylPerm n * torusPerm n c * weylPerm n =
      torusPerm n (weylParameterHom n c) := by
  apply Equiv.Perm.ext
  intro p
  cases p with
  | none =>
      change weylPerm n (torusPerm n c (weylPerm n (infinity n))) =
        torusPerm n (weylParameterHom n c) (infinity n)
      simp
  | some u =>
      by_cases hu : u = 1
      · subst u
        change weylPerm n (torusPerm n c (weylPerm n (affine 1))) =
          torusPerm n (weylParameterHom n c) (affine 1)
        simp
      · change weylPerm n (torusPerm n c (weylPerm n (affine u))) =
          torusPerm n (weylParameterHom n c) (affine u)
        rw [weylPerm_affine_of_ne_one u hu, torusPerm_affine,
          weylPerm_affine_of_ne_one _
            (RootGroup.scalePoint_ne_one c (RootGroup.weylReciprocal u hu)
              (RootGroup.weylReciprocal_ne_one u hu)),
          torusPerm_affine]
        exact congrArg affine
          (RootGroup.weylReciprocal_scalePoint_weylReciprocal c u hu)

/-- The same Weyl conjugation relation inside the determinant-one torus action. -/
theorem weylPerm_mul_psuTorusPerm_mul_weylPerm {n : ℕ}
    (c : PSUTorusParameter n) :
    weylPerm n * psuTorusPerm n c * weylPerm n =
      psuTorusPerm n (psuWeylParameterHom n c) := by
  exact weylPerm_mul_torusPerm_mul_weylPerm c.1

end Unital

end

end

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
