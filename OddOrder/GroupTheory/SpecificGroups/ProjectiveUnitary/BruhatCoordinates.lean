/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.Borel

/-!
# Bruhat coordinates for the projective unitary group

For a nonidentity Hermitian root point `u = (a,b)`, this file constructs the
determinant-one Hua parameter

`c(u) = b / star(b)^2`.

The Lean root group acts by left translation.  Peterfalvi writes the root
action on the right; under the affine dictionary `u = x⁻¹`, his reciprocal
map is therefore transported by inversion to `J ∘ F ∘ J`, implemented as
`RootGroup.weylReciprocal`.  With this convention the determinant-one witness
for the Hua parameter is `b⁻¹`.

These are the reciprocal and cubic Hua coordinates in **Peterfalvi, Part II,
Chapter IV §3, Proposition and Corollary 2** (pp. 129–132).  They supply
the coordinate input for the canonical-form decomposition
analogous to **Peterfalvi, Part II, Chapter I §1, Proposition 4(a)**.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

noncomputable section

variable {n : ℕ}

section /- Part II, Chapter IV §3: determinant-one Hua coordinates -/

/-- The unit whose special determinant-one weight is the Bruhat torus
parameter. -/
def bruhatSourceUnit (u : RootGroup n) (hu : u ≠ 1) :
    GeneralTorusParameter n :=
  Units.mk0 u.snd⁻¹
    (inv_ne_zero ((RootGroup.ne_one_iff_snd_ne_zero u).mp hu))

@[simp]
theorem coe_bruhatSourceUnit (u : RootGroup n) (hu : u ≠ 1) :
    (bruhatSourceUnit u hu : Field n) = u.snd⁻¹ :=
  rfl

/-- The full diagonal parameter underlying the determinant-one Hua element. -/
def bruhatFullTorus (u : RootGroup n) (hu : u ≠ 1) :
    GeneralTorusParameter n :=
  Units.mk0 (u.snd / (star u.snd) ^ 2)
    (div_ne_zero
      ((RootGroup.ne_one_iff_snd_ne_zero u).mp hu)
      (pow_ne_zero 2 ((star_ne_zero (R := Field n)).2
        ((RootGroup.ne_one_iff_snd_ne_zero u).mp hu))))

@[simp]
theorem coe_bruhatFullTorus (u : RootGroup n) (hu : u ≠ 1) :
    (bruhatFullTorus u hu : Field n) = u.snd / (star u.snd) ^ 2 :=
  rfl

/-- The Bruhat parameter is exactly a special determinant-one torus weight. -/
theorem bruhatFullTorus_eq_specialTorusWeight
    (u : RootGroup n) (hu : u ≠ 1) :
    bruhatFullTorus u hu =
      specialTorusWeightHom n (bruhatSourceUnit u hu) := by
  have hb : u.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero u).mp hu
  have hsb : star u.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hb
  apply Units.ext
  change u.snd / (star u.snd) ^ 2 =
    (star u.snd⁻¹) ^ 2 * (u.snd⁻¹)⁻¹
  rw [star_inv₀]
  field_simp

/-- The determinant-one torus parameter in the nontrivial unitary Bruhat
relation.  Positivity is used only to identify the special weight with the
power-map range defining `PSUTorusParameter`. -/
def bruhatTorus (u : RootGroup n) (hu : u ≠ 1)
    (hn : 0 < n) : PSUTorusParameter n :=
  ⟨bruhatFullTorus u hu, by
    rw [bruhatFullTorus_eq_specialTorusWeight u hu,
      specialTorusWeightHom_eq_powMonoidHom n hn]
    exact ⟨bruhatSourceUnit u hu, rfl⟩⟩

@[simp]
theorem coe_bruhatTorus (u : RootGroup n) (hu : u ≠ 1)
    (hn : 0 < n) :
    ((bruhatTorus u hu hn).1 : Field n) =
      u.snd / (star u.snd) ^ 2 :=
  rfl

/-- The Hermitian norm weight of the full Bruhat torus parameter. -/
theorem torusWeight_bruhatFullTorus (u : RootGroup n) (hu : u ≠ 1) :
    torusWeight (bruhatFullTorus u hu) =
      1 / (u.snd * star u.snd) := by
  have hb : u.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero u).mp hu
  have hsb : star u.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hb
  rw [torusWeight, coe_bruhatFullTorus]
  simp only [star_div₀, star_pow, star_star]
  field_simp

/-- The same norm-weight formula for the restricted determinant-one
parameter. -/
theorem torusWeight_bruhatTorus (u : RootGroup n) (hu : u ≠ 1)
    (hn : 0 < n) :
    torusWeight (bruhatTorus u hu hn).1 =
      1 / (u.snd * star u.snd) := by
  exact torusWeight_bruhatFullTorus u hu

end

section /- Part II, Chapter IV §3: the affine-origin Bruhat identity -/

/-- Scaling the Weyl image of Peterfalvi's reciprocal by the Hua parameter
gives the inverse Weyl image.  This is the affine-origin coordinate case of
the nontrivial Bruhat relation. -/
theorem scalePoint_weylReciprocal_reciprocal_eq_inv
    (u : RootGroup n) (hu : u ≠ 1) :
    scalePoint (bruhatFullTorus u hu)
        (RootGroup.weylReciprocal (RootGroup.reciprocal u hu)
          (RootGroup.reciprocal_ne_one u hu)) =
      (RootGroup.weylReciprocal u hu)⁻¹ := by
  have hb : u.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero u).mp hu
  have hsb : star u.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hb
  ext
  · simp only [scalePoint_fst, coe_bruhatFullTorus,
      RootGroup.weylReciprocal_fst, RootGroup.reciprocal_fst,
      RootGroup.reciprocal_snd, star_div₀, star_one, RootGroup.fst_inv]
    field_simp
  · simp only [scalePoint_snd, torusWeight_bruhatFullTorus,
      RootGroup.weylReciprocal_snd, RootGroup.reciprocal_snd,
      RootGroup.snd_inv, RootGroup.weylReciprocal_fst, star_div₀,
      star_star]
    field_simp
    symm
    calc
      star u.snd + u.fst * star u.fst =
          star u.snd + (u.snd + star u.snd) := by rw [u.condition]
      _ = u.snd := by
        rw [add_comm u.snd, ← add_assoc, CharTwo.add_self_eq_zero,
          zero_add]

/-- The normalized affine-origin Bruhat coordinate identity. -/
theorem origin_bruhat_identity (u : RootGroup n) (hu : u ≠ 1) :
    RootGroup.weylReciprocal u hu *
        scalePoint (bruhatFullTorus u hu)
          (RootGroup.weylReciprocal (RootGroup.reciprocal u hu)
            (RootGroup.reciprocal_ne_one u hu)) = 1 := by
  rw [scalePoint_weylReciprocal_reciprocal_eq_inv]
  exact mul_inv_cancel _

end
section /- Part II, Chapter IV §3: pole and generic affine identities -/

/-- The two affine expressions in the normalized Bruhat relation reach the
Weyl pole simultaneously. -/
theorem mul_weylReciprocal_eq_one_iff_reciprocal_mul_eq_one
    (u v : RootGroup n) (hu : u ≠ 1) (hv : v ≠ 1) :
    u * RootGroup.weylReciprocal v hv = 1 ↔
      RootGroup.reciprocal u hu * v = 1 := by
  have hub : u.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero u).mp hu
  have hvb : v.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero v).mp hv
  rw [RootGroup.eq_one_iff_snd_eq_zero,
    RootGroup.eq_one_iff_snd_eq_zero]
  simp only [RootGroup.snd_mul, RootGroup.weylReciprocal_snd,
    RootGroup.weylReciprocal_fst, RootGroup.reciprocal_snd,
    RootGroup.reciprocal_fst, star_div₀, star_star]
  field_simp
  ring_nf

/-- Generic affine coordinate identity in the normalized unitary Bruhat
relation.  The two nonidentity hypotheses are exactly the condition that
neither side passes through the pole. -/
theorem generic_bruhat_identity
    (u v : RootGroup n) (hu : u ≠ 1) (hv : v ≠ 1)
    (hleft : u * RootGroup.weylReciprocal v hv ≠ 1)
    (hright : RootGroup.reciprocal u hu * v ≠ 1) :
    RootGroup.weylReciprocal
        (u * RootGroup.weylReciprocal v hv) hleft =
      RootGroup.weylReciprocal u hu *
        scalePoint (bruhatFullTorus u hu)
          (RootGroup.weylReciprocal
            (RootGroup.reciprocal u hu * v) hright) := by
  have hub : u.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero u).mp hu
  have husb : star u.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hub
  have hvb : v.snd ≠ 0 := (RootGroup.ne_one_iff_snd_ne_zero v).mp hv
  have hvsb : star v.snd ≠ 0 := (star_ne_zero (R := Field n)).2 hvb
  have htwo : (2 : Field n) = 0 := CharTwo.two_eq_zero
  let D : Field n := 1 + u.snd * v.snd + u.fst * star v.fst
  have hlform :
      (u * RootGroup.weylReciprocal v hv).snd = D / v.snd := by
    dsimp only [D]
    simp only [RootGroup.snd_mul, RootGroup.weylReciprocal_snd,
      RootGroup.weylReciprocal_fst, star_div₀, star_star]
    field_simp
    ring
  have hrform :
      (RootGroup.reciprocal u hu * v).snd = D / u.snd := by
    dsimp only [D]
    simp only [RootGroup.snd_mul, RootGroup.reciprocal_snd,
      RootGroup.reciprocal_fst]
    field_simp
  have hD : D ≠ 0 := by
    intro hzero
    apply (RootGroup.ne_one_iff_snd_ne_zero _).mp hleft
    rw [hlform, hzero, zero_div]
  have hstarD : star D ≠ 0 := (star_ne_zero (R := Field n)).2 hD
  have hleft_fst :
      (RootGroup.weylReciprocal
        (u * RootGroup.weylReciprocal v hv) hleft).fst =
        (u.fst * star v.snd + v.fst) / star D := by
    rw [RootGroup.weylReciprocal_fst, hlform]
    simp only [RootGroup.fst_mul, RootGroup.weylReciprocal_fst,
      star_div₀]
    field_simp
  have hright_fst :
      (RootGroup.weylReciprocal u hu *
          scalePoint (bruhatFullTorus u hu)
            (RootGroup.weylReciprocal
              (RootGroup.reciprocal u hu * v) hright)).fst =
        (u.fst * star v.snd + v.fst) / star D := by
    simp only [RootGroup.fst_mul, RootGroup.weylReciprocal_fst,
      scalePoint_fst, coe_bruhatFullTorus, RootGroup.reciprocal_fst]
    rw [hrform]
    dsimp only [D] at hstarD ⊢
    simp only [star_div₀, star_add, star_mul, star_star, star_one]
      at hstarD ⊢
    let E : Field n :=
      1 + v.fst * star u.fst + star u.snd * star v.snd
    have hE : E ≠ 0 := by
      intro hzero
      apply hstarD
      calc
        1 + star v.snd * star u.snd + v.fst * star u.fst = E := by
          dsimp only [E]
          ring
        _ = 0 := hzero
    have hEinv : E⁻¹ * E = 1 := inv_mul_cancel₀ hE
    field_simp [hE]
    dsimp only [E] at hEinv ⊢
    linear_combination
      (v.fst + (v.fst +
        (1 + v.fst * star u.fst + star u.snd * star v.snd)⁻¹ *
          v.fst)) * u.condition +
      u.fst * hEinv +
      (u.fst + u.snd *
          (1 + v.fst * star u.fst + star u.snd * star v.snd)⁻¹ *
            v.fst +
        (u.fst * v.fst * star u.fst -
          u.fst * star u.snd * star v.snd *
            (1 + v.fst * star u.fst + star u.snd * star v.snd)⁻¹ -
          v.fst * star u.snd -
          v.fst * star u.snd *
            (1 + v.fst * star u.fst + star u.snd * star v.snd)⁻¹ -
          v.fst *
            (1 + v.fst * star u.fst + star u.snd * star v.snd)⁻¹ *
              u.snd -
          v.fst * u.snd)) * htwo
  have hleft_snd :
      (RootGroup.weylReciprocal
        (u * RootGroup.weylReciprocal v hv) hleft).snd =
        v.snd / D := by
    rw [RootGroup.weylReciprocal_snd, hlform]
    field_simp
  have hright_snd :
      (RootGroup.weylReciprocal u hu *
          scalePoint (bruhatFullTorus u hu)
            (RootGroup.weylReciprocal
              (RootGroup.reciprocal u hu * v) hright)).snd =
        v.snd / D := by
    rw [RootGroup.snd_mul]
    simp only [RootGroup.weylReciprocal_snd, scalePoint_snd,
      torusWeight_bruhatFullTorus, RootGroup.weylReciprocal_fst,
      scalePoint_fst, coe_bruhatFullTorus]
    rw [hrform]
    simp only [RootGroup.fst_mul, RootGroup.reciprocal_fst, star_mul,
      star_add, star_div₀, star_pow, star_star]
    dsimp only [D] at hD ⊢
    field_simp
    linear_combination u.condition +
      (star u.snd * u.fst * star v.fst +
        u.fst * star u.fst) * htwo
  ext
  · rw [hleft_fst, hright_fst]
  · rw [hleft_snd, hright_snd]

end


end


end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
