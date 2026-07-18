/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.Borel

/-!
# Bruhat decomposition of the standard Suzuki permutation group

For the concrete Suzuki ovoid action, this file derives the Weyl--torus relation
and the explicit nontrivial Weyl--root relation from the anisotropic norm.  Closure
induction on the three standard generator families then gives the two Bruhat cells
`B` and `B w B`.  Consequently the constructed Borel subgroup is the stabilizer of
infinity and the full group has order `q² (q² + 1) (q - 1)`.

This is concrete Suzuki-group infrastructure for **Peterfalvi, Part II, Chapter I,
§3 Lemma 1** (pp. 100--107).  The construction is defined for every `m`; the later
simplicity target assumes `0 < m` (hence `q = 2^(2m+1) ≥ 8`), excluding the
degenerate order-20 case at `m = 0`.  The Bruhat result here is the set-theoretic
cover `B ∪ B w B`, not the stronger unique `adtb` canonical form on p. 98.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.Suzuki

variable {m : ℕ}

section /- §3 Lemma 1 Suzuki target: Weyl--torus relation (pp. 100--107) -/

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The Suzuki norm scales homogeneously under the standard torus action. -/
theorem suzukiNorm_torusScale (c : TorusParameter m) (u : RootGroup m) :
    (torusScale c u).suzukiNorm =
      u.suzukiNorm / ((c : Field m) ^ 2 * titsTwist m (c : Field m)) := by
  rw [RootGroup.suzukiNorm, RootGroup.suzukiNorm, torusScale_fst,
    torusScale_snd, suzukiNorm, suzukiNorm]
  dsimp only [torusWeight]
  simp only [map_div₀, map_mul, titsTwist_twice]
  field_simp [Units.ne_zero c, (map_ne_zero (titsTwist m)).2 (Units.ne_zero c)]

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
Reciprocal ovoid coordinates conjugate a torus scaling to its inverse. -/
theorem Ovoid.weylAffine_torusScale (c : TorusParameter m) (u : RootGroup m) :
    Ovoid.weylAffine (torusScale c u) =
      torusScale c⁻¹ (Ovoid.weylAffine u) := by
  by_cases hu : u = 1
  · subst u
    ext <;> simp
  · have hn : u.suzukiNorm ≠ 0 := Ovoid.suzukiNorm_ne_zero_of_ne_one hu
    ext
    · simp only [Ovoid.weylAffine_fst, torusScale_snd, torusScale_fst,
        suzukiNorm_torusScale]
      dsimp only [torusWeight]
      simp only [Units.val_inv_eq_inv_val]
      field_simp [hn, Units.ne_zero c,
        (map_ne_zero (titsTwist m)).2 (Units.ne_zero c)]
    · simp only [Ovoid.weylAffine_snd, torusScale_fst, torusScale_snd,
        suzukiNorm_torusScale]
      dsimp only [torusWeight]
      simp only [Units.val_inv_eq_inv_val, map_inv₀]
      field_simp [hn, Units.ne_zero c,
        (map_ne_zero (titsTwist m)).2 (Units.ne_zero c)]

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The Weyl involution conjugates
each standard torus element to its inverse. -/
theorem weylElement_mul_torusHom_mul_weylElement (c : TorusParameter m) :
    weylElement m * torusHom m c * weylElement m = torusHom m c⁻¹ := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro p
  cases p with
  | none =>
      change Ovoid.weylPerm m
        (Ovoid.torusPerm m c (Ovoid.weylPerm m (Ovoid.infinity m))) =
          Ovoid.torusPerm m c⁻¹ (Ovoid.infinity m)
      rw [Ovoid.weylPerm_infinity]
      change Ovoid.weylPerm m
        (Ovoid.torusPerm m c (Ovoid.affine (1 : RootGroup m))) =
          Ovoid.torusPerm m c⁻¹ (Ovoid.infinity m)
      rw [Ovoid.torusPerm_affine, map_one]
      change Ovoid.weylPerm m (Ovoid.origin m) =
        Ovoid.torusPerm m c⁻¹ (Ovoid.infinity m)
      rw [Ovoid.weylPerm_origin, Ovoid.torusPerm_infinity]
  | some u =>
      by_cases hu : u = 1
      · subst u
        change Ovoid.weylPerm m
          (Ovoid.torusPerm m c (Ovoid.weylPerm m (Ovoid.origin m))) =
            Ovoid.torusPerm m c⁻¹ (Ovoid.origin m)
        rw [Ovoid.weylPerm_origin, Ovoid.torusPerm_infinity,
          Ovoid.weylPerm_infinity,
          show Ovoid.origin m = Ovoid.affine (1 : RootGroup m) by rfl,
          Ovoid.torusPerm_affine, map_one]
      · have hscale : torusScale c (Ovoid.weylAffine u) ≠ 1 := by
          intro h
          apply Ovoid.weylAffine_ne_one hu
          exact (torusScale c).injective (by simpa using h)
        change Ovoid.weylPerm m
          (Ovoid.torusPerm m c (Ovoid.weylPerm m (Ovoid.affine u))) =
            Ovoid.torusPerm m c⁻¹ (Ovoid.affine u)
        rw [Ovoid.weylPerm_affine_of_ne_one u hu, Ovoid.torusPerm_affine,
          Ovoid.weylPerm_affine_of_ne_one _ hscale, Ovoid.torusPerm_affine,
          Ovoid.weylAffine_torusScale, Ovoid.weylAffine_weylAffine hu]

end

section /- §3 Lemma 1 Suzuki target: nontrivial Weyl--root relation (pp. 100--107) -/

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The Suzuki norm is invariant under inversion in the root group. -/
theorem RootGroup.suzukiNorm_inv (u : RootGroup m) : u⁻¹.suzukiNorm = u.suzukiNorm := by
  change OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm m u⁻¹.fst u⁻¹.snd =
    OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm m u.fst u.snd
  simp only [RootGroup.fst_inv, RootGroup.snd_inv,
    OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm, map_add, map_mul,
    titsTwist_twice]
  ring_nf
  have h3 : (3 : Field m) = 1 := by
    calc
      (3 : Field m) = 2 + 1 := by norm_num
      _ = (0 : Field m) + 1 :=
        congrArg (fun z : Field m => z + 1) CharTwo.two_eq_zero
      _ = 1 := zero_add 1
  simp only [h3, mul_one]

/-- The right root parameter in the nontrivial Suzuki Bruhat relation. -/
noncomputable def bruhatRightRoot (u : RootGroup m) : RootGroup m :=
  RootGroup.mk
    ((u.snd + u.fst * titsTwist m u.fst) / u.suzukiNorm)
    (u.snd / titsTwist m u.suzukiNorm)

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The right Bruhat root has inverse equal to the reciprocal of `u⁻¹`. -/
theorem bruhatRightRoot_inv (u : RootGroup m) (hu : u ≠ 1) :
    (bruhatRightRoot u)⁻¹ = Ovoid.weylAffine u⁻¹ := by
  have hn : u.suzukiNorm ≠ 0 := Ovoid.suzukiNorm_ne_zero_of_ne_one hu
  have htn : titsTwist m u.suzukiNorm ≠ 0 :=
    (map_ne_zero (titsTwist m)).2 hn
  ext
  · change (u.snd + u.fst * titsTwist m u.fst) / u.suzukiNorm =
      u⁻¹.snd / u⁻¹.suzukiNorm
    rw [RootGroup.snd_inv, RootGroup.suzukiNorm_inv]
  · rw [RootGroup.snd_inv, Ovoid.weylAffine_snd, RootGroup.fst_inv,
      RootGroup.suzukiNorm_inv]
    change
      u.snd / titsTwist m u.suzukiNorm +
          ((u.snd + u.fst * titsTwist m u.fst) / u.suzukiNorm) *
            titsTwist m
              ((u.snd + u.fst * titsTwist m u.fst) / u.suzukiNorm) =
        u.fst / u.suzukiNorm
    simp only [map_div₀, map_add, map_mul, titsTwist_twice]
    field_simp [hn, htn]
    simp only [RootGroup.suzukiNorm,
      OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm, map_add, map_mul,
      map_pow, titsTwist_twice]
    ring_nf
    have h2 : (2 : Field m) = 0 := CharTwo.two_eq_zero
    simp only [h2, mul_zero, zero_add]

/-- The torus parameter in the nontrivial Suzuki Bruhat relation. -/
noncomputable def bruhatTorus (u : RootGroup m) (hu : u ≠ 1) :
    TorusParameter m :=
  Units.mk0
    (u.suzukiNorm ^ 2 / titsTwist m u.suzukiNorm)
    (div_ne_zero
      (pow_ne_zero 2 (Ovoid.suzukiNorm_ne_zero_of_ne_one hu))
      ((map_ne_zero (titsTwist m)).2
        (Ovoid.suzukiNorm_ne_zero_of_ne_one hu)))

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The underlying field element of the Bruhat torus parameter. -/
@[simp] theorem coe_bruhatTorus (u : RootGroup m) (hu : u ≠ 1) :
    (bruhatTorus u hu : Field m) =
      u.suzukiNorm ^ 2 / titsTwist m u.suzukiNorm :=
  rfl

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The second-coordinate torus weight is the twisted Suzuki norm. -/
theorem torusWeight_bruhatTorus (u : RootGroup m) (hu : u ≠ 1) :
    torusWeight (bruhatTorus u hu) = titsTwist m u.suzukiNorm := by
  have hn : u.suzukiNorm ≠ 0 := Ovoid.suzukiNorm_ne_zero_of_ne_one hu
  have htn : titsTwist m u.suzukiNorm ≠ 0 :=
    (map_ne_zero (titsTwist m)).2 hn
  rw [torusWeight, coe_bruhatTorus]
  simp only [map_div₀, map_pow, titsTwist_twice]
  field_simp [hn, htn]


/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
A nontrivial left root has a nontrivial right Bruhat parameter. -/
theorem bruhatRightRoot_ne_one (u : RootGroup m) (hu : u ≠ 1) :
    bruhatRightRoot u ≠ 1 := by
  intro h
  have hinv : (bruhatRightRoot u)⁻¹ = 1 := by rw [h, inv_one]
  rw [bruhatRightRoot_inv u hu] at hinv
  exact Ovoid.weylAffine_ne_one (inv_ne_one.mpr hu) hinv

private theorem bruhatPoleIff (u v : RootGroup m) (hu : u ≠ 1) (hv : v ≠ 1) :
    bruhatRightRoot u * v = 1 ↔ u * Ovoid.weylAffine v = 1 := by
  have hui : u⁻¹ ≠ 1 := inv_ne_one.mpr hu
  constructor
  · intro h
    have hvd : v = Ovoid.weylAffine u⁻¹ := by
      calc
        v = (bruhatRightRoot u)⁻¹ := eq_inv_of_mul_eq_one_right h
        _ = Ovoid.weylAffine u⁻¹ := bruhatRightRoot_inv u hu
    rw [hvd, Ovoid.weylAffine_weylAffine hui, mul_inv_cancel]
  · intro h
    have hwv : Ovoid.weylAffine v = u⁻¹ := eq_inv_of_mul_eq_one_right h
    have hvd : v = Ovoid.weylAffine u⁻¹ := by
      calc
        v = Ovoid.weylAffine (Ovoid.weylAffine v) :=
          (Ovoid.weylAffine_weylAffine hv).symm
        _ = Ovoid.weylAffine u⁻¹ := congrArg Ovoid.weylAffine hwv
    rw [hvd, ← bruhatRightRoot_inv u hu, mul_inv_cancel]

private noncomputable def bruhatRightRootAux (u : RootGroup m) (hu : u ≠ 1) :
    RootGroup m :=
  torusScale (bruhatTorus u hu)
    (Ovoid.weylAffine (Ovoid.weylAffine u)⁻¹)

private theorem bruhatRightRootAux_eq (u : RootGroup m) (hu : u ≠ 1) :
    bruhatRightRootAux u hu = (Ovoid.weylAffine u⁻¹)⁻¹ := by
  have hn : u.suzukiNorm ≠ 0 := Ovoid.suzukiNorm_ne_zero_of_ne_one hu
  have htn : titsTwist m u.suzukiNorm ≠ 0 :=
    (map_ne_zero (titsTwist m)).2 hn
  ext
  · simp only [bruhatRightRootAux, torusScale_fst, Ovoid.weylAffine_fst,
      RootGroup.snd_inv, RootGroup.fst_inv, Ovoid.weylAffine_snd,
      coe_bruhatTorus, RootGroup.suzukiNorm_inv,
      Ovoid.weylAffine_suzukiNorm, map_div₀]
    field_simp [hn, htn]
    rw [RootGroup.suzukiNorm, titsTwist_suzukiNorm, suzukiNorm]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · simp only [bruhatRightRootAux, torusScale_snd, Ovoid.weylAffine_snd,
      RootGroup.fst_inv, RootGroup.snd_inv, torusWeight_bruhatTorus,
      RootGroup.suzukiNorm_inv, Ovoid.weylAffine_suzukiNorm,
      Ovoid.weylAffine_fst, map_add, map_mul, map_div₀, titsTwist_twice]
    field_simp [hn, htn]
    rw [RootGroup.suzukiNorm, titsTwist_suzukiNorm, suzukiNorm]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]

private theorem bruhatRightRoot_eq_compact (u : RootGroup m) (hu : u ≠ 1) :
    bruhatRightRoot u = (Ovoid.weylAffine u⁻¹)⁻¹ := by
  apply inv_injective
  rw [bruhatRightRoot_inv u hu, inv_inv]

private theorem bruhatRightRootAux_eq_rightRoot
    (u : RootGroup m) (hu : u ≠ 1) :
    bruhatRightRootAux u hu = bruhatRightRoot u := by
  rw [bruhatRightRootAux_eq u hu, bruhatRightRoot_eq_compact u hu]

private theorem bruhatOrigin (u : RootGroup m) (hu : u ≠ 1) :
    Ovoid.weylAffine u *
      torusScale (bruhatTorus u hu) (Ovoid.weylAffine (bruhatRightRoot u)) = 1 := by
  rw [← bruhatRightRootAux_eq_rightRoot u hu, bruhatRightRootAux,
    Ovoid.weylAffine_torusScale]
  have hwi : (Ovoid.weylAffine u)⁻¹ ≠ 1 :=
    inv_ne_one.mpr (Ovoid.weylAffine_ne_one hu)
  rw [Ovoid.weylAffine_weylAffine hwi]
  have hcancel :
      torusScale (bruhatTorus u hu)
          (torusScale (bruhatTorus u hu)⁻¹ (Ovoid.weylAffine u)⁻¹) =
        (Ovoid.weylAffine u)⁻¹ := by
    change (torusScaleHom m (bruhatTorus u hu) *
      torusScaleHom m (bruhatTorus u hu)⁻¹) (Ovoid.weylAffine u)⁻¹ = _
    rw [← map_mul]
    simp
  rw [hcancel, mul_inv_cancel]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Clearing both reciprocal norms produces a large characteristic-two polynomial.
/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The norms of the two generic affine products satisfy the Bruhat scaling relation. -/
theorem suzukiNorm_bruhatRightRoot_mul (u v : RootGroup m)
    (hu : u ≠ 1) (hv : v ≠ 1) :
    (bruhatRightRoot u * v).suzukiNorm =
      (u * Ovoid.weylAffine v).suzukiNorm * v.suzukiNorm / u.suzukiNorm := by
  set n : Field m := u.suzukiNorm
  set r : Field m := v.suzukiNorm
  have hn : n ≠ 0 := by
    simpa only [n] using Ovoid.suzukiNorm_ne_zero_of_ne_one hu
  have hr : r ≠ 0 := by
    simpa only [r] using Ovoid.suzukiNorm_ne_zero_of_ne_one hv
  have htn : titsTwist m n ≠ 0 := (map_ne_zero (titsTwist m)).2 hn
  have htr : titsTwist m r ≠ 0 := (map_ne_zero (titsTwist m)).2 hr
  change suzukiNorm m (bruhatRightRoot u * v).fst
      (bruhatRightRoot u * v).snd =
    suzukiNorm m (u * Ovoid.weylAffine v).fst
      (u * Ovoid.weylAffine v).snd * r / n
  simp only [suzukiNorm, bruhatRightRoot, RootGroup.fst_mul, RootGroup.snd_mul,
    Ovoid.weylAffine_fst, Ovoid.weylAffine_snd, map_div₀, map_add, map_mul,
    map_pow, titsTwist_twice]
  simp only [show u.suzukiNorm = n by rfl, show v.suzukiNorm = r by rfl]
  field_simp [hn, hr, htn, htr]
  simp only [n, r, RootGroup.suzukiNorm, suzukiNorm, map_add, map_mul,
    map_pow, titsTwist_twice]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- Generic affine compatibility needed in the nontrivial Bruhat product. -/
private theorem Ovoid.weylAffine_bruhat_compat
    (u v : RootGroup m) (hu : u ≠ 1) (hv : v ≠ 1)
    (hp : u * Ovoid.weylAffine v ≠ 1)
    (hnorm :
      (bruhatRightRoot u * v).suzukiNorm =
        (u * Ovoid.weylAffine v).suzukiNorm * v.suzukiNorm / u.suzukiNorm) :
    Ovoid.weylAffine (u * Ovoid.weylAffine v) =
      Ovoid.weylAffine u *
        torusScale (bruhatTorus u hu)
          (Ovoid.weylAffine (bruhatRightRoot u * v)) := by
  have hNu : u.suzukiNorm ≠ 0 := Ovoid.suzukiNorm_ne_zero_of_ne_one hu
  have hNv : v.suzukiNorm ≠ 0 := Ovoid.suzukiNorm_ne_zero_of_ne_one hv
  have hNp : (u * Ovoid.weylAffine v).suzukiNorm ≠ 0 :=
    Ovoid.suzukiNorm_ne_zero_of_ne_one hp
  have htNu : titsTwist m u.suzukiNorm ≠ 0 :=
    (map_ne_zero (titsTwist m)).2 hNu
  have htNv : titsTwist m v.suzukiNorm ≠ 0 :=
    (map_ne_zero (titsTwist m)).2 hNv
  have hPcoord :
      (u * Ovoid.weylAffine v).suzukiNorm =
        OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm m
          (u.fst + v.snd / v.suzukiNorm)
          (u.snd + v.fst / v.suzukiNorm +
            (v.snd / v.suzukiNorm) * titsTwist m u.fst) := by
    rfl
  ext
  · simp only [Ovoid.weylAffine_fst, Ovoid.weylAffine_snd,
      RootGroup.snd_mul, torusScale_fst, RootGroup.fst_mul]
    rw [hnorm]
    simp only [coe_bruhatTorus, bruhatRightRoot]
    field_simp [hNu, hNv, hNp, htNu]
    simp only [map_div₀, map_add, map_mul, titsTwist_twice]
    field_simp [hNu, htNu]
    rw [hPcoord]
    simp only [OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm,
      map_div₀, map_add, map_mul, titsTwist_twice]
    field_simp [hNv, htNv]
    simp only [RootGroup.suzukiNorm,
      OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm,
      map_add, map_mul, map_pow, titsTwist_twice]
    ring_nf
    set_option maxRecDepth 10000 in
      simp [CharTwo.ofNat_eq_mod]
  · simp only [Ovoid.weylAffine_snd, Ovoid.weylAffine_fst,
      RootGroup.fst_mul, RootGroup.snd_mul, torusScale_snd, torusScale_fst]
    rw [hnorm]
    simp only [torusWeight_bruhatTorus, coe_bruhatTorus, bruhatRightRoot]
    field_simp [hNu, hNv, hNp, htNu]
    simp only [map_div₀, map_add, map_mul, titsTwist_twice]
    field_simp [hNu, htNu]
    rw [hPcoord]
    simp only [OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm,
      map_div₀, map_add, map_mul, titsTwist_twice]
    field_simp [hNv, htNv]
    simp only [RootGroup.suzukiNorm,
      OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm,
      map_add, map_mul, map_pow, titsTwist_twice]
    set_option maxRecDepth 10000 in
      ring_nf
    set_option maxRecDepth 10000 in
      simp [CharTwo.ofNat_eq_mod]

private theorem bruhatRelationAtInfinity (u : RootGroup m) (hu : u ≠ 1) :
    (weylElement m * rootHom m u * weylElement m) • Ovoid.infinity m =
      (rootHom m (Ovoid.weylAffine u) *
        torusHom m (bruhatTorus u hu) * weylElement m *
          rootHom m (bruhatRightRoot u)) • Ovoid.infinity m := by
  simp only [mul_smul, rootHom_smul_infinity, weylElement_smul_infinity,
    Ovoid.origin, rootHom_smul_affine, mul_one, torusHom_smul_affine, map_one,
    weylElement_smul_affine_of_ne_one u hu]

private theorem bruhatRelationAtOrigin (u : RootGroup m) (hu : u ≠ 1) :
    (weylElement m * rootHom m u * weylElement m) • Ovoid.origin m =
      (rootHom m (Ovoid.weylAffine u) *
        torusHom m (bruhatTorus u hu) * weylElement m *
          rootHom m (bruhatRightRoot u)) • Ovoid.origin m := by
  rw [mul_smul, mul_smul, weylElement_smul_origin, rootHom_smul_infinity,
    weylElement_smul_infinity]
  change Ovoid.origin m =
    rootHom m (Ovoid.weylAffine u) •
      torusHom m (bruhatTorus u hu) •
        weylElement m • rootHom m (bruhatRightRoot u) • Ovoid.affine 1
  rw [rootHom_smul_affine, mul_one,
    weylElement_smul_affine_of_ne_one _ (bruhatRightRoot_ne_one u hu),
    torusHom_smul_affine, rootHom_smul_affine, bruhatOrigin u hu]
  rfl

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The explicit nontrivial-root
relation in the standard Suzuki Bruhat decomposition. -/
theorem weylElement_mul_rootHom_mul_weylElement
    (u : RootGroup m) (hu : u ≠ 1) :
    weylElement m * rootHom m u * weylElement m =
      rootHom m (Ovoid.weylAffine u) *
        torusHom m (bruhatTorus u hu) * weylElement m *
          rootHom m (bruhatRightRoot u) := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro p
  change (weylElement m * rootHom m u * weylElement m) • p =
    (rootHom m (Ovoid.weylAffine u) *
      torusHom m (bruhatTorus u hu) * weylElement m *
        rootHom m (bruhatRightRoot u)) • p
  cases p with
  | none => exact bruhatRelationAtInfinity u hu
  | some v =>
      change (weylElement m * rootHom m u * weylElement m) • Ovoid.affine v =
        (rootHom m (Ovoid.weylAffine u) *
          torusHom m (bruhatTorus u hu) * weylElement m *
            rootHom m (bruhatRightRoot u)) • Ovoid.affine v
      by_cases hv : v = 1
      · subst v
        exact bruhatRelationAtOrigin u hu
      · by_cases hp : u * Ovoid.weylAffine v = 1
        · have hq : bruhatRightRoot u * v = 1 :=
            (bruhatPoleIff u v hu hv).mpr hp
          rw [mul_smul, mul_smul, weylElement_smul_affine_of_ne_one v hv,
            rootHom_smul_affine, hp]
          change weylElement m • Ovoid.origin m = _
          rw [weylElement_smul_origin, mul_smul, mul_smul, mul_smul,
            rootHom_smul_affine, hq]
          change Ovoid.infinity m =
            rootHom m (Ovoid.weylAffine u) •
              torusHom m (bruhatTorus u hu) • weylElement m • Ovoid.origin m
          rw [weylElement_smul_origin, torusHom_smul_infinity,
            rootHom_smul_infinity]
        · have hq : bruhatRightRoot u * v ≠ 1 := by
            intro h
            exact hp ((bruhatPoleIff u v hu hv).mp h)
          rw [mul_smul, mul_smul, weylElement_smul_affine_of_ne_one v hv,
            rootHom_smul_affine, weylElement_smul_affine_of_ne_one _ hp,
            mul_smul, mul_smul, mul_smul, rootHom_smul_affine,
            weylElement_smul_affine_of_ne_one _ hq, torusHom_smul_affine,
            rootHom_smul_affine]
          exact congrArg Ovoid.affine
            (Ovoid.weylAffine_bruhat_compat u v hu hv hp
              (suzukiNorm_bruhatRightRoot_mul u v hu hv))


end

section /- §3 Lemma 1 Suzuki target: the two Bruhat cells (pp. 100--107) -/

variable (m : ℕ)

/-- The union of the two prospective Bruhat cells `B` and `B w B`. -/
def InStandardBruhatCells (g : standardPermGroup m) : Prop :=
  g ∈ standardBorel m ∨
    ∃ b₁ ∈ standardBorel m, ∃ b₂ ∈ standardBorel m,
      g = b₁ * weylElement m * b₂

private theorem one_mem_standardBruhatCells :
    InStandardBruhatCells m 1 :=
  Or.inl (standardBorel m).one_mem

private theorem borel_mul_mem_standardBruhatCells
    {b g : standardPermGroup m}
    (hb : b ∈ standardBorel m) (hg : InStandardBruhatCells m g) :
    InStandardBruhatCells m (b * g) := by
  rcases hg with hg | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact Or.inl ((standardBorel m).mul_mem hb hg)
  · right
    exact ⟨b * b₁, (standardBorel m).mul_mem hb hb₁, b₂, hb₂, by
      simp only [mul_assoc]⟩

private theorem mul_borel_mem_standardBruhatCells
    {g b : standardPermGroup m}
    (hg : InStandardBruhatCells m g) (hb : b ∈ standardBorel m) :
    InStandardBruhatCells m (g * b) := by
  rcases hg with hg | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact Or.inl ((standardBorel m).mul_mem hg hb)
  · right
    exact ⟨b₁, hb₁, b₂ * b, (standardBorel m).mul_mem hb₂ hb, by
      simp only [mul_assoc]⟩

private theorem one_mul_mem_standardBruhatCells
    {g : standardPermGroup m} (hg : InStandardBruhatCells m g) :
    InStandardBruhatCells m (1 * g) := by
  simpa only [one_mul] using hg

private theorem rootHom_mul_mem_standardBruhatCells
    (u : RootGroup m) {g : standardPermGroup m}
    (hg : InStandardBruhatCells m g) :
    InStandardBruhatCells m (rootHom m u * g) :=
  borel_mul_mem_standardBruhatCells m (rootHom_mem_standardBorel u) hg

private theorem torusHom_mul_mem_standardBruhatCells
    (c : TorusParameter m) {g : standardPermGroup m}
    (hg : InStandardBruhatCells m g) :
    InStandardBruhatCells m (torusHom m c * g) :=
  borel_mul_mem_standardBruhatCells m (torusHom_mem_standardBorel c) hg

/-- The only relations needed by the set-theoretic two-cell argument.

The second field is deliberately weaker than a coordinate formula: a concrete
Weyl--root identity supplies its two Borel factors immediately. -/
private structure StandardBruhatRelations : Prop where
  weyl_torus_mem : ∀ c : TorusParameter m,
    weylElement m * torusHom m c * weylElement m ∈ standardBorel m
  weyl_root_eq : ∀ u : RootGroup m, u ≠ 1 →
    ∃ b₁ ∈ standardBorel m, ∃ b₂ ∈ standardBorel m,
      weylElement m * rootHom m u * weylElement m =
        b₁ * weylElement m * b₂

private theorem weyl_mul_mem_standardBruhatCells
    (hrel : StandardBruhatRelations m)
    {g : standardPermGroup m} (hg : InStandardBruhatCells m g) :
    InStandardBruhatCells m (weylElement m * g) := by
  have hw : weylElement m * weylElement m = 1 := by
    simpa only [pow_two] using weylElement_sq_eq_one m
  rcases hg with hg | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · right
    exact ⟨1, (standardBorel m).one_mem, g, hg, by simp⟩
  · obtain ⟨p, hp, -⟩ :=
      (mem_standardBorel_iff_existsUnique_root_torus b₁).mp hb₁
    rcases p with ⟨u, c⟩
    have hroot :
        InStandardBruhatCells m
          (weylElement m * rootHom m u * weylElement m) := by
      by_cases hu : u = 1
      · left
        subst u
        simpa only [map_one, mul_one, hw] using (standardBorel m).one_mem
      · exact Or.inr (hrel.weyl_root_eq u hu)
    have htorus := hrel.weyl_torus_mem c
    have hcore := mul_borel_mem_standardBruhatCells m hroot htorus
    have hfactor :
        weylElement m * (rootHom m u * torusHom m c) * weylElement m =
          (weylElement m * rootHom m u * weylElement m) *
            (weylElement m * torusHom m c * weylElement m) := by
      calc
        _ = weylElement m * rootHom m u * torusHom m c * weylElement m := by
          ac_rfl
        _ = weylElement m * rootHom m u * 1 * torusHom m c * weylElement m := by
          simp only [mul_one]
        _ = weylElement m * rootHom m u *
              (weylElement m * weylElement m) * torusHom m c * weylElement m := by
          rw [hw]
        _ = _ := by ac_rfl
    have hconj :
        InStandardBruhatCells m (weylElement m * b₁ * weylElement m) := by
      rw [hp, hfactor]
      exact hcore
    have hfinal := mul_borel_mem_standardBruhatCells m hconj hb₂
    simpa only [mul_assoc] using hfinal

private theorem inv_mem_standardGeneratorSet
    {x : Equiv.Perm (Ovoid m)} (hx : x ∈ standardGeneratorSet m) :
    x⁻¹ ∈ standardGeneratorSet m := by
  rcases hx with ⟨u, rfl⟩ | (⟨c, rfl⟩ | hx)
  · exact Or.inl ⟨u⁻¹, map_inv (Ovoid.rootPermHom m) u⟩
  · exact Or.inr (Or.inl ⟨c⁻¹, map_inv (Ovoid.torusPerm m) c⟩)
  · have hxw : x = Ovoid.weylPerm m := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    right
    right
    rw [Set.mem_singleton_iff]
    change (Ovoid.weylPerm m).symm = Ovoid.weylPerm m
    exact Ovoid.weylPerm_symm m

private theorem standardGenerator_mul_mem_standardBruhatCells
    (hrel : StandardBruhatRelations m)
    {x : Equiv.Perm (Ovoid m)} (hx : x ∈ standardGeneratorSet m)
    {g : standardPermGroup m} (hg : InStandardBruhatCells m g) :
    InStandardBruhatCells m
      ((⟨x, Subgroup.subset_closure hx⟩ : standardPermGroup m) * g) := by
  rcases hx with ⟨u, rfl⟩ | (⟨c, rfl⟩ | hx)
  · change InStandardBruhatCells m (rootHom m u * g)
    exact rootHom_mul_mem_standardBruhatCells m u hg
  · change InStandardBruhatCells m (torusHom m c * g)
    exact torusHom_mul_mem_standardBruhatCells m c hg
  · have hxw : x = Ovoid.weylPerm m := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    change InStandardBruhatCells m (weylElement m * g)
    exact weyl_mul_mem_standardBruhatCells m hrel hg

/-- Every element of the standard generated group belongs to `B ∪ B w B`.

This is the closure-induction endpoint. The induction predicate says that the
ambient permutation acts by left multiplication preserving the two cells.
The inverse-generator branch uses `inv_mem_standardGeneratorSet`; it does not
require the two-cell set itself to be a subgroup. -/
private theorem mem_standardBruhatCells
    (hrel : StandardBruhatRelations m) (g : standardPermGroup m) :
    InStandardBruhatCells m g := by
  let P : (x : Equiv.Perm (Ovoid m)) →
      x ∈ Subgroup.closure (standardGeneratorSet m) → Prop :=
    fun x hx ↦ ∀ y : standardPermGroup m, InStandardBruhatCells m y →
      InStandardBruhatCells m
        ((⟨x, hx⟩ : standardPermGroup m) * y)
  have hP : P (g : Equiv.Perm (Ovoid m)) g.property := by
    apply Subgroup.closure_induction_left (p := P)
    · intro y hy
      change InStandardBruhatCells m ((1 : standardPermGroup m) * y)
      exact one_mul_mem_standardBruhatCells m hy
    · intro x hx y hy ih z hz
      have hyz := ih z hz
      have hxyz := standardGenerator_mul_mem_standardBruhatCells m hrel hx hyz
      change InStandardBruhatCells m
        (((⟨x, Subgroup.subset_closure hx⟩ : standardPermGroup m) *
          (⟨y, hy⟩ : standardPermGroup m)) * z)
      simpa only [mul_assoc] using hxyz
    · intro x hx y hy ih z hz
      have hyz := ih z hz
      have hxyz := standardGenerator_mul_mem_standardBruhatCells m hrel
        (inv_mem_standardGeneratorSet m hx) hyz
      change InStandardBruhatCells m
        (((⟨x⁻¹, Subgroup.subset_closure
              (inv_mem_standardGeneratorSet m hx)⟩ : standardPermGroup m) *
          (⟨y, hy⟩ : standardPermGroup m)) * z)
      simpa only [mul_assoc] using hxyz
  have hg := hP 1 (one_mem_standardBruhatCells m)
  simpa only [mul_one] using hg


private theorem concreteStandardBruhatRelations (m : ℕ) :
    StandardBruhatRelations m where
  weyl_torus_mem c := by
    rw [weylElement_mul_torusHom_mul_weylElement]
    exact torusHom_mem_standardBorel c⁻¹
  weyl_root_eq u hu := by
    refine ⟨rootHom m (Ovoid.weylAffine u) * torusHom m (bruhatTorus u hu),
      (standardBorel m).mul_mem (rootHom_mem_standardBorel _)
        (torusHom_mem_standardBorel _),
      rootHom m (bruhatRightRoot u), rootHom_mem_standardBorel _, ?_⟩
    exact weylElement_mul_rootHom_mul_weylElement u hu

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
Every standard Suzuki-group
element lies in `B` or in `B w B`. -/
theorem standardBruhatDecomposition (g : standardPermGroup m) :
    InStandardBruhatCells m g :=
  mem_standardBruhatCells m (concreteStandardBruhatRelations m) g

end

section /- §3 Lemma 1 Suzuki target: point stabilizer and group order (pp. 100--107) -/

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The standard Borel subgroup is
exactly the stabilizer of infinity. -/
theorem standardBorel_eq_infinityStabilizer :
    standardBorel m =
      MulAction.stabilizer (standardPermGroup m) (Ovoid.infinity m) := by
  apply le_antisymm standardBorel_le_infinityStabilizer
  intro g hg
  rcases standardBruhatDecomposition m g with hgB | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact hgB
  · rw [MulAction.mem_stabilizer_iff] at hg
    rcases hb₁ with ⟨x, rfl⟩
    have hb₂fix : b₂ • Ovoid.infinity m = Ovoid.infinity m :=
      MulAction.mem_stabilizer_iff.mp
        (standardBorel_le_infinityStabilizer hb₂)
    rw [mul_smul, mul_smul, hb₂fix, weylElement_smul_infinity] at hg
    have : Ovoid.affine x.left = Ovoid.infinity m := by
      simp only [borelHom_apply, mul_smul, Ovoid.origin,
        torusHom_smul_affine, map_one, rootHom_smul_affine, mul_one] at hg
      exact hg
    exact (Ovoid.affine_ne_infinity x.left this).elim

/-- **Peterfalvi Part II, Ch. I, §3 Lemma 1 (Suzuki target).**
The exact order of the standard
Suzuki permutation group is `q² (q² + 1) (q - 1)`, where `q = 2^(2m+1)`. -/
theorem natCard_standardPermGroup (m : ℕ) :
    Nat.card (standardPermGroup m) =
      2 ^ (2 * (2 * m + 1)) *
        (2 ^ (2 * (2 * m + 1)) + 1) *
          (2 ^ (2 * m + 1) - 1) := by
  letI : MulAction.IsPretransitive (standardPermGroup m) (Ovoid m) :=
    standardPermGroup_isPretransitive m
  have hindex := MulAction.index_stabilizer_of_transitive
    (standardPermGroup m) (Ovoid.infinity m)
  rw [← standardBorel_eq_infinityStabilizer, Ovoid.natCard] at hindex
  calc
    Nat.card (standardPermGroup m) =
        Nat.card (standardBorel m) * (standardBorel m).index :=
      (standardBorel m).card_mul_index.symm
    _ = 2 ^ (2 * (2 * m + 1)) * (2 ^ (2 * m + 1) - 1) *
        (2 ^ (2 * (2 * m + 1)) + 1) := by
      rw [natCard_standardBorel, hindex]
    _ = _ := by ac_rfl

end

end OddOrder.GroupTheory.SpecificGroups.Suzuki
