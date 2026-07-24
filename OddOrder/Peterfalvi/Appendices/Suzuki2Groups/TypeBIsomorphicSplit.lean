/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralExtensionAutomorphisms
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.AutomorphismInducedMaps
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanDE

/-!
# Peterfalvi Appendix III, Theorem (e), forward direction: setup

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Theorem (e), p. 141 (issue 2052).

For the type-B model `B(n, φ, ε)` the theorem identifies the actor `K`
with `F*` acting *diagonally* on the quotient coordinate `F × F` —
`(a, b)^x = (xa, xb)` — and by `c^x = xφ(x)·c` on the center.  This file
constructs, for each `x ∈ F*`, an actual automorphism of the model
inducing that pair (`exists_diagonalAut`): the compatibility identity
`q(xa, xb) = xφ(x)·q(a, b)` of the type-B square map feeds the Lemma 1(c)
sufficiency (`exists_mulEquiv_of_comp_squareMap_eq`).

The isomorphic-split payload of Theorem (e) built from these
automorphisms — the invariant summands `F × 0` and `0 × F` swapped by a
`K`-equivariant isomorphism — is assembled downstream in this file's
follow-up sections.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open QuadraticExtension

noncomputable section

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (phi : RingAut F) (epsilon : F)

local instance instAlgebraZMod2TypeBSplit : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

omit [Finite F] in
/-- **The type-B square map is `xφ(x)`-semilinear for the diagonal scalar
action**: `q(xa, xb) = xφ(x)·q(a, b)`. -/
theorem typeBQuadraticMap_smul (x : F) (v : F × F) :
    typeBQuadraticMap phi epsilon (x * v.1, x * v.2) =
      x * phi x * typeBQuadraticMap phi epsilon v := by
  simp only [typeBQuadraticMap_apply, map_mul]
  ring

/-- The diagonal scalar action of a unit on `F × F`, as an additive
automorphism. -/
def diagUnitsAddEquiv (x : Fˣ) : (F × F) ≃+ (F × F) :=
  AddEquiv.mk' (Equiv.prodCongr (Equiv.mulLeft₀ (x : F) x.ne_zero)
    (Equiv.mulLeft₀ (x : F) x.ne_zero)) (by
      intro v v'
      ext <;> simp [mul_add])

omit [Finite F] [CharP F 2] in
@[simp] theorem diagUnitsAddEquiv_apply (x : Fˣ) (v : F × F) :
    diagUnitsAddEquiv x v = ((x : F) * v.1, (x : F) * v.2) :=
  rfl

/-- The multiplication by `xφ(x)` on the central coordinate, as an
additive automorphism. -/
def normUnitsAddEquiv (x : Fˣ) : F ≃+ F :=
  AddEquiv.mk'
    (Equiv.mulLeft₀ ((x : F) * phi x)
      (mul_ne_zero x.ne_zero (Units.map (phi : F →* F) x).ne_zero))
    (mul_add ((x : F) * phi x))

omit [Finite F] [CharP F 2] in
@[simp] theorem normUnitsAddEquiv_apply (x : Fˣ) (w : F) :
    normUnitsAddEquiv phi x w = (x : F) * phi x * w :=
  rfl

/-- **The diagonal automorphisms of the type-B model** (Appendix III,
Theorem (e), p. 141): for each `x ∈ F*` the model `B(n, φ, ε)` has an
automorphism acting by `c ↦ xφ(x)·c` on the embedded center and by
`(a, b) ↦ (xa, xb)` on the quotient coordinate.  The compatible pair
`(diag x, xφ(x)·)` lifts by the Lemma 1(c) sufficiency. -/
theorem exists_diagonalAut (x : Fˣ) :
    ∃ Φ : MulAut (TypeBModel phi epsilon),
      (∀ w : F,
        Φ ((QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
            (Module.finBasis (ZMod 2) (F × F))).inl (Multiplicative.ofAdd w)) =
          (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
            (Module.finBasis (ZMod 2) (F × F))).inl
            (Multiplicative.ofAdd ((x : F) * phi x * w))) ∧
      ∀ e : TypeBModel phi epsilon,
        ((QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
            (Module.finBasis (ZMod 2) (F × F))).rightHom (Φ e)).toAdd =
          ((x : F) * ((QuadraticExtension.extension
              (typeBQuadraticMap phi epsilon)
              (Module.finBasis (ZMod 2) (F × F))).rightHom e).toAdd.1,
            (x : F) * ((QuadraticExtension.extension
              (typeBQuadraticMap phi epsilon)
              (Module.finBasis (ZMod 2) (F × F))).rightHom e).toAdd.2) := by
  obtain ⟨Φ, hinl, hright⟩ :=
    GroupExtension.exists_mulEquiv_of_comp_squareMap_eq
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F)))
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F)))
      (range_inl_le_center _ _) (range_inl_le_center _ _)
      ⇑(typeBQuadraticMap phi epsilon) ⇑(typeBQuadraticMap phi epsilon)
      (Module.finBasis (ZMod 2) (F × F))
      (fun e => sq_eq_inl_q _ _ e) (fun e => sq_eq_inl_q _ _ e)
      (diagUnitsAddEquiv x) (normUnitsAddEquiv phi x)
      (fun v => by
        rw [normUnitsAddEquiv_apply, diagUnitsAddEquiv_apply]
        exact (typeBQuadraticMap_smul phi epsilon (x : F) v).symm)
  refine ⟨Φ, fun w => ?_, fun e => ?_⟩
  · rw [hinl w]
    rfl
  · rw [hright e]
    rfl

/-! ### The diagonal actor subgroup -/

open OddOrder.Isaacs.Ch03 in
/-- An automorphism of the model *induces the diagonal action of `x`* when
its effect on the quotient coordinate is `(a, b) ↦ (xa, xb)`. -/
def InducesDiag (Φ : MulAut (TypeBModel phi epsilon)) (x : Fˣ) : Prop :=
  ∀ e : TypeBModel phi epsilon,
    ((QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F))).rightHom (Φ e)).toAdd =
      ((x : F) * ((QuadraticExtension.extension
          (typeBQuadraticMap phi epsilon)
          (Module.finBasis (ZMod 2) (F × F))).rightHom e).toAdd.1,
        (x : F) * ((QuadraticExtension.extension
          (typeBQuadraticMap phi epsilon)
          (Module.finBasis (ZMod 2) (F × F))).rightHom e).toAdd.2)

theorem InducesDiag.one : InducesDiag phi epsilon 1 1 := by
  intro e
  simp

theorem InducesDiag.mul {Φ Ψ : MulAut (TypeBModel phi epsilon)} {x y : Fˣ}
    (hΦ : InducesDiag phi epsilon Φ x) (hΨ : InducesDiag phi epsilon Ψ y) :
    InducesDiag phi epsilon (Φ * Ψ) (x * y) := by
  intro e
  have h1 := hΦ (Ψ e)
  have h2 := hΨ e
  change ((QuadraticExtension.extension _ _).rightHom (Φ (Ψ e))).toAdd = _
  rw [h1, h2]
  ext <;> push_cast <;> ring

theorem InducesDiag.inv {Φ : MulAut (TypeBModel phi epsilon)} {x : Fˣ}
    (hΦ : InducesDiag phi epsilon Φ x) :
    InducesDiag phi epsilon Φ⁻¹ x⁻¹ := by
  intro e
  have h := hΦ (Φ⁻¹ e)
  rw [show Φ (Φ⁻¹ e) = e from Φ.apply_symm_apply e] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only at h1 h2
  ext
  · rw [h1, Units.val_inv_eq_inv_val, ← mul_assoc,
      inv_mul_cancel₀ x.ne_zero, one_mul]
  · rw [h2, Units.val_inv_eq_inv_val, ← mul_assoc,
      inv_mul_cancel₀ x.ne_zero, one_mul]

/-- **The diagonal actor of Theorem (e)** (p. 141): the subgroup of
automorphisms of the type-B model inducing the diagonal action of some
unit on the quotient coordinate.  By `exists_diagonalAut` its image on
the quotient realizes the full diagonal `F*`-action. -/
def diagonalAuts : Subgroup (MulAut (TypeBModel phi epsilon)) where
  carrier := {Φ | ∃ x : Fˣ, InducesDiag phi epsilon Φ x}
  one_mem' := ⟨1, InducesDiag.one phi epsilon⟩
  mul_mem' := fun ⟨x, hx⟩ ⟨y, hy⟩ =>
    ⟨x * y, InducesDiag.mul phi epsilon hx hy⟩
  inv_mem' := fun ⟨x, hx⟩ => ⟨x⁻¹, InducesDiag.inv phi epsilon hx⟩

/-! ### The central quotient in coordinates -/

/-- The center of the type-B model is the embedded kernel (`ε ≠ 0`). -/
theorem center_typeBModel (hε : epsilon ≠ 0) :
    Subgroup.center (TypeBModel phi epsilon) =
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F))).inl.range :=
  center_eq_range_inl _ _
    (fun v hadd => typeBQuadraticMap_radical_eq_zero phi epsilon hε v hadd)

/-- The central quotient of the type-B model, identified with the
coordinate plane `F × F` via the quotient coordinate. -/
def quotientCenterEquiv (hε : epsilon ≠ 0) :
    (TypeBModel phi epsilon ⧸ Subgroup.center (TypeBModel phi epsilon)) ≃*
      Multiplicative (F × F) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [center_typeBModel phi epsilon hε]
    exact (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
      (Module.finBasis (ZMod 2) (F × F))).range_inl_eq_ker_rightHom)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F))).rightHom_surjective)

@[simp] theorem quotientCenterEquiv_mk (hε : epsilon ≠ 0)
    (e : TypeBModel phi epsilon) :
    quotientCenterEquiv phi epsilon hε (e : TypeBModel phi epsilon ⧸
        Subgroup.center (TypeBModel phi epsilon)) =
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F))).rightHom e :=
  rfl

/-- The first coordinate line `F × 0`, as a subgroup of the multiplicative
plane. -/
def leftLine : Subgroup (Multiplicative (F × F)) :=
  AddSubgroup.toSubgroup (AddSubgroup.prod ⊤ ⊥)

/-- The second coordinate line `0 × F`. -/
def rightLine : Subgroup (Multiplicative (F × F)) :=
  AddSubgroup.toSubgroup (AddSubgroup.prod ⊥ ⊤)

omit [Finite F] [CharP F 2] in
theorem mem_leftLine_iff (y : Multiplicative (F × F)) :
    y ∈ leftLine (F := F) ↔ y.toAdd.2 = 0 := by
  change y.toAdd ∈ AddSubgroup.prod ⊤ ⊥ ↔ _
  simp [AddSubgroup.mem_prod]

omit [Finite F] [CharP F 2] in
theorem mem_rightLine_iff (y : Multiplicative (F × F)) :
    y ∈ rightLine (F := F) ↔ y.toAdd.1 = 0 := by
  change y.toAdd ∈ AddSubgroup.prod ⊥ ⊤ ↔ _
  simp [AddSubgroup.mem_prod]

/-! ### The isomorphic split -/

open OddOrder.Isaacs.Ch03 in
private theorem quotient_action_eq (hε : epsilon ≠ 0)
    (k : ↥(diagonalAuts phi epsilon)) {x : Fˣ}
    (hx : InducesDiag phi epsilon k.val x)
    (y : TypeBModel phi epsilon ⧸
      Subgroup.center (TypeBModel phi epsilon)) :
    (quotientCenterEquiv phi epsilon hε
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic
            (diagonalAuts phi epsilon).subtype) k y)).toAdd =
      ((x : F) * (quotientCenterEquiv phi epsilon hε y).toAdd.1,
        (x : F) * (quotientCenterEquiv phi epsilon hε y).toAdd.2) := by
  refine QuotientGroup.induction_on y fun e => ?_
  have h1 : (IsAInvariant.quotientMulAutHom
      (IsAInvariant.of_characteristic
        (diagonalAuts phi epsilon).subtype) k)
      ((e : TypeBModel phi epsilon ⧸
        Subgroup.center (TypeBModel phi epsilon))) =
      ((k.val e : TypeBModel phi epsilon) : TypeBModel phi epsilon ⧸
        Subgroup.center (TypeBModel phi epsilon)) := rfl
  rw [h1, quotientCenterEquiv_mk, quotientCenterEquiv_mk]
  exact hx e

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03 in
/-- **Peterfalvi Appendix III, Theorem (e), forward half, model form**
(p. 141): for the type-B model the central quotient splits as the direct
sum of the two coordinate lines `F × 0` and `0 × F`, which are invariant
under the diagonal actor and equivariantly isomorphic via the coordinate
swap. -/
theorem nonempty_isomorphicOrderQModuleSplit_diagonalAuts
    (hε : epsilon ≠ 0) :
    Nonempty (IsomorphicOrderQModuleSplit
      (diagonalAuts phi epsilon).subtype
      (Subgroup.center (TypeBModel phi epsilon))
      (IsAInvariant.of_characteristic _)) := by
  classical
  set χ := quotientCenterEquiv phi epsilon hε with hχdef
  set L : Subgroup (TypeBModel phi epsilon ⧸
      Subgroup.center (TypeBModel phi epsilon)) :=
    (leftLine (F := F)).comap χ.toMonoidHom with hLdef
  set R : Subgroup (TypeBModel phi epsilon ⧸
      Subgroup.center (TypeBModel phi epsilon)) :=
    (rightLine (F := F)).comap χ.toMonoidHom with hRdef
  have hmemL : ∀ y, y ∈ L ↔ (χ y).toAdd.2 = 0 := fun y => by
    rw [hLdef, Subgroup.mem_comap, mem_leftLine_iff]
    exact Iff.rfl
  have hmemR : ∀ y, y ∈ R ↔ (χ y).toAdd.1 = 0 := fun y => by
    rw [hRdef, Subgroup.mem_comap, mem_rightLine_iff]
    exact Iff.rfl
  -- elementary abelian quotient
  have hEA : IsElementaryAbelian 2
      (TypeBModel phi epsilon ⧸ Subgroup.center (TypeBModel phi epsilon)) := by
    constructor
    · intro a b
      apply χ.injective
      rw [map_mul, map_mul, mul_comm]
    · intro a
      apply χ.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      ext
      · rw [Prod.smul_fst, two_nsmul, CharTwo.add_self_eq_zero, Prod.fst_zero]
      · rw [Prod.smul_snd, two_nsmul, CharTwo.add_self_eq_zero, Prod.snd_zero]
  -- invariance of the coordinate lines
  have hLinv : IsAInvariant
      (IsAInvariant.quotientMulAutHom (IsAInvariant.of_characteristic
        (diagonalAuts phi epsilon).subtype)) L := by
    rw [isAInvariant_iff_smul_mem]
    intro k y hy
    obtain ⟨x, hx⟩ := k.2
    rw [hmemL] at hy ⊢
    have h2 := congrArg Prod.snd (quotient_action_eq phi epsilon hε k hx y)
    simp only at h2
    rw [h2, hy, mul_zero]
  have hRinv : IsAInvariant
      (IsAInvariant.quotientMulAutHom (IsAInvariant.of_characteristic
        (diagonalAuts phi epsilon).subtype)) R := by
    rw [isAInvariant_iff_smul_mem]
    intro k y hy
    obtain ⟨x, hx⟩ := k.2
    rw [hmemR] at hy ⊢
    have h1 := congrArg Prod.fst (quotient_action_eq phi epsilon hε k hx y)
    simp only at h1
    rw [h1, hy, mul_zero]
  -- cardinalities
  have hZcard : Nat.card ↥(Subgroup.center (TypeBModel phi epsilon)) =
      Nat.card F := by
    rw [center_typeBModel phi epsilon hε]
    exact (Nat.card_congr (MonoidHom.ofInjective
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F))).inl_injective).toEquiv).symm
  have hLLcard : Nat.card ↥(leftLine (F := F)) = Nat.card F := by
    refine Nat.card_congr ⟨fun s => s.val.toAdd.1,
      fun a => ⟨Multiplicative.ofAdd (a, 0), (mem_leftLine_iff _).mpr rfl⟩,
      fun s => ?_, fun a => rfl⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact Prod.ext rfl ((mem_leftLine_iff s.val).mp s.2).symm
  have hRLcard : Nat.card ↥(rightLine (F := F)) = Nat.card F := by
    refine Nat.card_congr ⟨fun s => s.val.toAdd.2,
      fun a => ⟨Multiplicative.ofAdd (0, a), (mem_rightLine_iff _).mpr rfl⟩,
      fun s => ?_, fun a => rfl⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact Prod.ext ((mem_rightLine_iff s.val).mp s.2).symm rfl
  have hLcard : Nat.card ↥L = Nat.card F := by
    rw [← hLLcard]
    refine Nat.card_congr
      ⟨fun s => ⟨χ s.val, (mem_leftLine_iff _).mpr ((hmemL s.val).mp s.2)⟩,
        fun t => ⟨χ.symm t.val, (hmemL _).mpr (by
          rw [χ.apply_symm_apply]
          exact (mem_leftLine_iff _).mp t.2)⟩,
        fun s => Subtype.ext (χ.symm_apply_apply s.val),
        fun t => Subtype.ext (χ.apply_symm_apply t.val)⟩
  have hRcard : Nat.card ↥R = Nat.card F := by
    rw [← hRLcard]
    refine Nat.card_congr
      ⟨fun s => ⟨χ s.val, (mem_rightLine_iff _).mpr ((hmemR s.val).mp s.2)⟩,
        fun t => ⟨χ.symm t.val, (hmemR _).mpr (by
          rw [χ.apply_symm_apply]
          exact (mem_rightLine_iff _).mp t.2)⟩,
        fun s => Subtype.ext (χ.symm_apply_apply s.val),
        fun t => Subtype.ext (χ.apply_symm_apply t.val)⟩
  -- complementarity
  have hcompl : IsCompl L R := by
    constructor
    · rw [disjoint_iff_inf_le]
      intro y hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyL, hyR⟩ := hy
      rw [hmemL] at hyL
      rw [hmemR] at hyR
      rw [Subgroup.mem_bot]
      apply χ.injective
      rw [map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact Prod.ext hyR hyL
    · rw [codisjoint_iff_le_sup]
      intro y _
      have hL1 : χ.symm (Multiplicative.ofAdd ((χ y).toAdd.1, 0)) ∈ L := by
        rw [hmemL, χ.apply_symm_apply]
        rfl
      have hR1 : χ.symm (Multiplicative.ofAdd (0, (χ y).toAdd.2)) ∈ R := by
        rw [hmemR, χ.apply_symm_apply]
        rfl
      have hdecomp : y =
          χ.symm (Multiplicative.ofAdd ((χ y).toAdd.1, 0)) *
            χ.symm (Multiplicative.ofAdd (0, (χ y).toAdd.2)) := by
        apply χ.injective
        rw [map_mul, χ.apply_symm_apply, χ.apply_symm_apply]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul]
        exact Prod.ext (by simp) (by simp)
      rw [hdecomp]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hL1)
        (Subgroup.mem_sup_right hR1)
  -- the coordinate swap
  set swapM : Multiplicative (F × F) ≃* Multiplicative (F × F) :=
    AddEquiv.toMultiplicative (AddEquiv.prodComm (M := F) (N := F))
    with hswapdef
  set σ : (TypeBModel phi epsilon ⧸
        Subgroup.center (TypeBModel phi epsilon)) ≃*
      (TypeBModel phi epsilon ⧸
        Subgroup.center (TypeBModel phi epsilon)) :=
    (χ.trans swapM).trans χ.symm with hσdef
  have hχσ : ∀ y, χ (σ y) = swapM (χ y) := fun y => χ.apply_symm_apply _
  have hswapAdd : ∀ z : Multiplicative (F × F),
      (swapM z).toAdd = (z.toAdd.2, z.toAdd.1) := fun _ => rfl
  have hσLR : ∀ y, σ y ∈ R ↔ y ∈ L := fun y => by
    rw [hmemR, hmemL, hχσ, hswapAdd]
  have hmapσ : L.map σ.toMonoidHom = R := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (hσLR l).mpr hl
    · intro hy
      refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
      refine (hσLR (σ.symm y)).mp ?_
      rw [σ.apply_symm_apply]
      exact hy
  -- equivariance of the swap
  have hactval : ∀ (k : ↥(diagonalAuts phi epsilon)) y,
      σ ((IsAInvariant.quotientMulAutHom (IsAInvariant.of_characteristic
        (diagonalAuts phi epsilon).subtype) k) y) =
      (IsAInvariant.quotientMulAutHom (IsAInvariant.of_characteristic
        (diagonalAuts phi epsilon).subtype) k) (σ y) := by
    intro k y
    obtain ⟨x, hx⟩ := k.2
    apply χ.injective
    apply Multiplicative.toAdd.injective
    have hL' := quotient_action_eq phi epsilon hε k hx y
    have hR' := quotient_action_eq phi epsilon hε k hx (σ y)
    rw [hχσ, hswapAdd, hL', hR', hχσ, hswapAdd]
  exact ⟨⟨⟨hEA, L, R, hLinv, hRinv,
    hLcard.trans hZcard.symm, hRcard.trans hZcard.symm, hcompl⟩,
    ⟨(MulEquiv.subgroupMap σ L).trans (MulEquiv.subgroupCongr hmapσ),
      fun k s => Subtype.ext (hactval k s.val)⟩⟩⟩

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
