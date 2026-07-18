/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerNormalizer
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Peterfalvi Part II, Ch. I §3: conjugacy inside `V`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, p. 107.

Lemma 2 says that arbitrary subsets `X, Y ⊆ V` which are conjugate in `G`
are already conjugate by an element of `V`.  The proof first corrects an
ambient conjugator into `D` using double transitivity of `C_G(Y)`, then
applies the canonical projection `D = K ⋊ V → V`.

Peterfalvi uses right actions.  With Lean's left-action convention the
centralizing correction is multiplied on the left.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction

section /- §3, Lemma 2 (p. 107) -/

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **Peterfalvi Part II, Ch. I §3, Lemma 2.**  The subgroups `K` and `V`
are complementary inside `D`.  This is the internal semidirect-product
decomposition underlying the source's canonical homomorphism `D → V`. -/
theorem K_isComplement_V :
    (hyp.K.subgroupOf hyp.D).IsComplement' (hyp.V.subgroupOf hyp.D) := by
  refine Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    hyp.V_le_D hyp.K_le_D hyp.V_inf_K_eq_bot ?_
  intro d hdD
  obtain ⟨⟨⟨v, hv⟩, ⟨k, hk⟩⟩, hvk⟩ :=
    (invertedProdEquiv (X := hyp.D) (t := hyp.t)
      hyp.t_mul_t hyp.D_odd (fun _ hx => hyp.t_conj_mem_D' hx)).surjective
      ⟨d⁻¹, inv_mem hdD⟩
  have hvV : v ∈ hyp.V := hv
  have hkK : k ∈ hyp.K := by
    change k ∈ (hyp.K : Set G)
    rw [hyp.coe_K]
    exact hk
  refine ⟨k⁻¹, hyp.K.inv_mem hkK, v⁻¹, hyp.V.inv_mem hvV, ?_⟩
  have hvkG : v * k = d⁻¹ := congrArg Subtype.val hvk
  have h := congrArg Inv.inv hvkG
  simpa [mul_inv_rev] using h

/-- The canonical homomorphism `D = K ⋊ V → V` used in the final sentence
of Peterfalvi §3 Lemma 2. -/
noncomputable def dToV : ↥hyp.D →* ↥hyp.V :=
  (Subgroup.subgroupOfEquivOfLe hyp.V_le_D).toMonoidHom.comp
    (SemidirectProduct.rightHom.comp
      (SemidirectProduct.mulEquivSubgroup hyp.K_isComplement_V).symm.toMonoidHom)

/-- The canonical projection `D → V` is the identity on its complementary
subgroup `V`. -/
@[simp] theorem dToV_of_mem_V {v : G} (hv : v ∈ hyp.V) :
    hyp.dToV ⟨v, hyp.V_le_D hv⟩ = ⟨v, hv⟩ := by
  let vd : ↥hyp.D := ⟨v, hyp.V_le_D hv⟩
  let vv : ↥(hyp.V.subgroupOf hyp.D) := ⟨vd, hv⟩
  let e := SemidirectProduct.mulEquivSubgroup hyp.K_isComplement_V
  have he : e.symm vd = SemidirectProduct.inr vv := by
    rw [e.symm_apply_eq]
    simp [e, vd, vv]
  change (Subgroup.subgroupOfEquivOfLe hyp.V_le_D)
    (SemidirectProduct.right (e.symm vd)) = ⟨v, hv⟩
  rw [he]
  rfl

/-- **Peterfalvi Part II, Ch. I §3, Lemma 2**, first step.  An ambient
conjugator between subsets of `V` can be corrected into the two-point
stabilizer `D` by double transitivity of the centralizer of the target.

The source writes the corrected element on the right.  Under Lean's left
action convention it is `h * g`, where `h` centralizes the target. -/
theorem exists_mem_D_conj_image_eq
    {X Y : Set G} (hXV : X ⊆ hyp.V) (hYV : Y ⊆ hyp.V)
    {g : G} (hXY : (MulAut.conj g).toMonoidHom '' X = Y) :
    ∃ d ∈ hyp.D, (MulAut.conj d).toMonoidHom '' X = Y := by
  let Xc : Subgroup G := Subgroup.closure X
  let Yc : Subgroup G := Subgroup.closure Y
  have hXcV : Xc ≤ hyp.V := (Subgroup.closure_le hyp.V).mpr hXV
  have hYcV : Yc ≤ hyp.V := (Subgroup.closure_le hyp.V).mpr hYV
  have hXcD : Xc ≤ hyp.D := hXcV.trans hyp.V_le_D
  have hYcD : Yc ≤ hyp.D := hYcV.trans hyp.V_le_D
  have hmap : Xc.map (MulAut.conj g).toMonoidHom = Yc := by
    change (Subgroup.closure X).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure Y
    rw [MonoidHom.map_closure, hXY]
  have hgb : g • hyp.basept ∈ fixedPoints Yc Ω := by
    rw [Hypothesis.mem_fixedPoints_iff_forall]
    intro y hy
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxb : x • hyp.basept = hyp.basept :=
      Hypothesis.mem_fixedPoints_iff_forall.mp
        (hyp.basept_mem_fixedPoints hXcD) x hx
    change (g * x * g⁻¹) • (g • hyp.basept) = g • hyp.basept
    calc
      (g * x * g⁻¹) • (g • hyp.basept) = g • (x • hyp.basept) := by
        simp only [smul_smul]
        congr 1
        group
      _ = g • hyp.basept := by rw [hxb]
  have hgt : g • (hyp.t • hyp.basept) ∈ fixedPoints Yc Ω := by
    rw [Hypothesis.mem_fixedPoints_iff_forall]
    intro y hy
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxt : x • (hyp.t • hyp.basept) = hyp.t • hyp.basept :=
      Hypothesis.mem_fixedPoints_iff_forall.mp
        (hyp.t_smul_basept_mem_fixedPoints hXcD) x hx
    change (g * x * g⁻¹) • (g • (hyp.t • hyp.basept)) =
      g • (hyp.t • hyp.basept)
    calc
      (g * x * g⁻¹) • (g • (hyp.t • hyp.basept)) =
          g • (x • (hyp.t • hyp.basept)) := by
        simp only [smul_smul]
        congr 1
        group
      _ = g • (hyp.t • hyp.basept) := by rw [hxt]
  have hb : hyp.basept ∈ fixedPoints Yc Ω :=
    hyp.basept_mem_fixedPoints hYcD
  have ht : hyp.t • hyp.basept ∈ fixedPoints Yc Ω :=
    hyp.t_smul_basept_mem_fixedPoints hYcD
  have hbt : hyp.basept ≠ hyp.t • hyp.basept :=
    (hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H).symm
  have hgbt : g • hyp.basept ≠ g • (hyp.t • hyp.basept) := by
    intro heq
    exact hbt (smul_left_cancel g heq)
  have h3 : 3 ≤ (fixedPoints Yc Ω).ncard :=
    hyp.three_le_ncard_fixedPoints_of_le_V hYcV
  obtain ⟨h, hhC, hhgb, hhgt⟩ :=
    hyp.exists_mem_centralizer_smul_pair hYcD h3 hgb hgt hb ht hgbt hbt
  let d : G := h * g
  have hdD : d ∈ hyp.D := by
    rw [hyp.D_eq_stabilizer_inf, Subgroup.mem_inf]
    constructor
    · rw [mem_stabilizer_iff]
      simpa [d, mul_smul] using hhgb
    · rw [mem_stabilizer_iff]
      simpa [d, mul_smul] using hhgt
  refine ⟨d, hdD, ?_⟩
  have hpoint : ∀ x ∈ X,
      (MulAut.conj d).toMonoidHom x = (MulAut.conj g).toMonoidHom x := by
    intro x hx
    have hy : (MulAut.conj g).toMonoidHom x ∈ Y := by
      rw [← hXY]
      exact ⟨x, hx, rfl⟩
    have hyc : (MulAut.conj g).toMonoidHom x ∈ Yc :=
      Subgroup.subset_closure hy
    have hcomm := Subgroup.mem_centralizer_iff.mp hhC _ hyc
    change (g * x * g⁻¹) * h = h * (g * x * g⁻¹) at hcomm
    change (h * g) * x * (h * g)⁻¹ = g * x * g⁻¹
    calc
      (h * g) * x * (h * g)⁻¹ = h * (g * x * g⁻¹) * h⁻¹ := by group
      _ = g * x * g⁻¹ := by
        rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  calc
    (MulAut.conj d).toMonoidHom '' X =
        (MulAut.conj g).toMonoidHom '' X := Set.image_congr hpoint
    _ = Y := hXY


/-- **Peterfalvi Part II, Ch. I §3, Lemma 2.**  Subsets of `V` that are
conjugate in the ambient group are already conjugate by an element of `V`.

After correcting an ambient conjugator into `D`, the canonical homomorphism
`D → V` preserves its conjugation action on `V`. -/
theorem exists_mem_V_conj_image_eq
    {X Y : Set G} (hXV : X ⊆ hyp.V) (hYV : Y ⊆ hyp.V)
    (hconj : ∃ g : G, (MulAut.conj g).toMonoidHom '' X = Y) :
    ∃ v ∈ hyp.V, (MulAut.conj v).toMonoidHom '' X = Y := by
  obtain ⟨g, hXY⟩ := hconj
  obtain ⟨d, hdD, hdXY⟩ := hyp.exists_mem_D_conj_image_eq hXV hYV hXY
  let dD : ↥hyp.D := ⟨d, hdD⟩
  let vV : ↥hyp.V := hyp.dToV dD
  refine ⟨(vV : G), vV.2, ?_⟩
  calc
    (MulAut.conj (vV : G)).toMonoidHom '' X =
        (MulAut.conj d).toMonoidHom '' X := Set.image_congr (fun x hx => ?_)
    _ = Y := hdXY
  let xD : ↥hyp.D := ⟨x, hyp.V_le_D (hXV hx)⟩
  have hconjY : d * x * d⁻¹ ∈ Y := by
    rw [← hdXY]
    exact ⟨x, hx, rfl⟩
  have hconjV : d * x * d⁻¹ ∈ hyp.V := hYV hconjY
  have hproj :
      hyp.dToV (dD * xD * dD⁻¹) = ⟨d * x * d⁻¹, hconjV⟩ := by
    rw [show dD * xD * dD⁻¹ =
      (⟨d * x * d⁻¹, hyp.V_le_D hconjV⟩ : ↥hyp.D) by rfl]
    exact hyp.dToV_of_mem_V hconjV
  have hprojVal := congrArg Subtype.val hproj
  rw [map_mul, map_mul, map_inv, hyp.dToV_of_mem_V (hXV hx)] at hprojVal
  change (vV : G) * x * (vV : G)⁻¹ = d * x * d⁻¹
  simpa [vV, dD, xD] using hprojVal

end Hypothesis

end

end OddOrder.Peterfalvi.Appendices.Suzuki
