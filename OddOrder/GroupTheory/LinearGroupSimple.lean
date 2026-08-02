/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.Transvection
import OddOrder.GroupTheory.NonzeroVectorAction
import Mathlib.GroupTheory.GroupAction.Iwasawa

/-!
# `GL(V)` is simple over `𝔽₂` in dimension at least three

Iwasawa's criterion (`MulAction.IwasawaStructure`, mathlib) applied to the action of
`V ≃ₗ[K] V` on the non-zero vectors, with the transvection subgroups as the abelian family.
Over a two-element field:

* the action is `2`-transitive, hence preprimitive and quasiprimitive
  (`isPreprimitive_nonzeroVector`);
* the transvections with a fixed centre commute and are permuted by conjugation exactly as
  their centres are (`transvectionSubgroup_isMulCommutative`,
  `transvectionSubgroup_map_conj`);
* they generate (`iSup_transvectionSubgroup_eq_top`);
* and the group is perfect once `dim V ≥ 3` (`commutator_linearEquiv_eq_top`).

The dimension bound is needed only for perfectness: `⁅t_{v,h}, t_{w,g}⁆ = t_{w, −(g v)•h}`
realises `t_{w,h}` as a commutator provided one can pick `v ≠ 0, w` inside `ker h`, which
needs `dim ker h ≥ 2`.

## Main results

* `OddOrder.GroupTheory.commutator_linearEquiv_eq_top` — perfectness.
* `OddOrder.GroupTheory.linearEquivIwasawaStructure` — the Iwasawa structure.
* `OddOrder.GroupTheory.isSimpleGroup_linearEquiv` — **`GL(V)` is simple**.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

open MulAction Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- In a two-element field, `-1 = 1`. -/
theorem neg_one_eq_one_of_forall_eq_zero_or_one (hK : ∀ x : K, x = 0 ∨ x = 1) :
    (-1 : K) = 1 := by
  have h2 : (1 : K) + 1 = 0 := by
    rcases hK (1 + 1) with h | h
    · exact h
    · exfalso
      refine one_ne_zero (α := K) (add_right_cancel (b := (1 : K)) ?_)
      rw [h, zero_add]
  exact neg_eq_of_add_eq_zero_left h2

/-- **The linear group over `𝔽₂` is perfect in dimension at least three.**

Every transvection is a commutator: for `t_{w,h}` pick `v ≠ 0, w` in `ker h` and a
functional `g` with `g w = 0`, `g v = 1`; then `⁅t_{v,h}, t_{w,g}⁆ = t_{w, −(g v)•h}`,
which is `t_{w,h}` because `−1 = 1`.  Since the transvections generate, the commutator
subgroup is everything. -/
theorem commutator_linearEquiv_eq_top [FiniteDimensional K V]
    (hK : ∀ x : K, x = 0 ∨ x = 1) (h3 : 3 ≤ Module.finrank K V) :
    commutator (V ≃ₗ[K] V) = ⊤ := by
  classical
  rw [eq_top_iff, ← LinearMap.iSup_transvectionSubgroup_eq_top (K := K) (W := V) hK]
  refine iSup_le fun w => ?_
  rintro _ ⟨h, hhw, rfl⟩
  obtain ⟨v, hvker, hv0, hvw⟩ := exists_mem_ker_ne_zero_ne h hhw h3
  have hind : LinearIndependent K ![(w : V), v] :=
    linearIndependent_pair_of_ne_of_ne_zero K hK w.2 hv0 (Ne.symm hvw)
  obtain ⟨g, hgw, hgv⟩ := exists_dual_eq_zero_eq_one hind
  have hcomm := LinearMap.commutator_transvection (R := K) (v := v) (w := (w : V))
    (f := h) (g := g) hvker hhw hgw
  have hkey : LinearMap.transvection (w : V) h hhw
      = LinearMap.transvection v h hvker * LinearMap.transvection (w : V) g hgw *
        (LinearMap.transvection v h hvker)⁻¹ * (LinearMap.transvection (w : V) g hgw)⁻¹ := by
    rw [hcomm]
    ext x
    simp [hgv, neg_one_eq_one_of_forall_eq_zero_or_one hK]
  rw [hkey]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **The Iwasawa structure of the linear group on the non-zero vectors** — the
transvection subgroups, indexed by their centres. -/
def linearEquivIwasawaStructure [FiniteDimensional K V] (hK : ∀ x : K, x = 0 ∨ x = 1) :
    IwasawaStructure (V ≃ₗ[K] V) (NonzeroVector K V) where
  T w := LinearMap.transvectionSubgroup (R := K) (w : V)
  is_comm w := LinearMap.transvectionSubgroup_isMulCommutative (w : V)
  is_conj g w := by
    rw [Subgroup.pointwise_smul_def]
    exact LinearMap.transvectionSubgroup_map_conj g (w : V)
  is_generator := LinearMap.iSup_transvectionSubgroup_eq_top hK

/-- **🎯 `GL(V)` is simple** for a vector space of dimension at least `3` over a
two-element field (Iwasawa's criterion). -/
theorem isSimpleGroup_linearEquiv [FiniteDimensional K V]
    (hK : ∀ x : K, x = 0 ∨ x = 1) (h3 : 3 ≤ Module.finrank K V) :
    IsSimpleGroup (V ≃ₗ[K] V) := by
  classical
  haveI := isPreprimitive_nonzeroVector (V := V) K hK
  haveI : Nontrivial (V ≃ₗ[K] V) := by
    obtain ⟨w, v, hwv, hw0, hv0⟩ : ∃ w v : V, w ≠ v ∧ w ≠ 0 ∧ v ≠ 0 := by
      have hB := Module.finBasis K V
      refine ⟨hB ⟨0, by omega⟩, hB ⟨1, by omega⟩, ?_, hB.ne_zero _, hB.ne_zero _⟩
      exact fun hc => absurd (hB.injective hc) (by simp)
    have hind : LinearIndependent K ![w, v] :=
      linearIndependent_pair_of_ne_of_ne_zero K hK hw0 hv0 hwv
    obtain ⟨g, hgw, hgv⟩ := exists_dual_eq_zero_eq_one hind
    refine ⟨LinearMap.transvection w g hgw, 1, ?_⟩
    intro hc
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hc
    simp only [LinearMap.transvection_apply, hgv, one_smul] at this
    exact hw0 (by simpa using this)
  exact IwasawaStructure.isSimpleGroup (commutator_linearEquiv_eq_top hK h3)
    (linearEquivIwasawaStructure hK) inferInstance

end OddOrder.GroupTheory
