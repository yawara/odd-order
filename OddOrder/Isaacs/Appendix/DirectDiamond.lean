/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Group

/-!
# Isaacs, *Finite Group Theory*, Appendix — products of two subgroups

This file formalizes two elementary results from the appendix ("The Basics") of
I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), used implicitly throughout the book.

## Main results

* **Lemma X.1** (`Subgroup.coe_sup_eq_mul_iff_mul_comm`): for subgroups `H`, `K` of a group
  `G`, the set product `HK` is a subgroup **iff** `HK = KH`. Here "`HK` is a subgroup" is
  encoded as `↑(H ⊔ K) = ↑H * ↑K`: the carrier of the join equals the pointwise set product
  (equivalently, `↑H * ↑K` is closed, i.e. is the carrier of a subgroup).

* **Corollary X.4** (`Subgroup.directDiamond_bijOn`), the *direct diamond* correspondence:
  if `HK` is a subgroup and `D = H ⊓ K`, then intersection with `K` is a bijection from the
  interval `𝒳 = [H, H ⊔ K]` of subgroups onto
  `𝒲 = {W | D ≤ W ≤ K ∧ WH = HW}` (the members of `𝒴 = [D, K]` that permute with `H`,
  equivalently, by Lemma X.1, those `W` for which `WH` is a subgroup). Injectivity and the
  image description are also exposed separately as `Subgroup.directDiamond_injOn` and
  `Subgroup.directDiamond_image`.

Isaacs' Lemma X.3 (Dedekind's modular law) `HK ∩ U = H(K ∩ U)` for `H ≤ U` is mathlib's
`Subgroup.mul_inf_assoc`. Note that the *lattice* modular law fails for the subgroup lattice
of a general (nonabelian) group — mathlib's `IsModularLattice (Subgroup G)` requires `G`
commutative — so, exactly as in Isaacs, the argument is carried out with pointwise set
products (`Subgroup.mul_inf_assoc`) rather than with `sup_inf_assoc_of_le`.

See `issues/3018-isaacs-appendix-x-gaps.md`.
-/

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

/-- **Isaacs, Finite Group Theory, Lemma X.1.**
For subgroups `H`, `K` of a group `G`, the set product `HK` is a subgroup if and only if
`HK = KH`. Here "`HK` is a subgroup" is encoded as `↑(H ⊔ K) = ↑H * ↑K`: the carrier of the
join equals the pointwise product (equivalently `↑H * ↑K` is closed, hence a subgroup). -/
theorem coe_sup_eq_mul_iff_mul_comm (H K : Subgroup G) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) ↔
      (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G) := by
  constructor
  · -- If `↑H * ↑K` is a subgroup carrier `S`, then `S⁻¹ = S`, and `(↑H * ↑K)⁻¹ = ↑K * ↑H`.
    intro h
    have e1 : ((H : Set G) * (K : Set G))⁻¹ = (K : Set G) * (H : Set G) := by
      rw [mul_inv_rev, inv_coe_set, inv_coe_set]
    calc (H : Set G) * (K : Set G)
        = ((H ⊔ K : Subgroup G) : Set G) := h.symm
      _ = ((H ⊔ K : Subgroup G) : Set G)⁻¹ := (inv_coe_set (H := (H ⊔ K : Subgroup G))).symm
      _ = ((H : Set G) * (K : Set G))⁻¹ := by rw [h]
      _ = (K : Set G) * (H : Set G) := e1
  · -- Conversely, if `HK = KH`, then `↑H * ↑K` is closed; build it as a subgroup `= H ⊔ K`.
    intro hcomm
    let HK : Subgroup G :=
      { carrier := (H : Set G) * (K : Set G)
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
          have hbc : b * c ∈ (K : Set G) * (H : Set G) := ⟨b, hb, c, hc, rfl⟩
          rw [← hcomm] at hbc
          obtain ⟨e, he, f, hf, hef⟩ := hbc
          refine ⟨a * e, H.mul_mem ha he, f * d, K.mul_mem hf hd, ?_⟩
          have eq1 : a * e * (f * d) = a * (e * f) * d := by group
          have eq2 : a * (e * f) * d = a * (b * c) * d := congrArg (fun x => a * x * d) hef
          have eq3 : a * (b * c) * d = a * b * (c * d) := by group
          exact eq1.trans (eq2.trans eq3)
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * (H : Set G) :=
            ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
          rw [← hcomm] at hba
          rw [mul_inv_rev]
          exact hba }
    have hHK_eq : HK = H ⊔ K := by
      apply le_antisymm
      · intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
      · refine sup_le ?_ ?_
        · intro a ha; exact ⟨a, ha, 1, K.one_mem, mul_one a⟩
        · intro b hb; exact ⟨1, H.one_mem, b, hb, one_mul b⟩
    have h1 : ((HK : Subgroup G) : Set G) = (H : Set G) * (K : Set G) := rfl
    have h2 : ((H ⊔ K : Subgroup G) : Set G) = ((HK : Subgroup G) : Set G) :=
      congrArg (fun P : Subgroup G => (P : Set G)) hHK_eq.symm
    exact h2.trans h1

/-- **Isaacs, Finite Group Theory, Corollary X.4** (direct diamond correspondence).
Let `H`, `K` be subgroups of `G` with `HK` a subgroup (encoded as `↑(H ⊔ K) = ↑H * ↑K`), and
let `D = H ⊓ K`. Intersection with `K` is a bijection from the interval `𝒳 = [H, H ⊔ K]` of
subgroups onto `𝒲 = {W | D ≤ W ≤ K ∧ WH = HW}`: the subgroups `W` between `D` and `K` that
permute with `H` (equivalently, by Lemma X.1, those `W` for which `WH` is a subgroup). -/
theorem directDiamond_bijOn {H K : Subgroup G}
    (hHK : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G)) :
    Set.BijOn (· ⊓ K) (Set.Icc H (H ⊔ K))
      {W | H ⊓ K ≤ W ∧ W ≤ K ∧ (W : Set G) * (H : Set G) = (H : Set G) * (W : Set G)} := by
  -- Dedekind (set form, Isaacs X.3): for `H ≤ X ≤ H ⊔ K`, one has `↑X = ↑H * ↑(X ⊓ K)`.
  have hXeq : ∀ X : Subgroup G, H ≤ X → X ≤ H ⊔ K →
      (X : Set G) = (H : Set G) * ((X ⊓ K : Subgroup G) : Set G) := by
    intro X hHX hXHK
    have hd := mul_inf_assoc H K X hHX
    rw [inf_comm K X, ← hHK,
      Set.inter_eq_right.mpr (SetLike.coe_subset_coe.mpr hXHK)] at hd
    exact hd.symm
  -- Consequently `H ⊔ (X ⊓ K) = X` as subgroups, purely from the set identity above.
  have hXsup : ∀ X : Subgroup G, H ≤ X → X ≤ H ⊔ K → H ⊔ (X ⊓ K) = X := by
    intro X hHX hXHK
    refine le_antisymm (sup_le hHX inf_le_left) ?_
    intro x hx
    have hx' : x ∈ (H : Set G) * ((X ⊓ K : Subgroup G) : Set G) := by
      rw [← hXeq X hHX hXHK]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  refine ⟨?_, ?_, ?_⟩
  · -- `MapsTo`: `θ(X) = X ⊓ K` lands in `𝒲`.
    intro X hX
    obtain ⟨hHX, hXHK⟩ := Set.mem_Icc.mp hX
    refine ⟨inf_le_inf hHX le_rfl, inf_le_right, ?_⟩
    have hsupset : ((H ⊔ (X ⊓ K) : Subgroup G) : Set G)
        = (H : Set G) * ((X ⊓ K : Subgroup G) : Set G) := by
      rw [hXsup X hHX hXHK]; exact hXeq X hHX hXHK
    exact ((coe_sup_eq_mul_iff_mul_comm H (X ⊓ K)).mp hsupset).symm
  · -- `InjOn`: `X = ↑H * ↑(X ⊓ K)` recovers `X` from `θ(X) = X ⊓ K`.
    intro X hX Y hY hθ
    obtain ⟨hHX, hXHK⟩ := Set.mem_Icc.mp hX
    obtain ⟨hHY, hYHK⟩ := Set.mem_Icc.mp hY
    have hθ' : X ⊓ K = Y ⊓ K := hθ
    apply SetLike.coe_injective
    rw [hXeq X hHX hXHK, hXeq Y hHY hYHK, hθ']
  · -- `SurjOn`: every `W ∈ 𝒲` is `θ(W ⊔ H)` (using Lemma X.1 to know `↑(W ⊔ H) = ↑W * ↑H`).
    intro W hW
    obtain ⟨hDW, hWK, hperm⟩ := hW
    have hWHsub : ((W ⊔ H : Subgroup G) : Set G) = (W : Set G) * (H : Set G) :=
      (coe_sup_eq_mul_iff_mul_comm W H).mpr hperm
    have hWD : (W : Set G) * ((H ⊓ K : Subgroup G) : Set G) = (W : Set G) :=
      Set.Subset.antisymm
        (by rintro _ ⟨a, ha, b, hb, rfl⟩; exact W.mul_mem ha (hDW hb))
        (fun w hw => ⟨w, hw, 1, (H ⊓ K).one_mem, mul_one w⟩)
    have hpre : (W ⊔ H) ⊓ K = W := by
      apply SetLike.coe_injective
      rw [Subgroup.coe_inf, hWHsub, ← mul_inf_assoc W H K hWK]
      exact hWD
    exact ⟨W ⊔ H,
      Set.mem_Icc.mpr ⟨le_sup_right, sup_le (hWK.trans le_sup_right) le_sup_left⟩, hpre⟩

/-- **Isaacs, Finite Group Theory, Corollary X.4**, injectivity part: intersection with `K`
is injective on the interval `𝒳 = [H, H ⊔ K]`. -/
theorem directDiamond_injOn {H K : Subgroup G}
    (hHK : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G)) :
    Set.InjOn (· ⊓ K) (Set.Icc H (H ⊔ K)) :=
  (directDiamond_bijOn hHK).injOn

/-- **Isaacs, Finite Group Theory, Corollary X.4**, image part: the image of the interval
`𝒳 = [H, H ⊔ K]` under intersection with `K` is exactly `𝒲`. -/
theorem directDiamond_image {H K : Subgroup G}
    (hHK : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G)) :
    (· ⊓ K) '' Set.Icc H (H ⊔ K)
      = {W | H ⊓ K ≤ W ∧ W ≤ K ∧ (W : Set G) * (H : Set G) = (H : Set G) * (W : Set G)} :=
  (directDiamond_bijOn hHK).image_eq

end Subgroup
