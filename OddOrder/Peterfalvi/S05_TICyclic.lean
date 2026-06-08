/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S03_PreliminaryCharacter
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter

/-!
# Peterfalvi §5: TI-Subsets with Cyclic Normalizers

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5, pp. 15-20.

This file starts the formal interface for the TI-cyclic normalizer setup in
Peterfalvi (3.1).  The key point of the current slice is that this setup gives
a canonical TI-specialized instance of the §4 Dade hypothesis, and then reuses
the §4 Dade-isometry packages for the maps used in (3.2)-(3.5).

Reference note: `notes/peterfalvi/s05_ti_cyclic_normalizer.md`.
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

/- 3: TI-subsets with cyclic normalizers (pp. 15-20) -/

/-- The ambient data in Peterfalvi (3.1).

`V` is kept as a field instead of being defined from `W`, `W1`, and `W2` so that
later sections can use the same interface for the slightly varied normalizer
setups that occur in §6 and §8. -/
structure TICyclicHypothesis (G : Type*) [Group G] [Fintype G] where
  W : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W1_le_W : W1 ≤ W
  W2_le_W : W2 ≤ W
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  W_sup : W1 ⊔ W2 = W
  W_disjoint : Disjoint W1 W2
  W_card_coprime : Nat.Coprime (Nat.card W1) (Nat.card W2)
  W_card_odd : Odd (Nat.card W)
  /-- (3.1): `W = W₁ × W₂` is cyclic.  Cyclicity is part of Peterfalvi's Hypothesis (3.1)
  ("`W` is cyclic of odd order"); it makes `W` abelian, so `Irr(W)` consists of linear
  characters (used to build the `ω_{ij}` family in (3.3)).  It also forces `W₁` and `W₂`
  to be cyclic and `W = W₁ × W₂` to be an internal direct product. -/
  W_cyclic : IsCyclic W
  V : Set G
  V_subset_sharp : V ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G)
  V_subset_W : V ⊆ W
  W_normalizes_V :
    ∀ (w : W) ⦃v : G⦄, v ∈ V → (w : G) * v * (w : G)⁻¹ ∈ V
  V_ti : OddOrder.GroupTheory.IsTISubset V W

namespace TICyclicHypothesis

/-- Peterfalvi (3.1), viewed as the `H(a)=1` specialization of §4 Hypothesis
(2.2). -/
def toDadeHypothesis (hyp : TICyclicHypothesis G) :
    OddOrder.Peterfalvi.S04.Hypothesis G hyp.V hyp.W :=
  OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
    hyp.V_subset_sharp hyp.V_subset_W hyp.W_normalizes_V hyp.V_ti

@[simp] theorem toDadeHypothesis_H (hyp : TICyclicHypothesis G)
    (a : {a : G // a ∈ hyp.V}) :
    (hyp.toDadeHypothesis).H a = ⊥ :=
  rfl

theorem toDadeHypothesis_isTISubset (hyp : TICyclicHypothesis G) :
    OddOrder.GroupTheory.IsTISubset hyp.V hyp.W :=
  (hyp.toDadeHypothesis).isTISubset_of_forall_H_eq_bot
    (fun a => hyp.toDadeHypothesis_H a)

/-- The supported class-function space `CF(W,V)` used by (3.2)-(3.5). -/
abbrev SupportedOnV (k : Type*) [CommRing k] (hyp : TICyclicHypothesis G) :=
  OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) k hyp.V hyp.W

variable {k : Type*} [CommRing k] [StarRing k]
variable [Invertible (Nat.card G : k)]

/-- A §5 application package: a TI-cyclic setup together with a Dade map for
the induced §4 `H(a)=1` hypothesis. -/
structure DadeApplication (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)] where
  tau : OddOrder.Peterfalvi.S04.DadeIsometryData
    (G := G) (k := k) hyp.toDadeHypothesis

instance (hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)] :
    CoeFun (DadeApplication (G := G) (k := k) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) k hyp.V hyp.W) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem coe_mk (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)]
    (tau : OddOrder.Peterfalvi.S04.DadeIsometryData
      (G := G) (k := k) hyp.toDadeHypothesis) :
    ((DadeApplication.mk tau : DadeApplication (G := G) (k := k) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) k hyp.V hyp.W) = tau.toDadeMap :=
  rfl

theorem map_eq_of_mem_V {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)]
    (app : DadeApplication (G := G) (k := k) hyp)
    (α : SupportedOnV (G := G) k hyp) {v : G} (hv : v ∈ hyp.V) :
    app.tau.toDadeMap α v =
      (α : ClassFunction hyp.W k) ⟨v, hyp.V_subset_W hv⟩ := by
  exact OddOrder.Peterfalvi.S04.map_eq_of_mem_A_of_forall_H_eq_bot
    app.tau.isDadeMap (fun a => hyp.toDadeHypothesis_H a) α hv

theorem map_eq_zero_of_not_mem_conjugatesOfSet_V {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)]
    (app : DadeApplication (G := G) (k := k) hyp)
    (α : SupportedOnV (G := G) k hyp) {g : G}
    (hg : g ∉ Group.conjugatesOfSet hyp.V) :
    app.tau.toDadeMap α g = 0 :=
  OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
    app.tau.isDadeMap (fun a => hyp.toDadeHypothesis_H a) α hg

variable [Invertible (Nat.card G : ℂ)]

/-- A complex §5 application package including the virtual-character part of
the §4 Dade isometry theorem. -/
structure FullDadeApplication (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] where
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData
    (G := G) hyp.toDadeHypothesis

instance (hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] :
    CoeFun (FullDadeApplication (G := G) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ hyp.V hyp.W) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem full_coe_mk (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData
      (G := G) hyp.toDadeHypothesis) :
    ((FullDadeApplication.mk tau : FullDadeApplication (G := G) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ hyp.V hyp.W) = tau.toDadeMap :=
  rfl

theorem full_map_eq_of_mem_V {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV (G := G) ℂ hyp) {v : G} (hv : v ∈ hyp.V) :
    app.tau.toDadeMap α v =
      (α : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ := by
  exact OddOrder.Peterfalvi.S04.map_eq_of_mem_A_of_forall_H_eq_bot
    app.tau.toDadeIsometryData.isDadeMap
    (fun a => hyp.toDadeHypothesis_H a) α hv

theorem full_map_eq_zero_of_not_mem_conjugatesOfSet_V {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV (G := G) ℂ hyp) {g : G}
    (hg : g ∉ Group.conjugatesOfSet hyp.V) :
    app.tau.toDadeMap α g = 0 :=
  OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
    app.tau.toDadeIsometryData.isDadeMap
    (fun a => hyp.toDadeHypothesis_H a) α hg

theorem full_inner_eq {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α β : SupportedOnV (G := G) ℂ hyp) :
    ClassFunction.inner (app.tau.toDadeMap α) (app.tau.toDadeMap β) =
      ClassFunction.inner (α : ClassFunction hyp.W ℂ) (β : ClassFunction hyp.W ℂ) :=
  app.tau.inner_eq α β

theorem full_maps_virtualCharacter {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV (G := G) ℂ hyp)
    (hα : (α : ClassFunction hyp.W ℂ) ∈ ZIrr hyp.W) :
    app.tau.toDadeMap α ∈ ZIrr G :=
  app.tau.maps_virtualCharacter α hα

end TICyclicHypothesis

namespace TICyclicHypothesis

/- 3.3: The linear-character family `ω` of the cyclic group `W` (pp. 16-17) -/

/-- **Peterfalvi (3.1)/(3.3)**: `W` is commutative.  It is cyclic by `W_cyclic`, and a cyclic
group is abelian (`commutative_of_cyclic_center_quotient` applied to the identity map).  This is
what makes every irreducible character of `W` linear, so that the `ω_{ij}` of (3.3) exhaust
`Irr(W)` (`omegaEquiv`). -/
theorem isMulCommutative_W (hyp : TICyclicHypothesis G) : IsMulCommutative hyp.W :=
  haveI := hyp.W_cyclic
  ⟨⟨fun a b =>
    commutative_of_cyclic_center_quotient (MonoidHom.id hyp.W)
      (by
        intro x hx
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact Subgroup.one_mem _) a b⟩⟩

/-- **Peterfalvi (3.3)**: the irreducible character `ω(χ)` of `W` attached to a linear character
`χ : W →* ℂˣ`.  Since `W` is abelian, every irreducible character of `W` is of this form
(`omega_surjective`) and distinct linear characters give distinct irreducible characters
(`omega_injective`); the two facts are packaged as the bijection `omegaEquiv`.  In Peterfalvi's
notation these are the `ω_{ij}` (`0 ≤ i < w₁`, `0 ≤ j < w₂`). -/
noncomputable def omega (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    IrreducibleCharacter hyp.W :=
  linearIrreducibleCharacter χ

@[simp] theorem omega_apply (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) (w : hyp.W) :
    ((hyp.omega χ : ClassFunction hyp.W ℂ)) w = (χ w : ℂ) :=
  linearClassFunction_apply χ w

/-- (3.3): each `ω(χ)` has degree one. -/
@[simp] theorem omega_apply_one (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    ((hyp.omega χ : ClassFunction hyp.W ℂ)) 1 = 1 := by
  rw [omega_apply, map_one, Units.val_one]

theorem omega_injective (hyp : TICyclicHypothesis G) :
    Function.Injective hyp.omega :=
  linearIrreducibleCharacter_injective

theorem omega_surjective (hyp : TICyclicHypothesis G) :
    Function.Surjective hyp.omega := by
  haveI := hyp.isMulCommutative_W
  intro χ
  obtain ⟨h, hh⟩ := χ.2.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  exact ⟨h, Subtype.ext hh⟩

/-- **Peterfalvi (3.3)**: `Irr(W) = {ω_{ij}}`, packaged as the bijection `Hom(W, ℂˣ) ≃ Irr(W)`.
Every irreducible character of the cyclic group `W` is the linear character `ω(χ)` of a unique
`χ : W →* ℂˣ`. -/
noncomputable def omegaEquiv (hyp : TICyclicHypothesis G) :
    (hyp.W →* ℂˣ) ≃ IrreducibleCharacter hyp.W :=
  Equiv.ofBijective hyp.omega ⟨hyp.omega_injective, hyp.omega_surjective⟩

@[simp] theorem omegaEquiv_apply (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    hyp.omegaEquiv χ = hyp.omega χ :=
  rfl

/- 3.3 (cont.): `W = W₁ × W₂` as an internal direct product, used to split `ω_{ij} = ω_{i0}·ω_{0j}` -/

/-- `W₁` and `W₂`, viewed inside `↥W`, intersect trivially (from `W_disjoint`). -/
theorem W1_subgroupOf_inf_W2_subgroupOf_eq_bot (hyp : TICyclicHypothesis G) :
    hyp.W1.subgroupOf hyp.W ⊓ hyp.W2.subgroupOf hyp.W = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
  have hxbot : (x : G) ∈ hyp.W1 ⊓ hyp.W2 := hx
  rw [disjoint_iff.mp hyp.W_disjoint, Subgroup.mem_bot] at hxbot
  rw [Subgroup.mem_bot]
  exact Subtype.ext hxbot

/-- `W₁` and `W₂`, viewed inside `↥W`, generate `↥W` (from `W_sup`). -/
theorem W1_subgroupOf_sup_W2_subgroupOf_eq_top (hyp : TICyclicHypothesis G) :
    hyp.W1.subgroupOf hyp.W ⊔ hyp.W2.subgroupOf hyp.W = ⊤ := by
  rw [← Subgroup.subgroupOf_sup hyp.W1_le_W hyp.W2_le_W, hyp.W_sup, Subgroup.subgroupOf_self]

section
open scoped IsMulCommutative

/-- **Peterfalvi (3.1)/(3.3)**: `W = W₁ × W₂` is an internal direct product — the multiplication
map `↥W₁ × ↥W₂ → ↥W` is a group isomorphism (`W` is abelian, `W₁ ⊓ W₂ = 1`, `W₁ ⊔ W₂ = W`).
This is what lets a linear character `ω` of `W` split as `ω_{i0}·ω_{0j}` with `ω_{i0}` trivial on
`W₂` and `ω_{0j}` trivial on `W₁`. -/
noncomputable def wProdEquiv (hyp : TICyclicHypothesis G) :
    (hyp.W1.subgroupOf hyp.W) × (hyp.W2.subgroupOf hyp.W) ≃* hyp.W :=
  haveI := hyp.isMulCommutative_W
  MulEquiv.ofBijective
    (MonoidHom.coprod (hyp.W1.subgroupOf hyp.W).subtype (hyp.W2.subgroupOf hyp.W).subtype) <| by
    constructor
    · rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ hab
      rw [MonoidHom.coprod_apply, Subgroup.coe_subtype, Subgroup.coe_subtype] at hab
      have hain : (a : hyp.W) ∈ hyp.W1.subgroupOf hyp.W ⊓ hyp.W2.subgroupOf hyp.W := by
        refine ⟨a.2, ?_⟩
        have hinv : (a : hyp.W) = ((b : hyp.W))⁻¹ := mul_eq_one_iff_eq_inv.mp hab
        rw [hinv]
        exact (hyp.W2.subgroupOf hyp.W).inv_mem b.2
      rw [hyp.W1_subgroupOf_inf_W2_subgroupOf_eq_bot, Subgroup.mem_bot] at hain
      have hb1 : (b : hyp.W) = 1 := by rw [hain, one_mul] at hab; exact hab
      exact Prod.ext (Subtype.ext hain) (Subtype.ext hb1)
    · intro w
      have hw : w ∈ hyp.W1.subgroupOf hyp.W ⊔ hyp.W2.subgroupOf hyp.W := by
        rw [hyp.W1_subgroupOf_sup_W2_subgroupOf_eq_top]; exact Subgroup.mem_top w
      rw [Subgroup.mem_sup] at hw
      obtain ⟨x, hx, y, hy, hxy⟩ := hw
      refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
      rw [MonoidHom.coprod_apply, Subgroup.coe_subtype, Subgroup.coe_subtype]
      exact hxy

@[simp] theorem wProdEquiv_apply (hyp : TICyclicHypothesis G)
    (p : (hyp.W1.subgroupOf hyp.W) × (hyp.W2.subgroupOf hyp.W)) :
    (hyp.wProdEquiv p : hyp.W) = (p.1 : hyp.W) * (p.2 : hyp.W) := by
  haveI := hyp.isMulCommutative_W
  rfl

end

/-- Projection `↥W →* ↥W` onto the `W₁`-component (image in `W₁`, kills the `W₂`-component),
through the internal-product iso `wProdEquiv`. -/
noncomputable def wProj1 (hyp : TICyclicHypothesis G) : hyp.W →* hyp.W :=
  (hyp.W1.subgroupOf hyp.W).subtype.comp
    ((MonoidHom.fst _ _).comp hyp.wProdEquiv.symm.toMonoidHom)

/-- Projection `↥W →* ↥W` onto the `W₂`-component. -/
noncomputable def wProj2 (hyp : TICyclicHypothesis G) : hyp.W →* hyp.W :=
  (hyp.W2.subgroupOf hyp.W).subtype.comp
    ((MonoidHom.snd _ _).comp hyp.wProdEquiv.symm.toMonoidHom)

@[simp] theorem wProj1_apply (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wProj1 w = ((hyp.wProdEquiv.symm w).1 : hyp.W) := rfl

@[simp] theorem wProj2_apply (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wProj2 w = ((hyp.wProdEquiv.symm w).2 : hyp.W) := rfl

/-- Reconstruction from the internal direct product: `w = (W₁-part of w) · (W₂-part of w)`. -/
theorem wProj1_mul_wProj2 (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wProj1 w * hyp.wProj2 w = w := by
  rw [wProj1_apply, wProj2_apply, ← hyp.wProdEquiv_apply, MulEquiv.apply_symm_apply]

/-- **Peterfalvi (3.3)**: every linear character of `W` factors as its `W₂`-trivial part
(`χ ∘ wProj1`, an `ω_{i0}`) times its `W₁`-trivial part (`χ ∘ wProj2`, an `ω_{0j}`).  This is the
`ω_{ij} = ω_{i0}·ω_{0j}` decomposition at the level of `Hom(W, ℂˣ)`. -/
theorem char_eq_wProj_comp_mul (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    χ = (χ.comp hyp.wProj1) * (χ.comp hyp.wProj2) := by
  ext w
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul,
    hyp.wProj1_mul_wProj2]

/-- The `W₁`-projection kills `W₂`: this is why `χ ∘ wProj1` (the `ω_{i0}` factor) has `W₂` in
its kernel. -/
theorem wProj1_eq_one_of_mem_W2 (hyp : TICyclicHypothesis G) {w : hyp.W}
    (hw : w ∈ hyp.W2.subgroupOf hyp.W) : hyp.wProj1 w = 1 := by
  have hsymm : hyp.wProdEquiv.symm w = (1, ⟨w, hw⟩) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  rw [wProj1_apply, hsymm]
  simp

/-- The `W₂`-projection kills `W₁`: this is why `χ ∘ wProj2` (the `ω_{0j}` factor) has `W₁` in
its kernel. -/
theorem wProj2_eq_one_of_mem_W1 (hyp : TICyclicHypothesis G) {w : hyp.W}
    (hw : w ∈ hyp.W1.subgroupOf hyp.W) : hyp.wProj2 w = 1 := by
  have hsymm : hyp.wProdEquiv.symm w = (⟨w, hw⟩, 1) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  rw [wProj2_apply, hsymm]
  simp

/-- **Peterfalvi (3.3)**: the `ω_{i0}` factor `χ ∘ wProj1` of a linear character has `W₂` in its
kernel (it is one of the irreducible characters of `W` trivial on `W₂`). -/
theorem W2_subgroupOf_le_ker_comp_wProj1 (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    hyp.W2.subgroupOf hyp.W ≤ (χ.comp hyp.wProj1).ker := by
  intro w hw
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hyp.wProj1_eq_one_of_mem_W2 hw, map_one]

/-- **Peterfalvi (3.3)**: the `ω_{0j}` factor `χ ∘ wProj2` has `W₁` in its kernel. -/
theorem W1_subgroupOf_le_ker_comp_wProj2 (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    hyp.W1.subgroupOf hyp.W ≤ (χ.comp hyp.wProj2).ker := by
  intro w hw
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hyp.wProj2_eq_one_of_mem_W1 hw, map_one]

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
