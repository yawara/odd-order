/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CoprimeAction
import OddOrder.GroupTheory.RepresentationTheory.ElementaryAbelianRepresentation
import OddOrder.GroupTheory.RepresentationTheory.WielandtCounting
import Mathlib.FieldTheory.Finiteness

/-!
# Peterfalvi (9.1): the elementary-abelian chief-factor bridge

For the chief-series assembly of Wielandt's fixed-point formula (Peterfalvi (9.1), assembled in
`OddOrder.GroupTheory.CoprimeFrobeniusAction.wielandt_fixedPoint_frobenius`), each
elementary-abelian chief factor `V` of the solvable group `H` is viewed as a `ZMod p`-linear
representation of `L = U ⋊ E` through an action `φ : L →* MulAut V`.  The module-level
elementary-abelian identity (⋆) `WielandtCounting.finrank_elab_identity` lives in *dimensions*,
while Wielandt's formula is a statement about *cardinalities* of fixed-point subgroups.

This file supplies the bridge (parametrised by an abstract `ZMod p`-module structure on
`Additive V`, which the caller produces from the elementary-abelian structure via
`IsElementaryAbelian.zmodModule`):

* `elabRepresentation φ` — the `ZMod p`-representation on `Additive V` (action via `φ`);
* `card_fixedSubgroup_eq_card_invariants` — the group fixed-point subgroup
  `C_V(X) = fixedSubgroup φ X` and the module invariants `V^X = invariants (ρ.comp X.subtype)`
  have the same cardinality (they are the same subset of `V = Additive V`, via `Additive.ofMul`);
* `card_fixedSubgroup_eq_pow_finrank` — hence `|C_V(X)| = p ^ dim V^X`.

`notes/peterfalvi/s11_wielandt_91_design.md` (lane-h pickup), issue 2014.
-/

namespace OddOrder.GroupTheory

open Module Representation

variable {L V : Type*} [Group L] [CommGroup V]

/-- The `ZMod p`-linear `L`-representation on `Additive V` attached to an action
`φ : L →* MulAut V` of `L` on `V`.  Built from `φ` via `MulDistribMulAction.compHom` and the
ambient `ZMod p`-module structure on `Additive V` (supplied by `IsElementaryAbelian.zmodModule`
for an elementary abelian `V`).  The action is `ρ l = φ l` (independent of the scalars). -/
noncomputable def elabRepresentation (p : ℕ) [Module (ZMod p) (Additive V)]
    (φ : L →* MulAut V) :
    Representation (ZMod p) L (Additive V) :=
  letI : MulDistribMulAction L V := MulDistribMulAction.compHom V φ
  Representation.ofDistribMulAction (ZMod p) L (Additive V)

theorem elabRepresentation_apply (p : ℕ) [Module (ZMod p) (Additive V)] (φ : L →* MulAut V)
    (l : L) (x : V) :
    elabRepresentation p φ l (Additive.ofMul x) = Additive.ofMul (φ l x) := rfl

/-- **The fixed-point bridge.**  The group fixed-point subgroup `C_V(X) = fixedSubgroup φ X` and
the module invariants `V^X = invariants (ρ.comp X.subtype)` of the elementary-abelian
representation have the same cardinality: they are the same subset of `V = Additive V`,
identified by `Additive.ofMul`. -/
theorem card_fixedSubgroup_eq_card_invariants (p : ℕ) [Module (ZMod p) (Additive V)] [Finite V]
    (φ : L →* MulAut V) (X : Subgroup L) :
    Nat.card ↥(fixedSubgroup φ X) =
      Nat.card ↥(invariants ((elabRepresentation p φ).comp X.subtype)) :=
  Nat.card_congr <| (Additive.ofMul (α := V)).subtypeEquiv fun x => by
    simp only [mem_fixedSubgroup, mem_invariants, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · intro hx l
      rw [elabRepresentation_apply, hx l.1 l.2]
    · intro hx l hl
      have h := hx ⟨l, hl⟩
      rw [elabRepresentation_apply] at h
      exact Additive.ofMul.injective h

/-- **Cardinality form of the fixed-point bridge** (`|C_V(X)| = p ^ dim V^X`).  Combines
`card_fixedSubgroup_eq_card_invariants` with `Module.card_eq_pow_finrank` for the finite
`ZMod p`-vector space `V^X`. -/
theorem card_fixedSubgroup_eq_pow_finrank (p : ℕ) [Fact p.Prime] [Module (ZMod p) (Additive V)]
    [Finite V] (φ : L →* MulAut V) (X : Subgroup L) :
    Nat.card ↥(fixedSubgroup φ X) =
      p ^ Module.finrank (ZMod p) ↥(invariants ((elabRepresentation p φ).comp X.subtype)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  classical
  letI : Fintype ↥(invariants ((elabRepresentation p φ).comp X.subtype)) := Fintype.ofFinite _
  rw [card_fixedSubgroup_eq_card_invariants p, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

/-- Being fixed by all of `⊤ ≤ G` is being fixed by all of `G`: the invariants of
`ρ.comp ⊤.subtype` coincide with `ρ.invariants`. -/
theorem invariants_comp_top_subtype {k G W : Type*} [CommRing k] [Group G] [AddCommGroup W]
    [Module k W] (ρ : Representation k G W) :
    invariants (ρ.comp (⊤ : Subgroup G).subtype) = ρ.invariants := by
  ext v
  simp only [mem_invariants, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact ⟨fun h g => h ⟨g, Subgroup.mem_top g⟩, fun h g => h g⟩

/-- **Per-factor cardinality form of Wielandt (9.1)** on a single elementary-abelian module `V`.
Given the dimension identity (⋆) `hdim` — the conclusion of
`WielandtCounting.finrank_elab_identity`, itself modulo the kernel-FPF fact (†) — raising it to
the `p`-th power through the fixed-point
bridge yields the cardinality identity `|C_V(UE)|^{|E|} · |V| = |C_V(E)|^{|E|} · |C_V(U)|`.

Here `C_V(UE) = fixedSubgroup φ ⊤` (the whole group `L = U ⊔ E` fixes), and the three terms of
`hdim` are `dim V^{UE} = dim ρ.invariants`, `dim V^E`, `dim V^U`, together with `dim V`.  This is
the per-chief-factor input that the chief-series multiplicativity multiplies up to the group-level
formula `wielandt_fixedPoint_frobenius`. -/
theorem card_fixedSubgroup_wielandt_of_dim (p : ℕ) [Fact p.Prime] [Module (ZMod p) (Additive V)]
    [Finite V] {U E : Subgroup L} [Fintype E] (φ : L →* MulAut V)
    (hdim : Fintype.card E * Module.finrank (ZMod p) ↥(elabRepresentation p φ).invariants +
        Module.finrank (ZMod p) (Additive V) =
      Fintype.card E *
          Module.finrank (ZMod p) ↥(invariants ((elabRepresentation p φ).comp E.subtype)) +
        Module.finrank (ZMod p) ↥(invariants ((elabRepresentation p φ).comp U.subtype))) :
    Nat.card ↥(fixedSubgroup φ ⊤) ^ Nat.card E * Nat.card V =
      Nat.card ↥(fixedSubgroup φ E) ^ Nat.card E * Nat.card ↥(fixedSubgroup φ U) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  classical
  letI : Fintype V := Fintype.ofFinite _
  have hV : Nat.card V = p ^ Module.finrank (ZMod p) (Additive V) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_additive V,
      Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hTop := card_fixedSubgroup_eq_pow_finrank p φ (⊤ : Subgroup L)
  rw [invariants_comp_top_subtype] at hTop
  rw [hTop, card_fixedSubgroup_eq_pow_finrank p φ E, card_fixedSubgroup_eq_pow_finrank p φ U, hV,
    ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  simp only [Nat.card_eq_fintype_card]
  rw [mul_comm _ (Fintype.card E), mul_comm _ (Fintype.card E)]
  exact hdim

end OddOrder.GroupTheory
