/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.WielandtAssembly
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge

/-!
# Peterfalvi (9.1): per-chief-factor discharge of the Wielandt identity

`OddOrder.GroupTheory.WielandtPerFactorDischarge`: piece C of the chief-series assembly of
**Peterfalvi (9.1)**.  It discharges the per-chief-factor predicate `WielandtPerFactor L U E` (the
single input to the group-level assembly `wielandt_formula_of_perfactor`) down to the *dimension*
identity (⋆) on each elementary-abelian chief factor — the only genuinely representation-theoretic
content (the kernel-FPF fact (†), discharged later in lane-f).

For an elementary-abelian `L`-invariant normal subgroup `N ◁ H` of prime exponent `p`, the
restricted action `hN.restrict : L →* MulAut ↥N` makes `↥N` an `𝔽_p`-representation
(`elabRepresentation`).  Given the dimension identity (⋆) `PerFactorDimIdentity` for that
representation (the conclusion of `WielandtCounting.finrank_elab_identity`, modulo (†)):

* `card_fixedSubgroup_wielandt_of_dim` raises it to the cardinality identity
  `|C_N(UE)|^{|E|} · |N| = |C_N(E)|^{|E|} · |C_N(U)|` on `↥N`;
* `card_fixedSubgroup_restrict` rewrites each restricted fixed-point count `|C_N(X)|` as the ambient
  `|C_H(X) ⊓ N|`,

yielding exactly the per-chief-factor identity packaged by `WielandtPerFactor`.  This completes the
reduction of the group-level Wielandt formula to the single per-factor dimension identity (†).

## Instance plumbing for `↥N`

Viewing the subgroup `↥N` as an `𝔽_p`-vector space is delicate: `↥N` carries the *canonical*
non-commutative `Group ↥N`, so layering a `CommGroup ↥N` on top creates an `Additive ↥N` diamond
that defeats the `↥(Submodule …)` coercions appearing in the dimension identity.  We avoid this two
ways:

* the commutative-group / module structures are built on the canonical underlying group
  (`subgroupCommGroup`, `subgroupZmodModule`), so `MulAut ↥N` still matches `hN.restrict`;
* the dimension identity itself is stated through `WielandtDimIdentity`, whose module is a proper
  instance *binder* (not a `letI`).  The `↥(Submodule …)` coercions are then resolved once, against
  the binder, and survive substitution of the concrete `↥N` module — whereas resolving them against
  a `letI`-bound module fails.

`notes/peterfalvi/s11_wielandt_91_design.md` (assembly piece C), issue 2014.
-/

namespace OddOrder.GroupTheory

open Module Representation
open OddOrder.Isaacs.Ch03 (IsAInvariant)

/-- The commutative-group structure on an elementary-abelian subgroup `↥N` whose underlying group is
the *canonical* `Group ↥N` (so `MulAut ↥N` is unchanged, and the action `hN.restrict` still
typechecks against `elabRepresentation`'s `[CommGroup ↥N]`). -/
abbrev IsElementaryAbelian.subgroupCommGroup {H : Type*} [Group H] {N : Subgroup H} {p : ℕ}
    (hpe : IsElementaryAbelian p ↥N) : CommGroup ↥N :=
  { (inferInstance : Group ↥N) with mul_comm := hpe.comm }

/-- The canonical `𝔽_p`-module structure on `Additive ↥N` for an elementary-abelian subgroup `↥N` of
exponent `p`, built directly on `subgroupCommGroup` via `AddCommGroup.zmodModule` (so its
`AddCommGroup (Additive ↥N)` is the canonical one — *not* the one PRank's
`IsElementaryAbelian.zmodModule` produces through `IsMulCommutative`, which would diamond against
the `↥(Submodule …)` coercions). -/
noncomputable abbrev IsElementaryAbelian.subgroupZmodModule {H : Type*} [Group H] {N : Subgroup H}
    {p : ℕ} (hpe : IsElementaryAbelian p ↥N) :
    letI : CommGroup ↥N := hpe.subgroupCommGroup
    Module (ZMod p) (Additive ↥N) :=
  letI : CommGroup ↥N := hpe.subgroupCommGroup
  AddCommGroup.zmodModule (n := p) fun x => by
    have h2 : Additive.ofMul ((Additive.toMul x) ^ p) = Additive.ofMul (1 : ↥N) := by
      rw [hpe.pow_eq_one]
    rwa [ofMul_pow, ofMul_one, ofMul_toMul] at h2

variable {L : Type*} [Group L] {U E : Subgroup L}

/-- The **dimension identity** (⋆) of Peterfalvi (9.1) for an abstract `𝔽_p`-representation `ρ` of
`L` on `Additive V` (`V` elementary abelian): `|E|·dim V^{UE} + dim V = |E|·dim V^E + dim V^U`,
where `V^{UE} = ρ.invariants` (the whole `L = ⟨U,E⟩` fixes).

This is the conclusion of `WielandtCounting.finrank_elab_identity` (modulo the kernel-FPF fact (†)).
The module is a proper instance *binder* so the `↥(Submodule …)` coercions resolve here, once,
rather than against a `letI`-bound module at each chief factor (where they fail). -/
def WielandtDimIdentity {V : Type*} [CommGroup V] (p : ℕ) [Module (ZMod p) (Additive V)]
    (ρ : L →* MulAut V) (U E : Subgroup L) [Fintype E] : Prop :=
  Fintype.card E * Module.finrank (ZMod p) ↥(elabRepresentation p ρ).invariants +
      Module.finrank (ZMod p) (Additive V) =
    Fintype.card E *
        Module.finrank (ZMod p) ↥(invariants ((elabRepresentation p ρ).comp E.subtype)) +
      Module.finrank (ZMod p) ↥(invariants ((elabRepresentation p ρ).comp U.subtype))

/-- The per-chief-factor instance of the dimension identity (⋆), on an elementary-abelian
`L`-invariant normal subgroup `N ◁ H` of exponent `p`, for the restricted action `hN.restrict`.
This is `WielandtDimIdentity` specialised to `V = ↥N` with its canonical `𝔽_p`-structure; it is
the sole representation-theoretic input to the chief-series assembly (the kernel-FPF fact (†)). -/
def PerFactorDimIdentity [Fintype E] {H : Type*} [Group H] (φ : L →* MulAut H) {N : Subgroup H}
    (hN : IsAInvariant φ N) (p : ℕ) (hpe : IsElementaryAbelian p ↥N) : Prop :=
  letI : CommGroup ↥N := hpe.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥N) := hpe.subgroupZmodModule
  WielandtDimIdentity p hN.restrict U E

/-- **Peterfalvi (9.1), the per-chief-factor discharge (piece C).**  Given the dimension identity
(⋆) `hdim` on every elementary-abelian chief factor (the kernel-FPF fact (†), supplied later by the
representation theory of lane-f), the per-chief-factor predicate `WielandtPerFactor L U E` holds.

For each factor `N` (prime exponent `p`): `card_fixedSubgroup_wielandt_of_dim` turns the dimension
identity into the cardinality identity `|C_N(UE)|^{|E|} · |N| = |C_N(E)|^{|E|} · |C_N(U)|` on `↥N`,
and `card_fixedSubgroup_restrict` rewrites `|C_N(X)| = |C_H(X) ⊓ N|`.  Feeding the result into
`wielandt_formula_of_perfactor` proves the group-level Wielandt formula. -/
theorem wielandtPerFactor_of_dim.{u} [Fintype E]
    (hdim : ∀ (H : Type u) [Group H] [Finite H] (φ : L →* MulAut H) (N : Subgroup H) [N.Normal]
      (hN : IsAInvariant φ N) (p : ℕ) (_hp : p.Prime) (hpe : IsElementaryAbelian p ↥N),
      PerFactorDimIdentity (U := U) (E := E) φ hN p hpe) :
    WielandtPerFactor.{_, u} L U E := by
  intro H _ _ φ N _ hN_inv helab
  obtain ⟨p, hp, hpe⟩ := helab
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup ↥N := hpe.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥N) := hpe.subgroupZmodModule
  -- The per-factor dimension identity, unfolded to the abstract `WielandtDimIdentity` form.
  have hd : WielandtDimIdentity (V := ↥N) p hN_inv.restrict U E := hdim H φ N hN_inv p hp hpe
  -- The cardinality identity on the elementary-abelian chief factor `↥N` (restricted action).
  have key := card_fixedSubgroup_wielandt_of_dim (V := ↥N) (U := U) (E := E) p hN_inv.restrict hd
  -- Rewrite the restricted fixed-point counts `|C_N(X)|` as the ambient `|C_H(X) ⊓ N|`.
  rw [card_fixedSubgroup_restrict hN_inv (X := ⊤), card_fixedSubgroup_restrict hN_inv (X := E),
    card_fixedSubgroup_restrict hN_inv (X := U)] at key
  exact key

end OddOrder.GroupTheory
