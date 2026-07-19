/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppB_Thm62
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity

/-!
# BG Appendix D: CN-groups and the standing hypothesis

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix D, pp. 153--156.

Appendix D is a guide to the Feit--Hall--Thompson CN-theorem proof.  It is not part of the main
BG-to-Peterfalvi proof path, but it records two reusable local-analysis consequences for a
**minimal simple** CN-group of odd order.  This file carries the definitions and the elementary
consequences of the standing hypothesis; Lemmas D.1 and D.2 are in the sibling files.

## De-opacification (2026-07-18)

The hypothesis used to carry minimal simplicity and nonsolvability as *free* `Prop` fields with
self-carried proofs (`minimal_simple : Prop` together with `minimal_simple_holds :
minimal_simple`).  That made `MinimalSimpleCNHypothesis` inhabited for **every** odd-order
CN-group (instantiate both fields with `True`), so Lemmas D.1 and D.2 as stated asserted their
conclusions for all odd CN-groups — and in that reading **both are false**:

* **D.2** is refuted by `G = C₃` (abelian, hence CN, of odd order `3`): its Sylow `3`-subgroup is
  `P = ⊤ ≠ ⊥`, yet `derivedInG (N_G(P)) = ⊥`, so `P ≤ derivedInG (N_G(P))` fails.
* **D.1** is refuted by the solvable odd CN-group `F_{3⁶} ⋊ (C₇ ⋊ C₃)` of order `3⁷·7`: its
  normal elementary abelian kernel `K = F_{3⁶}` lies in every Sylow `3`-subgroup, while `n₃ = 7`
  (the quotient `C₇ ⋊ C₃` has seven Sylow `3`-subgroups), so distinct Sylow `3`-subgroups meet
  nontrivially.

The hypothesis is now the honest one: `IsCNGroup` together with the repository's standard
`OddOrder.BG.IsMinimalSimpleOdd` (used uniformly across BG §7--§16), for which both lemmas are
genuine theorems.  The former `CNTheoremReductionData` / `cnTheorem_reduction` "reduction
package" was deleted: its three components were exactly D.1, D.2 and Gorenstein Thm 14.2.2, so
once D.1 and D.2 are honest statements the package is a contentless wrapper (and it was itself
vacuous, being dischargeable by `True`-instantiation).

⚠ Do **not** discharge the Appendix D lemmas vacuously from `feitThompson`.  The CN-theorem is an
*input* to Feit--Thompson (BG p. 153: it "is actually needed in **FT**, although not for the part
covered by this book"), so deriving Appendix D from `feitThompson` would invert the mathematical
dependency order and produce contentless declarations.
-/

namespace OddOrder.BG.AppD

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-! ## CN-groups -/

/-- A `CN`-group is a group in which every nonidentity element has nilpotent
centralizer. -/
def IsCNGroup (G : Type*) [Group G] : Prop :=
  ∀ x : G, x ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({x} : Set G))

/-- The CN condition passes to subgroups: `C_H(x)` embeds into `C_G(x)`.

BG uses this silently in the proof of D.1, where the maximal subgroup `M` is treated as a
solvable CN-group so that Gorenstein's Corollary 1.6 applies to it. -/
theorem IsCNGroup.to_subgroup (h : IsCNGroup G) (H : Subgroup G) : IsCNGroup ↥H := by
  intro x hx
  have hxG : (x : G) ≠ 1 := fun hc => hx (Subtype.ext hc)
  haveI hnil : Group.IsNilpotent ↥(Subgroup.centralizer ({(x : G)} : Set G)) := h (x : G) hxG
  -- The inclusion `C_H(x) → C_G(x)`.
  let f : ↥(Subgroup.centralizer ({x} : Set ↥H)) →*
      ↥(Subgroup.centralizer ({(x : G)} : Set G)) :=
    { toFun := fun y => ⟨((y : ↥H) : G), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hy : (y : ↥H) * x = x * (y : ↥H) :=
          Subgroup.mem_centralizer_singleton_iff.mp y.2
        exact congrArg (Subtype.val (p := fun g => g ∈ H)) hy⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : ((a : ↥H) : G) = ((b : ↥H) : G) :=
      congrArg (fun (z : ↥(Subgroup.centralizer ({(x : G)} : Set G))) => (z : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  haveI : Group.IsNilpotent ↥f.range := inferInstance
  exact Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hf).symm

/-- The standing hypothesis for BG Appendix D: `G` is a **minimal simple** CN-group of odd order.

Minimal simplicity and nonsolvability are carried by the repository's standard
`OddOrder.BG.IsMinimalSimpleOdd` (odd order, simple, not solvable, every proper subgroup
solvable); in particular the oddness of `|G|` is `minimalSimpleOdd.odd` and is not repeated. -/
structure MinimalSimpleCNHypothesis (G : Type*) [Group G] [Finite G] : Prop where
  /-- Every nonidentity element of `G` has nilpotent centralizer. -/
  cn : IsCNGroup G
  /-- `G` is a minimal simple group of odd order. -/
  minimalSimpleOdd : OddOrder.BG.IsMinimalSimpleOdd G

namespace MinimalSimpleCNHypothesis

variable [Finite G]

/-- Under the standing hypothesis `G` has no nontrivial normal `p`-subgroup: `O_p(G) = 1`.

`O_p(G)` is normal, so simplicity leaves `⊥` or `⊤`; the latter would make `G` a `p`-group,
hence nilpotent, hence solvable. -/
theorem oPiCore_eq_bot (hyp : MinimalSimpleCNHypothesis G) (p : ℕ) [Fact p.Prime] :
    Isaacs.Ch03.oPiCore ({p} : Set ℕ) G = ⊥ := by
  haveI := hyp.minimalSimpleOdd.simple
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)
    inferInstance) with hbot | htop
  · exact hbot
  · exfalso
    have hpg : IsPGroup p ↥(Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
      Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (Isaacs.Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
    rw [htop] at hpg
    haveI : Group.IsNilpotent ↥(⊤ : Subgroup G) := hpg.isNilpotent
    haveI : Group.IsNilpotent G :=
      Group.nilpotent_of_mulEquiv (G := ↥(⊤ : Subgroup G)) Subgroup.topEquiv
    exact hyp.minimalSimpleOdd.notSolvable inferInstance

/-- A proper subgroup of `G` is a solvable CN-group; this is the package Gorenstein's
Corollary 1.6 consumes. -/
theorem solvable_cn_of_lt_top (hyp : MinimalSimpleCNHypothesis G) {M : Subgroup G} (hM : M < ⊤) :
    IsSolvable ↥M ∧ IsCNGroup ↥M :=
  ⟨hyp.minimalSimpleOdd.solvable_of_lt_top M hM, hyp.cn.to_subgroup M⟩

end MinimalSimpleCNHypothesis

end OddOrder.BG.AppD
