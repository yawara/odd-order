/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.HartleyTurull
import Mathlib.Algebra.Group.Action.End

/-!
# BG Theorem 3.10 — coprime fixed-point order split across an invariant normal subgroup

*(b)-glue infra for the general-nilpotent-`M` packaging of BG Theorem 3.10; see
`issues/3011-thm310-nilpotent-packaging.md`.)*

For a coprime, solvable automorphic action `φ : A →* MulAut G` and an `A`-invariant normal
subgroup `N ⊴ G`, the `B`-fixed points (`B ≤ A`) split multiplicatively across `N`:
```
|C_G(B)| = |C_N(B)| · |C_{G/N}(B)|.
```
Here all three counts are fixed subgroups of *restricted/induced* actions in the sense the
downstream Thm 3.10 induction on `|M|` needs:

* `C_G(B) = fixedSubgroup φ B`;
* `C_N(B) = fixedSubgroup hN.restrict B`, the fixed points of the action **restricted to `N`
  as a group in its own right** (`IsAInvariant.restrict`), *not* the ambient intersection
  `N ⊓ C_G(B)`;
* `C_{G/N}(B) = fixedSubgroup hN.quotientMulAutHom B`, the fixed points of the induced action on
  `G ⧸ N` (`IsAInvariant.quotientMulAutHom`).

## Relation to existing results

The mathematical content is already in the repository; this file only assembles it into the exact
statement shape the induction consumes:

* `OddOrder.Isaacs.Ch04.card_fixedSubgroup_eq_mul_of_normal` (Isaacs Cor 3.28 corollary, from the
  Hartley–Turull development) gives the split with the middle factor in the ambient
  `N ⊓ fixedSubgroup φ B` form (first-isomorphism theorem + BG Prop 1.5(d) quotient lift,
  `coprime_fixedPoints_quotient`);
* `OddOrder.Isaacs.Ch04.card_fixedSubgroup_restrict` identifies `|C_N(B)|` with `|C_G(B) ⊓ N|`.

Combining them yields the restrict-form split below.  The `MulDistribMulAction` bridge
(`card_fixedSubgroup_eq_mul_of_mulDistribMulAction`) specializes `φ := MulDistribMulAction.toMulAut`
so the Thm 3.10 top-level (stated for `MulDistribMulAction H M`) can invoke Prop 1.5(d)'s
`MulAut`-framework infra directly.
-/

namespace OddOrder.BG.Ch1.S03g

open OddOrder.GroupTheory (fixedSubgroup)
open _root_.OddOrder.Isaacs.Ch03 (IsAInvariant)

/-- **BG Theorem 3.10, coprime fixed-point order split** (the `(b)`-glue, `MulAut` framework).
For a coprime action `φ : A →* MulAut G` (`(|A|, |G|) = 1`), solvable on one side, and an
`A`-invariant normal `N ⊴ G`, the `B`-fixed points split as
`|C_G(B)| = |C_N(B)| · |C_{G/N}(B)|`, where `C_N(B)` is the fixed subgroup of the action
**restricted to `N`** (`hN.restrict`) and `C_{G/N}(B)` that of the induced action on `G ⧸ N`
(`hN.quotientMulAutHom`).

Proof: `card_fixedSubgroup_eq_mul_of_normal` gives the split with the ambient middle factor
`|N ⊓ C_G(B)|`, and `card_fixedSubgroup_restrict` rewrites it as the restricted count `|C_N(B)|`. -/
theorem card_fixedSubgroup_eq_mul_of_invariantNormal
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN : IsAInvariant φ N) (B : Subgroup A) :
    Nat.card ↥(fixedSubgroup φ B) =
      Nat.card ↥(fixedSubgroup hN.restrict B) *
        Nat.card ↥(fixedSubgroup hN.quotientMulAutHom B) := by
  rw [OddOrder.Isaacs.Ch04.card_fixedSubgroup_eq_mul_of_normal hCop hSolv hN B,
    OddOrder.Isaacs.Ch04.card_fixedSubgroup_restrict hN B]

/-- **BG Theorem 3.10, coprime fixed-point order split** (`MulDistribMulAction` bridge).
The framework-bridge form of `card_fixedSubgroup_eq_mul_of_invariantNormal`: a finite group `H`
acting on a finite solvable group `M` via `MulDistribMulAction`, with `(|H|, |M|) = 1`, splits the
`R`-fixed points (`R ≤ H`) across an `H`-invariant normal `M₀ ⊴ M`:
`|C_M(R)| = |C_{M₀}(R)| · |C_{M/M₀}(R)|`.

The action is presented as `φ := MulDistribMulAction.toMulAut H M : H →* MulAut M`, so `C_M(R)`,
`C_{M₀}(R)`, `C_{M/M₀}(R)` are the fixed subgroups of `φ`, of its restriction to `M₀`, and of the
induced action on `M ⧸ M₀`.  The invariance hypothesis `IsAInvariant (toMulAut H M) M₀` is
definitionally `∀ h : H, M₀.map (MulDistribMulAction.toMulEquiv M h) = M₀`. -/
theorem card_fixedSubgroup_eq_mul_of_mulDistribMulAction
    {H M : Type*} [Group H] [Finite H] [Group M] [Finite M] [IsSolvable M]
    [MulDistribMulAction H M] (hcop : Nat.Coprime (Nat.card H) (Nat.card M))
    (R : Subgroup H) {M₀ : Subgroup M} [M₀.Normal]
    (hM₀inv : IsAInvariant (MulDistribMulAction.toMulAut H M) M₀) :
    Nat.card ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R) =
      Nat.card ↥(fixedSubgroup hM₀inv.restrict R) *
        Nat.card ↥(fixedSubgroup hM₀inv.quotientMulAutHom R) :=
  card_fixedSubgroup_eq_mul_of_invariantNormal hcop (Or.inr ‹IsSolvable M›) hM₀inv R

end OddOrder.BG.Ch1.S03g
