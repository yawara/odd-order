/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRank
import Mathlib.RepresentationTheory.Basic

/-!
# `ZMod n`-modules with a group action: the missing `SMulCommClass`

For BG Theorem 3.7 (Frobenius kernel nilpotency), the coprime chief-factor case views a chief
factor — an elementary abelian `p`-group `M` with a conjugation `MulDistribMulAction` of the
ambient group `G` — as a `ZMod p`-linear `G`-representation on `Additive M`, via mathlib's
`Representation.ofDistribMulAction`, so that BG Lemma 3.3
(`OddOrder.BG.Ch1.S03b.centralizer_ne_bot_of_nontrivial_kernel`) applies (its coefficient field
is `ZMod p`, a field since `p` is prime).

mathlib already supplies `Module (ZMod p) (Additive M)` (`IsElementaryAbelian.zmodModule`) and
`DistribMulAction G (Additive M)`. The only piece `ofDistribMulAction` still needs is the
`SMulCommClass G (ZMod n) A` between the group action and the `ZMod n`-scalars — which holds for
*every* `ZMod n`-module, because each `g` acts by an additive endomorphism and additive maps
between `ZMod n`-modules are automatically `ZMod n`-linear (`ZMod.map_smul`).

plan = `notes/bg/s03_thm37_plan.md`.
-/

namespace OddOrder.GroupTheory

/-- A `MulDistribMulAction G M` on a `CommGroup` `M` transports to a `DistribMulAction` of `G` on
the additive group `Additive M`: `g` acts the same way, and distributing over `*` becomes
distributing over `+`. (mathlib only transports actions when `Additive`/`Multiplicative` is on the
acting side, so this acted-on-side transport is provided here.) -/
instance Additive.instDistribMulActionOfMulDistribMulAction {G M : Type*} [Monoid G] [CommGroup M]
    [MulDistribMulAction G M] : DistribMulAction G (Additive M) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := by
    change Additive.ofMul ((1 : G) • Additive.toMul a) = a
    rw [one_smul]
    rfl
  mul_smul g h a := by
    change Additive.ofMul ((g * h) • Additive.toMul a)
      = Additive.ofMul (g • (h • Additive.toMul a))
    rw [mul_smul]
  smul_zero g := by
    change Additive.ofMul (g • (1 : M)) = Additive.ofMul (1 : M)
    rw [smul_one]
  smul_add g a b := by
    change Additive.ofMul (g • (Additive.toMul a * Additive.toMul b))
      = Additive.ofMul (g • Additive.toMul a * g • Additive.toMul b)
    rw [smul_mul']

/-- On any `ZMod n`-module `A` carrying a `DistribMulAction` of a monoid `G`, the group action and
the `ZMod n`-scalar action commute: each `g` acts by an additive endomorphism, which is
automatically `ZMod n`-linear (`ZMod.map_smul`). This is the `SMulCommClass` that
`Representation.ofDistribMulAction (ZMod n) G A` requires. -/
instance instSMulCommClassZModOfDistribMulAction {n : ℕ} {G A : Type*} [Monoid G]
    [AddCommGroup A] [Module (ZMod n) A] [DistribMulAction G A] :
    SMulCommClass G (ZMod n) A where
  smul_comm g c a := ZMod.map_smul (DistribSMul.toAddMonoidHom A g) c a

/-- Descend a `MulDistribMulAction G M` to the quotient `G ⧸ L` when the normal subgroup `L` acts
trivially on `M`. (Used in BG Theorem 3.7's coprime chief-factor case: the conjugation action of
`G` on a chief factor `V` factors through `Ḡ = G/L` because `L` centralizes `V`.) -/
@[reducible]
noncomputable def mulDistribMulActionQuotientOfTrivial {G M : Type*} [Group G] [Monoid M]
    [MulDistribMulAction G M] (L : Subgroup G) [L.Normal]
    (hL : ∀ l : G, l ∈ L → ∀ m : M, l • m = m) :
    MulDistribMulAction (G ⧸ L) M :=
  MulDistribMulAction.compHom M
    (QuotientGroup.lift L (MulDistribMulAction.toMulAut G M)
      (fun l hl => MulEquiv.ext (fun m => by simpa using hL l hl m)))

/-- The descended action of `G ⧸ L` on `M` agrees with the original `G`-action on representatives:
`⟦g⟧ • m = g • m`. -/
theorem mulDistribMulActionQuotientOfTrivial_smul_mk {G M : Type*} [Group G] [Monoid M]
    [MulDistribMulAction G M] {L : Subgroup G} [L.Normal]
    (hL : ∀ l : G, l ∈ L → ∀ m : M, l • m = m) (g : G) (m : M) :
    letI := mulDistribMulActionQuotientOfTrivial L hL
    (QuotientGroup.mk g : G ⧸ L) • m = g • m :=
  rfl

/-- Sanity check that the coprime-bridge representation now elaborates: an elementary abelian
`p`-group `M` with a `MulDistribMulAction` of `G` becomes a `ZMod p`-linear `G`-representation on
`Additive M` through `Representation.ofDistribMulAction`. -/
example {p : ℕ} [Fact p.Prime] {G M : Type*} [Group G] [CommGroup M]
    [MulDistribMulAction G M] (hM : IsElementaryAbelian p M) : True := by
  letI := hM.zmodModule
  let _ρ : Representation (ZMod p) G (Additive M) :=
    Representation.ofDistribMulAction (ZMod p) G (Additive M)
  trivial

end OddOrder.GroupTheory
