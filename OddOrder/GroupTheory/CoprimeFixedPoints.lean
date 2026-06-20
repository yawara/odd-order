/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CoprimeAction
import OddOrder.Isaacs.Ch04_Commutators.Main

/-!
# Multiplicativity of coprime fixed points across a chief step

`OddOrder.GroupTheory.CoprimeFixedPoints`: the group-theoretic core of the chief-series
assembly of **Peterfalvi (9.1)** (Wielandt's fixed-point formula).

Let `φ : L →* MulAut H` be an action of a finite group `L` on a finite group `H`, let
`X ≤ L` be a subgroup, and let `N ◁ H` be an `L`-invariant normal subgroup.  When the action
is coprime (`gcd(|X|, |H|) = 1`) and one of `X`, `H` is solvable, the fixed points split
multiplicatively across the short exact sequence `1 → N → H → H/N → 1`:
`|C_H(X)| = |C_H(X) ⊓ N| · |C_{H/N}(X)|`,
where `C_H(X) = fixedSubgroup φ X` and `C_{H/N}(X) = fixedSubgroup hN.quotientMulAutHom X` is the
fixed subgroup of the action induced on the quotient `H/N`.

The reduction map `C_H(X) →* H/N` (restriction of `QuotientGroup.mk' N`) has kernel
`C_H(X) ⊓ N` and image `C_{H/N}(X)`; the only nontrivial step is *surjectivity* onto the
quotient fixed points, which is exactly **Isaacs Cor 3.28**
(`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient`): every `X`-fixed coset has an `X`-fixed
representative.

Iterating this identity along an `L`-invariant chief series of `H` and multiplying the
per-chief-factor identity (`OddOrder.GroupTheory.card_fixedSubgroup_wielandt_of_dim`) yields the
group-level Wielandt formula `wielandt_fixedPoint_frobenius`.

`notes/peterfalvi/s11_wielandt_91_design.md` (I-5 chief-series multiplicativity), issue 2014.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

variable {L H : Type*} [Group L] [Group H]

section ChiefStep

variable {φ : L →* MulAut H} {X : Subgroup L} {N : Subgroup H}

/-- Restriction of `A`-invariance along a subgroup inclusion `X ≤ L`: if `N` is invariant under
the whole action `φ : L →* MulAut H`, it is invariant under the restricted action
`φ.comp X.subtype : X →* MulAut H`. -/
theorem isAInvariant_comp_subtype (hN : IsAInvariant φ N) :
    IsAInvariant (φ.comp X.subtype) N := by
  rw [isAInvariant_iff_smul_mem]
  intro a g hg
  simpa only [MonoidHom.comp_apply] using hN.smul_mem (X.subtype a) hg

/-- **The reduction map sends `C_H(X)` onto `C_{H/N}(X)`.**  The image of the fixed subgroup
`C_H(X) = fixedSubgroup φ X` under `QuotientGroup.mk' N` equals the fixed subgroup
`C_{H/N}(X) = fixedSubgroup hN.quotientMulAutHom X` of the induced quotient action.

`⊆` is automatic from `quotientMulAutHom_apply_mk'`; `⊇` is **Isaacs Cor 3.28**: an `X`-fixed
coset `gN` contains an `X`-fixed representative `c`, so `gN = cN` lies in the image. -/
theorem map_fixedSubgroup_eq_fixedSubgroup_quotient [N.Normal] [Finite ↥X] [Finite H]
    (hN : IsAInvariant φ N)
    (hCop : Nat.Coprime (Nat.card ↥X) (Nat.card H))
    (hSolv : IsSolvable ↥X ∨ IsSolvable H) :
    (fixedSubgroup φ X).map (QuotientGroup.mk' N) =
      fixedSubgroup (OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) X := by
  ext q
  simp only [Subgroup.mem_map, mem_fixedSubgroup]
  constructor
  · rintro ⟨c, hc, rfl⟩ l hl
    rw [OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk' hN, hc l hl]
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    -- The coset `gN` is `X`-fixed: each `φ l g` lies in `gN`.
    have hfix : ∀ a : ↥X, ∃ n ∈ N, (φ.comp X.subtype) a g = g * n := by
      intro a
      have h := hq (X.subtype a) a.2
      rw [OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk' hN,
        QuotientGroup.mk'_eq_mk'] at h
      obtain ⟨z, hz, hzeq⟩ := h
      exact ⟨z⁻¹, N.inv_mem hz, by
        rw [MonoidHom.comp_apply, eq_mul_inv_iff_mul_eq]; exact hzeq⟩
    -- Cor 3.28 produces an `X`-fixed representative `c ∈ gN`.
    obtain ⟨c, hc_fix, n, hn, hc_eq⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φ.comp X.subtype)
        hCop hSolv (isAInvariant_comp_subtype hN) hfix
    refine ⟨c, fun l hl => ?_, ?_⟩
    · simpa only [MonoidHom.comp_apply] using hc_fix ⟨l, hl⟩
    · have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [hc_eq, map_mul, hn1, mul_one]

/-- **Peterfalvi (9.1), I-5 chief-step multiplicativity.**  For a coprime solvable action
`φ : L →* MulAut H`, a subgroup `X ≤ L`, and an `L`-invariant normal subgroup `N ◁ H`, the
fixed points split across the chief step `1 → N → H → H/N → 1`:
`|C_H(X)| = |C_H(X) ⊓ N| · |C_{H/N}(X)|`.

The reduction homomorphism `C_H(X) →* H/N` has kernel `C_H(X) ⊓ N` and image `C_{H/N}(X)`
(surjectivity is Isaacs Cor 3.28, `map_fixedSubgroup_eq_fixedSubgroup_quotient`); Lagrange's
theorem and Noether's first isomorphism theorem give the product. -/
theorem card_fixedSubgroup_eq_mul [N.Normal] [Finite ↥X] [Finite H]
    (hN : IsAInvariant φ N)
    (hCop : Nat.Coprime (Nat.card ↥X) (Nat.card H))
    (hSolv : IsSolvable ↥X ∨ IsSolvable H) :
    Nat.card ↥(fixedSubgroup φ X) =
      Nat.card ↥((fixedSubgroup φ X ⊓ N : Subgroup H)) *
        Nat.card ↥(fixedSubgroup (OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) X) := by
  set C := fixedSubgroup φ X with hC
  -- The reduction map `f : C →* H/N`, its image and its kernel.
  have hr : ((QuotientGroup.mk' N).comp C.subtype).range =
      fixedSubgroup (OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hC]
    exact map_fixedSubgroup_eq_fixedSubgroup_quotient hN hCop hSolv
  have hke : ((QuotientGroup.mk' N).comp C.subtype).ker = N.subgroupOf C := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hk : Nat.card ↥((QuotientGroup.mk' N).comp C.subtype).ker
      = Nat.card ↥((C ⊓ N : Subgroup H)) := by
    rw [hke, Nat.card_congr ((N.subgroupOf C).equivMapOfInjective C.subtype
      C.subtype_injective).toEquiv, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((QuotientGroup.mk' N).comp C.subtype).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange
      ((QuotientGroup.mk' N).comp C.subtype)).toEquiv, hr, hk, mul_comm]

/-- The fixed subgroup of the **restricted action** `hN.restrict : L →* MulAut ↥N` on an
`L`-invariant subgroup `N ≤ H` is, as a subgroup of `↥N`, exactly `(C_H(X)).subgroupOf N`: an
element `n ∈ N` is fixed by the restricted `X`-action iff it is fixed by the ambient action
(`IsAInvariant.restrict_apply_val`). -/
theorem fixedSubgroup_restrict_eq (hN : IsAInvariant φ N) :
    fixedSubgroup hN.restrict X = (fixedSubgroup φ X).subgroupOf N := by
  ext x
  simp only [mem_fixedSubgroup, Subgroup.mem_subgroupOf]
  constructor
  · intro hx l hl
    have h := congrArg Subtype.val (hx l hl)
    rwa [IsAInvariant.restrict_apply_val] at h
  · intro hx l hl
    exact Subtype.ext ((IsAInvariant.restrict_apply_val hN l x).trans (hx l hl))

/-- **Card of the restricted fixed subgroup.**  `|C_N(X)| = |C_H(X) ⊓ N|`: the fixed points of the
`X`-action restricted to an `L`-invariant subgroup `N ≤ H` are exactly the ambient fixed points
lying in `N`.  This is the subgroup-side bridge feeding the per-chief-factor Wielandt identity on an
elementary-abelian chief factor `N` (its module `C_N(X)` of fixed points has this cardinality). -/
theorem card_fixedSubgroup_restrict (hN : IsAInvariant φ N) :
    Nat.card ↥(fixedSubgroup hN.restrict X) =
      Nat.card ↥((fixedSubgroup φ X ⊓ N : Subgroup H)) := by
  rw [fixedSubgroup_restrict_eq,
    Nat.card_congr (((fixedSubgroup φ X).subgroupOf N).equivMapOfInjective N.subtype
      N.subtype_injective).toEquiv, Subgroup.subgroupOf_map_subtype]

end ChiefStep

end OddOrder.GroupTheory
