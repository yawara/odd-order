/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310ElemAbelian
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310FixedPointSplit
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310

/-!
# BG Theorem 3.10 for elementary abelian `M`, GROUP form (issue 3011, piece 2)

The elementary-abelian base results
`OddOrder.BG.Ch1.S03.card_eq_pow_card_invariants_of_elemAbelian_general` (part (b)) and
`OddOrder.BG.Ch1.S03.commutator_acts_trivially_of_elemAbelian_general` (part (c)) are stated in
**module** terms: the `R`-fixed points of `M` appear as the module `invariants` submodule
of `Additive M`, namely
`Representation.invariants ((ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)`.

The downstream general-nilpotent-`M` induction (issue 3011, piece 3) works uniformly in **group**
terms, denoting the fixed points as `fixedSubgroup (MulDistribMulAction.toMulAut H M) R` — the same
`fixedSubgroup` convention as the fixed-point split
`card_fixedSubgroup_eq_mul_of_mulDistribMulAction` (piece 1).  This file bridges the two:
`bgThm310_elemAbelian_group` restates (b)+(c) with the centralizer `C_M(R)` written as
`fixedSubgroup (MulDistribMulAction.toMulAut H M) R`, so piece 3 never touches the module framework.

## The bridge

The crux is that the module `invariants` submodule (of `Additive M`) and the group `fixedSubgroup`
(of `M`) are the same "`R`-fixed points of `M`", carried by the type synonym equivalence
`Additive.toMul`.  `card_invariants_eq_card_fixedSubgroup` establishes the cardinality equality via
`Equiv.subtypeEquiv Additive.toMul`; for part (c) the extra `IsCyclic C_M(R) ⟹ finrank ≤ 1` step
uses that `M` (hence `C_M(R)`) is elementary abelian, so a cyclic `C_M(R)` has order dividing `p`.

The fixed-point-free conjugation hypothesis `hFrob` the module leaves need is supplied by
`IsFrobeniusGroup.conj_frobenius`.
-/

namespace OddOrder.BG.Ch1.S03g

open OddOrder.GroupTheory
open Module

variable {p : ℕ} {H : Type*} [Group H] {M : Type*} [CommGroup M]

/-- `(MulDistribMulAction.toMulAut H M) l x = l • x`: the `MulAut`-framework action agrees with the
scalar action `•`. -/
private theorem toMulAut_apply_smul [MulDistribMulAction H M] (l : H) (x : M) :
    (MulDistribMulAction.toMulAut H M) l x = l • x := rfl

/-- In an elementary abelian `p`-group (`Module (ZMod p) (Additive M)`) every element satisfies
`m ^ p = 1`. -/
private theorem pow_card_eq_one_of_module_zmod [Module (ZMod p) (Additive M)] (m : M) :
    m ^ p = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  rfl

/-- **Bridge #3 (crux): the module invariants and the group fixed subgroup have equal cardinality.**
Both are the `R`-fixed points of `M`; the type-synonym equivalence `Additive.toMul` carries a fixed
vector of `Additive M` (module `invariants`) to a fixed element of `M` (group `fixedSubgroup`). -/
private theorem card_invariants_eq_card_fixedSubgroup [Module (ZMod p) (Additive M)]
    [MulDistribMulAction H M] (R : Subgroup H) :
    Nat.card ↥(Representation.invariants
        ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype))
      = Nat.card ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv Additive.toMul (fun v => ?_)
  rw [mem_fixedSubgroup]
  constructor
  · -- `v ∈ invariants → toMul v ∈ fixedSubgroup`
    intro hv l hl
    rw [toMulAut_apply_smul]
    have h := (Representation.mem_invariants _ v).mp hv ⟨l, hl⟩
    rw [MonoidHom.comp_apply, Representation.ofDistribMulAction_apply_apply] at h
    have h2 := congrArg Additive.toMul h
    rwa [show Additive.toMul ((R.subtype ⟨l, hl⟩) • v) = l • Additive.toMul v from rfl] at h2
  · -- `toMul v ∈ fixedSubgroup → v ∈ invariants`
    intro hx
    rw [Representation.mem_invariants]
    intro g
    rw [MonoidHom.comp_apply, Representation.ofDistribMulAction_apply_apply]
    have h := hx (R.subtype g) g.2
    rw [toMulAut_apply_smul] at h
    apply Additive.toMul.injective
    rw [show Additive.toMul ((R.subtype g) • v) = (R.subtype g) • Additive.toMul v from rfl]
    exact h

/-- Fixed-point characterisation of the cyclic-generated fixed subgroup: `m` is fixed by every power
of `x` iff it is fixed by `x`.  (The stabiliser of `m` is a subgroup, so
`x ∈ stab ↔ zpowers x ≤ stab`.) -/
private theorem mem_fixedSubgroup_zpowers_iff [MulDistribMulAction H M] (x : H) (m : M) :
    m ∈ fixedSubgroup (MulDistribMulAction.toMulAut H M) (Subgroup.zpowers x) ↔ x • m = m := by
  rw [mem_fixedSubgroup]
  constructor
  · intro h
    have hx := h x (Subgroup.mem_zpowers x)
    rwa [toMulAut_apply_smul] at hx
  · intro h l hl
    rw [toMulAut_apply_smul]
    have hxstab : x ∈ MulAction.stabilizer H m := MulAction.mem_stabilizer_iff.mpr h
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hxstab hl)

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

/-- **BG Theorem 3.10 (b)+(c) for an elementary abelian `M`, GROUP form** (issue 3011, piece 2).

Let a finite solvable group `H` act (`MulDistribMulAction`) on a finite nontrivial elementary
abelian `p`-group `M`, forming a Frobenius group `H = KR` with kernel `K ⊴ H` and complement `R`,
with `p ∤ |H|`, `(|R|, |K|) = 1`, `C_M(K) = 1` and the "prime manner" condition `C_M(⟨x⟩) = C_M(R)`
for every nonidentity `x ∈ R`.  Then:

* **(b)** `|M| = |C_M(R)| ^ |R|`;
* **(c)** if `C_M(R)` is cyclic then the kernel's derived subgroup acts trivially: every
  `g ∈ ⁅K, K⁆` fixes every `m ∈ M`.

Here `C_M(R) = fixedSubgroup (MulDistribMulAction.toMulAut H M) R` (group form, matching piece 1);
the module leaves are `card_eq_pow_card_invariants_of_elemAbelian_general` and
`commutator_acts_trivially_of_elemAbelian_general`, whose `invariants` centralizer is bridged to the
`fixedSubgroup` form by `card_invariants_eq_card_fixedSubgroup`.  `C_M(K) = 1`, the prime-manner
condition, and the fixed-point-free conjugation `hFrob` are supplied in group/`fixedSubgroup` form
and translated to the leaves' pointwise form. -/
theorem bgThm310_elemAbelian_group [Fact p.Prime]
    [Finite H] [IsSolvable H] [Finite M] [Nontrivial M] [Module (ZMod p) (Additive M)]
    [MulDistribMulAction H M] {K R : Subgroup H} [K.Normal]
    (hIsFrob : IsFrobeniusGroup H K R) (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hpH : ¬ p ∣ Nat.card H) (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hCK : fixedSubgroup (MulDistribMulAction.toMulAut H M) K = ⊥)
    (hcond3 : ∀ x ∈ R, x ≠ 1 →
      fixedSubgroup (MulDistribMulAction.toMulAut H M) (Subgroup.zpowers x)
        = fixedSubgroup (MulDistribMulAction.toMulAut H M) R) :
    Nat.card M = (Nat.card ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R)) ^ (Nat.card ↥R) ∧
      (IsCyclic ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R) →
        ∀ g ∈ ⁅K, K⁆, ∀ m : M, (g : H) • m = m) := by
  classical
  -- Translate the group-form hypotheses to the leaves' pointwise form.
  have hCK' : ∀ m : M, (∀ k : ↥K, (k : H) • m = m) → m = 1 := by
    intro m hm
    have hmem : m ∈ fixedSubgroup (MulDistribMulAction.toMulAut H M) K := by
      rw [mem_fixedSubgroup]
      intro l hl
      rw [toMulAut_apply_smul]
      exact hm ⟨l, hl⟩
    rw [hCK, Subgroup.mem_bot] at hmem
    exact hmem
  have hcond3' : ∀ x : H, x ∈ R → x ≠ 1 →
      ∀ m : M, ((x : H) • m = m) ↔ (∀ s : ↥R, (s : H) • m = m) := by
    intro x hxR hx1 m
    rw [← mem_fixedSubgroup_zpowers_iff x m, hcond3 x hxR hx1, mem_fixedSubgroup]
    constructor
    · intro h s
      have hs := h (s : H) s.2
      rwa [toMulAut_apply_smul] at hs
    · intro h l hl
      rw [toMulAut_apply_smul]
      exact h ⟨l, hl⟩
  refine ⟨?_, ?_⟩
  · -- (b): rewrite the module leaf's `invariants` count to the `fixedSubgroup` count.
    rw [← card_invariants_eq_card_fixedSubgroup (p := p) R]
    exact OddOrder.BG.Ch1.S03.card_eq_pow_card_invariants_of_elemAbelian_general
      hRne hKne hpH hcop hCK' hIsFrob.conj_frobenius hcond3'
  · -- (c): `IsCyclic C_M(R)` ⟹ `finrank (invariants) ≤ 1`, then the module leaf.
    intro hcyc
    have hfinrank : finrank (ZMod p) (Representation.invariants
        ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) ≤ 1 := by
      -- Every element of `C_M(R) ≤ M` satisfies `x ^ p = 1`, so its exponent divides `p`.
      haveI := hcyc
      have hexp : Monoid.exponent ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R) ∣ p := by
        apply Monoid.exponent_dvd_of_forall_pow_eq_one
        intro g
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact pow_card_eq_one_of_module_zmod (p := p) (g : M)
      -- Cyclic ⟹ `|C_M(R)| = exponent`, so `|C_M(R)| ∣ p`.
      have hcardFix : Nat.card ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R) ∣ p := by
        rw [← IsCyclic.exponent_eq_card]; exact hexp
      -- `|invariants| = p ^ finrank` and `|invariants| = |C_M(R)|`, so `p ^ finrank ∣ p`.
      haveI : Fintype ↥(Representation.invariants
          ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) :=
        Fintype.ofFinite _
      have hInvcard : Nat.card ↥(Representation.invariants
          ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype))
          = p ^ finrank (ZMod p) (Representation.invariants
            ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) := by
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
      set d := finrank (ZMod p) (Representation.invariants
        ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) with hd
      have hdvd : p ^ d ∣ p := by
        rw [← hInvcard, card_invariants_eq_card_fixedSubgroup (p := p) R]; exact hcardFix
      -- `p ^ d ∣ p` with `p` prime forces `d ≤ 1`.
      have hp : p.Prime := Fact.out
      have hp2 : 2 ≤ p := hp.two_le
      by_contra hcon
      rw [not_le] at hcon
      have h2 : p * p ∣ p := by
        have := dvd_trans (pow_dvd_pow p (show 2 ≤ d by omega)) hdvd
        rwa [pow_two] at this
      obtain ⟨c, hc⟩ := h2
      rw [mul_assoc] at hc
      have hone : (1 : ℕ) = p * c := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hc)
      have hple : p ≤ 1 := Nat.le_of_dvd one_pos ⟨c, hone⟩
      omega
    exact OddOrder.BG.Ch1.S03.commutator_acts_trivially_of_elemAbelian_general
      hIsFrob hRne hKne hpH hCK' hcond3' hfinrank

end OddOrder.BG.Ch1.S03g
