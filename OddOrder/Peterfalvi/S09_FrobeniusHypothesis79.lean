/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusHypothesis78

/-!
# Peterfalvi (7.9) two-family datum for a Frobenius family

Downstream of `S09_FrobeniusHypothesis78` (per-member `Hypothesis78` as data): for two *distinct*
members `i ≠ j` of a `FrobeniusFamily`, the pair of (7.8) coherence setups forms a `Hypothesis79`
(the (7.9) two-family interface).  Its `dadeSupport_disjoint` field reduces — via
`sibley_dadeSupport_eq_kernelSpread` — to the family's already-proven `kernelSpread_disjoint`.

This unlocks the sorry-free (7.9) `conclusion` dichotomy (`(β_i, ζ_j^ν) ≠ 0 ∨ (β_j, ζ_i^ν) ≠ 0`)
for each pair, the `hbeta_ne` input of the good-index estimate `chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero`
in the (7.10) `card_G0_lower_bound` assembly (issue 0044).
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Sibley (7.1) datum's Dade support is the kernel spread** `(H_i^#)^G`.  Same computation as
`dadeSupport_hypothesis71_eq_kernelSpread` (the local subgroups `H(a) = ⊥` of the `of_isTISubset`
construction collapse each coset `aH(a)` to `{a}`), but for `sibleyToHypothesis71` (support written as
`sharpImage ((H_i).subgroupOf L_i) = H_i^#` via `sharpImage_subgroupOf_eq`).  This identifies the
`Hypothesis79.dadeSupport_disjoint` field with `kernelSpread_disjoint`. -/
lemma sibley_dadeSupport_eq_kernelSpread [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.sibleyToHypothesis71 i hodd hnilp C hFrob).hyp.dadeSupport = F.kernelSpread i := by
  rw [F.kernelSpread_eq_conjugatesOfSet i]
  ext g
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff, Group.mem_conjugatesOfSet_iff]
  constructor
  · rintro ⟨⟨aval, ha_mem⟩, h, hh, hconj⟩
    have hh1 : h = 1 := Subgroup.mem_bot.mp hh
    subst hh1
    rw [F.sharpImage_subgroupOf_eq i] at ha_mem
    exact ⟨aval, ha_mem, by simpa using hconj⟩
  · rintro ⟨y, hy, hconj⟩
    have hy' : y ∈ OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)) := by
      rw [F.sharpImage_subgroupOf_eq i]; exact hy
    exact ⟨⟨y, hy'⟩, 1, Subgroup.one_mem _, by simpa using hconj⟩

/-- **The Peterfalvi (7.9) two-family datum for two distinct Frobenius members** `i ≠ j`.  Bundles
the two per-member `Hypothesis78` (as data, `F.hypothesis78`) with the disjointness of their Dade
supports, which reduces to `kernelSpread_disjoint` via `sibley_dadeSupport_eq_kernelSpread`.  Feeds
the sorry-free (7.9) `Hypothesis79.conclusion` dichotomy. -/
noncomputable def hypothesis79 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i j : Fin k) (hij : i ≠ j) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C_i : Subgroup ↥(F.L i))
    (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
    [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
    [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
    (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
    (C_j : Subgroup ↥(F.L j))
    (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j) :
    Hypothesis79 G (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i)
      (OddOrder.Peterfalvi.S08.sharpImage ((F.H j).subgroupOf (F.L j))) (F.L j) where
  odd_card := hodd
  first := F.hypothesis78 i hodd hnilp_i C_i hFrob_i
  second := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  dadeSupport_disjoint := by
    haveI : Finite G := Finite.of_fintype G
    rw [show (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.hyp71.hyp.dadeSupport
          = F.kernelSpread i from F.sibley_dadeSupport_eq_kernelSpread i hodd hnilp_i C_i hFrob_i,
        show (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.hyp71.hyp.dadeSupport
          = F.kernelSpread j from F.sibley_dadeSupport_eq_kernelSpread j hodd hnilp_j C_j hFrob_j]
    exact F.kernelSpread_disjoint hij

/-- **The `ν` of the `i`-th member's `Hypothesis78` is the coherent extension** (the `hnu` input of
the (7.9) `conclusion` producers).  Definitional: `hypothesis78` feeds `coh.extension` as the `nu`
field of `hypothesis78OfDade`. -/
lemma hypothesis78_nu_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).nu = (F.coherence i hodd hnilp C hFrob).extension := rfl

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
