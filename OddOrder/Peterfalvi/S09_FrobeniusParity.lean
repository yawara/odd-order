/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusConjIndex
import OddOrder.Peterfalvi.S09_ParityPrimitive

/-!
# Peterfalvi (7.9) conclusion for a Frobenius family (pp. 41-42)

The family-level (7.9) dichotomy: for two distinct members `i ≠ j` of a `FrobeniusFamily`,
`⟨β_i, ζ_j^{ν_j}⟩ ≠ 0` or `⟨β_j, ζ_i^{ν_i}⟩ ≠ 0` (`hypothesis79_conclusion`).

The one input of the parity route not yet assembled at family level is `hdelta_even`
(`⟨Δ_i, Δ_j⟩` is an even integer), built here from
* `Δ ∈ ℤ[Irr G]` (`delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent`, via the
  Sibley coherence `hypothesis78_isCoherent_sourceSet`),
* `Δ` real (`hypothesis78_delta_isReal`, the issue-0044 delta-reality milestone),
* `⟨Δ, 1_G⟩ = 0` (`delta_orth_one`), and
* the odd-order parity primitive `cfdot_real_vchar_even`
  (`⟨φ, ψ⟩ ≡ ⟨φ, 1⟩⟨ψ, 1⟩ (mod 2)` for real virtual characters).

Together with the already-landed cross orthogonality `hypothesis79_zetaImage_cross_eq_zero`
this closes the (7.9) chain; the conclusion is the `hbeta_ne` input of the good-index
estimates in the (7.10) `card_G0_lower_bound` assembly (issue 0044).
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **`Ind 1_H` is a virtual character** (the `hindZ` input of the (7.9) parity route): the
`ind1H`-indexed member of the `i`-th Sibley family is `Ind_{H_i}^{L_i} 1`, induced from an
irreducible, hence in `ℤ[Irr L_i]`. -/
theorem hypothesis78_ind1H_mem_ZIrr [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
      (F.hypothesis78 i hodd hnilp C hFrob).ind1H ∈ ZIrr ↥(F.L i) := by
  classical
  rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) _]
  exact ClassFunction.induce_mem_ZIrr _
    ((F.sibleyPlacedFamily i hodd hnilp C hFrob).θ _).property.mem_ZIrr

/-- **The (7.9) `hdelta_even` for a Frobenius family**: `⟨Δ_i, Δ_j⟩` is an even integer.

Both residuals are real (`hypothesis78_delta_isReal`) virtual characters
(`delta_mem_ZIrr_…_of_isCoherent`), so the odd-order parity primitive gives
`⟨Δ_i, Δ_j⟩ ≡ ⟨Δ_i, 1_G⟩ · ⟨Δ_j, 1_G⟩ (mod 2)`, and `⟨Δ_i, 1_G⟩ = 0` (`delta_orth_one`). -/
theorem hypothesis79_delta_even [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i j : Fin k) (hij : i ≠ j) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C_i : Subgroup ↥(F.L i))
    (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
    [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
    [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
    [((F.H j).subgroupOf (F.L j)).Normal]
    (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
    (C_j : Subgroup ↥(F.L j))
    (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j) :
    ∃ z : ℤ,
      ClassFunction.inner
          (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).first.delta
          (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).second.delta
        = (z : ℂ) ∧ Even z := by
  classical
  set H79 := F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j with hH79
  -- `Δ ∈ ℤ[Irr G]` for both members, off the Sibley coherence.
  obtain ⟨hδ₁Z, hδ₂Z, -, -⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_nu_eq i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
      (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j)
      (F.hypothesis78_ind1H_mem_ZIrr i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_zeta_irreducible i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_ind1H_mem_ZIrr j hodd hnilp_j C_j hFrob_j)
      (F.hypothesis78_zeta_irreducible j hodd hnilp_j C_j hFrob_j)
  -- Parity primitive on the two real virtual characters.
  obtain ⟨m, a, b, hm, ha, hb, heven⟩ :=
    cfdot_real_vchar_even hodd hδ₁Z
      (F.hypothesis78_delta_isReal i hodd hnilp_i C_i hFrob_i) hδ₂Z
      (F.hypothesis78_delta_isReal j hodd hnilp_j C_j hFrob_j)
  -- `a = ⟨Δ_i, 1_G⟩ = 0` (`constOne` and the trivial character coincide definitionally).
  have horth : ClassFunction.inner H79.first.delta
      ((trivialIrreducibleCharacter G : IrreducibleCharacter G) : ClassFunction G ℂ) = 0 :=
    H79.first.delta_orth_one (F.hypothesis78_betaDecomp i hodd hnilp_i C_i hFrob_i)
  have ha0 : a = 0 := by exact_mod_cast ha.trans horth
  exact ⟨m, hm.symm, by simpa [ha0] using heven⟩

/-- **Peterfalvi (7.9) for a Frobenius family**: for distinct members `i ≠ j`,
`⟨β_i, ζ_j^{ν_j}⟩ ≠ 0` or `⟨β_j, ζ_i^{ν_i}⟩ ≠ 0`.

Assembles the parity route `conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity`
from the Frobenius-level suppliers: the Sibley coherence over the source set with `ν` its
extension, `Ind 1_H ∈ ℤ[Irr L]`, irreducibility of the distinguished `ζ`, the (7.8.a) beta
decompositions, the cross orthogonality `⟨ζ_i^ν, ζ_j^ν⟩ = 0`, and the even parity of
`⟨Δ_i, Δ_j⟩` (`hypothesis79_delta_even`).  This is the `hbeta_ne` source for the good-index
norm estimates in the (7.10) assembly. -/
theorem hypothesis79_conclusion [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i j : Fin k) (hij : i ≠ j) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C_i : Subgroup ↥(F.L i))
    (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
    [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
    [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
    [((F.H j).subgroupOf (F.L j)).Normal]
    (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
    (C_j : Subgroup ↥(F.L j))
    (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j) :
    (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).conclusion := by
  classical
  exact (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j
      hFrob_j).conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    (F.hypothesis78_isCoherent_sourceSet i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_nu_eq i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_ind1H_mem_ZIrr i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_zeta_irreducible i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_ind1H_mem_ZIrr j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_zeta_irreducible j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_betaDecomp i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_betaDecomp j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis79_zetaImage_cross_eq_zero i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j)
    (F.hypothesis79_delta_even i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j)

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
