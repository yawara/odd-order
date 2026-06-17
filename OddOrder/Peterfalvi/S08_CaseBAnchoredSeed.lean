/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBAssembly
import OddOrder.Peterfalvi.S08_CaseBXChiCoherence

/-!
# Peterfalvi §6.8.2 case-(B) — per-column anchored seed (`hXanchored`)

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.8.2.3).

The case-(B) coherence seed `IsCoherent hyp.tau (Xset W₂ ∪ Yset)` (consumed by the (6.8.3) endgame
`false_of_coherentXunionYset_caseB_of_not_coherentS`) is built by gluing the certain-type column
coherence `certainTypeSet_isCoherent_via_anchoredImages` (`S08_CaseBXChiCoherence`) with the
irreducible-`X` chain and the `Y`-coherence.  The remaining input to the column coherence is the
**`(6.8.2.3)` anchored-image identity** `hXanchored`:

  `∀ χ₂, columnSum h46 χ₂ ∈ certainTypeSet h46 k →`
  `  τ(columnSum χ₂ − a₀·η₁) = Ximg χ₂ − a₀·η₁^{τ₁}`.

This leaf assembles `hXanchored` from the per-`φ` anchored-image producer
`caseB_per_phi_anchored_fromYset` (`S08_CaseBAssembly`).  The key structural point (Peterfalvi
(6.8.2.3), verified gap analysis): the columns do **not** all lie over a single source character `φ`;
each column's underlying irreducible `θ_{χ₂} = Res^H μ_{0,χ₂}` lies over its **own** central linear
character `φ_θ` ([Is] Lemma 2.27, `Res^H_{W₂} θ = θ(1)·φ_θ` with `W₂ ≤ Z(H)`).  The first piece is
therefore the per-`θ` central-character data:

* `exists_central_phi_data` — for every irreducible `θ` of `H`, the central linear character `φ_θ`
  packages: irreducibility in both forms (`compHom e φ` on `W₂.subgroupOf H` for the per-`φ`
  producer; `φ` on `W₂` for the aggregate), linearity `φ_θ(1) = 1`, and positivity
  `0 < constituentWeight` (so `θ` is a positive-weight constituent of `φ_θ`).
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped Classical

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.3) per-column central-character data** (the Q1 "central gap").

For any irreducible character `θ` of `H` and a central subgroup `W₂ ≤ Z(H)`, the central **linear**
character `φ_θ` of `θ` ([Is] Lemma 2.27 `exists_central_linear_restriction`,
`Res^H_{W₂} θ = θ(1)·φ_θ`), transported from `W₂.subgroupOf H` to the ambient `L`-subgroup `W₂` via
`subgroupOfEquivOfLe`, packages every datum the per-`φ` machinery needs:

* `hφ' : IsIrreducibleCharacter (compHom e φ)` — irreducibility on `W₂.subgroupOf H`, the form
  consumed by `caseB_per_phi_anchored_fromYset` / `caseB_hcol` / `caseB_hirr`;
* `IsIrreducibleCharacter φ` (on the `L`-subgroup `W₂`, via `compHom_of_surjective`) and `φ 1 = 1`
  (linearity) — the form consumed by the `(6.8.2.2)` aggregate `exists_decomposition_caseB`
  (`φ : IrreducibleCharacter ↥W₂`, `φ(1) = 1`);
* `0 < constituentWeight hφ' θ` — positivity (`= θ(1)`), so `θ` is a positive-weight constituent of
  `φ_θ`;
* `Res^H_{W₂} θ = θ(1)·(compHom e φ_θ)` — the master central-restriction equation ([Is] 2.27), from
  which nontriviality (`φ_θ ≠ 1 ⟺ W₂ ⊄ ker θ`) is downstream-derivable.

This resolves the fixed-`φ` mismatch of the naive reading: the certain-type columns each lie over
their **own** central `φ_θ` (read off from `θ` via the central restriction), not over a single
shared `φ`.  Positivity is immediate from `⟨φ_θ, Res θ⟩ = θ(1)·⟨φ_θ,φ_θ⟩ = θ(1) ≠ 0`. -/
theorem exists_central_phi_data
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)] [Fintype ↥H]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    (θ : IrreducibleCharacter ↥H) :
    ∃ (φ : ClassFunction ↥W2 ℂ)
      (hφ' : IsIrreducibleCharacter
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ)),
      IsIrreducibleCharacter φ ∧ φ 1 = 1 ∧ 0 < constituentWeight hφ' θ ∧
      ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ)
        = (θ : ClassFunction ↥H ℂ) 1 •
          ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ := by
  obtain ⟨φN, hφNirr, hφN1, hres, _⟩ :=
    θ.2.exists_central_linear_restriction (W2.subgroupOf H) hcen
  set e := Subgroup.subgroupOfEquivOfLe hW2H with he
  have htrans : ClassFunction.compHom e.toMonoidHom
      (ClassFunction.compHom e.symm.toMonoidHom φN) = φN := by
    ext x
    simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine ⟨ClassFunction.compHom e.symm.toMonoidHom φN, by rw [htrans]; exact hφNirr,
    IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective hφNirr, ?_, ?_, ?_⟩
  · rw [ClassFunction.compHom_apply, map_one]; exact hφN1
  · rw [constituentWeight_pos_iff, htrans, hres, OddOrder.RepresentationTheory.inner_smul_right]
    obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hself : ClassFunction.inner φN φN = 1 := by
      have h := irreducibleCharacter_inner_eq_ite
        (⟨φN, hφNirr⟩ : IrreducibleCharacter ↥(W2.subgroupOf H))
        (⟨φN, hφNirr⟩ : IrreducibleCharacter ↥(W2.subgroupOf H))
      rwa [if_pos rfl] at h
    rw [hself, mul_one, star_ne_zero, hd]
    exact_mod_cast hdpos.ne'
  · rw [htrans]; exact hres

end OddOrder.Peterfalvi.S08
