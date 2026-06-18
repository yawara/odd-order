/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBAssembly
import OddOrder.Peterfalvi.S08_CaseBXChiCoherence
import OddOrder.Peterfalvi.S08_CaseBEnumeration

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

/-- **Central character nontriviality** from the master restriction equation.  If
`Res^H_N θ = θ(1)·χ` (the [Is] 2.27 form, `χ = compHom e φ_θ`) and `θ` is **not** constant on `N`
(some `w ∈ N` with `θ(w) ≠ θ(1)`, i.e. `N ⊄ ker θ`), then the central character `χ` is nontrivial.
Indeed `χ = trivial` would force `θ(w) = θ(1)·1 = θ(1)` for every `w ∈ N`. -/
theorem compHom_phi_ne_trivial_of_restrict
    {N : Subgroup ↥H} {θ : ClassFunction ↥H ℂ} {χ : ClassFunction ↥N ℂ}
    (hres : ClassFunction.restrict N θ = θ 1 • χ)
    (hne : ∃ w : ↥N, θ (w : ↥H) ≠ θ 1) :
    χ ≠ trivialClassFunction ↥N := by
  obtain ⟨w, hw⟩ := hne
  intro htriv
  apply hw
  have hval := congrFun (congrArg (fun f : ClassFunction ↥N ℂ => (f : ↥N → ℂ)) hres) w
  rw [htriv] at hval
  simpa [ClassFunction.restrict_apply, ClassFunction.smul_apply, trivialClassFunction_apply,
    smul_eq_mul] using hval

/-- **(6.8.2.2) aggregate for the canonical `Y`-coherence** (good-case form).  The variant of
`exists_decomposition_caseB` that returns the decomposition against the **canonical** Sibley
`Y`-coherence `hyp.coherentYset` (not an opaque existential `cY`): in the good case the witness of
`coeff_eq_neg_or_edge_caseB` *is* `hyp.coherentYset`, and the edge case requires `|𝒴| = 2`, excluded
by `hYcard`.  This is what makes the `∀`-column `hXanchored` use a **single uniform** anchor
`hyp.coherentYset.extension η₁` across all columns. -/
theorem exists_decomposition_caseB_coherentYset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2)
    (hYcard : hyp.Yset.ncard ≠ 2) :
    ∃ X : ClassFunction G ℂ,
      (∀ η ∈ hyp.Yset, ClassFunction.inner X (hyp.coherentYset.extension η) = 0)
        ∧ X ∈ ZIrr G
        ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          = X - ((W2.subgroupOf H).index : ℂ) • hyp.coherentYset.extension η₁ := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  have hgood : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁)
      = -((W2.subgroupOf H).index : ℂ) := by
    rcases hyp.coeff_eq_neg_or_edge_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hc2 hFPF
      with h | ⟨hm2, _⟩
    · exact h
    · exact absurd hm2 hYcard
  obtain ⟨horth, hXZ⟩ :=
    hyp.orthogonal_tau_indW2_add_extension_general_caseB hW2H hW2comm hyp.coherentYset hη₁ φ hφ1 h1
      hgood
  refine ⟨hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)
      + ((W2.subgroupOf H).index : ℂ) • hyp.coherentYset.extension η₁, horth, hXZ, ?_⟩
  abel

/-- **(6.8.2.3) certain-type column is nonconstant on `W₂`** (`hWne` provider, the `(R1)` §6 fact).
For a nontrivial column `χ₂ ≠ 1`, the underlying irreducible `θ = Res^H μ_{0,χ₂}` is **not constant
on `W₂.subgroupOf H`** (`∃ w, θ(w) ≠ θ(1)`, i.e. `W₂ ⊄ ker θ`).  This is Peterfalvi (4.7)
`not_subset_characterKernel_chiRestrict_of_ne_one` (`χ_j = Res_K μ_{0j}` has `W₂ ⊄ ker`), repackaged
to the existential form at `H = K` and reduced to the underlying `L`-values of `μ_{0,χ₂}`. -/
theorem caseB_column_W2_nonconstant
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    ∃ w : ↥(h46.W2.subgroupOf H),
      (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) (w : ↥H)
        ≠ (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) 1 := by
  classical
  by_contra hc
  push_neg at hc
  refine OddOrder.Peterfalvi.S06.Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one
    h46.toCertainTypeHypothesis.toHypothesis hχ₂ ?_
  intro g hg
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, ClassFunction.restrict_apply,
    ClassFunction.restrict_apply]
  have hW2H : h46.W2 ≤ H := h46.W2_le_K.trans (le_of_eq hHK)
  have hgW2 : (g : ↥L) ∈ h46.W2 := Subgroup.mem_subgroupOf.mp hg
  have hgH : (g : ↥L) ∈ H := hW2H hgW2
  have hval := hc ⟨⟨(g : ↥L), hgH⟩, Subgroup.mem_subgroupOf.mpr hgW2⟩
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply] at hval
  simpa using hval

/-- **(6.8.2.3) per-column anchored image** — the core integration.

For a **nontrivial** certain-type column `χ₂ ≠ 1` (`hχ₂`; its underlying irreducible
`θ = Res^H μ_{0,χ₂}` is then nonconstant on `W₂` by `caseB_column_W2_nonconstant`), and with
`|𝒴| ≠ 2` (`hYcard`, excluding the relabel edge), the Sibley–Dade map sends the anchored difference
`columnSum χ₂ − a·η₁` to `X − a·η₁^{τ₁}` for some virtual `X` against the **canonical** `Y`-coherence
`hyp.coherentYset`, with `a = θ(1)` (the constituent weight).

Assembles the per-`θ` central character (`exists_central_phi_data`), the `(6.8.2.2)` aggregate
against `hyp.coherentYset` (`exists_decomposition_caseB_coherentYset`), the column/irreducible bundles
(`caseB_hcol`/`caseB_hirr`/`caseB_hirrAnc`, with non-linearity `caseB_hnonlin`), and the per-`φ`
anchored producer (`caseB_per_phi_anchored_fromYset`), then rewrites `Ind^L_H θ = columnSum χ₂`
(`columnSum_eq_induce_H`).  This is the `(6.8.2.3)` per-column anchored image `hXanchored` (modulo the
uniform `a₀` and the `Ximg` packaging, handled at the `∀`-column assembly). -/
theorem caseB_column_anchored_image
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hYcard : hyp.Yset.ncard ≠ 2) :
    ∃ (X : ClassFunction G ℂ) (a : ℕ),
      ((OddOrder.Peterfalvi.S06.columnSum h46 χ₂ : ClassFunction ↥L ℂ) 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁)
        = X - (a : ℂ) • hyp.coherentYset.extension η₁ := by
  classical
  haveI : Fintype ↥h46.W2 := Fintype.ofFinite _
  have hWne := caseB_column_W2_nonconstant h46 hHK hχ₂
  have hθirr : IsIrreducibleCharacter
      (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) := by
    have h := h46.certainTypeRestrict_isIrreducible χ₂; rwa [hHK] at h
  set θ : IrreducibleCharacter ↥H :=
    ⟨ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ), hθirr⟩ with hθdef
  have hθval : (θ : ClassFunction ↥H ℂ)
      = ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) := by
    rw [hθdef]
  obtain ⟨φ, hφ', hφirr, hφ1, hweight, hreseq⟩ := exists_central_phi_data hW2H hcen θ
  rw [hθval] at hreseq
  have hφne : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ
      ≠ trivialClassFunction ↥(h46.W2.subgroupOf H) :=
    compHom_phi_ne_trivial_of_restrict hreseq hWne
  have hφneIrr : (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2)
      ≠ trivialIrreducibleCharacter ↥h46.W2 := by
    intro heq
    apply hφne
    have hφtriv : φ = trivialClassFunction ↥h46.W2 := by
      have h := congrArg (fun c : IrreducibleCharacter ↥h46.W2 => (c : ClassFunction ↥h46.W2 ℂ)) heq
      simpa using h
    rw [hφtriv]
    ext x
    simp [ClassFunction.compHom_apply, trivialClassFunction_apply]
  obtain ⟨Xagg, hXaggorth, hXZ, hdecomp⟩ :=
    exists_decomposition_caseB_coherentYset hyp hcop hp hHp hprime hW2comm hW2cenL hη₁
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2) hφ1 hφneIrr hc2 hFPF hYcard
  simp only [IrreducibleCharacter.coe_mk] at hdecomp
  have hnonlin := caseB_hnonlin hW2H hderiv hφ' hφne
  have hcol := caseB_hcol hyp h46 hHK hW1 hW2H hcen hφ' hη₁
  have hirr := caseB_hirr hyp h46 hHK hW2H hcen hφ' hη₁ hnonlin
  have hirrAnc := caseB_hirrAnc hyp h46 hHK hW2H hφ' hη₁ hnonlin
  have hanc := caseB_per_phi_anchored_fromYset hyp h46 hHK hW2H hcen hφ' hyp.coherentYset hη₁
    hcol hirr hirrAnc (hXaggorth η₁ hη₁) hdecomp ⟨θ, hweight⟩
  refine ⟨(caseB_phi_family hyp h46 hW2H hφ' hcol hirr ⟨θ, hweight⟩).X,
    constituentWeight hφ' θ, ?_, ?_⟩
  · rw [columnSum_eq_induce_H h46 hHK χ₂, ← hθval, ClassFunction.induce_apply_one,
      hyp.index_H_eq_card_W1, hyp.Yset_apply_one hη₁,
      constituentWeight_eq_apply_one hW2H hcen hφ' hweight]
    ring
  · rw [columnSum_eq_induce_H h46 hHK χ₂, ← hθval]
    exact hanc

/-- **(6.8.2.3) per-member anchored image — general `χ = Ind^L_H θ ∈ X`.**  Generalizes
`caseB_column_anchored_image` from a certain-type column to an **arbitrary** irreducible `θ` of `H`
that is nonconstant on `W₂` (`hθne`, i.e. `W₂ ⊄ ker θ`, equivalently `Ind^L_H θ ∈ X = S − S(W₂)`),
and additionally exposes the **seam orthogonality** `⟨X, η₁^{τ₁}⟩ = 0`
(`caseB_constituentDecomposition_X_orthogonal`).

Returns the Peterfalvi (6.8.2.3) anchored image
`τ(Ind^L_H θ − a·η₁) = X − a·η₁^{τ₁}` (`a = θ(1)`) together with `X ⊥ η₁^{τ₁}`.  Since under central
`W₂` every `χ = Ind^L_H θ ∈ X` (reducible certain-type column **or** irreducible) arises as a
positive-weight constituent of the central `φ_θ`-induction (`exists_central_phi_data`), this single
lemma is the uniform (6.8.2.3) `hXanchored` + `hXmixed` content for the **whole** of `X` — the basis
of the case-(B) `X ∪ Y` coherence seed (`coherentXunionYset_caseB_of_glued`).

The proof mirrors `caseB_column_anchored_image` (central char + (6.8.2.2) aggregate + bundles +
per-`φ` producer) with `θ` taken directly instead of `Res^H μ_{0,χ₂}`, plus the `X ⊥ Y^{τ₁}` call
with the textbook partner `η' = η̄₁` reconstructed from `η₁ ∈ Y`. -/
theorem caseB_member_anchored_image
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (θ : IrreducibleCharacter ↥H)
    (hθne : ∃ w : ↥(h46.W2.subgroupOf H),
      (θ : ClassFunction ↥H ℂ) (w : ↥H) ≠ (θ : ClassFunction ↥H ℂ) 1)
    (hYcard : hyp.Yset.ncard ≠ 2) :
    ∃ (X : ClassFunction G ℂ) (a : ℕ),
      ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ) : ClassFunction ↥L ℂ) 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁)
        = X - (a : ℂ) • hyp.coherentYset.extension η₁ ∧
      ClassFunction.inner X (hyp.coherentYset.extension η₁) = 0 := by
  classical
  haveI : Fintype ↥h46.W2 := Fintype.ofFinite _
  obtain ⟨φ, hφ', hφirr, hφ1, hweight, hreseq⟩ := exists_central_phi_data hW2H hcen θ
  have hφne : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ
      ≠ trivialClassFunction ↥(h46.W2.subgroupOf H) :=
    compHom_phi_ne_trivial_of_restrict hreseq hθne
  have hφneIrr : (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2)
      ≠ trivialIrreducibleCharacter ↥h46.W2 := by
    intro heq
    apply hφne
    have hφtriv : φ = trivialClassFunction ↥h46.W2 := by
      have h := congrArg (fun c : IrreducibleCharacter ↥h46.W2 => (c : ClassFunction ↥h46.W2 ℂ)) heq
      simpa using h
    rw [hφtriv]; ext x
    simp [ClassFunction.compHom_apply, trivialClassFunction_apply]
  obtain ⟨Xagg, hXaggorth, hXZ, hdecomp⟩ :=
    exists_decomposition_caseB_coherentYset hyp hcop hp hHp hprime hW2comm hW2cenL hη₁
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2) hφ1 hφneIrr hc2 hFPF hYcard
  simp only [IrreducibleCharacter.coe_mk] at hdecomp
  have hnonlin := caseB_hnonlin hW2H hderiv hφ' hφne
  have hcol := caseB_hcol hyp h46 hHK hW1 hW2H hcen hφ' hη₁
  have hirr := caseB_hirr hyp h46 hHK hW2H hcen hφ' hη₁ hnonlin
  have hirrAnc := caseB_hirrAnc hyp h46 hHK hW2H hφ' hη₁ hnonlin
  have hanc := caseB_per_phi_anchored_fromYset hyp h46 hHK hW2H hcen hφ' hyp.coherentYset hη₁
    hcol hirr hirrAnc (hXaggorth η₁ hη₁) hdecomp ⟨θ, hweight⟩
  -- seam orthogonality `⟨X, η₁^{τ₁}⟩ = 0`, textbook partner `η' = η̄₁` reconstructed from `η₁ ∈ Y`.
  have hη₁irr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hconj : η₁.conj ∈ hyp.Yset := hyp.Yset_closedUnderConjugate hη₁
  have hrealc1 : ¬ ClassFunction.IsReal η₁ :=
    fun hreal => hyp.Yset_hasNoRealCharacters.not_mem_of_isReal hreal hη₁
  have hne : η₁ ≠ η₁.conj := fun heq => hrealc1 heq.symm
  have hee : ClassFunction.inner η₁ η₁.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hη₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁.conj, hη₁irr.conj⟩ : IrreducibleCharacter ↥L)
    rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at h
    simpa using h
  have hval : η₁ (1 : ↥L) = η₁.conj (1 : ↥L) :=
    (hyp.Yset_apply_one hη₁).trans (hyp.Yset_apply_one hconj).symm
  have hsupp : (η₁ - η₁.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₁) (hyp.Yset_subset_S hconj) hval
  have hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hconj) (hyp.Yset_subset_S hη₁)
      hval.symm
  have hXorth := caseB_constituentDecomposition_X_orthogonal hyp h46 hHK θ
    (hcol ⟨θ, hweight⟩) (hirr ⟨θ, hweight⟩) hyp.coherentYset hη₁ hη₁irr hrealc1 hdiffsuppc1 hconj
    (hyp.coherentYset.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) hee hconj hη₁irr.conj hee
    hsupp (hirrAnc ⟨θ, hweight⟩)
  refine ⟨(caseB_phi_family hyp h46 hW2H hφ' hcol hirr ⟨θ, hweight⟩).X,
    constituentWeight hφ' θ, ?_, hanc, hXorth⟩
  rw [ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hyp.Yset_apply_one hη₁,
    constituentWeight_eq_apply_one hW2H hcen hφ' hweight]
  ring

/-- **(6.8.2.3) seam for an irreducible `X`-member** — `⟨χ^{τ₂}, η^{τ₁}⟩ = 0` for an irreducible
`χ ∈ X(W₂)` and `η ∈ Y`.  The case-(B) (mixed-`X`) analogue of the Frobenius
`inner_extension_Xset_centralCommutator_Yset_eq_zero_general`.

The Frobenius proof requires **all** of `X` irreducible; here `X(W₂)` also contains the reducible
certain-type columns, so the all-irreducible source-orthogonality is unavailable.  Instead we take
the distinct reference `χ' = χ̄` (the conjugate: irreducible `hχirr.conj`, in `X(W₂)` `hχconj` since
`X(W₂)` is conjugation-closed, distinct `hχne` as `X(W₂)` has no real characters), and discharge the
source orthogonality `⟨d'•χ − d•χ̄, η − η'⟩ = 0` from the supplied `X(W₂) ⊥ Y` pairing `hpair`
(`inner_eq_zero_of_mem_span_of_pairwise_orthogonal`, needing **no** irreducibility of the columns).
The rest is the (4.1) signed-difference argument
(`pairwise_inner_eq_zero_of_orthogonal_signedDifference`) over the supported degree-`0` differences
`d'•χ − d•χ̄` (`sMember_smulDiffSupport_of_charValue_eq`) and `η − η'` (`sMember_diffSupport`).

Paired with the certain-type column seam `inner_coherent_extension_certainTypeOmegaSigma_eq_zero`,
this is the irreducible half of the case-(B) `X ∪ Y` glue `hmixed`. -/
theorem inner_extension_caseB_Xset_Yset_eq_zero_of_irreducible
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L}
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hpair : ∀ x ∈ hyp.Xset W2, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset W2) (hχirr : IsIrreducibleCharacter χ)
    (hχconj : χ.conj ∈ hyp.Xset W2) (hχne : χ ≠ χ.conj)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (cX.extension χ) (cY.extension η) = 0 := by
  classical
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hχirr⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ.conj, hχirr.conj⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset W2) := Submodule.subset_span hχ
  have hχ's : χ.conj ∈ Submodule.span ℤ (hyp.Xset W2) := Submodule.subset_span hχconj
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ.conj with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ.conj]; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχconj) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  have hXeq : ((d' : ℝ) : ℂ) • cX.extension χ - ((d : ℝ) : ℂ) • cX.extension χ.conj
      = cX.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (cX.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (cX.extension χ.conj)]
    push_cast
    ring
  have hYeq : cY.extension η - cY.extension η' = cY.extension ydiff := by
    rw [hydiff_def, map_sub]
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_pairwise_orthogonal hpair xdiff hx_supp.1 ydiff hy_supp.1
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := cY.extension η) (β := cY.extension η')
    (γ := cX.extension χ) (δ := cX.extension χ.conj)
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (cY.extension_mem_ZIrr η hηs)
    (by rw [cY.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη), if_pos rfl])
    (cY.extension_mem_ZIrr η' hη's)
    (by rw [cY.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        if_pos rfl])
    (cX.extension_mem_ZIrr χ hχs)
    (by rw [cX.extension_inner_eq χ χ hχs hχs, hinner χ χ hχirr hχirr, if_pos rfl])
    (cX.extension_mem_ZIrr χ.conj hχ's)
    (by rw [cX.extension_inner_eq χ.conj χ.conj hχ's hχ's,
        hinner χ.conj χ.conj hχirr.conj hχirr.conj, if_pos rfl])
    (by rw [cY.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        if_neg (fun h => hη'ne h.symm)])
    (by rw [cX.extension_inner_eq χ χ.conj hχs hχ's, hinner χ χ.conj hχirr hχirr.conj, if_neg hχne])
    (by
      rw [hXeq, hYeq, inner_conj_symm (cX.extension xdiff) (cY.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hyp.hconj cX cY hx_supp hy_supp,
        hsrc0, star_zero])
    (by rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj cY hy_supp)
    (by rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj cX hx_supp)
  rw [inner_conj_symm (cY.extension η) (cX.extension χ), hconcl.1, star_zero]

/-- **(6.8.2) case-(B) `X ∪ Y` glue `hmixed`** — the seam orthogonality
`⟨ν x, ν y⟩ = ⟨x, y⟩` of `coherentXunionYset_caseB_of_glued`, reduced to the single `cX`-construction
obligation `hcolAgree` (`cX.extension μ_j = certainTypeExtension μ_j` on the certain-type columns, a
property of the canonical `xChainCoherentW` base).

Since `X(W₂) ⊥ Y` (`caseB_Xset_orthogonal_Yset`) both sides vanish; the image side splits by
`caseB_S_member_column_or_irreducible`:

* reducible certain-type column `x = μ_j`: `⟨cX.extension μ_j, η^{τ₁}⟩ = 0` by `hcolAgree` + the
  column-`Y` seam `inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero`;
* irreducible `x = Ind^L_H θ`: `⟨cX.extension χ, η^{τ₁}⟩ = 0` by the (4.1) seam
  `inner_extension_caseB_Xset_Yset_eq_zero_of_irreducible` (reference `χ̄`).

This is the `hmixed` input of `coherentXunionYset_caseB_of_glued`; only `cX` and `hcolAgree` remain
(supplied by the canonical `xChainCoherentW` `X`-coherence construction). -/
theorem caseB_hmixed
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset h46.W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcolAgree : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      cX.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        = OddOrder.Peterfalvi.S06.certainTypeExtension h46
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)) :
    ∀ x ∈ hyp.Xset h46.W2, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (cX.extension x) (hyp.coherentYset.extension y)
        = ClassFunction.inner x y := by
  have hpair := caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm
  intro x hx y hy
  rw [hpair x hx y hy]
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hx) with
    ⟨χ₂, hχ₂, hcol⟩ | hirr
  · rw [← hcol, hcolAgree χ₂ hχ₂]
    exact inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero hyp h46 hHK hy χ₂
  · have hχconj : x.conj ∈ hyp.Xset h46.W2 :=
      hyp.Xset_closedUnderConjugate_unconditional h46.W2 hx
    have hχne : x ≠ x.conj := fun heq =>
      (Xset_hasNoRealCharacters_caseB hyp h46 hHK).not_mem_of_isReal (heq.symm : x.IsReal) hx
    exact inner_extension_caseB_Xset_Yset_eq_zero_of_irreducible hyp cX hyp.coherentYset hpair
      hx hirr hχconj hχne hy

end OddOrder.Peterfalvi.S08
