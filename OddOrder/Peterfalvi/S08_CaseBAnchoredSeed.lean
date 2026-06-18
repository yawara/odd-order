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

end OddOrder.Peterfalvi.S08
