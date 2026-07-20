/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
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
(6.8.2.3), verified gap analysis): the columns do **not** all lie over a single source character
`φ`;
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

omit [Invertible (Nat.card G : ℂ)] in
omit [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card ↥H : ℂ)] in
omit [Fintype G] in
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
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)] [Finite ↥H]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    (θ : IrreducibleCharacter ↥H) :
    ∃ (φ : ClassFunction ↥W2 ℂ)
      (hφ' : IsIrreducibleCharacter
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ)),
      IsIrreducibleCharacter φ ∧ φ 1 = 1 ∧ 0 < constituentWeight hφ' θ ∧
      ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ)
        = (θ : ClassFunction ↥H ℂ) 1 •
          ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ := by
  haveI : Fintype ↥H := Fintype.ofFinite _
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

omit [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [Invertible (Nat.card ↥H : ℂ)] in
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

/-- **(6.8.2.2) aggregate against an arbitrary `Y`-coherence `cY`** — the `hYcard`-free,
uniform-`cY` form of `exists_decomposition_caseB_coherentYset`.  Given the good anchor multiplicity
`hgood : ⟨(Ind^L_{W₂}φ − |H:W₂|·η₁)^τ, cY.extension η₁⟩ = −|H:W₂|` (supplied uniformly across all
`φ`
by `SibleyDadeHypothesis.exists_Ycoherence_hgood_uniform_caseB`, folding in the `m = 2` relabel),
produces the anchored decomposition against `cY` with `X ⊥ cY.extension(𝒴)` and `X ∈ ZIrr`.
Replaces
the `coeff_eq_neg_or_edge_caseB` + `hYcard` derivation by the `hgood` hypothesis; the rest of the
proof (`orthogonal_tau_indW2_add_extension_general_caseB`, already `cY`-generic) is unchanged.  This
is the bottom of the `hYcard`-free case-(B) `X ∪ Y`-coherence chain. -/
theorem exists_decomposition_caseB_anchorCY
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hW2comm : W2 ≤ ⁅H, H⁆)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hgood : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
        = -((W2.subgroupOf H).index : ℂ)) :
    ∃ X : ClassFunction G ℂ,
      (∀ η ∈ hyp.Yset, ClassFunction.inner X (cY.extension η) = 0)
        ∧ X ∈ ZIrr G
        ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          = X - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ := by
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
  obtain ⟨horth, hXZ⟩ :=
    hyp.orthogonal_tau_indW2_add_extension_general_caseB hW2H hW2comm cY hη₁ φ hφ1 h1 hgood
  refine ⟨hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)
      + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁, horth, hXZ, ?_⟩
  abel

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **(6.8.2.3) certain-type column is nonconstant on `W₂`** (`hWne` provider, the `(R1)` §6 fact).
For a nontrivial column `χ₂ ≠ 1`, the underlying irreducible `θ = Res^H μ_{0,χ₂}` is **not constant
on `W₂.subgroupOf H`** (`∃ w, θ(w) ≠ θ(1)`, i.e. `W₂ ⊄ ker θ`).  This is Peterfalvi (4.7)
`not_subset_characterKernel_chiRestrict_of_ne_one` (`χ_j = Res_K μ_{0j}` has `W₂ ⊄ ker`), repackaged
to the existential form at `H = K` and reduced to the underlying `L`-values of `μ_{0,χ₂}`. -/
theorem caseB_column_W2_nonconstant
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    ∃ w : ↥(h46.W2.subgroupOf H),
      (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) (w : ↥H)
        ≠ (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) 1 := by
  haveI : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  classical
  by_contra hc
  push Not at hc
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
`columnSum χ₂ − a·η₁` to `X − a·η₁^{τ₁}` for some virtual `X` against the **canonical**
`Y`-coherence
`hyp.coherentYset`, with `a = θ(1)` (the constituent weight).

Assembles the per-`θ` central character (`exists_central_phi_data`), the `(6.8.2.2)` aggregate
against `hyp.coherentYset` (`exists_decomposition_caseB_coherentYset`), the column/irreducible
bundles
(`caseB_hcol`/`caseB_hirr`/`caseB_hirrAnc`, with non-linearity `caseB_hnonlin`), and the per-`φ`
anchored producer (`caseB_per_phi_anchored_fromYset`), then rewrites `Ind^L_H θ = columnSum χ₂`
(`columnSum_eq_induce_H`). This is the `(6.8.2.3)` per-column anchored image `hXanchored` (modulo
the
uniform `a₀` and the `Ximg` packaging, handled at the `∀`-column assembly). -/
theorem caseB_column_anchored_image
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
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
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  haveI : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
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
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (_hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (_hp : p.Prime) (_hHp : IsPGroup p ↥H)
    (_hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (_hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (_hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (_hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (θ : IrreducibleCharacter ↥H)
    (hθne : ∃ w : ↥(h46.W2.subgroupOf H),
      (θ : ClassFunction ↥H ℂ) (w : ↥H) ≠ (θ : ClassFunction ↥H ℂ) 1)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    ∃ (X : ClassFunction G ℂ) (a : ℕ),
      ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ) : ClassFunction ↥L ℂ) 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁)
        = X - (a : ℂ) • cY.extension η₁ ∧
      ClassFunction.inner X (cY.extension η₁) = 0 ∧
      X ∈ ZIrr G := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  haveI : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  haveI : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
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
    exists_decomposition_caseB_anchorCY hyp hW2comm cY hη₁
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2) hφ1
      (hcYgood (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2) hφ1 hφneIrr)
  simp only [IrreducibleCharacter.coe_mk] at hdecomp
  have hnonlin := caseB_hnonlin hW2H hderiv hφ' hφne
  have hcol := caseB_hcol hyp h46 hHK hW1 hW2H hcen hφ' hη₁
  have hirr := caseB_hirr hyp h46 hHK hW2H hcen hφ' hη₁ hnonlin
  have hirrAnc := caseB_hirrAnc hyp h46 hHK hW2H hφ' hη₁ hnonlin
  have hanc := caseB_per_phi_anchored_fromYset hyp h46 hHK hW2H hcen hφ' cY hη₁
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
    (hcol ⟨θ, hweight⟩) (hirr ⟨θ, hweight⟩) cY hη₁ hη₁irr hrealc1 hdiffsuppc1 hconj
    (cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) hee hconj hη₁irr.conj hee
    hsupp (hirrAnc ⟨θ, hweight⟩)
  refine ⟨(caseB_phi_family hyp h46 hW2H hφ' hcol hirr ⟨θ, hweight⟩).X,
    constituentWeight hφ' θ, ?_, hanc, hXorth,
    characterPsiDecomposition_X_mem_ZIrr _⟩
  rw [ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hyp.Yset_apply_one hη₁,
    constituentWeight_eq_apply_one hW2H hcen hφ' hweight]
  ring

/-- **(6.8.2.3) anchored image ⊥ the whole `Y`-image.**  The per-column anchored `X` (from the
anchored image `τ(μ − a₀·η₁) = X − a₀·ν₁`, `hanc`, where `μ = columnSum χ₂`, `ν₁ = η₁^{τ₁}`) is
orthogonal to `cY.extension y` for **every** `y ∈ Y`, not only the anchor `η₁`.

Writing `⟨X, ν_y⟩ = ⟨X, ν_y − ν₁⟩ + ⟨X, ν₁⟩`, the anchor term is `hmix = 0` and the difference term
`⟨X, cY.ext(y − η₁)⟩ = ⟨X, τ(y − η₁)⟩` (`cY` extends `τ` on the `H^#`-supported `y − η₁`) vanishes
by
the Dade isometry of `τ` and the `Y`-isometry of `cY`: with `X = τ(μ − a₀η₁) + a₀·ν₁`,
`⟨X, τ(y − η₁)⟩ = ⟨μ − a₀η₁, y − η₁⟩ + a₀·⟨η₁, y − η₁⟩ = a₀(1 − c) + a₀(c − 1) = 0`
(`c = ⟨η₁, y⟩`, the columns being orthogonal to `Y`).  This is the uniform `hXmixed` content for the
case-(B) `certainTypeSet ∪ Y` coherence (Peterfalvi (6.8.2.3) "`X₁ ⊥ Y^{τ₁}`"). -/
theorem caseB_anchoredImage_seam_all_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) {a₀ : ℕ}
    {X : ClassFunction G ℂ}
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hanc : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
      = X - a₀ • cY.extension η₁)
    (hmix : ClassFunction.inner X (cY.extension η₁) = 0)
    (hsupp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    {y : ClassFunction ↥L ℂ} (hy : y ∈ hyp.Yset) :
    ClassFunction.inner X (cY.extension y) = 0 := by
  classical
  -- `y − η₁` is `H^#`-supported (equal degree `|W₁|`) and lies in the `Y`-span.
  have hydeg : y (1 : ↥L) = η₁ (1 : ↥L) :=
    (hyp.Yset_apply_one hy).trans (hyp.Yset_apply_one hη₁).symm
  have hysupp : (y - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hy) (hyp.Yset_subset_S hη₁) hydeg
  have hymemZ : y - η₁ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥L) hyp.Yset :=
    Submodule.sub_mem _ (Submodule.subset_span hy) (Submodule.subset_span hη₁)
  have hη₁memZ : η₁ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥L) hyp.Yset :=
    Submodule.subset_span hη₁
  -- `cY` extends `τ` on the supported `y − η₁`.
  have hcYext : cY.extension (y - η₁) = hyp.tau (y - η₁) :=
    cY.extends_on_supported (y - η₁) ⟨hymemZ, hysupp⟩
  -- `X = τ(μ − a₀η₁) + a₀·ν₁`.
  have hX : X = hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
      + (a₀ : ℂ) • cY.extension η₁ := by
    rw [hanc, ← Nat.cast_smul_eq_nsmul ℂ a₀ (cY.extension η₁)]; abel
  -- split `⟨X, ν_y⟩ = ⟨X, cY(y − η₁)⟩ + ⟨X, ν₁⟩` and discharge the anchor term by `hmix`.
  have hsplit : ClassFunction.inner X (cY.extension y)
      = ClassFunction.inner X (cY.extension (y - η₁))
        + ClassFunction.inner X (cY.extension η₁) := by
    rw [map_sub, ClassFunction.inner_sub_right]; ring
  rw [hsplit, hmix, add_zero, hcYext]
  -- the Dade isometry of `τ` on the supported pair `{μ − a₀η₁, y − η₁}`.
  have hiso : ClassFunction.inner
        (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)) (hyp.tau (y - η₁))
      = ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁) (y - η₁) :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade hyp.hconj
      (S := ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁, y - η₁}
        : Set (ClassFunction ↥L ℂ)))
      (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl; exacts [hsupp, hysupp])
      (Submodule.subset_span (Set.mem_insert _ _))
      (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  -- the `Y`-isometry of `cY`: `⟨ν₁, τ(y − η₁)⟩ = ⟨η₁, y − η₁⟩`.
  have hcYiso : ClassFunction.inner (cY.extension η₁) (hyp.tau (y - η₁))
      = ClassFunction.inner η₁ (y - η₁) := by
    rw [← hcYext, cY.extension_inner_eq η₁ (y - η₁) hη₁memZ hymemZ]
  -- the columns are orthogonal to `Y`.
  have hμy : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) y = 0 :=
    inner_columnSum_Yset_eq_zero hyp h46 hW1 hy χ₂
  have hμη : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) η₁ = 0 :=
    inner_columnSum_Yset_eq_zero hyp h46 hW1 hη₁ χ₂
  have hηirr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηη : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  -- assemble: the `c = ⟨η₁, y⟩` terms cancel.
  rw [hX, ClassFunction.inner_add_left, hiso, ClassFunction.inner_smul_left, hcYiso]
  simp only [← Nat.cast_smul_eq_nsmul ℂ a₀ η₁, ClassFunction.inner_sub_left,
    ClassFunction.inner_sub_right, ClassFunction.inner_smul_left, hμy, hμη, hηη]
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
`⟨ν x, ν y⟩ = ⟨x, y⟩` of `coherentXunionYset_caseB_of_glued`, reduced to the single
`cX`-construction
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

/-- **(6.8.2.3) per-column anchored image — full bundle.**  For a nontrivial certain-type column
`χ₂ ≠ 1`, packages every datum the case-(B) `certainTypeSet ∪ Y` coherence needs: the degree
`columnSum χ₂(1) = a·η₁(1)`, the anchored image `τ(columnSum χ₂ − a·η₁) = X − a·ν₁`, the anchor
seam `⟨X, ν₁⟩ = 0`, `X ∈ ZIrr`, and the `H^#`-support of the anchored difference.

Extracts `θ = Res^H μ_{0,χ₂}` (irreducible by `certainTypeRestrict_isIrreducible`, nonconstant on
`W₂` by `caseB_column_W2_nonconstant`), feeds it to `caseB_member_anchored_image`, transports
`Ind^L_H θ = columnSum χ₂` (`columnSum_eq_induce_H`), and derives the support from the equal-degree
`sMember_smulDiffSupport_of_charValue_eq`. -/
theorem caseB_column_anchored_full
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
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
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    ∃ (X : ClassFunction G ℂ) (a : ℕ),
      ((OddOrder.Peterfalvi.S06.columnSum h46 χ₂ : ClassFunction ↥L ℂ) 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁)
        = X - (a : ℂ) • cY.extension η₁ ∧
      ClassFunction.inner X (cY.extension η₁) = 0 ∧
      X ∈ ZIrr G ∧
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  haveI : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
  have hWne := caseB_column_W2_nonconstant h46 hHK hχ₂
  have hθirr : IsIrreducibleCharacter
      (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) := by
    have h := h46.certainTypeRestrict_isIrreducible χ₂; rwa [hHK] at h
  set θ : IrreducibleCharacter ↥H :=
    ⟨ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ), hθirr⟩ with hθdef
  have hθval : (θ : ClassFunction ↥H ℂ)
      = ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) := by rw [hθdef]
  have hθne : ∃ w : ↥(h46.W2.subgroupOf H),
      (θ : ClassFunction ↥H ℂ) (w : ↥H) ≠ (θ : ClassFunction ↥H ℂ) 1 := by rw [hθval]; exact hWne
  obtain ⟨X, a, hdeg, hanc, hmix, hXZ⟩ :=
    caseB_member_anchored_image hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
      hW2cenL hc2 hFPF hη₁ θ hθne cY hcYgood
  have hcsum : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ := by
    rw [hθval]; exact (columnSum_eq_induce_H h46 hHK χ₂).symm
  rw [hcsum] at hdeg hanc
  have hsupp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    have h := hyp.sMember_smulDiffSupport_of_charValue_eq
      (hyp.columnSum_mem_S h46 hHK hχ₂) (hyp.Yset_subset_S hη₁)
      (m := 1) (n := a) (by rw [Nat.cast_one, one_mul]; exact hdeg)
    rwa [one_smul] at h
  exact ⟨X, a, hdeg, hanc, hmix, hXZ, hsupp⟩

/-- **Peterfalvi (6.8.2) — case-(B) `certainTypeSet ∪ Y` coherence (unconditional base).**

The viable-route base (roadmap cont.¹⁰): under the case-(B) structural hypotheses, `hyp.tau` is
coherent on `certainTypeSet h46 k ∪ Yset` — the seed onto which the irreducible-`X` weighted chain
(`xChainCoherentW`, `Y`-anchored, `‖η‖² = 1`) is folded to build `IsCoherent (Xset W₂ ∪ Y)`.

All anchored-image obligations of `coherentCertainTypeSet_union_Yset_via_anchoredImages` are
discharged from the per-column full bundle `caseB_column_anchored_full`:
* `Ximg χ₂ := τ(columnSum χ₂ − a₀·η₁) + a₀·ν₁` on the certain-type columns (`0` elsewhere), so the
  gated `hXanchored` is the rearranged anchored image;
* `hXinner` from `xchi_inner_eq_of_anchored` (per-member, supports from the bundle);
* `hXzirr` from the bundle (`0 ∈ ZIrr` off the columns);
* `hXmixed` from `caseB_anchoredImage_seam_all_Yset` (the `X ⊥ Y^{τ₁}` content, all of `Y`).
The uniform anchor weight `a₀` is the reference column `k`'s weight; the equal degree built into
`certainTypeSet` membership (`columnSum_apply_one`) forces every column's weight to `a₀`. -/
noncomputable def coherentCertainTypeSet_union_Yset_caseB
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
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- the reference column `k` and its anchor weight `a₀` (data — extracted via `Exists.choose`, not
  -- `obtain`, since the goal `IsCoherent` lives in `Type`).
  have hkfull := caseB_column_anchored_full hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime
    hW2comm hW2cenL hc2 hFPF hη₁ hk cY hcYgood
  set a₀ : ℕ := hkfull.choose_spec.choose with ha₀def
  have hdegk : (OddOrder.Peterfalvi.S06.columnSum h46 k) 1 = (a₀ : ℂ) * η₁ 1 :=
    hkfull.choose_spec.choose_spec.1
  have hk0mem : OddOrder.Peterfalvi.S06.columnSum h46 k
      ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k := ⟨k, hk, rfl, rfl⟩
  -- `η₁(1) ≠ 0` (irreducible degree).
  have hηirr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hη0 : η₁ (1 : ↥L) ≠ 0 := by
    obtain ⟨dη, hdη_pos, hdη_eq⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hdη_eq
    rw [hdη_eq]; exact_mod_cast hdη_pos.ne'
  -- the textbook image `Ximg` (rearranged anchored image on columns, `0` elsewhere).
  set Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ :=
    fun χ₂ => if OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k
      then hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
        + a₀ • cY.extension η₁
      else 0 with hXimg
  -- per-member data, with the weight forced to the uniform `a₀`.
  have key : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k →
      (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
          = Ximg χ₂ - a₀ • cY.extension η₁) ∧
        ClassFunction.inner (Ximg χ₂) (cY.extension η₁) = 0 ∧
        Ximg χ₂ ∈ ZIrr G ∧
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro χ₂ hmem
    obtain ⟨χ₂', hne', hdegm', hcseq⟩ := hmem
    obtain ⟨X', a', hdeg', hanc', hmix', hXZ', hsupp'⟩ :=
      caseB_column_anchored_full hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
        hW2cenL hc2 hFPF hη₁ hne' cY hcYgood
    -- the weight is uniform: `a' = a₀`.
    have hcs1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂') 1
        = (OddOrder.Peterfalvi.S06.columnSum h46 k) 1 := by
      rw [OddOrder.Peterfalvi.S06.columnSum_apply_one,
        OddOrder.Peterfalvi.S06.columnSum_apply_one]; exact hdegm'
    have ha' : a' = a₀ := by
      have h1 : (a' : ℂ) * η₁ 1 = (a₀ : ℂ) * η₁ 1 := by rw [← hdeg', hcs1, hdegk]
      exact_mod_cast mul_right_cancel₀ hη0 h1
    subst ha'
    rw [← hcseq] at hanc' hsupp'
    -- align the smul convention: the bundle uses `(a₀ : ℂ) •`, the union lemma uses `a₀ •` (`ℕ`).
    rw [Nat.cast_smul_eq_nsmul ℂ a₀ (cY.extension η₁)] at hanc'
    have hmem2 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k := ⟨χ₂', hne', hdegm', hcseq⟩
    have hXimgeq : Ximg χ₂ = X' := by
      simp only [hXimg, if_pos hmem2]; rw [hanc']; abel
    exact ⟨by rw [hXimgeq]; exact hanc', by rw [hXimgeq]; exact hmix',
      by rw [hXimgeq]; exact hXZ', hsupp'⟩
  refine coherentCertainTypeSet_union_Yset_via_anchoredImages hyp h46 hHK hW1 cY hk hη₁
    hk0mem hdegk Ximg (fun χ₂ hmem => (key χ₂ hmem).1) (fun χ₂ χ₂' hmem hmem' => ?_)
    (fun χ₂ => ?_) (fun χ₂ y hy => ?_)
  · -- `hXinner` (gated to members).
    exact xchi_inner_eq_of_anchored hyp h46 hW1 cY hη₁ (key χ₂ hmem).1 (key χ₂' hmem').1
      (key χ₂ hmem).2.1 (key χ₂' hmem').2.1 (key χ₂ hmem).2.2.2 (key χ₂' hmem').2.2.2
  · -- `hXzirr` (ungated; `0 ∈ ZIrr` off the columns).
    by_cases hmem : OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k
    · exact (key χ₂ hmem).2.2.1
    · rw [hXimg]; simp only [if_neg hmem]; exact Submodule.zero_mem _
  · -- `hXmixed` (ungated; `⟨0, ·⟩ = 0` off the columns, seam-for-all-`y` on the columns).
    by_cases hmem : OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k
    · exact caseB_anchoredImage_seam_all_Yset hyp h46 hW1 cY hη₁ (key χ₂ hmem).1
        (key χ₂ hmem).2.1 (key χ₂ hmem).2.2.2 hy
    · rw [hXimg]; simp only [if_neg hmem]; rw [ClassFunction.inner_zero_left]

/-- **(6.8.2.3) per-member anchored image for an arbitrary `X`-member.**  Generalizes
`caseB_column_anchored_full` from a certain-type column to **any** `χ ∈ Xset W₂` (reducible column
or
irreducible).  Every such `χ = Ind^L_H θ` with `W₂ ⊄ Ker θ` (from `S_eq` and `χ ∉ S(W₂)`: had
`W₂ ⊆ Ker θ` then `χ ∈ S(W₂)`), so `caseB_member_anchored_image` supplies the (6.8.2.3) anchored
image with `a = χ(1)/|W₁| = θ(1)`.

This is the uniform (6.8.2.3) datum for the **whole** of `X` — the per-member input to the case-(B)
`Xset W₂ ∪ Y` coherence seed (Peterfalvi (6.8.2), built via the anchored-image isometry `τ₂`, *not*
the `(6.6)` chain — see roadmap cont.¹²). -/
theorem caseB_Xset_member_anchored
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
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
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset h46.W2)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    ∃ (X : ClassFunction G ℂ) (a : ℕ),
      ((χ : ClassFunction ↥L ℂ) 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (χ - a • η₁) = X - (a : ℂ) • cY.extension η₁ ∧
      ClassFunction.inner X (cY.extension η₁) = 0 ∧
      X ∈ ZIrr G ∧
      (χ - a • η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  haveI : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  haveI : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
  obtain ⟨hχS, hχnotsub⟩ := hyp.mem_Xset.mp hχ
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, hθne1, hχeq⟩ := hχS
  have hθne : ∃ w : ↥(h46.W2.subgroupOf H),
      (θ : ClassFunction ↥H ℂ) (w : ↥H) ≠ (θ : ClassFunction ↥H ℂ) 1 := by
    by_contra hc
    push Not at hc
    exact hχnotsub (hyp.mem_SsubFiltration.mpr ⟨θ, hθne1, fun g hg => by
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel]; exact hc ⟨g, hg⟩, hχeq⟩)
  obtain ⟨X, a, hdeg, hanc, hmix, hXZ⟩ :=
    caseB_member_anchored_image hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
      hW2cenL hc2 hFPF hη₁ θ hθne cY hcYgood
  subst hχeq
  have hsupp : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    have h := hyp.sMember_smulDiffSupport_of_charValue_eq
      (hyp.Xset_subset_S hχ) (hyp.Yset_subset_S hη₁) (m := 1) (n := a)
      (by rw [Nat.cast_one, one_mul]; exact hdeg)
    rwa [one_smul] at h
  exact ⟨X, a, hdeg, hanc, hmix, hXZ, hsupp⟩

/-- **(6.8.2) cross-member isometry, varying degree.**  Generalizes `xchi_inner_eq_of_anchored`
from a single uniform anchor weight `a₀` (equal-degree columns) to **per-member** weights `aᵢ, aⱼ`
(arbitrary `X`-members of differing degree).  From the anchored images `τ(χᵢ − aᵢη₁) = Xᵢ − aᵢν₁`
(`hancᵢ`), the seams `⟨Xᵢ, ν₁⟩ = 0` (`hmixᵢ`), the source orthogonalities `⟨χᵢ, η₁⟩ = 0`
(`horthᵢ`, the `X ⊥ Y` pairing), the Dade isometry of `τ` on the `H^#`-supported anchored
differences, and `‖η₁‖² = ‖ν₁‖² = 1`:
`⟨Xᵢ, Xⱼ⟩ = (⟨χᵢ,χⱼ⟩ + aᵢaⱼ) − aᵢaⱼ − aᵢaⱼ + aᵢaⱼ = ⟨χᵢ, χⱼ⟩`.

This is the `hXinner` content for the **full** `Xset W₂` coherence (varying-degree generalization of
the certain-type `hXinner`). -/
theorem inner_eq_of_anchored_varying
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χi χj : ClassFunction ↥L ℂ} {ai aj : ℕ} {Xi Xj : ClassFunction G ℂ}
    (hanci : hyp.tau (χi - ai • η₁) = Xi - (ai : ℂ) • cY.extension η₁)
    (hancj : hyp.tau (χj - aj • η₁) = Xj - (aj : ℂ) • cY.extension η₁)
    (hmixi : ClassFunction.inner Xi (cY.extension η₁) = 0)
    (hmixj : ClassFunction.inner Xj (cY.extension η₁) = 0)
    (horthi : ClassFunction.inner χi η₁ = 0) (horthj : ClassFunction.inner χj η₁ = 0)
    (hsuppi : (χi - ai • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hsuppj : (χj - aj • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ClassFunction.inner Xi Xj = ClassFunction.inner χi χj := by
  classical
  set ν := cY.extension η₁ with hνdef
  have hXi : Xi = hyp.tau (χi - ai • η₁) + (ai : ℂ) • ν := by
    rw [hanci]; abel
  have hXj : Xj = hyp.tau (χj - aj • η₁) + (aj : ℂ) • ν := by
    rw [hancj]; abel
  have hηirr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηη : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hνν : ClassFunction.inner ν ν = 1 := by
    rw [hνdef, cY.extension_inner_eq η₁ η₁ (Submodule.subset_span hη₁)
      (Submodule.subset_span hη₁), hηη]
  -- `⟨τ(χᵢ−aᵢη₁), τ(χⱼ−aⱼη₁)⟩ = ⟨χᵢ,χⱼ⟩ + aᵢaⱼ` (Dade isometry on the supported pair).
  have hττ : ClassFunction.inner (hyp.tau (χi - ai • η₁)) (hyp.tau (χj - aj • η₁))
      = ClassFunction.inner χi χj + (ai : ℂ) * (aj : ℂ) := by
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade
        hyp.hconj (S := ({χi - ai • η₁, χj - aj • η₁} : Set (ClassFunction ↥L ℂ)))
        (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl; exacts [hsuppi, hsuppj])
        (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))]
    have hηj : ClassFunction.inner η₁ χj = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, horthj, star_zero]
    simp only [← Nat.cast_smul_eq_nsmul ℂ ai η₁, ← Nat.cast_smul_eq_nsmul ℂ aj η₁,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast, horthi, hηj, hηη]
    ring
  -- the cross terms with `ν`.
  have hτiν : ClassFunction.inner (hyp.tau (χi - ai • η₁)) ν = -(ai : ℂ) := by
    rw [hanci]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
    rw [hmixi, hνν]; ring
  have hτjν : ClassFunction.inner (hyp.tau (χj - aj • η₁)) ν = -(aj : ℂ) := by
    rw [hancj]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
    rw [hmixj, hνν]; ring
  have hντj : ClassFunction.inner ν (hyp.tau (χj - aj • η₁)) = -(aj : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hτjν, star_neg, star_natCast]
  rw [hXi, hXj]
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hττ, hτiν, hντj, hνν]; ring

/-- **(6.8.2) scaled-difference identity** (the `extends_on_supported` content for the full
`Xset W₂` coherence).  From two anchored images `τ(χᵢ − aᵢη₁) = Xᵢ − aᵢν₁`, `τ(χ₁ − a₁η₁) =
X₁ − a₁ν₁` with the **degree ratio** `aᵢ = dᵢ·a₁` (i.e. `χᵢ(1) = dᵢ·χ₁(1)`, integral since `H` is a
`p`-group), the `ν₁`-terms cancel and `τ` is linear, so the scaled difference maps homogeneously:
`Xᵢ − dᵢ·X₁ = τ(χᵢ − dᵢ·χ₁)`.

This is the textbook fact that on the supported generators `χᵢ − dᵢχ₁` the running extension
`τ₂` agrees with `τ` (the `(6.8.2)` `τ₂` defined via the anchored images), generalizing the
equal-degree column-difference identity to varying degree (cf. `span_subset_span_
zSupportedSpan_union_anchor_of_scaledDiffs`, the matching generation). -/
theorem anchoredImage_scaledDiff_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ}
    {χi χ1 : ClassFunction ↥L ℂ} {ai a1 di : ℕ} {Xi X1 : ClassFunction G ℂ}
    (hanci : hyp.tau (χi - ai • η₁) = Xi - (ai : ℂ) • cY.extension η₁)
    (hanc1 : hyp.tau (χ1 - a1 • η₁) = X1 - (a1 : ℂ) • cY.extension η₁)
    (hai : ai = di * a1) :
    Xi - di • X1 = hyp.tau (χi - di • χ1) := by
  have hχ : χi - di • χ1 = (χi - ai • η₁) - di • (χ1 - a1 • η₁) := by
    rw [smul_sub, ← mul_smul, ← hai]; abel
  have hνcancel : di • ((a1 : ℂ) • cY.extension η₁)
      = (ai : ℂ) • cY.extension η₁ := by
    rw [← Nat.cast_smul_eq_nsmul ℂ di ((a1 : ℂ) • cY.extension η₁), smul_smul,
      ← Nat.cast_mul, ← hai]
  rw [hχ, map_sub, map_nsmul, hanci, hanc1, smul_sub, hνcancel]; abel

/-- **(6.8.2) grid constituents are not `X`-members** — `μ_{iχ₂} ∉ Xset W₂`.  A certain-type grid
character has degree `≡ ±1 (mod |W₁|)` (`certainType_degree_modEq`, the sign `= ±1`), whereas every
`X`-member `Ind^L_H θ` has degree `|W₁|·θ(1) ≡ 0 (mod |W₁|)`; with `|W₁| ≠ 1` these are
incompatible.

This is the disjointness underlying the **dichotomy extension** for the full `Xset W₂` coherence: on
the basis `Irr L`, the irreducible `X`-members `χ ↦ Ximg χ` and the column grid members
`μ_{iχ₂} ↦ (column image, concentrated on `i = 0`)` never collide, so the extension is well-defined
and sends each column `columnSum χ₂ = ∑_i μ_{iχ₂}` to its image. -/
theorem grid_mu_notMem_Xset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Finite ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) ∉ hyp.Xset h46.W2 := by
  haveI : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  intro hmem
  have hS := hyp.Xset_subset_S hmem
  rw [hyp.S_eq, Set.mem_setOf_eq] at hS
  obtain ⟨θ, -, hμeq⟩ := hS
  obtain ⟨a, ha⟩ := h46.certainType_degree_modEq χ₂ i
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hindeg : ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
      = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
    rw [hμeq, ClassFunction.induce_apply_one, hd, hyp.index_H_eq_card_W1]
  rw [hindeg] at ha
  have hcard : (Nat.card h46.W1 : ℂ) = (Nat.card hyp.W1 : ℂ) := by rw [hW1]
  rw [hcard] at ha
  have hw1 : Nat.card hyp.W1 ≠ 1 := fun h => hyp.W1_nontrivial (Subgroup.card_eq_one.mp h)
  have hsignZ : (h46.columnFamily χ₂).sign = (Nat.card hyp.W1 : ℤ) * ((d : ℤ) - a) := by
    have hsign : ((h46.columnFamily χ₂).sign : ℂ)
        = (Nat.card hyp.W1 : ℂ) * ((d : ℂ) - (a : ℂ)) := by linear_combination -ha
    exact_mod_cast hsign
  have hdvd1 : (Nat.card hyp.W1 : ℤ) ∣ 1 := by
    have hdvd : (Nat.card hyp.W1 : ℤ) ∣ (h46.columnFamily χ₂).sign := ⟨(d : ℤ) - a, hsignZ⟩
    rcases (h46.columnFamily χ₂).sign_eq with hs | hs
    · rwa [hs] at hdvd
    · rw [hs] at hdvd; exact (dvd_neg).mp hdvd
  exact hw1 (Nat.dvd_one.mp (by exact_mod_cast hdvd1))

/-- **(6.8.2) the dichotomy extension function** for the full `Xset W₂` coherence.  On the basis
`Irr L`: an irreducible `X`-member `ω ∈ Xset W₂` maps to its anchored image `Ximg ω`; everything
else falls back to the column extension `xChiExtensionFun` (which sends a grid `0`-row member
`μ_{0χ₂}` to `Ximg (columnSum χ₂)`, other grid members to `0`).  By `grid_mu_notMem_Xset` the two
branches never collide on the grid, so each column `columnSum χ₂` maps to `Ximg (columnSum χ₂)`. -/
noncomputable def caseBXsetExtensionFun
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ) :
    IrreducibleCharacter ↥L → ClassFunction G ℂ :=
  fun ω => if (ω : ClassFunction ↥L ℂ) ∈ hyp.Xset h46.W2 then Ximg (ω : ClassFunction ↥L ℂ)
    else xChiExtensionFun h46 (fun χ₂ => Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)) ω

/-- The dichotomy extension `ν` (the case-(B) `τ₂` on the full `X`-set): the global `ℤ`-linear
`CF(L) → CF(G)` built from `caseBXsetExtensionFun` on the basis `Irr L`. -/
noncomputable def caseBXsetExtension
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G :=
  ((OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr ℂ
    (caseBXsetExtensionFun hyp h46 Ximg)).restrictScalars ℤ

/-- On a grid member `μ_{iχ₂}` (not an `X`-member, `grid_mu_notMem_Xset`) the dichotomy extension
agrees with the column extension `xChiExtension`. -/
theorem caseBXsetExtension_grid
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    caseBXsetExtension hyp h46 Ximg ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = xChiExtension h46 (fun χ₂ => Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂))
          ((h46.columnFamily χ₂).mu i) := by
  classical
  rw [caseBXsetExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu i)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu i), caseBXsetExtensionFun,
    if_neg (grid_mu_notMem_Xset hyp h46 hW1 χ₂ i),
    xChiExtension, LinearMap.restrictScalars_apply]
  conv_rhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu i)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu i)]

/-- On a certain-type column `columnSum χ₂` the dichotomy extension sends it to
`Ximg (columnSum χ₂)`:
every grid member maps via the column extension (`caseBXsetExtension_grid`), and only the `0`-row
survives (`xChiExtension_columnSum`). -/
theorem caseBXsetExtension_columnSum
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    caseBXsetExtension hyp h46 Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      = Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) := by
  classical
  rw [OddOrder.Peterfalvi.S06.columnSum_def, map_sum,
    Finset.sum_congr rfl (fun i _ => caseBXsetExtension_grid hyp h46 hW1 Ximg χ₂ i),
    ← map_sum, ← OddOrder.Peterfalvi.S06.columnSum_def, xChiExtension_columnSum]

/-- On an irreducible `X`-member `χ ∈ Xset W₂` the dichotomy extension sends it to `Ximg χ`
(the `ω ∈ Xset W₂` branch on the basis element `χ`). -/
theorem caseBXsetExtension_irr
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    {χ : ClassFunction ↥L ℂ} (hirr : IsIrreducibleCharacter χ)
    (hmem : χ ∈ hyp.Xset h46.W2) :
    caseBXsetExtension hyp h46 Ximg χ = Ximg χ := by
  classical
  have hcoe : ((⟨χ, hirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ := rfl
  rw [caseBXsetExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← hcoe, ← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    (⟨χ, hirr⟩ : IrreducibleCharacter ↥L), caseBXsetExtensionFun, hcoe, if_pos hmem]

/-- **The dichotomy extension realizes the anchored images on the whole `X`-set**: `ν χ = Ximg χ`
for every `χ ∈ Xset W₂` (column or irreducible, via `caseB_S_member_column_or_irreducible`). -/
theorem caseBXsetExtension_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    {χ : ClassFunction ↥L ℂ} (hmem : χ ∈ hyp.Xset h46.W2) :
    caseBXsetExtension hyp h46 Ximg χ = Ximg χ := by
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hmem) with
    ⟨χ₂, -, hcol⟩ | hirr
  · rw [← hcol, caseBXsetExtension_columnSum hyp h46 hW1 Ximg χ₂]
  · exact caseBXsetExtension_irr hyp h46 Ximg hirr hmem

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] in
/-- **(6.8.2) supported generation by scaled differences** (the varying-degree analogue of
`mem_span_columnDiff_of_mem_zSupportedSpan`).  Given an anchor `χ₁ ∈ S₁` (with `χ₁(1) ≠ 0`) such
that
every `f ∈ S₁` has degree `f(1) = d·χ₁(1)` for some `d : ℕ` (the integral degree ratio, available
for
`X`-members since `H` is a `p`-group), every supported (degree-`0`) `φ ∈ Z[S₁, A₀]` lies in the span
of the scaled differences `f − d·χ₁`.

The support set is arbitrary subject to `1 ∉ A₀` — that is the only thing the argument uses of it
(it forces `φ(1) = 0`).  Stating it that way lets the same lemma serve the §9 route, where `A₀` is
`A(M) ∪ V^M` rather than `H^#`.

Proof mirrors the equal-degree case: the scaled differences vanish at `1` (`f(1) − d·χ₁(1) = 0`), so
`D = span{f − d·χ₁}` sits inside `ker(ev₁)`; `Z[S₁] ≤ D ⊔ ℤ·χ₁` (write `f = (f − d·χ₁) + d·χ₁`); and
a
supported `φ = y + n·χ₁` has `0 = φ(1) = n·χ₁(1)`, forcing `n = 0`, so `φ = y ∈ D`. -/
theorem mem_span_scaledDiff_of_mem_zSupportedSpan
    {A0 : Set ↥L} (h1A0 : (1 : ↥L) ∉ A0)
    {S₁ : Set (ClassFunction ↥L ℂ)} {χ₁ : ClassFunction ↥L ℂ}
    (hχ₁1 : (χ₁ : ClassFunction ↥L ℂ) 1 ≠ 0)
    (hdeg : ∀ f ∈ S₁, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan S₁ A0) :
    φ ∈ Submodule.span ℤ
      {g : ClassFunction ↥L ℂ | ∃ f ∈ S₁, ∃ d : ℕ,
        (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1 ∧ g = f - d • χ₁} := by
  classical
  obtain ⟨hφspan, hφsupp⟩ := hφ
  set T : Set (ClassFunction ↥L ℂ) := {g | ∃ f ∈ S₁, ∃ d : ℕ,
    (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1 ∧ g = f - d • χ₁} with hT
  set ev1 : ClassFunction ↥L ℂ →+ ℂ := AddMonoidHom.mk' (fun ψ => ψ (1 : ↥L)) (fun _ _ => rfl)
    with hev1
  have hD_vanish : ∀ δ ∈ Submodule.span ℤ T, ev1 δ = 0 := by
    intro δ hδ
    induction hδ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, _, d, hfd, rfl⟩ := hx
        change (f - d • χ₁) (1 : ↥L) = 0
        rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ d χ₁, ClassFunction.smul_apply,
          hfd, sub_self]
    | zero => exact map_zero ev1
    | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul a x _ ih => rw [map_zsmul, ih, smul_zero]
  have hspan_le : Submodule.span ℤ S₁ ≤ Submodule.span ℤ T ⊔ Submodule.span ℤ {χ₁} := by
    rw [Submodule.span_le]
    intro f hf
    obtain ⟨d, hfd⟩ := hdeg f hf
    rw [show f = (f - d • χ₁) + d • χ₁ from by abel]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨f, hf, d, hfd, rfl⟩))
      (Submodule.mem_sup_right ?_)
    rw [← Nat.cast_smul_eq_nsmul ℤ d χ₁]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hspan_le hφspan)
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hφ1 : ev1 φ = 0 := by
    change φ (1 : ↥L) = 0
    by_contra hne
    exact h1A0 (hφsupp (ClassFunction.mem_support.mpr hne))
  rw [← hyz, map_add, hD_vanish y hy, zero_add, map_zsmul] at hφ1
  have hn : n = 0 := by
    rcases smul_eq_zero.mp hφ1 with hn | hd
    · exact hn
    · exact absurd hd (show ev1 χ₁ ≠ 0 from hχ₁1)
  rw [← hyz, hn, zero_smul, add_zero]; exact hy

/-- **The case-(B) anchored-image function** `Ximg : CF(L) → CF(G)` on the `X`-set: each
`χ ∈ Xset W₂` maps to the `(6.8.2.3)` virtual character `X` (`caseB_Xset_member_anchored`, chosen),
elsewhere `0`. -/
noncomputable def caseBXimg
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    ClassFunction ↥L ℂ → ClassFunction G ℂ :=
  fun χ => if hχ : χ ∈ hyp.Xset h46.W2 then
    (caseB_Xset_member_anchored hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
      hW2cenL hc2 hFPF hη₁ hχ cY hcYgood).choose
  else 0

/-- The defining property of `caseBXimg` on an `X`-member: the `(6.8.2.3)` anchored image, seam,
`ZIrr`-membership and support, with the chosen weight `a`. -/
theorem caseBXimg_spec
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset h46.W2) :
    ∃ a : ℕ, (χ 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (χ - a • η₁) = caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
          hW2cenL hc2 hFPF hη₁ cY hcYgood χ - (a : ℂ) • cY.extension η₁ ∧
      ClassFunction.inner (caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
          hW2cenL hc2 hFPF hη₁ cY hcYgood χ) (cY.extension η₁) = 0 ∧
      caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF hη₁
          cY hcYgood χ ∈ ZIrr G ∧
      (χ - a • η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  have : caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF hη₁
      cY hcYgood χ = (caseB_Xset_member_anchored hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime
        hW2comm hW2cenL hc2 hFPF hη₁ hχ cY hcYgood).choose := by
    rw [caseBXimg, dif_pos hχ]
  rw [this]
  exact (caseB_Xset_member_anchored hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
    hW2cenL hc2 hFPF hη₁ hχ cY hcYgood).choose_spec

/-- **Peterfalvi (6.8.2) — case-(B) `X`-coherence via anchored images** (the full `Xset W₂`, varying
degree).  Given the case-(B) structural data, a degree anchor `χ₁ ∈ Xset W₂` with `χ₁(1) ≠ 0` whose
degree divides every `X`-member's (`hdvd`, integral since `H` is a `p`-group), and a nonzero
supported witness, `hyp.tau` is coherent on `Xset W₂` with extension the dichotomy map
`caseBXsetExtension` (sending each `χ` to its `(6.8.2.3)` anchored image `Ximg χ`).

The three coherence conditions are exactly the building blocks: the isometry is
`inner_eq_of_anchored_varying` (per member, varying degree), the supported `τ`-agreement is
`anchoredImage_scaledDiff_eq` over the scaled-difference generators
(`mem_span_scaledDiff_of_mem_zSupportedSpan`), and the `ZIrr`-codomain is the per-member bundle. -/
noncomputable def caseBXset_isCoherent
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ))
    (hη₁1 : η₁ (1 : ↥L) ≠ 0)
    {χ₁ : ClassFunction ↥L ℂ} (hanchor : χ₁ ∈ hyp.Xset h46.W2) (hχ₁1 : χ₁ (1 : ↥L) ≠ 0)
    (hdvd : ∀ f ∈ hyp.Xset h46.W2, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    (hnonzero : ∃ φ : ClassFunction ↥L ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset h46.W2) (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset h46.W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) where
  nonzero := hnonzero
  extension := caseBXsetExtension hyp h46
    (caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
      hη₁ cY hcYgood)
  extension_inner_eq := by
    intro φ ψ hφ hψ
    rw [OddOrder.Peterfalvi.S07.zSpan] at hφ hψ
    induction hφ, hψ using Submodule.span_induction₂ with
    | mem_mem u v hu hv =>
        rw [caseBXsetExtension_eq hyp h46 hHK hW1 _ hu, caseBXsetExtension_eq hyp h46 hHK hW1 _ hv]
        obtain ⟨au, -, hauanc, hauseam, -, hausupp⟩ :=
          caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2
            hFPF hη₁ cY hcYgood hu
        obtain ⟨av, -, havanc, havseam, -, havsupp⟩ :=
          caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2
            hFPF hη₁ cY hcYgood hv
        exact inner_eq_of_anchored_varying hyp cY hη₁ hauanc havanc hauseam havseam
          (caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm u hu η₁ hη₁)
          (caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm v hv η₁ hη₁) hausupp havsupp
    | zero_left v _ => rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
    | zero_right u _ => rw [map_zero, ClassFunction.inner_zero_right,
        ClassFunction.inner_zero_right]
    | add_left u₁ u₂ v _ _ _ ih₁ ih₂ =>
        rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, ih₁, ih₂]
    | add_right u v₁ v₂ _ _ _ ih₁ ih₂ =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ih₁, ih₂]
    | smul_left r u v _ _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (caseBXsetExtension hyp h46 _ u),
          ← Int.cast_smul_eq_zsmul ℂ r u, ClassFunction.inner_smul_left,
          ClassFunction.inner_smul_left, ih]
    | smul_right r u v _ _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (caseBXsetExtension hyp h46 _ v),
          ← Int.cast_smul_eq_zsmul ℂ r v, OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, ih]
  extends_on_supported := by
    intro φ hφ
    refine OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on ?_
      (mem_span_scaledDiff_of_mem_zSupportedSpan
        (by
          rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
          simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff]
          exact fun h => h.2 (by simp))
        hχ₁1 hdvd hφ)
    rintro _ ⟨f, hf, d, hfd, rfl⟩
    obtain ⟨af, hafdeg, hafanc, -, -, -⟩ :=
      caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
        hη₁ cY hcYgood hf
    obtain ⟨a1, ha1deg, ha1anc, -, -, -⟩ :=
      caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
        hη₁ cY hcYgood hanchor
    have haf : af = d * a1 := by
      have h1 : (af : ℂ) * η₁ 1 = ((d * a1 : ℕ) : ℂ) * η₁ 1 := by
        rw [← hafdeg, hfd, ha1deg]; push_cast; ring
      exact_mod_cast mul_right_cancel₀ hη₁1 h1
    rw [map_sub, map_nsmul, caseBXsetExtension_eq hyp h46 hHK hW1 _ hf,
      caseBXsetExtension_eq hyp h46 hHK hW1 _ hanchor]
    rw [show af = d * a1 from haf] at hafanc
    exact anchoredImage_scaledDiff_eq hyp cY hafanc ha1anc rfl
  extension_mem_ZIrr := by
    intro φ hφ
    rw [OddOrder.Peterfalvi.S07.zSpan] at hφ
    induction hφ using Submodule.span_induction with
    | mem u hu =>
        rw [caseBXsetExtension_eq hyp h46 hHK hW1 _ hu]
        obtain ⟨-, -, -, -, hZ, -⟩ :=
          caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2
            hFPF hη₁ cY hcYgood hu
        exact hZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

/-- **⚠ Structural record — the recorded obstruction is GONE as of 2026-07-19; re-evaluate before
reusing this note.**  The map convention here is correct
(`hyp.tau = dadeIntegralCharacterMap hyp.dade (hyp.dade.fullDadeIsometryData hyp.hconj)` defeq, so
`xChainCoherentW hyp.dade hyp.hconj` lands at `hyp.tau` — no retargeting).

The original record read: "the `hstep` hypothesis is unsatisfiable at step 0, because
`XAdjoinStepInputW` requires a **norm-1 anchor** in the accumulator (`hanchorNorm : mc i₁ = 1`) and
the base `certainTypeSet h46 k` has **no** norm-1 member (every column has `‖μ_k‖² = |W₁| > 1`,
`S06_CertainTypeConjugation`)".  **That requirement no longer exists**: the (5.6) engine was
generalized to an arbitrary anchor norm (`S08.crux1_of_memberFamilyW`; Peterfalvi (5.6) never
assumes the anchor is irreducible, and its proof carries `‖χ₁‖²` symbolically), and
`XAdjoinStepInputW` has no `hanchorNorm` field any more.  ⚠ This says only that *this particular*
obstruction is removed — whether folding the weighted chain onto `certainTypeSet` alone is now
actually viable has **not** been re-checked (the other `hstep` obligations were never analysed,
since the norm-1 blocker made the question moot).

**Viable architecture instead**: fold the weighted chain onto base `certainTypeSet ∪ Y` (the
`Y`-anchor `η` has `‖η‖² = 1`), building `IsCoherent hyp.tau (Xset W₂ ∪ Y)` — the **seed directly**,
reusing brick 3's `Y`-anchored field assembly (`sMember_degreeSqNormBound`) and handling the `X ⊥ Y`
seam in-chain via `hortho_mem`.  See roadmap cont.¹⁰.

*(The map-convention fact and the `xChainCoherentW`-wrapper structure stay reusable for the
corrected
base; only the base/`X` sets change.)*

**(6.6) case-(B) weighted `X`-coherence chain consumer** (gated on the per-step weighted adjoin
data).  The reducible-member analogue of `Xset_isCoherent_from_adjoinSteps_of_irreducible_X`. -/
noncomputable def caseB_Xset_isCoherent_of_hstepW
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1)
    (hbase : OddOrder.Peterfalvi.S06.certainTypeSet h46 k ⊆ hyp.Xset h46.W2)
    (hnonS₀_irr : ∀ χ ∈ hyp.Xset h46.W2,
      χ ∉ OddOrder.Peterfalvi.S06.certainTypeSet h46 k → IsIrreducibleCharacter χ)
    (hstep : ∀ (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
        (χs : ℕ → IrreducibleCharacter ↥L),
        (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
        (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
        (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset h46.W2) →
        (∀ χ ∈ hyp.Xset h46.W2, χ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k ∨
          ∃ j, j < N ∧ χ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
        ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
              (hyp.dade.fullDadeIsometryData hyp.hconj))
            (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L)
              (OddOrder.Peterfalvi.S06.certainTypeSet h46 k) pair i)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
          XAdjoinStepInputW hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset h46.W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  choose pair N χs hpair0 hpair1 hpairs hcover using
    caseB_Xset_conjugatePairCover hyp h46 hHK hbase hnonS₀_irr
  exact xChainCoherentW hyp.dade hyp.hconj pair N χs hpair0 hpair1 hbase hpairs hcover
    (hyp.certainTypeSet_isCoherent_tau_canonical h46 hk)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hcover i hi hcoh)

end OddOrder.Peterfalvi.S08
