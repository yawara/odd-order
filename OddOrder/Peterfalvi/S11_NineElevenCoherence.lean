/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S08_CoherenceWeighted

/-!
# Peterfalvi (9.11): coherence of `𝒮(H₀C′)` — the maximality induction

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§9, pp. 55–57 (mmd `04.11`); Coq mirror `Ptype_core_coherence`
(`PFsection9.v:1484-2227`).

## What this file provides

The §9-family instantiation of the (9.11) maximality induction, assembled on

* the maximal-coherent-subfamily skeleton
  (`S07.exists_maximal_coherent_between` / `S07.coherent_of_maximal_coherent_pair_refuted`,
  `S07_Subcoherent.lean`),
* the `Snorm`/`sumnS` squeeze lemmas (`S07_Subcoherent.lean`: `lb0_le_lb1_of_degreeRatio_le`,
  `two_mul_le_of_dvd_of_odd` (lb12), `relIndex_le_relIndex_of_le` (lb23),
  `sumnS_of_norm_one_constant_degree` (lb3S1′), `sumnS_le_of_subset` (lbS1′2),
  `two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS` (the `extend_coherent` firing bridge)),
* the weighted (5.6) adjoin engines (`S08.xAdjoinStepW` for irreducible breaks,
  `S08.xAdjoinStepW_k` for reducible `μ_j`-column breaks, `S08_CoherenceWeighted.lean`).

The (9.11) proof splits on the Clifford dichotomy (9.7):

* **case (9.7.b)**: every member of `𝒮(H₀C′)` has degree `qu` (`caseB_degree_qu`, proven), and
  the uniform-degree producer (5.7) applies — the reducible members `μ_j` (norm `q`) need the
  weighted adjoining, seeded from the irreducible uniform cut;
* **case (9.7.a)**: the maximality induction proper — `𝒮₁` = degree-`qa` members (coherent by
  (5.7)), `𝒮₂ ⊇ 𝒮₁` maximal coherent conjugation-closed, and if `𝒮₃ = 𝒮(H₀C′) − 𝒮₂ ≠ ∅` the
  squeeze (9.11.1) either fires the adjoin engine on some `χ ∈ 𝒮₃` (contradicting maximality)
  or forces the equality configuration `a = (p−1)/2`, `C = U′`, `𝒮₂ = 𝒮₁`, … refuted by
  (9.11.2)–(9.11.8).

Consumers: lane b's (13.3) `coherent_H0Cprime_S` re-grounding (`S`-instance, issue 1017 G1),
lane a's gate-2 `hY` (`coherent_Sset_diff_SHCSet`, issue 9016) and (10.7)
`typeII_derived_frobenius`.

Reference note: `issues/1017-pf-s5-uniform-degree-coherence.md` (G1),
`issues/9016-gate2-nine-eleven-difference-report.md` (hY contract).
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-! ### (9.11.1) preamble: the source-degree bound `χ(1) ≤ u` on `𝒳(H₀C′)`

Book (9.11.1), first paragraph: *"Let `χ ∈ 𝒳(H₀C′)`.  There is thus a character `θ ∈ Irr(HC)`
such that `H₀C′ ⊂ Ker θ` and such that `χ` is an irreducible component of `Ind_{HC}^{HU} θ`.
Thus, `χ(1) ≤ |U : C|·θ(1) = u`."*  (Coq `lb01`'s inner bound, `PFsection9.v:1560-1571`.)

The constituent `θ = ψ` is any `Irr(HC)`-character `χ` lies over (`exists_liesOver`); it is
linear because `⁅HC,HC⁆ ⊆ H₀C′ ⊆ Ker χ` (`commutator_hcInHu_le_realized`, the (9.9.a) kernel
containment) makes it factor through the abelian quotient; and the constituent degree bound
`χ(1) ≤ (Ind_{HC}^{HU} ψ)(1) = [HU:HC]·ψ(1)` (`apply_one_le_induce_apply_one_of_liesOver`)
finishes with `[HU:HC] = [U:C] = u` (the (9.9.a) index steps). -/

section DegreeBound

variable [Finite G] {M : Subgroup G}

open scoped Classical ComplexOrder in
/-- **Peterfalvi (9.11.1), the source-degree bound: every `χ ∈ 𝒳(H₀C′)` has `χ(1) ≤ u`.**

The degree of a source character with `H₀C′` in its kernel is at most `u = [U:C]`: `χ` lies over
a linear character `ψ` of `HC` (linear by the (9.9.a) commutator containment
`⁅HC,HC⁆ ≤ H₀C′ ⊆ Ker χ`), so `χ(1) ≤ (Ind_{HC}^{HU} ψ)(1) = [HU:HC] = u`.  This is the *upper*
half of the (9.9.a) degree computation, valid in **both** Clifford cases (case (b) upgrades it
to equality via the inertia argument, `caseB_degree_qu`); the (9.11.1) squeeze `lb0 ≤ lb1`
consumes it for the `𝒮₃`-member `χ` (member degree `q·χ(1) ≤ q·u`). -/
theorem xiOf_H0Cprime_source_apply_one_le_u {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiOf data (chief.H0 ⊔ chars.Cprime)) :
    ((χ : ClassFunction ↥(huSub data) ℂ) : ↥(huSub data) → ℂ) 1 ≤ (chars.u : ℂ) := by
  classical
  haveI : Fintype ↥M := Fintype.ofFinite _
  haveI : Fintype ↥(huSub data) := Fintype.ofFinite _
  haveI : Fintype ↥(hInHu data ⊔ cInHu data chief) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥(hInHu data ⊔ cInHu data chief) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter ↥(huSub data)) :=
    Fintype.ofFinite _
  -- A constituent `ψ ∈ Irr(HC)` that `χ` lies over.
  obtain ⟨ψ, hψover⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
      (H := hInHu data ⊔ cInHu data chief) χ
  -- `ψ` is linear: `⁅HC,HC⁆ ⊆ Ker χ` (via `H₀C′ ⊆ Ker χ`), so `ψ` factors through the
  -- abelianization (the (9.9.a) obligation-3 block of `caseB_degree_qu`, verbatim).
  have hψdeg : (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ)
      (1 : ↥(hInHu data ⊔ cInHu data chief)) = 1 := by
    haveI : IsMulCommutative (↥(hInHu data ⊔ cInHu data chief) ⧸
        commutator ↥(hInHu data ⊔ cInHu data chief)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥(hInHu data ⊔ cInHu data chief)))
    refine OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥(hInHu data ⊔ cInHu data chief)) ψ ?_
    intro g hg
    refine liesOver_mem_characterKernel hψover ?_
    refine hχ.2 ?_
    have hgmem : (g : ↥(huSub data))
        ∈ ⁅hInHu data ⊔ cInHu data chief, hInHu data ⊔ cInHu data chief⁆ := by
      rw [← derivedInG_eq_commutator]
      exact Subgroup.mem_map_of_mem _ hg
    exact commutator_hcInHu_le_realized data chief hgmem
  -- Constituent degree bound: `χ(1) ≤ (Ind_{HC}^{HU} ψ)(1)`.
  have hle := OddOrder.RepresentationTheory.apply_one_le_induce_apply_one_of_liesOver
    (I := hInHu data ⊔ cInHu data chief) χ ψ hψover
  -- `(Ind_{HC}^{HU} ψ)(1) = [HU:HC]·ψ(1) = [HU:HC] = u`.
  have hind : ClassFunction.induce (hInHu data ⊔ cInHu data chief)
      (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ) (1 : ↥(huSub data))
      = (chars.u : ℂ) := by
    rw [ClassFunction.induce_apply_one, hψdeg, mul_one]
    have hidx : (hInHu data ⊔ cInHu data chief).index = chars.u :=
      (index_hcInHu_eq_relindex_cInHu data chief).trans
        (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) hidx
  rw [hind] at hle
  exact hle

open scoped ComplexOrder in
/-- **Peterfalvi (9.11.1), member form: every `φ ∈ 𝒮(H₀C′)` has `φ(1) ≤ q·u`.**

The `M`-induced form of `xiOf_H0Cprime_source_apply_one_le_u`: `φ = Ind_{HU}^M χ` has degree
`q·χ(1) ≤ q·u` (`induceHU_apply_one_eq_q_mul`).  This bounds the `𝒮₃`-member degree in the
(9.11.1) squeeze `lb0 = 2qa·χ(1) ≤ 2qa·qu ~ lb1` (after the anchor rescaling). -/
theorem sOf_H0Cprime_apply_one_le_qu {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data (chief.H0 ⊔ chars.Cprime)) :
    (φ : ↥M → ℂ) 1 ≤ ((data.q * chars.u : ℕ) : ℂ) := by
  classical
  obtain ⟨χ, hχ, rfl⟩ := hφ
  rw [induceHU_apply_one_eq_q_mul]
  have hle := xiOf_H0Cprime_source_apply_one_le_u chars hχ
  push_cast
  refine mul_le_mul_of_nonneg_left hle ?_
  exact_mod_cast Nat.zero_le data.q

end DegreeBound

end OddOrder.Peterfalvi.S11
