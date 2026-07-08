/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup
import OddOrder.Peterfalvi.S10_MinimalSimpleStructure

/-!
# Peterfalvi (8.10)/(8.15): the honest type-`P₂` `A₀`-support `A₀(S) = A(S) ∪ V^S`

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §8/§13.

For a type-`P₂` maximal `S`, the Dade support that the §13 machinery actually needs is the **full**
`'A0(S) = 'A(S) ∪ class_support(V_S)` (Coq `FTtypeP_supp0_def`), **not** the smaller `'A(S)`
(`honestTypeP2ASet`).  The `μ`-column differences `μ_{0j} − μ_{01}` are supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S = W ∖ (W₁ ∪ W₂)` has elements with nontrivial `W₂`-component,
hence lies **outside** `S' = derivedInG S ⊇ A(S)`.  So a Dade map built on `'A(S)` alone cannot see
the `V_S`-part of a `μ`-difference (it falls in the arbitrary linear-extension region), which is why
the row-`0` cross-relation `τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` (S15 `tauS_mu_row0_cross`) is not
provable with the `'A(S)`-Dade map (issue 9076).

This file defines the honest type-`P₂` `A₀`-support

`honestTypeP2A0Set M data = honestTypeP2ASet M ∪ conjClassSetIn M (typePV M data)`

using the **correct** `M_σ^#`-indexed `A(S)` (`honestTypeP2ASet`, avoiding the issue-9008 `typePA`
over-claim over `M^#` which includes the escaping non-`σ`-sharp `U^#`), together with the exceptional
`V^M = conjClassSetIn M (typePV M data)`.  The set-level facts (`⊆ M`, non-identity, `M`-conjugation
invariance, `A(S) ⊆ A₀(S)`) are assembled here from the corresponding `honestTypeP2ASet` and `typePV`
facts.  The Dade hypothesis (8.15) for this support — assembled through the `σ`-decomposition engine
`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`, whose `V`-part obligations are vacuous or
generic (`centralizer_typePV_le_M`, `coprime_FT_signalizer_centralizerIn_typePV`,
`conjClassSetIn_typePV_isConj_conj_in_M`) — is the next step (issue 9076 piece 4c).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **The honest type-`P₂` `A₀`-support**: `A₀(S) = A(S) ∪ V^S`, with `A(S) = honestTypeP2ASet S`
(the correct `M_σ^#`-indexed support) and `V^S = conjClassSetIn S (typePV S data)` the `S`-conjugacy
closure of the cyclic-`TI` regular set `V_S = W ∖ (W₁ ∪ W₂)`. -/
def honestTypeP2A0Set (M : Subgroup G) (data : TypePData M) : Set G :=
  honestTypeP2ASet M ∪ conjClassSetIn M (typePV M data)

/-- `A(S) ⊆ A₀(S)`: the honest type-`P₂` support is contained in its `A₀`-completion. -/
theorem honestTypeP2ASet_subset_A0Set {M : Subgroup G} (data : TypePData M) :
    honestTypeP2ASet M ⊆ honestTypeP2A0Set M data :=
  Set.subset_union_left

/-- `W ≤ M` for type-`P` data: the cyclic factor `W = W₁ ⊔ W₂` lands in `M`
(`W₁ ≤ M`; `W₂ ≤ H ⊓ M'' ≤ H ≤ M' ≤ M`). -/
theorem typePData_W_le_M {M : Subgroup G} (data : TypePData M) :
    (data.W : Subgroup G) ≤ M := by
  rw [data.W_eq]
  exact sup_le data.W1_le
    (data.W2_le.trans (le_trans inf_le_left
      (data.H_le.trans (Subgroup.map_subtype_le _))))

/-- `V_S ⊆ M`: the exceptional regular set lands in `M` (it is `⊆ W ≤ M`). -/
theorem typePV_subset_M {M : Subgroup G} (data : TypePData M) :
    typePV M data ⊆ (M : Set G) := fun _ hv =>
  typePData_W_le_M data (((Set.mem_diff _).mp hv).1)

/-- `A₀(S) ⊆ M`: both the `A(S)`-part (`honestTypeP2ASet_subset`) and the `V^S`-part
(`conjClassSetIn` of the `⊆ M` regular set) land in `M`. -/
theorem honestTypeP2A0Set_subset {M : Subgroup G} (data : TypePData M) :
    honestTypeP2A0Set M data ⊆ (M : Set G) := by
  rintro x (hx | hx)
  · exact honestTypeP2ASet_subset hx
  · exact conjClassSetIn_subset (typePV_subset_M data) hx

/-- A `V^M`-element is nonidentity: `V_S` avoids `1` (it is off `W₁ ∋ 1`), preserved under
`M`-conjugation. -/
theorem conjClassSetIn_typePV_one_not_mem {M : Subgroup G} (data : TypePData M) :
    (1 : G) ∉ conjClassSetIn M (typePV M data) := by
  rintro ⟨v, hv, h, -, hconj⟩
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact ((Set.mem_diff _).mp hv).2 (Or.inl (Subgroup.one_mem data.W1))
  exact hv1 (by
    have : v = h⁻¹ * (h * v * h⁻¹) * h := by group
    rw [this, hconj]; group)

/-- `1 ∉ A₀(S)`: both parts avoid the identity (`honestTypeP2ASet_one_not_mem` and
`conjClassSetIn_typePV_one_not_mem`). -/
theorem honestTypeP2A0Set_one_not_mem {M : Subgroup G} (data : TypePData M) :
    (1 : G) ∉ honestTypeP2A0Set M data := by
  rintro (h | h)
  · exact honestTypeP2ASet_one_not_mem h
  · exact conjClassSetIn_typePV_one_not_mem data h

/-- **`A₀(S)` is `M`-conjugation invariant**: both `A(S)` (`honestTypeP2ASet_conj_mem`) and `V^S`
(`mem_conjClassSetIn_conj_iff`) are stable under conjugation by `m ∈ M`. -/
theorem honestTypeP2A0Set_conj_mem [Finite G] {M : Subgroup G} (data : TypePData M) {m : G}
    (hm : m ∈ M) {x : G} :
    m * x * m⁻¹ ∈ honestTypeP2A0Set M data ↔ x ∈ honestTypeP2A0Set M data := by
  simp only [honestTypeP2A0Set, Set.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl (by
        have := honestTypeP2ASet_conj_mem (inv_mem hm) h
        rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at this)
    · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mp h)
  · rintro (h | h)
    · exact Or.inl (honestTypeP2ASet_conj_mem hm h)
    · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mpr h)

end OddOrder.Peterfalvi.S15
