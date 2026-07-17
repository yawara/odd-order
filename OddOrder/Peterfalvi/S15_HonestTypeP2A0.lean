/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup
import OddOrder.Peterfalvi.S10_MinimalSimpleStructure
import OddOrder.Peterfalvi.S13_PrimeTIResidueBridge

/-!
# Peterfalvi (8.10)/(8.15): the honest type-`P₂` `A₀`-support `A₀(S) = A(S) ∪ V^S`

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §8/§13.

For a type-`P₂` maximal `S`, the Dade support that the §13 machinery actually needs is the **full**
`'A0(S) = 'A(S) ∪ class_support(V_S)` (Coq `FTtypeP_supp0_def`), **not** the smaller `'A(S)`
(`honestTypeP2ASet`).  The `μ`-column differences `μ_{0j} − μ_{01}` are supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S = W ∖ (W₁ ∪ W₂)` has elements with nontrivial `W₂`-component,
hence lies **outside** `S' = derivedInG S ⊇ A(S)`.  So a Dade map built on `'A(S)` alone cannot see
the `V_S`-part of a `μ`-difference (it falls in the arbitrary linear-extension region), which is why
the row-`0` cross-relation `τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` (S15 `tauS_mu_row0_cross`) is
not
provable with the `'A(S)`-Dade map (issue 9076).

This file defines the honest type-`P₂` `A₀`-support

`honestTypeP2A0Set M data = honestTypeP2ASet M ∪ conjClassSetIn M (typePV M data)`

using the **correct** `M_σ^#`-indexed `A(S)` (`honestTypeP2ASet`, avoiding the issue-9008 `typePA`
over-claim over `M^#` which includes the escaping non-`σ`-sharp `U^#`), together with the
exceptional
`V^M = conjClassSetIn M (typePV M data)`.  The set-level facts (`⊆ M`, non-identity, `M`-conjugation
invariance, `A(S) ⊆ A₀(S)`) are assembled here from the corresponding `honestTypeP2ASet` and
`typePV`
facts.  The Dade hypothesis (8.15) for this support — assembled through the `σ`-decomposition engine
`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`, whose `V`-part obligations are vacuous or
generic (`centralizer_typePV_le_M`, `coprime_FT_signalizer_centralizerIn_typePV`,
`conjClassSetIn_typePV_isConj_conj_in_M`) — is the next step (issue 9076 piece 4c).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

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
  typePData_W_le_M data (((Set.mem_sdiff _).mp hv).1)

/-- **`V^M`-points lie in BG's `σ`-saturation `hatMsigma M`** (issue 9076 piece 4c-2b″, step 2a of
the `honestTypeP2A0Set ⊆ A0Set` bridge).  A `V = typePV`-point `v = a·b` (`a ∈ W₁`, `b ∈ W₂`, the
`W = W₁ ⊔ W₂` factorization) has a **nontrivial** `W₂`-component `b ≠ 1` (else `v = a ∈ W₁`), and
`W₂ ≤ H = M_F ≤ M_σ` (`maxNilpotentNormalHall_le_Msigma`); since `W` is cyclic (abelian) `v`
commutes
with `b`, so `b ∈ M_σ ⊓ C_G(v)` witnesses `M_σ ⊓ C_G(v) ≠ ⊥`.  This is the `V`-side half of showing
`A₀(S) ⊆ hatMsigma M`, feeding the BG §16 Theorem-II tame conjugation. -/
theorem typePV_subset_hatMsigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypePData M) :
    typePV M data ⊆ OddOrder.BG.Ch4.S16.hatMsigma M := by
  intro v hv
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at hv
  obtain ⟨hvW, hvnW1, _hvnW2⟩ := hv
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hWM : (data.W : Subgroup G) ≤ M := by
    rw [data.W_eq]
    exact sup_le data.W1_le
      (data.W2_le.trans (inf_le_left.trans (data.H_le.trans (Subgroup.map_subtype_le _))))
  -- `v = a·b` with `a ∈ W₁`, `b ∈ W₂` (cyclic `W = W₁ ⊔ W₂`).
  have hsup : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hvmem : (⟨v, hvW⟩ : ↥data.W) ∈
      data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hvmem
  obtain ⟨a, ha, b, hb, hab⟩ := hvmem
  have haW1 : ((a : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : ((b : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hb
  have habG : ((a : ↥data.W) : G) * ((b : ↥data.W) : G) = v := by
    have := congrArg (Subtype.val) hab; simpa using this
  -- `b ≠ 1` (else `v = a ∈ W₁`).
  have hb1 : ((b : ↥data.W) : G) ≠ 1 := by
    intro h; exact hvnW1 (by rw [← habG, h, mul_one]; exact haW1)
  -- `b ∈ M_σ` (`W₂ ≤ H = M_F ≤ M_σ`).
  have hbMσ : ((b : ↥data.W) : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    refine (data.W2_le.trans (inf_le_left.trans ?_)) hbW2
    rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM
  -- `v` commutes with `b` (both in the abelian `W`).
  have hcomm : v * ((b : ↥data.W) : G) = ((b : ↥data.W) : G) * v := by
    have h := congrArg Subtype.val (mul_comm (⟨v, hvW⟩ : ↥data.W) b)
    simpa using h
  refine ⟨hWM hvW, fun hbot => hb1 ?_⟩
  have hbInf : ((b : ↥data.W) : G) ∈
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({v} : Set G) :=
    ⟨hbMσ, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  rw [hbot, Subgroup.mem_bot] at hbInf; exact hbInf

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
    exact ((Set.mem_sdiff _).mp hv).2 (Or.inl (Subgroup.one_mem data.W1))
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

/-- `∀ x ∈ A₀(S), x ≠ 1` — the `≠ 1` form of `honestTypeP2A0Set_one_not_mem` (the shape the
`σ`-decomposition Dade engine's `hXsharp` obligation takes). -/
theorem honestTypeP2A0Set_ne_one {M : Subgroup G} (data : TypePData M) :
    ∀ x ∈ honestTypeP2A0Set M data, x ≠ (1 : G) :=
  fun _ hx h => honestTypeP2A0Set_one_not_mem data (h ▸ hx)

/-- **A `V^S`-point does not escape `M`**: its centralizer lies in `M`.  For `b = h·v·h⁻¹`
(`v ∈ V_S`, `h ∈ M`), `C_G(b) = h·C_G(v)·h⁻¹ ≤ h·M·h⁻¹ = M` (`centralizer_typePV_le_M`, `h ∈ M`).
This is what makes the `V`-part of the Dade engine's escaping-`σ`-sharp obligation **vacuous**. -/
theorem conjClassSetIn_typePV_centralizer_le_M {M : Subgroup G} (data : TypePData M)
    {b : G} (hb : b ∈ conjClassSetIn M (typePV M data)) :
    Subgroup.centralizer ({b} : Set G) ≤ M := by
  obtain ⟨v, hv, h, hhM, rfl⟩ := hb
  intro x hx
  have hcomm : x * (h * v * h⁻¹) = (h * v * h⁻¹) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  -- `h⁻¹ x h` commutes with `v`, hence lies in `C_G(v) ≤ M`.
  have hcv : (h⁻¹ * x * h) ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (h⁻¹ * x * h) * v
        = h⁻¹ * (x * (h * v * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * v * h⁻¹) * x) * h := by rw [hcomm]
      _ = v * (h⁻¹ * x * h) := by group
  have hxM : (h⁻¹ * x * h) ∈ M :=
    OddOrder.Peterfalvi.S10.centralizer_typePV_le_M data hv hcv
  have hxeq : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [hxeq]
  exact M.mul_mem (M.mul_mem hhM hxM) (M.inv_mem hhM)

/-- **Escaping `A₀(S)`-points come from the `A(S)`-part**: since `V^S`-points do not escape
(`conjClassSetIn_typePV_centralizer_le_M`), any escaping point of `A₀(S)` lies in `A(S)` and escapes
there too.  This reduces the Dade engine's escaping-`σ`-sharp and coprimality obligations for `A₀(S)`
to the already-established `honestTypeP2ASet` ones. -/
theorem escaping_honestTypeP2A0Set_mem_honestTypeP2ASet {M : Subgroup G} (data : TypePData M)
    {a : G} (ha : a ∈ escapingCentralizerSet M (honestTypeP2A0Set M data)) :
    a ∈ escapingCentralizerSet M (honestTypeP2ASet M) := by
  obtain ⟨haA0, haesc⟩ := ha
  rcases haA0 with hpa | hva
  · exact ⟨hpa, haesc⟩
  · exact absurd (conjClassSetIn_typePV_centralizer_le_M data hva) haesc

/-- **(13.2.e) `normedTI` core for the `A₀`-support: no `A₀(S)`-point escapes.**  Every escaping
`A₀(S)`-point reduces to an escaping `A(S)`-point
(`escaping_honestTypeP2A0Set_mem_honestTypeP2ASet`,
since `V^S` does not escape), and the honest `A(S)` has no escaping point on a type-`P₂` maximal
(`escaping_honestTypeP2ASet_eq_empty`, the proven (13.2.e) core via BG Theorem D(4)).  So the full
`'A0(S)` support is `normedTI`: this is the trivial-stabilizer input `∀ a, dadeHypS0.H a = ⊥` the
`τ_S = Ind_S^G` Dade=Ind bridge needs (feeding (13.18.c) `⟨Γ, 1_G⟩ = 0` etc., issue 9076). -/
theorem escaping_honestTypeP2A0Set_eq_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M) (data : TypePData M) :
    OddOrder.GroupTheory.escapingCentralizerSet M (honestTypeP2A0Set M data) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro a ha
  have hAesc := escaping_honestTypeP2A0Set_mem_honestTypeP2ASet data ha
  rw [escaping_honestTypeP2ASet_eq_empty hG hnoV hM hTP] at hAesc
  exact Set.notMem_empty a hAesc

/-! ### The `A₀(S) ⊆ A0Set M K₀` bridge (issue 9076 piece 4c)

The honest support `honestTypeP2A0Set M data = A(S) ∪ V^S` embeds into BG's Theorem-E set
`A0Set M K₀ = hatMsigma M ∖ 𝒞_G(K₀#)`.  The `A(S)`-part uses `honestTypeP2ASet_subset_ASet`
composed with `ASet ⊆ A0Set`; the `V^S`-part uses `typePV_subset_hatMsigma` (conjugacy-closed) plus
the order argument that a `V`-point carries a `σ`-prime while `K₀#` is pure `κ`.  The order pieces
all reduce to: `𝒞_G(K₀#)`-points are nonidentity `κ`-elements
(`kappaHall_conjClassSet_isPiElement`), while `A(S)`-points are `κ′`-elements and `V^S`-points have
a `σ ⊆ κ′`-prime. -/

/-- **`W₁ ⊓ W₂ = ⊥`** for a `TypePData`: the two cyclic factors intersect trivially.  `W₂ ≤ M'`
(`W2_le`/`H_le`) while `W₁` complements `M' = derivedInG M` in `M` (`M_complement`), so
`W₁ ⊓ W₂ ≤ W₁ ⊓ M' = ⊥`.  (Ambient-subgroup form of the disjoint half of `M_complement`, mirroring
`TypePData.fitting_inf_U_eq_bot`.) -/
theorem typePData_W1_inf_W2_eq_bot {M : Subgroup G} (data : TypePData M) :
    data.W1 ⊓ data.W2 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxW1, hxW2⟩ := hx
  have hxM : x ∈ M := data.W1_le hxW1
  have hxD : x ∈ derivedInG M := data.H_le (Subgroup.mem_inf.mp (data.W2_le hxW2)).1
  have hmem : (⟨x, hxM⟩ : ↥M) ∈
      ((derivedInG M).subgroupOf M) ⊓ (data.W1.subgroupOf M) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hxD, Subgroup.mem_subgroupOf.mpr hxW1⟩
  have hd := data.M_complement.disjoint
  rw [disjoint_iff] at hd
  rw [hd, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext_iff.mp hmem

/-- **A `V^S`-point's order is divisible by a `σ`-prime** (issue 9076 piece 4c): a
`V = typePV`-point `v = a·b` (`a ∈ W₁`, `b ∈ W₂`, cyclic `W = W₁ ⊔ W₂`) has a nontrivial
`W₂`-component `b ≠ 1` (else
`v = a ∈ W₁`).  Since `W₁ ⊓ W₂ = ⊥` (`typePData_W1_inf_W2_eq_bot`) and `a, b` commute (abelian `W`),
`orderOf b ∣ orderOf v`; and `b ∈ W₂ ≤ M_σ` is a `σ`-element (`isPiElement_sigma_of_mem_Msigma`),
so some `σ`-prime divides `orderOf b ∣ orderOf v`.  This is the `V`-side "order carries a `σ`-prime"
input that excludes `V^S` from the pure-`κ` set `𝒞_G(K₀#)`. -/
theorem exists_sigma_prime_dvd_orderOf_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {v : G} (hv : v ∈ typePV M data) :
    ∃ p ∈ (orderOf v).primeFactors,
      p ∈ OddOrder.BG.Ch3.S10.sigma M ∧ p ∣ Nat.card ↥data.W2 := by
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at hv
  obtain ⟨hvW, hvnW1, _hvnW2⟩ := hv
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hsup : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hvmem : (⟨v, hvW⟩ : ↥data.W) ∈
      data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hvmem
  obtain ⟨a, ha, b, hb, hab⟩ := hvmem
  have haW1 : ((a : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : ((b : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hb
  have habG : ((a : ↥data.W) : G) * ((b : ↥data.W) : G) = v := by
    have := congrArg (Subtype.val) hab; simpa using this
  have hb1 : ((b : ↥data.W) : G) ≠ 1 := by
    intro h; exact hvnW1 (by rw [← habG, h, mul_one]; exact haW1)
  have hcomm : Commute ((a : ↥data.W) : G) ((b : ↥data.W) : G) := by
    have h : ((a : ↥data.W) : G) * ((b : ↥data.W) : G)
        = ((b : ↥data.W) : G) * ((a : ↥data.W) : G) := by
      have h0 := congrArg Subtype.val (mul_comm a b); simpa using h0
    exact h
  -- `orderOf b ∣ orderOf v` (commuting factors of a cyclic `W = W₁ × W₂`).
  have hbdvd : orderOf ((b : ↥data.W) : G) ∣ orderOf v := by
    have hab_n : ((a : ↥data.W) : G) ^ orderOf v * ((b : ↥data.W) : G) ^ orderOf v = 1 := by
      rw [← hcomm.mul_pow, habG]; exact pow_orderOf_eq_one v
    have hanW1 : ((a : ↥data.W) : G) ^ orderOf v ∈ data.W1 := pow_mem haW1 _
    have hbnW2 : ((b : ↥data.W) : G) ^ orderOf v ∈ data.W2 := pow_mem hbW2 _
    have han_eq : ((a : ↥data.W) : G) ^ orderOf v
        = (((b : ↥data.W) : G) ^ orderOf v)⁻¹ := mul_eq_one_iff_eq_inv.mp hab_n
    have han_in_W2 : ((a : ↥data.W) : G) ^ orderOf v ∈ data.W2 := by
      rw [han_eq]; exact inv_mem hbnW2
    have han_bot : ((a : ↥data.W) : G) ^ orderOf v ∈ data.W1 ⊓ data.W2 :=
      Subgroup.mem_inf.mpr ⟨hanW1, han_in_W2⟩
    rw [typePData_W1_inf_W2_eq_bot data, Subgroup.mem_bot] at han_bot
    have hbn1 : ((b : ↥data.W) : G) ^ orderOf v = 1 := by
      rw [han_bot, one_mul] at hab_n; exact hab_n
    exact orderOf_dvd_of_pow_eq_one hbn1
  -- `b ∈ M_σ` (`W₂ ≤ H = M_F ≤ M_σ`), so a `σ`-prime divides `orderOf b`.
  have hbMσ : ((b : ↥data.W) : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    refine (data.W2_le.trans (inf_le_left.trans ?_)) hbW2
    rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM
  have hbσ : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) ((b : ↥data.W) : G) :=
    OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma hbMσ
  have hbord1 : orderOf ((b : ↥data.W) : G) ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpp, hpdvdb⟩ := (orderOf ((b : ↥data.W) : G)).exists_prime_and_dvd hbord1
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hpp, hpdvdb.trans hbdvd, (orderOf_pos v).ne'⟩, ?_, ?_⟩
  · exact hbσ p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvdb, (orderOf_pos _).ne'⟩)
  · exact hpdvdb.trans (data.W2.orderOf_dvd_natCard hbW2)

/-- **`𝒞_G(K₀#)`-points are nonidentity `κ`-elements** (issue 9076 piece 4c): every `G`-conjugate of
a nontrivial element of the `κ(M)`-Hall `K₀` is a nonidentity `κ(M)`-element.  A `k ∈ K₀#` has
`orderOf k ∣ |K₀|`, a `κ`-number (`hK`), so `k` is a `κ`-element; conjugation preserves this
(`isPiElement_conj`) and non-triviality.  This is the exclusion input for both `A(S)` (`κ′`-elements)
and `V^S` (`σ`-prime carriers) against `A0Set M K₀ = hatMsigma M ∖ 𝒞_G(K₀#)`. -/
theorem kappaHall_conjClassSet_isPiElement [Finite G] {M K₀ : Subgroup G} (hKM : K₀ ≤ M)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    {w : G} (hw : w ∈ conjClassSet (OddOrder.GroupTheory.sharpSubgroup K₀)) :
    IsPiElement (OddOrder.BG.Ch4.S14.kappa M) w ∧ w ≠ 1 := by
  obtain ⟨k, hk, g, hgw⟩ := hw
  rw [OddOrder.GroupTheory.sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
    Set.mem_singleton_iff] at hk
  obtain ⟨hkK, hk1⟩ := hk
  subst hgw
  have hkord : orderOf k ∣ Nat.card ↥K₀ := by
    have horx : orderOf k = orderOf (⟨k, hkK⟩ : ↥K₀) :=
      orderOf_injective K₀.subtype K₀.subtype_injective ⟨k, hkK⟩
    rw [horx]; exact orderOf_dvd_natCard _
  have hkκ : IsPiElement (OddOrder.BG.Ch4.S14.kappa M) k := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ orderOf k := Nat.dvd_of_mem_primeFactors hp
    have hcardeq : Nat.card ↥(K₀.subgroupOf M) = Nat.card ↥K₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    refine hK.1 p ?_
    rw [hcardeq]
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hkord, Nat.card_pos.ne'⟩
  refine ⟨OddOrder.BG.Ch4.S14.isPiElement_conj g hkκ, fun hcontra => hk1 ?_⟩
  have hkk : k = g⁻¹ * (g * k * g⁻¹) * g := by group
  rw [hkk, hcontra]; group

/-- **`ASet M U₀ ⊆ A0Set M K₀`** (issue 9076 piece 4c): the BG Theorem-E `A(M)`-set embeds into the
`A_0(M)`-set.  Both are `⊆ hatMsigma M`; and an `ASet`-point `x ∈ U₀ ⊔ M_σ` is a `κ′`-element
(`mem_U_sup_Msigma_iff_isPiElement_kappa_compl`), while a `𝒞_G(K₀#)`-point is a nonidentity
`κ`-element (`kappaHall_conjClassSet_isPiElement`) — no element is both, so `x ∉ 𝒞_G(K₀#)`. -/
theorem aSet_subset_A0Set [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M)) :
    OddOrder.BG.Ch4.S16.ASet M U₀ ⊆ OddOrder.BG.Ch4.S16.A0Set M K₀ := by
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hnorm : ((U₀ ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hUM hMσM)).mpr
      (OddOrder.BG.Ch4.S16.theoremA_ungated_conjuncts hG hM hKM hUM hK rfl hU).2.2.1
  intro x hx
  simp only [OddOrder.BG.Ch4.S16.ASet, Set.mem_inter_iff, SetLike.mem_coe] at hx
  obtain ⟨hxhat, hxsup⟩ := hx
  simp only [OddOrder.BG.Ch4.S16.A0Set, Set.mem_sdiff]
  refine ⟨hxhat, fun hxconj => ?_⟩
  obtain ⟨hxκ, hx1⟩ := kappaHall_conjClassSet_isPiElement hKM hK hxconj
  have hxκ' : IsPiElement (OddOrder.BG.Ch4.S14.kappa M)ᶜ x :=
    (OddOrder.BG.Ch4.S14.mem_U_sup_Msigma_iff_isPiElement_kappa_compl hG hM hUM hU hnorm
      hxhat.1).mp hxsup
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpp, hpdvd⟩ := (orderOf x).exists_prime_and_dvd hne1
  have hpf : p ∈ (orderOf x).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, (orderOf_pos x).ne'⟩
  exact (hxκ' p hpf) (hxκ p hpf)

/-- **`V^S ⊆ A0Set M K₀`** (issue 9076 piece 4c): the `M`-conjugacy closure of the exceptional
regular set `V = typePV` embeds into the `A_0(M)`-set.  `V ⊆ hatMsigma M` (`typePV_subset_hatMsigma`)
extends to the closure because `hatMsigma M` is `M`-conjugation invariant (`M_σ ◁ M`); and a
`V`-point carries a `σ`-prime (`exists_sigma_prime_dvd_orderOf_typePV`), `σ ⊆ κ′`
(`kappa_subset_sigmaCompl`), so it is not a `κ`-element, hence off the pure-`κ` set `𝒞_G(K₀#)`
(conjugation-invariant, `mem_conjClassSet_conj_iff`). -/
theorem conjClassSetIn_typePV_subset_A0Set [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K₀ : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K₀ ≤ M)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (data : TypePData M) :
    conjClassSetIn M (typePV M data) ⊆ OddOrder.BG.Ch4.S16.A0Set M K₀ := by
  have hM_le_NMσ : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  haveI hMσ_norm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr hM_le_NMσ
  rintro _ ⟨v, hv, m, hmM, rfl⟩
  have hvhat : v ∈ OddOrder.BG.Ch4.S16.hatMsigma M := typePV_subset_hatMsigma hG hM data hv
  simp only [OddOrder.BG.Ch4.S16.A0Set, Set.mem_sdiff, OddOrder.BG.Ch4.S16.hatMsigma,
    Set.mem_setOf_eq]
  refine ⟨⟨M.mul_mem (M.mul_mem hmM hvhat.1) (M.inv_mem hmM), ?_⟩, ?_⟩
  · -- `M_σ ⊓ C_G(m·v·m⁻¹) ≠ ⊥`: conjugate the `M_σ`-centralizing witness of `v`.
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hvhat.2
    obtain ⟨hwMσ, hwC⟩ := Subgroup.mem_inf.mp w.2
    have hw0C : (w : G) * v = v * (w : G) := Subgroup.mem_centralizer_singleton_iff.mp hwC
    have hwne : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hconjMσ : m * (w : G) * m⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
      have h := hMσ_norm.conj_mem ⟨(w : G), OddOrder.BG.Ch3.S10.Msigma_le M hwMσ⟩
        (Subgroup.mem_subgroupOf.mpr hwMσ) ⟨m, hmM⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    have hconjC : m * (w : G) * m⁻¹ ∈ Subgroup.centralizer ({m * v * m⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (m * (w : G) * m⁻¹) * (m * v * m⁻¹)
          = m * ((w : G) * v) * m⁻¹ := by group
        _ = m * (v * (w : G)) * m⁻¹ := by rw [hw0C]
        _ = (m * v * m⁻¹) * (m * (w : G) * m⁻¹) := by group
    have hconjne : m * (w : G) * m⁻¹ ≠ 1 := by
      intro h
      refine hwne ?_
      have hww : (w : G) = m⁻¹ * (m * (w : G) * m⁻¹) * m := by group
      rw [hww, h]; group
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨m * (w : G) * m⁻¹, Subgroup.mem_inf.mpr ⟨hconjMσ, hconjC⟩⟩,
      fun h => hconjne (Subtype.ext_iff.mp h)⟩
  · -- `m·v·m⁻¹ ∉ 𝒞_G(K₀#)`: reduce to `v` (conj-invariant), which carries a `σ ⊆ κ′`-prime.
    intro hconj
    rw [mem_conjClassSet_conj_iff] at hconj
    obtain ⟨hvκ, -⟩ := kappaHall_conjClassSet_isPiElement hKM hK hconj
    obtain ⟨p, hpf, hpσ, -⟩ := exists_sigma_prime_dvd_orderOf_typePV hG hM data hv
    exact OddOrder.BG.Ch4.S14.kappa_subset_sigmaCompl (hvκ p hpf) hpσ

/-- **`A₀(S) ⊆ A0Set M K₀`** (issue 9076 piece 4c): the honest type-`P₂` support embeds into BG's
Theorem-E set.  `A(S)`-part via `honestTypeP2ASet_subset_ASet` + `aSet_subset_A0Set`; `V^S`-part via
`conjClassSetIn_typePV_subset_A0Set`.  This is the bridge feeding `theoremII_tame_embedding` for
`honestTypeP2A0Set_tame_conj`. -/
theorem honestTypeP2A0Set_subset_A0Set [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K₀ ≤ M) (hUM : U₀ ≤ M) (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    (data : TypePData M) :
    honestTypeP2A0Set M data ⊆ OddOrder.BG.Ch4.S16.A0Set M K₀ := by
  apply Set.union_subset
  · exact (honestTypeP2ASet_subset_ASet hG hM hKM hUM hKne hK hU).trans
      (aSet_subset_A0Set hG hM hKM hUM hK hU)
  · exact conjClassSetIn_typePV_subset_A0Set hG hM hKM hK data

/-- **Tame conjugation for the honest type-`P₂` `A₀`-support** (BG §16 Theorem II): two `G`-conjugate
elements of `A₀(M) = A(M) ∪ V^M` are already `M`-conjugate.  This is the first conjunct of BG Theorem
II (`OddOrder.BG.Ch4.S16.theoremII_tame_embedding` with `X = A0Set M K`): for the tame embedding, a
`G`-fusion of support points is controlled by `N_G(M) = M`.

Discharge route (issue 9076 piece 4c): bridge the honest support `honestTypeP2A0Set M data` into
BG's
`A0Set M K = hatMsigma M ∖ 𝒞_G(K#)` — the `A(M)`-part via `honestTypeP2ASet_subset_hatMsigma`, the
`V^M`-part via `typePV ⊆ hatMsigma` plus the order argument `V^M ∩ 𝒞_G(K#) = ∅` (a `V`-point has
order divisible by `pq`, a `K#`-point only by `q`) — and produce the `κ`-Hall `K` / `(κ∪σ)′`-Hall
`U`
of the type-`P` maximal `M`.  With `a, b ∈ A0Set M K`, `theoremII_tame_embedding`'s first conjunct
supplies the `M`-conjugator.  (Reduces the earlier "genuine deep FT-support geometry" pin to this
concrete BG-support bridge.) -/
theorem honestTypeP2A0Set_tame_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {K₀ U₀ : Subgroup G} (hKM : K₀ ≤ M) (hUM : U₀ ≤ M) (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a b : G}
    (ha : a ∈ honestTypeP2A0Set M data) (hb : b ∈ honestTypeP2A0Set M data)
    (hab : IsConj a b) : ∃ m ∈ M, b = m * a * m⁻¹ := by
  have hsub := honestTypeP2A0Set_subset_A0Set hG hM hKM hUM hKne hK hU data
  have hII := OddOrder.BG.Ch4.S16.theoremII_tame_embedding hG hM hKM hUM hK hU
    (X := OddOrder.BG.Ch4.S16.A0Set M K₀) (Or.inr rfl)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  obtain ⟨m, hmM, hmb⟩ := hII.1 a (hsub ha) b (hsub hb) ⟨g, hg.symm⟩
  exact ⟨m, hmM, hmb⟩

/-- **(8.13.a), the mixed `A(S)`–`V^S` case is vacuous**: an `A(S)`-point is never `G`-conjugate to a
`V^S`-point.  An `A(S) = honestTypeP2ASet` element lies in `S' = derivedInG S`, while a `V^S`-point
lies **outside** `S'` (`typePData_typePV_not_mem_derived`, the nontrivial `W₁`-component).

Proved (issue 9076 piece 4c) via the honest-support tame conjugation `honestTypeP2A0Set_tame_conj`
(BG §16 Theorem II): if `a` and `b` were `G`-conjugate, they would be **`M`-conjugate**
(`b = m·a·m⁻¹`, `m ∈ M`); but `M' = derivedInG M` is normal in `M`, so `M`-conjugation preserves
`M'`-membership, forcing `b ∈ M'` from `a ∈ M'` — contradicting `b ∉ M'`.  This replaces the earlier
circular `normedTI`-based argument with the direct FT-support-geometry route (Coq `FTsupp0`). -/
theorem not_isConj_honestTypeP2ASet_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {K₀ U₀ : Subgroup G} (hKM : K₀ ≤ M) (hUM : U₀ ≤ M) (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a b : G}
    (ha : a ∈ honestTypeP2ASet M) (hb : b ∈ conjClassSetIn M (typePV M data))
    (hab : IsConj a b) : False := by
  -- `M`-conjugation preserves `M' = derivedInG M`-membership (`M' ⊴ M`).
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hconj_derived : ∀ x w : G, x ∈ M → w ∈ derivedInG M → x * w * x⁻¹ ∈ derivedInG M := by
    intro x w hxM hwD
    have hconj := (inferInstance : ((derivedInG M).subgroupOf M).Normal).conj_mem
      ⟨w, hM'le hwD⟩ (Subgroup.mem_subgroupOf.mpr hwD) ⟨x, hxM⟩
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  -- `a ∈ M'`, and (BG tame) `b ∈ A₀(M)` is `M`-conjugate to `a ∈ A(M) ⊆ A₀(M)`.
  have haD : a ∈ derivedInG M := (mem_honestTypeP2ASet.mp ha).1
  have hbA0 : b ∈ honestTypeP2A0Set M data := Set.mem_union_right _ hb
  obtain ⟨v, hv, h, hhM, hhvb⟩ := hb
  -- `b ∉ M'`: `b = h·v·h⁻¹`, `v ∈ V ⊄ M'`, `h ∈ M`, and `M' ⊴ M`.
  have hbnD : b ∉ derivedInG M := by
    intro hbD
    refine OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived data hv ?_
    have hvconj : h⁻¹ * b * (h⁻¹)⁻¹ ∈ derivedInG M :=
      hconj_derived h⁻¹ b (M.inv_mem hhM) hbD
    rwa [show h⁻¹ * b * (h⁻¹)⁻¹ = v from by rw [← hhvb]; group] at hvconj
  -- BG §16 Theorem II tame conjugation ⟹ `b = m·a·m⁻¹ ∈ M'`, contradiction.
  obtain ⟨m, hmM, hmc⟩ :=
    honestTypeP2A0Set_tame_conj hG hM data hKM hUM hKne hK hU
      (honestTypeP2ASet_subset_A0Set data ha) hbA0 hab
  exact hbnD (hmc ▸ hconj_derived m a hmM haD)

/-- **Peterfalvi (8.15) for the honest type-`P₂` `A₀`-support**: the Dade (2.2) support hypotheses
hold for `A₀(S) = A(S) ∪ V^S`.  Assembled through the `σ`-decomposition engine
`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`:

* set-facts (`⊆ M`, `≠ 1`, `M`-conjugation-invariant, nonempty) — the `honestTypeP2A0Set_*` facts;
* escaping-`σ`-sharp and coprimality — reduced to the `A(S)`-part
  (`escaping_honestTypeP2A0Set_mem_honestTypeP2ASet`, since `V^S` does not escape) plus the generic
  `V`-part coprimality (`coprime_FT_signalizer_centralizerIn_typePV`);
* the `isConj → M`-conjugate obligation — the `A`–`A` and `V`–`V` cases are
  `honestTypeP2ASet_isConj_conj_in_M` / `conjClassSetIn_typePV_isConj_conj_in_M`, and the mixed case
  is the vacuity `not_isConj_honestTypeP2ASet_typePV` (the one deep `'A0`-`normedTI` pin).

This is the `S`-side Dade datum the (13.18) row-`0` cross-relation `τ_S(μ_{0j} − μ_{01}) =
η_{0j} − η_{01}` actually needs (the `μ`-differences are `A₀(S)`-supported, not `A(S)`-supported). -/
theorem dadeSupportHypothesisData_honestTypeP2A0Set [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M) (data : TypePData M) :
    Nonempty (OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M (honestTypeP2A0Set M data)) := by
  classical
  obtain ⟨K₀, U₀, hKM, hUM, hKne, hK, hU⟩ :=
    OddOrder.Peterfalvi.S15.typeP_exists_kappa_hall_pair hG hM hTP
  refine OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset_escaping_sigmaSharp hG hM
    (honestTypeP2A0Set_subset data) (honestTypeP2A0Set_ne_one data)
    (fun a ha => escaping_honestTypeP2ASet_mem_sigmaSharp hG hM hKM hUM hKne hK hU
      (escaping_honestTypeP2A0Set_mem_honestTypeP2ASet data ha))
    ?_ ?_ ?_ ?_
  · -- `isConj → M`-conjugate: A–A / A–V (vacuous) / V–A (vacuous) / V–V.
    intro a ha b hb hab
    rcases ha with hpa | hva
    · rcases hb with hpb | hvb
      · exact honestTypeP2ASet_isConj_conj_in_M hG hM hKM hUM hKne hK hU hpa hpb hab
      · exact (not_isConj_honestTypeP2ASet_typePV hG hM data hKM hUM hKne hK hU hpa hvb hab).elim
    · rcases hb with hpb | hvb
      · exact (not_isConj_honestTypeP2ASet_typePV hG hM data hKM hUM hKne hK hU hpb hva
          hab.symm).elim
      · exact OddOrder.Peterfalvi.S10.conjClassSetIn_typePV_isConj_conj_in_M data hva hvb hab
  · -- coprimality: the escaping point is in `A(S)`; `b` is in `A(S)` or `V^S`.
    intro a ha b hb
    have haA := escaping_honestTypeP2A0Set_mem_honestTypeP2ASet data ha
    have haσ := escaping_honestTypeP2ASet_mem_sigmaSharp hG hM hKM hUM hKne hK hU haA
    rcases hb with hpb | hvb
    · exact coprime_FT_signalizer_centralizerIn_honestTypeP2ASet hG hM haσ ha.2 hpb
    · exact OddOrder.Peterfalvi.S10.coprime_FT_signalizer_centralizerIn_typePV hG hM data haσ
        ha.2 hvb
  · -- nonempty: `M_σ^# ⊆ A(S) ⊆ A₀(S)`.
    obtain ⟨a, ha1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haMσ : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := a.2
    have haM' : (a : G) ∈ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM haMσ
    exact ⟨a.1, Or.inl ⟨haM', ha1', a.1,
      (Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr haMσ, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩⟩
  · -- `M`-conjugation invariance.
    intro m x hm
    exact honestTypeP2A0Set_conj_mem data hm

/-- **(13.18) `S`-instance `'A0`-Dade hypothesis**: the `Hypothesis`-level instantiation of
`dadeSupportHypothesisData_honestTypeP2A0Set` at the type-`P` maximal `S` (via `hyp.S_maximal`/
`hyp.S_isTypeP`/`hyp.Sdata`), packaging the honest full support `A₀(S) = A(S) ∪ V^S` as an
`S04.Hypothesis`.  This is the `S`-side Dade datum for the (13.18) cross-relation
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` — the `μ`-column differences are `A₀(S)`-supported (the
`V_S`-part falls outside `A(S) ⊆ S'`), so the `A(S)`-Dade `dadeHypS` cannot see them; `dadeHypS0`
is the correction.  (Its `.fullDadeIsometryData` inherits the one deep `'A0`-`normedTI` pin
`not_isConj_honestTypeP2ASet_typePV`.) -/
noncomputable def Hypothesis.dadeHypS0 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S04.Hypothesis G (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.S_maximal (hyp.S_isTypeP hG)
    hyp.Sdata).some.dade

/-- **(13.18) `S`-instance `'A0`-Dade `H`-conjugation invariance**: the `HConjInvariant` of
`dadeHypS0`, carried by the underlying `DadeSupportHypothesisData` (Peterfalvi (8.14)/(8.15)).  This
is the `hconj` input for `dadeHypS0.fullDadeIsometryData`, so the `'A0`-Dade isometry
`τ_S = dadeIntegralCharacterMap (dadeHypS0 hG) …` is well-defined. -/
theorem Hypothesis.dadeHypS0_hconj [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (hyp.dadeHypS0 hG).HConjInvariant :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.S_maximal (hyp.S_isTypeP hG)
    hyp.Sdata).some.hconj

/-- **`T`-instance `'A0`-Dade hypothesis** (the S↔T mirror of `dadeHypS0`): the honest
`A₀(T) = A(T) ∪ (V_T)^T` Dade datum for `T`, from the generic type-`P₂` construction
`dadeSupportHypothesisData_honestTypeP2A0Set` at `T`.  The constructor itself needs only
`IsTypeP T`, so it is taken as a parameter together with a `T`-side reconciled
`TypePData` (supplied by `reconciled_typePData_T`).  This is the `τ_T` underlying the (14.3.b)
bridge image `τ_T(β_T)` (`tauTbetaGrid`). -/
noncomputable def Hypothesis.dadeHypT0 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T) :
    OddOrder.Peterfalvi.S04.Hypothesis G (honestTypeP2A0Set hyp.T Tdata) hyp.T :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.T_maximal hTP Tdata).some.dade

/-- **`T`-instance `'A0`-Dade `H`-conjugation invariance** (mirror of `dadeHypS0_hconj`). -/
theorem Hypothesis.dadeHypT0_hconj [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T) :
    (hyp.dadeHypT0 hG hTP Tdata).HConjInvariant :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.T_maximal hTP Tdata).some.hconj

/-- **`dadeHypS0.H a = ftSupportKernel S (A₀(S)) a`** (A₀ analogue of `dadeHypS_H_eq_ftSupportKernel`).
The `'A0(S)`-instance Dade stabilizer at a support point `a` is the faithful (8.14) signalizer
kernel
`R(a) = ftSupportKernel S (A₀(S)) a`, read off the `H_eq_ftSupportKernel` field of the underlying
`DadeSupportHypothesisData` that `dadeHypS0` is projected from. -/
theorem Hypothesis.dadeHypS0_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (a : {a : G // a ∈ honestTypeP2A0Set hyp.S hyp.Sdata}) :
    (hyp.dadeHypS0 hG).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.S (honestTypeP2A0Set hyp.S hyp.Sdata) a.1 :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.S_maximal (hyp.S_isTypeP hG)
    hyp.Sdata).some.H_eq_ftSupportKernel a

/-- **All `'A0(S)`-instance Dade stabilizers vanish** (the (13.2.e) `A₀` `normedTI` conclusion): since
no `A₀(S)`-point escapes (`escaping_honestTypeP2A0Set_eq_empty`), the faithful kernel
`ftSupportKernel S (A₀(S)) a` is `⊥` at every support point
(`ftSupportKernel_eq_bot_of_not_escaping`).  This is the trivial-stabilizer input the `τ_S = Ind_S^G`
Dade=Ind bridge consumes (for (13.18.c) `⟨Γ,1_G⟩ = 0` and pin C `tauS_mu_row0_vanish_on_V`). -/
theorem Hypothesis.forall_dadeHypS0_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) :
    ∀ a : {a : G // a ∈ honestTypeP2A0Set hyp.S hyp.Sdata}, (hyp.dadeHypS0 hG).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypS0_H_eq_ftSupportKernel hG a]
  have hempty := escaping_honestTypeP2A0Set_eq_empty hG hnoV hyp.S_maximal
    (hyp.S_isTypeP hG) hyp.Sdata
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (fun hesc => Set.notMem_empty a.1 (hempty ▸ hesc))

open OddOrder.RepresentationTheory in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`τ_S = Ind_S^G` on `A₀(S)`-supported functions** (the honest `'A0`-Dade=Ind bridge): for `f`
supported in `A₀(S)`, the `'A0(S)`-Dade lift `dadeIntegralCharacterMap (dadeHypS0 …) f` equals plain
induction `Ind_S^G f`.  All `'A0(S)`-instance Dade stabilizers vanish
(`forall_dadeHypS0_H_eq_bot`, the (13.2.e) `A₀` `normedTI`), so on the `A₀(S)`-supported span the
Dade map coincides with the induction map (`dadeMap_eq_induce_of_supported_on_trivial_H` at the full
support `A₁ = A₀(S)`).  This is the `'A0` analogue of `sInstance_dade_eq_induce`; it is the
`τ_S = Ind` half of (13.18.c) `⟨Γ,1_G⟩ = 0` (`gammaGrid_orthogonal_one`) and of pin C
`tauS_mu_row0_vanish_on_V` (both additionally need prime-`TI` `μ`-value content, issue 9014). -/
theorem Hypothesis.sInstance_dade0_eq_induce [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {f : ClassFunction ↥hyp.S ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) f
      = ClassFunction.induce hyp.S f := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) hf]
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H (hyp.dadeHypS0 hG)
    (subset_refl _)
    (fun l _ ha => (honestTypeP2A0Set_conj_mem hyp.Sdata l.2).mpr ha)
    (fun a => by
      rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H]
      exact hyp.forall_dadeHypS0_H_eq_bot hG hnoV ⟨a.1, a.2⟩)
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The type-`P₂` `Hypothesis46`-for-`S`** (issue 9076 piece 4c-4; the (13.18) pin-2/3 route).
Assembles the §6 certain-type `Hypothesis46 (honestTypeP2ASet S) ↥S` from the type-uniform
constructor `hypothesis46OfTypePData` (`S13_PrimeTIResidueBridge`): the type-`P` datum `hyp.Sdata`
(with `IsTypeP S` from `S_nonI`), the honest `A(S)`-support with its `'A0(S)`-Dade `dadeHypS0`, and
the kernel-family subgroup `subH = M_σ` — for which the covering `A(S) = ⋃_{z∈M_σ#} C_{S'}(z)#`
holds
(`mem_honestTypeP2ASet`).  This supplies the `certainTypeDiffSupported` /
`certainType_diff_dade_apply_eq_of_mem_V` residue facts behind the `(13.18)` support/`V`-value pins
(`tauS_mu_row0_diff_support` / `tauS_mu_row0_vanish_on_V`), which then discharge once `hyp.mu` is
grounded to `residueS.mu2` (b-side grid field, cf. `mu_row0_ne`).  **Ungated** — pure structural
assembly (no grounding needed to *build* the `Hypothesis46`). -/
noncomputable def Hypothesis.hyp46S [Finite G] (hyp : Hypothesis (G := G))
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (honestTypeP2ASet hyp.S) hyp.S :=
  hypothesis46OfTypePData hG hyp.S_maximal
    (hyp.S_isTypeP hG) hyp.Sdata hG.odd
    (honestTypeP2ASet hyp.S) (hyp.dadeHypS0 hG) (hyp.dadeHypS0_hconj hG)
    (fun l _ ha => honestTypeP2ASet_conj_mem l.2 ha)
    ((OddOrder.BG.Ch3.S10.Msigma hyp.S).subgroupOf hyp.S)
    (by rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance)
    (by
      -- `W₂ ≤ H = maxNilpotentNormalHall S ≤ M_σ` (`W2_le`/`H_eq` +
      -- `maxNilpotentNormalHall_le_Msigma`).
      refine Subgroup.subgroupOf_mono hyp.S ?_
      have hW2H : hyp.Sdata.W2 ≤ hyp.Sdata.H := le_trans hyp.Sdata.W2_le inf_le_left
      rw [hyp.Sdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal))
    (by
      -- `M_σ ≤ S'` (`Msigma_le_derived`).
      exact Subgroup.subgroupOf_mono hyp.S
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hyp.S_maximal))
    (by
      -- **`A_covers`**: for `hh ∈ M_σ#` and `x ∈ C_S(hh) ⊓ S'` with `x ≠ 1`, the point `↑x` lies in
      -- `A(S) = ⋃_{z∈M_σ#} C_{S'}(z)#` — witnessed by `z = ↑hh` (the covering
      -- `mem_honestTypeP2ASet`).
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [Subgroup.mem_subgroupOf] at hxD hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [mem_honestTypeP2ASet]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · -- `↑x ≠ 1`
        simpa using hx1
      · -- `↑hh ≠ 1`
        simpa using hh1
      · -- `↑x ∈ C_G(↑hh)` from `x ∈ C_S(hh)`
        rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥hyp.S) rfl
        have := congrArg (hyp.S.subtype) hcomm
        simpa using this)

/-! ### Prime-`TI` pins for the (13.18) `S`-side cross-relation (issue 9076 piece 4c-4)

The three isolated prime-`TI` obligations behind `tauS_mu_row0_cross`
(`τ_S(μ_{0j} − μ_{0,#1}) = η_{0j} − η_{0,#1}`, `S15_SAndT.lean`).  Once these are discharged the
cross-relation is a pure assembly around the (3.8) rigidity engine `S16.eta_diff_rigidity` (issue
9076 piece 4b) + the `'A0(S)`-Dade isometry.  They are the `S`-side instances of the Coq prime-`TI`
lemmas (`prTIres`/`prDade_sub_TIirr_on`/`prTIirr_id`, `PFsection4.v`), the shared prime-`TI` residue
foundation tracked in issue 9014. -/

open scoped FiniteInduce in
/-- **Prime-`TI` row-`0` cross-column distinctness** (issue 9076 piece 4c-4): distinct columns of
row `0` carry distinct `μ`-entries, `μ_{0j} ≠ μ_{0,#1}` for `j ≠ #1`.  This is the cross-column
injectivity of the prime-`TI` residue grid: the `μ_{ij}` are pairwise-distinct irreducibles across
the *whole* grid (Coq: the residues `prTIres i j` are distinct for distinct `(i, j)`).  The
`Hypothesis` structure records only the *within-column* distinctness `mu_col_injective`; this
row-direction distinctness is the missing prime-`TI` fact.  Prime-`TI` theory, cf. issue 9014. -/
theorem Hypothesis.mu_row0_ne [Finite G] (hyp : Hypothesis (G := G)) {j : Fin hyp.p}
    (hj : j ≠ ⟨1, by have := hyp.three_le_p; omega⟩) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j
      ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  intro heq
  -- The diagonal value `⟨μ_{0,#1}, μ_{0,#1}⟩ = 1` (irreducibility, `mu_irreducible`).
  have hdiag : OddOrder.RepresentationTheory.ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 1 :=
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩).inner_self_eq_one
  -- The off-diagonal (row-`0` cross-column) value `⟨μ_{0j}, μ_{0,#1}⟩ = 0` (`j ≠ #1`) is the
  -- prime-`TI` grounding: the full-grid orthonormality field `mu_orthonormal` (b-side, issues
  -- 9076/3002/9014), discharged in the spine by `Section16CharacterData.muS_orthonormal`
  -- (`muS = columnFamily.mu = residueS.mu2`, cf. `S13_PrimeTIResidueBridge`).
  have hoff : OddOrder.RepresentationTheory.ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
    rw [hyp.mu_orthonormal]
    exact if_neg (fun hc => hj hc.2)
  rw [heq, hdiag] at hoff
  exact one_ne_zero hoff


open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (4.8) conclusion (1) on the `S`-side residue grid** — the `S`-instance of Coq
`prDade_sub_TIirr_on` (`PFsection4.v:838`), **with Coq's exact hypotheses**: for *nontrivial*
columns `j, k ≠ 0` of *equal degree* (`mu2_ i j 1%g = mu2_ i k 1%g` is an explicit hypothesis of
the Coq lemma, discharged by its §13/§14 consumers from the concrete degree values), the
residue-column difference `μ2_{ij} − μ2_{ik}` is supported in `A₀(S) = A(S) ∪ V^S`.

This is the *engine* of the `(13.18)` support pin `tauS_mu_row0_diff_support` (at `i = 0`): once
`hyp.mu` is grounded to the residue grid (`hyp.mu = residueS.mu2`, the b-side grid-property field
of issues 9076/3002) *and* the pin signature carries the honest `(j : ℕ) ≠ 0` (the 9076 over-claim
fix — the hypothesis shape here matches the consumer's `_hj` verbatim), the pin is this theorem
after rewriting — with the degree hypothesis supplied, as in Coq, by the concrete §13 degree facts
of the grounded grid.  Proven by instantiating the §6 certain-type support bound
`certainType_diff_supp_subset_A0` at the type-`P₂` `Hypothesis46` `hyp46S` (whose support is the
honest `A(S)`, so the conclusion is `A₀(S)`-membership definitionally). -/
theorem Hypothesis.residueS_mu2_diff_support [Finite G] (hyp : Hypothesis (G := G))
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [NeZero (Nat.card ↥(hyp.s06S hG).W1)] [NeZero (Nat.card ↥(hyp.s06S hG).W2)]
    (i : Fin (Nat.card ↥(hyp.s06S hG).W1)) {j k : Fin (Nat.card ↥(hyp.s06S hG).W2)}
    (hj0 : (j : ℕ) ≠ 0) (hk0 : (k : ℕ) ≠ 0)
    (hdeg : ((hyp.residueS hG).mu2 i j
            : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ) 1
          = ((hyp.residueS hG).mu2 i k
            : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ) 1) :
    (((hyp.residueS hG).mu2 i j : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ)
        - ((hyp.residueS hG).mu2 i k
            : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S := by
  classical
  -- `Prop`-side bridge: the §6 lemma searches for the `hyp46S`-form `NeZero` (data instances all
  -- come from the scoped `FiniteInduce` constants, so they unify without bridging)
  haveI : NeZero (Nat.card ↥(hyp.hyp46S hG).W1) :=
    inferInstanceAs (NeZero (Nat.card ↥(hyp.s06S hG).W1))
  -- nontrivial columns: the enumeration sends only `0` to the trivial character
  have hχj : (hyp.s06S hG).charGroupW2Equiv j ≠ 1 := by
    intro hc
    have h0 : j = 0 := (hyp.s06S hG).charGroupW2Equiv.injective
      (hc.trans (OddOrder.Peterfalvi.S06.Hypothesis.charGroupW2Equiv_zero
        (h := hyp.s06S hG)).symm)
    exact hj0 (by simp [h0])
  have hχk : (hyp.s06S hG).charGroupW2Equiv k ≠ 1 := by
    intro hc
    have h0 : k = 0 := (hyp.s06S hG).charGroupW2Equiv.injective
      (hc.trans (OddOrder.Peterfalvi.S06.Hypothesis.charGroupW2Equiv_zero
        (h := hyp.s06S hG)).symm)
    exact hk0 (by simp [h0])
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact OddOrder.Peterfalvi.S06.certainType_diff_supp_subset_A0 (hyp.hyp46S hG).toCore
    hχj hχk i hdeg hz

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (4.8) step (4) on the `S`-side residue grid, through the `'A0(S)`-Dade lift** —
the `S`-instance of the value identity behind Coq `prTIirr_id`/`prDade_sub_TIirr` on the regular
set `V_S = W ∖ (W₁ ∪ W₂)`: for nontrivial equal-degree columns `j, k ≠ 0` and a *regular* point
`v`, the `'A0(S)`-Dade image of the residue-column difference evaluates to the signed certain-type
`σ`-image difference `τ_S(μ2_{ij} − μ2_{ik})(v) = δ · (ω^σ_{ij}(v) − ω^σ_{ik}(v))`.

This is the *engine* of the `(13.18)` `V`-value pin `tauS_mu_row0_vanish_on_V` (at `i = 0`): the
Dade side is fully discharged — the lift agrees with the Dade map on `A₀(S)`-supported inputs
(`dadeIntegralCharacterMap_apply_of_support`, support by the proven `residueS_mu2_diff_support`),
and the value identity is the §6 `certainType_diff_dade_apply_eq_of_mem_V` at `hyp46S`.  What
remains for the pin is *only* the grid grounding: `hyp.mu = residueS.mu2` (b-side field, issues
9076/3002) together with the `ω^σ`/`η`-grid identification (`η_{ij} = δ·ω^σ_{ij}` on the regular
set, the (3.5)/(13.1.d) spine-grid correspondence) — after which the pin's vanishing statement is
this identity minus itself. -/
theorem Hypothesis.residueS_mu2_diff_dade_apply_of_mem_V [Finite G]
    (hyp : Hypothesis (G := G)) (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [NeZero (Nat.card ↥(hyp.s06S hG).W1)] [NeZero (Nat.card ↥(hyp.s06S hG).W2)]
    [NeZero (Nat.card ↥(hyp.hyp46S hG).W1)]
    (i : Fin (Nat.card ↥(hyp.s06S hG).W1)) {j k : Fin (Nat.card ↥(hyp.s06S hG).W2)}
    (hj0 : (j : ℕ) ≠ 0) (hk0 : (k : ℕ) ≠ 0)
    (hdeg : ((hyp.residueS hG).mu2 i j
            : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ) 1
          = ((hyp.residueS hG).mu2 i k
            : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ) 1)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (hyp.hyp46S hG)).V) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
        (((hyp.residueS hG).mu2 i j : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ)
          - ((hyp.residueS hG).mu2 i k
              : OddOrder.RepresentationTheory.ClassFunction ↥hyp.S ℂ)) v
      = (((hyp.hyp46S hG).columnFamily ((hyp.s06S hG).charGroupW2Equiv j)).sign : ℂ)
        * (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma (hyp.hyp46S hG)
              ((hyp.s06S hG).charGroupW2Equiv j) i v
          - OddOrder.Peterfalvi.S06.certainTypeOmegaSigma (hyp.hyp46S hG)
              ((hyp.s06S hG).charGroupW2Equiv k) i v) := by
  classical
  have hχj : (hyp.s06S hG).charGroupW2Equiv j ≠ 1 := by
    intro hc
    have h0 : j = 0 := (hyp.s06S hG).charGroupW2Equiv.injective
      (hc.trans (OddOrder.Peterfalvi.S06.Hypothesis.charGroupW2Equiv_zero
        (h := hyp.s06S hG)).symm)
    exact hj0 (by simp [h0])
  have hχk : (hyp.s06S hG).charGroupW2Equiv k ≠ 1 := by
    intro hc
    have h0 : k = 0 := (hyp.s06S hG).charGroupW2Equiv.injective
      (hc.trans (OddOrder.Peterfalvi.S06.Hypothesis.charGroupW2Equiv_zero
        (h := hyp.s06S hG)).symm)
    exact hk0 (by simp [h0])
  -- the `'A0(S)`-support of the difference: the proven support engine
  have hsupp := hyp.residueS_mu2_diff_support hG i hj0 hk0 hdeg
  -- Dade lift = Dade map on supported inputs
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) hsupp]
  -- the supported element is `certainTypeDiffSupported` (same underlying function), and the Dade
  -- map is `hyp46S.tau.toDadeMap` (`dadeIsometryData_toDadeMap`, `rfl`); conclude by the §6
  -- certain-type value identity on the regular set.
  have hφ : (⟨_, (OddOrder.RepresentationTheory.ClassFunction.mem_supportedSubmodule).mpr hsupp⟩
        : OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
            (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S)
      = OddOrder.Peterfalvi.S06.certainTypeDiffSupported (hyp.hyp46S hG).toCore hχj hχk i hdeg :=
    Subtype.ext rfl
  rw [hφ]
  exact OddOrder.Peterfalvi.S06.certainType_diff_dade_apply_eq_of_mem_V
    (hyp.hyp46S hG) hχj hχk i hdeg hv

/-- **Prime-`TI` support pin, proven** (Coq `prDade_sub_TIirr_on`, `PFsection4.v`): the `μ`-column
difference `μ_{0j} − μ_{0,#1}` is supported inside `A₀(S) = A(S) ∪ V^S` — its support meets `S`
only in `P^# ∪ V_S`, because the two prime-`TI` residues share the same `1_S`-part off `A₀(S)` and
it cancels in the difference.  This is the `S`-side instance of Coq `prDade_sub_TIirr_on`
(`μ2_{ij} − μ2_{ik} ∈ 'CF(S, 'A0)`).

**Honest signature (issue 9076, 2026-07-11)**: carries `(hj0 : (j:ℕ) ≠ 0)` — the unrestricted
`∀ j` form is *false* at the trivial column `j = 0` (`μ_{00}(1) = 1 ≠ μ_{0,#1}(1)`, and `1 ∉ A₀`).
The sole consumer `tauS_mu_row0_cross` (S15_SAndT) passes its `_hj`.

**Fully discharged (2026-07-11)**: the support claim is the `(13.18)` grounding field
`mu_diff_support` (issue 9081: producer-supplied by the proven
`Section16CharacterData.muS_diff_support`, Dade-free via `hyp46SmpCore`), and the degree
hypothesis is the proven per-entry degree `mu_apply_one_eq_u` (Pf (13.3)(a): `μ_{ij}(1) = u` for
`j ≠ 0`, via `mu_j_isIndPC` + `H_index_eq_uq`) — the same two steps Coq's `defGamma` uses
(`prDade_sub_TIirr` + the `FTprTIred1` `mulfI`-cancellation, `PFsection13.v:1909`). -/
theorem Hypothesis.tauS_mu_row0_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj0 : (j : ℕ) ≠ 0) :
    (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S :=
  hyp.mu_diff_support ⟨0, hyp.q_prime.pos⟩
    (fun h => hj0 (congrArg Fin.val h))
    (fun h => one_ne_zero (congrArg Fin.val h))
    ((hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j
        (fun h => hj0 (congrArg Fin.val h))).trans
      (hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩
        ⟨1, by have := hyp.three_le_p; omega⟩
        (fun h => one_ne_zero (congrArg Fin.val h))).symm)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Prime-`TI` `V`-value pin** (Coq `prTIirr_id` + Dade `Dade_id` on the regular set): on the
regular classes `conjClassSet(W \ (W₁ ∪ W₂)) = V^S`, the `'A0(S)`-Dade lift
`τ_S(μ_{0j} − μ_{0,#1})` agrees with the grid difference `η_{0j} − η_{0,#1}`.  Both reduce to the
same `ω`-value there: `τ_S = Ind_S^G` on `A₀(S)`-support (`normedTI 'A0`, `H = ⊥`) followed by the
prime-`TI` restriction identity `μ_{0j}|_V = ω`-value (Coq `prTIirr_id`), matching
`η_{0j}|_V = ω_{0j}|_V` (the (3.3) `τ₃ = Dade` identity on `V`).  Prime-`TI` theory, cf. issue
9014.

**Honest signature (issue 9076, 2026-07-11)**: carries `(hj0 : (j:ℕ) ≠ 0)` — the `V`-value
identity is meaningful only for the residue columns `j ≠ 0` (same honest fix as
`tauS_mu_row0_diff_support`); the sole consumer `tauS_mu_row0_cross` passes its `_hj`.

**Fully discharged (2026-07-12)**: at a regular point `x ~ w` (`w ∈ V_W ⊆ A₀(S)`, the `V`-part
of the honest `A₀` at the trivial conjugator) the Dade lift evaluates by the §2.5 point formula
(`dadeIntegralCharacterMap_apply_of_support` at the proven pin-2 support, then `dadeValue_eq` at
`h = 1` — all `A₀(S)`-stabilizers vanish, `forall_dadeHypS0_H_eq_bot`), giving the `S`-value
`(μ_{0j} − μ_{0,#1})(w)`; the `(4.3.c)` grounding field `mu_apply_of_not_mem_W2` (Coq
`prTIirr_id`) with `δ_j = 1` (`delta_eq_one_S`, Pf (13.3.c)) turns it into the `ω`-difference,
which is exactly the `η`-difference value by `eta_eq_tau_omega` + `tau3_apply_of_regular`
(the (3.2.c) regular-set identity). -/
theorem Hypothesis.tauS_mu_row0_vanish_on_V [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p)
    (hj0 : (j : ℕ) ≠ 0) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
            - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
            - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
  classical
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hwW : w ∈ hyp.W := hw.1
  have hw12 : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := hw.2
  have hw2 : w ∉ (hyp.W2 : Set G) := fun h => hw12 (Or.inr h)
  have hwS : w ∈ hyp.S := ((le_of_eq hyp.W_eq_inter).trans inf_le_left) hwW
  have hconjwx : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  -- `w ∈ A₀(S)`: the `V`-part of the honest `A₀`, at the trivial conjugator
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
    constructor
    · have hWeq : (hyp.Sdata.W : Set G) = (hyp.W : Set G) := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, ← hyp.W_eq_join]
      rw [hWeq]; exact hwW
    · rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hw12
  have hwA0 : w ∈ honestTypeP2A0Set hyp.S hyp.Sdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  -- the Dade lift's value at `x ~ w·1`: the `(2.5)` point formula at the pin-2 support
  have hsupp := hyp.tauS_mu_row0_diff_support hG j hj0
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) hsupp,
    (hyp.dadeHypS0 hG).dadeMap_apply]
  have h1H : (1 : G) ∈ (hyp.dadeHypS0 hG).H ⟨w, hwA0⟩ := by
    rw [hyp.forall_dadeHypS0_H_eq_bot hG hnoV ⟨w, hwA0⟩]
    exact Subgroup.mem_bot.mpr rfl
  have hconj1 : IsConj ((⟨w, hwA0⟩ :
      {a : G // a ∈ honestTypeP2A0Set hyp.S hyp.Sdata}).1 * 1) x := by
    rw [mul_one]; exact hconjwx
  rw [(hyp.dadeHypS0 hG).dadeValue_eq _ h1H hconj1]
  -- both sides reduce to the same `ω`-difference value at `w`
  have hmu : ∀ (l : Fin hyp.p), (l : ℕ) ≠ 0 →
      hyp.mu ⟨0, hyp.q_prime.pos⟩ l ⟨w, (hyp.dadeHypS0 hG).mem_L hwA0⟩
        = hyp.omega ⟨0, hyp.q_prime.pos⟩ l ⟨w, hwW⟩ := by
    intro l hl0
    rw [hyp.mu_apply_of_not_mem_W2 ⟨0, hyp.q_prime.pos⟩ l w hwW
      ((hyp.dadeHypS0 hG).mem_L hwA0) hw2, hyp.delta_eq_one_S hG l]
    norm_num
  have heta : ∀ (l : Fin hyp.p),
      hyp.eta ⟨0, hyp.q_prime.pos⟩ l x = hyp.omega ⟨0, hyp.q_prime.pos⟩ l ⟨w, hwW⟩ := by
    intro l
    rw [(hyp.eta ⟨0, hyp.q_prime.pos⟩ l).of_isConj hconjwx.symm, hyp.eta_eq_tau_omega,
      hyp.tau3_apply_of_regular _ w hwW hw12]
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply, OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    hmu j hj0, hmu ⟨1, by have := hyp.three_le_p; omega⟩ one_ne_zero,
    heta j, heta ⟨1, by have := hyp.three_le_p; omega⟩]
  ring

/-- **Peterfalvi (4.8), full-grid `μ`-column-difference support** (issue 1017; the all-rows/all-cols
generalization of `tauS_mu_row0_diff_support`).  For any row `i` and any two nontrivial columns
`j₁, j₂ ≠ 0`, the difference `μ_{i,j₁} − μ_{i,j₂}` is supported in `A₀(S) = A(S) ∪ V^S`.  Both
columns have equal degree `u` (`mu_apply_one_eq_u`), so the (4.3.c) support grounding field
`mu_diff_support` applies.  This is the support input the general prime-`TI` cross-relation
`tauS_mu_cross` (`S15_BridgeCharacter`) consumes on each row of a reducible μ-column difference. -/
theorem Hypothesis.tauS_mu_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) {j1 j2 : Fin hyp.p}
    (hj1 : j1 ≠ ⟨0, hyp.p_prime.pos⟩) (hj2 : j2 ≠ ⟨0, hyp.p_prime.pos⟩) :
    (hyp.mu i j1 - hyp.mu i j2).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S :=
  hyp.mu_diff_support i hj1 hj2
    ((hyp.mu_apply_one_eq_u hG i j1 hj1).trans (hyp.mu_apply_one_eq_u hG i j2 hj2).symm)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Prime-`TI` `V`-value pin, full-grid form** (the all-rows/all-cols generalization of
`tauS_mu_row0_vanish_on_V`).  On the regular set `V^S = conjClassSet(W ∖ (W₁ ∪ W₂))`, for any row
`i` and columns `j₁, j₂` (arbitrary — the value identity `mu_apply_of_not_mem_W2` holds off `W₂`
regardless of column), the `'A0(S)`-Dade lift `τ_S(μ_{i,j₁} − μ_{i,j₂})` agrees with the grid
difference `η_{i,j₁} − η_{i,j₂}`.  Both reduce to the same `ω`-value there (`μ_{i,l}|_V = δ_l·ω = ω`
by `mu_apply_of_not_mem_W2` + `delta_eq_one_S`; `η_{i,l}|_V = ω` by `eta_eq_tau_omega` +
`tau3_apply_of_regular`).  The nontriviality `j₁, j₂ ≠ 0` is only needed for the *support* input
`tauS_mu_diff_support`. -/
theorem Hypothesis.tauS_mu_vanish_on_V [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q)
    {j1 j2 : Fin hyp.p}
    (hj1 : j1 ≠ ⟨0, hyp.p_prime.pos⟩) (hj2 : j2 ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          (hyp.mu i j1 - hyp.mu i j2)
        - (hyp.eta i j1 - hyp.eta i j2)) x = 0 := by
  classical
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hwW : w ∈ hyp.W := hw.1
  have hw12 : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := hw.2
  have hw2 : w ∉ (hyp.W2 : Set G) := fun h => hw12 (Or.inr h)
  have hwS : w ∈ hyp.S := ((le_of_eq hyp.W_eq_inter).trans inf_le_left) hwW
  have hconjwx : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
    constructor
    · have hWeq : (hyp.Sdata.W : Set G) = (hyp.W : Set G) := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, ← hyp.W_eq_join]
      rw [hWeq]; exact hwW
    · rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hw12
  have hwA0 : w ∈ honestTypeP2A0Set hyp.S hyp.Sdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  have hsupp := hyp.tauS_mu_diff_support hG i hj1 hj2
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) hsupp,
    (hyp.dadeHypS0 hG).dadeMap_apply]
  have h1H : (1 : G) ∈ (hyp.dadeHypS0 hG).H ⟨w, hwA0⟩ := by
    rw [hyp.forall_dadeHypS0_H_eq_bot hG hnoV ⟨w, hwA0⟩]
    exact Subgroup.mem_bot.mpr rfl
  have hconj1 : IsConj ((⟨w, hwA0⟩ :
      {a : G // a ∈ honestTypeP2A0Set hyp.S hyp.Sdata}).1 * 1) x := by
    rw [mul_one]; exact hconjwx
  rw [(hyp.dadeHypS0 hG).dadeValue_eq _ h1H hconj1]
  have hmu : ∀ (l : Fin hyp.p),
      hyp.mu i l ⟨w, (hyp.dadeHypS0 hG).mem_L hwA0⟩ = hyp.omega i l ⟨w, hwW⟩ := by
    intro l
    rw [hyp.mu_apply_of_not_mem_W2 i l w hwW
      ((hyp.dadeHypS0 hG).mem_L hwA0) hw2, hyp.delta_eq_one_S hG l]
    norm_num
  have heta : ∀ (l : Fin hyp.p), hyp.eta i l x = hyp.omega i l ⟨w, hwW⟩ := by
    intro l
    rw [(hyp.eta i l).of_isConj hconjwx.symm, hyp.eta_eq_tau_omega,
      hyp.tau3_apply_of_regular _ w hwW hw12]
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.RepresentationTheory.ClassFunction.sub_apply, hmu j1, hmu j2, heta j1, heta j2]
  ring


/-- **`dadeHypT0.H a = ftSupportKernel T (A₀(T)) a`** (mirror of
`dadeHypS0_H_eq_ftSupportKernel`). -/
theorem Hypothesis.dadeHypT0_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T)
    (a : {a : G // a ∈ honestTypeP2A0Set hyp.T Tdata}) :
    (hyp.dadeHypT0 hG hTP Tdata).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.T (honestTypeP2A0Set hyp.T Tdata) a.1 :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.T_maximal hTP
    Tdata).some.H_eq_ftSupportKernel a

/-- **All `'A0(T)`-instance Dade stabilizers vanish** (mirror of
`forall_dadeHypS0_H_eq_bot`; the `T`-side (13.2.e) `A₀` `normedTI` conclusion, from the generic
`escaping_honestTypeP2A0Set_eq_empty` at the (14.9)-parametric `hTP`/`Tdata`). -/
theorem Hypothesis.forall_dadeHypT0_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T) :
    ∀ a : {a : G // a ∈ honestTypeP2A0Set hyp.T Tdata},
      (hyp.dadeHypT0 hG hTP Tdata).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypT0_H_eq_ftSupportKernel hG hTP Tdata a]
  have hempty := escaping_honestTypeP2A0Set_eq_empty hG hnoV hyp.T_maximal hTP Tdata
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (fun hesc => Set.notMem_empty a.1 (hempty ▸ hesc))

/-- **Peterfalvi (4.8), full-grid `ν`-row-difference support** (mirror of
`tauS_mu_diff_support`): for any column `j` and nontrivial rows `r, s ≠ 0`, the difference
`ν_{r,j} − ν_{s,j}` is supported in `A₀(T) = A(T) ∪ (V_T)^T` — both rows have equal degree `v`
(`nu_apply_one_eq_v`), so the (4.8)-at-`T` grid field `nu_diff_support` applies. -/
theorem Hypothesis.tauT_nu_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (j : Fin hyp.p) {r s : Fin hyp.q}
    (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) :
    (hyp.nu r j - hyp.nu s j).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.T Tdata) hyp.T :=
  pins.nu_diff_support Tdata hU hW1 hW2 j hr hs
    ((hyp.nu_apply_one_eq_v hG pins r j hr).trans
      (hyp.nu_apply_one_eq_v hG pins s j hs).symm)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Prime-`TI` `V`-value pin, `T`-side full-grid form** (mirror of `tauS_mu_vanish_on_V`):
on the regular set `(V_T)^T = conjClassSet(W ∖ (W₁ ∪ W₂))`, the `'A0(T)`-Dade lift
`τ_T(ν_{r,j} − ν_{s,j})` agrees with the grid difference `η_{r,j} − η_{s,j}` — both reduce to
the same `ω`-value (`ν_{l,j}|_V = δ'_l·ω = ω` by `nu_apply_of_not_mem_W1` +
`deltaPrime_eq_one_pins`; `η|_V = ω` by `eta_eq_tau_omega` + `tau3_apply_of_regular`). -/
theorem Hypothesis.tauT_nu_vanish_on_V [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (j : Fin hyp.p) {r s : Fin hyp.q}
    (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
          ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hTP Tdata))
          (hyp.nu r j - hyp.nu s j)
        - (hyp.eta r j - hyp.eta s j)) x = 0 := by
  classical
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hwW : w ∈ hyp.W := hw.1
  have hw12 : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := hw.2
  have hw1 : w ∉ (hyp.W1 : Set G) := fun h => hw12 (Or.inl h)
  have hwT : w ∈ hyp.T := ((le_of_eq hyp.W_eq_inter).trans inf_le_right) hwW
  have hconjwx : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.T Tdata := by
    constructor
    · have hWeq : (Tdata.W : Set G) = (hyp.W : Set G) := by
        rw [Tdata.W_eq, hW1, hW2, sup_comm, ← hyp.W_eq_join]
      rw [hWeq]; exact hwW
    · rw [hW1, hW2, Set.union_comm]; exact hw12
  have hwA0 : w ∈ honestTypeP2A0Set hyp.T Tdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  have hsupp := hyp.tauT_nu_diff_support hG pins Tdata hU hW1 hW2 j hr hs
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      (hyp.dadeHypT0 hG hTP Tdata)
      ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hTP Tdata))
      hsupp,
    (hyp.dadeHypT0 hG hTP Tdata).dadeMap_apply]
  have h1H : (1 : G) ∈ (hyp.dadeHypT0 hG hTP Tdata).H ⟨w, hwA0⟩ := by
    rw [hyp.forall_dadeHypT0_H_eq_bot hG hnoV hTP Tdata ⟨w, hwA0⟩]
    exact Subgroup.mem_bot.mpr rfl
  have hconj1 : IsConj ((⟨w, hwA0⟩ :
      {a : G // a ∈ honestTypeP2A0Set hyp.T Tdata}).1 * 1) x := by
    rw [mul_one]; exact hconjwx
  rw [(hyp.dadeHypT0 hG hTP Tdata).dadeValue_eq _ h1H hconj1]
  have hnu : ∀ (l : Fin hyp.q),
      hyp.nu l j ⟨w, (hyp.dadeHypT0 hG hTP Tdata).mem_L hwA0⟩ = hyp.omega l j ⟨w, hwW⟩ := by
    intro l
    rw [pins.nu_apply_of_not_mem_W1 l j w hwW
      ((hyp.dadeHypT0 hG hTP Tdata).mem_L hwA0) hw1, hyp.deltaPrime_eq_one_pins hG pins l]
    norm_num
  have heta : ∀ (l : Fin hyp.q), hyp.eta l j x = hyp.omega l j ⟨w, hwW⟩ := by
    intro l
    rw [(hyp.eta l j).of_isConj hconjwx.symm, hyp.eta_eq_tau_omega,
      hyp.tau3_apply_of_regular _ w hwW hw12]
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.RepresentationTheory.ClassFunction.sub_apply, hnu r, hnu s, heta r, heta s]
  ring


/-- **`dadeHypT.H a = ftSupportKernel T (A(T)) a`** (mirror of
`dadeHypS_H_eq_ftSupportKernel`). -/
theorem Hypothesis.dadeHypT_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (a : {a : G // a ∈ honestTypeP2ASet hyp.T}) :
    (hyp.dadeHypT hG hTP).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.T (honestTypeP2ASet hyp.T) a.1 :=
  (dadeSupportHypothesisData_honestTypeP2ASet hG hyp.T_maximal hTP).some.H_eq_ftSupportKernel a

/-- **No `A(T)`-point escapes `T`** (mirror of `no_escaping_honestTypeP2ASet`, at the
(14.9)-parametric `hTP`). -/
theorem Hypothesis.no_escaping_honestTypeP2ASet_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) :
    ∀ a ∈ honestTypeP2ASet hyp.T,
      a ∉ OddOrder.GroupTheory.escapingCentralizerSet hyp.T (honestTypeP2ASet hyp.T) := by
  intro a _ ha
  rw [escaping_honestTypeP2ASet_eq_empty hG hnoV hyp.T_maximal hTP] at ha
  exact Set.notMem_empty a ha

/-- **(13.2.e)-at-`T`, stabilizer form: every `T`-instance Dade stabilizer is trivial**
(mirror of `forall_dadeHypS_H_eq_bot`). -/
theorem Hypothesis.forall_dadeHypT_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) :
    ∀ a : {a : G // a ∈ honestTypeP2ASet hyp.T}, (hyp.dadeHypT hG hTP).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypT_H_eq_ftSupportKernel hG hTP a]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (hyp.no_escaping_honestTypeP2ASet_T hG hnoV hTP a.1 a.2)

open OddOrder.RepresentationTheory in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`τ_T = Ind_T^G` on `A(T)`-supported functions** (mirror of `sInstance_dade_eq_induce`):
the `T`-instance `A(T)`-Dade isometry agrees with plain induction on every `A(T)`-supported
class function. -/
theorem Hypothesis.tInstance_dade_eq_induce [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    {f : ClassFunction ↥hyp.T ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData (hyp.dadeHypT_hconj hG hTP)) f
      = ClassFunction.induce hyp.T f := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypT hG hTP)
    ((hyp.dadeHypT hG hTP).fullDadeIsometryData (hyp.dadeHypT_hconj hG hTP)) hf]
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H
    (hyp.dadeHypT hG hTP)
    (subset_refl _)
    (fun l _ ha => honestTypeP2ASet_conj_mem l.2 ha)
    (fun a => by
      rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H]
      exact hyp.forall_dadeHypT_H_eq_bot hG hnoV hTP ⟨a.1, a.2⟩)
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

open OddOrder.RepresentationTheory in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`τ_T⁰ = Ind_T^G` on `A₀(T)`-supported functions** (mirror of
`sInstance_dade0_eq_induce`, from the `A₀(T)` normedTI `forall_dadeHypT0_H_eq_bot`). -/
theorem Hypothesis.tInstance_dade0_eq_induce [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T)
    {f : ClassFunction ↥hyp.T ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.T Tdata) hyp.T) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
        ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hTP Tdata)) f
      = ClassFunction.induce hyp.T f := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    (hyp.dadeHypT0 hG hTP Tdata)
    ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hTP Tdata)) hf]
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H
    (hyp.dadeHypT0 hG hTP Tdata)
    (subset_refl _)
    (fun l _ ha => (honestTypeP2A0Set_conj_mem Tdata l.2).mpr ha)
    (fun a => by
      rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H]
      exact hyp.forall_dadeHypT0_H_eq_bot hG hnoV hTP Tdata ⟨a.1, a.2⟩)
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

end OddOrder.Peterfalvi.S15
