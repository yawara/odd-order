/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_MinimalSimpleStructure

/-!
# Peterfalvi (8.15) claim 1 for the book-literal type-`𝒫` support `A₀(M) = A(M) ∪ V^M`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, (8.10)/(8.15), pp. 47-48.

The Dade (2.2) support hypotheses for the honest type-`𝒫` support
`A₀(M) = A(M) ∪ V^M` (`S10.typePACore0`), together with the containment / conjugacy /
coprimality facts its assembly needs.

**Why this file exists** (issue 1046): all of this is §8 content — every statement is about a bare
`M : Subgroup G` with `TypePData M` / `IsTypeP M`, and none of it mentions the §13 `S`/`T` setup —
but it used to live in `S15_HonestTypeP2A0.lean` (namespace `S15`), i.e. *downstream* of the
§8/§10 layer that consumes it.  Same layering inversion as `sSet_finite` and
`dadeSupportHypothesisData_typePACore`, fixed in the same pass.

⚠ `escaping_typePACore0_eq_empty` deliberately stays behind in `S15_HonestTypeP2A0`: it is *not*
part of this closure and genuinely depends on §14 (`S14.typeI_frobenius`).
-/

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- `A(S) ⊆ A₀(S)`: the honest type-`P₂` support is contained in its `A₀`-completion. -/
theorem typePACore_subset_A0Set {M : Subgroup G} (data : TypePData M) :
    S10.typePACore M ⊆ S10.typePACore0 M data :=
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
the `S10.typePACore0 ⊆ A0Set` bridge).  A `V = typePV`-point `v = a·b` (`a ∈ W₁`, `b ∈ W₂`, the
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

/-- `A₀(S) ⊆ M`: both the `A(S)`-part (`S10.typePACore_subset`) and the `V^S`-part
(`conjClassSetIn` of the `⊆ M` regular set) land in `M`. -/
theorem typePACore0_subset {M : Subgroup G} (data : TypePData M) :
    S10.typePACore0 M data ⊆ (M : Set G) := by
  rintro x (hx | hx)
  · exact S10.typePACore_subset hx
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

/-- `1 ∉ A₀(S)`: both parts avoid the identity (`S10.typePACore_one_not_mem` and
`conjClassSetIn_typePV_one_not_mem`). -/
theorem typePACore0_one_not_mem {M : Subgroup G} (data : TypePData M) :
    (1 : G) ∉ S10.typePACore0 M data := by
  rintro (h | h)
  · exact S10.typePACore_one_not_mem h
  · exact conjClassSetIn_typePV_one_not_mem data h

/-- **`A₀(S)` is `M`-conjugation invariant**: both `A(S)` (`S10.typePACore_conj_mem`) and `V^S`
(`mem_conjClassSetIn_conj_iff`) are stable under conjugation by `m ∈ M`. -/
theorem typePACore0_conj_mem [Finite G] {M : Subgroup G} (data : TypePData M) {m : G}
    (hm : m ∈ M) {x : G} :
    m * x * m⁻¹ ∈ S10.typePACore0 M data ↔ x ∈ S10.typePACore0 M data := by
  simp only [S10.typePACore0, Set.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl (by
        have := S10.typePACore_conj_mem (inv_mem hm) h
        rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at this)
    · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mp h)
  · rintro (h | h)
    · exact Or.inl (S10.typePACore_conj_mem hm h)
    · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mpr h)

/-- `∀ x ∈ A₀(S), x ≠ 1` — the `≠ 1` form of `typePACore0_one_not_mem` (the shape the
`σ`-decomposition Dade engine's `hXsharp` obligation takes). -/
theorem typePACore0_ne_one {M : Subgroup G} (data : TypePData M) :
    ∀ x ∈ S10.typePACore0 M data, x ≠ (1 : G) :=
  fun _ hx h => typePACore0_one_not_mem data (h ▸ hx)

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
there too.  This reduces the Dade engine's escaping-`σ`-sharp and coprimality obligations for
`A₀(S)` to the already-established `S10.typePACore` ones. -/
theorem escaping_typePACore0_mem_typePACore {M : Subgroup G} (data : TypePData M)
    {a : G} (ha : a ∈ escapingCentralizerSet M (S10.typePACore0 M data)) :
    a ∈ escapingCentralizerSet M (S10.typePACore M) := by
  obtain ⟨haA0, haesc⟩ := ha
  rcases haA0 with hpa | hva
  · exact ⟨hpa, haesc⟩
  · exact absurd (conjClassSetIn_typePV_centralizer_le_M data hva) haesc

/-! ### The `A₀(S) ⊆ A0Set M K₀` bridge (issue 9076 piece 4c)

The honest support `S10.typePACore0 M data = A(S) ∪ V^S` embeds into BG's Theorem-E set
`A0Set M K₀ = hatMsigma M ∖ 𝒞_G(K₀#)`.  The `A(S)`-part uses `S10.typePACore_subset_ASet`
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
(`isPiElement_conj`) and non-triviality.  This is the exclusion input for both `A(S)`
(`κ′`-elements) and `V^S` (`σ`-prime carriers) against `A0Set M K₀ = hatMsigma M ∖ 𝒞_G(K₀#)`. -/
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
regular set `V = typePV` embeds into the `A_0(M)`-set.  `V ⊆ hatMsigma M`
(`typePV_subset_hatMsigma`) extends to the closure because `hatMsigma M` is `M`-conjugation
invariant (`M_σ ◁ M`); and a `V`-point carries a `σ`-prime
(`exists_sigma_prime_dvd_orderOf_typePV`), `σ ⊆ κ′` (`kappa_subset_sigmaCompl`), so it is not a
`κ`-element, hence off the pure-`κ` set `𝒞_G(K₀#)` (conjugation-invariant,
`mem_conjClassSet_conj_iff`). -/
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
Theorem-E set.  `A(S)`-part via `S10.typePACore_subset_ASet` + `aSet_subset_A0Set`; `V^S`-part via
`conjClassSetIn_typePV_subset_A0Set`.  This is the bridge feeding `theoremII_tame_embedding` for
`typePACore0_tame_conj`. -/
theorem typePACore0_subset_A0Set [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K₀ ≤ M) (hUM : U₀ ≤ M) (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    (data : TypePData M) :
    S10.typePACore0 M data ⊆ OddOrder.BG.Ch4.S16.A0Set M K₀ := by
  apply Set.union_subset
  · exact (S10.typePACore_subset_ASet hG hM hKM hUM hKne hK hU).trans
      (aSet_subset_A0Set hG hM hKM hUM hK hU)
  · exact conjClassSetIn_typePV_subset_A0Set hG hM hKM hK data

/-- **Tame conjugation for the honest type-`P₂` `A₀`-support** (BG §16 Theorem II): two
`G`-conjugate elements of `A₀(M) = A(M) ∪ V^M` are already `M`-conjugate.  This is the first
conjunct of BG Theorem II (`OddOrder.BG.Ch4.S16.theoremII_tame_embedding` with `X = A0Set M K`): for
the tame embedding, a `G`-fusion of support points is controlled by `N_G(M) = M`.

Discharge route (issue 9076 piece 4c): bridge the honest support `S10.typePACore0 M data` into
BG's
`A0Set M K = hatMsigma M ∖ 𝒞_G(K#)` — the `A(M)`-part via `S10.typePACore_subset_hatMsigma`, the
`V^M`-part via `typePV ⊆ hatMsigma` plus the order argument `V^M ∩ 𝒞_G(K#) = ∅` (a `V`-point has
order divisible by `pq`, a `K#`-point only by `q`) — and produce the `κ`-Hall `K` / `(κ∪σ)′`-Hall
`U`
of the type-`P` maximal `M`.  With `a, b ∈ A0Set M K`, `theoremII_tame_embedding`'s first conjunct
supplies the `M`-conjugator.  (Reduces the earlier "genuine deep FT-support geometry" pin to this
concrete BG-support bridge.) -/
theorem typePACore0_tame_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {K₀ U₀ : Subgroup G} (hKM : K₀ ≤ M) (hUM : U₀ ≤ M) (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a b : G}
    (ha : a ∈ S10.typePACore0 M data) (hb : b ∈ S10.typePACore0 M data)
    (hab : IsConj a b) : ∃ m ∈ M, b = m * a * m⁻¹ := by
  have hsub := typePACore0_subset_A0Set hG hM hKM hUM hKne hK hU data
  have hII := OddOrder.BG.Ch4.S16.theoremII_tame_embedding hG hM hKM hUM hK hU
    (X := OddOrder.BG.Ch4.S16.A0Set M K₀) (Or.inr rfl)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  obtain ⟨m, hmM, hmb⟩ := hII.1 a (hsub ha) b (hsub hb) ⟨g, hg.symm⟩
  exact ⟨m, hmM, hmb⟩

/-- **(8.13.a), the mixed `A(S)`–`V^S` case is vacuous**: an `A(S)`-point is never `G`-conjugate to
a `V^S`-point.  An `A(S) = S10.typePACore` element lies in `S' = derivedInG S`, while a
`V^S`-point lies **outside** `S'` (`typePData_typePV_not_mem_derived`, the nontrivial
`W₁`-component).

Proved (issue 9076 piece 4c) via the honest-support tame conjugation `typePACore0_tame_conj`
(BG §16 Theorem II): if `a` and `b` were `G`-conjugate, they would be **`M`-conjugate**
(`b = m·a·m⁻¹`, `m ∈ M`); but `M' = derivedInG M` is normal in `M`, so `M`-conjugation preserves
`M'`-membership, forcing `b ∈ M'` from `a ∈ M'` — contradicting `b ∉ M'`.  This replaces the earlier
circular `normedTI`-based argument with the direct FT-support-geometry route (Coq `FTsupp0`). -/
theorem not_isConj_typePACore_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {K₀ U₀ : Subgroup G} (hKM : K₀ ≤ M) (hUM : U₀ ≤ M) (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a b : G}
    (ha : a ∈ S10.typePACore M) (hb : b ∈ conjClassSetIn M (typePV M data))
    (hab : IsConj a b) : False := by
  -- `M' ⊴ M`.  (In the file this was extracted from, the instance came in transitively through the
  -- §13 import closure; here it is derived on the spot — `M'.subgroupOf M` is the comap of a
  -- `map` along the injective `M.subtype`.)
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  -- `M`-conjugation preserves `M' = derivedInG M`-membership (`M' ⊴ M`).
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hconj_derived : ∀ x w : G, x ∈ M → w ∈ derivedInG M → x * w * x⁻¹ ∈ derivedInG M := by
    intro x w hxM hwD
    have hconj := (inferInstance : ((derivedInG M).subgroupOf M).Normal).conj_mem
      ⟨w, hM'le hwD⟩ (Subgroup.mem_subgroupOf.mpr hwD) ⟨x, hxM⟩
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  -- `a ∈ M'`, and (BG tame) `b ∈ A₀(M)` is `M`-conjugate to `a ∈ A(M) ⊆ A₀(M)`.
  have haD : a ∈ derivedInG M := (S10.mem_typePACore.mp ha).1
  have hbA0 : b ∈ S10.typePACore0 M data := Set.mem_union_right _ hb
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
    typePACore0_tame_conj hG hM data hKM hUM hKne hK hU
      (typePACore_subset_A0Set data ha) hbA0 hab
  exact hbnD (hmc ▸ hconj_derived m a hmM haD)

/-- **Peterfalvi (8.15) for the honest type-`P₂` `A₀`-support**: the Dade (2.2) support hypotheses
hold for `A₀(S) = A(S) ∪ V^S`.  Assembled through the `σ`-decomposition engine
`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`:

* set-facts (`⊆ M`, `≠ 1`, `M`-conjugation-invariant, nonempty) — the `typePACore0_*` facts;
* escaping-`σ`-sharp and coprimality — reduced to the `A(S)`-part
  (`escaping_typePACore0_mem_typePACore`, since `V^S` does not escape) plus the generic
  `V`-part coprimality (`coprime_FT_signalizer_centralizerIn_typePV`);
* the `isConj → M`-conjugate obligation — the `A`–`A` and `V`–`V` cases are
  `S10.typePACore_isConj_conj_in_M` / `conjClassSetIn_typePV_isConj_conj_in_M`, and the mixed case
  is the vacuity `not_isConj_typePACore_typePV` (the one deep `'A0`-`normedTI` pin).

This is the `S`-side Dade datum the (13.18) row-`0` cross-relation `τ_S(μ_{0j} − μ_{01}) =
η_{0j} − η_{01}` actually needs (the `μ`-differences are `A₀(S)`-supported, not `A(S)`-supported).
-/
theorem dadeSupportHypothesisData_typePACore0 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M) (data : TypePData M) :
    Nonempty (OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M (S10.typePACore0 M data)) := by
  classical
  obtain ⟨K₀, U₀, hKM, hUM, hKne, hK, hU⟩ :=
    OddOrder.Peterfalvi.S10.typeP_exists_kappa_hall_pair hG hM hTP
  refine OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset_escaping_sigmaSharp hG hM
    (typePACore0_subset data) (typePACore0_ne_one data)
    (fun a ha => S10.escaping_typePACore_mem_sigmaSharp hG hM hKM hUM hKne hK hU
      (escaping_typePACore0_mem_typePACore data ha))
    ?_ ?_ ?_ ?_
  · -- `isConj → M`-conjugate: A–A / A–V (vacuous) / V–A (vacuous) / V–V.
    intro a ha b hb hab
    rcases ha with hpa | hva
    · rcases hb with hpb | hvb
      · exact S10.typePACore_isConj_conj_in_M hG hM hKM hUM hKne hK hU hpa hpb hab
      · exact (not_isConj_typePACore_typePV hG hM data hKM hUM hKne hK hU hpa hvb hab).elim
    · rcases hb with hpb | hvb
      · exact (not_isConj_typePACore_typePV hG hM data hKM hUM hKne hK hU hpb hva
          hab.symm).elim
      · exact OddOrder.Peterfalvi.S10.conjClassSetIn_typePV_isConj_conj_in_M data hva hvb hab
  · -- coprimality: the escaping point is in `A(S)`; `b` is in `A(S)` or `V^S`.
    intro a ha b hb
    have haA := escaping_typePACore0_mem_typePACore data ha
    have haσ := S10.escaping_typePACore_mem_sigmaSharp hG hM hKM hUM hKne hK hU haA
    rcases hb with hpb | hvb
    · exact S10.coprime_FT_signalizer_centralizerIn_typePACore hG hM haσ ha.2 hpb
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
    exact typePACore0_conj_mem data hm

end OddOrder.Peterfalvi.S10
