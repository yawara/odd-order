/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_Section9Counts
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.Peterfalvi.S04_DadeIsometryBasic
import OddOrder.Peterfalvi.S12_TypeIIDadeBase
import OddOrder.Peterfalvi.S07_PivotCoherence
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TheoremsAE
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TaxonomyOutput
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TypeBridges
import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting.Basics

/-!
# Peterfalvi (10.7): the Type-II `HU`-Frobenius dichotomy assembly

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 10, pp. 58--59, Theorem (10.7); Coq mirror `Frob_der1_type2`
(`coq/theories/PFsection10.v:549-658`).

Under Hypothesis (10.4) (the type-`P₁` maximal `M` with its coherent extension `τ₁`),
every Type-II maximal subgroup `S` of `G` has `[S,S] = S_F ⋊ U` a **Frobenius group with
kernel `S_F`**.  The proof splits on the `S`-side §9 Clifford dichotomy
(Coq `typeP_reducible_core_cases`):

* **Exceptional (right) branch** — `𝒮(H₀C')` has no irreducible of degree `q·u`: then
  `C = ⊥`, `U` is cyclic, and the type-II `HU`-Frobenius conclusion is immediate
  (`S11.exceptional_case_frobenius_realization`, proven).
* **Reducible-core (left) branch** — an irreducible `λ ∈ 𝒮(H₀)` and a reducible
  `ν ∈ 𝒮(H₀)` of equal degree `q·u` exist: this is **refuted** by the cross-isometry
  computation of (10.7): the 4-element family `T2 = {λ, λ̄, ν, ν̄}` is coherent by (5.7)
  with an extension `τ₂`; (5.8) pins `ν^{τ₂}` to a signed `ω^σ`-row-sum of the grid
  **shared** with `M` (the (8.8) pair structure `S ∩ M = W`); the Dade supports
  `Ã₁(M)` and `Ã(S)` are disjoint ((8.18.b) via (8.13.c4), since `M` is not Frobenius
  with kernel `M_F`), so `⟨α^τ, β^{τ_S}⟩ = 0` for `α = μ_s − d·ζ`, `β = ν − λ`; expanding
  through the proven `M`-side (10.6.a) pin `μ_s^{τ₁} = δ·∑_i ω_{is}^σ`
  (`Hypothesis.muColumn_tau1_pin`) leaves the single shared grid entry
  `±⟨ω_{r's}^σ, ω_{r's}^σ⟩ = ±1 ≠ 0` — contradiction.

The left-branch cross facts (τ₂-coherence of `T2`, the `S`-side (5.8) row identity against
the shared grid, the (4.1)/(5.3.b) orthogonality of `λ^{τ₂}`, `ζ^{τ₁}` to the grid and to
each other, and the (8.18.b)-based `⟨α^τ, β^{τ_S}⟩ = 0`) are bundled as the explicit
carrier `TypeIICrossIsometryData`, produced by the (sorried) named gate
`exists_typeIICrossIsometryData` — see its docstring for the precise provenance of each
obligation.  The contradiction consumer (`TypeIICrossIsometryData.elim`) and the dichotomy
assembly (`typeII_HU_frobenius_of_coherent`) are proven.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]


/-! ## Peterfalvi (8.16) ⇒ Hypothesis (4.6) for `(A(S), S)`: the `S`-side certain-type instance

The (10.7) left branch runs the (5.7) engine over the reducible column family `R(ν)`
(`S06.certainTypeR`), which consumes an `S06.Hypothesis46 (A(S)) S` — Peterfalvi's "(8.15):
Hypothesis (4.6) holds with `L = S`, `K = S'`, `A = A(S)`, `A₀ = A₀(S)`, `H = S_F`" for the
Type-II maximal `S`.  The `M`-side precedent (`Hypothesis.toHypothesis46`) receives its
`A₀`-level Dade datum as a hoisted §10 field; here we *construct* it: Peterfalvi (8.16) claims
`A₀(S) = A(S) ∪ V^S` is also a TI-subset, and the three-case extension of the landed `A(S)`
argument proves it —

* `(A, A)`: the landed `typeII_centralizerSupport_isTISubset`;
* `(V^S, V^S)`: the (3.1)/(4.3.a) ambient TI property of `V` (`typePData_V_ti`, normalizer
  bound `W ≤ S`);
* mixed: **impossible** — `orderOf` separates the two parts.  `A(S) ⊆ (S')^#` consists of
  `π(S')`-elements, while an exceptional `v ∈ V` has a nontrivial `W₁`-component whose order
  is coprime to `|S'|` (the (4.2.a) Hall coprimality `typePData_W1_hall_coprime`), so
  `orderOf v ∤ |S'|` (`typePV_orderOf_not_dvd_card_derived`); conjugation preserves orders.

This mirrors the Coq `FTsupport0` definition (`BGsection16.v:194`), whose exceptional part is
the *order-characterized* set `{x ∈ M | x` neither a `π(M')`- nor a `π(M')'`-element`}` —
`FTsupp0_typeP` (`PFsection8.v:772`) identifies it with `V^M` for type-`P` maximals. -/

section Hypothesis46Instance

open OddOrder.BG.Ch3.S10

/-- **Type-`P` exceptional elements have order outside `π(M')`**: for `v ∈ V = W − (W₁ ∪ W₂)`,
`orderOf v ∤ |M'|`.

Decompose `v = a·b` along the cyclic (hence abelian) `W = W₁ ⊔ W₂`.  If `orderOf v` divided
`|M'|` it would be coprime to `w₁ = |W₁|` (the (4.2.a) Hall coprimality `hHall`), so
`v ∈ ⟨v^{w₁}⟩` (the power map by a coprime exponent preserves the cyclic subgroup); but
`v^{w₁} = a^{w₁}·b^{w₁} = b^{w₁} ∈ W₂` (Lagrange kills the `W₁`-component), forcing `v ∈ W₂` —
contradicting `v ∉ W₁ ∪ W₂`.

This is the conjugation-invariant separator between `A(S) ⊆ (S')^#` (whose elements are
`π(S')`-elements) and the exceptional part `V^S` of `A₀(S)` in the (8.16) TI argument; it is
the type-data form of the Coq `FTsupport0` order characterization (`BGsection16.v:194`). -/
theorem typePV_orderOf_not_dvd_card_derived [Finite G] {M : Subgroup G} (data : TypePData M)
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    {v : G} (hv : v ∈ typePV M data) :
    ¬ orderOf v ∣ Nat.card ↥(derivedInG M) := by
  intro hdvd
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at hv
  obtain ⟨hvW, -, hvnW2⟩ := hv
  -- decompose `v = a·b` along `W = W₁ ⊔ W₂` (the cyclic `W` is abelian)
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
    have := congrArg (Subtype.val) hab
    simpa using this
  -- `v^{w₁} = b^{w₁} ∈ W₂`: the `W₁`-part dies by Lagrange, the factors commute in `W`
  set w₁ := Nat.card ↥data.W1 with hw₁def
  have hcomm : Commute ((a : ↥data.W) : G) ((b : ↥data.W) : G) :=
    OddOrder.Peterfalvi.S06.commute_of_mem_of_isCyclic data.W_cyclic (hW1le haW1) (hW2le hbW2)
  have hapow : ((a : ↥data.W) : G) ^ w₁ = 1 := by
    have h1 : (⟨((a : ↥data.W) : G), haW1⟩ : ↥data.W1) ^ w₁ = 1 := pow_card_eq_one'
    have := congrArg (Subtype.val) h1
    simpa using this
  have hvpow : v ^ w₁ ∈ data.W2 := by
    rw [← habG, hcomm.mul_pow, hapow, one_mul]
    exact pow_mem hbW2 w₁
  -- coprimality: `orderOf v` is coprime to `w₁`, so `⟨v^{w₁}⟩ = ⟨v⟩ ∋ v`
  have hcop : (orderOf v).Coprime w₁ := hHall.coprime_dvd_left hdvd
  have hord : orderOf (v ^ w₁) = orderOf v := by
    rw [orderOf_pow, hcop.gcd_eq_one, Nat.div_one]
  have hzle : Subgroup.zpowers (v ^ w₁) ≤ Subgroup.zpowers v :=
    Subgroup.zpowers_le.mpr ((Subgroup.zpowers v).pow_mem (Subgroup.mem_zpowers v) w₁)
  have hzeq : Subgroup.zpowers (v ^ w₁) = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge hzle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzeq ▸ Subgroup.mem_zpowers v)
  exact hvnW2 (hk ▸ zpow_mem hvpow k)

/-- **Peterfalvi (8.16), TI part, for the full `A₀(S) = A(S) ∪ V^S`** of a Type-II maximal:
the (8.10) enlarged support `A₀(S) = A(S) ∪ conjClassSetIn S V` is a TI-subset of `G` with
normalizer bound `S`.

Four cases for `a, g·a·g⁻¹ ∈ A₀(S)`: both in `A(S)` is the landed
`typeII_centralizerSupport_isTISubset`; both in `V^S` reduces (conjugating the `S`-parts away)
to the ambient (3.1) TI property `V ∩ V^h ≠ ∅ → h ∈ W` (`typePData_V_ti`) with `W ≤ S`; and
the mixed cases are impossible because conjugation preserves element orders while `orderOf`
separates `A(S)` from `V^S` (`typePV_orderOf_not_dvd_card_derived`). -/
theorem typeII_A0_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    OddOrder.GroupTheory.IsTISubset
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data)) S := by
  classical
  have hP : OddOrder.BG.Ch4.S14.IsTypeP S :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hSmax (Or.inl hSII)
  have hHall := typePData_W1_hall_coprime hG hSmax hP data
  have hWle : data.W ≤ S := typePData_W_le_self data
  -- the order separator: `A(S)`-elements have order dividing `|S'|`, `V^S`-elements do not
  have hAord : ∀ {x : G}, x ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) →
      orderOf x ∣ Nat.card ↥(derivedInG S) := by
    intro x hx
    have h1 := orderOf_dvd_natCard (⟨x, hx.1⟩ : ↥(derivedInG S))
    rwa [← Subgroup.orderOf_coe] at h1
  have hVord : ∀ {x : G}, x ∈ conjClassSetIn S (typePV S data) →
      ¬ orderOf x ∣ Nat.card ↥(derivedInG S) := by
    rintro x ⟨t, htV, h, -, rfl⟩
    have hoeq : orderOf (h * t * h⁻¹) = orderOf t := by
      have := orderOf_injective (MulAut.conj h).toMonoidHom (MulEquiv.injective _) t
      simpa [MulAut.conj_apply] using this
    rw [hoeq]
    exact typePV_orderOf_not_dvd_card_derived data hHall htV
  have horder : ∀ (g x : G), orderOf (g * x * g⁻¹) = orderOf x := by
    intro g x
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective _) x
    simpa [MulAut.conj_apply] using this
  rintro g ⟨a, ha, hga⟩
  rcases ha with haA | haV
  · rcases hga with hgaA | hgaV
    · -- `(A, A)`: the landed (8.16) `A(S)`-TI
      exact typeII_centralizerSupport_isTISubset hG hSmax hSII g ⟨a, haA, hgaA⟩
    · -- `(A, V^S)`: impossible by the order separator
      exact absurd (horder g a ▸ hAord haA) (hVord hgaV)
  · rcases hga with hgaA | hgaV
    · -- `(V^S, A)`: impossible by the order separator
      exact absurd (horder g a ▸ hAord hgaA) (hVord haV)
    · -- `(V^S, V^S)`: the ambient (3.1) `V`-TI, then `W ≤ S`
      obtain ⟨t, htV, s, hsS, rfl⟩ := haV
      obtain ⟨t', ht'V, s', hs'S, heq⟩ := hgaV
      have hconj : (s'⁻¹ * g * s) * t * (s'⁻¹ * g * s)⁻¹ = t' := by
        have h3 : s' * ((s'⁻¹ * g * s) * t * (s'⁻¹ * g * s)⁻¹) * s'⁻¹
            = s' * t' * s'⁻¹ := by
          rw [heq]; group
        exact mul_left_cancel (mul_right_cancel h3)
      have hmemW : s'⁻¹ * g * s ∈ data.W :=
        OddOrder.Peterfalvi.S10.typePData_V_ti data (s'⁻¹ * g * s)
          ⟨t, htV, hconj ▸ ht'V⟩
      have hgeq : g = s' * (s'⁻¹ * g * s) * s⁻¹ := by group
      rw [hgeq]
      exact S.mul_mem (S.mul_mem hs'S (hWle hmemW)) (S.inv_mem hsS)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.16) ⇒ Hypothesis (2.2) for `(A₀(S), S)`, Type II**: the honest type-II Dade
base on the *enlarged* support `A₀(S) = A(S) ∪ V^S`.  All (8.14) signalizers are trivial —
`A₀(S)` is a TI-subset (`typeII_A0_isTISubset`) — so Hypothesis (2.2) is `of_isTISubset` with
`H(a) = ⊥`.  This is the `dade0` datum of the `S`-side Hypothesis (4.6)
(`typeIIHypothesis46`), over which the reducible-column `R`-family `S06.certainTypeR` and its
Dade identities run. -/
noncomputable def typeIIDadeHypothesis0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    OddOrder.Peterfalvi.S04.Hypothesis G
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data)) S :=
  OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
    (by
      rintro y (hy | ⟨t, htV, h, -, rfl⟩)
      · exact OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ _, hy.2.1⟩
      · refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ _, fun h1 => htV.2 ?_⟩
        have ht1 : t = 1 := by
          have hteq : t = h⁻¹ * (h * t * h⁻¹) * h := by group
          rw [hteq, h1]; group
        exact (Set.mem_union _ _ _).mpr (Or.inl (by
          rw [ht1]; exact SetLike.mem_coe.mpr data.W1.one_mem)))
    (by
      rintro y (hy | ⟨t, htV, h, hhS, rfl⟩)
      · exact Subgroup.map_subtype_le _ hy.1
      · exact S.mul_mem (S.mul_mem hhS (typePData_W_le_self data htV.1)) (S.inv_mem hhS))
    (by
      rintro l a (ha | ⟨t, htV, h, hhS, rfl⟩)
      · exact Or.inl (centralizerSupport_sharpMsigma_conj_mem l.2 ha)
      · exact Or.inr ⟨t, htV, (l : G) * h, S.mul_mem l.2 hhS, by group⟩)
    (typeII_A0_isTISubset hG hSmax hSII data)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.15) for Type II / the (10.7) sentence "Hypothesis (4.6) holds with `L = S`,
`K = S'`, `A = A(S)`, `A₀ = A₀(S)`, `H = S_F`"**: a Type-II maximal subgroup `S` instantiates
the §4/§6 Hypothesis (4.6) carrier `S06.Hypothesis46 (A(S)) S`, with the honest (8.10) support
`A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#`.

Field sources (mirroring the `M`-side `Hypothesis.toHypothesis46`, but with every Dade datum
*constructed* rather than hoisted):

* the (4.2) structural part: `typePData_toS06Hypothesis` (Hall coprimality from
  `typePData_W1_hall_coprime`, BG `IsTypeP` from `isTypeP_of_isTypeNonI`);
* the `A`-side Dade datum: the landed (8.16) `typeIIDadeHypothesis`;
* the ambient (3.1) TI-cyclic data (4.6.b): `typePData_toTICyclicHypothesis`, with the same
  `subgroupOf`-vs-ambient matching as the `M`-side (`Subgroup.map_subgroupOf_eq_of_le`, `rfl`);
* (4.6.c): `H := S_F` — the (10.7)/(8.15) choice for type II (`M`-side types III–V take
  `H = K`); `W₂ ≤ S_F` and `S_F ≤ S'` are the `TypePData` fields, normality is
  `S ≤ N_G(S_F)`;
* (4.6.d): the covering `⋃_{h∈S_F^#} C_{S'}(h)^# ⊆ A(S)` holds *by definition* of the honest
  `A(S)`: `S_F = S_σ` for type II (`maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`), so
  every such element carries an `S_σ^#`-witness;
* (4.6.d)/(4.6.e): the `A₀`-side Dade datum and isometry are the (8.16) TI construction
  `typeIIDadeHypothesis0` (with the trivial-signalizer `hconj`), on
  `A(S) ∪ conjClassSetIn S V` — definitionally the required `A ∪ V^L` shape. -/
noncomputable def typeIIHypothesis46 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    OddOrder.Peterfalvi.S06.Hypothesis46
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S :=
  { toHypothesis := typePData_toS06Hypothesis data hG.odd
      (typePData_W1_hall_coprime hG hSmax
        (OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hSmax (Or.inl hSII)) data)
    dade := typeIIDadeHypothesis hG hSmax hSII
    tic := typePData_toTICyclicHypothesis data hG.odd
    tic_W1 := (Subgroup.map_subgroupOf_eq_of_le data.W1_le).symm
    tic_W2 := (Subgroup.map_subgroupOf_eq_of_le (typePData_W2_le_self data)).symm
    tic_V := rfl
    subH := data.H.subgroupOf S
    subH_normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer
        (data.H_le.trans (Subgroup.map_subtype_le _))).mpr ?_
      rw [data.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer S
    W2_le_subH := Subgroup.comap_mono (data.W2_le.trans inf_le_left)
    subH_le_K := Subgroup.comap_mono data.H_le
    A_covers := by
      intro hh hhH hhne x hx hxne
      -- the witness `z = (hh : G) ∈ S_σ^#`: `S_F = S_σ` for type II
      have hhσ : (hh : G) ∈ Msigma S := by
        rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
          hG hSmax (Or.inr hSII), ← data.H_eq]
        exact Subgroup.mem_subgroupOf.mp hhH
      obtain ⟨hxC, hxK⟩ := Subgroup.mem_inf.mp hx
      refine ⟨Subgroup.mem_subgroupOf.mp hxK, fun h1 => hxne (Subtype.ext h1),
        (hh : G), (Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr hhσ,
          fun he => hhne (Subtype.ext (Set.mem_singleton_iff.mp he))⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    dade0 := typeIIDadeHypothesis0 hG hSmax hSII data
    tau := (typeIIDadeHypothesis0 hG hSmax hSII data).fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)) }

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **World-bridge, `S`-side subset direction**: the §9 induced family `𝒮(Y)` of a
Types-II/III/IV setup lands in the §6/§8 kernel-filtered family
`S(Y) = inducedKernelFamily S' (Y ∩ S)`.  Both families induce from `HU = S'`
(`huSub_eq_derivedInG_subgroupOf`), and the `H ⊄ Ker` condition of `xiSet` supplies the
`θ ≠ 1` of `inducedKernelFamily`.

Setup-generic mirror of the `S13.Hypothesis`-locked `sOf_subset_SOf` (S13 is downstream of
this leaf, so it cannot be cited here; dedup candidate on a future upstream hoist).  Feeds the
`(9.8)` reducible classification and the `inducedKernelFamily_*` support/orthogonality/no-real
facts to the (10.7) `T2`-family. -/
theorem typeII_sOf_subset_inducedKernelFamily [Finite G] {S : Subgroup G}
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S) (Y : Subgroup G) :
    OddOrder.Peterfalvi.S11.sOf data Y ⊆
      OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG S).subgroupOf S) (Y.subgroupOf S) := by
  classical
  have hHU : huSub data = (derivedInG S).subgroupOf S :=
    huSub_eq_derivedInG_subgroupOf data
  rintro _ ⟨χ, hχ, rfl⟩
  rw [← hHU, OddOrder.Peterfalvi.S08.mem_inducedKernelFamily]
  refine ⟨χ, ?_, hχ.2, induceHU_eq_induce data χ⟩
  intro htriv
  exact hχ.1 (by rw [htriv]; simp [OddOrder.Peterfalvi.S03.characterKernel])

open scoped Classical FiniteInduce in
/-- **Peterfalvi (9.8)-classification at the type-II `S`-side bridge family**: a *reducible*
member of `inducedKernelFamily S' B` (any kernel filter `B`) is a nontrivial certain-type
column sum `μ_j = columnSum χ₂` of the `S`-side Hypothesis (4.6) instance
(`typeIIHypothesis46`).

Setup-generic mirror of the `M`-side
`Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (S12_HcBound), stopping at
the raw column form (no `Fin w₂` re-indexing): the reducible source is a Clifford restriction
`θ = χ_j = chiRestrict χ₂` (Peterfalvi (4.5.b), `induce_not_isIrreducible_iff`), the trivial
column is excluded by the family's `θ ≠ 1` (`chiRestrict_one_eq_trivial`), and the (4.5.a)
induction identity `induce_restrict_certainType_eq` rewrites `Ind_{S'}^S θ` as the column sum.
This is the "`ν` is a column" input of the (10.7) reducible `R(ν)`-datum
(`S06.certainTypeR`). -/
theorem typeII_reducible_inducedKernelFamily_eq_columnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)]
    {B : Subgroup ↥S} {ψ : ClassFunction ↥S ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG S).subgroupOf S) B)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ χ₂ : ((typeIIHypothesis46 hG hSmax hSII data).W2.subgroupOf
        ((typeIIHypothesis46 hG hSmax hSII data).W1
          ⊔ (typeIIHypothesis46 hG hSmax hSII data).W2)) →* ℂˣ,
      χ₂ ≠ 1 ∧
        ψ = OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data) χ₂ := by
  classical
  obtain ⟨θ, hθne, -, rfl⟩ := hψ
  set h : OddOrder.Peterfalvi.S06.Hypothesis ↥S :=
    (typeIIHypothesis46 hG hSmax hSII data).toHypothesis with hh
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  -- the reducible source is a §6 column `χ_j`
  obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [h.chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨χ₂', hχ₂'ne, ?_⟩
  rw [← hχ₂', h.coe_chiRestrict]
  exact h.induce_restrict_certainType_eq χ₂'

open scoped Classical FiniteInduce in
/-- The (8.16) `A₀(S)` Dade base has conjugation-invariant (trivial) signalizers: every
`H(a) = ⊥` by the `of_isTISubset` construction.  The `hconj` input of the §4 full Dade
isometry (2.6) at `typeIIHypothesis46 … |>.dade0`; since `HConjInvariant` is a proposition,
this is definitionally interchangeable with the proof baked into `typeIIHypothesis46 … |>.tau`. -/
theorem typeIIHypothesis46_dade0_hConjInvariant [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    (typeIIHypothesis46 hG hSmax hSII data).dade0.HConjInvariant :=
  OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

open scoped Classical FiniteInduce in
/-- **The `S`-side Dade image of an `A(S)`-supported function vanishes on the exceptional set
`V`** (type-II mirror of the §12 `S13.tau_apply_eq_zero_of_mem_typePV`, over the (8.16)
`A₀(S)`-Dade base): for `α` supported on `A(S)` and `v ∈ (ticVdiff h46).V = W ∖ (W₁ ∪ W₂) =
typePV S`, the image `α^{τ_S}` vanishes at `v`.

`V^S ⊆ A₀(S)`, so `v` **is** a Dade base point: the explicit (2.5) evaluation
(`dadeValue_eq` with witness `a = v`, `h = 1`) gives `α^{τ_S}(v) = α(v)`, which vanishes
because `v ∉ S'` (`typePData_typePV_not_mem_derived`) while `α` is supported on
`A(S) ⊆ S'`.  This is the anchor of the `S`-side cross-orthogonality `R(μ_j) ⊥ R(χ)`
(`typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff`). -/
theorem typeII_tau_apply_eq_zero_of_mem_ticVdiffV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    {α : ClassFunction ↥S ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S)
    {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (typeIIHypothesis46 hG hSmax hSII data).dade0
      (typeIIHypothesis46 hG hSmax hSII data).tau α v = 0 := by
  classical
  -- `v ∈ typePV S` (the `ticVdiff` exceptional set is definitionally `W ∖ (W₁ ∪ W₂)`)
  have hvPV : v ∈ typePV S data := hv
  -- `v ∈ A₀(S)` (the `V^S`-part, conjugator `1`)
  have hvA0 : v ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
      ∪ conjClassSetIn S (typePV S data) :=
    Or.inr ⟨v, hvPV, 1, S.one_mem, by group⟩
  -- `α` is `A₀`-supported (monotone from `A(S)`-supported)
  have hαA0 : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data)) S :=
    hαsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- evaluate the explicit (2.5) Dade map at the base point `a = v`, `h = 1`
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      (typeIIHypothesis46 hG hSmax hSII data).dade0 _ hαA0,
    OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_apply,
    (typeIIHypothesis46 hG hSmax hSII data).dade0.dadeValue_eq _ (a := ⟨v, hvA0⟩)
      (Subgroup.one_mem _) (by rw [mul_one])]
  -- `α(v) = 0`: `v ∉ S'` while `α` is `A(S) ⊆ S'`-supported
  by_contra hne
  have hmem := hαsupp (ClassFunction.mem_support.mpr hne)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
  exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived data hvPV hmem.1

open scoped Classical FiniteInduce in
/-- **(5.2.e) certain-type column vs irreducible break cross-orthogonality, type-II `S`-side**
`R(μ_j) ⊥ R(χ)` — the (10.7) analogue of the §12
`S13.certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP` (which is downstream of this leaf), over
the (8.16) `A₀(S)`-Dade base `typeIIHypothesis46 … |>.dade0`.

The proof is the same mirror of the Sibley `certainTypeR_imageSet_orthogonal_dadeOfDiff`: the
disjointness machine (`inner_smul_chiFam_eq_zero_of_diff_vanishOnV` on `ticVdiff h46`) and the
two-element `R(χ)` capture are `h46`-generic; the single anchor — vanishing of `(χ − χ̄)^{τ_S}`
on the exceptional `V` — is `typeII_tau_apply_eq_zero_of_mem_ticVdiffV` (base-point evaluation,
`V^S ⊆ A₀(S)`).  The conjugate difference is `A(S)`-supported (`hdiffsuppχA`, feeding the
anchor) and `A₀(S)`-supported (`hdiffsuppχ`, defining the Dade image family `R(χ)`).  This is
the irr × column case of the (10.7) `T2`-family `hRorth`. -/
theorem typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)]
    {χ₂ : ((typeIIHypothesis46 hG hSmax hSII data).W2.subgroupOf
      ((typeIIHypothesis46 hG hSmax hSII data).W1
        ⊔ (typeIIHypothesis46 hG hSmax hSII data).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, (((typeIIHypothesis46 hG hSmax hSII data).columnFamily χ₂).mu i
        : ClassFunction ↥S ℂ) 1)
      = (∑ i, (((typeIIHypothesis46 hG hSmax hSII data).columnFamily χ₂⁻¹).mu i
        : ClassFunction ↥S ℂ) 1))
    (χ : IrreducibleCharacter ↥S)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥S ℂ))
    (hdiffsuppχA : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S)
    (hdiffsuppχ : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data)) S) :
    ∀ α ∈ (OddOrder.Peterfalvi.S06.certainTypeR (typeIIHypothesis46 hG hSmax hSII data)
        hχ₂ hdeg).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
        (typeIIHypothesis46 hG hSmax hSII data).dade0
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data)
        χ hrealχ hdiffsuppχ).imageSet,
      ClassFunction.inner α β = 0 := by
  classical
  -- `hmin`: `2 < min(w₁, w₂)` for the `ticVdiff` exceptional structure.
  have hmin : 2 < min
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W2
    omega
  -- core disjointness brick (mirror of the Sibley/§12 `key`)
  have key : ∀ (χ₂' : ((typeIIHypothesis46 hG hSmax hSII data).W2.subgroupOf
      ((typeIIHypothesis46 hG hSmax hSII data).W1
        ⊔ (typeIIHypothesis46 hG hSmax hSII data).W2)) →* ℂˣ)
      (i : Fin (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)) {c c' : ℂ}
      {ξ ξ' : ClassFunction G ℂ},
      ξ ∈ ZIrr G → ClassFunction.inner ξ ξ = 1 → ξ' ∈ ZIrr G →
      ClassFunction.inner ξ' ξ' = 1 →
      ClassFunction.inner ξ ξ' = 0 → c ≠ 0 →
      (∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
        (c • ξ - c' • ξ') v = 0) →
      ClassFunction.inner (c • ξ)
        (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma
          (typeIIHypothesis46 hG hSmax hSII data) χ₂' i) = 0 := by
    intro χ₂' i c c' ξ ξ' hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
    rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam]
    exact OddOrder.Peterfalvi.S08.inner_smul_chiFam_eq_zero_of_diff_vanishOnV
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)) rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (typeIIHypothesis46 hG hSmax hSII data))
      hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish hmin _
  -- `(χ − χ̄)^{τ_S}` vanishes on `V` (the type-II anchor, base-point evaluation)
  have hsuppsub : (((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
    rw [show (χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj =
        -((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχA
  have htauvanish : ∀ v ∈
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data).dade0
        (typeIIHypothesis46 hG hSmax hSII data).tau
        ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj) v = 0 :=
    fun v hv => typeII_tau_apply_eq_zero_of_mem_ticVdiffV hG hSmax hSII data hsuppsub hv
  -- capture the two-element `R(χ)` abstractly
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
          (typeIIHypothesis46 hG hSmax hSII data).dade0
          ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData
            (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data)))
        (χ : ClassFunction ↥S ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            (typeIIHypothesis46 hG hSmax hSII data).dade0
            (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data) χ hrealχ hdiffsuppχ
          = cd.toOrthonormalImage := ⟨_, rfl⟩
  have hcdimg : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (typeIIHypothesis46 hG hSmax hSII data).dade0
      ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data))
      ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj)
      = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction := by
    rw [cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.mu; rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.nu; rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.nu; rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsignC : (cd.sign : ℂ) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hnsignC : (-(cd.sign : ℂ)) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  intro α hα β hβ
  rw [hcd] at hβ
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hβ
  simp only [OddOrder.Peterfalvi.S06.certainTypeR, Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, -, rfl⟩ := hα
  have hvanishμν : ∀ v ∈
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) v = 0 := by
    intro v hv; rw [← hcdimg]; exact htauvanish v hv
  have hvanishνμ : ∀ v ∈
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction) v = 0 := by
    intro v hv
    rw [show (-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction
        = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction by
      rw [neg_smul, neg_smul]; abel]
    exact hvanishμν v hv
  have hμcast : cd.sign • cd.muClassFunction = (cd.sign : ℂ) • cd.muClassFunction :=
    (Int.cast_smul_eq_zsmul ℂ cd.sign cd.muClassFunction).symm
  have hνcast : (-cd.sign) • cd.nuClassFunction = (-(cd.sign : ℂ)) • cd.nuClassFunction := by
    rw [← Int.cast_smul_eq_zsmul ℂ (-cd.sign) cd.nuClassFunction, Int.cast_neg]
  rcases hβ with rfl | rfl <;> cases b <;>
    simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]

/-! ### The (10.7) `T2 = {λ, λ̄, ν, ν̄}` family: membership, support and degree bookkeeping -/

/-- **Equal-degree differences of `A ∪ {1}`-supported class functions are `A`-supported** —
the abstract core of the (4.7)-style `hsuppdiff` inputs (each member's support lies in
`A ∪ {1}` and the shared degree kills the `1`-point).  Abstracted from
`typeII_sSet_diff_support_subset` so the `T2`-family conjugates (whose member-support facts
come from support-invariance of conjugation, not from `xiSet`-membership) feed the same
engine input. -/
theorem diff_support_subset_of_support_subset_union_one {L : Subgroup G}
    {A : Set ↥L} {a b : ClassFunction ↥L ℂ}
    (ha : a.support ⊆ A ∪ {1}) (hb : b.support ⊆ A ∪ {1}) (hdeg : a 1 = b 1) :
    (a - b).support ⊆ A := by
  intro x hx
  have hx0 : (a - b) x ≠ 0 := ClassFunction.mem_support.mp hx
  have hx1 : x ≠ 1 := by
    intro he
    apply hx0
    rw [he, ClassFunction.sub_apply, hdeg, sub_self]
  rcases ClassFunction.support_sub_subset a b hx with h | h
  · rcases ha h with h' | h'
    · exact h'
    · exact absurd (Set.mem_singleton_iff.mp h') hx1
  · rcases hb h with h' | h'
    · exact h'
    · exact absurd (Set.mem_singleton_iff.mp h') hx1

/-- Complex conjugation preserves the support of a class function. -/
theorem conj_support_eq {L : Subgroup G} (φ : ClassFunction ↥L ℂ) :
    φ.conj.support = φ.support := by
  ext y
  simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **`𝒮(Y)`-members have positive natural degree**: `φ(1) = q·ξ(1) ∈ ℕ₊` (the (9.5) degree
formula `induceHU_apply_one_eq_q_mul` on the irreducible source degree).  Supplies the
`T2`-family's `hdeg0` (nonzero pivot degree) and the conjugate-degree realness
(`star (φ 1) = φ 1`). -/
theorem typeII_sOf_apply_one_eq_pos_natCast [Finite G] {S : Subgroup G}
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S) {Y : Subgroup G}
    {φ : ClassFunction ↥S ℂ} (hφ : φ ∈ OddOrder.Peterfalvi.S11.sOf data Y) :
    ∃ n : ℕ, 0 < n ∧ φ 1 = (n : ℂ) := by
  obtain ⟨ξ, -, rfl⟩ := hφ
  obtain ⟨d, hd0, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  refine ⟨data.q * d, Nat.mul_pos Nat.card_pos hd0, ?_⟩
  rw [induceHU_apply_one_eq_q_mul, hd]
  push_cast
  ring

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **The `T2`-family lands in the kernel-filtered family**: every member of
`{λ, λ̄, ν, ν̄}` (with `λ, ν ∈ 𝒮(Y)`) lies in `inducedKernelFamily S' (Y ∩ S)` — the base
members via the world-bridge `typeII_sOf_subset_inducedKernelFamily`, their conjugates via
the family's conjugation-closure.  Feeds the pairwise-orthogonality / no-real / `ℤIrr`
engine inputs. -/
theorem typeII_T2_subset_inducedKernelFamily [Finite G] {S : Subgroup G}
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S) {Y : Subgroup G}
    {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y) :
    ∀ η ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)),
      η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG S).subgroupOf S) (Y.subgroupOf S) := by
  have hlam := typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  have hnu := typeII_sOf_subset_inducedKernelFamily data Y hnu_mem
  rintro η (rfl | rfl | rfl | rfl)
  · exact hlam
  · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hlam
  · exact hnu
  · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hnu

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **`T2`-member supports lie in `A(S) ∪ {1}`**: the base members by the landed (4.7)
`typeII_sSet_member_support_subset`, the conjugates by support-invariance of conjugation
(`conj_support_eq`). -/
theorem typeII_T2_member_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S) {Y : Subgroup G}
    {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y) :
    ∀ η ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)),
      η.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S ∪ {1} := by
  have hbase : ∀ {φ : ClassFunction ↥S ℂ}, φ ∈ OddOrder.Peterfalvi.S11.sOf data Y →
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S ∪ {1} := by
    intro φ hφ
    obtain ⟨ξ, hξ, rfl⟩ := hφ
    exact typeII_sSet_member_support_subset hG hSmax hSII data
      (OddOrder.Peterfalvi.S11.xiOf_subset_xiSet data Y hξ)
  rintro η (rfl | rfl | rfl | rfl)
  · exact hbase hlam_mem
  · rw [conj_support_eq]; exact hbase hlam_mem
  · exact hbase hnu_mem
  · rw [conj_support_eq]; exact hbase hnu_mem

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **`T2` has uniform degree `λ(1)`**: the base members by the (10.7) hypothesis
`λ(1) = ν(1)`, the conjugates because the shared degree is a natural number
(`typeII_sOf_apply_one_eq_pos_natCast`), hence fixed by the conjugation
`φ̄(1) = star (φ(1))`. -/
theorem typeII_T2_apply_one_eq [Finite G] {S : Subgroup G}
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S) {Y : Subgroup G}
    {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1) :
    ∀ η ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)), η 1 = lam 1 := by
  obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
  obtain ⟨m, -, hm⟩ := typeII_sOf_apply_one_eq_pos_natCast data hnu_mem
  rintro η (rfl | rfl | rfl | rfl)
  · rfl
  · rw [ClassFunction.conj_apply, hn, star_natCast]
  · exact hdeg.symm
  · rw [ClassFunction.conj_apply, hm, star_natCast, ← hm, ← hdeg]

/-! ### The (10.7) `T2` per-member `R`-data dispatch -/

open scoped Classical FiniteInduce in
/-- **Per-member orthonormal `R`-family over the (10.7) `T2 = {λ, λ̄, ν, ν̄}`** (the raw
(5.2.d) datum for the norm-general (5.7) engine `uniform_degree_coherence_of_families`),
over the `S`-side `A₀(S)`-Dade base `typeIIHypothesis46 … |>.dade0`.

Dispatch mirrors the §13 `caseB_sOf_memberRFamily`, by irreducibility (not by member
identity):

* **irreducible `η`** (`λ` or `λ̄`) — the 2-element signed Dade family
  `dadeOrthonormalCharacterImageFamilyOfDiff`; realness from the kernel-filtered family's
  no-real property, difference-support from `typeII_T2_member_support` + the degree
  realness (`typeII_T2_apply_one_eq`);
* **reducible `η`** (`ν` or `ν̄`) — the (9.8) classification
  `typeII_reducible_inducedKernelFamily_eq_columnSum` produces the column `χ₂ ≠ 1` with
  `η = columnSum χ₂`, and the `R`-family is `S06.certainTypeR` rebuilt at the abstract
  member (the `imageSet`/`orthonormal`/`mem_ZIrr` fields are `η`-independent, `image_eq`
  is re-proved through the classification equation) — so
  `(typeII_T2_memberRFamily …).imageSet` is *definitionally* `certainTypeR.imageSet`.

Both branches land definitionally on
`τ_S = dadeIntegralCharacterMap (typeIIHypothesis46 …).dade0 (typeIIHypothesis46 …).tau`
(the `tau` field is `fullDadeIsometryData` of the `dade0` field at the proof-irrelevant
`hconj`), so no `congrMap` seam. -/
noncomputable def typeII_T2_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    {η : ClassFunction ↥S ℂ}
    (hη : η ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau) η := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  have hηIKF : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG S).subgroupOf S) (Y.subgroupOf S) :=
    typeII_T2_subset_inducedKernelFamily data hlam_mem hnu_mem η hη
  by_cases hirr : IsIrreducibleCharacter η
  · -- irreducible: the signed Dade family over the `A₀(S)` base
    have hreal : ¬ ClassFunction.IsReal (η : ClassFunction ↥S ℂ) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
        (Y.subgroupOf S) hηIKF
    have hdiffsupp : ((η : ClassFunction ↥S ℂ).conj - η).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
            ∪ conjClassSetIn S (typePV S data.typeP)) S := by
      refine (diff_support_subset_of_support_subset_union_one
        (by rw [conj_support_eq]
            exact typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem η hη)
        (typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem η hη) ?_).trans
        (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
      rw [ClassFunction.conj_apply,
        typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg η hη]
      obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
      rw [hn, star_natCast]
    exact OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
      (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
      ⟨η, hirr⟩ hreal hdiffsupp
  · -- reducible: rebuild `certainTypeR` at the abstract member (column extracted by choice)
    have hex := typeII_reducible_inducedKernelFamily_eq_columnSum hG hSmax hSII data.typeP
      hηIKF hirr
    let χ₂ := hex.choose
    have hχ₂ne : χ₂ ≠ 1 := hex.choose_spec.1
    have hkeq : η = OddOrder.Peterfalvi.S06.columnSum
        (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂ := hex.choose_spec.2
    exact
      { imageSet := (OddOrder.Peterfalvi.S06.certainTypeR
          (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm).imageSet
        mem_ZIrr := (OddOrder.Peterfalvi.S06.certainTypeR
          (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm).mem_ZIrr
        orthonormal := (OddOrder.Peterfalvi.S06.certainTypeR
          (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm).orthonormal
        image_eq := by
          rw [hkeq]
          exact (OddOrder.Peterfalvi.S06.certainTypeR
            (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
            (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
              (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm).image_eq }

open scoped Classical FiniteInduce in
/-- **`typeII_T2_memberRFamily` reduction, irreducible case**: for an irreducible `T2`-member
`η`, the dispatched `R`-family *is* `dadeOrthonormalCharacterImageFamilyOfDiff` (imageSet
form).  The realness and support proofs are existential (proof-irrelevant inputs to a
proof-independent `imageSet`), so the (5.2.e) cross lemmas apply after rewriting. -/
theorem typeII_T2_memberRFamily_imageSet_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    {η : ClassFunction ↥S ℂ}
    (hη : η ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)))
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal η)
      (hs : (η.conj - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S),
      (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
          (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
          ⟨η, hirr⟩ hr hs).imageSet := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  have hηIKF : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG S).subgroupOf S) (Y.subgroupOf S) :=
    typeII_T2_subset_inducedKernelFamily data hlam_mem hnu_mem η hη
  refine ⟨OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (Y.subgroupOf S) hηIKF, ?_, ?_⟩
  · refine (diff_support_subset_of_support_subset_union_one
      (by rw [conj_support_eq]
          exact typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem η hη)
      (typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem η hη) ?_).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
    rw [ClassFunction.conj_apply,
      typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg η hη]
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [hn, star_natCast]
  · unfold typeII_T2_memberRFamily
    rw [dif_pos hirr]

open scoped Classical FiniteInduce in
/-- **`typeII_T2_memberRFamily` reduction, column case**: for a reducible `T2`-member `η`,
the dispatched `R`-family *is* `certainTypeR` at the classified column `χ₂` (imageSet form),
exposed existentially together with the membership equation `η = columnSum χ₂` (which
supplies the `≠`-side conditions of the μ×μ cross-orthogonality). -/
theorem typeII_T2_memberRFamily_imageSet_of_col [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    {η : ClassFunction ↥S ℂ}
    (hη : η ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)))
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (χ₂ : ((typeIIHypothesis46 hG hSmax hSII data.typeP).W2.subgroupOf
        ((typeIIHypothesis46 hG hSmax hSII data.typeP).W1
          ⊔ (typeIIHypothesis46 hG hSmax hSII data.typeP).W2)) →* ℂˣ)
      (hχ₂ne : χ₂ ≠ 1),
      η = OddOrder.Peterfalvi.S06.columnSum
        (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂ ∧
      (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR
          (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm).imageSet := by
  classical
  have hηIKF : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG S).subgroupOf S) (Y.subgroupOf S) :=
    typeII_T2_subset_inducedKernelFamily data hlam_mem hnu_mem η hη
  have hex := typeII_reducible_inducedKernelFamily_eq_columnSum hG hSmax hSII data.typeP
    hηIKF hcol
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold typeII_T2_memberRFamily
  rw [dif_neg hcol]

set_option maxHeartbeats 1600000 in
-- the `2×2` dichotomy case split repeatedly matches the reduced dispatched families against
-- the (5.2.e) lemmas through the `tau = fullDadeIsometryData` proof-irrelevance defeq
open scoped Classical FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the dispatched `T2` `R`-families** (the `hRorth` input
of the norm-general (5.7) engine over `T2 = {λ, λ̄, ν, ν̄}`): for members `φ, ξ` with
`⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the `R`-families satisfy `R(φ) ⊥ R(ξ)`.  The `2×2` dispatch mirrors
the §13 `caseB_sOf_memberRFamily_orthogonal`:

* **irr × irr** — the generic `S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`;
  the extra scalars `⟨φ̄, ξ⟩`, `⟨φ̄, ξ̄⟩` are `star`-conjugates of the inputs;
* **irr × column** / **column × irr** — the landed
  `typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff` (with an `inner_conj_symm` swap for
  the irr-on-left order);
* **column × column** — `S06.certainTypeR_imageSet_orthogonal_certainTypeR`, the `χ₂ ≠ χ₂'`
  and `χ₂ ≠ χ₂'⁻¹` side conditions from `⟨φ, ξ⟩ = 0` / `⟨φ, ξ̄⟩ = 0` (else `φ = ξ` resp.
  `φ = ξ̄` has inner product `w₁ ≠ 0`). -/
theorem typeII_T2_memberRFamily_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    {φ ξ : ClassFunction ↥S ℂ}
    (hφ : φ ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)))
    (hξ : ξ ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)))
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg hφ).Orthogonal
      (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg hξ) := by
  classical
  -- `A(S)`-support of an irreducible member's conjugate difference (the anchor input of the
  -- μ×irr cross-orthogonality)
  have hIrrA : ∀ {ζ : ClassFunction ↥S ℂ},
      ζ ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) →
      ((ζ.conj - ζ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S) := by
    intro ζ hζ
    refine diff_support_subset_of_support_subset_union_one
      (by rw [conj_support_eq]
          exact typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem ζ hζ)
      (typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem ζ hζ) ?_
    rw [ClassFunction.conj_apply,
      typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg ζ hζ]
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [hn, star_natCast]
  have hw1ne : (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne _)
  intro α hα β hβ
  by_cases hφirr : IsIrreducibleCharacter φ <;> by_cases hξirr : IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ := typeII_T2_memberRFamily_imageSet_of_irr hG hSmax hSII data
      hlam_mem hnu_mem hdeg hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := typeII_T2_memberRFamily_imageSet_of_irr hG hSmax hSII data
      hlam_mem hnu_mem hdeg hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
      (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
      (x := ⟨φ, hφirr⟩) (χ := ⟨ξ, hξirr⟩)
      hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ := typeII_T2_memberRFamily_imageSet_of_irr hG hSmax hSII data
      hlam_mem hnu_mem hdeg hφ hφirr
    obtain ⟨k, hk0, hkeq, hξeq⟩ := typeII_T2_memberRFamily_imageSet_of_col hG hSmax hSII data
      hlam_mem hnu_mem hdeg hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [OddOrder.RepresentationTheory.inner_conj_symm β α]
    rw [typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff hG hSmax hSII data.typeP hk0
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
        (typeIIHypothesis46 hG hSmax hSII data.typeP) k).symm
      ⟨φ, hφirr⟩ hrφ (hIrrA hφ) hsφ β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨k, hk0, hkeq, hφeq⟩ := typeII_T2_memberRFamily_imageSet_of_col hG hSmax hSII data
      hlam_mem hnu_mem hdeg hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := typeII_T2_memberRFamily_imageSet_of_irr hG hSmax hSII data
      hlam_mem hnu_mem hdeg hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff hG hSmax hSII data.typeP hk0
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
        (typeIIHypothesis46 hG hSmax hSII data.typeP) k).symm
      ⟨ξ, hξirr⟩ hrξ (hIrrA hξ) hsξ α hα β hβ
  · -- column × column
    obtain ⟨kφ, hkφ0, hkφeq, hφeq⟩ := typeII_T2_memberRFamily_imageSet_of_col hG hSmax hSII
      data hlam_mem hnu_mem hdeg hφ hφirr
    obtain ⟨kξ, hkξ0, hkξeq, hξeq⟩ := typeII_T2_memberRFamily_imageSet_of_col hG hSmax hSII
      data hlam_mem hnu_mem hdeg hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hne1 : kφ ≠ kξ := by
      intro heq
      have hφξ : φ = ξ := by rw [hkφeq, hkξeq, heq]
      rw [hφξ, hkξeq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    have hne2 : kφ ≠ kξ⁻¹ := by
      intro heq
      have hφξc : φ = ξ.conj := by
        rw [hkφeq, heq, ← OddOrder.Peterfalvi.S06.columnSum_conj_eq, hkξeq]
      rw [hφξc, hkξeq, OddOrder.Peterfalvi.S06.columnSum_conj_eq,
        OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h2
      exact hw1ne h2
    exact OddOrder.Peterfalvi.S06.certainTypeR_imageSet_orthogonal_certainTypeR
      (typeIIHypothesis46 hG hSmax hSII data.typeP) hkφ0 hkξ0
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
        (typeIIHypothesis46 hG hSmax hSII data.typeP) kφ).symm
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
        (typeIIHypothesis46 hG hSmax hSII data.typeP) kξ).symm
      hne1 hne2 α hα β hβ

set_option maxHeartbeats 1600000 in
-- the engine threads the dispatched `R`-families and the `hZdiff`/`hiso` inputs through the
-- `tau = fullDadeIsometryData` proof-irrelevance defeq, which is feasible but expensive
open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.7) for the (10.7) `T2 = {λ, λ̄, ν, ν̄}` family — obligation 1 of
`exists_typeIICrossIsometryData`**: for an irreducible `λ` and a reducible `ν` of equal degree
in the `S`-side §9 family `𝒮(Y)`, the 4-element family `T2` is coherent over the `S`-side
`A₀(S)`-Dade isometry `τ_S` (the (8.16) `typeIIHypothesis46` base).

One shot of the norm-general uniform-degree engine
(`uniform_degree_coherence_of_families`), with pivot `λ` (norm `1`), second member `ν`, the
per-member `R`-data dispatch `typeII_T2_memberRFamily` and its (5.2.e) cross-orthogonality
`typeII_T2_memberRFamily_orthogonal`; the family-level facts (pairwise orthogonality,
no-real, `ℤIrr`) flow through `inducedKernelFamily`, the support facts through the (4.7)
`typeII_T2_member_support` and the degree bookkeeping `typeII_T2_apply_one_eq`. -/
theorem typeII_T2_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_red : ¬ IsIrreducibleCharacter nu)
    (hdeg : lam 1 = nu 1) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S)) := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  have hT2IKF := typeII_T2_subset_inducedKernelFamily data hlam_mem hnu_mem
  have hT2supp := typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem
  have hT2one := typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg
  -- uniform `A₀(S)`-support of member differences
  have hsuppdiff : ∀ a ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)),
      ∀ b ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)),
      ((a - b : ClassFunction ↥S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
            ∪ conjClassSetIn S (typePV S data.typeP)) S := by
    intro a ha b hb
    exact (diff_support_subset_of_support_subset_union_one (hT2supp a ha) (hT2supp b hb)
      ((hT2one a ha).trans (hT2one b hb).symm)).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  refine OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))))
    (Set.mem_insert _ _)
    (fun η hη => typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg hη)
    (fun a ha b hb hab =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hT2IKF a ha) (hT2IKF b hb) hab)
    ?hconj
    (fun a ha h =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
        (Y.subgroupOf S) (hT2IKF a ha) h.symm)
    ⟨1, by
      have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam, hlam_irr⟩
      rw [if_pos rfl] at h
      simpa using h⟩
    (fun {φ ψ} hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hφ)
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hψ))
    (fun a ha b hb =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
        (hsuppdiff a ha b hb)
        (Submodule.sub_mem _
          (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hT2IKF a ha))
          (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hT2IKF b hb))))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 =>
      typeII_T2_memberRFamily_orthogonal hG hSmax hSII data hlam_mem hnu_mem hdeg
        hφ hξ h1 h2)
    hT2one
    ?hdeg0
    ?h1A
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (fun h => hnu_red (h ▸ hlam_irr))
  case hconj =>
    rintro a (rfl | rfl | rfl | rfl)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [ClassFunction.conj_conj]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl))
    · rw [ClassFunction.conj_conj]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  case hdeg0 =>
    obtain ⟨n, hn0, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [hn]
    exact Nat.cast_ne_zero.mpr hn0.ne'
  case h1A =>
    intro hmem
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    rcases hmem with h | ⟨t, htV, h, -, heq⟩
    · exact h.2.1 rfl
    · have ht1 : t = 1 := by
        have h2 : t = h⁻¹ * (h * t * h⁻¹) * h := by group
        rw [h2, heq, OneMemClass.coe_one]
        group
      exact htV.2 ((Set.mem_union _ _ _).mpr (Or.inl (by
        rw [ht1]
        exact SetLike.mem_coe.mpr data.typeP.W1.one_mem)))

end Hypothesis46Instance

/-! ## The (10.7) cross-isometry package -/

/-- **Peterfalvi (10.7), left-branch cross-isometry data** for a Type-II maximal `S`
against the type-`P₁` `M` of Hypothesis (10.1)/(10.4).

Bundles, for an irreducible `lam` and a reducible `nu` of equal degree in the `S`-side
induced family `𝒮(H₀)(S)`, the five character-theoretic facts that Peterfalvi's (10.7)
contradiction consumes.  Each field cites its book source:

* `tau2` — the coherent extension `τ₂` of the `S`-side Dade isometry to
  `ℤ[{λ, λ̄, ν, ν̄}]` (Peterfalvi (5.7): the 4-element family is uniform-degree coherent).
* `r'`, `delta'`, `nu_tau2_eq` — Peterfalvi (5.8) for `τ₂` against the **shared** `ω^σ`-grid:
  `ν^{τ₂} = δ'·∑_{j<w₂} ω_{r'j}^σ` for some row `r'` and sign `δ'`.  The grid here is `M`'s
  aligned `σ`-grid: the (8.8) pair structure (`S ∩ M = W`, `W₁/W₂` roles swapped) and the
  (3.2)-uniqueness of the cyclic-TI isometry `σ` identify `S`'s grid with the transpose of
  `M`'s, so the `S`-side (4.5)-column sum is an `M`-side row sum.
* `lam_ortho_grid` — `λ^{τ₂} ⊥ ω_{ij}^σ` (Peterfalvi (5.3.b): the coherent image of an
  irreducible family member is orthogonal to the `σ`-image; Coq `coherent_ortho_cycTIiso`).
* `zeta_ortho_grid` — `ζ^{τ₁} ⊥ ω_{ij}^σ` (same source, `M`-side).
* `zeta_lam_ortho` — `⟨ζ^{τ₁}, λ^{τ₂}⟩ = 0` (from `⟨(ζ−ζ̄)^τ, (λ−λ̄)^{τ_S}⟩ = 0` — the
  (8.18.b) support disjointness — and orthonormality of the conjugate pairs;
  Coq `orthonormal_vchar_diff_ortho` step of `Frob_der1_type2`).
* `cross_zero` — Peterfalvi's `(α^τ, β^τ) = 0` for `α = μ_s − d·ζ ∈ ℤ[𝒮, M^#]` and
  `β = ν − λ ∈ ℤ[T2, S^#]`: `Supp(α) ⊆ A₁(M)` by (8.10), `Supp(β) ⊆ A(S)` by (8.15)+(4.7),
  and `Ã₁(M) ∩ Ã(S) = ∅` by (8.18.b) (using (8.13.c4): no conjugate of `S` supports `M`,
  because `M` is not Frobenius with kernel `M_F` under Hypothesis (10.1)).  On these
  supports `τ = τ₁` and `τ_S = τ₂` (coherence agreement), giving the stated form. -/
structure TypeIICrossIsometryData [Finite G] [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (lam nu : ClassFunction ↥S ℂ) where
  /-- The (5.7) coherent extension `τ₂` of the `S`-side Dade isometry to the 4-element
  uniform-degree family `{λ, λ̄, ν, ν̄}`. -/
  tau2 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G
  /-- The `M`-grid row index of the (5.8) image of `ν`. -/
  r' : Fin hyp.w1
  /-- The (5.8) sign of the image of `ν`. -/
  delta' : ℤ
  delta'_pm : delta' = 1 ∨ delta' = -1
  /-- **Peterfalvi (5.8)** for `τ₂` against the shared grid: `ν^{τ₂} = δ'·∑_j ω_{r'j}^σ`. -/
  nu_tau2_eq : tau2 nu
    = (delta' : ℂ) • ∑ j : Fin hyp.w2, hyp.alignedOmegaSigmaGrid hG hG.odd r' j
  /-- **Peterfalvi (5.3.b)** (`S`-side): `λ^{τ₂}` is orthogonal to the `σ`-grid. -/
  lam_ortho_grid : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j) (tau2 lam) = 0
  /-- **Peterfalvi (5.3.b)** (`M`-side): `ζ^{τ₁}` is orthogonal to the `σ`-grid. -/
  zeta_ortho_grid : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
    ClassFunction.inner (coh.tau1 params.zeta) (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0
  /-- `⟨ζ^{τ₁}, λ^{τ₂}⟩ = 0` (cross-side orthogonality of the two coherent images). -/
  zeta_lam_ortho : ClassFunction.inner (coh.tau1 params.zeta) (tau2 lam) = 0
  /-- **Peterfalvi's `(α^τ, β^τ) = 0`** for `α = μ_s − d·ζ` and `β = ν − λ`
  ((8.10)+(8.15)+(4.7) supports and the (8.18.b) disjointness). -/
  cross_zero : ∀ s : Fin hyp.w2, s ≠ 0 →
    ClassFunction.inner
      (coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
        - (params.d : ℂ) • params.zeta))
      (tau2 nu - tau2 lam) = 0

open scoped Classical FiniteInduce in
/-- **The (10.7) left-branch gate** (Coq `Frob_der1_type2`, `PFsection10.v:568-658` tail):
for a Type-II maximal `S` whose `S`-side §9 family `𝒮(H₀)` contains an irreducible `lam`
and a reducible `nu` of equal degree, the (10.7) cross-isometry package exists.

The honest production decomposes into (tracking: the (10.7) frontier note
`notes/peterfalvi/s10_7_derived_frobenius.md`):

1. **`τ₂` = T2-coherence** (Peterfalvi (5.7)): the norm-general uniform-degree engine
   `S07.uniform_degree_coherence_of_families` applied to `{λ, λ̄, ν, ν̄}` over the honest
   type-`P₂` `S`-side Dade datum (`dadeSupportHypothesisData_honestTypeP2ASet`), with the
   reducible column `R(ν)`-family `S06.certainTypeRImage` and the irreducible 2-element
   `R(λ)` (`dadeCharacterDifferenceImageOfDiff`).
2. **The shared grid** ((8.8) pair + (3.2) σ-uniqueness): `S ∩ M = W` with the `W₁/W₂`
   roles swapped identifies the `S`-side `certainTypeOmegaSigma` grid with the transpose of
   `M`'s `alignedOmegaSigmaGrid`; then (5.8) (Coq `coherent_prDade_TIred`, via (3.7)
   coefficient rigidity and the `V`-vanishing (3.2.d)) pins `ν^{τ₂}` to a signed row sum.
3. **Support disjointness** ((8.18.b) via (8.13.c4)): `Ã₁(M) ∩ Ã(S) = ∅` because `M` is
   not Frobenius with kernel `M_F` (Hypothesis (10.1)), so no conjugate of `S` supports
   `M`; with (8.10)/(8.15)/(4.7) this gives `cross_zero` and (with the conjugate-pair
   difference trick) `zeta_lam_ortho`.

Each numbered item is genuine unformalized mathematics (none is `M`-side §10 material,
which is fully proven); item 2 is in the `typeP_pair` sphere (issue 0098 item 1), item 3
in the §8 support geometry (S10).  Consumed by `TypeIICrossIsometryData.elim` /
`typeII_HU_frobenius_of_coherent` below. -/
theorem exists_typeIICrossIsometryData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (hSII : IsTypeII S)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief)
    {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0)
    (hnu_red : ¬ IsIrreducibleCharacter nu)
    (hdeg : lam 1 = nu 1) :
    Nonempty (TypeIICrossIsometryData hG coh lam nu) := by
  sorry

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7), left-branch contradiction** (the tail computation of Coq
`Frob_der1_type2`): the cross-isometry package is contradictory.

Choose any nontrivial column `s ≠ 0`.  The proven `M`-side (10.6.a) pin
(`Hypothesis.muColumn_tau1_pin`) gives `μ_s^{τ₁} = δ·∑_i ω_{is}^σ`, so
`(μ_s − d·ζ)^{τ₁} = δ·∑_i ω_{is}^σ − d·ζ^{τ₁}`; the package's (5.8) identity gives
`(ν − λ)^{τ₂} = δ'·∑_j ω_{r'j}^σ − λ^{τ₂}`.  The bilinear expansion of `cross_zero`
against the orthonormal grid (`alignedOmegaSigmaGrid_inner`) kills every term except the
shared entry `⟨ω_{r's}^σ, ω_{r's}^σ⟩`, leaving `0 = δ·δ' = ±1` — absurd.  (This inlines
the abstract bookkeeping of `S15.eta_cross_expansion_ne_zero`, which lives downstream of
this file.) -/
theorem TypeIICrossIsometryData.elim [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    {coh : CoherentHypothesis hyp params}
    {S : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (pkg : TypeIICrossIsometryData hG coh lam nu)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    False := by
  haveI := hyp.finiteG
  classical
  haveI : NeZero hyp.w2 := ⟨params.w2_prime.pos.ne'⟩
  -- the nontrivial-column degree fact `μ_{0j}(1) = d ≠ 1` feeding the pin.
  have hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1 := by
    intro jj hjj h1
    rw [← hmu, params.degree_independent 0 jj hjj] at h1
    have hd := params.d_gt_one
    have : params.d = 1 := Nat.cast_eq_one.mp h1
    omega
  -- choose the column `s = 1 ≠ 0` (`w₂ ≥ 2` since it is prime).
  have hw2 : 1 < hyp.w2 := params.w2_prime.one_lt
  set s : Fin hyp.w2 := ⟨1, hw2⟩ with hs_def
  have hs0 : s ≠ 0 := Fin.ne_of_val_ne (by simp [hs_def])
  -- the proven `M`-side (10.6.a) pin: `μ_s^{τ₁} = δ·∑_i ω_{is}^σ`.
  have hpin := hyp.muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hs0
  -- shorthands (folded into the pin and the package projections).
  set eta : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ :=
    hyp.alignedOmegaSigmaGrid hG hG.odd with heta_def
  set Z : ClassFunction G ℂ := coh.tau1 params.zeta with hZ_def
  set L : ClassFunction G ℂ := pkg.tau2 lam with hL_def
  -- `τ₁(μ_s − d·ζ) = δ·∑_i ω_{is}^σ − d·ζ^{τ₁}` (ℤ-linearity through the ℕ-cast scalar).
  have hτlin : coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta)
      = (params.delta : ℂ) • (∑ i : Fin hyp.w1, eta i s) - (params.d : ℂ) • Z := by
    rw [Nat.cast_smul_eq_nsmul ℂ params.d params.zeta, map_sub, map_nsmul, hpin,
      ← Nat.cast_smul_eq_nsmul ℂ params.d Z]
  -- the cross-orthogonality, rewritten through the two (5.8)-type identities.
  have h0 := pkg.cross_zero s hs0
  rw [hτlin, pkg.nu_tau2_eq, ← heta_def, ← hL_def] at h0
  -- the surviving grid entry and the three vanishing cross terms.
  have hgrid : ClassFunction.inner (∑ i : Fin hyp.w1, eta i s)
      (∑ j : Fin hyp.w2, eta pkg.r' j) = 1 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    have hrow : ∀ i : Fin hyp.w1,
        ClassFunction.inner (eta i s) (∑ j : Fin hyp.w2, eta pkg.r' j)
          = if i = pkg.r' then (1 : ℂ) else 0 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      by_cases hir : i = pkg.r'
      · subst hir
        rw [if_pos rfl, Finset.sum_eq_single s]
        · rw [heta_def, hyp.alignedOmegaSigmaGrid_inner]; simp
        · intro j _ hjs
          rw [heta_def, hyp.alignedOmegaSigmaGrid_inner]
          simp [Ne.symm hjs]
        · intro h; exact absurd (Finset.mem_univ s) h
      · rw [if_neg hir]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [heta_def, hyp.alignedOmegaSigmaGrid_inner]
        simp [hir]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simp
  have hZsum : ClassFunction.inner Z (∑ j : Fin hyp.w2, eta pkg.r' j) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun j _ => pkg.zeta_ortho_grid pkg.r' j
  have hsumL : ClassFunction.inner (∑ i : Fin hyp.w1, eta i s) L = 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    exact Finset.sum_eq_zero fun i _ => pkg.lam_ortho_grid i s
  have hZL : ClassFunction.inner Z L = 0 := pkg.zeta_lam_ortho
  -- expand the bilinear form; only the shared grid entry survives: `0 = δ·δ'`.
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right] at h0
  rw [hgrid, hZsum, hsumL, hZL] at h0
  simp only [star_intCast, mul_one, mul_zero, sub_zero] at h0
  rcases hδpm with hδ | hδ <;> rcases pkg.delta'_pm with hδ' | hδ' <;>
    rw [hδ, hδ'] at h0 <;> norm_num at h0

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7), dichotomy assembly** (setup form): under Hypothesis (10.4) for
`M`, a maximal `S` with a Types-II/III/IV setup that is actually of Type II has
`[S,S] = S_F ⋊ U` Frobenius with kernel `S_F` (on the `derivedInG S` carrier).

Splits on the `S`-side §9 Clifford dichotomy (`S11.clifford_dichotomy`):

* **Case A** (imprimitive `Ū`-action): (9.8.c) supplies an irreducible of degree `q·u` in
  `𝒮(H₀C)` and (9.8.a,b) a reducible of the same degree — the left-branch package
  (`exists_typeIICrossIsometryData`) is contradictory (`TypeIICrossIsometryData.elim`).
* **Case B, exceptional** (no irreducible of degree `q·u` in `𝒮(H₀C')`): Peterfalvi (9.10)
  = `S11.exceptional_case_frobenius_realization` yields the `H ⊔ U` Frobenius structure
  directly (its Type-II conjunct), transported to `derivedInG S` by
  `M' = H ⊔ U` (`TypePData.derivedInG_eq_fitting_sup_U`).
* **Case B, non-exceptional**: the degree-`q·u` irreducible exists in `𝒮(H₀C')`, and
  (9.9.b,c) supply the equal-degree reducible — again the left-branch contradiction. -/
theorem typeII_HU_frobenius_of_coherent_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    (hSII : IsTypeII S) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S)
      (data.typeP.H.subgroupOf (derivedInG S))
      (data.typeP.U.subgroupOf (derivedInG S)) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the (10.3) parameters carrying the grid/`ζ` pins (the coherence datum is
  -- params-independent), as in `typeII_coherence_contradiction_estimate`.
  obtain ⟨params', hmu, hos, hzS, hz1, hzconj, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
  let coh' : CoherentHypothesis hyp params' := ⟨coh.coherent⟩
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  -- §9 character data: only the genuine `u`/`u_eq` pair is consumed by the counts; the
  -- coherence-only fields are inert placeholders (cf. `Hypothesis.mkSection11CharacterData`).
  let chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief :=
    { u := Nat.card ↥(((OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
          (N := chief.N) chief.N_aInvariant).comp
          (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).range)
      u_eq_card_quotient := rfl
      H0CprimeSupport := ∅
      tau := 0
      quotientSemidirectFrobenius := True }
  -- the reducible `ν ∈ 𝒮(H₀)`: the (9.8.a)/(9.9.b) count `p − 1 ≥ 1`.
  have hred_ne : {φ ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0 |
      ¬ IsIrreducibleCharacter φ}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [OddOrder.Peterfalvi.S11.reducible_count_sOf_H0 hG chief]
    have := chief.p_prime.two_le
    omega
  obtain ⟨nu, hnu_mem, hnu_red⟩ := hred_ne
  -- the left-branch refutation, shared by Case A and the non-exceptional Case B.
  have hleft : ∀ lam : ClassFunction ↥S ℂ,
      lam ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0 → IsIrreducibleCharacter lam →
      lam 1 = nu 1 → False := fun lam hlam_mem hlam_irr hdeg =>
    (exists_typeIICrossIsometryData hG coh' hSII chars
      hlam_mem hlam_irr hnu_mem hnu_red hdeg).elim fun pkg =>
      pkg.elim hG hmu hos hzS hz1 hzconj hδpm hδj
  -- the §9 Clifford dichotomy.
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
  · -- **Case A**: (9.8.c) irreducible + (9.8.b) reducible degree — contradiction.
    exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, hbred, ⟨lam, hlam_mem, hlam_irr, hlam_deg⟩, -⟩ :=
      OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
    have hnu_deg := (hbred nu hnu_mem hnu_red).1
    exact hleft lam
      (OddOrder.Peterfalvi.S11.sOf_antitone data le_sup_left hlam_mem)
      hlam_irr (by rw [hlam_deg, hnu_deg])
  · -- **Case B**: split on the exceptional condition.
    obtain ⟨caseB⟩ := hB
    by_cases hex : ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
        IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * chars.u : ℕ) : ℂ)
    · -- non-exceptional: the degree-`q·u` irreducible exists — contradiction.
      exfalso
      obtain ⟨lam, hlam_mem, hlam_irr, hlam_deg⟩ := hex
      obtain ⟨-, -, hbred, -⟩ :=
        OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB
      have hnu_deg := (hbred nu hnu_mem hnu_red).1
      exact hleft lam
        (OddOrder.Peterfalvi.S11.sOf_antitone data le_sup_left hlam_mem)
        hlam_irr (by rw [hlam_deg, hnu_deg])
    · -- exceptional: (9.10) gives the `H ⊔ U` Frobenius, transported to `M' = derivedInG S`.
      have hfrobHU := (OddOrder.Peterfalvi.S11.exceptional_case_frobenius_realization
        hG chars caseB hex).2.2 hSII
      have hM'eq : derivedInG S = data.typeP.H ⊔ data.typeP.U := by
        rw [data.typeP.derivedInG_eq_fitting_sup_U, ← data.typeP.H_eq]
      rw [hM'eq]
      exact hfrobHU

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7)** (Type-II datum form): under Hypothesis (10.4) for `M`, every
Type-II maximal subgroup `S` has `[S,S] = S_F ⋊ U` Frobenius with kernel `S_F`, on the
`derivedInG S` carrier with the type-`P` factors of the given `TypeIIData`. -/
theorem typeII_HU_frobenius_of_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (hSmax : S ∈ maximalSubgroups G) (dII : TypeIIData S) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S)
      (dII.typeP.H.subgroupOf (derivedInG S))
      (dII.typeP.U.subgroupOf (derivedInG S)) :=
  typeII_HU_frobenius_of_coherent_aux hG coh
    { maximal := hSmax
      typeP := dII.typeP
      nontrivial := dII.common
      type_alt := Or.inl ⟨dII⟩ } ⟨dII⟩

end OddOrder.Peterfalvi.S12
