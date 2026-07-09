/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBCoherence2

/-!
# Peterfalvi §8: Case (B) coherence — the per-`φ` constituent dispatch and `X ∪ Y` assembly

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37, the **(6.8.2.3)** core of the (6.8) coherence capstone.

This continues `S08_CaseBCoherence2` (which holds the (6.8.2.2) aggregate, the positive-weight
subtype index, both decomposition branches `columnDecompositionTau` / `irreducibleDecompositionTau`,
and the route-independent anchored-image skeleton `per_phi_anchored_image`).  Here we build the
**mixed per-`φ` family** by dispatching each constituent `θ` of `Ind^L_K φ` to the column branch
(when `Ind^L_H θ = μ_j` is a reducible certain-type column, `θ = Res_H μ_{0j}`) or the irreducible
branch (when `Ind^L_H θ ∈ Irr L`), and assemble the (6.8.2.3) anchored image
`(χᵢ − aᵢ·η₁)^{hyp.tau} = Xᵢ − aᵢ·Y₀` over the whole family.

The constituent dichotomy is taken at the *value* level (`columnSum h46 χ₂ = Ind^L_H θ`, an equation
of class functions on `L`) to avoid the `↥h46.K` vs `↥H` type-mismatch of the index-level form
`chiRestrict χ₂ = θ` (`h46.K = H` is only a propositional equality).

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` ("session 41 cont.⁷ 続⁵+").
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-! ## Dade-map canonicality core (general group theory)

The (6.8.2.3) capstone needs the **map agreement** `dadeIntegralCharacterMap h46.dade0 h46.tau φ =
hyp.tau φ` on `H^#`-supported `φ`.  Since the only *data* field of `S04.Hypothesis` is the `H(a)`
assignment (every other field is a `Prop`), this reduces to the equality of the `H`-fields of
`h46.dade0.restrict A` and `hyp.dade` — both the normal Hall complement of `C_L(a)` in `C_G(a)`.  The
following two general lemmas are the group-theoretic core of that uniqueness: a subgroup of order
coprime to a normal subgroup's index is contained in it (so the running images in `C ⧸ N` are
trivial), whence the normal complement of a fixed subgroup is unique. -/

/-- **A subgroup of order coprime to a normal subgroup's index is contained in it.**  The image of
`K` in `C ⧸ N` has order dividing both `|K|` and `[C : N]` (Lagrange), which are coprime, so the image
is trivial and `K ≤ ker (mk' N) = N`. -/
theorem le_of_card_coprime_index {C : Type*} [Group C]
    {K N : Subgroup C} [N.Normal] (hcop : Nat.Coprime (Nat.card K) N.index) : K ≤ N := by
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  rw [← hker, ← Subgroup.map_eq_bot_iff, ← Subgroup.card_eq_one]
  have hd1 : Nat.card (K.map (QuotientGroup.mk' N)) ∣ Nat.card K :=
    Subgroup.card_map_dvd K (QuotientGroup.mk' N)
  have hd2 : Nat.card (K.map (QuotientGroup.mk' N)) ∣ N.index :=
    Subgroup.card_subgroup_dvd_card (K.map (QuotientGroup.mk' N))
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)

/-- **The `H`-field of an `S04.Hypothesis` is determined by `(G, A, L)`.**  Two Dade hypotheses on the
same data agree on every `H(a)`: each is the normal complement of `C_L(a)` in `C_G(a)`
(`centralizer_eq_sup`/`centralizer_disjoint`/`H_normalized`), of order coprime to `|C_L(a)|`
(`centralizer_coprime`).  Working inside `↥C_G(a)`, `[C_G(a) : H(a)] = |C_L(a)|`
(`card_centralizer_eq` + `card_mul_index`), so `le_of_card_coprime_index` gives each `H(a) ≤` the
other, hence equality.  This is the uniqueness behind the (6.8.2.3) map-agreement: since `H` is the
only *data* field of `S04.Hypothesis`, it makes the enlarged datum `h46.dade0` restrict to the base
`hyp.dade` on `H^#`-supported functions (Dade map being `H`-determined). -/
theorem dade_H_eq {A : Set G} (hyp₁ hyp₂ : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (a : {x : G // x ∈ A}) : hyp₁.H a = hyp₂.H a := by
  suffices h : ∀ p q : OddOrder.Peterfalvi.S04.Hypothesis G A L, p.H a ≤ q.H a from
    le_antisymm (h hyp₁ hyp₂) (h hyp₂ hyp₁)
  intro p q
  have hqC : q.H a ≤ Subgroup.centralizer ({a.1} : Set G) := by
    rw [q.centralizer_eq_sup a]; exact le_sup_left
  have hpC : p.H a ≤ Subgroup.centralizer ({a.1} : Set G) := by
    rw [p.centralizer_eq_sup a]; exact le_sup_left
  -- `(q.H a).subgroupOf C` is normal in `↥C` (C normalizes `q.H a`, by `H_normalized`).
  have hCnorm : Subgroup.centralizer ({a.1} : Set G) ≤ Subgroup.normalizer (q.H a) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => q.H_normalized a c hc n hn, fun hn => ?_⟩
    have hmem := q.H_normalized a c⁻¹ (Subgroup.inv_mem _ hc) _ hn
    have heq : c⁻¹ * (c * n * c⁻¹) * (c⁻¹)⁻¹ = n := by group
    rwa [heq] at hmem
  haveI : ((q.H a).subgroupOf (Subgroup.centralizer ({a.1} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hqC).mpr hCnorm
  -- `|C| = |q.H a| · |C_L(a)|`.
  have hcard : Nat.card (Subgroup.centralizer ({a.1} : Set G))
      = Nat.card (q.H a) * Nat.card (OddOrder.Peterfalvi.S04.centralizerIn L a.1) :=
    q.card_centralizer_eq a
  -- `[↥C : (q.H a).subgroupOf C] = |C_L(a)|`.
  have hidx : ((q.H a).subgroupOf (Subgroup.centralizer ({a.1} : Set G))).index
      = Nat.card (OddOrder.Peterfalvi.S04.centralizerIn L a.1) := by
    have hmi := Subgroup.card_mul_index ((q.H a).subgroupOf (Subgroup.centralizer ({a.1} : Set G)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hqC).toEquiv, hcard] at hmi
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmi
  -- `le_of_card_coprime_index` inside `↥C`, then transport back to `G`.
  have hle : (p.H a).subgroupOf (Subgroup.centralizer ({a.1} : Set G))
      ≤ (q.H a).subgroupOf (Subgroup.centralizer ({a.1} : Set G)) := by
    apply le_of_card_coprime_index
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hpC).toEquiv]
    exact p.centralizer_coprime a a
  intro x hx
  have h1 : (⟨x, hpC hx⟩ : ↥(Subgroup.centralizer ({a.1} : Set G)))
      ∈ (p.H a).subgroupOf (Subgroup.centralizer ({a.1} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hle h1)

/-- **Structure extensionality for `S04.Hypothesis` via the data field `H`.**  `H` is the only
`Type`-valued field of `S04.Hypothesis`; the remaining eight fields are `Prop`s, equal by proof
irrelevance.  So two hypotheses on the same `(G, A, L)` whose `H`-fields coincide are equal.  This
is the structural half of the `dade_H_eq` canonicality (the group theory pins `H`, this packages it
back into a structure equality). -/
theorem dadeHypothesis_ext_of_H_eq {A : Set G}
    {p q : OddOrder.Peterfalvi.S04.Hypothesis G A L} (hH : p.H = q.H) : p = q := by
  cases p with
  | mk s1 s2 s3 H1 c1 c2 c3 c4 c5 =>
    cases q with
    | mk t1 t2 t3 H2 d1 d2 d3 d4 d5 =>
      subst hH
      rfl

/-- The integral Dade map `dadeIntegralCharacterMap` ignores its `FullDadeIsometryData` argument:
its definition extends only `hyp.dadeLinearMap`, so the map is a function of the underlying
`S04.Hypothesis` alone.  Hence equal hypotheses give the same map, regardless of the (unused)
isometry data carried alongside. -/
theorem dadeIntegralCharacterMap_congr_hyp {A : Set G}
    {hyp₁ hyp₂ : OddOrder.Peterfalvi.S04.Hypothesis G A L} (h : hyp₁ = hyp₂)
    (d₁ : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp₁)
    (d₂ : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp₂)
    (φ : ClassFunction ↥L ℂ) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp₁ d₁ φ
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp₂ d₂ φ := by
  subst h; rfl

/-- **(6.8.2.3) map-agreement — the `hmapagree` linchpin.**  On every `H^#`-supported `φ`, the
enlarged `(4.6)` Dade map `dadeIntegralCharacterMap h46.dade0 h46.tau` (on `A₀ = H^# ∪ V^L`)
agrees with the Sibley–Dade `hyp.tau` (the genuine Dade map on `A = H^#`).

Both sides agree on `CF(L, H^#)` with the Dade map of an `S04.Hypothesis` over `(G, H^#, L)`:
restricting `h46.dade0` to `H^#` (`dadeIntegralCharacterMap_restrict_eq_of_support`) yields such a
hypothesis, and by the canonicality `dade_H_eq` it shares its only data field `H` with `hyp.dade`,
hence equals it (`dadeHypothesis_ext_of_H_eq`); since `dadeIntegralCharacterMap` depends only on
the hypothesis (`dadeIntegralCharacterMap_congr_hyp`) and `hyp.tau` unfolds to
`dadeIntegralCharacterMap hyp.dade _`, the two maps agree.  This is the agreement consumed by
`certainTypeSet_isCoherent_tau`
to re-target the certain-type column coherence (built against `h46.dade0`) onto `hyp.tau`. -/
theorem SibleyDadeHypothesis.dade0_map_eq_tau_of_support
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau φ = hyp.tau φ := by
  have hLemmaD :
      h46.dade0.restrict Set.subset_union_left hyp.dade.L_normalizes_A = hyp.dade :=
    dadeHypothesis_ext_of_H_eq
      (funext fun a => dade_H_eq
        (h46.dade0.restrict Set.subset_union_left hyp.dade.L_normalizes_A) hyp.dade a)
  rw [← dadeIntegralCharacterMap_restrict_eq_of_support h46.dade0 h46.tau
        Set.subset_union_left hyp.dade.L_normalizes_A hφ]
  exact dadeIntegralCharacterMap_congr_hyp hLemmaD _ _ φ

/-- **(6.8.2) case-(B) certain-type column coherence for `hyp.tau`, `hmapagree` discharged.**  The
reducible certain-type columns `{μ_j} = certainTypeSet h46 k` are coherent for the genuine
Sibley–Dade map `hyp.tau` — the unconditional form of `certainTypeSet_isCoherent_tau`, with its
map-agreement hypothesis supplied by the canonicality `dade0_map_eq_tau_of_support` (each
`φ ∈ zSupportedSpan` being `H^#`-supported by `support_subset_of_mem_zSupportedSpan`).  This is
the `cX_col` reducible side of the case-(B) `X`-coherence. -/
noncomputable def SibleyDadeHypothesis.certainTypeSet_isCoherent_tau_canonical
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.certainTypeSet_isCoherent_tau h46 hk
    (fun _ hφ => hyp.dade0_map_eq_tau_of_support h46
      (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hφ))

/-- **(6.8.2.3) column-branch map-agreement** (the `hmapagree` conjunct of `CaseBColBundle`),
*unconditional*.  For any nontrivial column `χ₂`, the `hyp.tau`-image of the conjugate column
difference agrees with its enlarged `(4.6)` Dade image
`dadeIntegralCharacterMap h46.dade0 h46.tau`.  This is the column-bundle conjunct that was
*unconstructible* before the canonicality linchpin: the conjugate column is `μ_{χ₂⁻¹}`
(`columnSum_conj_eq`) of equal degree (`columnSum_inv_apply_one`), so the difference is
`H^#`-supported (`columnDiff_support_subset`) and the map-agreement is exactly
`dade0_map_eq_tau_of_support`.  Both bundle-intrinsic column conjuncts — degree equality and this
map-agreement — are thus discharged with no side hypotheses. -/
theorem caseB_column_mapagree
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj) := by
  rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
  exact (hyp.dade0_map_eq_tau_of_support h46
    (OddOrder.Peterfalvi.S06.columnDiff_support_subset h46 hχ₂
      ((inv_ne_one (a := χ₂)).mpr hχ₂)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm)).symm

/-- **(6.8.2.3) raw `X ⊥ Y`, per certain-type constituent** — Peterfalvi (4.1), source level.
A grid character of a column is orthogonal to every `Y`-member.  Both are irreducible
(`SignedIrreducibleDifferenceFamily.mu` is `IrreducibleCharacter`), and distinct *by degree*: a
`Y`-member has degree `|W₁|` (`Yset_apply_one`) but a grid degree is `≡ ±1 (mod |W₁|)`
(`certainType_degree_modEq`), with `|W₁| ≠ 1`.  So the inner product vanishes. -/
theorem inner_columnFamily_mu_Yset_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ClassFunction.inner ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) η = 0 := by
  have hηirr := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hne : ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) ≠ η := by
    intro heq
    obtain ⟨a, ha⟩ := h46.certainType_degree_modEq χ₂ i
    rw [heq, hyp.Yset_apply_one hη] at ha
    have hcard : (Nat.card h46.W1 : ℂ) = (Nat.card hyp.W1 : ℂ) := by rw [hW1]
    rw [hcard] at ha
    have hw1 : Nat.card hyp.W1 ≠ 1 := fun h => hyp.W1_nontrivial (Subgroup.card_eq_one.mp h)
    have hsign : ((h46.columnFamily χ₂).sign : ℂ)
        = (Nat.card hyp.W1 : ℂ) * (1 - (a : ℂ)) := by linear_combination -ha
    have hsignZ : (h46.columnFamily χ₂).sign = (Nat.card hyp.W1 : ℤ) * (1 - a) := by
      exact_mod_cast hsign
    have hdvd1 : (Nat.card hyp.W1 : ℤ) ∣ 1 := by
      have hdvd : (Nat.card hyp.W1 : ℤ) ∣ (h46.columnFamily χ₂).sign := ⟨1 - a, hsignZ⟩
      rcases (h46.columnFamily χ₂).sign_eq with hs | hs
      · rwa [hs] at hdvd
      · rw [hs] at hdvd; exact (dvd_neg).mp hdvd
    exact hw1 (Nat.dvd_one.mp (by exact_mod_cast hdvd1))
  have hkron := irreducibleCharacter_inner_eq_ite ((h46.columnFamily χ₂).mu i)
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
  rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at hkron
  simpa using hkron

/-- **(6.8.2.3) raw `X ⊥ Y`, column form** — Peterfalvi (4.1).  A whole certain-type column
(a sum of grid characters) is orthogonal to every `Y`-member, by additivity over the constituents
(`inner_columnFamily_mu_Yset_eq_zero`).  This is the `hpair` orthogonality of the case-(B) `X ∪ Y`
glue, restricted to the reducible column side. -/
theorem inner_columnSum_Yset_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) η = 0 := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, inner_sum_left]
  exact Finset.sum_eq_zero
    (fun i _ => inner_columnFamily_mu_Yset_eq_zero hyp h46 hW1 hη χ₂ i)

/-- **(6.8.2.3) column-branch orthogonality scalars** (the `hχψ` conjunct of `CaseBColBundle`).
A column is orthogonal to the weighted `Y`-anchor `a • η₁`: pull the natural scalar out
(`inner_smul_right`) and apply the raw column orthogonality `inner_columnSum_Yset_eq_zero`. -/
theorem caseB_column_orthogonal_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (a : ℕ) :
    ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, OddOrder.RepresentationTheory.inner_smul_right,
    inner_columnSum_Yset_eq_zero hyp h46 hW1 hη₁ χ₂, mul_zero]

/-- **(6.8.2.3) column-branch orthogonality scalars, conjugate** (the `hχbarψ` conjunct of
`CaseBColBundle`).  The conjugate column is the inverse column `columnSum h46 χ₂⁻¹`
(`columnSum_conj_eq`), so it too is orthogonal to the weighted `Y`-anchor by
`caseB_column_orthogonal_Yset`. -/
theorem caseB_column_conj_orthogonal_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (a : ℕ) :
    ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0 := by
  rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
  exact caseB_column_orthogonal_Yset hyp h46 hW1 hη₁ χ₂⁻¹ a

/-- **(6.8.2.3) column-anchor difference support.**  Given the degree match at `1`, the column
difference `columnSum h46 χ₂ − a·η₁` is `H^#`-supported.  A column is induced from `H`
(`columnSum_eq_induce_H`, case `h46.K = H`), so this is the `Ind − scalar·η₁` support lemma
`support_indW2_sub_smul_subset_sharpImage` instantiated at the subgroup `H` itself. -/
theorem caseB_column_sub_smul_support
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (a : ℕ)
    (h1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) (1 : ↥L) = (a : ℂ) * η₁ (1 : ↥L)) :
    (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  rw [columnSum_eq_induce_H h46 hHK, ← Nat.cast_smul_eq_nsmul ℂ]
  refine hyp.support_indW2_sub_smul_subset_sharpImage (le_refl H) _ hη₁ (a : ℂ) ?_
  rw [← columnSum_eq_induce_H h46 hHK]; exact h1

/-- **(6.8.2.3) column-branch supports** (the `hSdiff` conjunct of `CaseBColBundle`).  Both running
difference generators are `H^#`-supported: `columnSum − conj` by `columnDiff_support_subset` (the
conjugate is the inverse column, equal degree), and `columnSum − a·η₁` by
`caseB_column_sub_smul_support` (given the degree match `h1`). -/
theorem caseB_column_hSdiff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (a : ℕ)
    (h1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) (1 : ↥L) = (a : ℂ) * η₁ (1 : ↥L)) :
    ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
    exact OddOrder.Peterfalvi.S06.columnDiff_support_subset h46 hχ₂
      ((inv_ne_one (a := χ₂)).mpr hχ₂)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
  · exact caseB_column_sub_smul_support hyp h46 hHK hη₁ χ₂ a h1

/-- **(6.8.2.3) column-branch `ZIrr`-membership** (the `htau1_mema` conjunct of `CaseBColBundle`).
The `hyp.tau`-image of the column difference is a virtual character: the argument
is `H^#`-supported (`caseB_column_sub_smul_support`, given the degree match) and virtual
(`columnSum` a sum of irreducibles, `η₁` irreducible), so the Dade map carries it into `ZIrr G`
(`dadeIntegralCharacterMap_mem_ZIrr_of_supported`, the `(2.6)` integrality of `tau`). -/
theorem caseB_column_htau1_mema
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (a : ℕ)
    (h1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) (1 : ↥L) = (a : ℂ) * η₁ (1 : ↥L)) :
    hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dade hyp.hconj (caseB_column_sub_smul_support hyp h46 hHK hη₁ χ₂ a h1) ?_
  refine Submodule.sub_mem _ ?_
    (nsmul_mem (IsIrreducibleCharacter.mem_ZIrr (hyp.isIrreducibleCharacter_of_mem_Yset hη₁)) a)
  rw [OddOrder.Peterfalvi.S06.columnSum_def]
  exact Submodule.sum_mem _ (fun i _ => ((h46.columnFamily χ₂).mu i).mem_ZIrr)

/-- **(6.8.2.3) weight reconciliation `aθ = θ(1)`.**  When the source `φ` actually occurs in the
central restriction of `θ` (`0 < constituentWeight`), the multiplicity `aθ = ⟨φ, Res^H_{W₂} θ⟩`
equals the degree `θ(1)`.  Indeed `W₂` is central in `H`, so `Res^H_{W₂} θ = θ(1)·λ` for a unique
linear `λ` (Schur, `exists_central_linear_restriction`); then `aθ = θ(1)·⟨φ, λ⟩` with `⟨φ, λ⟩` a
Kronecker delta (both irreducible), and positivity forces it to be `1`.  This reconciles the
multiplicity weight with the degree ratio `θ(1) = χθ(1)/|W₁|` of (6.8.2.3). -/
theorem constituentWeight_eq_apply_one
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)] [Fintype ↥H]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {θ : IrreducibleCharacter ↥H} (hweight : 0 < constituentWeight hφ' θ) :
    (constituentWeight hφ' θ : ℂ) = (θ : ClassFunction ↥H ℂ) 1 := by
  obtain ⟨lam, hlamirr, _hlam1, hres, _⟩ :=
    θ.2.exists_central_linear_restriction (W2.subgroupOf H) hcen
  have hspec := constituentWeight_spec hφ' θ
  rw [hres, OddOrder.RepresentationTheory.inner_smul_right] at hspec
  obtain ⟨d, _hd0, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  rw [hd, star_natCast] at hspec
  have hkron := irreducibleCharacter_inner_eq_ite
    (⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ, hφ'⟩ :
      IrreducibleCharacter ↥(W2.subgroupOf H))
    (⟨lam, hlamirr⟩ : IrreducibleCharacter ↥(W2.subgroupOf H))
  by_cases heq : (⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ, hφ'⟩ :
      IrreducibleCharacter ↥(W2.subgroupOf H)) = ⟨lam, hlamirr⟩
  · rw [if_pos heq] at hkron
    rw [hkron, mul_one] at hspec
    rw [hd]; exact hspec.symm
  · rw [if_neg heq] at hkron
    rw [hkron, mul_zero] at hspec
    exact absurd hspec.symm (by exact_mod_cast hweight.ne')

/-- **(6.8.2.3) column-anchor degree match.**  For a column `columnSum h46 χ₂ = Ind^L_H θ` with the
source occurring in `θ` (`0 < constituentWeight`), the column degree equals the weighted `Y`-anchor
degree: `columnSum(1) = constituentWeight · η₁(1)`.  Indeed `columnSum(1) = (Ind^L_H θ)(1) =
|W₁|·θ(1)` (`induce_apply_one`, `index_H_eq_card_W1`), `η₁(1) = |W₁|` (`Yset_apply_one`), and
`constituentWeight = θ(1)` (`constituentWeight_eq_apply_one`).  This is the `h1` hypothesis that the
support/`ZIrr` column conjuncts need. -/
theorem caseB_column_degree_match
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {θ : IrreducibleCharacter ↥H} (hweight : 0 < constituentWeight hφ' θ)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hcoleq : OddOrder.Peterfalvi.S06.columnSum h46 χ₂
      = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) :
    (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) (1 : ↥L)
      = (constituentWeight hφ' θ : ℂ) * η₁ (1 : ↥L) := by
  rw [hcoleq, ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hyp.Yset_apply_one hη₁,
    constituentWeight_eq_apply_one hW2H hcen hφ' hweight]
  ring

/-- **(6.8.2.3) induced-character degree match** (irreducible-branch form).  For the dispatch weight
`aθ = constituentWeight hφ' θ` (`0 < aθ`), the induced degree matches the weighted `Y`-anchor:
`(Ind^L_H θ)(1) = aθ · η₁(1)`.  Same arithmetic as `caseB_column_degree_match`, for the
induced character directly (no column rewrite). -/
theorem caseB_induce_degree_match
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {θ : IrreducibleCharacter ↥H} (hweight : 0 < constituentWeight hφ' θ)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (1 : ↥L)
      = (constituentWeight hφ' θ : ℂ) * η₁ (1 : ↥L) := by
  rw [ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hyp.Yset_apply_one hη₁,
    constituentWeight_eq_apply_one hW2H hcen hφ' hweight]
  ring

/-- **(6.8.2.3) irreducible-branch anchor difference support** (`CaseBIrrBundle` conjunct).
`Ind^L_H θ − aθ·η₁` is `H^#`-supported, by `support_indW2_sub_smul_subset_sharpImage` at `H`
with the degree match `caseB_induce_degree_match`. -/
theorem caseB_irr_sub_smul_support
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {θ : IrreducibleCharacter ↥H} (hweight : 0 < constituentWeight hφ' θ)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - constituentWeight hφ' θ • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  exact hyp.support_indW2_sub_smul_subset_sharpImage (le_refl H) _ hη₁
    (constituentWeight hφ' θ : ℂ) (caseB_induce_degree_match hyp hW2H hcen hφ' hweight hη₁)

/-- **(6.8.2.3) irreducible-branch `ZIrr`-membership** (`CaseBIrrBundle` conjunct).
`hyp.tau (Ind^L_H θ − aθ·η₁) ∈ ZIrr G`: the argument is `H^#`-supported
(`caseB_irr_sub_smul_support`) and a virtual character (`induce_mem_ZIrr`, `η₁` irreducible), so the
Dade map carries it into `ZIrr G` (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`). -/
theorem caseB_irr_htau1_mema
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {θ : IrreducibleCharacter ↥H} (hweight : 0 < constituentWeight hφ' θ)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) :
    hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - constituentWeight hφ' θ • η₁)
      ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dade hyp.hconj (caseB_irr_sub_smul_support hyp hW2H hcen hφ' hweight hη₁) ?_
  exact Submodule.sub_mem _
    (ClassFunction.induce_mem_ZIrr H (IsIrreducibleCharacter.mem_ZIrr θ.2))
    (nsmul_mem (IsIrreducibleCharacter.mem_ZIrr (hyp.isIrreducibleCharacter_of_mem_Yset hη₁)) _)

/-- **(6.8.2.3) irreducible-branch conjugate difference support** (`CaseBIrrBundle` conjunct).
`(Ind^L_H θ).conj − Ind^L_H θ` is `H^#`-supported, with no irreducibility assumption: both terms are
supported on `H` (`support_induce_subset_of_normal`, conj preserves support), and the difference
vanishes at `1` since `(Ind^L_H θ)(1) = |W₁|·θ(1)` is a (real) positive integer fixed by `star`. -/
theorem caseB_irr_conj_diff_support
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (θ : IrreducibleCharacter ↥H) :
    ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
        - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  have hsupp : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆ (H : Set ↥L) :=
    ClassFunction.support_induce_subset_of_normal H _
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply] at hx
  have hxH : x ∈ H := by
    by_contra hxnotH
    have h1 : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) x = 0 := by
      by_contra h; exact hxnotH (hsupp (ClassFunction.mem_support.mpr h))
    exact hx (by rw [ClassFunction.conj_apply, h1, star_zero, sub_zero])
  have hxne : x ≠ 1 := by
    intro hx1
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    refine hx ?_
    rw [hx1, ClassFunction.conj_apply, ClassFunction.induce_apply_one, hd]
    simp [← Nat.cast_mul]
  change (x : G) ∈ sharpImage H
  exact ⟨Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩, fun hx1G => hxne (Subtype.ext hx1G)⟩

/-- **(6.8.2.3) irreducible-branch irreducibility** (`CaseBIrrBundle` conjunct #1, the gate).
When `Ind^L_H θ` is not a (nontrivial) certain-type column (`hnotcol`) and `θ` is nontrivial, the
induced character is irreducible.  Transport `θ` to `↥h46.K` (`subgroupCongr` +
`compHom_of_surjective`), then apply `induce_isIrreducible_of_forall_chiRestrict_ne`: a nontrivial
column source `chiRestrict χ₂` would give a column equal to the induced character
(`induce_restrict_certainType_eq`), contradicting `hnotcol`; and `chiRestrict 1` is trivial
(`certainType_zero_column_anchor`) while the transported `θ` is not. -/
theorem caseB_irr_induce_isIrreducible
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥H}
    (hθne : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H)
    (hnotcol : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) :
    IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  set e : ↥h46.K ≃* ↥H := MulEquiv.subgroupCongr hHK with he
  set θK : IrreducibleCharacter ↥h46.K :=
    ⟨ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ),
      IsIrreducibleCharacter.compHom_of_surjective e.surjective θ.2⟩ with hθK
  have hθKval : ∀ (x : ↥L) (hx₁ : x ∈ h46.K) (hx₂ : x ∈ H),
      (θK : ClassFunction ↥h46.K ℂ) ⟨x, hx₁⟩
        = (θ : ClassFunction ↥H ℂ) ⟨x, hx₂⟩ := by
    intro x hx₁ hx₂
    show ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ) ⟨x, hx₁⟩ = _
    rw [ClassFunction.compHom_apply]
    rfl
  have hindeq : ClassFunction.induce h46.K (θK : ClassFunction ↥h46.K ℂ)
      = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
    OddOrder.Peterfalvi.S04.Hypothesis.induce_congr_of_subgroup_eq hHK hθKval
  rw [← hindeq]
  refine h46.induce_isIrreducible_of_forall_chiRestrict_ne (fun χ₂ hcontra => ?_)
  by_cases hχ₂1 : χ₂ = 1
  · -- `χ₂ = 1`: `chiRestrict 1` is trivial, so `θ ∘ e = 1`, hence `θ = 1` (`e` surjective)
    subst hχ₂1
    have hcompeq : ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ)
        = ClassFunction.restrict h46.K (trivialClassFunction ↥L) := by
      have h0 : (θK : ClassFunction ↥h46.K ℂ)
          = ClassFunction.restrict h46.K (trivialClassFunction ↥L) := by
        rw [← hcontra, h46.coe_chiRestrict, (h46.certainType_zero_column_anchor).2]
      rw [hθK] at h0; exact h0
    refine hθne (ClassFunction.ext fun h => ?_)
    obtain ⟨k, rfl⟩ := e.surjective h
    have hk := congrArg (fun f : ClassFunction ↥h46.K ℂ => f k) hcompeq
    simp only [ClassFunction.compHom_apply, ClassFunction.restrict_apply,
      trivialClassFunction_apply, MulEquiv.coe_toMonoidHom] at hk
    rw [hk, trivialClassFunction_apply]
  · -- `χ₂ ≠ 1`: `chiRestrict χ₂ = θ_K` forces `columnSum χ₂ = Ind^L_H θ`
    refine hnotcol χ₂ hχ₂1 ?_
    rw [← hindeq, OddOrder.Peterfalvi.S06.columnSum_def,
      ← h46.induce_restrict_certainType_eq χ₂, ← h46.coe_chiRestrict χ₂, hcontra]

/-- `Ind^L_H θ ≠ 1_L`: its degree is a multiple of `|W₁| > 1` (`W₁ ≠ ⊥`), unlike the
degree-`1` trivial character. -/
theorem caseB_induce_ne_trivial
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (θ : IrreducibleCharacter ↥H) :
    ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥L := by
  intro h
  obtain ⟨d, hd0, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have h1 : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)
      = trivialClassFunction ↥L (1 : ↥L) := by rw [h]
  rw [ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hd, trivialClassFunction_apply,
    ← Nat.cast_mul] at h1
  have h2 : Nat.card hyp.W1 * d = 1 := by exact_mod_cast h1
  exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp (Nat.dvd_one.mp ⟨d, h2.symm⟩))

/-- **(6.8.2.3) irreducible-branch non-realness** (`CaseBIrrBundle` conjunct #2).  An irreducible
`Ind^L_H θ` is non-real: it is nontrivial (`caseB_induce_ne_trivial`) and `L` has odd order
(`card_L_odd`), so Peterfalvi (1.1) (`not_isReal_of_ne_trivial_of_odd_card'`) applies. -/
theorem caseB_irr_nonreal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {θ : IrreducibleCharacter ↥H}
    (hirr1 : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))) :
    ¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  refine OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd (χ := ⟨_, hirr1⟩) (fun htriv => caseB_induce_ne_trivial hyp θ ?_)
  rw [← IrreducibleCharacter.coe_trivialIrreducibleCharacter (G := ↥L), ← htriv]

/-- **(6.8.2.3) irreducible-branch self-conjugate orthogonality** (`CaseBIrrBundle` conjunct #8).
`⟨Ind^L_H θ, (Ind^L_H θ).conj⟩ = 0`: both `Ind^L_H θ` (`hirr1`) and its conjugate
(`IsIrreducibleCharacter.conj`) are irreducible and distinct (non-real, `caseB_irr_nonreal`), so the
irreducible Kronecker inner product vanishes. -/
theorem caseB_irr_conj_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {θ : IrreducibleCharacter ↥H}
    (hirr1 : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0 := by
  set Φ := ClassFunction.induce H (θ : ClassFunction ↥H ℂ) with hΦ
  have hnonreal := caseB_irr_nonreal hyp hirr1
  have hne : (⟨Φ, hirr1⟩ : IrreducibleCharacter ↥L) ≠ ⟨Φ.conj, hirr1.conj⟩ := by
    intro heq
    apply hnonreal
    have h2 := congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) heq
    show Φ.conj = Φ
    simpa using h2.symm
  have hkron := irreducibleCharacter_inner_eq_ite (⟨Φ, hirr1⟩ : IrreducibleCharacter ↥L)
    (⟨Φ.conj, hirr1.conj⟩ : IrreducibleCharacter ↥L)
  rw [if_neg hne] at hkron
  simpa using hkron

/-- An irreducible character distinct from a `Y`-member is orthogonal to it (both irreducible, so
the inner product is the Kronecker delta).  The raw `X ⊥ Y` for the irreducible branch. -/
theorem inner_irr_Yset_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ η₁ : ClassFunction ↥L ℂ} (hφirr : IsIrreducibleCharacter φ)
    (hη₁ : η₁ ∈ hyp.Yset) (hne : φ ≠ η₁) : ClassFunction.inner φ η₁ = 0 := by
  have hηirr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hkron := irreducibleCharacter_inner_eq_ite (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
    (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
  rw [if_neg (fun heq => hne (by
    simpa using congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) heq))]
    at hkron
  simpa using hkron

/-- **(6.8.2.3) irreducible-branch anchor orthogonality** (`CaseBIrrBundle` conjunct #6).
The induced character is orthogonal to the weighted `Y`-anchor, given the `X ⊥ Y` distinctness
`Ind^L_H θ ≠ η₁` (a structural input), via `inner_irr_Yset_eq_zero`. -/
theorem caseB_irr_orthogonal_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {θ : IrreducibleCharacter ↥H}
    (hirr1 : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hne : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ≠ η₁) (a : ℕ) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (a • η₁ : ClassFunction ↥L ℂ) = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, OddOrder.RepresentationTheory.inner_smul_right,
    inner_irr_Yset_eq_zero hyp hirr1 hη₁ hne, mul_zero]

/-- **(6.8.2.3) irreducible-branch conjugate anchor orthogonality** (`CaseBIrrBundle` conjunct #7).
The conjugate induced character is orthogonal to the weighted `Y`-anchor, given
`(Ind^L_H θ).conj ≠ η₁`: the conjugate is irreducible, so `inner_irr_Yset_eq_zero` applies. -/
theorem caseB_irr_conj_orthogonal_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {θ : IrreducibleCharacter ↥H}
    (hirr1 : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hne : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj ≠ η₁) (a : ℕ) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, OddOrder.RepresentationTheory.inner_smul_right,
    inner_irr_Yset_eq_zero hyp hirr1.conj hη₁ hne, mul_zero]

/-- A `Y`-member is orthogonal to a distinct irreducible (`Y`-member in the *first* slot, the form
the per-`θ` anchor orthogonality `hirrAnc` needs).  Irreducible Kronecker delta. -/
theorem inner_Yset_irr_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {η ψ : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hψirr : IsIrreducibleCharacter ψ)
    (hne : η ≠ ψ) : ClassFunction.inner η ψ = 0 := by
  have hηirr := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hkron := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    (⟨ψ, hψirr⟩ : IrreducibleCharacter ↥L)
  rw [if_neg (fun heq => hne (by
    simpa using congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) heq))]
    at hkron
  simpa using hkron

/-- **`Ind^L_H θ ≠ η`** for a `Y`-member `η`, when `θ` is non-linear (`θ(1) ≠ 1`): the induced
degree differs from the `Y`-degree `|W₁|`.  The `X ⊥ Y` distinctness for the irreducible branch. -/
theorem caseB_induce_ne_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {θ : IrreducibleCharacter ↥H} (hθ1 : (θ : ClassFunction ↥H ℂ) 1 ≠ 1)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ≠ η := by
  intro h
  have h1 : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L) = η (1 : ↥L) :=
    by rw [h]
  rw [ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hyp.Yset_apply_one hη] at h1
  have hw : (Nat.card hyp.W1 : ℂ) ≠ 0 := by
    have : 0 < Nat.card hyp.W1 := Nat.card_pos
    exact_mod_cast this.ne'
  exact hθ1 (mul_left_cancel₀ hw (by rw [mul_one]; exact h1))

/-- **`(Ind^L_H θ).conj ≠ η`** for `θ` non-linear: the conjugate has the same (real) degree
`|W₁|·θ(1)`, still `≠ |W₁|`. -/
theorem caseB_induce_conj_ne_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {θ : IrreducibleCharacter ↥H} (hθ1 : (θ : ClassFunction ↥H ℂ) 1 ≠ 1)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj ≠ η := by
  intro h
  have h1 : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj (1 : ↥L) = η (1 : ↥L) :=
    by rw [h]
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  rw [ClassFunction.conj_apply, ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hd,
    hyp.Yset_apply_one hη, ← Nat.cast_mul, star_natCast] at h1
  have hw : (Nat.card hyp.W1 : ℂ) ≠ 0 := by
    have : 0 < Nat.card hyp.W1 := Nat.card_pos
    exact_mod_cast this.ne'
  refine hθ1 ?_
  rw [hd]
  have hd1 : (Nat.card hyp.W1 : ℂ) * (d : ℂ) = (Nat.card hyp.W1 : ℂ) * 1 := by
    rw [mul_one, ← Nat.cast_mul]; exact h1
  exact mul_left_cancel₀ hw hd1

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [Invertible (Nat.card ↥H : ℂ)] in
/-- **(6.8.2.3) positive-weight constituents are non-linear** (the single `hnonlin` dispatch input).
When the central source character `φ` of `W₂ ⊆ ⁅H,H⁆` is **non-trivial**, every constituent `θ`
of `Res^H_{W₂}` (i.e. every `θ` with positive Clifford weight `⟨φ, Res^H_{W₂} θ⟩ > 0`) has
degree `> 1`.

Indeed a degree-one `θ` is trivial on the commutator subgroup `⁅H,H⁆ ⊇ W₂.subgroupOf H`
(`IsIrreducibleCharacter.apply_eq_one_of_mem_commutator_of_apply_one_eq_one`), so
`Res^H_{W₂} θ = 1_{W₂}` and the weight `⟨φ, Res θ⟩ = ⟨φ, 1⟩ = 0` (orthogonality of the
non-trivial irreducible `φ` to the trivial one), contradicting `0 < weight`.

This discharges the structural hypothesis `hnonlin` of `caseB_hirrAnc` (and, through `θ ≠ 1` and
the `Ind θ ≠ η` distinctnesses, of `caseB_irr_bundle`).  The two inputs `W₂ ⊆ ⁅H,H⁆` and `φ ≠ 1`
are the case-(B) data: `φ` is a non-trivial central character (the `X`-side selector) and
`W₂ ≤ ⁅H,H⁆` is the CertainType hypothesis `cert.W2 ≤ ⁅H,H⁆`. -/
theorem caseB_hnonlin [Finite ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hderiv : W2.subgroupOf H ≤ commutator ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (hφne : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ
      ≠ trivialClassFunction ↥(W2.subgroupOf H)) :
    ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (i.val : ClassFunction ↥H ℂ) 1 ≠ 1 := by
  rintro ⟨θ, hweight⟩ h1
  -- Degree-one `θ` is trivial on `⁅H,H⁆ ⊇ W₂.subgroupOf H`, so `Res^H_{W₂} θ = 1`.
  have hrestrict : ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ)
      = trivialClassFunction ↥(W2.subgroupOf H) := by
    refine ClassFunction.ext fun n => ?_
    rw [ClassFunction.restrict_apply, trivialClassFunction_apply]
    exact θ.2.apply_eq_one_of_mem_commutator_of_apply_one_eq_one h1 (hderiv n.2)
  -- Hence the multiplicity `⟨φ, Res θ⟩ = ⟨φ, 1⟩ = 0` (φ a non-trivial irreducible).
  have hzero : ClassFunction.inner
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ)
      (ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ)) = 0 := by
    have hne : (⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ, hφ'⟩
        : IrreducibleCharacter ↥(W2.subgroupOf H)) ≠ trivialIrreducibleCharacter _ := by
      intro heq
      apply hφne
      have h := congrArg (fun c : IrreducibleCharacter ↥(W2.subgroupOf H) =>
        (c : ClassFunction ↥(W2.subgroupOf H) ℂ)) heq
      simpa only [IrreducibleCharacter.coe_mk,
        IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h
    rw [hrestrict, ← IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      ← IrreducibleCharacter.coe_mk _ hφ', irreducibleCharacter_inner_eq_ite, if_neg hne]
  exact (constituentWeight_pos_iff hφ' θ).mp hweight hzero

/-- **(6.8.2.3) per-`θ` anchor-vs-constituent orthogonality** (`hirrAnc` of the dispatch).  For a
positive-weight `θ` whose `Ind^L_H θ` is not a column (irreducible branch), the four inner products of
`η₁, η̄₁` against the induced character and its conjugate vanish: each is a `Y`-member against a
distinct irreducible (`inner_Yset_irr_eq_zero`), distinctness from non-linearity `hnonlin`. -/
theorem caseB_hirrAnc
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hnonlin : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (i.val : ClassFunction ↥H ℂ) 1 ≠ 1) :
    ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
          OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
        ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0
        ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁.conj
            (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0 := by
  intro i hnotcol
  have hθne : (i.val : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H := fun heq =>
    hnonlin i (by rw [heq, trivialClassFunction_apply])
  have h1 := caseB_irr_induce_isIrreducible h46 hHK hθne hnotcol
  have hconj := hyp.Yset_closedUnderConjugate hη₁
  refine ⟨inner_Yset_irr_eq_zero hyp hη₁ h1 (caseB_induce_ne_Yset hyp (hnonlin i) hη₁).symm,
    inner_Yset_irr_eq_zero hyp hη₁ h1.conj (caseB_induce_conj_ne_Yset hyp (hnonlin i) hη₁).symm,
    inner_Yset_irr_eq_zero hyp hconj h1 (caseB_induce_ne_Yset hyp (hnonlin i) hconj).symm,
    inner_Yset_irr_eq_zero hyp hconj h1.conj
      (caseB_induce_conj_ne_Yset hyp (hnonlin i) hconj).symm⟩

/-- The `tau1` field of a (5.4) decomposition is unchanged when its `χ`-index is transported along
an equality `χ = χ'` (the field type `IntegralCharacterMap ↥L G` does not mention `χ`).  Used to
read off `tau1 = hyp.tau` through the column-branch index cast of the per-constituent dispatch. -/
theorem charPsiDecomp_eqRec_tau1
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ χ' ψ : ClassFunction ↥L ℂ} (h : χ = χ')
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) :
    (h ▸ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ' ψ).tau1 = D.tau1 := by
  cases h; rfl

/-- The `imageFamily.imageSet` of a (5.4) decomposition is unchanged when its `χ`-index is
transported along `χ = χ'` (`imageSet : Finset (ClassFunction G ℂ)` does not mention `χ`).  Used to
read off the `X`-image set through the column-branch index cast of the per-constituent dispatch,
for the seam-1 orthogonality `⟨cY.ext η₁, X-member⟩ = 0`. -/
theorem charPsiDecomp_eqRec_imageSet
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ χ' ψ : ClassFunction ↥L ℂ} (h : χ = χ')
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) :
    (h ▸ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ' ψ).imageFamily.imageSet
      = D.imageFamily.imageSet := by
  cases h; rfl

/-- The `X` image side of a (5.4) decomposition is unchanged when its `χ`-index is transported along
`χ = χ'` (`X : ClassFunction G ℂ` does not mention `χ`).  Used to read the column-branch `X` through
the dispatch index cast for the seam-1 orthogonality `⟨X, cY.ext η₁⟩ = 0`. -/
theorem charPsiDecomp_eqRec_X
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ χ' ψ : ClassFunction ↥L ℂ} (h : χ = χ')
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) :
    (h ▸ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ' ψ).X = D.X := by
  cases h; rfl

/-- The `Y` orthogonal side of a (5.4) decomposition is unchanged when its `χ`-index is transported
along `χ = χ'` (`Y : ClassFunction G ℂ` does not mention `χ`).  Used to read the column-branch `Y`
through the dispatch index cast for the integrality `⟨Y, cY.ext η₁⟩ ∈ ℤ`. -/
theorem charPsiDecomp_eqRec_Y
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ χ' ψ : ClassFunction ↥L ℂ} (h : χ = χ')
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) :
    (h ▸ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ' ψ).Y = D.Y := by
  cases h; rfl

/-- **(6.8.2.3) integrality of the orthogonal side against a `ZIrr` anchor.**  For any (5.4)
decomposition `D` with image side `D.X ⊥ Y₀` (`hX`), `τ₁`-image a virtual character
`D.tau1 (χ − ψ) ∈ ZIrr G` (`hτmem`) and a virtual-character anchor `Y₀ ∈ ZIrr G` (`hY₀`), the
orthogonal residual pairs integrally with the anchor:
`⟨D.Y, Y₀⟩ = ⟨D.X, Y₀⟩ − ⟨D.tau1 (χ−ψ), Y₀⟩ = −⟨D.tau1 (χ−ψ), Y₀⟩ ∈ ℤ`.
This is the route-independent `hbi` of `per_phi_anchored_image` (`Y = X − τ₁(χ−ψ)` from `tau1_image`;
`⟨τ₁(χ−ψ), Y₀⟩ ∈ ℤ` by `inner_mem_ZIrr_int`). -/
theorem psiDecomp_Y_inner_int {L' G' : Type*} [Group L'] [Group G'] [Fintype L'] [Fintype G']
    [Invertible (Nat.card L' : ℂ)] [Invertible (Nat.card G' : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L' G'} {χ ψ : ClassFunction L' ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ)
    {Y₀ : ClassFunction G' ℂ}
    (hX : ClassFunction.inner D.X Y₀ = 0)
    (hτmem : D.tau1 (χ - ψ) ∈ ZIrr G')
    (hY₀ : Y₀ ∈ ZIrr G') :
    ∃ n : ℤ, ClassFunction.inner D.Y Y₀ = (n : ℂ) := by
  obtain ⟨n, hn⟩ := ClassFunction.inner_mem_ZIrr_int hτmem hY₀
  refine ⟨-n, ?_⟩
  have hYeq : D.Y = D.X - D.tau1 (χ - ψ) := by rw [D.tau1_image]; abel
  rw [hYeq, ClassFunction.inner_sub_left, hX, hn]
  push_cast; ring

/-- The per-`θ` **column-branch bundle** (mixed dispatch).  For each nontrivial column character
`χ₂` whose certain-type column `μ_j = columnSum h46 χ₂` equals `Ind^L_H θ`, the structural inputs of
`columnDecompositionTau`: equal column degrees, the `τ`-image agreement on `μ_j − μ̄_j`, the two
`H^#`-supports, the `ZIrr`-membership of `(μ_j − a·η₁)^{hyp.tau}`, and the three (5.2.c) orthogonality
scalars.  Extracted as an abbreviation so the dispatch lemmas share one bundle type with
`caseB_constituentDecomposition` (definitionally the same `hcol` Prop). -/
abbrev CaseBColBundle (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    (θ : IrreducibleCharacter ↥H) (η₁ : ClassFunction ↥L ℂ) (a : ℕ) : Prop :=
  ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) →
    (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
        = ∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1)
    ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
        = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
    ∧ (∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
          OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
        s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        (a • η₁ : ClassFunction ↥L ℂ) = 0)
    ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
        (a • η₁ : ClassFunction ↥L ℂ) = 0)

/-- The per-`θ` **irreducible-branch bundle** (mixed dispatch).  When no nontrivial column equals
`Ind^L_H θ`, the structural inputs of `irreducibleDecompositionTau` (= `decompositionDaFromDadeOfDiff
hyp.dade hyp.hconj`): irreducibility, non-realness, the two `H^#`-supports, the `ZIrr`-membership of
`(Ind^L_H θ − a·η₁)^{hyp.tau}`, and the (5.2.c) orthogonality scalars.  Shared with
`caseB_constituentDecomposition` (definitionally the same `hirr` Prop). -/
abbrev CaseBIrrBundle (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    (θ : IrreducibleCharacter ↥H) (η₁ : ClassFunction ↥L ℂ) (a : ℕ) : Prop :=
  (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
    IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
    ∧ (¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    ∧ (((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
          - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    ∧ ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    ∧ (hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
    ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (a • η₁ : ClassFunction ↥L ℂ) = 0)
    ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
        (a • η₁ : ClassFunction ↥L ℂ) = 0)
    ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)

/-- **(6.8.2.3) full column-branch bundle.**  Assembles the entire `CaseBColBundle` for the dispatch
weight `aθ = constituentWeight hφ' θ`: all six conjuncts hold.  The two degree-coupled ones (`hSdiff`,
`htau1_mema`) are supplied with the degree match `caseB_column_degree_match` (needs the source to
occur in `θ`, `0 < constituentWeight`); the rest are unconditional.  This is the column-branch input
`hcol` of the mixed per-`φ` dispatch (`caseB_per_phi_anchored_fromYset`). -/
theorem caseB_column_bundle
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {θ : IrreducibleCharacter ↥H} (hweight : 0 < constituentWeight hφ' θ)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) :
    CaseBColBundle hyp h46 θ η₁ (constituentWeight hφ' θ) := by
  intro χ₂ hχ₂ hcoleq
  have h1 := caseB_column_degree_match hyp h46 hW2H hcen hφ' hweight hη₁ hcoleq
  exact ⟨(OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm,
    caseB_column_mapagree hyp h46 hχ₂,
    caseB_column_hSdiff hyp h46 hHK hη₁ hχ₂ (constituentWeight hφ' θ) h1,
    caseB_column_htau1_mema hyp h46 hHK hη₁ χ₂ (constituentWeight hφ' θ) h1,
    caseB_column_orthogonal_Yset hyp h46 hW1 hη₁ χ₂ (constituentWeight hφ' θ),
    caseB_column_conj_orthogonal_Yset hyp h46 hW1 hη₁ χ₂ (constituentWeight hφ' θ)⟩

/-- **(6.8.2.3) full irreducible-branch bundle.**  Assembles the entire `CaseBIrrBundle` for the
dispatch weight `aθ = constituentWeight hφ' θ`.  Given the structural inputs `θ ≠ 1` (for
irreducibility) and the `X ⊥ Y` distinctnesses of the induced character and its conjugate from the
anchor, all eight conjuncts are discharged (irreducibility, non-realness, the two supports, `ZIrr`,
the two anchor orthogonalities, self-conjugate orthogonality).  This is the irreducible-branch input
`hirr` of the mixed per-`φ` dispatch. -/
theorem caseB_irr_bundle
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {θ : IrreducibleCharacter ↥H} (hweight : 0 < constituentWeight hφ' θ)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hθne : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H)
    (hneη : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ≠ η₁)
    (hneη' : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj ≠ η₁) :
    CaseBIrrBundle hyp h46 θ η₁ (constituentWeight hφ' θ) := by
  intro hnotcol
  have h1 := caseB_irr_induce_isIrreducible h46 hHK hθne hnotcol
  exact ⟨h1, caseB_irr_nonreal hyp h1, caseB_irr_conj_diff_support hyp θ,
    caseB_irr_sub_smul_support hyp hW2H hcen hφ' hweight hη₁,
    caseB_irr_htau1_mema hyp hW2H hcen hφ' hweight hη₁,
    caseB_irr_orthogonal_Yset hyp h1 hη₁ hneη (constituentWeight hφ' θ),
    caseB_irr_conj_orthogonal_Yset hyp h1 hη₁ hneη' (constituentWeight hφ' θ),
    caseB_irr_conj_inner hyp h1⟩

/-- **(6.8.2.3) column dispatch bundle over the whole positive-weight family** (`hcol` input of
`caseB_per_phi_anchored_fromYset`).  Maps `caseB_column_bundle` over every positive-weight
constituent `i`; the column branch needs no non-linearity hypothesis (it is gated on the column
witness equation `columnSum χ₂ = Ind^L_H θ`). -/
theorem caseB_hcol
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) :
    ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBColBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val) :=
  fun i => caseB_column_bundle hyp h46 hHK hW1 hW2H hcen hφ' i.property hη₁

/-- **(6.8.2.3) irreducible dispatch bundle over the whole positive-weight family** (`hirr` input of
`caseB_per_phi_anchored_fromYset`).  Maps `caseB_irr_bundle` over every positive-weight constituent
`i`, supplying the three structural inputs `θ ≠ 1`, `Ind θ ≠ η₁`, `(Ind θ)‾ ≠ η₁` from the single
non-linearity hypothesis `hnonlin` (`caseB_hnonlin`): `θ ≠ 1` since `θ(1) ≠ 1`, and the two `≠ η₁`
distinctnesses by `caseB_induce_ne_Yset` / `caseB_induce_conj_ne_Yset` (degree mismatch). -/
theorem caseB_hirr
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hnonlin : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (i.val : ClassFunction ↥H ℂ) 1 ≠ 1) :
    ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBIrrBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val) :=
  fun i => caseB_irr_bundle hyp h46 hHK hW2H hcen hφ' i.property hη₁
    (fun heq => hnonlin i (by rw [heq, trivialClassFunction_apply]))
    (caseB_induce_ne_Yset hyp (hnonlin i) hη₁)
    (caseB_induce_conj_ne_Yset hyp (hnonlin i) hη₁)

/-- **(6.8.2.3) per-constituent decomposition (mixed dispatch).**  For a constituent `θ : Irr H` of
`Ind^L_K φ` (with `K = H`, case (c2)), the (5.4) decomposition data of `Ind^L_H θ` against the
Sibley–Dade map `hyp.tau`, dispatched on whether `Ind^L_H θ` is a reducible certain-type column
`μ_j = columnSum h46 χ₂` or an irreducible induced character:

* **column branch** (`∃ χ₂ ≠ 1, columnSum h46 χ₂ = Ind^L_H θ`): `columnDecompositionTau` (the
  rebuilt certain-type `R(μ_j)` family), with the column character rewritten to `Ind^L_H θ` along
  the witness equation;
* **irreducible branch** (no nontrivial column equals `Ind^L_H θ`): `irreducibleDecompositionTau`
  (`decompositionDaFromDadeOfDiff hyp.dade hyp.hconj`).

Both branches land in the *same* map `hyp.tau`, so the family
`fun i => caseB_constituentDecomposition …` feeds the pinning `per_phi_anchored_image`.  The per-`θ`
structural hypotheses of each branch are supplied by the (conditional) bundles `hcol` / `hirr`; they
are discharged at the family construction
from the §5/§6 X-member machinery (column: certain-type `(4.9)` reflection; irreducible: as in the
case-A Dade chain). -/
noncomputable def caseB_constituentDecomposition
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) →
      (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
          = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
              - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
      ∧ (∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
            OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
          s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
          (a • η₁ : ClassFunction ↥L ℂ) = 0))
    (hirr : (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
      IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      ∧ (¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
      ∧ (((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
            - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
          (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (a • η₁) := by
  classical
  by_cases hcase : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
  · -- column branch: the witness `χ₂` is extracted by choice (the goal is `Type`-valued, so a
    -- direct `obtain` on the `Prop`-`∃` would be an illegal large elimination).  The decomposition
    -- bundle is consumed by `.1`/`.2.…` projections (not `obtain`/`And.casesOn`) so that the `tau1`
    -- field reduces through `caseB_constituentDecomposition_tau1`; the index is cast by `heq ▸`.
    have hχ₂ne := hcase.choose_spec.1
    have heq := hcase.choose_spec.2
    have hb := hcol _ hχ₂ne heq
    exact heq ▸ columnDecompositionTau hyp h46 hχ₂ne hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
      hb.2.2.2.2.1 hb.2.2.2.2.2
  · -- irreducible branch: no nontrivial column equals `Ind^L_H θ`
    have hnc : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
      fun χ₂ hne heq2 => hcase ⟨χ₂, hne, heq2⟩
    have hb := hirr hnc
    exact irreducibleDecompositionTau hyp θ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1
      hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2

/-- The `tau1` field of `caseB_constituentDecomposition` is `hyp.tau`, in both dispatch branches
(`columnDecompositionTau`/`irreducibleDecompositionTau` both build via `ofProjection … hyp.tau …`,
and `hyp.tau = dadeIntegralCharacterMap hyp.dade …`).  This is the `htau1` input of
`per_phi_anchored_image` for the mixed per-`φ` family. -/
theorem caseB_constituentDecomposition_tau1
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    {hcol _hirr} :
    (caseB_constituentDecomposition (a := a) (η₁ := η₁) hyp h46 θ hcol _hirr).tau1 = hyp.tau := by
  unfold caseB_constituentDecomposition
  split
  · rw [charPsiDecomp_eqRec_tau1]; rfl
  · rfl

/-- **(6.8.2.3) the mixed per-`φ` decomposition family.**  Over the positive-weight subtype
`{θ : Irr H // 0 < aθ}` (`aθ = ⟨φ, Res^H_{W₂} θ⟩`), each constituent `Ind^L_H θ` of `Ind^L_{W₂} φ`
is decomposed against `hyp.tau` by the per-`θ` dispatch `caseB_constituentDecomposition` (column /
irreducible).  This is the family `D` fed to `caseB_per_phi_anchored`; its `tau1 = hyp.tau` is
`caseB_constituentDecomposition_tau1`.  The per-`θ` column/irreducible bundles `hcol`/`hirr` are the
genuine §5/§6 discharge (supplied at the capstone). -/
noncomputable def caseB_phi_family
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H)
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ}
    (hcol : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        = ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) →
      (∑ k, ((h46.columnFamily χ₂).mu k : ClassFunction ↥L ℂ) 1
          = ∑ k, ((h46.columnFamily χ₂⁻¹).mu k : ClassFunction ↥L ℂ) 1)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
          = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
              - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
      ∧ (∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
            OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - constituentWeight hφ' i.val • η₁}
            : Set (ClassFunction ↥L ℂ)),
          s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - constituentWeight hφ' i.val • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0))
    (hirr : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
      IsIrreducibleCharacter (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
      ∧ (¬ ClassFunction.IsReal (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)))
      ∧ (((ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj
            - ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ ((ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
          - constituentWeight hφ' i.val • η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
          - constituentWeight hφ' i.val • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
          (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0)) :
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁) :=
  fun i => caseB_constituentDecomposition hyp h46 i.val (hcol i) (hirr i)

/-- The mixed per-`φ` family lands in `tau1 = hyp.tau` at every constituent — the `htau1` input of
`caseB_per_phi_anchored`. -/
theorem caseB_phi_family_tau1
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H)
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ} {hcol _hirr}
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    (caseB_phi_family hyp h46 hW2H hφ' (η₁ := η₁) hcol _hirr i).tau1 = hyp.tau :=
  caseB_constituentDecomposition_tau1 hyp h46 i.val

/-- **(6.8.2.3) seam-1 orthogonality, column branch.**
`⟨(columnDecompositionTau …).X, cY.ext η₁⟩ = 0`.  The column decomposition's image side
`X ∈ ℤ[R(μ_j)]` is orthogonal to the `Y`-anchor extension `cY.extension η₁`: by
`inner_X_Y_eq_zero_of_orthogonal` it suffices that each member of `R(μ_j) = certainTypeR.imageSet`
(a signed `±δ_j·ω_{ij}^σ`, `certainTypeRImage`) is `⊥ cY.extension η₁`, which is
`inner_coherent_extension_certainTypeOmegaSigma_eq_zero` (the certain-type seam-1, generic in the
coherence `cY`).  The partner anchor `η'` supplies the supported difference `η₁ − η'` the seam-1
proof needs (the `V`-vanishing of `cY.extension η₁ − cY.extension η'`). -/
theorem columnDecompositionTau_X_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
    (hSdiff : ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    (hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η' : ClassFunction ↥L ℂ} (hη₁Y : η₁ ∈ hyp.Yset) (hη'Y : η' ∈ hyp.Yset)
    (hη₁irr : IsIrreducibleCharacter η₁) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ClassFunction.inner
        (columnDecompositionTau hyp h46 hχ₂ hdeg hmapagree hSdiff htau1_mema hχψ hχbarψ).X
        (cY.extension η₁) = 0 := by
  classical
  apply inner_X_Y_eq_zero_of_orthogonal
  intro α hα
  change α ∈ Finset.univ.image (OddOrder.Peterfalvi.S06.certainTypeRImage h46 χ₂ χ₂⁻¹) at hα
  rw [Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
  cases b
  · simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK cY hη₁Y hη'Y hη₁irr hη'irr
        hee hsupp χ₂ i, mul_zero]
  · simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK cY hη₁Y hη'Y hη₁irr hη'irr
        hee hsupp χ₂⁻¹ i, mul_zero]

/-- **(6.8.2.3) seam-1 orthogonality, irreducible branch.**
`⟨(irreducibleDecompositionTau …).X, cY.extension η₁⟩ = 0`.  The irreducible constituent's image
side is orthogonal to the `Y`-anchor extension — a re-instantiation of the case-A X-member
orthogonality `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` (the Dade
`R(Ind^L_H θ)` family is `⊥ cY.extension η₁` by the (5.2.e) family orthogonality), with
`χ = ⟨Ind^L_H θ, hirr⟩` and the `Y`-anchor `chi1 = ⟨η₁, hη₁irr⟩`.  The `χ`-facts are exactly
`irreducibleDecompositionTau`'s hypotheses; the `η₁`-facts (real, supports, `Yset`-membership,
`ZIrr` extension, orthogonality to the constituent) are the per-anchor data the (5.2.e) family
orthogonality needs. -/
theorem irreducibleDecompositionTau_X_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (θ : IrreducibleCharacter ↥H)
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hreal : ¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    (hdiffsupp : ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
        - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hdiffasupp : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχχbar' : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1S1 : η₁ ∈ hyp.Yset) (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    (hc1χ : ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0)
    (hc1χbar : ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)
    (hc1barχ : ClassFunction.inner η₁.conj (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0)
    (hc1barχbar : ClassFunction.inner η₁.conj
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    ClassFunction.inner
        (irreducibleDecompositionTau hyp θ hirr hreal hdiffsupp hdiffasupp htau1_mema
          hχaχ1 hχbaraχ1 hχχbar').X
        (cY.extension η₁) = 0 :=
  inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero hyp.dade hyp.hconj cY
    ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ ⟨η₁, hη₁irr⟩
    hreal hdiffsupp hdiffasupp htau1_mema hχaχ1 hχbaraχ1 hχχbar'
    hrealc1 hdiffsuppc1 hc1S1 hc1barS1 hνZc1 hc1c1bar hc1χ hc1χbar hc1barχ hc1barχbar

/-- **(6.8.2.3) `hsq` over the positive-weight subtype.**  The Clifford square-sum
`∑_θ ⟨φ, Res^H_{W₂} θ⟩² = |H : W₂|` (`sum_inner_restrict_sq_eq_index`, `W₂` central in `H`),
reindexed to the positive-weight subtype `{θ // 0 < aθ}` (zero-weight constituents drop) and cast to
`ℤ`.  This is the `hsq` input of `per_phi_anchored_image` (the `n = |H : W₂|` of the (6.8.2.2)
aggregate). -/
theorem sum_constituentWeight_sq_subtype {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (hcen : K.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥K ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)) :
    ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
        ((constituentWeight hφ' i.val : ℤ)) ^ 2 = ((K.subgroupOf H).index : ℤ) := by
  classical
  -- the full square-sum over `Irr H`, in `ℤ`-form
  have hfull : (∑ θ : IrreducibleCharacter ↥H, ((constituentWeight hφ' θ : ℤ)) ^ 2)
      = ((K.subgroupOf H).index : ℤ) := by
    have key := sum_inner_restrict_sq_eq_index (M := ↥H) (N := K.subgroupOf H) hcen hφ'
    simp only [constituentWeight_spec hφ'] at key
    have hcast : ((∑ θ : IrreducibleCharacter ↥H, ((constituentWeight hφ' θ : ℤ)) ^ 2 : ℤ) : ℂ)
        = (((K.subgroupOf H).index : ℤ) : ℂ) := by
      push_cast
      simp only [pow_two]
      exact key
    exact_mod_cast hcast
  refine Eq.trans ?_ hfull
  exact (sum_eq_sum_pos_weight_subtype (constituentWeight hφ')
    (fun θ => ((constituentWeight hφ' θ : ℤ)) ^ 2)
    (fun θ hθ => by
      change (constituentWeight hφ' θ : ℤ) ^ 2 = 0
      rw [hθ]; norm_num)).symm

/-- **(6.8.2.2)→(6.8.2.3) aggregate `hagg` for the mixed per-`φ` family.**  The (6.8.2.2)
decomposition `τ(Ind^L_{W₂} φ − |H:W₂|·η₁) = Xagg − |H:W₂|·Y₀` (`hdecomp`, from
`exists_decomposition_caseB`), combined with the constituent sum
`Ind^L_{W₂} φ − |H:W₂|·η₁ = ∑_θ aθ·(Ind^L_H θ − aθ·η₁)`
(`sum_smul_constituent_diff_pos_weight_subtype`) and the per-constituent images
`τ(Ind^L_H θ − aθ·η₁) = (D θ).X − (D θ).Y` (`(D θ).tau1_image`, `tau1 = hyp.tau` via `htau1`), gives
the `hagg` input of `per_phi_anchored_image`:
`Xagg − |H:W₂|·Y₀ = ∑_θ aθ·((D θ).X − (D θ).Y)`.  The source aggregate's `ℂ`-scalar `(aθ : ℂ)·η₁`
is reconciled with the family's `ℕ`-anchor `aθ • η₁` by `Nat.cast_smul_eq_nsmul`. -/
theorem caseB_hagg
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ}
    (D : (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg Y₀ : ClassFunction G ℂ}
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • Y₀) :
    Xagg - (((W2.subgroupOf H).index : ℤ) : ℂ) • Y₀
      = ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
          ((constituentWeight hφ' i.val : ℤ) : ℂ) • ((D i).X - (D i).Y) := by
  have hagg := aggregate_eq_sum_of_constituent (L := L) Finset.univ hyp.tau
    (fun i => ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
      - constituentWeight hφ' i.val • η₁)
    (fun i => (D i).X) (fun i => (D i).Y) (fun i => (constituentWeight hφ' i.val : ℤ))
    (β := ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
    (n := ((W2.subgroupOf H).index : ℤ))
    -- `hmemimg`: each constituent image is `(D i).tau1_image`, with `tau1 = hyp.tau`.
    (fun i _ => by have h := (D i).tau1_image; rw [htau1 i] at h; exact h)
    -- `hconstit`: the source aggregate, with the `ℂ`-anchor reconciled to the `ℕ`-anchor.
    ((sum_smul_constituent_diff_pos_weight_subtype hW2H hcen φ hφ' η₁).trans
      (Finset.sum_congr rfl fun i _ => by
        simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]))
    -- `hdecomp`: the (6.8.2.2) decomposition (`n = |H:W₂|`), bridging the `ℕ`/`ℤ` index cast.
    (by exact_mod_cast hdecomp)
  exact hagg

/-- **Peterfalvi (6.8.2.3), the per-`φ` anchored image (mixed family, abstract `D`).**  For the
per-`φ` decomposition family `D` (each constituent `Ind^L_H θ` of `Ind^L_{W₂} φ` decomposed against
`hyp.tau`, e.g. by the dispatch `caseB_constituentDecomposition`), with `(D θ).tau1 = hyp.tau`, the
seam-`1` orthogonality `(D θ).X ⊥ Y₀` (`hXorth`) and integrality `⟨(D θ).Y, Y₀⟩ ∈ ℤ` (`hbi`), and
the (6.8.2.2) decomposition `hdecomp`/`hXaggorth` of `exists_decomposition_caseB`, the pinning gives
the **anchored image**
`(Ind^L_H θ − aθ·η₁)^{hyp.tau} = (D θ).X − aθ·Y₀`   (`Y₀ = cY.extension η₁`, `aθ = ⟨φ, Res θ⟩`).

This is the route-independent (6.8.2.3) core: the `Xagg`/`hsq`/`hagg` are assembled internally
(`caseB_hagg`, `sum_constituentWeight_sq_subtype`); only the family `D` (the constituent dispatch)
and its per-`θ` orthogonality/integrality remain for the capstone. -/
theorem caseB_per_phi_anchored
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (D : (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg : ClassFunction G ℂ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
    {b : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ} → ℤ}
    (hXorth : ∀ i, ClassFunction.inner (D i).X (cY.extension η₁) = 0)
    (hbi : ∀ i, ClassFunction.inner (D i).Y (cY.extension η₁) = (b i : ℂ))
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) - constituentWeight hφ' i.val • η₁)
      = (D i).X - (constituentWeight hφ' i.val : ℂ) • cY.extension η₁ :=
  per_phi_anchored_image hyp cY hη₁ Finset.univ D htau1 hXaggorth
    (caseB_hagg hyp hW2H hcen hφ' D htau1 hdecomp)
    (sum_constituentWeight_sq_subtype hW2H hcen hφ')
    (fun i _ => hXorth i) (fun i _ => hbi i) i (Finset.mem_univ i) i.2

/-- **(6.8.2.3) the `τ₁`-image of the dispatch is a virtual character.**  For the per-constituent
dispatch `caseB_constituentDecomposition`, `hyp.tau (Ind^L_H θ − a·η₁) ∈ ZIrr G`, extracted from the
appropriate branch bundle (`hcol`/`hirr`): on the column branch the witness equation rewrites
`Ind^L_H θ` to `μ_j = columnSum h46 χ₂` and the column bundle's `ZIrr`-conjunct applies; on the
irreducible branch the irreducible bundle's `ZIrr`-conjunct applies directly.  This is the `hτmem`
input of `psiDecomp_Y_inner_int` for the dispatch (via `caseB_constituentDecomposition_tau1`). -/
theorem caseB_constituentDecomposition_tau1_mem_ZIrr
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : CaseBColBundle hyp h46 θ η₁ a) (hirr : CaseBIrrBundle hyp h46 θ η₁ a) :
    hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G := by
  classical
  by_cases hcase : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
  · obtain ⟨χ₂, hne, heq⟩ := hcase
    rw [← heq]
    exact (hcol χ₂ hne heq).2.2.2.1
  · exact (hirr (fun χ₂ hne heq2 => hcase ⟨χ₂, hne, heq2⟩)).2.2.2.2.1

/-- **(6.8.2.3) seam-1 orthogonality of the dispatch.**  `⟨(caseB_constituentDecomposition …).X,
cY.extension η₁⟩ = 0`, dispatched per branch through the index cast (`charPsiDecomp_eqRec_X`): on the
column branch the certain-type seam-1 `columnDecompositionTau_X_orthogonal` (using the partner anchor
`η' ≠ η₁ ∈ Yset`), on the irreducible branch the Dade family seam-1
`irreducibleDecompositionTau_X_orthogonal` (using the per-`θ` anchor-vs-constituent orthogonality
`hirrAnc`).  The partner data and the `η₁`-anchor data are explicit hypotheses (the genuine §5 content
discharged at the capstone); this lemma is the pure branch plumbing. -/
theorem caseB_constituentDecomposition_X_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : CaseBColBundle hyp h46 θ η₁ a) (hirr : CaseBIrrBundle hyp h46 θ η₁ a)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hη₁Y : η₁ ∈ hyp.Yset) (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    {η' : ClassFunction ↥L ℂ} (hη'Y : η' ∈ hyp.Yset) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hirrAnc : (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
      ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0
      ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁.conj
          (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    ClassFunction.inner (caseB_constituentDecomposition hyp h46 θ hcol hirr).X
        (cY.extension η₁) = 0 := by
  classical
  unfold caseB_constituentDecomposition
  split
  · rw [charPsiDecomp_eqRec_X]
    exact columnDecompositionTau_X_orthogonal hyp h46 hHK _ _ _ _ _ _ _ cY
      hη₁Y hη'Y hη₁irr hη'irr hee hsupp
  · next hneg =>
    have hncond : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
      fun χ₂ hne heq2 => hneg ⟨χ₂, hne, heq2⟩
    obtain ⟨hc1χ, hc1χbar, hc1barχ, hc1barχbar⟩ := hirrAnc hncond
    exact irreducibleDecompositionTau_X_orthogonal hyp θ _ _ _ _ _ _ _ _ cY hη₁irr
      hrealc1 hdiffsuppc1 hη₁Y hc1barS1 hνZc1 hc1c1bar hc1χ hc1χbar hc1barχ hc1barχbar

/-- **(6.8.2.3) integrality of the dispatch's orthogonal side.**  `⟨(caseB_constituentDecomposition
…).Y, cY.extension η₁⟩ ∈ ℤ`, via the route-independent `psiDecomp_Y_inner_int`: the image side is
`⊥ cY.extension η₁` (`caseB_constituentDecomposition_X_orthogonal`), the `τ₁`-image is a virtual
character (`caseB_constituentDecomposition_tau1_mem_ZIrr`, read through
`caseB_constituentDecomposition_tau1`), and the anchor `cY.extension η₁ ∈ ZIrr G` (`hνZc1`).  This is
the `hbi` of `caseB_per_phi_anchored` for the dispatch family. -/
theorem caseB_constituentDecomposition_Y_inner_int
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : CaseBColBundle hyp h46 θ η₁ a) (hirr : CaseBIrrBundle hyp h46 θ η₁ a)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hη₁Y : η₁ ∈ hyp.Yset) (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    {η' : ClassFunction ↥L ℂ} (hη'Y : η' ∈ hyp.Yset) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hirrAnc : (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
      ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0
      ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁.conj
          (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    ∃ n : ℤ, ClassFunction.inner (caseB_constituentDecomposition hyp h46 θ hcol hirr).Y
      (cY.extension η₁) = (n : ℂ) := by
  apply psiDecomp_Y_inner_int (caseB_constituentDecomposition hyp h46 θ hcol hirr)
  · exact caseB_constituentDecomposition_X_orthogonal hyp h46 hHK θ hcol hirr cY hη₁Y hη₁irr
      hrealc1 hdiffsuppc1 hc1barS1 hνZc1 hc1c1bar hη'Y hη'irr hee hsupp hirrAnc
  · rw [caseB_constituentDecomposition_tau1]
    exact caseB_constituentDecomposition_tau1_mem_ZIrr hyp h46 θ hcol hirr
  · exact hνZc1

/-- **Peterfalvi (6.8.2.3), the per-`φ` anchored image — concrete dispatch family.**  The
specialization of `caseB_per_phi_anchored` to the mixed dispatch family `caseB_phi_family`: the
abstract decomposition family `D`, its seam-1 orthogonality `hXorth` and integrality `hbi` are all
resolved (`caseB_phi_family` / `caseB_constituentDecomposition_X_orthogonal` /
`caseB_constituentDecomposition_Y_inner_int`, the latter's `b` read off by choice).  For each
constituent `θ = i.val` of `Ind^L_{W₂} φ` (with `aᵢ = ⟨φ, Res^H_{W₂} θ⟩ > 0`):
`(Ind^L_H θ − aᵢ·η₁)^{hyp.tau} = (caseB_phi_family … i).X − aᵢ·cY.extension η₁`.

The remaining inputs are exactly the genuine §5/§6 content discharged at the capstone: the per-`θ`
column/irreducible structural bundles `hcol`/`hirr`, the `Y`-anchor `η₁` data (`hη₁` and its real /
support / conjugate facts), the partner anchor `η' ≠ η₁ ∈ Yset`, the per-`θ` anchor-vs-constituent
orthogonality `hirrAnc`, and the (6.8.2.2) aggregate `hXaggorth`/`hdecomp` (`exists_decomposition_caseB`). -/
theorem caseB_per_phi_anchored_family
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hcol : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBColBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hirr : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBIrrBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    {η' : ClassFunction ↥L ℂ} (hη'Y : η' ∈ hyp.Yset) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hirrAnc : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
          OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
        ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0
        ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁.conj
            (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0)
    {Xagg : ClassFunction G ℂ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) - constituentWeight hφ' i.val • η₁)
      = (caseB_phi_family hyp h46 hW2H hφ' hcol hirr i).X
        - (constituentWeight hφ' i.val : ℂ) • cY.extension η₁ := by
  have hX : ∀ j, ClassFunction.inner
      (caseB_phi_family hyp h46 hW2H hφ' hcol hirr j).X (cY.extension η₁) = 0 :=
    fun j => caseB_constituentDecomposition_X_orthogonal hyp h46 hHK j.val (hcol j) (hirr j) cY
      hη₁ hη₁irr hrealc1 hdiffsuppc1 hc1barS1 hνZc1 hc1c1bar hη'Y hη'irr hee hsupp (hirrAnc j)
  have hY : ∀ j, ∃ n : ℤ, ClassFunction.inner
      (caseB_phi_family hyp h46 hW2H hφ' hcol hirr j).Y (cY.extension η₁) = (n : ℂ) :=
    fun j => caseB_constituentDecomposition_Y_inner_int hyp h46 hHK j.val (hcol j) (hirr j) cY
      hη₁ hη₁irr hrealc1 hdiffsuppc1 hc1barS1 hνZc1 hc1c1bar hη'Y hη'irr hee hsupp (hirrAnc j)
  exact caseB_per_phi_anchored hyp hW2H hcen hφ' cY hη₁
    (caseB_phi_family hyp h46 hW2H hφ' hcol hirr)
    (fun j => caseB_phi_family_tau1 hyp h46 hW2H hφ' j)
    hXaggorth hdecomp (b := fun j => (hY j).choose) hX (fun j => (hY j).choose_spec) i

/-- **Peterfalvi (6.8.2.3), the per-`φ` anchored image — `Y`-anchor data internalized.**  Strengthens
`caseB_per_phi_anchored_family` by discharging the entire `η₁`-anchor / partner block from
`η₁ ∈ Yset` alone, via the textbook choice of partner `η' = η̄₁` (the complex conjugate): `η̄₁ ∈ Y`
(`Yset_closedUnderConjugate`), `η₁ ≠ η̄₁` (`Yset_hasNoRealCharacters`, Peterfalvi (5.2.a): odd order ⇒
no nontrivial real irreducible), `⟨η₁, η̄₁⟩ = 0` (distinct irreducibles), and `η₁ − η̄₁` `H^#`-supported
(equal degree `Yset_apply_one`, `sMember_diffSupport_of_charValue_eq`).  The remaining inputs are the
genuinely hard §5/§6 content: the per-`θ` column/irreducible bundles `hcol`/`hirr`, the per-`θ`
anchor-vs-constituent orthogonality `hirrAnc`, and the (6.8.2.2) aggregate `hXaggorth`/`hdecomp`. -/
theorem caseB_per_phi_anchored_fromYset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hcol : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBColBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hirr : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBIrrBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hirrAnc : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
          OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
        ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0
        ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁.conj
            (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0)
    {Xagg : ClassFunction G ℂ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) - constituentWeight hφ' i.val • η₁)
      = (caseB_phi_family hyp h46 hW2H hφ' hcol hirr i).X
        - (constituentWeight hφ' i.val : ℂ) • cY.extension η₁ := by
  have hη₁irr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hconj : η₁.conj ∈ hyp.Yset := hyp.Yset_closedUnderConjugate hη₁
  have hrealc1 : ¬ η₁.IsReal :=
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
  exact caseB_per_phi_anchored_family hyp h46 hHK hW2H hcen hφ' cY hη₁ hcol hirr
    hη₁irr hrealc1 hdiffsuppc1 hconj
    (cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) hee
    hconj hη₁irr.conj hee hsupp hirrAnc hXaggorth hdecomp i

/-- **(6.8.2) X∪Y fold per-step: adjoin an irreducible non-real `χ` (with `χ̄`) to a coherent set.**
A thin wrapper over `retarget_isCoherent_of_supportedDecomposition` that discharges its five
orthonormality hypotheses (`⟨χ,χ⟩ = ⟨χ̄,χ̄⟩ = ⟨χ₁,χ₁⟩ = 1`, `⟨χ,χ̄⟩ = ⟨χ̄,χ⟩ = 0`) from
irreducibility of `χ`, `χ₁` and non-realness of `χ` (the irreducible Kronecker `if`).

This is the per-step of the case-(B) `X ∪ Y` coherence fold (Peterfalvi (6.8.2), `τ₂` route): the
anchor `χ₁ = η₁ ∈ 𝒴` and the supported decomposition `Da` is the per-`φ` anchored image
`caseB_phi_family … i` of an irreducible `X`-member `χ = Ind^L_H θ`.  The remaining `S₁`-dependent
inputs (prefix orthogonality `hperElem`/`hχ_S1`/`hχbar_S1`, `χ₁ ∈ S₁`, the decomposition
consistency `htau1_*`/`hY`, and generation `hgen`) are supplied by the chain fold.  (NB: lives in
this leaf as a case-(B) frontier helper; a candidate to lift to `S07_Coherence` at the
`S08_CaseBAssembly` split, issue 0070.) -/
noncomputable def adjoin_irr_nonreal_of_supportedDecomposition
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {S₁ : Set (ClassFunction ↥L ℂ)} {A : Set ↥L}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A)
    {χ chi1 : ClassFunction ↥L ℂ} {a : ℕ}
    (hχirr : IsIrreducibleCharacter χ) (hχnonreal : ¬ χ.IsReal)
    (hchi1irr : IsIrreducibleCharacter chi1)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ (a • chi1))
    (hperElem : ∀ ξ ∈ Submodule.span ℤ S₁, ∀ α ∈ Da.imageFamily.imageSet,
      ClassFunction.inner (hS₁.extension ξ) α = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (htau1_diff : Da.tau1 (χ - a • chi1) = τ (χ - a • chi1))
    (hY : Da.Y = a • Da.tau1 chi1)
    (htau1_chi1 : Da.tau1 chi1 = hS₁.extension chi1)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (S₁ ∪ {χ, χ.conj}) A ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁ A
        ∪ {χ - χ.conj, χ - a • chi1})) :
    OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {χ, χ.conj}) A := by
  have hχχ : ClassFunction.inner χ χ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ, hχirr⟩ : IrreducibleCharacter ↥L)
      (⟨χ, hχirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hχbarχbar : ClassFunction.inner χ.conj χ.conj = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hχirr.conj⟩ : IrreducibleCharacter ↥L)
      (⟨χ.conj, hχirr.conj⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hne : (⟨χ, hχirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ.conj, hχirr.conj⟩ := by
    intro heq
    apply hχnonreal
    have h2 := congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) heq
    show χ.conj = χ
    simpa using h2.symm
  have hχχbar : ClassFunction.inner χ χ.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ, hχirr⟩ : IrreducibleCharacter ↥L)
      (⟨χ.conj, hχirr.conj⟩ : IrreducibleCharacter ↥L)
    rwa [if_neg hne] at h
  have hχbarχ : ClassFunction.inner χ.conj χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχχbar, star_zero]
  have hchi1chi1 : ClassFunction.inner chi1 chi1 = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨chi1, hchi1irr⟩ : IrreducibleCharacter ↥L)
      (⟨chi1, hchi1irr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  exact OddOrder.Peterfalvi.S07.retarget_isCoherent_of_supportedDecomposition hS₁ Da rfl
    hχχ hχbarχbar hχχbar hχbarχ hchi1chi1 hperElem hχ_S1 hχbar_S1 hchi1 htau1_diff hY
    htau1_chi1 hgen

/-- **(6.8.2) X-member dichotomy: column or irreducible.**  For a non-trivial `θ : Irr ↥H`, the
induced character `Ind^L_H θ` either equals a non-trivial certain-type column `columnSum h46 χ₂`
(`χ₂ ≠ 1`) — the reducible/column branch — or is itself irreducible — the irreducible branch.

This is the cover dichotomy underlying the case-(B) `X = 𝒳(W₂)` coherence: every `X`-member splits
into the certain-type column part (coherent as a set, `certainTypeSet_isCoherent_tau_canonical`) or
the irreducible part (adjoined as a `{χ, χ̄}` pair via `adjoin_irr_nonreal_of_supportedDecomposition`).
The irreducible branch is `caseB_irr_induce_isIrreducible` (the value↔index seam, settled session 43
cont.⁹); the column branch is the witnessing `χ₂`. -/
theorem caseB_induce_column_or_irreducible
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥H}
    (hθne : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H) :
    (∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      ∨ IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  classical
  by_cases hc : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
  · exact Or.inl hc
  · exact Or.inr (caseB_irr_induce_isIrreducible h46 hHK hθne
      (fun χ₂ hχ₂ heq => hc ⟨χ₂, hχ₂, heq⟩))

/-- **(6.8.2) irreducible `X`-member ⊥ certain-type column** — the cross-orthogonality the case-(B)
`X`-coherence fold needs (an irreducible `Ind^L_H θ` adjoined onto the column base `cX_col`).

`⟨Ind^L_H θ, columnSum h46 χ₂⟩ = 0`: by additivity `columnSum = ∑_i μ_{ij}`, it suffices each grid
character `μ_{ij}` is `⊥ Ind^L_H θ`.  Both are irreducible, and distinct **by degree mod `|W₁|`**:
`Ind^L_H θ` has degree `|W₁|·θ(1) ≡ 0 (mod |W₁|)` (`induce_apply_one` + `index_H_eq_card_W1`), whereas
a grid degree is `≡ ±1 (mod |W₁|)` (`certainType_degree_modEq`, sign `= ±1`), with `|W₁| ≠ 1`.  So the
irreducible Kronecker inner product vanishes.  (This is the same degree argument as the `X ⊥ Y`
`inner_columnFamily_mu_Yset_eq_zero`, with the `Y`-degree `|W₁|` replaced by `|W₁|·θ(1)`.) -/
theorem caseB_inner_irr_columnSum_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥H}
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = 0 := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, inner_sum_right]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hne : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      ≠ ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) := by
    intro heq
    obtain ⟨a, ha⟩ := h46.certainType_degree_modEq χ₂ i
    obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hindeg : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)
        = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
      rw [ClassFunction.induce_apply_one, hd, hyp.index_H_eq_card_W1]
    rw [← heq, hindeg] at ha
    have hcard : (Nat.card h46.W1 : ℂ) = (Nat.card hyp.W1 : ℂ) := by rw [hW1]
    rw [hcard] at ha
    have hw1 : Nat.card hyp.W1 ≠ 1 := fun h => hyp.W1_nontrivial (Subgroup.card_eq_one.mp h)
    have hsign : ((h46.columnFamily χ₂).sign : ℂ)
        = (Nat.card hyp.W1 : ℂ) * ((d : ℂ) - (a : ℂ)) := by linear_combination -ha
    have hsignZ : (h46.columnFamily χ₂).sign = (Nat.card hyp.W1 : ℤ) * ((d : ℤ) - a) := by
      exact_mod_cast hsign
    have hdvd1 : (Nat.card hyp.W1 : ℤ) ∣ 1 := by
      have hdvd : (Nat.card hyp.W1 : ℤ) ∣ (h46.columnFamily χ₂).sign := ⟨(d : ℤ) - a, hsignZ⟩
      rcases (h46.columnFamily χ₂).sign_eq with hs | hs
      · rwa [hs] at hdvd
      · rw [hs] at hdvd; exact (dvd_neg).mp hdvd
    exact hw1 (Nat.dvd_one.mp (by exact_mod_cast hdvd1))
  have hkron := irreducibleCharacter_inner_eq_ite
    (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ : IrreducibleCharacter ↥L)
    ((h46.columnFamily χ₂).mu i)
  rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at hkron
  simpa using hkron

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **(6.8.2) distinct certain-type columns are orthogonal** — `⟨columnSum h46 χ₂, columnSum h46 χ₂'⟩
= 0` for `χ₂ ≠ χ₂'`.  By additivity over `columnSum = ∑_i μ_{ij}`, it reduces to the cross-column
grid orthogonality `⟨μ_{ij}, μ_{i'j'}⟩ = 0` (`columnFamily_cross_products_zero`, Peterfalvi (4.1)),
read off via the same `i, i' = 0` case split as `columnFamily_mu_ne`.

This is the cross-orthogonality between different certain-type columns the case-(B) `X`-coherence
needs to assemble the column base across degree classes (columns of distinct `W₂`-duals — in
particular distinct degrees — are mutually orthogonal). -/
theorem inner_columnSum_cross_eq_zero
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂') :
    ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂') = 0 := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnSum_def,
    inner_sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_sum_right]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have hz : (⟨1, h46.one_lt_card_W1⟩ : Fin (Nat.card h46.W1)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  rcases eq_or_ne i 0 with hi | hi <;> rcases eq_or_ne j 0 with hj | hj
  · subst hi; subst hj; exact (h46.columnFamily_cross_products_zero hne hz hz).2.2.2
  · subst hi; exact (h46.columnFamily_cross_products_zero hne hz hj).2.2.1
  · subst hj; exact (h46.columnFamily_cross_products_zero hne hi hz).2.1
  · exact (h46.columnFamily_cross_products_zero hne hi hj).1

/-- **(6.8.2) conjugate irreducible `X`-member ⊥ certain-type column** — the `χ̄`-side companion of
`caseB_inner_irr_columnSum_eq_zero`: `⟨(Ind^L_H θ)‾, columnSum h46 χ₂⟩ = 0` for irreducible
`Ind^L_H θ`.  Same degree argument: `(Ind θ)‾` has degree `|W₁|·θ(1) ≡ 0 (mod |W₁|)` (conjugation
fixes the degree, a real value), while grid degrees are `≡ ±1`, so `(Ind θ)‾` is distinct from every
`μ_{ij}` and the inner product vanishes.  This supplies the `χ̄ ⊥ S₁` (`hχbar_S1`) input when the
irreducible pair `{Ind θ, (Ind θ)‾}` is adjoined onto the column base in the case-(B) `X`-fold. -/
theorem caseB_inner_irr_conj_columnSum_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥H}
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = 0 := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, inner_sum_right]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hne : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      ≠ ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) := by
    intro heq
    obtain ⟨a, ha⟩ := h46.certainType_degree_modEq χ₂ i
    obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hindeg : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj (1 : ↥L)
        = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
      rw [ClassFunction.conj_apply, ClassFunction.induce_apply_one, hd, hyp.index_H_eq_card_W1]
      simp [mul_comm]
    rw [← heq, hindeg] at ha
    have hcard : (Nat.card h46.W1 : ℂ) = (Nat.card hyp.W1 : ℂ) := by rw [hW1]
    rw [hcard] at ha
    have hw1 : Nat.card hyp.W1 ≠ 1 := fun h => hyp.W1_nontrivial (Subgroup.card_eq_one.mp h)
    have hsign : ((h46.columnFamily χ₂).sign : ℂ)
        = (Nat.card hyp.W1 : ℂ) * ((d : ℂ) - (a : ℂ)) := by linear_combination -ha
    have hsignZ : (h46.columnFamily χ₂).sign = (Nat.card hyp.W1 : ℤ) * ((d : ℤ) - a) := by
      exact_mod_cast hsign
    have hdvd1 : (Nat.card hyp.W1 : ℤ) ∣ 1 := by
      have hdvd : (Nat.card hyp.W1 : ℤ) ∣ (h46.columnFamily χ₂).sign := ⟨(d : ℤ) - a, hsignZ⟩
      rcases (h46.columnFamily χ₂).sign_eq with hs | hs
      · rwa [hs] at hdvd
      · rw [hs] at hdvd; exact (dvd_neg).mp hdvd
    exact hw1 (Nat.dvd_one.mp (by exact_mod_cast hdvd1))
  have hkron := irreducibleCharacter_inner_eq_ite
    (⟨(ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj, hirr.conj⟩ : IrreducibleCharacter ↥L)
    ((h46.columnFamily χ₂).mu i)
  rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at hkron
  simpa using hkron

/-- **(6.8.2) irreducible `X`-member ⊥ a certain-type column base** — the `χ`/`χ̄ ⊥ S₁` inputs
(`hχ_S1`/`hχbar_S1`) of the case-(B) `X`-fold per-step, for the part of the prefix `S₁` consisting of
certain-type columns.  Given that every member of `S₀` is a non-trivial column `columnSum h46 χ₂`,
the irreducible `Ind^L_H θ` and its conjugate are orthogonal to all of `S₀`, by
`caseB_inner_irr_columnSum_eq_zero` / `caseB_inner_irr_conj_columnSum_eq_zero`.  (The prefix's
already-adjoined irreducible pairs are handled separately by the irreducible Kronecker delta.) -/
theorem caseB_irr_orthogonal_columnBase
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥H}
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    {S₀ : Set (ClassFunction ↥L ℂ)}
    (hS₀ : ∀ x ∈ S₀, ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      χ₂ ≠ 1 ∧ OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x) :
    (∀ x ∈ S₀, ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) x = 0) ∧
      (∀ x ∈ S₀,
        ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj x = 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨χ₂, -, rfl⟩ := hS₀ x hx
    exact caseB_inner_irr_columnSum_eq_zero hyp h46 hW1 hirr χ₂
  · obtain ⟨χ₂, -, rfl⟩ := hS₀ x hx
    exact caseB_inner_irr_conj_columnSum_eq_zero hyp h46 hW1 hirr χ₂

/-- **(6.8.2) `S`-member dichotomy: column or irreducible** — the `S`-level cover lifting the per-`θ`
`caseB_induce_column_or_irreducible` over `S = {Ind^L_H θ | θ ≠ 1}`.  Every member of the Sibley set
`S` is either a non-trivial certain-type column `columnSum h46 χ₂` or an irreducible character.

This is the cover used to assemble the case-(B) `X = 𝒳(W₂)`-coherence (`X ⊆ S`): every `X`-member
splits into the certain-type column part (coherent as a set) or the irreducible part (adjoined as a
`{χ, χ̄}` pair).  It also feeds the `X ⊥ Y` orthogonality `hpair` of the `X ∪ Y` glue (a column is
`⊥ Y` by `inner_columnSum_Yset_eq_zero`; an irreducible `X`-member is `⊥ Y` by degree/distinctness). -/
theorem caseB_S_member_column_or_irreducible
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {x : ClassFunction ↥L ℂ} (hx : x ∈ hyp.S) :
    (∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x)
      ∨ IsIrreducibleCharacter x := by
  rw [hyp.S_eq, Set.mem_setOf_eq] at hx
  obtain ⟨θ, hθne, rfl⟩ := hx
  have hθne' : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H := fun heq =>
    hθne (Subtype.ext (heq.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm))
  exact caseB_induce_column_or_irreducible h46 hHK hθne'

/-- **(6.8.2) `X(W₂) ⊥ Y`** — the `hpair` orthogonality input of the case-(B) `X ∪ Y` glue
(`coherentXunionYset_caseB_of_glued`).  Every `X`-member is orthogonal to every `Y`-member: by the
`S`-level cover (`caseB_S_member_column_or_irreducible`) an `X`-member is either a certain-type column
(`⊥ Y` by `inner_columnSum_Yset_eq_zero`) or an irreducible distinct from the `Y`-member (`⊥ Y` by
`inner_irr_Yset_eq_zero`); the distinctness is the disjointness `X(W₂) ∩ Y = ∅` (`Y = S(⁅H,H⁆) ⊆
S(W₂)` since `W₂ ⊆ ⁅H,H⁆`, antitone, and `X(W₂)` is disjoint from `S(W₂)`). -/
theorem caseB_Xset_orthogonal_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {W2 : Subgroup ↥L} (hW2comm : W2 ≤ ⁅H, H⁆) :
    ∀ x ∈ hyp.Xset W2, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0 := by
  have hdisj : Disjoint (hyp.Xset W2) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration W2 :=
      hyp.SsubFiltration_antitone hW2comm
    exact Set.disjoint_of_subset_right hYsub (hyp.disjoint_Xset_SsubFiltration (Z := W2))
  intro x hx y hy
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hx) with
    ⟨χ₂, -, rfl⟩ | hirr
  · exact inner_columnSum_Yset_eq_zero hyp h46 hW1 hy χ₂
  · exact inner_irr_Yset_eq_zero hyp hirr hy (fun heq => Set.disjoint_left.mp hdisj hx (heq.symm ▸ hy))

end OddOrder.Peterfalvi.S08
