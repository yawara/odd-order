import OddOrder.Peterfalvi.S16_NonExistenceG.KeyInequality

/-!
# Peterfalvi (14.10)-(14.11) — the subgroup M over N_G(V)

Split from the former monolithic `OddOrder.Peterfalvi.S16_NonExistenceG` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]


/-! ## (14.10)--(14.11): the subgroup `M` over `N_G(V)` -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.10)**: the type-I maximal subgroup `M` containing
`N_G(V)`, its Fitting kernel `K`, the Dade extension, and `beta_M`. -/
structure MHypothesis (hyp : Hypothesis (G := G)) where
  [finiteG : Finite G]
  M : Subgroup G
  K : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  normalizer_V_le_M : Subgroup.normalizer (hyp.base.V : Set G) ≤ M
  K_eq_MF : K = maxNilpotentNormalHall M
  /-- **Peterfalvi (12.1) for `M`**: the genuine type-I Dade setup of the maximal subgroup `M`
  over `N_G(V)` — its `TypeIData`, the (8.15) Dade support data for `A(M)`, and the support-kernel
  conjugation invariance.  This is the honest carrier (sorry-free constructible from `IsTypeI M`
  via `S14.exists_typeI_hypothesis`) supplying the concrete `S04.Hypothesis`/`S04.DadeMap` that
  bridge `M` to the §7 ρ-machinery (`S09.Hypothesis71`/`FamilyHypothesis71`/`family_inequality`),
  the common §3/§4 Dade foundation of the (14.11) norm-cascade producers. -/
  typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M
  /-- **Peterfalvi (7.8) for `M`**: the §7 coherence data (`S09.Hypothesis78`) of the type-I
  maximal subgroup `M` on its Dade support `A(M) = typeIA M`.  Its (7.8.a) `β`-decomposition and
  (7.8.b) norm estimates feed the (14.11) cascade producers (`betaM_expansion_data` via
  `betaMExpansionData_of_hypothesis78`; `normCascadeData` via `family_inequality`).  The genuine
  M-coherence supply (Pf §5–§8 + §13/§14), isolated here as the single honest obligation that
  `exists_MHypothesis` discharges. -/
  h78 : OddOrder.Peterfalvi.S09.Hypothesis78 G
    (OddOrder.GroupTheory.typeIA M typeIHyp.typeI) M
  Mset : Set (ClassFunction ↥M ℂ)
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  psi : ClassFunction ↥M ℂ
  e : ℕ
  k : ℕ
  /-- **Peterfalvi (14.10)**: `e = |M : K|` (the degree of `ψ`).  De-opacified from the former
  opaque `Prop` to the concrete index identity (lane-c §16 char-endpoint, carrier honesty). -/
  e_eq_index : e = (K.subgroupOf M).index
  /-- **Peterfalvi (14.11)**: `e = |M : K| = p q`.  The V-side dual of
  `LHypothesis.typeI_complement_card_eq_pq`: `M` is type I over `N_G(V)` with Frobenius complement
  `W₁ W₂^y` of order `p q` ((13.17.c)/(14.5), dual side).  Carried structurally and supplied by
  `exists_MHypothesis` (from the T/V-side `typeII_overNormalizer_frobenius`), so that the index
  half of (14.11) `K_eq_V_index_pq` is a direct consequence rather than a separate obligation. -/
  complement_card_eq_pq : e = hyp.base.p * hyp.base.q
  k_eq_card_K : k = Nat.card ↥K
  psi_mem : psi ∈ Mset
  psi_degree_eq_e : psi 1 = (e : ℂ)
  betaM : ClassFunction G ℂ
  /-- **Peterfalvi (14.10)**: `betaM` is `β_M^τ`, the image under the Dade isometry `τ` of
  `β_M = Ind_K^M 1_K − ψ`.  Still carried as an opaque `Prop` pending the induce/`Invertible`
  instance plumbing needed to spell `Ind_K^M 1_K` inside a field type (lane-c §16). -/
  betaM_formula : Prop
  betaM_formula_holds : betaM_formula
  /-- **Peterfalvi (7.8.a) for `M`**: `β_M^τ` is the Dade image `β` carried by `h78`. -/
  betaM_eq : betaM = h78.beta
  /-- **Peterfalvi (14.10)/(7.8)**: `ψ^{τ₁}` is the coherent image `ζ^ν` of the distinguished `ζ`. -/
  psi_tau1_eq : tau1 psi = h78.nu (h78.hyp76.zeta h78.zetaDistinct)
  /-- **Peterfalvi (13.1.d)/(3.9)**: the `±1` signs of the `η`-grid expansion of `1_G + Δ`. -/
  betaSigns : Fin hyp.base.q → Fin hyp.base.p → ℤ
  betaSigns_pm : ∀ i j, betaSigns i j = 1 ∨ betaSigns i j = -1
  /-- **Peterfalvi (13.1.d)**: `1_G + Δ = Σ ε_ij η_ij` ties the residual `Δ` of `h78`'s (7.8.a)
  decomposition to the §13 `η`-grid. -/
  betaGrid : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + h78.delta =
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (betaSigns i j : ℂ) • hyp.base.eta i j
  G0 : Set G
  /-- **Peterfalvi (14.10)/(7.5)**: the test character `ψ^{τ₁}` has norm one — it is the
  Dade-isometry `τ₁`-image of the unit-norm coherent `ζ`, hence admissible in the family
  inequality (7.5) `S09.family_inequality`.  V-side dual of
  `S12.Hypothesis.inner_tau1_zeta_self_eq_one`; a genuine consequence of `tau1` being an isometry
  on `ℤ[ℳ]` and `ψ ∈ ℳ` irreducible. -/
  psi_tau1_norm_one : ClassFunction.inner (tau1 psi) (tau1 psi) = 1
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: `G₀ ⊆ G − Ã(M)`.  The (14.11.3) set
  `G₀ = G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]` lies inside the family `(7.4)` support complement
  `famG₀ = (toFamilyHypothesis71).G0 = G − Ã(M)`, since every `g ∈ G₀` is off the Dade support
  `Ã(M)` of `A(M)` (`typeIHyp.dadeData.dade.dadeSupport`).  This is the inclusion `G₀ ⊆ famG₀`
  used to drop the `G₀`-part of the (7.5) sum in (14.11.4). -/
  G0_off_dadeSupport : ∀ g ∈ G0, g ∉ typeIHyp.dadeData.dade.dadeSupport
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: the complement of `G₀` is covered by the Dade support
  `Ã(M)` and the three orbits `(W − (W₁∪W₂))^G`, `(P#)^G`, `(Q#)^G`.  Concretely, `G₀` is the
  (14.11.3) set `G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`, so any `g` off `Ã(M)` and off `G₀`
  lies in the orbit union.  This is the §8 TI-counting input: `famG₀ ∖ G₀ ⊆ orbits` lets the
  `(7.5)` `G₀`-drop in line 83 (`chiRhoNormSq_psi_le_line83`) be bounded by the orbit cardinalities
  (the genuine §8 structural fact, supplied from the partner type-`P` structure). -/
  G0_orbit_cover : ∀ g : G, g ∉ typeIHyp.dadeData.dade.dadeSupport → g ∉ G0 →
    g ∈ OddOrder.GroupTheory.conjClassSet
          ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
        ∪ OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
        ∪ OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  /-- **Peterfalvi (14.11.3), avoidance half**: the generic set meets none of the three
  singular orbits — no conjugate of the regular Weyl set `W − (W₁∪W₂)`, of `P#`, or of `Q#`.
  Together with `G0_off_dadeSupport` this pins `G₀` inside Peterfalvi's (14.11.3) complement
  `G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]`; the support half of (14.11.3) — every `g ∈ G₀`
  has order prime to `pq` — follows through `orderOf_coprime_pq_of_not_mem_conj`
  (`G0_orderOf_coprime` below). -/
  G0_avoid : ∀ g ∈ G0,
    g ∉ OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
      ∧ g ∉ OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
      ∧ g ∉ OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  /-- **Peterfalvi §13 `normalizer_V` for the `W`-set**: `N_G(X) = W` for every nonempty
  `X ⊆ W − (W₁∪W₂)` (the type-`P` exceptional-set normalizer, from the partner structure).  The
  `hnorm` input to the `W`-orbit TI count (`orbit_sdiff_sup_normSq_term`). -/
  W_normalizer_V : ∀ X : Set G, X.Nonempty →
    X ⊆ (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) →
    Subgroup.normalizer X = hyp.base.W
  -- **Peterfalvi (14.11)/(14.11.3)**: `|W| = p q`, `|W₁| + |W₂| = p + q`, and the nonemptiness of
  -- `W − (W₁∪W₂)` are **base-derived** (`S15.card_W_eq_pq`, `S15.card_W1_add_W2`,
  -- `S15.W_sdiff_nonempty`), so they are no longer carried as fields — the `W = W₁ × W₂` cyclic
  -- structure is an elementary consequence of the base `Hypothesis`, not a §13-14 σ-obligation.
  /-- **Peterfalvi §8**: `P` is a TI-subgroup (distinct conjugates meet trivially). -/
  P_isTI : Subgroup.IsTI hyp.base.P
  /-- **Peterfalvi §8**: `Q` is a TI-subgroup. -/
  Q_isTI : Subgroup.IsTI hyp.base.Q
  /-- **Peterfalvi (14.11.4)**: `|N_G(P)| = |P| u q` (the Type-II partner `S = (H ⋊ U) ⋊ W₂`). -/
  card_normalizer_P_eq : Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G))
    = Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q
  /-- **Peterfalvi (14.11.4)**: `|N_G(Q)| = |Q| v p` (the `T`-side partner). -/
  card_normalizer_Q_eq : Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G))
    = Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p
  /-- **Peterfalvi (7.1)/(14.11.4) bridge compatibility.**  The underlying `(7.1)` Dade hypothesis
  of the §7 coherence datum `h78` is the type-I Dade support hypothesis of `M` carried by
  `typeIHyp` (i.e. `h78` is built over the same `(M, A(M))` Dade map that powers the family
  inequality (7.5) via `toFamilyHypothesis71`).  Since `S09.Hypothesis71.chiRho` depends only on
  the support hypothesis `H71.hyp` (the `H(a)`-family), not on the chosen Dade map `τ`, this
  identifies the `ρ`-image of `h78` (used in `zetaNuRho`, (7.8.b)) with the family member's
  `ρ`-image, so the `ρ`-norm `‖ψ^{τ₁ρ}‖²` of (14.11.4) equals `h78.zetaNuRhoNormSq`.  Holds by
  `rfl` for any `h78` built from `typeIHyp.dadeData`; carried so `exists_MHypothesis` supplies a
  compatible `h78`. -/
  h78_hyp_eq : h78.hyp76.hyp71.hyp = typeIHyp.dadeData.dade
  /-- **Peterfalvi (7.6)/(14.10).**  The normal kernel `H` of the §7 coherence datum `h78` is the
  Fitting kernel `K = M_F`.  (For type-I `M`, `A(M) = K^#` is the Dade support; the coherent family
  `T = {Ind_K^M θ}` has kernel `K`.)  Gives `h78.kernelOrder = |K| = k` and
  `h78.complementIndex = |M : K| = e = p q` for the (7.8.b) lower bound. -/
  h78_H_eq : h78.hyp76.H = K
  /-- **Peterfalvi (7.8.b) for `M`** — the coherence-norm lower bound
  `‖ζ^{νρ}‖² ≥ 1 − e/h = 1 − |M:K|/|K|`.  This is
  `S09.Hypothesis78.NormEstimates.zetaNuRho_norm_sq_ge` for the coherent type-I `M`, with the
  small-index hypothesis `smallIndex` (`2·|M:K| + 1 ≤ |K|`, i.e. `2 p q + 1 ≤ k`, a consequence of
  (14.11.1) `k > 2 p v` and `v ≥ q`) discharged.  The genuine §7 Dade content of the (14.11.4)
  lower bound, isolated here as part of the `exists_MHypothesis` obligation. -/
  h78_zetaNuRho_normSq_ge :
    1 - (h78.complementIndex : ℝ) / (h78.kernelOrder : ℝ) ≤ h78.zetaNuRhoNormSq

namespace MHypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Peterfalvi (7.4) one-member family `{(M, A(M))}` for the V-side type-I subgroup `M`** —
the §7 input bridging `M` to the family inequality (7.5) `S09.family_inequality`, the common
foundation of the (14.11) norm-cascade producers (`normCascadeData`, …).

Built genuinely from the type-I Dade setup carried by `typeIHyp` (its (8.15) Dade support
`dadeData` for `A(M) = typeIA M` and the conjugation invariance `hconj`), mirroring
`S12.Hypothesis.toFamilyHypothesis71` for type-`P` subgroups — but on the type-I support `typeIA`,
so no `A_0(M) → A(M)` restriction is needed.  The single member's (7.1) data is the restricted Dade
map of `dadeData`, the `IsDadeIsometry` certificate is `FullDadeIsometryData`'s, and
`pairwise_disjoint` is vacuous over `Fin 1`.  **Sorry-free + self-contained** from the genuine
`typeIHyp`. -/
noncomputable def toFamilyHypothesis71 [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) : OddOrder.Peterfalvi.S09.FamilyHypothesis71 G 1 where
  L := fun _ => Mdata.M
  A := fun _ => OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI
  fintypeL := fun _ => inferInstance
  invertibleL := fun _ => inferInstance
  hyp71 := fun _ =>
    { hyp := Mdata.typeIHyp.dadeData.dade
      τ := (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData Mdata.typeIHyp.hconj).toDadeMap
      isDadeMap :=
        (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData
          Mdata.typeIHyp.hconj).toDadeIsometryData.isDadeMap
      hConjInvariant := Mdata.typeIHyp.hconj }
  isDadeIsometry := fun _ =>
    (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData
      Mdata.typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
  pairwise_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

end MHypothesis

/-- The displayed rational inequality produced by the norm calculation in
**Peterfalvi (14.11.4)**, after substituting `e = p q`.  It is kept concrete so
future character-theoretic producers can target the exact arithmetic consumer
without adding another opaque proposition. -/
def normCascadeBound (hyp : Hypothesis (G := G)) (k : ℕ) : Prop :=
  (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
    ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
      2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)

/-- Pure arithmetic estimate used in **Peterfalvi (14.11.4)**.  Once the
norm calculation reduces the error terms to `2 / (p q) + 1 / (u q) + 1 / (v p)`,
the Section 16 size assumptions `u > 2q`, `v > 2p`, and `q < p` bound that error
strictly by `1 / q`. -/
theorem norm_error_terms_lt_inv_q {p q u v : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v) :
    (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
        1 / ((v * p : ℕ) : ℚ) < 1 / (q : ℚ) := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hupos_nat : 0 < u := by omega
  have hvpos_nat : 0 < v := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hupos : (0 : ℚ) < u := by exact_mod_cast hupos_nat
  have hvpos : (0 : ℚ) < v := by exact_mod_cast hvpos_nat
  have hq3q : (3 : ℚ) ≤ q := by exact_mod_cast hq3
  have hqpq : (q : ℚ) < p := by exact_mod_cast hqp
  have huq : (2 : ℚ) * q < u := by exact_mod_cast hu
  have hvp : (2 : ℚ) * p < v := by exact_mod_cast hv
  have hterm1 : (2 : ℚ) / ((p * q : ℕ) : ℚ) < 2 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    exact div_lt_div_of_pos_left (by norm_num) (mul_pos hqpos hqpos)
      (mul_lt_mul_of_pos_right hqpq hqpos)
  have hterm2 : (1 : ℚ) / ((u * q : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hden : (2 : ℚ) * q * q < u * q := by nlinarith [huq, hqpos]
    have hcore : (1 : ℚ) / (u * q) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hterm3 : (1 : ℚ) / ((v * p : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hsq : (q : ℚ) * q < p * p := by nlinarith [hqpq, hqpos, hppos]
    have hden : (2 : ℚ) * q * q < v * p := by nlinarith [hsq, hvp, hppos]
    have hcore : (1 : ℚ) / (v * p) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hsum :
      (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ) <
        2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) := by
    nlinarith [hterm1, hterm2, hterm3]
  have hsum_eq :
      2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) = 3 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    field_simp [hqpos.ne']
    ring
  have hthree_le : (3 : ℚ) / ((q * q : ℕ) : ℚ) ≤ 1 / (q : ℚ) := by
    norm_num [Nat.cast_mul]
    have hmul_nonneg : 0 ≤ (q : ℚ) * ((q : ℚ) - 3) :=
      mul_nonneg (le_of_lt hqpos) (sub_nonneg.mpr hq3q)
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  nlinarith [hsum, hsum_eq, hthree_le]

/-- **Peterfalvi (14.11.4), the upper-bound loosening step** (04.16 line 115).  The raw `(7.8.b)`
upper estimate
`1 − 1/p − 1/q + 1/(pq) + (|P|−1)/(|P|uq) + (|Q|−1)/(|Q|vp) + (k−1)/(kpq)`
is loosened to the displayed `NormCascadeData.upper`
`1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)`
via `(|P|−1)/|P| ≤ 1`, `(|Q|−1)/|Q| ≤ 1`, and `(k−1)/k ≤ 1` (so `(k−1)/(kpq) ≤ 1/(pq)`).  Pure `ℝ`
arithmetic; reusable by the `normCascadeData` producer to discharge `NormCascadeData.upper` once the
§8 TI-counting has produced the raw bound. -/
theorem normCascade_upper_loosen {p q u v k cardP cardQ : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (hk : 0 < k) (hP : 0 < cardP) (hQ : 0 < cardQ) :
    (1 : ℝ) - 1 / (p : ℝ) - 1 / (q : ℝ) + 1 / ((p * q : ℕ) : ℝ)
        + ((cardP : ℝ) - 1) / ((cardP * u * q : ℕ) : ℝ)
        + ((cardQ : ℝ) - 1) / ((cardQ * v * p : ℕ) : ℝ)
        + ((k : ℝ) - 1) / ((k * p * q : ℕ) : ℝ)
      ≤ 1 - 1 / (p : ℝ) - 1 / (q : ℝ) + 2 / ((p * q : ℕ) : ℝ)
        + 1 / ((u * q : ℕ) : ℝ) + 1 / ((v * p : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hPR : (0 : ℝ) < cardP := by exact_mod_cast hP
  have hQR : (0 : ℝ) < cardQ := by exact_mod_cast hQ
  -- `(|P|−1)/(|P|uq) ≤ 1/(uq)`.
  have h1 : ((cardP : ℝ) - 1) / ((cardP * u * q : ℕ) : ℝ) ≤ 1 / ((u * q : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hPR, huR, hqR, mul_pos huR hqR]
  -- `(|Q|−1)/(|Q|vp) ≤ 1/(vp)`.
  have h2 : ((cardQ : ℝ) - 1) / ((cardQ * v * p : ℕ) : ℝ) ≤ 1 / ((v * p : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hQR, hvR, hpR, mul_pos hvR hpR]
  -- `(k−1)/(kpq) ≤ 1/(pq)`.
  have h3 : ((k : ℝ) - 1) / ((k * p * q : ℕ) : ℝ) ≤ 1 / ((p * q : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hkR, hpR, hqR, mul_pos hpR hqR]
  -- `1/(pq) + (k−1)/(kpq) ≤ 2/(pq)`, plus the two complement bounds.
  have hpq2 : (2 : ℝ) / ((p * q : ℕ) : ℝ)
      = 1 / ((p * q : ℕ) : ℝ) + 1 / ((p * q : ℕ) : ℝ) := by ring
  linarith [h1, h2, h3, hpq2]

/-- Arithmetic endpoint for **Peterfalvi (14.11.4)**.  If the norm calculation
has already yielded the displayed bound from the text, then the lower bound
`k > 2 p v` and the cyclotomic lower consequence `p q < v` are contradictory. -/
theorem norm_cascade_contradiction {p q u v k : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v)
    (hk : 2 * p * v < k) (hvlarge : p * q < v)
    (hbound :
      (1 : ℚ) / (p : ℚ) + 1 / (q : ℚ) ≤
        ((p * q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((p * q : ℕ) : ℚ) +
          1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ)) :
    False := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hvpos_nat : 0 < v := by omega
  have hkpos_nat : 0 < k := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hkpos_nat
  have hsmall := norm_error_terms_lt_inv_q (p := p) (q := q) (u := u) (v := v)
    hq3 hqp hu hv
  have hpinv_lt : (1 : ℚ) / (p : ℚ) < ((p * q : ℕ) : ℚ) / (k : ℚ) := by
    nlinarith [hbound, hsmall]
  have hk_lt : (k : ℚ) < (p : ℚ) * (p : ℚ) * (q : ℚ) := by
    field_simp [Nat.cast_mul, hppos.ne', hqpos.ne', hkpos.ne'] at hpinv_lt
    norm_num [Nat.cast_mul] at hpinv_lt
    nlinarith [hpinv_lt]
  have hk_gt : ((2 * p * v : ℕ) : ℚ) < k := by exact_mod_cast hk
  have hvlargeq : ((p * q : ℕ) : ℚ) < v := by exact_mod_cast hvlarge
  norm_num [Nat.cast_mul] at hk_gt hvlargeq
  nlinarith [hk_lt, hk_gt, hvlargeq, hppos]

/-- **Peterfalvi (14.11.4)** arithmetic consumer with the T-side case-(9.7.b)
data already materialized.  The T-side data supplies both `p q < v` and
`2 p < v`, so the remaining inputs are exactly the S-side lower bound on `u`,
the `k > 2 p v` lower bound, and the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_T_caseB {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (hu : 2 * hyp.base.q < hyp.base.u) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction hyp.base.three_le_q hyp.q_lt_p hu
    Tdata.two_p_lt_v hk Tdata.pq_lt_v hbound

/-- **Peterfalvi (14.11.4)** arithmetic consumer with both case-(9.7.b) data
packages materialized.  The S-side data supplies `2 q < u`; the T-side data
supplies `2 p < v` and `p q < v`. -/
theorem norm_cascade_contradiction_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction_of_T_caseB Tdata Sdata.two_q_lt_u hk hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T` and `caseB_for_S`.  It leaves only the lower bound on `k` and the
concrete displayed norm inequality as inputs. -/
theorem norm_cascade_contradiction_of_caseB_outputs {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k) (hbound : normCascadeBound hyp k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hk hbound

/-- **Peterfalvi (14.11.4)** consumer after the first numerical output of
`main_size_bounds` has supplied `k > 2 p v`.  The remaining non-arithmetic work
is precisely to produce the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_main_size_bound {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v)
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hsize hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact three-part numerical output
of **Peterfalvi (14.11.1)**.  Only the first component, `k > 2 p v`, is needed
by the norm-cascade contradiction; the remaining components stay available to
match the theorem output without weakening its shape. -/
theorem norm_cascade_contradiction_of_caseB_data_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_main_size_bound Tdata Sdata Mdata hsize.1 hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T`, `caseB_for_S`, and `main_size_bounds`. -/
theorem norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data_main_size_bounds Tdata Sdata Mdata
    hsize hbound

/-- **Fixed-point-free congruence** (the mod-`p` analogue of the `U⋊W₁` Frobenius congruence,
group-theoretic core).  If a subgroup `A` of prime order `p` normalizes a finite group `U` and
acts on it fixed-point-freely by conjugation, then `|U| ≡ 1 (mod p)`.  The conjugation action of
the `p`-group `A` on `U` has `{1}` as its only fixed point, so the `p`-group fixed-point
congruence `Nat.card U ≡ Nat.card (fixedPoints) (mod p)` gives `|U| ≡ 1 (mod p)`. -/
theorem card_modEq_one_of_prime_normalizing_fpf {G : Type*} [Group G] [Finite G]
    {U A : Subgroup G} {p : ℕ} (hp : p.Prime) (hA_card : Nat.card ↥A = p)
    (hA_norm : A ≤ Subgroup.normalizer (U : Set G))
    (hfpf : ∀ a ∈ A, a ≠ 1 → ∀ u ∈ U, u ≠ 1 → (a : G) * u * (a : G)⁻¹ ≠ u) :
    Nat.card ↥U ≡ 1 [MOD p] := by
  letI : MulAction ↥A ↥U := MulAction.compHom ↥U (Subgroup.inclusion hA_norm)
  have hpg : IsPGroup p ↥A := IsPGroup.of_card (by rw [hA_card, pow_one])
  -- the conjugation `smul` is `a • u = a u a⁻¹`
  have hsmul : ∀ (a : ↥A) (u : ↥U), ((a • u : ↥U) : G) = (a : G) * (u : G) * (a : G)⁻¹ := by
    intro a u; rfl
  -- the only fixed point is `1`
  haveI : Nontrivial ↥A :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hA_card]; exact hp.one_lt)
  obtain ⟨a0, ha0⟩ := exists_ne (1 : ↥A)
  have ha0G : (a0 : G) ≠ 1 := fun h => ha0 (Subtype.ext h)
  have hfix_eq : MulAction.fixedPoints ↥A ↥U = {(1 : ↥U)} := by
    ext u
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hu
      by_contra hune
      have huG : (u : G) ≠ 1 := fun h => hune (Subtype.ext h)
      have hfixa : ((a0 • u : ↥U) : G) = (u : G) :=
        congrArg (Subtype.val) (hu a0)
      rw [hsmul] at hfixa
      exact hfpf (a0 : G) a0.2 ha0G (u : G) u.2 huG hfixa
    · rintro rfl
      intro a
      apply Subtype.ext
      rw [hsmul]
      simp
  have hfix_card : Nat.card (MulAction.fixedPoints ↥A ↥U) = 1 := by
    rw [hfix_eq]
    haveI := Set.uniqueSingleton (1 : ↥U)
    exact Nat.card_unique
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcong := hpg.card_modEq_card_fixedPoints (α := ↥U)
  rwa [hfix_card] at hcong

/-- **A Frobenius complement acts fixed-point-freely on its kernel** (ambient-group form).
If `↥L` is a Frobenius group with kernel `H.subgroupOf L` and complement `compl`, and `H ≤ L`,
then every `a ≠ 1` lying — as a `G`-element — in the complement image `compl.map L.subtype`
conjugates no nontrivial `u ∈ H` to itself: `a * u * a⁻¹ ≠ u`.  This transports
`IsFrobeniusGroup.conj_frobenius` from `↥L` down to `G` through `L.subtype`. -/
theorem isFrobeniusGroup_conj_ne_of_mem_map_complement
    {L H : Subgroup G} {compl : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (H.subgroupOf L) compl)
    (hHL : H ≤ L) {a : G} (ha_mem : a ∈ compl.map L.subtype) (ha_ne : a ≠ 1)
    {u : G} (hu_mem : u ∈ H) (hu_ne : u ≠ 1) :
    a * u * a⁻¹ ≠ u := by
  obtain ⟨a', ha'_compl, ha'_eq⟩ := Subgroup.mem_map.mp ha_mem
  have ha'_ne : a' ≠ 1 := by
    intro h
    rw [h] at ha'_eq
    exact ha_ne (by simpa using ha'_eq.symm)
  have hmemL : u ∈ L := hHL hu_mem
  have hu'_ker : (⟨u, hmemL⟩ : ↥L) ∈ H.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]; exact hu_mem
  have hu'_ne : (⟨u, hmemL⟩ : ↥L) ≠ 1 := fun h => hu_ne (congrArg Subtype.val h)
  have hconj := hfrob.conj_frobenius a' ha'_compl ha'_ne ⟨u, hmemL⟩ hu'_ker hu'_ne
  intro hcontra
  apply hconj
  apply Subtype.coe_injective
  show ((a' * ⟨u, hmemL⟩ * a'⁻¹ : ↥L) : G) = ((⟨u, hmemL⟩ : ↥L) : G)
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, InvMemClass.coe_inv,
    show ((a' : G)) = a from ha'_eq]
  exact hcontra

/-- If `x ≡ 1 (mod p)` with `p` odd and `≥ 2`, `x` odd and `x ≠ 1`, then `x ≥ 2p + 1`.  This is the
elided "fixed-point-free congruence + oddness" step of Peterfalvi (14.11.1): `x ≡ 1 (mod p)` and
`x ≠ 1` give `x = pm + 1` with `m ≥ 1`, and `x` odd with `p` odd forces `m` even, hence `m ≥ 2`. -/
private theorem two_mul_add_one_le_of_modEq_one_odd {p x : ℕ} (hp : Odd p) (hp2 : 2 ≤ p)
    (hmod : x ≡ 1 [MOD p]) (hodd : Odd x) (hne : x ≠ 1) : 2 * p + 1 ≤ x := by
  have hxmod : x % p = 1 := by
    have h := hmod
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (by omega : 1 < p)] at h
  have hdm := Nat.div_add_mod x p
  set m := x / p with hm_def
  rw [hxmod] at hdm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at hdm; omega
    · exact h1
  have hpm_even : Even (p * m) := by
    rcases hodd with ⟨t, ht⟩; exact ⟨t, by omega⟩
  have hm_even : Even m := by
    by_contra hodd_m
    rw [Nat.not_even_iff_odd] at hodd_m
    exact (Nat.not_odd_iff_even.mpr hpm_even) (Nat.odd_mul.mpr ⟨hp, hodd_m⟩)
  have hm2 : 2 ≤ m := by rcases hm_even with ⟨r, hr⟩; omega
  have hpm : 2 * p ≤ p * m := by
    calc 2 * p = p * 2 := by ring
      _ ≤ p * m := by gcongr
  omega

/-- **Peterfalvi (14.11.1)** structural half: under `K ≠ V`, the Fitting kernel `K = M_F` is large
(`k > 2 p v`) and the Frobenius quotient `(k − 1) / e` dominates `(v − 1) / p`.  The **quotient
bound is now a genuine consequence** of `k > 2 p v` (with `e = pq`, `q < p`): `q(v−1) ≤ qv ≤ 2pv ≤
k−1`, so `(v−1)/p ≤ (k−1)/(pq)` (`div_le_div_iff₀` + `nlinarith`).  The `k > 2 p v` bound is in turn
the arithmetic consequence (`two_mul_add_one_le_of_modEq_one_odd`) of the §13/§15 structural datum
`hstruct` of (14.11.1): by (13.17) the kernel order factors as `k = v·x` with `x` an integer, `x ≠ 1`
(as `K ≠ V`), and `x ≡ 1 (mod p)` (since `W₂` acts fixed-point-freely on `K` and `V`); as `k = |K|`
is odd, `x` is odd, so `x ≥ 2p+1` and `k = vx > 2pv`.  The third inequality of (14.11.1),
`(v − 1) / p > (u − 1) / q`, is `key_ratio_inequality_of_caseB_data` (14.8), discharged in
`main_size_bounds`. -/
theorem main_size_bounds_structural [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) := by
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  -- (14.11.1): `k = v·x`, `x ≡ 1 (mod p)` (`W₂` fixed-point-free on `K`, `V`), `x ≠ 1` (`K ≠ V`) —
  -- the §13/§15 structural datum (13.17); `k > 2 p v` is then arithmetic (`x` odd, so `x ≥ 2p+1`).
  have hstruct : ∃ x : ℕ, Mdata.k = hyp.base.v * x ∧ x ≡ 1 [MOD hyp.base.p] ∧ x ≠ 1 := by
    have hMI : IsTypeI Mdata.M := ⟨Mdata.typeIHyp.typeI⟩
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hyp
    -- **(13.17)/(14.11.1)**: `V ≤ K = M_F` (type-I-over-`N_G(V)` Fitting inclusion).
    have hVK : hyp.base.V ≤ Mdata.K := by
      rw [Mdata.K_eq_MF]
      exact OddOrder.Peterfalvi.S15.typeI_overNormalizer_V_le_fitting _hG hyp.base hTII
        Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    -- `|V| = v` (`d = 1` from `D = V ⊓ C_G(Q) = ⊥`, (13.12) dual).
    have hVcard : Nat.card ↥hyp.base.V = hyp.base.v := by
      have hDbot : hyp.base.D = ⊥ := by
        rw [hyp.base.D_eq]
        exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot _hG hyp.base hTII
      have hd1 : hyp.base.d = 1 := by rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
      rw [hyp.base.card_V_eq_vd, hd1, mul_one]
    -- `v ∣ k` from `V ≤ K`; set `x = k / v`.
    have hvdvdk : hyp.base.v ∣ Mdata.k := by
      rw [Mdata.k_eq_card_K, ← hVcard]
      exact Subgroup.card_dvd_of_le hVK
    obtain ⟨x, hkx⟩ := hvdvdk
    -- **(13.17)**: type-I Frobenius data with `W₂ ≤ complement`, so `W₂` acts fpf on `K = M_F`.
    obtain ⟨frob, _hker, hW2E⟩ := OddOrder.Peterfalvi.S15.exists_typeIFrobeniusData_W2_le
      _hG hyp.base Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    have hKeq : Mdata.K = frob.typeI.typeF.H := by rw [Mdata.K_eq_MF, frob.typeI.typeF.H_eq]
    have hW2card : Nat.card ↥hyp.base.W2 = hyp.base.p := hyp.base.p_eq_card_W2.symm
    have hW2M : hyp.base.W2 ≤ Mdata.M := by
      intro a ha
      obtain ⟨x', _, hx'⟩ := Subgroup.mem_map.mp (hW2E ha)
      rw [← hx']; exact x'.2
    have hW2normK : hyp.base.W2 ≤ Subgroup.normalizer (Mdata.K : Set G) := by
      refine hW2M.trans ?_
      rw [Mdata.K_eq_MF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer Mdata.M
    -- `W₂` acts fixed-point-freely on `K` (Frobenius complement on the kernel).
    have hfpfK : ∀ a ∈ hyp.base.W2, a ≠ 1 → ∀ u ∈ Mdata.K, u ≠ 1 → a * u * a⁻¹ ≠ u := by
      intro a ha ha_ne u hu hu_ne
      refine isFrobeniusGroup_conj_ne_of_mem_map_complement frob.frobenius
        frob.typeI.typeF.H_le (hW2E ha) ha_ne ?_ hu_ne
      rw [← hKeq]; exact hu
    -- `k ≡ 1 (mod p)` and `v ≡ 1 (mod p)` (`W₂` fpf on `K` and on `V ≤ K`).
    have hkmod : Mdata.k ≡ 1 [MOD hyp.base.p] := by
      rw [Mdata.k_eq_card_K]
      exact card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2card hW2normK hfpfK
    have hvmod : hyp.base.v ≡ 1 [MOD hyp.base.p] := by
      rw [← hVcard]
      refine card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2card
        hyp.base.W2_normalizes_V ?_
      intro a ha ha_ne u hu hu_ne
      exact hfpfK a ha ha_ne u (hVK hu) hu_ne
    refine ⟨x, hkx, ?_, ?_⟩
    · -- `x ≡ 1 (mod p)`: from `v x = k ≡ 1` and `v ≡ 1`.
      have hvx1 : hyp.base.v * x ≡ 1 [MOD hyp.base.p] := hkx ▸ hkmod
      have hvxx : hyp.base.v * x ≡ x [MOD hyp.base.p] := by simpa using hvmod.mul_right x
      exact hvxx.symm.trans hvx1
    · -- `x ≠ 1`: if `x = 1` then `k = v`, so `|K| = |V|` with `V ≤ K`, forcing `V = K` (⊥ `K ≠ V`).
      intro hx1
      have hkv : Mdata.k = hyp.base.v := by rw [hkx, hx1, Nat.mul_one]
      have hKcardV : Nat.card ↥Mdata.K = Nat.card ↥hyp.base.V := by
        rw [← Mdata.k_eq_card_K, hkv, hVcard]
      exact hne (Subgroup.eq_of_le_of_card_ge hVK (le_of_eq hKcardV)).symm
  have hk : Mdata.k > 2 * hyp.base.p * hyp.base.v := by
    obtain ⟨x, hkx, hxmod, hxne⟩ := hstruct
    have hk_odd : Odd Mdata.k := by
      rw [Mdata.k_eq_card_K]
      exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Mdata.K)
    have hvx_odd : Odd (hyp.base.v * x) := hkx ▸ hk_odd
    have hx_odd : Odd x := (Nat.odd_mul.mp hvx_odd).2
    have hv_pos : 0 < hyp.base.v := by rcases (Nat.odd_mul.mp hvx_odd).1 with ⟨r, hr⟩; omega
    have hx_ge : 2 * hyp.base.p + 1 ≤ x :=
      two_mul_add_one_le_of_modEq_one_odd hyp.base.p_odd hyp.base.p_prime.two_le hxmod hx_odd hxne
    have hle : hyp.base.v * (2 * hyp.base.p + 1) ≤ hyp.base.v * x := by gcongr
    have hexpand : hyp.base.v * (2 * hyp.base.p + 1)
        = 2 * hyp.base.p * hyp.base.v + hyp.base.v := by ring
    rw [hkx]; omega
  refine ⟨hk, ?_⟩
  -- The quotient bound `(k−1)/e ≥ (v−1)/p` is pure arithmetic from `k > 2pv`, `q < p`, `e = pq`:
  -- `q(v−1) ≤ qv ≤ 2pv ≤ k−1`, so `(v−1)/p ≤ (k−1)/(pq)`.
  have he : Mdata.e = hyp.base.p * hyp.base.q := Mdata.complement_card_eq_pq
  have hNat : hyp.base.q * (hyp.base.v - 1) ≤ Mdata.k - 1 := by
    have hb : 2 * hyp.base.p * hyp.base.v ≤ Mdata.k - 1 := Nat.le_sub_one_of_lt hk
    have ha : hyp.base.q * (hyp.base.v - 1) ≤ 2 * hyp.base.p * hyp.base.v := by
      calc hyp.base.q * (hyp.base.v - 1) ≤ hyp.base.q * hyp.base.v := by gcongr; omega
        _ ≤ 2 * hyp.base.p * hyp.base.v := by gcongr; omega
    exact le_trans ha hb
  rw [he, ge_iff_le]
  have hppos : (0 : ℚ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have hqpos : (0 : ℚ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hpqpos : (0 : ℚ) < ((hyp.base.p * hyp.base.q : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  rw [div_le_div_iff₀ hppos hpqpos]
  have hNatQ : (hyp.base.q : ℚ) * ((hyp.base.v - 1 : ℕ) : ℚ) ≤ ((Mdata.k - 1 : ℕ) : ℚ) := by
    exact_mod_cast hNat
  push_cast
  nlinarith [hNatQ, hppos, hqpos]

/-- **Peterfalvi (14.11.1)**: if `K != V`, then `k` is large and the quotient
bound dominates `(v - 1) / p`.

The third conjunct `(v − 1) / p > (u − 1) / q` is now a genuine proof: it is the arithmetic
ratio comparison `key_ratio_inequality_of_caseB_data` (14.8), fed by the (14.4)/(14.6) case-(9.7.b)
cyclotomic data.  The two structural bounds remain the named §13/§14 obligation
`main_size_bounds_structural`. -/
theorem main_size_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  obtain ⟨Tdata, _⟩ := caseB_for_T _hG hyp
  obtain ⟨Sdata, _⟩ := caseB_for_S _hG hyp Ldata
  obtain ⟨hk, hke⟩ := main_size_bounds_structural _hG hyp Mdata hne
  exact ⟨hk, hke, key_ratio_inequality_of_caseB_data Tdata Sdata⟩

/-- **Arithmetic core of Peterfalvi (14.11.2)**: an integer grid of *odd* Dade-isometry
coefficients whose squares sum to at most `e − 1`, with `e ≤ |grid| + 1`, forces `e = |grid| + 1`
and every coefficient `= ±1`.

The Dade parities (13.19.c / 7.8 / 3.7) make each pairing coefficient `a_ij = ⟨β_M^τ, η_ij⟩` an
*odd* integer, so `a_ij² ≥ 1`; the isometry norm bound gives `∑ a_ij² ≤ e − 1`; and `e ≤ pq`
(here `|grid| = pq − 1`, the non-principal η's, so `e ≤ |grid| + 1`).  Sandwiching
`|grid| ≤ ∑ a_ij² ≤ e − 1 ≤ |grid|` collapses every inequality: `e = pq` and each `a_ij² = 1`,
i.e. `a_ij = ±1`.  Stated generically over a `Fintype` (`|grid| = Fintype.card ι`); the η-grid
specialization indexes by the non-principal characters. -/
theorem all_pm_one_and_card_of_odd_sq_sum_le {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (e : ℕ)
    (hodd : ∀ i, Odd (a i))
    (hsq : ∑ i, (a i) ^ 2 ≤ (e : ℤ) - 1)
    (he : (e : ℤ) ≤ (Fintype.card ι : ℤ) + 1) :
    (e : ℤ) = (Fintype.card ι : ℤ) + 1 ∧ ∀ i, a i = 1 ∨ a i = -1 := by
  -- Each `a_i² ≥ 1` (odd ⟹ nonzero).
  have hge1 : ∀ i, (1 : ℤ) ≤ (a i) ^ 2 := by
    intro i
    have h0 : a i ≠ 0 := by rcases hodd i with ⟨m, hm⟩; omega
    nlinarith [Int.one_le_abs h0, sq_abs (a i)]
  -- `card ≤ ∑ a_i²`, so the sandwich `card ≤ ∑ a_i² ≤ e − 1 ≤ card` pins everything.
  have hsum_ge : (Fintype.card ι : ℤ) ≤ ∑ i, (a i) ^ 2 := by
    calc (Fintype.card ι : ℤ) = ∑ _i : ι, (1 : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ ∑ i, (a i) ^ 2 := Finset.sum_le_sum (fun i _ => hge1 i)
  refine ⟨by omega, ?_⟩
  have hsum_eq : ∑ i, (a i) ^ 2 = (Fintype.card ι : ℤ) := by omega
  -- `∑ (a_i² − 1) = 0` with each summand `≥ 0` ⟹ each `a_i² = 1` ⟹ `a_i = ±1`.
  have heach : ∀ i, (a i) ^ 2 = 1 := by
    have hz : ∑ i, ((a i) ^ 2 - 1) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hsum_eq]; ring
    have hnn : ∀ i ∈ (Finset.univ : Finset ι), (0 : ℤ) ≤ (a i) ^ 2 - 1 :=
      fun i _ => by linarith [hge1 i]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
    intro i; have := hall i (Finset.mem_univ i); linarith
  intro i
  have hfac : (a i - 1) * (a i + 1) = 0 := by nlinarith [heach i]
  rcases mul_eq_zero.mp hfac with h | h
  · left; linarith
  · right; linarith

/-- **Faithful §7/§3 Dade carrier for the `β_M` expansion of Peterfalvi (14.11.2).**

This is the `M`-instance of the (7.8) Dade-coherence decomposition specialised to the `η`-grid,
isolating the genuine character-theoretic content of (14.11.2) away from the pure algebra:

* `betaM_seven_eight` — **Peterfalvi (7.8.a)** for `M`: `β_M^τ = 1_G − χ + Δ`, the Dade-isometry
  image of `β_M = Ind_K^M 1_K − ψ` decomposed against the principal character `1_G` and the removed
  unit-norm coherent image `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`, recorded only through the
  branch-independent `chi_norm`).  In the `χ = ψ^{τ₁} = ζ^ν` branch this is exactly the `M`-instance
  of `S09.Hypothesis78.beta_eq_constOne_sub_zetaImage_add_delta` (`β = 1_G − ζ^ν + Δ`); see the
  bridge lemma `betaMExpansionData_of_hypothesis78` below.
* `grid_eq` — **Peterfalvi (13.1.d)/(7.8.b)** `η`-grid identification: `1_G + Δ = Σ_{ij} ε_ij η_ij`.
  The principal `η₀₀` carries the `1_G`, the off-principal grid realizes the residual `Δ`, and the
  `±1` signs come from the Dade congruence `a_ij ≡ 1 (mod 2)` (13.19.c / 7.8.c) with
  `Σ a_ij² ≤ e − 1` and `e = p q` (`all_pm_one_and_card_of_odd_sq_sum_le`).

All fields are genuine facts about the type-I maximal subgroup `M` (its Dade isometry and coherent
extension exist by the §3/§4/§5 machinery); their concrete construction is the remaining §3/§4
Dade-isometry obligation.  Cf. `EtaGenericData` for the dual generic-set carrier. -/
structure BetaMExpansionData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- The residual `Δ` of the (7.8.a) Dade expansion `β_M = 1_G − χ + Δ`. -/
  delta : ClassFunction G ℂ
  /-- The removed unit-norm character `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`). -/
  chi : ClassFunction G ℂ
  /-- `χ` has the same pointwise absolute value as `ψ^{τ₁}` (holds for both branches, since
  `|z| = |z̄|`) — exactly what (14.11.3) consumes. -/
  chi_norm : ∀ g : G, ‖chi g‖ = ‖(Mdata.tau1 Mdata.psi) g‖
  /-- **Peterfalvi (7.8.a)** for `M`: `β_M^τ = 1_G − χ + Δ`. -/
  betaM_seven_eight :
    Mdata.betaM = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G - chi + delta
  /-- The `±1` signs of the `η`-grid expansion. -/
  signs : Fin hyp.base.q → Fin hyp.base.p → ℤ
  signs_pm_one : ∀ i j, signs i j = 1 ∨ signs i j = -1
  /-- **Peterfalvi (13.1.d)/(7.8.b)** `η`-grid identification: `1_G + Δ = Σ_{ij} ε_ij η_ij`. -/
  grid_eq :
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + delta =
      ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §3/§7 Dade producer for (14.11.2).**  Under `K ≠ V`, the type-I maximal subgroup `M`
carries the (7.8) Dade-coherence decomposition `BetaMExpansionData` of `β_M^τ` against the `η`-grid.
The construction is the §3/§4 Dade-isometry layer (the abstract §16 `τ`/`τ₁`/`betaM` carriers do not
yet pin it); see the bridge lemma `betaMExpansionData_of_hypothesis78`, which reduces this to a
concrete `S09.Hypothesis78` for `M` plus the `η`-grid identification (3.9)/(13.1.d). -/
noncomputable def betaM_expansion_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) (_hne : Mdata.K ≠ hyp.base.V) :
    BetaMExpansionData hyp Mdata where
  delta := Mdata.h78.delta
  chi := Mdata.tau1 Mdata.psi
  chi_norm := fun _ => rfl
  betaM_seven_eight := by
    rw [Mdata.betaM_eq, Mdata.h78.beta_eq_constOne_sub_zetaImage_add_delta, Mdata.psi_tau1_eq]
  signs := Mdata.betaSigns
  signs_pm_one := Mdata.betaSigns_pm
  grid_eq := Mdata.betaGrid

/-- **§16 → §7 bridge for the `β_M` (7.8.a) decomposition.**  Given a concrete `S09.Hypothesis78`
for `M` whose Dade image `β` and coherent image `ζ^ν` are identified with the abstract §16 carriers
`β_M` and `ψ^{τ₁}`, the (7.8.a) field of `BetaMExpansionData` is exactly the `M`-instance of
`S09.Hypothesis78.beta_eq_constOne_sub_zetaImage_add_delta` (`β = 1_G − ζ^ν + Δ`).

This reduces the `betaM_expansion_data` obligation to (i) `M` instantiating `S09.Hypothesis78` with
`β_M = β` and `ψ^{τ₁} = ζ^ν`, and (ii) the `η`-grid identification `1_G + Δ = Σ ε_ij η_ij`
(3.9)/(13.1.d) — the genuine §3/§4 Dade content — and certifies that the (7.8.a) rearrangement is a
real S09 consequence, not an independent assumption.  The `χ = ζ^ν = ψ^{τ₁}` branch; `chi_norm` is
then `rfl`.  Axiom-clean. -/
noncomputable def betaMExpansionData_of_hypothesis78 [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    {A : Set G} [Fintype G] [Fintype ↥Mdata.M]
    [Invertible (Nat.card ↥Mdata.M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A Mdata.M)
    (hbeta : Mdata.betaM = H78.beta)
    (hchi : Mdata.tau1 Mdata.psi = H78.nu (H78.hyp76.zeta H78.zetaDistinct))
    (signs : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hsigns : ∀ i j, signs i j = 1 ∨ signs i j = -1)
    (hgrid : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + H78.delta =
      ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j) :
    BetaMExpansionData hyp Mdata where
  delta := H78.delta
  chi := Mdata.tau1 Mdata.psi
  chi_norm := fun _ => rfl
  betaM_seven_eight := by
    rw [hbeta, H78.beta_eq_constOne_sub_zetaImage_add_delta, hchi]
  signs := signs
  signs_pm_one := hsigns
  grid_eq := hgrid

/-- **Peterfalvi (14.11.2)**: under `K ≠ V`, `e = p q` and `β_M^τ` is a signed sum of the
`η_ij` grid with one unit-norm character `χ` removed:
`β_M^τ = Σ_{0≤i<q, 0≤j<p} (±η_ij) − χ`, where `χ = ψ^{τ₁}` or `−ψ̄^{τ₁}`.

De-opacified (W4 §16→§7 bridge, lane-h): the `e = p q` half is the structural field
`MHypothesis.complement_card_eq_pq` (Pf (14.11)), and the `η`-grid expansion is the pure-algebra
rearrangement of the faithful `BetaMExpansionData` (7.8.a) decomposition `β_M = 1_G − χ + Δ`
together with the `η`-grid identification `1_G + Δ = Σ ε_ij η_ij`.  The genuine character theory
(the (7.8) Dade decomposition for `M`) is confined to `betaM_expansion_data`. -/
theorem betaM_expansion [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.e = hyp.base.p * hyp.base.q ∧
      ∃ ε : Fin hyp.base.q → Fin hyp.base.p → ℤ,
        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        ∃ χ : ClassFunction G ℂ,
          (∀ g : G, ‖χ g‖ = ‖(Mdata.tau1 Mdata.psi) g‖) ∧
          Mdata.betaM =
            (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (ε i j : ℂ) • hyp.base.eta i j) - χ := by
  refine ⟨Mdata.complement_card_eq_pq, ?_⟩
  obtain ⟨delta, chi, hchi_norm, hbeta, signs, hsigns, hgrid⟩ :=
    betaM_expansion_data _hG hyp Mdata hne
  refine ⟨signs, hsigns, chi, hchi_norm, ?_⟩
  rw [hbeta, ← hgrid]
  abel

/-- **Parity core of Peterfalvi (3.9)/(14.11.3)**: a `±1`-signed sum of an integer-valued grid
that pairs under a conjugation involution has complex norm `≥ 1`.

Concretely, let `n : ι → ℤ` be constant on the orbits of an involution `ρ` whose *unique* fixed
point `i₀` carries the principal value `n i₀ = 1`, and let `ε : ι → ℤ` take values in `{±1}`.  Then
the signed sum `∑ ε_i n_i` is an **odd** integer — the `ρ`-paired off-principal terms contribute an
even total (`n` is `ρ`-invariant, so each pair sums to `2 n_i`), while the fixed point contributes
`±1` — so its image in `ℂ` has norm `≥ 1`.

This is the arithmetic heart of (14.11.3): on a generic element `g`, the η-grid values `η_ij(g)`
are rational integers (3.9.c) that pair under the conjugation `(i,j) ↦ (−i,−j)` with the single
principal value `η₀₀(g) = 1` (3.9.a); combined with the (14.11.2) expansion
`ψ^{τ₁}(g) = ±∑ ε_ij η_ij(g)` (valid on `G_0`, where `β_M^τ(g) = 0`) this forces
`|ψ^{τ₁}(g)| ≥ 1`.  Stated generically over a `Fintype` so it serves both the (14.11.3) bound and
the dual (14.16) parity contradiction. -/
theorem one_le_norm_signed_paired_sum {ι : Type*} [Fintype ι]
    (n ε : ι → ℤ) (ρ : Equiv.Perm ι) (i₀ : ι)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hρ : Function.Involutive ρ)
    (hfix : ∀ i, ρ i = i ↔ i = i₀)
    (hpair : ∀ i, n (ρ i) = n i)
    (hn0 : n i₀ = 1) :
    1 ≤ ‖(∑ i, (ε i : ℂ) * (n i : ℂ))‖ := by
  classical
  have hcast : (∑ i, (ε i : ℂ) * (n i : ℂ)) = ((∑ i, ε i * n i : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_intCast]
  -- Off-principal terms sum to an even integer (fixed-point-free involution on `univ ∖ {i₀}`).
  have heven_erase : (2 : ℤ) ∣ ∑ i ∈ Finset.univ.erase i₀, n i := by
    have hz : ((∑ i ∈ Finset.univ.erase i₀, n i : ℤ) : ZMod 2) = 0 := by
      push_cast
      refine Finset.sum_involution (fun a _ => ρ a) ?_ ?_ ?_ ?_
      · intro a _
        rw [hpair a]; exact CharTwo.add_self_eq_zero _
      · intro a ha _ hcontra
        exact (Finset.mem_erase.mp ha).1 ((hfix a).mp hcontra)
      · intro a ha
        rw [Finset.mem_erase] at ha ⊢
        refine ⟨fun hcontra => ha.1 ?_, Finset.mem_univ _⟩
        change ρ a = i₀ at hcontra
        calc a = ρ (ρ a) := (hρ a).symm
          _ = ρ i₀ := by rw [hcontra]
          _ = i₀ := (hfix i₀).mpr rfl
      · intro a _; exact hρ a
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  -- Each sign satisfies `ε_i ≡ 1 (mod 2)`, so `∑ ε_i n_i ≡ ∑ n_i (mod 2)`.
  have hdiff : (2 : ℤ) ∣ (∑ i, ε i * n i) - (∑ i, n i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum (fun i _ => ?_)
    have hrw : ε i * n i - n i = (ε i - 1) * n i := by ring
    rw [hrw]
    exact Dvd.dvd.mul_right (by rcases hε i with h | h <;> rw [h] <;> norm_num) (n i)
  have hsum_n : ∑ i, n i = (∑ i ∈ Finset.univ.erase i₀, n i) + n i₀ :=
    (Finset.sum_erase_add Finset.univ n (Finset.mem_univ i₀)).symm
  have hodd_n : Odd (∑ i, n i) := by
    rw [hsum_n, hn0]
    rcases heven_erase with ⟨c, hc⟩
    exact ⟨c, by rw [hc]⟩
  have hodd : Odd (∑ i, ε i * n i) := by
    rcases hdiff with ⟨d, hd⟩
    rcases hodd_n with ⟨m, hm⟩
    refine ⟨d + m, ?_⟩
    have hA : ∑ i, ε i * n i = (∑ i, n i) + 2 * d := by omega
    rw [hA, hm]; ring
  rcases hodd with ⟨m, hm⟩
  rw [hm, ← Int.cast_abs]
  have hh : (1 : ℤ) ≤ |2 * m + 1| := by
    rcases abs_cases (2 * m + 1 : ℤ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
  exact_mod_cast hh

/-- Negation `i ↦ -i ≡ (n − i) (mod n)` on `Fin n`, for `0 < n`.  This is the index map
realizing the conjugation pairing `(i,j) ↦ (−i,−j)` of the Dade `η`-grid in (3.9.a)/(14.11.3). -/
def finNeg {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩

@[simp] theorem finNeg_val {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (finNeg hn i).val = (n - i.val) % n := rfl

theorem finNeg_involutive {n : ℕ} (hn : 0 < n) : Function.Involutive (finNeg hn) := by
  intro i
  apply Fin.ext
  rw [finNeg_val, finNeg_val]
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · have hlt : i.val < n := i.isLt
    have h1 : (n - i.val) % n = n - i.val := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : n - (n - i.val) = i.val := by omega
    rw [h2, Nat.mod_eq_of_lt hlt]

theorem finNeg_eq_self_iff {n : ℕ} (hn : 0 < n) (hodd : Odd n) (i : Fin n) :
    finNeg hn i = i ↔ i = ⟨0, hn⟩ := by
  rw [Fin.ext_iff, Fin.ext_iff, finNeg_val]
  show (n - i.val) % n = i.val ↔ i.val = 0
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · exact h0
    · have hlt : i.val < n := i.isLt
      have h1 : (n - i.val) % n = n - i.val := Nat.mod_eq_of_lt (by omega)
      rw [h1] at h
      rcases hodd with ⟨k, hk⟩
      omega
  · intro h
    rw [h, Nat.sub_zero, Nat.mod_self]

/-- **Arithmetic core of Peterfalvi (14.11.3), specialised to the `η`-grid.**  An integer-valued
`q × p` grid `n` that pairs under the conjugation `(i,j) ↦ (−i,−j)` (`finNeg`) with principal value
`n₀₀ = 1`, summed against a `±1`-sign grid `ε`, has complex norm `≥ 1`.

This packages the conjugation involution `(i,j) ↦ (−i,−j)` on `Fin q × Fin p` (whose unique fixed
point is `(0,0)`, since `q`, `p` are odd) and feeds it to `one_le_norm_signed_paired_sum`.  It is the
exact arithmetic consumed by `generic_character_bound` (14.11.3) and the dual (14.16) parity
contradiction once the `(3.9)` integrality/pairing facts of the `η`-grid are supplied. -/
theorem one_le_norm_eta_grid_signed_sum {q p : ℕ} (hq : 0 < q) (hp : 0 < p)
    (hqodd : Odd q) (hpodd : Odd p) (n ε : Fin q → Fin p → ℤ)
    (hε : ∀ i j, ε i j = 1 ∨ ε i j = -1)
    (hpair : ∀ i j, n (finNeg hq i) (finNeg hp j) = n i j)
    (h00 : n ⟨0, hq⟩ ⟨0, hp⟩ = 1) :
    1 ≤ ‖(∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (n i j : ℂ))‖ := by
  classical
  have hinv : Function.Involutive
      (fun x : Fin q × Fin p => (finNeg hq x.1, finNeg hp x.2)) := by
    intro x
    show (finNeg hq (finNeg hq x.1), finNeg hp (finNeg hp x.2)) = x
    rw [finNeg_involutive hq x.1, finNeg_involutive hp x.2]
  have key := one_le_norm_signed_paired_sum
    (fun x : Fin q × Fin p => n x.1 x.2) (fun x => ε x.1 x.2)
    hinv.toPerm (⟨0, hq⟩, ⟨0, hp⟩) (fun x => hε x.1 x.2)
    (by rw [Function.Involutive.coe_toPerm]; exact hinv)
    (by
      intro x
      rw [Function.Involutive.coe_toPerm]
      constructor
      · intro h
        have h1 : finNeg hq x.1 = x.1 := (Prod.ext_iff.mp h).1
        have h2 : finNeg hp x.2 = x.2 := (Prod.ext_iff.mp h).2
        exact Prod.ext ((finNeg_eq_self_iff hq hqodd x.1).mp h1)
          ((finNeg_eq_self_iff hp hpodd x.2).mp h2)
      · intro h
        rw [h]
        exact Prod.ext ((finNeg_eq_self_iff hq hqodd _).mpr rfl)
          ((finNeg_eq_self_iff hp hpodd _).mpr rfl))
    (by intro x; rw [Function.Involutive.coe_toPerm]; exact hpair x.1 x.2)
    h00
  have hsum : (∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (n i j : ℂ))
      = ∑ x : Fin q × Fin p, (ε x.1 x.2 : ℂ) * (n x.1 x.2 : ℂ) := by
    rw [Fintype.sum_prod_type]
  rw [hsum]
  exact key

/-- Pointwise evaluation of a finite sum of class functions: `(∑ i ∈ s, f i) g = ∑ i ∈ s, f i g`.
General-purpose `ClassFunction` plumbing (hoistable to `ClassFunction.lean`). -/
theorem classFunction_sum_apply {ι : Type*} {k : Type*} [CommRing k]
    (s : Finset ι) (f : ι → ClassFunction G k) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ClassFunction.add_apply, ih, Finset.sum_insert ha]

/-- **Peterfalvi (14.6)+(13.12), the S-side Frobenius kernel** — `C_{S'}(x) ≤ P` for
`x ∈ P#`.  (14.6) puts `S` in case (9.7.b), whose field model (`FieldNormalizerData`) has
Frobenius kernel `P`; the proven transport `FieldNormalizerData.derived_inf_centralizer_le_P`
then gives the containment.  Named §14 obligation: what remains is the (9.7.b) resolution
for `S` — the (14.2.a)-carrier inputs of `field_normalizer_of_U_characteristic_of_inputs`
(§13 producers `basic_structure`/`c_eq_one`, issue 2035/9000 sphere). -/
theorem s_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.P,
      derivedInG hyp.base.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.P := by
  sorry

/-- **Gated `(9.7.b)` T-side field model** (issue 9078 / 9000 sphere): the T-side field-algebra
package assembled into a `TFieldModelData hyp.base` via the proven producer `tFieldModelData_of_repr`
(`SemilinearFieldModel.fieldModelEmbedding`, `E = Q`, `C = V`).  The `V`-conjugation closure `hVQ`
on `Q` is *proven* here (`V ≤ T = N_G(Q)`, `normalizer_Q_eq_T`), and the `Q ⊓ V = ⊥` disjointness
is the ungated `Q_inf_V_eq_bot` field; the σ-assembly, injectivity, kernel/complement identification
are all discharged by the engine.  The **single remaining `sorry`** is *exactly* the field-data
existence — an additive iso `Additive ↥Q ≃+ 𝔽_{q^p}` (from `exists_field_semilinear`, `Q`
elementary-abelian + `V`-irreducible) with a norm-one Singer character `μ : ↥V →* 𝔽_{q^p}ˣ`
(`μ.range = V*`) satisfying the `(14.2)(a)`-dual equivariance — supplied by the `(9.7.b)` resolution
for `T` (the case-B/issue-9000 obligation, dual to the S-side
`field_normalizer_of_U_characteristic_of_inputs`). -/
theorem t_side_caseB_fieldModel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Nonempty (TFieldModelData hyp.base) := by
  letI : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  -- `V` normalizes `Q`: `V ≤ T' ≤ T = N_G(Q)` (`normalizer_Q_eq_T`).
  have hVQ : ∀ (v : ↥hyp.base.V) (x : ↥hyp.base.Q),
      (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.Q := by
    intro v x
    have hVT : hyp.base.V ≤ hyp.base.T :=
      (show hyp.base.V ≤ derivedInG hyp.base.T by
        rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right).trans (Subgroup.map_subtype_le _)
    have hvN : (v : G) ∈ Subgroup.normalizer (hyp.base.Q : Set G) := by
      rw [OddOrder.Peterfalvi.S15.normalizer_Q_eq_T hG hyp.base]; exact hVT v.2
    exact (Subgroup.mem_set_normalizer_iff.mp hvN (x : G)).mp x.2
  -- gated `(9.7.b)` field-algebra package `(e, μ, hcompat)` for `T`
  obtain ⟨e, μ, hμ_inj, hμ_range, hcompat⟩ :
      ∃ (e : Additive ↥hyp.base.Q ≃+ GaloisField hyp.base.q hyp.base.p)
        (μ : ↥hyp.base.V →* (GaloisField hyp.base.q hyp.base.p)ˣ)
        (_ : Function.Injective μ)
        (_ : μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.q hyp.base.p),
        ∀ (v : ↥hyp.base.V) (x : ↥hyp.base.Q),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hVQ v x⟩ : ↥hyp.base.Q))
            = ((μ v : (GaloisField hyp.base.q hyp.base.p)ˣ) : GaloisField hyp.base.q hyp.base.p) *
                e (Additive.ofMul x) := by
    sorry
  exact tFieldModelData_of_repr hyp.base e μ hμ_inj hμ_range hVQ hcompat

/-- **Peterfalvi (14.4)+(13.12), the T-side Frobenius kernel** — `C_{T'}(x) ≤ Q` for
`x ∈ Q#` (dual of `s_side_frobenius_kernel`: (14.4) puts `T` in case (9.7.b), and the
T-side field model has Frobenius kernel `Q`).  Discharged (engine proven, `S16_G0Coprime`) by the
minimal (14.4) carrier `TFieldModelData` from `t_side_caseB_fieldModel` (injective
`σ : F_{q^p} ⋊ V* →* G` with kernel `Q`, complement `V`) through the proven transport
`TFieldModelData.derived_inf_centralizer_le_Q`. -/
theorem t_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.Q,
      derivedInG hyp.base.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.Q := by
  intro x hx
  obtain ⟨data⟩ := t_side_caseB_fieldModel hG hyp
  exact data.derived_inf_centralizer_le_Q hx

/-- **Peterfalvi (14.11.3), support half**: every element of the generic set `G₀` has order
prime to `pq`.  The avoidance fields of `MHypothesis` (`G0_avoid`) feed the proven
(14.11.3) chain `orderOf_coprime_pq_of_not_mem_conj` (W-orbit bridge + per-side
Sylow/TI/(2.1) coset collapse, `S16_G0Coprime`), with the two case-(9.7.b) Frobenius-kernel
inputs supplied by `s_side_frobenius_kernel`/`t_side_frobenius_kernel`. -/
theorem MHypothesis.G0_orderOf_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) {g : G} (hg : g ∈ Mdata.G0) :
    Nat.Coprime (orderOf g) (hyp.base.p * hyp.base.q) := by
  obtain ⟨hreg, hP, hQ⟩ := Mdata.G0_avoid g hg
  exact orderOf_coprime_pq_of_not_mem_conj hG hyp.base (T_typeII hG hyp)
    (s_side_frobenius_kernel hG hyp) (t_side_frobenius_kernel hG hyp) hreg hP hQ

/-- **Peterfalvi (3.9.a,c) for the `η`-grid on the generic set `G₀`** (faithful §3 Dade obligation).
For `g ∈ G₀` (an element of order prime to `pq` lying outside `Ã(M)`):

* (3.9.c) each grid value `η_ij(g)` is a rational integer (`eta_int`);
* (3.9.a) the grid is invariant under the conjugation `(i,j) ↦ (−i,−j)` (`finNeg`), i.e. the values
  pair up (`eta_pair`), with principal value `η₀₀(g) = 1` (`eta_principal`);
* `β_M^τ(g) = 0`, since `g ∉ Ã(M)` (`betaM_vanish`).

These are the Dade-character integrality/symmetry facts of Peterfalvi (3.9) specialised to the
`M`-grid plus the support vanishing of (14.10); their honest construction lives in the §3/§4
Dade-isometry layer (the abstract §16 `ω`/`η`/`tau3` carriers do not yet pin it). -/
structure EtaGenericData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  eta_int : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)
  eta_pair : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
      = hyp.base.eta i j g
  eta_principal : ∀ g ∈ Mdata.G0,
    hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1
  betaM_vanish : ∀ g ∈ Mdata.G0, Mdata.betaM g = 0

/-- **Peterfalvi (3.9.a/c), the Galois half of the `η`-grid facts** — the genuine §3/§5
obligation still gated on the `τ₃`-Galois-equivariance (issue 3002 follow-up; the carried
grid primitives determine `η` on `W`-regular values but not its Galois behaviour off `W`):
on the generic set `G₀`, the `η`-grid takes integer values (3.9.c) and pairs under the
negation involution (3.9.a). -/
theorem eta_grid_galois_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) := by
  -- Now **proven** by citing the issue-3002 keystone fields threaded into `S15.Hypothesis`
  -- by lane b (`eta_intCast_of_coprime` = (3.9.c), `eta_pair_of_coprime` = (3.9.a)), which apply
  -- to every `g` of order coprime to `pq` — and `G₀` elements are exactly such
  -- (`MHypothesis.G0_orderOf_coprime`).
  refine ⟨fun g hg i j => ?_, fun g hg i j => ?_⟩
  · exact hyp.base.eta_intCast_of_coprime g (Mdata.G0_orderOf_coprime hG hg) i j
  · exact hyp.base.eta_pair_of_coprime g (Mdata.G0_orderOf_coprime hG hg) i j

/-- **Peterfalvi (3.9.a/c) `η`-grid facts on `G₀`**: on the generic set `G₀`, the `η`-grid
takes integer values (3.9.c), pairs under the negation involution (3.9.a), and has principal
entry `η₀₀ = 1`.  The principal entry is now genuine (`eta_principal_apply_eq_one`, the
issue-2033 grid-semantics payoff, `S16_GridExpansion`); the Galois half remains the named
obligation `eta_grid_galois_facts_on_G0`. -/
theorem eta_grid_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) ∧
    (∀ g ∈ Mdata.G0,
      hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1) := by
  obtain ⟨hint, hpair⟩ := eta_grid_galois_facts_on_G0 hG hyp Mdata
  exact ⟨hint, hpair, fun g _ => eta_principal_apply_eq_one hyp.base g⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.9)/(14.10) generic-set producer.**  The `η`-grid integrality/symmetry on `G₀`
(`eta_grid_facts_on_G0`, the §3/§5 grid obligation) together with the **now-genuine** support
vanishing `β_M^τ = 0` on `G₀`: `β_M = β` is a Dade image, so its support lies in `Ã(M)`
(`beta_support_subset_dadeSupport`), while `G₀` avoids `Ã(M)` (`G0_off_dadeSupport`). -/
theorem eta_generic_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    EtaGenericData hyp Mdata := by
  obtain ⟨hint, hpair, hprinc⟩ := eta_grid_facts_on_G0 hG hyp Mdata
  refine { eta_int := hint, eta_pair := hpair, eta_principal := hprinc, betaM_vanish := ?_ }
  -- **Peterfalvi (14.11.3)**: `β_M^τ` vanishes off its Dade support `Ã(M)`, and `G₀ ⊆ G ∖ Ã(M)`.
  intro g hg
  rw [Mdata.betaM_eq]
  by_contra hne
  have hmem := Mdata.h78.beta_support_subset_dadeSupport (Function.mem_support.mpr hne)
  rw [Mdata.h78_hyp_eq] at hmem
  exact Mdata.G0_off_dadeSupport g hg hmem

/-- **Peterfalvi (14.11.3)**: on the generic set `G_0`, the extended character `ψ^{τ₁}` has
absolute value at least one: `|ψ^{τ₁}(g)| ≥ 1` for `g ∈ G_0`.

De-opacified (lane-c §16 char-endpoint): the former opaque carrier field
`generic_bound_formula : G → Prop` is replaced by this concrete inequality on the `ℤ`-linear
Dade extension `τ₁` applied to `ψ`.  Proof recipe (Pf p.89): for `g ∈ G_0`, `β_M^τ(g) = 0` (as
`g ∉ Ã(M)`), so by (14.11.2) `ψ^{τ₁}(g) = ±Σ_{i,j}(±η_ij(g))`; `g` has order prime to `pq`, so by
(3.9.c) each `η_ij(g) ∈ ℤ` and by (3.9.a) they pair under conjugation, and `η₀₀(g) = 1`, whence
`Σ(±η_ij(g)) ∈ 2ℤ+1`, giving absolute value `≥ 1`.  Depends on `betaM_expansion` (14.11.2). -/
theorem generic_character_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    ∀ g : G, g ∈ Mdata.G0 → 1 ≤ ‖(Mdata.tau1 Mdata.psi) g‖ := by
  classical
  -- (14.11.2): the signed `η`-grid expansion of `β_M^τ`.
  obtain ⟨_he, ε, hε, χ, hχnorm, hexp⟩ := betaM_expansion _hG hyp Mdata hne
  -- (3.9)/(14.10): the `η`-grid is integral and conjugation-symmetric on `G₀`, and `β_M^τ`
  -- vanishes there.
  have hdata := eta_generic_data _hG hyp Mdata
  intro g hg
  -- (3.9.c) integer values of the `η`-grid at `g`.
  choose n hn using hdata.eta_int g hg
  -- Evaluate the (14.11.2) expansion at `g` pointwise.
  have happ : Mdata.betaM g
      = (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
          (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g := by
    rw [hexp, ClassFunction.sub_apply, classFunction_sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [classFunction_sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ClassFunction.smul_apply]
  -- `β_M^τ(g) = 0` gives `χ(g) = Σ ε_ij η_ij(g) = Σ ε_ij (n_ij : ℂ)`.
  have hχ2 : χ g = ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ) := by
    have h0 : (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
        (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g = 0 := by
      rw [← happ]; exact hdata.betaM_vanish g hg
    rw [(sub_eq_zero.mp h0).symm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hn i j]
  -- (3.9.a) the integer grid pairs under negation with principal value `1`.
  have hpair : ∀ i j,
      n (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) = n i j := by
    intro i j
    have he := hdata.eta_pair g hg i j
    rw [hn, hn] at he
    exact_mod_cast he
  have h00 : n ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    have he := hdata.eta_principal g hg
    rw [hn] at he
    exact_mod_cast he
  -- The signed paired sum has norm `≥ 1` (14.11.3 arithmetic core), and `‖χ‖ = ‖ψ^{τ₁}‖`.
  calc (1 : ℝ)
      ≤ ‖∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ)‖ :=
        one_le_norm_eta_grid_signed_sum hyp.base.q_prime.pos hyp.base.p_prime.pos
          hyp.base.q_odd hyp.base.p_odd n ε hε hpair h00
    _ = ‖χ g‖ := by rw [hχ2]
    _ = ‖(Mdata.tau1 Mdata.psi) g‖ := hχnorm g

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), line-83 upper-bound step** — the V-side `M`-analogue of
`S12.Hypothesis.chiRhoNormSq_zeta_le_line83`.  Applying the family inequality (7.5)
`S09.family_inequality` to the norm-one character `ψ^{τ₁}` (`psi_tau1_norm_one`) and dropping the
`G₀`-part of the sum via (14.11.3) `generic_character_bound` (`|ψ^{τ₁}(g)| ≥ 1` on `G₀`) together
with the inclusion `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) gives
`‖ψ^{τ₁ρ}‖² ≤ |A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)`.

This is the first step of (14.11.4)'s upper bound; the remaining passage to the displayed
`1 − 1/p − 1/q + …` is the `|K#|/|M|` evaluation and the §8 TI-counting of the `(W#)^G`/`(P#)^G`/
`(Q#)^G` contributions, isolated for the cascade producer `normCascadeData`.  `famG₀ =
(toFamilyHypothesis71).G0 = G − Ã(M)` and `G₀ = Mdata.G0`. -/
theorem MHypothesis.chiRhoNormSq_psi_le_line83 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      ≤ (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
          / (Nat.card ↥Mdata.M : ℝ)
        + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
          - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)) := by
  haveI := Mdata.finiteG
  have hA0 : (Mdata.toFamilyHypothesis71).A 0
      = OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI := rfl
  have hL0 : (Mdata.toFamilyHypothesis71).L 0 = Mdata.M := rfl
  -- (7.5) line 81 (single member, `k = 1`).
  have h81 := OddOrder.Peterfalvi.S09.family_inequality (Mdata.toFamilyHypothesis71)
    (Mdata.tau1 Mdata.psi) Mdata.psi_tau1_norm_one
  rw [Fin.sum_univ_one, hA0, hL0] at h81
  -- `G₀ ⊆ famG₀`: every `g ∈ G₀` is off the Dade support `Ã(M)`.
  have hsub : Finset.univ.filter (fun g : G => g ∈ Mdata.G0)
      ⊆ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ g, fun _ => Mdata.G0_off_dadeSupport g hg.2⟩
  -- Drop the `G₀`-part: `|G₀| ≤ Σ_{G₀} ‖ψ^{τ₁}‖² ≤ Σ_{famG₀} ‖ψ^{τ₁}‖²`.
  have hge : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
    calc ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
        = ∑ _g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0), (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
            ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
          refine Finset.sum_le_sum (fun g hg => ?_)
          have hg2 : g ∈ Mdata.G0 := (Finset.mem_filter.mp hg).2
          have h1 := generic_character_bound _hG hyp Mdata hne g hg2
          nlinarith [h1, norm_nonneg ((Mdata.tau1 Mdata.psi : G → ℂ) g)]
  have hdrop : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 :=
    le_trans hge (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by positivity))
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hcS := mul_le_mul_of_nonneg_left hdrop hGinv
  rw [mul_sub] at h81 ⊢
  linarith [h81, hcS]

/-- **`S09.Hypothesis71.chiRho` depends only on the support hypothesis `H71.hyp`.**  Two `(7.1)`
data with the same underlying `S04.Hypothesis` (the same `H(a)`-family) induce the same `ρ`-image
of any `χ`, even if their chosen Dade maps `τ` differ — `chiRho` never mentions `τ`.  Used to
identify the family-inequality `ρ`-norm of (14.11.4) with the (7.8.b) `ρ`-norm of `h78`. -/
theorem chiRhoCF_congr_hyp [Fintype G] {A : Set G} {L : Subgroup G}
    {H71a H71b : OddOrder.Peterfalvi.S09.Hypothesis71 G A L}
    (h : H71a.hyp = H71b.hyp) (χ : ClassFunction G ℂ) :
    H71a.chiRhoCF χ = H71b.chiRhoCF χ := by
  apply ClassFunction.ext
  intro a
  simp only [OddOrder.Peterfalvi.S09.Hypothesis71.chiRhoCF_apply]
  unfold OddOrder.Peterfalvi.S09.Hypothesis71.chiRho
  rw [h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4) norm bridge.**  The family-inequality `ρ`-norm of `ψ^{τ₁}` (the LHS of
the line-83 bound) equals the (7.8.b) `ρ`-norm `h78.zetaNuRhoNormSq`.  Both are `‖(ψ^{τ₁})^ρ‖²` for
the `(M, A(M))` map `ρ`: `psi_tau1_eq` (`ψ^{τ₁} = ζ^ν`) matches the characters, and `h78_hyp_eq`
(same Dade support hypothesis) plus `chiRhoCF_congr_hyp` (independence of `chiRho` from `τ`) matches
the `ρ`-images.  This is the linchpin tying the (7.5) family-inequality layer to the (7.8.b)
coherence-norm layer of (14.11.4). -/
theorem MHypothesis.chiRhoNormSq_eq_zetaNuRhoNormSq [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      = Mdata.h78.zetaNuRhoNormSq := by
  have hcf : ((Mdata.toFamilyHypothesis71).hyp71 0).chiRhoCF (Mdata.tau1 Mdata.psi)
      = Mdata.h78.zetaNuRho := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho, Mdata.psi_tau1_eq]
    exact chiRhoCF_congr_hyp Mdata.h78_hyp_eq.symm _
  simp only [OddOrder.Peterfalvi.S09.FamilyHypothesis71.chiRhoNormSq,
    OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRhoNormSq, hcf]
  congr 1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the lower bound** `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²` — the genuine (7.8.b)
coherence-norm content of (14.11.4).  Combines the (7.8.b) lower bound for the coherent type-I `M`
(`h78_zetaNuRho_normSq_ge`) with the index identities `h78.kernelOrder = |K| = k` and
`h78.complementIndex = |M:K| = p q` (`h78_H_eq`, `e_eq_index`, `complement_card_eq_pq`) via the norm
bridge `chiRhoNormSq_eq_zetaNuRhoNormSq`.  This is the `lower` field of the `NormCascadeData`
producer `normCascadeData`; the remaining gate is the upper-bound §8 TI-counting. -/
theorem MHypothesis.rhoNormSq_ge_lower [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    1 - ((hyp.base.p * hyp.base.q : ℕ) : ℝ) / (Mdata.k : ℝ)
      ≤ (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0 := by
  rw [Mdata.chiRhoNormSq_eq_zetaNuRhoNormSq]
  -- `K ≤ M` for the index/card bookkeeping.
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  -- `h78.kernelOrder = |K| = k`.
  have hko : Mdata.h78.kernelOrder = Mdata.k := by
    rw [Mdata.k_eq_card_K]
    show Nat.card ↥(Mdata.h78.hyp76.H) = Nat.card ↥Mdata.K
    rw [Mdata.h78_H_eq]
  -- `h78.complementIndex = |M:K| = p q`.
  have hci : Mdata.h78.complementIndex = hyp.base.p * hyp.base.q := by
    have hmul := Mdata.h78.kernelOrder_mul_complementIndex_eq_card_L
    rw [hko, Mdata.k_eq_card_K] at hmul
    have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
    have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
      rw [← hcardK]; exact Subgroup.card_mul_index _
    have hidxpq : (Mdata.K.subgroupOf Mdata.M).index = hyp.base.p * hyp.base.q := by
      rw [← Mdata.e_eq_index]; exact Mdata.complement_card_eq_pq
    rw [hidxpq] at hidx
    have hKpos : 0 < Nat.card ↥Mdata.K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hKpos (hmul.trans hidx.symm)
  -- Rewrite the (7.8.b) carrier into `p q`/`k` and conclude.
  have key := Mdata.h78_zetaNuRho_normSq_ge
  rw [hci, hko] at key
  exact key

/-- **The type-I Dade support is the kernel sharp** `A(M) = K#`, the §8 cardinality input
`|A(M)| = |K#| = k − 1` of Peterfalvi (14.11.4) (Coq `PFsection14`: the `Dade_cover_inequality`
support term `#|A| = k.-1`).  For a Frobenius group `M` with kernel `N` (the complement acts
fixed-point-freely on `N#`), the centralizer-support
`centralizerSupport N# M = {y ∈ M : y ≠ 1, ∃ x ∈ N#, [y,x]=1}` is exactly `N#`: the forward
inclusion is the Frobenius FPF property `centralizer_kernel_le` (`C_M(x) ≤ N` for `x ∈ N#`), the
reverse takes `x = y`.  Applied with `N = K = M_F`, this is `typeIA M = K#`. -/
theorem centralizerSupport_sharpSubgroup_eq_of_frobenius [Finite G] {M N : Subgroup G}
    {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_setOf_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Peterfalvi (14.11.4): `|A(M)| = k − 1`** — the §8 cardinality input of the upper bound.  The
type-I Dade support `A(M) = typeIA M` equals `K#` (`centralizerSupport_sharpSubgroup_eq_of_frobenius`
applied to the Frobenius structure of `M` from `typeI_frobenius` (12.7), kernel `K = M_F`), so its
cardinality is `|K| − 1 = k − 1`. -/
theorem MHypothesis.card_typeIA_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) = Mdata.k - 1 := by
  -- Frobenius witness for `M` (kernel `M_F`), from (12.7).
  obtain ⟨fdata, _⟩ :=
    OddOrder.Peterfalvi.S14.typeI_frobenius hG Mdata.M_maximal ⟨Mdata.typeIHyp.typeI⟩
  -- The two kernels both equal `maxNilpotentNormalHall M`.
  have hKf : fdata.typeI.typeF.H = Mdata.typeIHyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, Mdata.typeIHyp.typeI.typeF.H_eq]
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥Mdata.M
      (Mdata.typeIHyp.typeI.typeF.H.subgroupOf Mdata.M) fdata.complement := hKf ▸ fdata.frobenius
  -- `typeIA M = K#` (FPF support identity).
  have hTI : OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup Mdata.typeIHyp.typeI.typeF.H :=
    centralizerSupport_sharpSubgroup_eq_of_frobenius hfrob Mdata.typeIHyp.typeI.typeF.H_le
  -- `typeF.H = K`, so `|K#| = |K| − 1 = k − 1`.
  have hHK : Mdata.typeIHyp.typeI.typeF.H = Mdata.K := by
    rw [Mdata.typeIHyp.typeI.typeF.H_eq, Mdata.K_eq_MF]
  have hc : Nat.card ↥Mdata.K = ((Mdata.K : Set G)).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hTI, hHK, Mdata.k_eq_card_K, Nat.card_coe_set_eq, OddOrder.GroupTheory.sharpSubgroup,
    Set.ncard_sdiff (Set.singleton_subset_iff.mpr Mdata.K.one_mem), Set.ncard_singleton, hc]

/-- **Peterfalvi (14.11): `|M| = p q k`** — the order of the type-I maximal `M`, from
`[M : K] = e = pq` (`e_eq_index`, `complement_card_eq_pq`) and `|K| = k` (`k_eq_card_K`) by Lagrange.
The denominator of the §8 cardinality input `|A(M)|/|M| = (k − 1)/(kpq)` of (14.11.4). -/
theorem MHypothesis.card_M_eq {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥Mdata.M = hyp.base.p * hyp.base.q * Mdata.k := by
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
    rw [← hcardK]; exact Subgroup.card_mul_index _
  have hidxpq : (Mdata.K.subgroupOf Mdata.M).index = hyp.base.p * hyp.base.q := by
    rw [← Mdata.e_eq_index]; exact Mdata.complement_card_eq_pq
  rw [hidxpq] at hidx
  rw [← hidx, Mdata.k_eq_card_K]; ring

/-- **The exceptional set `W − (W₁ ∪ W₂)` of a cyclic `W = W₁ × W₂` is a TI-subset with
normalizer-bound `W`** — the abstract core of Peterfalvi's `V`-set TI property, generalising
`S12.typePData_V_ti` to take the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`) directly.
Given `g` conjugating some `a` of the set into it, `N_G({a}) = W = N_G({g a g⁻¹})` forces `g` to
normalize `W`, and cyclic-uniqueness (`cyclic_subgroup_eq_of_card_eq`) makes `W₁`, `W₂`
`g`-stable, so `g` normalizes the set, whence `g ∈ N_G(set) = W`.  The `W`-orbit TI input to the
(14.11.4) §8 count (`hnorm` is the genuine §13 structural fact, supplied from the partner type-`P`
structure). -/
theorem isTISubset_sdiff_sup_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W) :
    OddOrder.GroupTheory.IsTISubset ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) W := by
  classical
  set vset : Set G := (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) with hvset
  haveI : IsCyclic ↥W := hWcyc
  have hW1le : W1 ≤ W := hWeq ▸ le_sup_left
  have hW2le : W2 ≤ W := hWeq ▸ le_sup_right
  have mem_norm_sing : ∀ c z : G,
      z ∈ Subgroup.normalizer ({c} : Set G) ↔ z * c * z⁻¹ = c := by
    intro c z
    rw [Subgroup.mem_set_normalizer_iff]
    constructor
    · intro hz; have := (hz c).mp rfl; simpa using this
    · intro hz h
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hrfl => hrfl ▸ hz, fun hh => ?_⟩
      have hcc : z * h * z⁻¹ = z * c * z⁻¹ := by rw [hh, hz]
      exact mul_left_cancel (mul_right_cancel hcc)
  intro g hg
  obtain ⟨a, haV, hbV⟩ := hg
  have hNa : Subgroup.normalizer ({a} : Set G) = W :=
    hnorm {a} (Set.singleton_nonempty a) (Set.singleton_subset_iff.mpr haV)
  have hNb : Subgroup.normalizer ({g * a * g⁻¹} : Set G) = W :=
    hnorm {g * a * g⁻¹} (Set.singleton_nonempty _) (Set.singleton_subset_iff.mpr hbV)
  have hgW : ∀ h, h ∈ W ↔ g * h * g⁻¹ ∈ W := by
    intro h
    have e1 : (h ∈ W) ↔ h * a * h⁻¹ = a := by rw [← hNa, mem_norm_sing]
    have e2 : (g * h * g⁻¹ ∈ W) ↔ h * a * h⁻¹ = a := by
      rw [← hNb, mem_norm_sing]
      have hexp : g * h * g⁻¹ * (g * a * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
        group
      rw [hexp]
      exact ⟨fun hh => mul_left_cancel (mul_right_cancel hh), fun hh => by rw [hh]⟩
    rw [e1, e2]
  have hstab : ∀ (A : Subgroup G), A ≤ W → ∀ x : G, g * x * g⁻¹ ∈ A ↔ x ∈ A := by
    intro A hAW
    have hmap_le : A.map (MulAut.conj g).toMonoidHom ≤ W := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hzA, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hgW z).mp (hAW hzA)
    have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    have hsubeq : (A.map (MulAut.conj g).toMonoidHom).subgroupOf W = A.subgroupOf W := by
      apply OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq (C := ↥W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, hcard]
    have hmapeq : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hmap_le, hsubeq,
        Subgroup.map_subgroupOf_eq_of_le hAW]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [hmapeq]; exact hx
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hzA, hz⟩ := hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz
      have hzx : z = x := mul_left_cancel (mul_right_cancel hz)
      rwa [hzx] at hzA
    · intro hx
      have hmem : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapeq] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  rw [← hnorm vset ⟨a, haV⟩ Set.Subset.rfl, Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [hvset, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe]
  rw [hgW h, hstab W1 hW1le h, hstab W2 hW2le h]

/-- **`W` stabilises its exceptional set `W − (W₁ ∪ W₂)` under conjugation** — the `hstab` input to
the `W`-orbit count `ncard_conjClassSet_of_isTISubset`/`orbit_normSq_term`, generalising
`S12.typePData_W_normalizes_typePV`.  Every `l ∈ W = N_G(set)` (via `hnorm`) normalizes the set. -/
theorem conj_smul_sdiff_sup_eq_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ∀ l ∈ W, MulAut.conj l • ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
      = (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) := by
  intro l hl
  have hlN : l ∈ Subgroup.normalizer ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) := by
    rw [hnorm _ hne Set.Subset.rfl]; exact hl
  rw [Subgroup.mem_set_normalizer_iff] at hlN
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact (hlN v).mp hv
  · intro hx
    refine ⟨l⁻¹ * x * l, (hlN _).mpr ?_, by group⟩
    rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hx

/-- **Orbit measure of a TI-subset** `|𝒞_G(A)|/|G| = |A|/|N|` — the real-valued form of the §8
TI-counting `ncard_conjClassSet_of_isTISubset` (`|𝒞_G(A)| = |A|·[G:N]`).  For a TI-subset `A` with
normalizer-bound `N` stabilizing `A`, the conjugacy-saturation `𝒞_G(A) = A^G` has relative measure
`|A|/|N|` in `G`.  The reusable bridge turning each (14.11.4) orbit `(W#)^G`/`(P#)^G`/`(Q#)^G` into a
`1/|N_G(·)|`-term (Pf 04.16 lines 109–115). -/
theorem orbit_normSq_term [Finite G] {A : Set G} {L : Subgroup G}
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A) :
    ((OddOrder.GroupTheory.conjClassSet A).ncard : ℝ) / (Nat.card G : ℝ)
      = (A.ncard : ℝ) / (Nat.card ↥L : ℝ) := by
  rw [OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset hTI hstab, ← L.card_mul_index]
  have hidx : (L.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.index_ne_zero_of_finite
  push_cast
  rw [mul_div_mul_right _ _ hidx]

/-- **`W`-orbit relative measure** `|(W − (W₁ ∪ W₂))^G|/|G| = |W − (W₁ ∪ W₂)|/|W|` — the assembled
`W`-orbit term of Peterfalvi (14.11.4), combining the TI core
(`isTISubset_sdiff_sup_of_normalizer_eq`), the `W`-stability
(`conj_smul_sdiff_sup_eq_of_normalizer_eq`), and the orbit bridge (`orbit_normSq_term`).  Given the
cyclic structure `W = W₁ × W₂` and the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`). -/
theorem orbit_sdiff_sup_normSq_term [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ((OddOrder.GroupTheory.conjClassSet
        ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))).ncard : ℝ) / (Nat.card G : ℝ)
      = (((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard : ℝ) / (Nat.card ↥W : ℝ) :=
  orbit_normSq_term (isTISubset_sdiff_sup_of_normalizer_eq hWcyc hWeq hnorm)
    (conj_smul_sdiff_sup_eq_of_normalizer_eq hnorm hne)

/-- **The normalizer of `P` stabilises `P# = P ∖ {1}` under conjugation** — the `hstab` input to the
`P#`-orbit count `orbit_normSq_term`.  For `l ∈ N_G(P)`, conjugation by `l` permutes `P` and fixes
`1`, so it permutes `P#`.  (With `IsTI P` — definitionally `IsTISubset (P ∖ {1}) (N_G(P))` — this
gives `|(P#)^G|/|G| = (|P|−1)/|N_G(P)|`, the `P`/`Q` orbit terms of Peterfalvi (14.11.4).) -/
theorem conj_smul_sharpSubgroup_eq_of_mem_normalizer {P : Subgroup G} {l : G}
    (hl : l ∈ Subgroup.normalizer (P : Set G)) :
    MulAut.conj l • (OddOrder.GroupTheory.sharpSubgroup P)
      = OddOrder.GroupTheory.sharpSubgroup P := by
  rw [Subgroup.mem_set_normalizer_iff] at hl
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply,
    OddOrder.GroupTheory.sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, ⟨hvP, hv1⟩, rfl⟩
    refine ⟨(hl v).mp hvP, fun h => hv1 ?_⟩
    have : v = l⁻¹ * (l * v * l⁻¹) * l := by group
    rw [this, h]; group
  · rintro ⟨hxP, hx1⟩
    refine ⟨l⁻¹ * x * l, ⟨(hl _).mpr ?_, fun h => hx1 ?_⟩, by group⟩
    · rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hxP
    · rw [show x = l * (l⁻¹ * x * l) * l⁻¹ by group, h]; group

/-- **`P#`-orbit relative measure** `|(P#)^G|/|G| = |P#|/|N_G(P)|` — the `P`/`Q` orbit term of
Peterfalvi (14.11.4), for a TI-subgroup `P` (`Subgroup.IsTI P`, definitionally
`IsTISubset (P ∖ {1}) (N_G(P))`).  Combines the TI property with the `P#`-stability
(`conj_smul_sharpSubgroup_eq_of_mem_normalizer`) via the orbit bridge `orbit_normSq_term`. -/
theorem orbit_sharpSubgroup_normSq_term [Finite G] {P : Subgroup G} (hTI : Subgroup.IsTI P) :
    ((OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup P)).ncard : ℝ)
        / (Nat.card G : ℝ)
      = ((OddOrder.GroupTheory.sharpSubgroup P).ncard : ℝ)
        / (Nat.card ↥(Subgroup.normalizer (P : Set G)) : ℝ) :=
  orbit_normSq_term hTI (fun _ hl => conj_smul_sharpSubgroup_eq_of_mem_normalizer hl)

/-- **`|P#| + 1 = |P|`** — the cardinality of the sharp subgroup (the `|P| − 1` numerator of the
`P`/`Q` orbit term of (14.11.4)), additive form. -/
theorem ncard_sharpSubgroup_add_one {P : Subgroup G} [Finite ↥P] :
    (OddOrder.GroupTheory.sharpSubgroup P).ncard + 1 = Nat.card ↥P := by
  have hc : Nat.card ↥P = (P : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hc, OddOrder.GroupTheory.sharpSubgroup, ← Set.ncard_singleton (1 : G),
    Set.ncard_diff_add_ncard_of_subset (Set.singleton_subset_iff.mpr P.one_mem)]

/-- **`|W − (W₁ ∪ W₂)| + |W₁| + |W₂| = |W| + 1`** — the cardinality of the exceptional set, by
inclusion–exclusion with `W₁ ∩ W₂ = {1}` (`hdisj`).  The numerator of the `W`-orbit term
`|W − (W₁ ∪ W₂)|/|W|` of Peterfalvi (14.11.4) (additive form, avoiding `ℕ`-truncation). -/
theorem ncard_sdiff_sup_add_eq [Finite G] {W W1 W2 : Subgroup G}
    (hW1le : W1 ≤ W) (hW2le : W2 ≤ W) (hdisj : W1 ⊓ W2 = ⊥) :
    ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard + Nat.card ↥W1 + Nat.card ↥W2
      = Nat.card ↥W + 1 := by
  have hsub : ((W1 : Set G) ∪ (W2 : Set G)) ⊆ (W : Set G) :=
    Set.union_subset (SetLike.coe_subset_coe.mpr hW1le) (SetLike.coe_subset_coe.mpr hW2le)
  have h1 := Set.ncard_diff_add_ncard_of_subset hsub
  have h2 := Set.ncard_union_add_ncard_inter (W1 : Set G) (W2 : Set G)
  have h3 : ((W1 : Set G) ∩ (W2 : Set G)).ncard = 1 := by
    rw [← Subgroup.coe_inf, hdisj, Subgroup.coe_bot, Set.ncard_singleton]
  have hcW : Nat.card ↥W = (W : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW1 : Nat.card ↥W1 = (W1 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW2 : Nat.card ↥W2 = (W2 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hcW, hcW1, hcW2]
  omega

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the `G₀`-drop set reduction** — `|famG₀| − |G₀| ≤ |(W−(W₁∪W₂))^G| +
|(P#)^G| + |(Q#)^G|` (as `ncard`s).  Since `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) and `famG₀ ∖ G₀` is
covered by the three orbits (`G0_orbit_cover`, the (14.11.3) `G₀ = G − [Ã(M) ∪ orbits]`), the
difference is bounded by the orbit cardinalities (`Set.ncard_sdiff` + `Set.ncard_union_le`).  The
set-theoretic core of the (14.11.4) §8 TI-counting, feeding `orbit_normSq_term` per orbit. -/
theorem MHypothesis.famG0_sub_filter_card_le_orbit_ncard [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ((OddOrder.GroupTheory.conjClassSet
            ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ) := by
  classical
  haveI := Mdata.finiteG
  set famG0 := (Mdata.toFamilyHypothesis71).G0 with hfamdef
  set Worb := OddOrder.GroupTheory.conjClassSet
    ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
  set Porb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
  set Qorb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  -- `g ∈ famG₀ ↔ g ∉ Ã(M)` (single-member family).
  have hmemfam : ∀ g : G, g ∈ famG0 ↔ g ∉ Mdata.typeIHyp.dadeData.dade.dadeSupport := by
    intro g
    refine ⟨fun hg => hg 0, fun hg i => ?_⟩
    fin_cases i; exact hg
  -- `G₀ ⊆ famG₀` and `famG₀ ∖ G₀ ⊆ orbits`.
  have hsub : Mdata.G0 ⊆ famG0 := fun g hg => (hmemfam g).mpr (Mdata.G0_off_dadeSupport g hg)
  have hcover : famG0 \ Mdata.G0 ⊆ Worb ∪ Porb ∪ Qorb := by
    rintro g ⟨hgfam, hgG0⟩
    exact Mdata.G0_orbit_cover g ((hmemfam g).mp hgfam) hgG0
  -- ncard reduction.
  have hdiff : (famG0 \ Mdata.G0).ncard ≤ Worb.ncard + Porb.ncard + Qorb.ncard :=
    le_trans (Set.ncard_le_ncard hcover)
      (le_trans (Set.ncard_union_le _ _) (by gcongr; exact Set.ncard_union_le _ _))
  have hdeq : (famG0 \ Mdata.G0).ncard = famG0.ncard - Mdata.G0.ncard := Set.ncard_sdiff hsub
  have hG0le : Mdata.G0.ncard ≤ famG0.ncard := Set.ncard_le_ncard hsub
  -- `Nat.card famG₀ = famG₀.ncard`, `|filter| = G₀.ncard`.
  have hfamcard : Nat.card famG0 = famG0.ncard := Nat.card_coe_set_eq famG0
  have hfiltcard : (Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card = Mdata.G0.ncard := by
    rw [Set.ncard_eq_toFinset_card']; congr 1; ext g; simp
  rw [hfamcard, hfiltcard]
  have hcast : (famG0.ncard : ℝ) - (Mdata.G0.ncard : ℝ)
      = ((famG0.ncard - Mdata.G0.ncard : ℕ) : ℝ) := (Nat.cast_sub hG0le).symm
  rw [hcast, ← hdeq]
  calc ((famG0 \ Mdata.G0).ncard : ℝ) ≤ ((Worb.ncard + Porb.ncard + Qorb.ncard : ℕ) : ℝ) := by
        exact_mod_cast hdiff
    _ = (Worb.ncard : ℝ) + (Porb.ncard : ℝ) + (Qorb.ncard : ℝ) := by push_cast; ring

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the upper-bound §8 TI-counting step** (04.16 lines 109–115).  Brings the
line-83 bound `|A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)` (`chiRhoNormSq_psi_le_line83`, proven) up to
the displayed `NormCascadeData.upper`.  The genuine §8 content: `|A(M)|/|M| = (k−1)/(kpq)`
(`card_typeIA_eq`/`card_M_eq`); the `G₀`-drop `famG0_sub_filter_card_le_orbit_ncard` (set-reduction,
proven) plus the orbit measures (`orbit_sdiff_sup_normSq_term`/`orbit_sharpSubgroup_normSq_term`)
and the structural values (`|W|`/`|N_G(P)|`, `IsTI P`/`IsTI Q`, `normalizer_V`) bound the orbits,
then `normCascade_upper_loosen`.  The remaining §8 structural input is the TI/normalizer data of the
Frobenius pieces `W`, `P`, `Q` (the type-I analogue of S12 (10.8)'s `G₁ ⊆ (H#)^G ∪ V^G`). -/
theorem MHypothesis.line83_le_displayed_upper [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
  haveI := Mdata.finiteG
  -- abbreviations
  have hW1le : hyp.base.W1 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_right
  -- positivity (`p`, `q` prime; `u`, `v` from the faithful normalizer carriers; `k`/cards `> 0`).
  have hp : (0 : ℝ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have hq : (0 : ℝ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hkpos : 0 < Mdata.k := Mdata.k_eq_card_K ▸ Nat.card_pos
  have hPpos : 0 < Nat.card ↥hyp.base.P := Nat.card_pos
  have hQpos : 0 < Nat.card ↥hyp.base.Q := Nat.card_pos
  have hNPpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) := Nat.card_pos
  have hNQpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) := Nat.card_pos
  have hupos : 0 < hyp.base.u := by
    by_contra hc
    have hu0 : hyp.base.u = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) = 0 := by
      rw [Mdata.card_normalizer_P_eq, hu0, mul_zero, zero_mul]
    omega
  have hvpos : 0 < hyp.base.v := by
    by_contra hc
    have hv0 : hyp.base.v = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) = 0 := by
      rw [Mdata.card_normalizer_Q_eq, hv0, mul_zero, zero_mul]
    omega
  -- orbit measures (equalities).
  have hWm := orbit_sdiff_sup_normSq_term hyp.base.W_cyclic hyp.base.W_eq_join
    Mdata.W_normalizer_V (S15.W_sdiff_nonempty hyp.base)
  have hPm := orbit_sharpSubgroup_normSq_term Mdata.P_isTI
  have hQm := orbit_sharpSubgroup_normSq_term Mdata.Q_isTI
  -- cardinalities of the supports.
  have hWc := ncard_sdiff_sup_add_eq hW1le hW2le hyp.base.W1_inf_W2_eq_bot
  have hPc := ncard_sharpSubgroup_add_one (P := hyp.base.P)
  have hQc := ncard_sharpSubgroup_add_one (P := hyp.base.Q)
  -- `|W-set| = pq + 1 − (p+q)`, `|N_G(P)| = |P| u q`, etc. (`ℕ`-level facts → `ℝ`).
  have hWsetR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
      = (hyp.base.p : ℝ) * hyp.base.q + 1 - hyp.base.p - hyp.base.q := by
    have : ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard
        + (hyp.base.p + hyp.base.q) = hyp.base.p * hyp.base.q + 1 := by
      rw [← S15.card_W1_add_W2 hyp.base,
        ← S15.card_W_eq_pq hyp.base]
      omega
    have hR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
        + ((hyp.base.p : ℝ) + hyp.base.q) = (hyp.base.p : ℝ) * hyp.base.q + 1 := by
      exact_mod_cast this
    linarith
  -- the three orbit-term values (equalities).
  have hWterm : (OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard
        / (Nat.card G : ℝ)
      = 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hWm, hWsetR]
    have hWcardR : (Nat.card ↥hyp.base.W : ℝ) = (hyp.base.p : ℝ) * hyp.base.q := by
      rw [S15.card_W_eq_pq hyp.base]; push_cast; ring
    rw [hWcardR]; push_cast; field_simp; ring
  have hPterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.P : ℝ) - 1)
        / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ) := by
    rw [hPm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ)
        = (Nat.card ↥hyp.base.P : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.P : ℝ) := by exact_mod_cast hPc
      linarith
    rw [hsharpR, Mdata.card_normalizer_P_eq]
  have hQterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.Q : ℝ) - 1)
        / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [hQm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ)
        = (Nat.card ↥hyp.base.Q : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.Q : ℝ) := by exact_mod_cast hQc
      linarith
    rw [hsharpR, Mdata.card_normalizer_Q_eq]
  -- `|A(M)|/|M| = (k−1)/(kpq)`.
  have hAterm : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      = ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [Mdata.card_typeIA_eq hG, Mdata.card_M_eq]
    have hkR : ((Mdata.k - 1 : ℕ) : ℝ) = (Mdata.k : ℝ) - 1 := by
      have : 1 ≤ Mdata.k := hkpos
      push_cast [Nat.cast_sub this]; ring
    rw [hkR]; push_cast; ring
  -- the `G₀`-drop, scaled by `1/|G|`.
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hdrop := mul_le_mul_of_nonneg_left Mdata.famG0_sub_filter_card_le_orbit_ncard hGinv
  -- `(1/|G|)·Σ ncard = Σ (ncard/|G|) = hWterm + hPterm + hQterm`.
  have hsum : (Nat.card G : ℝ)⁻¹ * (((OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ))
      = (1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ) + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ))
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [← hWterm, ← hPterm, ← hQterm]; ring
  -- assemble: `line83-RHS ≤ raw bound`.
  have hraw : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
          + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ)
        + ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hAterm]; rw [hsum] at hdrop; linarith
  -- loosen the raw bound to the displayed one.
  exact le_trans hraw (normCascade_upper_loosen hyp.base.p_prime.pos hyp.base.q_prime.pos
    hupos hvpos hkpos hPpos hQpos)

/-- **Faithful §7 carrier for the `ρ`-norm two-sided bound of Peterfalvi (14.11.4).**

The character theory of (14.11.4) reduces to a two-sided bound on `‖ψ^{τ₁ρ}‖²`, where `ρ` is the
Hypothesis (7.1) map for `(M, A(M))` (Pf (14.11.4), p.90):

* `lower` — **(7.8.b)** (Pf 04.16 line 113): the §7 coherence-norm formula `‖ζ^{νρ}‖² ≥ 1 − e/h`
  for the coherent type-I `M` (with `e = |M:K| = pq`, `h = |K| = k`) gives `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`.
  **Proven** (`MHypothesis.rhoNormSq_ge_lower`), via the `h78` coherence carrier and the norm bridge
  `chiRhoNormSq_eq_zetaNuRhoNormSq`.
* `upper` — **(7.5) + (14.11.3) + §8 TI-counting**: the (7.5) family inequality applied to the
  norm-one `ψ^{τ₁}`, dropping the `G_0`-part via `|ψ^{τ₁}(g)| ≥ 1` (`generic_character_bound`,
  14.11.3) to line 83 (`chiRhoNormSq_psi_le_line83`), then the §8 TI-counting of the
  `(W#)^G`/`(P#)^G`/`(Q#)^G` orbit contributions giving the raw estimate, loosened by
  `(|P|−1)/|P| ≤ 1`, `(|Q|−1)/|Q| ≤ 1`, `(k−1)/k ≤ 1` (`normCascade_upper_loosen`) to the
  `normCascadeBound` error terms `2/(pq) + 1/(uq) + 1/(vp)`.

The two-sided structure mirrors the textbook's two-step derivation; the `lower` (7.8.b) bound is
proven, and the remaining genuine obligation is the upper §8 TI-counting, isolated in
`normCascadeData`. -/
structure NormCascadeData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- `‖ψ^{τ₁ρ}‖²`, the squared `L`-norm of the Hypothesis (7.1) `ρ`-image of `ψ^{τ₁}`.
  Real-valued (matching `S09.FamilyHypothesis71.chiRhoNormSq : ℝ`), so the (7.5)/(7.8.b)
  derivation lives in `ℝ`; the passage to the rational `normCascadeBound` is a final cast. -/
  rhoNormSq : ℝ
  /-- **(7.8.b)** lower bound: `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`
  (proven, `MHypothesis.rhoNormSq_ge_lower`). -/
  lower :
    (1 : ℝ) - ((hyp.base.p * hyp.base.q : ℕ) : ℝ) / (Mdata.k : ℝ) ≤ rhoNormSq
  /-- **(7.5) + (14.11.3) + §8 TI-counting** upper bound (loosened to the `normCascadeBound`
  error terms). -/
  upper :
    rhoNormSq ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
      + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §7 Dade producer for (14.11.4).**  The `ρ`-norm is the concrete family-inequality
norm `(toFamilyHypothesis71).chiRhoNormSq (ψ^{τ₁}) 0` for the `(M, A(M))` map `ρ`.

* `lower` is **proven** (`MHypothesis.rhoNormSq_ge_lower`): the (7.8.b) coherence-norm lower bound
  `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²` (via the `h78` carrier and the bridge `chiRhoNormSq_eq_zetaNuRhoNormSq`).
* `upper` is the remaining genuine obligation: the **§8 TI-counting** of the `(W#)^G`/`(P#)^G`/
  `(Q#)^G` orbit contributions that turns the line-83 bound (`chiRhoNormSq_psi_le_line83`, proven)
  into the raw estimate, which `normCascade_upper_loosen` (proven) then loosens to the displayed
  `normCascadeBound` error terms.  Both arithmetic ends of `upper` are honest; the gap is the §8
  orbit cardinality `|K#|/|M|`, `|(W#)^G|`/`|(P#)^G|`/`|(Q#)^G|` count. -/
noncomputable def normCascadeData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    NormCascadeData hyp Mdata where
  rhoNormSq := (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
  lower := Mdata.rhoNormSq_ge_lower
  -- line-83 (`chiRhoNormSq_psi_le_line83`, proven) chained with the §8 TI-counting step
  -- (`line83_le_displayed_upper`, the single remaining gate).
  upper := le_trans (Mdata.chiRhoNormSq_psi_le_line83 _hG hne) (Mdata.line83_le_displayed_upper _hG)

/-- **Peterfalvi (14.11.4)**: the character-theoretic norm calculation produces the displayed
rational inequality `normCascadeBound hyp k`.

De-opacified (W4 §16→§7 bridge, lane-h): the genuine character theory is the two-sided `ρ`-norm
bound `NormCascadeData` (the (7.5) family inequality + (14.11.3)/(7.8.b) norm estimates); the
passage to `normCascadeBound` is then the pure rational rearrangement
`1 − pq/k ≤ ‖ψ^{τ₁ρ}‖² ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` ⟹
`1/p + 1/q ≤ pq/k + 2/(pq) + 1/(uq) + 1/(vp)` (`linarith`).  Everything downstream of
`normCascadeBound` is the arithmetic cascade already discharged in `norm_cascade_contradiction`. -/
theorem normCascadeBound_of_charData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    normCascadeBound hyp Mdata.k := by
  obtain ⟨R, hlower, hupper⟩ := normCascadeData _hG hyp Mdata hne
  unfold normCascadeBound
  -- The two-sided `ℝ` bound `1 − pq/k ≤ R ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` gives the
  -- displayed rational inequality; lift the `ℚ` goal to `ℝ` and close by `linarith`.
  rw [← Rat.cast_le (K := ℝ)]
  push_cast at hlower hupper ⊢
  linarith [hlower, hupper]

/-- **Peterfalvi (14.11.4)**: the norm inequality cascade contradicts `K != V`.

This is now a transparent composition rather than an opaque obligation: the
case-(9.7.b) outputs of `caseB_for_T` (14.4) and `caseB_for_S` (14.6) supply the
T-side/S-side cyclotomic size data, `main_size_bounds` (14.11.1) supplies
`k > 2 p v`, and `normCascadeBound_of_charData` (14.11.2)--(14.11.3) supplies the
displayed norm inequality.  The arithmetic consumer
`norm_cascade_contradiction_of_caseB_outputs_main_size_bounds` then closes the
cascade.  The only remaining genuine `sorry`s are the named producers above. -/
theorem contradiction_of_K_ne_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    False :=
  norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata) Mdata
    (main_size_bounds _hG hyp Mdata hne)
    (normCascadeBound_of_charData _hG hyp Mdata hne)

/-- **Peterfalvi (14.11)**: `K = V` and `|M : K| = p q`.

The `K = V` half is now a genuine consequence of the (14.11.1)--(14.11.4)
contradiction: assuming `K ≠ V` invokes `contradiction_of_K_ne_V`.  The index
computation `|M : K| = p q` (here `Mdata.e = p q`) is the remaining genuine
obligation; note `betaM_expansion`'s `e = p q` is unavailable here because it
is conditioned on `K ≠ V`, so the equal-index value under `K = V` needs the
type-I structure of `M` directly. -/
theorem K_eq_V_index_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by
  refine ⟨?_, ?_⟩
  · -- (14.11.1)--(14.11.4): `K ≠ V` is contradictory.
    by_contra hne
    exact contradiction_of_K_ne_V _hG hyp Ldata Mdata hne
  · -- `|M : K| = p q` from the type-I structure of `M`, carried by `MHypothesis`
    -- (V-side dual of `LHypothesis.typeI_complement_card_eq_pq`).
    exact Mdata.complement_card_eq_pq

end OddOrder.Peterfalvi.S16
