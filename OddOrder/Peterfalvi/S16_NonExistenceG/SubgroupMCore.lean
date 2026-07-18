import OddOrder.Peterfalvi.S16_PairingBessel
import OddOrder.Peterfalvi.S16_NonExistenceG.CoherentEtaOrthogonality
import OddOrder.Peterfalvi.S16_NonExistenceG.CoherentProjectionRigidity
import OddOrder.Peterfalvi.S16_NonExistenceG.KeyInequality

/-!
# Peterfalvi (14.10)-(14.11) — the `M`-carrier and the norm-cascade/parity groundwork

The `MHypothesis` carrier of Peterfalvi (14.10) with the (14.11.1)-(14.11.3) numeric layer:
the norm-cascade arithmetic, `main_size_bounds`, the `±1`-rigidity basis
(`all_pm_one_and_card_of_odd_sq_sum_le`, `one_le_norm_signed_paired_sum`, `finNeg`), and the
`β_M` expansion data.  Prefix-split from `SubgroupM.lean` (2000-line limit); the Frobenius-kernel
and field-model layer stays in `OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupM`.
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
  /-- The minimal odd-order counterexample fixed throughout §14.  Retaining this proof lets the
  coherent bundle expose its canonical `Hypothesis78` without erasing the proof argument used in
  that construction. -/
  hG : OddOrder.BG.IsMinimalSimpleOdd G
  /-- **Peterfalvi (5)--(8)/(12.1) for `M`**: the complete constructible type-I coherence bundle:
  the Dade setup, Frobenius complement, coherent extension, and placed induced family.  Earlier
  versions kept only the derived raw `Hypothesis78`, losing the family/coherence pins needed by
  (13.19) and (14.11.2).  This is upstream proof data, not a conclusion of (14.11). -/
  coherent78 : TypeICoherent78Data M
  e : ℕ
  k : ℕ
  /-- **Peterfalvi (14.10)**: `e = |M : K|` (the degree of `ψ`).  De-opacified from the former
  opaque `Prop` to the concrete index identity (lane-c §16 char-endpoint, carrier honesty). -/
  e_eq_index : e = (K.subgroupOf M).index
  /-- **Peterfalvi (13.17.c), V-side dual**: the faithful complement-index alternatives
  `e = p` or `e = p q`.  This is upstream input to (14.11), not either of its conclusions. -/
  complementIndex_cases : e = hyp.base.p ∨ e = hyp.base.p * hyp.base.q
  k_eq_card_K : k = Nat.card ↥K
  G0 : Set G
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: `G₀ ⊆ G − Ã(M)`.  The (14.11.3) set
  `G₀ = G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]` lies inside the family `(7.4)` support complement
  `famG₀ = (toFamilyHypothesis71).G0 = G − Ã(M)`, since every `g ∈ G₀` is off the Dade support
  `Ã(M)` of `A(M)` (`typeIHyp.dadeData.dade.dadeSupport`).  This is the inclusion `G₀ ⊆ famG₀`
  used to drop the `G₀`-part of the (7.5) sum in (14.11.4). -/
  G0_off_dadeSupport : ∀ g ∈ G0, g ∉ coherent78.typeIHyp.dadeData.dade.dadeSupport
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: the complement of `G₀` is covered by the Dade support
  `Ã(M)` and the three orbits `(W − (W₁∪W₂))^G`, `(P#)^G`, `(Q#)^G`.  Concretely, `G₀` is the
  (14.11.3) set `G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`, so any `g` off `Ã(M)` and off `G₀`
  lies in the orbit union.  This is the §8 TI-counting input: `famG₀ ∖ G₀ ⊆ orbits` lets the
  `(7.5)` `G₀`-drop in line 83 (`chiRhoNormSq_psi_le_line83`) be bounded by the orbit cardinalities
  (the genuine §8 structural fact, supplied from the partner type-`P` structure). -/
  G0_orbit_cover : ∀ g : G, g ∉ coherent78.typeIHyp.dadeData.dade.dadeSupport → g ∉ G0 →
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
namespace MHypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

/-- The type-I Dade setup retained inside the complete coherent bundle. -/
abbrev typeIHyp [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    OddOrder.Peterfalvi.S14.Hypothesis Mdata.M := Mdata.coherent78.typeIHyp

/-- The canonical §7.8 datum derived from the retained coherent bundle. -/
noncomputable abbrev h78 [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    OddOrder.Peterfalvi.S09.Hypothesis78 G
      (OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) Mdata.M :=
  Mdata.coherent78.h78 Mdata.hG

/-- Peterfalvi's coherent source family `𝓜`. -/
noncomputable abbrev Mset [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Set (ClassFunction ↥Mdata.M ℂ) := Mdata.typeIHyp.Sset

/-- The Dade isometry `τ` on the type-I source. -/
noncomputable abbrev tau [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥Mdata.M G := Mdata.typeIHyp.tau

/-- The coherent extension `τ₁`; unlike `τ`, it is defined on every member of `𝓜`. -/
noncomputable abbrev tau1 [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥Mdata.M G := Mdata.coherent78.coh.extension

/-- The placed distinguished member `ψ = ζ₀` of degree `[M : K]`. -/
noncomputable abbrev psi [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    ClassFunction ↥Mdata.M ℂ := Mdata.coherent78.zeta 0

/-- `β_M^τ`, the canonical §7.8 Dade image attached to the retained coherent bundle. -/
noncomputable abbrev betaM [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    ClassFunction G ℂ := Mdata.h78.beta

/-- The distinguished member belongs to the coherent source family. -/
theorem psi_mem [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.psi ∈ Mdata.Mset := by
  exact Mdata.coherent78.zeta_mem_Sset (Ne.symm Mdata.coherent78.ind1H_ne_zero)

/-- The distinguished member has degree `e = [M : K]`. -/
theorem psi_degree_eq_e [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) : Mdata.psi 1 = (Mdata.e : ℂ) := by
  have hK : Mdata.K = Mdata.coherent78.kernel := by
    calc
      Mdata.K = maxNilpotentNormalHall Mdata.M := Mdata.K_eq_MF
      _ = Mdata.coherent78.kernel := Mdata.typeIHyp.typeI.typeF.H_eq.symm
  have hidx : Mdata.coherent78.kernelIn.index =
      (Mdata.K.subgroupOf Mdata.M).index := by
    change (Mdata.coherent78.kernel.subgroupOf Mdata.M).index =
      (Mdata.K.subgroupOf Mdata.M).index
    rw [← hK]
  calc
    Mdata.psi 1 = (Mdata.coherent78.kernelIn.index : ℂ) := Mdata.coherent78.deg0
    _ = (Mdata.e : ℂ) := by rw [hidx, ← Mdata.e_eq_index]

@[simp] theorem betaM_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.betaM = Mdata.h78.beta := rfl

/-- The canonical `β_M` is the Dade image of `Ind_K^M 1_K - ψ`. -/
theorem betaM_eq_tau_induce_sub_psi [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    Mdata.betaM = Mdata.tau
      (ClassFunction.induce (Mdata.K.subgroupOf Mdata.M)
        (trivialClassFunction ↥(Mdata.K.subgroupOf Mdata.M)) - Mdata.psi) := by
  rw [Mdata.K_eq_MF, ← Mdata.typeIHyp.typeI.typeF.H_eq]
  rw [Mdata.betaM_eq, OddOrder.Peterfalvi.S09.Hypothesis78.beta_def]
  change Mdata.typeIHyp.toHypothesis71.τ _ = Mdata.typeIHyp.tau _
  rw [Mdata.typeIHyp.toHypothesis71_tau_apply]
  apply congrArg Mdata.typeIHyp.tau
  change Mdata.h78.hyp76.zeta Mdata.h78.ind1H -
      Mdata.h78.hyp76.zeta Mdata.h78.zetaDistinct = _
  rw [Mdata.coherent78.h78_ind1H_eq Mdata.hG,
    Mdata.coherent78.h78_zeta_eq Mdata.hG,
    Mdata.coherent78.h78_zetaDistinct_eq Mdata.hG,
    Mdata.coherent78.h78_zeta_eq Mdata.hG]
  change ClassFunction.induce Mdata.coherent78.kernelIn
      (Mdata.coherent78.θ Mdata.coherent78.ind1H : ClassFunction _ ℂ) -
        Mdata.coherent78.zeta 0 = _
  rw [Mdata.coherent78.triv,
    IrreducibleCharacter.coe_trivialIrreducibleCharacter]

@[simp] theorem psi_tau1_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.tau1 Mdata.psi =
      Mdata.h78.nu (Mdata.h78.hyp76.zeta Mdata.h78.zetaDistinct) := rfl

@[simp] theorem h78_hyp_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.h78.hyp76.hyp71.hyp = Mdata.typeIHyp.dadeData.dade :=
  Mdata.coherent78.h78_hyp_eq Mdata.hG

theorem h78_H_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.h78.hyp76.H = Mdata.K := by
  calc Mdata.h78.hyp76.H = Mdata.coherent78.kernel :=
        Mdata.coherent78.h78_H_eq Mdata.hG
    _ = maxNilpotentNormalHall Mdata.M := Mdata.typeIHyp.typeI.typeF.H_eq
    _ = Mdata.K := Mdata.K_eq_MF.symm

/-- The complement index of the canonical (7.8) bundle is the concrete index `e = |M : K|`
carried by `MHypothesis`. -/
theorem h78_complementIndex_eq_e [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) : Mdata.h78.complementIndex = Mdata.e := by
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  have hko : Mdata.h78.kernelOrder = Mdata.k := by
    rw [Mdata.k_eq_card_K]
    change Nat.card ↥(Mdata.h78.hyp76.H) = Nat.card ↥Mdata.K
    rw [Mdata.h78_H_eq]
  have hmul := Mdata.h78.kernelOrder_mul_complementIndex_eq_card_L
  rw [hko, Mdata.k_eq_card_K] at hmul
  have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
    rw [← hcardK]
    exact Subgroup.card_mul_index _
  rw [← Mdata.e_eq_index] at hidx
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hmul.trans hidx.symm)

theorem psi_tau1_norm_one [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    ClassFunction.inner (Mdata.tau1 Mdata.psi) (Mdata.tau1 Mdata.psi) = 1 := by
  simpa using Mdata.coherent78.nu_zeta_norm_one Mdata.hG
    (i := Mdata.h78.zetaDistinct) Mdata.h78.zetaDistinct_ne_ind1H

theorem h78_zetaNuRho_normSq_ge [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    1 - (Mdata.h78.complementIndex : ℝ) / (Mdata.h78.kernelOrder : ℝ) ≤
      Mdata.h78.zetaNuRhoNormSq :=
  (Mdata.coherent78.normEstimates Mdata.hG).zetaNuRho_norm_sq_ge
    (Mdata.coherent78.smallIndex Mdata.hG)

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
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
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
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
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
  change ((a' * ⟨u, hmemL⟩ * a'⁻¹ : ↥L) : G) = ((⟨u, hmemL⟩ : ↥L) : G)
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
(`k > 2 p v`) and `(k − 1) / e > (v − 1) / p`.  The strict quotient bound is a genuine
consequence of `k > 2 p v`, `e ≤ p q`, and `q < p`: cross multiplication reduces it to
`e(v−1) ≤ pq(v−1) < p(k−1)`.  The `k > 2 p v` bound is in turn
the arithmetic consequence (`two_mul_add_one_le_of_modEq_one_odd`) of the §13/§15 structural datum
`hstruct` of (14.11.1): by (13.17) the kernel order factors as `k = v·x` with `x` an integer,
`x ≠ 1`
(as `K ≠ V`), and `x ≡ 1 (mod p)` (since `W₂` acts fixed-point-freely on `K` and `V`); as `k = |K|`
is odd, `x` is odd, so `x ≥ 2p+1` and `k = vx > 2pv`.  The third inequality of (14.11.1),
`(v − 1) / p > (u − 1) / q`, is `key_ratio_inequality_of_caseB_data` (14.8), discharged in
`main_size_bounds`. -/
theorem main_size_bounds_structural [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V)
    (he_le : Mdata.e ≤ hyp.base.p * hyp.base.q) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) := by
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  -- (14.11.1): `k = v·x`, `x ≡ 1 (mod p)` (`W₂` fixed-point-free on `K`, `V`), `x ≠ 1` (`K ≠ V`) —
  -- the §13/§15 structural datum (13.17); `k > 2 p v` is then arithmetic (`x` odd, so `x ≥ 2p+1`).
  have hstruct : ∃ x : ℕ, Mdata.k = hyp.base.v * x ∧ x ≡ 1 [MOD hyp.base.p] ∧ x ≠ 1 := by
    have hMI : IsTypeI Mdata.M := ⟨Mdata.typeIHyp.typeI⟩
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
    -- **(13.17)/(14.11.1)**: `V ≤ K = M_F` (type-I-over-`N_G(V)` Fitting inclusion).
    have hVK : hyp.base.V ≤ Mdata.K := by
      rw [Mdata.K_eq_MF]
      exact OddOrder.Peterfalvi.S15.typeI_overNormalizer_V_le_fitting _hG hnoV hyp.base hTII
        Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    -- `|V| = v` (`d = 1` from `D = V ⊓ C_G(Q) = ⊥`, (13.12) dual).
    have hVcard : Nat.card ↥hyp.base.V = hyp.base.v := by
      have hDbot : hyp.base.D = ⊥ := by
        rw [hyp.base.D_eq]
        exact hyp.V_inf_centralizer_Q_eq_bot _hG
      have hd1 : hyp.base.d = 1 := by rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
      rw [hyp.base.card_V_eq_vd, hd1, mul_one]
    -- `v ∣ k` from `V ≤ K`; set `x = k / v`.
    have hvdvdk : hyp.base.v ∣ Mdata.k := by
      rw [Mdata.k_eq_card_K, ← hVcard]
      exact Subgroup.card_dvd_of_le hVK
    obtain ⟨x, hkx⟩ := hvdvdk
    -- **(13.17)**: type-I Frobenius data with `W₂ ≤ complement`, so `W₂` acts fpf on `K = M_F`.
    obtain ⟨frob, _hker, hW2E⟩ := OddOrder.Peterfalvi.S15.exists_typeIFrobeniusData_W2_le
      _hG hnoV hyp.base Mdata.M_maximal hMI Mdata.normalizer_V_le_M
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
  -- The strict quotient bound `(k−1)/e > (v−1)/p` is pure arithmetic from `k > 2pv`, `q < p`,
  -- and the faithful (13.17.c)-dual bound `e ≤ pq`:
  -- `e(v−1) ≤ pq(v−1) = p·q(v−1) ≤ p(k−1)`.
  have hv_pos : 0 < hyp.base.v := by
    obtain ⟨x, hkx, _, _⟩ := hstruct
    have hk_odd : Odd Mdata.k := by
      rw [Mdata.k_eq_card_K]
      exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Mdata.K)
    have hvx_odd : Odd (hyp.base.v * x) := hkx ▸ hk_odd
    exact (Nat.odd_mul.mp hvx_odd).1.pos
  have hNat : hyp.base.q * (hyp.base.v - 1) < Mdata.k - 1 := by
    have hb : 2 * hyp.base.p * hyp.base.v ≤ Mdata.k - 1 := Nat.le_sub_one_of_lt hk
    have ha : hyp.base.q * (hyp.base.v - 1) < 2 * hyp.base.p * hyp.base.v := by
      calc hyp.base.q * (hyp.base.v - 1) ≤ hyp.base.q * hyp.base.v := by gcongr; omega
        _ < 2 * hyp.base.p * hyp.base.v := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) hv_pos
    exact lt_of_lt_of_le ha hb
  rw [gt_iff_lt]
  have hppos : (0 : ℚ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have heposNat : 0 < Mdata.e := by
    rw [Mdata.e_eq_index]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hepos : (0 : ℚ) < Mdata.e := by exact_mod_cast heposNat
  rw [div_lt_div_iff₀ hppos hepos]
  have hcross :
      (hyp.base.v - 1) * Mdata.e < (Mdata.k - 1) * hyp.base.p := by
    calc
      (hyp.base.v - 1) * Mdata.e
          ≤ (hyp.base.v - 1) * (hyp.base.p * hyp.base.q) := by gcongr
      _ = hyp.base.p * (hyp.base.q * (hyp.base.v - 1)) := by ring
      _ < hyp.base.p * (Mdata.k - 1) := by
        exact Nat.mul_lt_mul_of_pos_left hNat hyp.base.p_prime.pos
      _ = (Mdata.k - 1) * hyp.base.p := by ring
  exact_mod_cast hcross

/-- **Peterfalvi (13.17.c), V-side dual complement alternatives**:
`e = |M : K| = p` or `e = p q`.

The alternatives are supplied by lane b's corrected `exists_M_structural_dichotomy` and stored
faithfully on the (14.10) witness. -/
theorem MHypothesis.complementIndex_eq_p_or_pq [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    Mdata.e = hyp.base.p ∨ Mdata.e = hyp.base.p * hyp.base.q := by
  exact Mdata.complementIndex_cases

/-- **Peterfalvi (13.17.c), V-side dual input for (14.11.1)**:
`e = |M : K| ≤ p q`, without choosing the `p q` branch. -/
theorem MHypothesis.complementIndex_le_pq [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    Mdata.e ≤ hyp.base.p * hyp.base.q := by
  rcases Mdata.complementIndex_eq_p_or_pq _hG with he | he
  · rw [he]
    exact Nat.le_mul_of_pos_right _ hyp.base.q_prime.pos
  · exact he.le

/-- **Peterfalvi (14.11.1)**: if `K != V`, then `k` is large and the first quotient is
strictly greater than `(v - 1) / p`.

The third conjunct `(v − 1) / p > (u − 1) / q` is now a genuine proof: it is the arithmetic
ratio comparison `key_ratio_inequality_of_caseB_data` (14.8), fed by the (14.4)/(14.6) case-(9.7.b)
cyclotomic data.  The two structural bounds remain the named §13/§14 obligation
`main_size_bounds_structural`. -/
theorem main_size_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hnoV hncH0C hyp
  obtain ⟨Tdata, _⟩ := caseB_for_T _hG hyp
  obtain ⟨Sdata, _⟩ := caseB_for_S _hG hyp Ldata
  obtain ⟨hk, hke⟩ :=
    main_size_bounds_structural _hG hnoV hncH0C hyp Mdata hne (Mdata.complementIndex_le_pq _hG)
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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), M-side bound-or-parity alternatives.**

This is the projection of each textbook (13.19.c) conjunction needed by (14.11.2): either the
corresponding degree bound holds, or the actual coefficient of `β_M^τ` on the non-principal zero
axis is an odd integer.  No parity branch is selected inside the carrier. -/
structure BetaMGridParityAlternatives [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  row :
    ((((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≤
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) ∨
      ∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j))
  col :
    ((((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≤
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∨
      ∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
          (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19), synchronized M-side grid source.**

The explicit `TypeIOrthogonalityGridData` producer
`typeIOrthogonalityGridData_of_coherent78_of_c_eq_one_and_d_eq_one`
(Pf (13.19), landed 2026-07-12) now fixes the family `Lset := dataL.typeIHyp.Sset` and chooses the
distinguished degree-`e` member via `exists_Sset_apply_one_eq_index`, so its `phi_mem` **is** the
required `phi ∈ typeIHyp.Sset` membership.  This theorem therefore just instantiates that producer
at `Mdata.coherent78` (using the symmetric non-type-I carrier for its T-side inputs) and
projects the chosen member's membership; no false uniqueness of the two class functions is
required. -/
theorem exists_betaMGridData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (_hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    ∃ grid : OddOrder.Peterfalvi.S15.TypeIOrthogonalityGridData hyp.base Mdata.coherent78,
      grid.phi ∈ Mdata.typeIHyp.Sset := by
  -- The faithful explicit (13.19) producer now fixes
  -- `Lset := dataL.typeIHyp.Sset` with `phi := choose (exists_Sset_apply_one_eq_index …)`, so the
  -- chosen member is *in* `Sset` by construction.  The producer uses the symmetric
  -- non-type-I carrier for its T-side type-`P` and commutativity inputs.
  have hc1 : hyp.base.c = 1 :=
    hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply
  have hDbot : hyp.base.D = ⊥ := (T_side_caseB_facts _hG hyp).1
  have hd1 : hyp.base.d = 1 := by
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  exact ⟨OddOrder.Peterfalvi.S15.typeIOrthogonalityGridData_of_coherent78_of_c_eq_one_and_d_eq_one
      _hG hnoV hyp.base hc1 hd1 Mdata.coherent78 (pins := hyp.nuGridSupply),
    (Classical.choose_spec (OddOrder.Peterfalvi.S15.exists_Sset_apply_one_eq_index _hG hnoV
      Mdata.coherent78.typeIHyp)).1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), faithful M-side source adapter.**  Projects the corrected conjunction
alternatives supplied by lane b.  The choice-invariance theorem identifies the `eta` coefficients
of its `β_L^τ` with those of the actual `Mdata.betaM`; it does not overclaim equality of the two
class functions. -/
theorem betaMGridParityAlternatives [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    BetaMGridParityAlternatives hyp Mdata := by
  obtain ⟨grid, hphi⟩ := exists_betaMGridData _hG hnoV hncH0C hyp Mdata
  have hbeta : Mdata.betaM =
      OrthogonalitySwitchData.coherentBeta _hG Mdata.coherent78 := rfl
  have hcoeff : ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner grid.betaL (hyp.base.eta i j) =
          ClassFunction.inner Mdata.betaM (hyp.base.eta i j) := by
    intro _ _ i j
    rw [hbeta]
    exact OrthogonalitySwitchData.typeIGrid_betaL_inner_eta_eq_h78_beta
      _hG hnoV hncH0C Mdata.M_maximal Mdata.coherent78 grid hphi i j
  have heM : Mdata.e = ((maxNilpotentNormalHall Mdata.M).subgroupOf Mdata.M).index := by
    rw [Mdata.e_eq_index, Mdata.K_eq_MF]
  have he : grid.e = Mdata.e := grid.e_eq_index.symm.trans heM.symm
  have hH : Mdata.typeIHyp.H = Mdata.K := by
    rw [OddOrder.Peterfalvi.S14.Hypothesis.H, Mdata.typeIHyp.typeI.typeF.H_eq,
      Mdata.K_eq_MF]
  have hk : Nat.card ↥Mdata.typeIHyp.H = Mdata.k := by
    rw [hH, ← Mdata.k_eq_card_K]
  constructor
  · rcases grid.caseC with hbound | hodd
    · left
      have h := hbound.2
      rw [hk, he] at h
      exact h
    · right
      intro j hj
      obtain ⟨n, hn, hinner⟩ := hodd.1 j hj
      refine ⟨n, hn, ?_⟩
      intro _ _
      calc
        ClassFunction.inner Mdata.betaM
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) =
            ClassFunction.inner grid.betaL
              (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) :=
          (hcoeff ⟨0, hyp.base.q_prime.pos⟩ j).symm
        _ = (n : ℂ) := hinner
  · rcases grid.caseC_dual with hbound | hodd
    · left
      have h := hbound.2
      rw [hk, he] at h
      exact h
    · right
      intro i hi
      obtain ⟨n, hn, hinner⟩ := hodd.1 i hi
      refine ⟨n, hn, ?_⟩
      intro _ _
      calc
        ClassFunction.inner Mdata.betaM
            (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) =
            ClassFunction.inner grid.betaL
              (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) :=
          (hcoeff i ⟨0, hyp.base.p_prime.pos⟩).symm
        _ = (n : ℂ) := hinner

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.1) → (13.19.c)**: the two strict size gaps exclude both degree-bound
branches of (13.19.c), so the row and column coefficients of the actual `β_M^τ` are odd. -/
theorem betaM_axis_odd_of_main_size_bounds [Finite G]
    {hyp : Hypothesis (G := G)} {Mdata : MHypothesis hyp}
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (h1319 : BetaMGridParityAlternatives hyp Mdata) :
    (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
    (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  constructor
  · rcases h1319.row with hbound | hodd
    · exfalso
      linarith [hsize.2.1, hsize.2.2]
    · exact hodd
  · rcases h1319.col with hbound | hodd
    · exfalso
      linarith [hsize.2.1]
    · exact hodd

/-- **Faithful §7/§3 Dade carrier for the `β_M` expansion of Peterfalvi (14.11.2).**

This is the `M`-instance of the (7.8) Dade-coherence decomposition specialised to the `η`-grid,
isolating the genuine character-theoretic content of (14.11.2) away from the pure algebra:

* `betaM_seven_eight` — **Peterfalvi (7.8.a)** for `M`: `β_M^τ = 1_G − χ + Δ`, the Dade-isometry
  image of `β_M = Ind_K^M 1_K − ψ` decomposed against the principal character `1_G` and the removed
  unit-norm coherent image `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`, recorded by `chi_classification`;
  `chi_norm` is its branch-independent consequence).  In the `χ = ψ^{τ₁} = ζ^ν` branch this is the
  `M`-instance
  of `S09.Hypothesis78.beta_eq_constOne_sub_zetaImage_add_delta` (`β = 1_G − ζ^ν + Δ`); see the
  bridge lemma `betaMExpansionData_of_hypothesis78` below.
* `grid_eq` — **Peterfalvi (13.1.d)/(7.8.b)** `η`-grid identification: `1_G + Δ = Σ_{ij} ε_ij η_ij`.
  The principal `η₀₀` carries the `1_G`, the off-principal grid realizes the residual `Δ`, and the
  `±1` signs come from the Dade congruence `a_ij ≡ 1 (mod 2)` (13.19.c / 7.8.c) with
  `Σ a_ij² ≤ e − 1` and `e = p q` (`all_pm_one_and_card_of_odd_sq_sum_le`).

All fields are the conditional conclusion of the (14.11.2) support-coherence argument: besides
the §3/§4/§5 Dade machinery it uses coefficient projection, norm tightness, and residual
vanishing.  Cf. `EtaGenericData` for the dual generic-set carrier. -/
structure BetaMExpansionData [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- The equality `e = p q`, obtained in the same norm-collapse as the signed expansion. -/
  e_eq_pq : Mdata.e = hyp.base.p * hyp.base.q
  /-- The residual `Δ` of the (7.8.a) Dade expansion `β_M = 1_G − χ + Δ`. -/
  delta : ClassFunction G ℂ
  /-- The removed unit-norm character `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`). -/
  chi : ClassFunction G ℂ
  /-- `χ` has the same pointwise absolute value as `ψ^{τ₁}` (holds for both branches, since
  `|z| = |z̄|`) — exactly what (14.11.3) consumes. -/
  chi_norm : ∀ g : G, ‖chi g‖ = ‖(Mdata.tau1 Mdata.psi) g‖
  /-- **Peterfalvi (14.11.2)**: the removed character is the coherent image of `ψ`, or the
  negative coherent image of its complex conjugate. -/
  chi_classification :
    chi = Mdata.tau1 Mdata.psi ∨ chi = -(Mdata.tau1 Mdata.psi.conj)
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
/-- **Faithful conditional support-coherence producer for (14.11.2).**  Under `K ≠ V`, the
coefficient projection and norm-tightness argument derives `e = p q`, vanishing of the orthogonal
residual, the signed `η`-grid expansion, and the classification of `χ`.  The bridge lemma
`betaMExpansionData_of_hypothesis78` supplies its concrete (7.8.a) branch. -/
noncomputable def betaM_expansion_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (_hne : Mdata.K ≠ hyp.base.V)
    (_he_le : Mdata.e ≤ hyp.base.p * hyp.base.q)
    (_hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (_hrow : ∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j))
    (_hcol : ∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) :
    BetaMExpansionData hyp Mdata := by
  classical
  haveI := Mdata.coherent78.kernelIn_normal
  set H78 := Mdata.h78 with hH78
  set BD := Mdata.coherent78.betaDecomp Mdata.hG with hBD
  -- The Fourier coefficients of `β_M` on the `η`-grid are integers.
  have hbetaZ : Mdata.betaM ∈ ZIrr G := by
    exact H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (Mdata.coherent78.h78_ind_mem_ZIrr Mdata.hG)
      (Mdata.coherent78.h78_zeta_irreducible Mdata.hG)
  have hint : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ n : ℤ, ClassFunction.inner Mdata.betaM (hyp.base.eta i j) = (n : ℂ) :=
    fun i j => ClassFunction.inner_mem_ZIrr_int hbetaZ (eta_mem_ZIrr hyp.base i j)
  choose m hcoeff using hint
  -- Every coherent family image, hence also the weighted sum, is orthogonal to the grid.
  have hDadeAvoid :=
    OrthogonalitySwitchData.mSide_dadeSupport_avoids_regular
      (hyp := hyp) Mdata.hG hnoV hncH0C Mdata.M_maximal Mdata.coherent78
  have hetaNu : ∀ (k : Fin (Mdata.coherent78.n + 1)), k ≠ H78.ind1H →
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner (H78.nu (H78.hyp76.zeta k)) (hyp.base.eta i j) = 0 := by
    intro k hk i j
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      OrthogonalitySwitchData.caseB_eta_orthogonal_nu_zeta_at
        Mdata.hG hyp.base Mdata.coherent78 hDadeAvoid hk i j,
      star_zero]
  have hWeta : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner H78.weightedNuSum (hyp.base.eta i j) = 0 := by
    intro i j
    rw [show H78.weightedNuSum =
        ∑ k ∈ (Finset.univ.erase H78.ind1H),
          (H78.hyp76.zeta k (1 : ↥Mdata.M) /
            (H78.hyp76.zeta H78.zetaDistinct (1 : ↥Mdata.M) *
              ClassFunction.inner (H78.hyp76.zeta k) (H78.hyp76.zeta k))) •
            H78.nu (H78.hyp76.zeta k) from rfl]
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ClassFunction.inner_smul_left, hetaNu k (Finset.mem_erase.mp hk).1 i j, mul_zero]
  -- Consequently the grid projection of `β_M` is the projection of `1_G + Γ`.
  set phi : ClassFunction G ℂ :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma with hphi
  have hphi_coeff : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner phi (hyp.base.eta i j) = (m i j : ℂ) := by
    intro i j
    rw [← hcoeff i j, hphi,
      show Mdata.betaM = H78.beta by rw [hH78],
      show H78.beta = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          + (BD.a : ℂ) • H78.weightedNuSum + BD.Gamma from BD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hetaNu H78.zetaDistinct H78.zetaDistinct_ne_ind1H i j, hWeta i j, mul_zero,
      sub_zero, add_zero]
  -- The principal coefficient is one.
  have heta0 : hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    rw [eta_principal_eq_trivial hyp.base]
    exact ClassFunction.ext fun _ => rfl
  have hprincipalInner : ClassFunction.inner Mdata.betaM
      (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) = 1 := by
    rw [heta0, show Mdata.betaM = H78.beta by rw [hH78],
      H78.beta_eq_constOne_sub_zetaImage_add_delta,
      ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
      BD.orth_one H78.zetaDistinct H78.zetaDistinct_ne_ind1H,
      H78.delta_orth_one BD]
    ring
  have hprincipal : m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    have hm := hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩
    have hc : ((m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ : ℤ) : ℂ) = 1 :=
      hm.symm.trans hprincipalInner
    exact_mod_cast hc
  -- Support avoidance gives the four-corner relation (3.7).
  have hbetaVanish : ∀ x ∈ conjClassSet
      ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      Mdata.betaM x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx
      (H78.beta_support_subset_dadeSupport (ClassFunction.mem_support.mpr hval))
  have hrelation : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      m i j + m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
        m i ⟨0, hyp.base.p_prime.pos⟩ + m ⟨0, hyp.base.q_prime.pos⟩ j := by
    intro i j
    have h := inner_eta_grid_relation hyp.base hbetaVanish i j
    rw [hcoeff i j,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff i ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ j] at h
    exact_mod_cast h
  -- The selected (13.19.c) alternatives make the two non-principal axes odd.
  have hrow : ∀ j, j ≠ ⟨0, hyp.base.p_prime.pos⟩ →
      Odd (m ⟨0, hyp.base.q_prime.pos⟩ j) := by
    intro j hj
    have hjnat : (j : ℕ) ≠ 0 := by
      intro hj0
      apply hj
      apply Fin.ext
      exact hj0
    obtain ⟨n, hnodd, hn⟩ := _hrow j hjnat
    have hnval : ClassFunction.inner Mdata.betaM
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) = (n : ℂ) := hn
    have hcast : ((m ⟨0, hyp.base.q_prime.pos⟩ j : ℤ) : ℂ) = (n : ℂ) :=
      (hcoeff ⟨0, hyp.base.q_prime.pos⟩ j).symm.trans hnval
    have hmn : m ⟨0, hyp.base.q_prime.pos⟩ j = n := by exact_mod_cast hcast
    rwa [hmn]
  have hcol : ∀ i, i ≠ ⟨0, hyp.base.q_prime.pos⟩ →
      Odd (m i ⟨0, hyp.base.p_prime.pos⟩) := by
    intro i hi
    have hinat : (i : ℕ) ≠ 0 := by
      intro hi0
      apply hi
      apply Fin.ext
      exact hi0
    obtain ⟨n, hnodd, hn⟩ := _hcol i hinat
    have hnval : ClassFunction.inner Mdata.betaM
        (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) = (n : ℂ) := hn
    have hcast : ((m i ⟨0, hyp.base.p_prime.pos⟩ : ℤ) : ℂ) = (n : ℂ) :=
      (hcoeff i ⟨0, hyp.base.p_prime.pos⟩).symm.trans hnval
    have hmn : m i ⟨0, hyp.base.p_prime.pos⟩ = n := by exact_mod_cast hcast
    rwa [hmn]
  have hecomp : H78.complementIndex = Mdata.e := by
    rw [hH78]
    exact Mdata.h78_complementIndex_eq_e
  obtain ⟨hepqH, hpm, hgrid⟩ :=
    Mdata.coherent78.etaGrid_projection_rigidity Mdata.hG hyp.base m
      (by simpa [phi, BD] using hphi_coeff) hprincipal hrelation hrow hcol (by
        rw [hecomp]
        exact _he_le)
  have hepq : Mdata.e = hyp.base.p * hyp.base.q := by
    rw [← hecomp]
    exact hepqH
  set X : ClassFunction G ℂ := etaGridProjection hyp.base m with hX
  set chi : ClassFunction G ℂ := X - Mdata.betaM with hchi
  have hchiSelf : ClassFunction.inner chi chi = 1 := by
    rw [hchi, hX, show Mdata.betaM = H78.beta by rw [hH78]]
    exact Mdata.coherent78.etaGrid_projection_sub_beta_norm_one Mdata.hG hyp.base m
      hpm hepqH (by simpa [hH78] using hcoeff)
  have hetaNuData : ∀ (k : Fin (Mdata.coherent78.n + 1)),
      k ≠ Mdata.coherent78.ind1H → ∀ i j,
        ClassFunction.inner
          ((Mdata.coherent78.h78 Mdata.hG).nu
            ((Mdata.coherent78.h78 Mdata.hG).hyp76.zeta k))
          (hyp.base.eta i j) = 0 := by
    intro k hk i j
    have hk' : k ≠ (Mdata.coherent78.h78 Mdata.hG).ind1H := by
      rw [Mdata.coherent78.h78_ind1H_eq Mdata.hG]
      exact hk
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      OrthogonalitySwitchData.caseB_eta_orthogonal_nu_zeta_at
        Mdata.hG hyp.base Mdata.coherent78 hDadeAvoid hk' i j,
      star_zero]
  have hclassSource :
      chi = Mdata.h78.nu (Mdata.h78.hyp76.zeta Mdata.h78.zetaDistinct) ∨
      chi = -Mdata.h78.nu (Mdata.h78.hyp76.zeta Mdata.h78.zetaDistinct).conj := by
    simpa [hchi, hX] using
      (Mdata.coherent78.etaGrid_projection_sub_beta_classification
        Mdata.hG hyp.base m hetaNuData (by simpa [hchi, hX, hH78] using hchiSelf))
  have hclass :
      chi = Mdata.tau1 Mdata.psi ∨ chi = -(Mdata.tau1 Mdata.psi.conj) := by
    rcases hclassSource with h | h
    · left
      exact h
    · right
      rw [Mdata.coherent78.h78_zetaDistinct_eq Mdata.hG,
        Mdata.coherent78.h78_zeta_eq Mdata.hG] at h
      exact h
  -- Both classified branches have the pointwise norm of `ψ^{τ₁}`.
  have hpsiS : Mdata.psi ∈ Mdata.typeIHyp.Sset := Mdata.psi_mem
  have h2 : ∃ psi ∈ Mdata.typeIHyp.Sset, psi ≠ Mdata.psi := by
    obtain ⟨j₁, hj₁ne, hj₁⟩ := Mdata.coherent78.exists_conjIndex Mdata.hG
    have hj₁mem : Mdata.h78.hyp76.zeta j₁ ∈ Mdata.typeIHyp.Sset :=
      Mdata.coherent78.zeta_mem_Sset (by
        rw [← Mdata.coherent78.h78_ind1H_eq Mdata.hG]
        exact hj₁ne)
    refine ⟨Mdata.h78.hyp76.zeta j₁, hj₁mem, ?_⟩
    rw [hj₁]
    exact (Mdata.coherent78.h78_zeta_ne_conj Mdata.hG Mdata.hG.odd).symm
  have hconj : (Mdata.tau1 Mdata.psi).conj = Mdata.tau1 Mdata.psi.conj :=
    Mdata.coherent78.coherence_extension_conj Mdata.hG hpsiS h2
  have hchiNorm : ∀ g : G, ‖chi g‖ = ‖(Mdata.tau1 Mdata.psi) g‖ := by
    intro g
    rcases hclass with h | h
    · rw [h]
    · rw [h, ClassFunction.neg_apply, norm_neg, ← hconj,
        ClassFunction.conj_apply, norm_star]
  refine
    { e_eq_pq := hepq
      delta := BD.Gamma
      chi := chi
      chi_norm := hchiNorm
      chi_classification := hclass
      betaM_seven_eight := ?_
      signs := m
      signs_pm_one := hpm
      grid_eq := ?_ }
  · rw [hchi, hX, show Mdata.betaM = H78.beta by rw [hH78]]
    rw [← show OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma =
        etaGridProjection hyp.base m by simpa [BD] using hgrid]
    abel
  · simpa [BD, hX, etaGridProjection] using hgrid

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
    (hepq : Mdata.e = hyp.base.p * hyp.base.q)
    (signs : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hsigns : ∀ i j, signs i j = 1 ∨ signs i j = -1)
    (hgrid : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + H78.delta =
      ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j) :
    BetaMExpansionData hyp Mdata where
  e_eq_pq := hepq
  delta := H78.delta
  chi := Mdata.tau1 Mdata.psi
  chi_norm := fun _ => rfl
  chi_classification := Or.inl rfl
  betaM_seven_eight := by
    rw [hbeta, H78.beta_eq_constOne_sub_zetaImage_add_delta, hchi]
  signs := signs
  signs_pm_one := hsigns
  grid_eq := hgrid

/-- **Peterfalvi (14.11.2)**: under `K ≠ V`, `e = p q` and `β_M^τ` is a signed sum of the
`η_ij` grid with one unit-norm character `χ` removed:
`β_M^τ = Σ_{0≤i<q, 0≤j<p} (±η_ij) − χ`, where `χ = ψ^{τ₁}` or `−ψ̄^{τ₁}`.

The equality `e = p q`, coefficient rigidity, vanishing of the orthogonal residual, and the χ
classification are derived together inside `betaM_expansion_data` from `K ≠ V`, (14.11.1), the
faithful (13.17.c)-dual bound, and the explicit (13.19.c) alternatives.  This public projection
retains only the pointwise norm consequence needed downstream.  No conclusion of (14.11.2) is
read from `MHypothesis`. -/
theorem betaM_expansion [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
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
  have he_le := Mdata.complementIndex_le_pq _hG
  have hsize := main_size_bounds _hG hnoV hncH0C hyp Mdata hne
  have haxis :=
    betaM_axis_odd_of_main_size_bounds hsize
      (betaMGridParityAlternatives _hG hnoV hncH0C hyp Mdata)
  obtain ⟨hepq, delta, chi, hchi_norm, _hchi_classification, hbeta, signs, hsigns, hgrid⟩ :=
    betaM_expansion_data _hG hnoV hncH0C hyp Mdata hne he_le hsize haxis.1 haxis.2
  refine ⟨hepq, ?_⟩
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
  change (n - i.val) % n = i.val ↔ i.val = 0
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
point is `(0,0)`, since `q`, `p` are odd) and feeds it to `one_le_norm_signed_paired_sum`.  It is
the
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
    change (finNeg hq (finNeg hq x.1), finNeg hp (finNeg hp x.2)) = x
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

end OddOrder.Peterfalvi.S16
