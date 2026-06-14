/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting

/-!
# BG §15: The Subgroup `M_F`

**Scope**: Bender--Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter IV §15 (pp. 117--122), mmd
`references/bg/local-analysis.mmd` L4086--4255.

This section analyzes `M_F`, the maximal nilpotent normal Hall subgroup of a
maximal subgroup `M`.  It connects the §14 type-P/Frobenius-family taxonomy with
Fitting-subgroup intersection arguments used in BG §16 and Peterfalvi §15.

The main scaffold endpoints are:

* **BG 15.2**: `M_F != M_sigma` forces `M` to be type `P1` and gives the
  normal `q`-subgroup / minimal-chief-factor structure.
* **BG 15.7**: if `F(M)` is not TI, then `M` is type `F` or `P1`, and the local
  structure falls into the three cases used in the main theorem.
* **BG 15.8--15.9**: the Feit--Thompson/Sibley constraints that feed the final
  local result.

Proofs are deferred; the purpose here is a stable importable surface for §16 and
Peterfalvi §§15--16.

## Lane C interface and proof-gate notes

- Import boundary: §15 imports §14 only. The §10--§13 and §12 exceptional-maximal
  gates are reached through the BG local-analysis spine, not through Peterfalvi modules.
- Lemma 15.1 uses Theorem 14.7(d)(h), Corollary 12.10(b), Theorem 10.2(c),
  Corollary 14.3, Theorem 12.5(d), and Theorem 12.12 (mmd L4144-L4148).
- Theorem 15.2 uses Lemma 14.1, Theorem 14.7(f), Proposition 14.2(a),
  Lemma 6.3(a), Theorem 3.8, Proposition 1.5(a)(d), Theorem 3.7,
  Theorem 3.10, and Theorem 5.5(a) (mmd L4160-L4172).
- Theorem 15.7 is a BG local case split for `F(M)` not TI. Its Lean statement
  records the compressed endpoint; the `E_i`, exponent-divisibility, and
  `Omega_1(Z(P))` subclauses remain deferred until the §12/§10.13 encodings are complete
  (mmd L4204-L4230).
- Theorem 15.8 and Corollary 15.9 are the Feit--Thompson/Sibley local endpoints
  feeding §16. They depend on Corollary 14.12, Theorem 15.2, Corollary 12.6,
  the Uniqueness Theorem, Lemma 12.17, and Theorem 14.4 (mmd L4234-L4288).
-/

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §15 notation -/

/-- **BG `M_F`**: the maximal nilpotent normal Hall subgroup of `M`. -/
noncomputable abbrev MF (M : Subgroup G) : Subgroup G :=
  maxNilpotentNormalHall M

/-- `M_F ≤ M`: basic containment, directly from the `sSup` construction.  (The full
BG §15 well-definedness — that the `sSup` again has the maximal nilpotent-normal-Hall
property, in particular that it is Hall — is deferred; this containment is not.) -/
theorem maxNilpotentNormalHall_le (M : Subgroup G) : maxNilpotentNormalHall M ≤ M :=
  sSup_le fun _ hN => hN.1

/-- `M` normalizes `M_F` (so `(M_F).subgroupOf M ⊴ M`): the `sSup` of `M`-normal
candidates is again `M`-normal.  Like `maxNilpotentNormalHall_le`, this is the
`§14`-independent part of the §15 well-definedness (the Hall maximality is deferred);
each candidate `N` is fixed by conjugation by `m ∈ M` because `(N.subgroupOf M).Normal`. -/
theorem maxNilpotentNormalHall_le_normalizer (M : Subgroup G) :
    M ≤ Subgroup.normalizer (maxNilpotentNormalHall M) := by
  intro m hm
  refine mem_normalizer_of_conj_smul_eq_self ?_
  unfold maxNilpotentNormalHall
  rw [Subgroup.pointwise_smul_def, (Subgroup.gc_map_comap _).l_sSup, sSup_eq_iSup]
  refine iSup_congr fun N => iSup_congr fun hN => ?_
  rw [← Subgroup.pointwise_smul_def]
  obtain ⟨hNM, hNnorm, -, -⟩ := hN
  exact conj_smul_eq_self_of_mem_normalizer
    (((Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNnorm) hm)

/-- `M_F ⊴ M` in the relative sense `(M_F).subgroupOf M`: the directly usable form of
`maxNilpotentNormalHall_le_normalizer`, matching the normality clause in the defining
predicate of `M_F`. -/
theorem maxNilpotentNormalHall_subgroupOf_normal (M : Subgroup G) :
    ((maxNilpotentNormalHall M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (maxNilpotentNormalHall_le M)).mpr
    (maxNilpotentNormalHall_le_normalizer M)

/-- `M_F ≤ F(M)`: the maximal nilpotent normal Hall subgroup lies inside the Fitting subgroup
`F(M)` (`OddOrder.BG.Ch2.S08.fittingInG`, defeq `(Ch01.fitting ↥M).map M.subtype`), because each
candidate `N` is nilpotent and normal in `M` (so `N.subgroupOf M ≤ fitting ↥M`).  `§14`-independent;
the structural bridge between `M_F` and `F(M)` used throughout §15/§16. -/
theorem maxNilpotentNormalHall_le_fittingInG [Finite G] (M : Subgroup G) :
    maxNilpotentNormalHall M ≤ OddOrder.BG.Ch2.S08.fittingInG M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNM, hNnorm, hNnil, -⟩ := hN
  haveI := hNnorm
  haveI := hNnil
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ OddOrder.BG.Ch2.S08.fittingInG M :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting

/-- **`M_F` is nilpotent** — the §15 well-definedness piece that the defining `sSup` is again
nilpotent.  `M_F ≤ F(M)` (`maxNilpotentNormalHall_le_fittingInG`) and `F(M)` is nilpotent
(image of the nilpotent `fitting ↥M` under the injective `M.subtype`).  `§14`-independent. -/
theorem maxNilpotentNormalHall_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(maxNilpotentNormalHall M) := by
  haveI : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting (↥M)) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG M) :=
    nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting (↥M)) M.subtype
        M.subtype_injective)
  exact nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (maxNilpotentNormalHall_le_fittingInG M))

/-- If `M_σ` is nilpotent, then `M_σ ≤ M_F`: `M_σ` is then a nilpotent normal Hall subgroup of
`M` (normal `σ`-core, `σ`-Hall by `Msigma_isHall`, nilpotent by hypothesis), hence one of the
candidates in the `sSup` defining `M_F`.  `§14`-independent.  Combined with the (gated)
`M_F ≤ M_σ` of Theorem A this gives `M_F = M_σ ⟺ M_σ` nilpotent (recall `M_F` is always
nilpotent, `maxNilpotentNormalHall_isNilpotent`). -/
theorem Msigma_le_maxNilpotentNormalHall_of_nilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M)) :
    OddOrder.BG.Ch3.S10.Msigma M ≤ maxNilpotentNormalHall M := by
  haveI := hnil
  have hle := OddOrder.BG.Ch3.S10.Msigma_le M
  have hcard : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
      Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  apply le_sSup
  refine ⟨hle, ?_, ?_, ?_⟩
  · rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  · exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
  · obtain ⟨hHcard, hHidx⟩ := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
    refine ⟨fun q hq => by rwa [hcard] at hq, fun q hq hqπ => ?_⟩
    obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.mp hq
    have hdvd : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣
        (OddOrder.BG.Ch3.S10.Msigma M).index :=
      Subgroup.relIndex_dvd_index_of_le hle
    exact hHidx q
      (Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans hdvd, Subgroup.index_ne_zero_of_finite⟩)
      (hHcard q hqπ)

/-- The Fitting subgroup of `M`, viewed in the ambient group as in BG §8/§15. -/
noncomputable abbrev fittingInAmbient (M : Subgroup G) : Subgroup G :=
  OddOrder.BG.Ch2.S08.fittingInG M

/-- The nonidentity part of the ambient Fitting subgroup of `M`. -/
def fittingSharp (M : Subgroup G) : Set G :=
  sharpSubgroup (fittingInAmbient M)

/-- The BG §15 hypothesis that `F(M)` is a TI-subgroup of `G`. -/
def FittingIsTI (M : Subgroup G) : Prop :=
  IsTISubset (fittingSharp M) (Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G))

/-- The subgroup generated by the centralizers in `U` of nonidentity elements of
`M_sigma`; this packages BG Lemma 15.1(d). -/
noncomputable def centralizerGeneratedBySigma (M U : Subgroup G) : Subgroup G :=
  sSup {C : Subgroup G | ∃ x ∈ sigmaSharp M,
    C = U ⊓ Subgroup.centralizer ({x} : Set G)}

/-! ## Lemma 15.1: the `U M_sigma` auxiliary structure -/

/-- **BG Lemma 15.1** (mmd L4116): auxiliary structure around the `U`-factor of an
**arbitrary** maximal subgroup `M = KUM_σ`.  The quotient assertion `M'/M_sigma` abelian is
encoded as `M'' <= M_sigma`, avoiding premature quotient API commitments.

Faithfulness fix (Lane G): the previous scaffold added a spurious `IsTypeP M` hypothesis;
mmd Lemma 15.1 holds for every `M ∈ ℳ` (the `K ≠ 1` clauses are guarded inline), and the
general form is what Theorem A(2) and Theorem B cite. -/
theorem typeP_auxiliary_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      IsCyclic ↥K ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      derivedInG (derivedInG M) ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      (K ≠ ⊥ → derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
        IsMulCommutative ↥U) ∧
      (∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
          maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
            IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M)) ∧
      IsMulCommutative ↥(centralizerGeneratedBySigma M U) ∧
      (U ≠ ⊥ → ∃ U0 : Subgroup G,
        U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
          OddOrder.Isaacs.Ch06.IsFrobeniusGroup
            ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
              (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
            (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))) := by
  sorry

/-! ## Theorem 15.2: `M_F != M_sigma` forces type `P1` -/

/-- **BG Theorem 15.2** (mmd L4112): if `M_F` is strictly smaller than `M_sigma`,
then `M` is type `P1` and has the normal `q`-subgroup / minimal chief factor
structure described in the text. -/
theorem mf_ne_msigma_typeP1_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    S14.IsTypeP1 M ∧
      ∃ K Kstar Q Q0 D : Subgroup G, ∃ p q : ℕ,
        Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) ∧
        Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ∧
        p.Prime ∧ q.Prime ∧ Nat.card ↥K = p ∧ Nat.card ↥Kstar = q ∧
        q ∈ S14.piSet (MF M) ∧ q ∈ OddOrder.BG.Ch3.S10.beta M ∧
        Q ≤ MF M ∧ M ≤ Subgroup.normalizer (Q : Set G) ∧
        Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
          (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) ∧
        Group.IsNilpotent ↥D ∧
        Q0 = Q ⊓ Subgroup.centralizer (D : Set G) ∧
        M ≤ Subgroup.normalizer (Q0 : Set G) ∧
        Nat.card ↥(Q.subgroupOf (Q ⊔ Q0)) = q ^ p ∧
        OddOrder.BG.Ch3.S10.Msigma M = derivedInG M ∧
        derivedInG (derivedInG M) ≤ fittingInAmbient M := by
  sorry

/-- **BG Corollary 15.3** (mmd L4204): for a nonidentity Hall subgroup `H` of `M_σ`,
(a) `C_M(H) = C_{M_σ}(H)·X` with `X` a cyclic `τ₂(M)`-subgroup, and (b) any two elements
of `H` conjugate in `G` are already conjugate in `N_M(H)` (`N_M(H)`-fusion control).

Faithfulness fix (Lane G 2026-06-14): the previous scaffold here stated an unrelated
centralizer-escape claim (`C_G(X) ≤ M ∨ …`), not the `C_M(H)`/fusion content the docstring
("centralizer and conjugacy control") names; restated to mmd L4204. Uncited, sorry-neutral. -/
theorem mf_hall_centralizer_control [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hH : Ch03.IsHallSubgroup (S14.piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) :
    (∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X) ∧
    (∀ x ∈ H, ∀ y ∈ H, (∃ g : G, y = g * x * g⁻¹) →
      ∃ n ∈ Subgroup.normalizer (H : Set G), y = n * x * n⁻¹) := by
  sorry

/-- **BG Corollary 15.4** (mmd L4215): a nonidentity nilpotent **Hall** subgroup `H` of `G`
can be embedded in `M_σ` for a suitable maximal subgroup `M` (`H ⊆ M_σ`).

Faithfulness fix (Lane G): the previous scaffold dropped the **Hall** hypothesis (mmd requires
`H` Hall of `G`) and over-claimed `H ≤ M_F` — the proof only gives `H ⊆ M_σ` (the textbook
conclusion), and `H ⊆ M_F` does not follow (`H` need not be normal in `M`). -/
theorem nilpotent_hall_embeds_in_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {H : Subgroup G}
    (hHnil : Group.IsNilpotent ↥H) (hHne : H ≠ ⊥)
    (hHall : Ch03.IsHallSubgroup (S14.piSet H) H) :
    ∃ M : Subgroup G, M ∈ maximalSubgroupsContaining H ∧
      H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  sorry

/-- **BG Corollary 15.5** (mmd L4225): the decomposition `F(M) = F(M_σ) × Y` with
`Y = O_{σ(M)'}(F(M))` a cyclic `τ₂(M)`-subgroup, together with `F(M) = C_M(M_F)·M_F`,
`M'' ⊆ F(M)`, `M_F ⊆ M'`, and `K ≠ 1 → F(M) ⊆ M'`.  Direct products are encoded by the
commuting/trivial-intersection package.

Faithfulness fix (Lane G): the previous scaffold parametrized an arbitrary `H ≤ M_F` (mmd
fixes `H = M_F`) and used `M_F(M_σ)` where the textbook has the Fitting subgroup `F(M_σ)`
(`fittingInAmbient (Msigma M)`); the dropped conjuncts (a)/(b)/(d) are restored.  The `M'/M_F`
nilpotent clause of (c) is still deferred (quotient API). -/
theorem fitting_decomposition [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ Y : Subgroup G,
      -- (a) `Y = O_{σ(M)'}(F(M))` is a cyclic `τ₂(M)`-subgroup of `F(M)`.
      IsCyclic ↥Y ∧ (↑(Nat.card ↥Y).primeFactors ⊆ tau2 M) ∧ Y ≤ fittingInAmbient M ∧
      -- (b) `M'' ⊆ F(M) = C_M(M_F)·M_F = F(M_σ) × Y`.
      derivedInG (derivedInG M) ≤ fittingInAmbient M ∧
      fittingInAmbient M = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M ∧
      fittingInAmbient M = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ⊔ Y ∧
      fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ⊓ Y = ⊥ ∧
      ⁅fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M), Y⁆ = ⊥ ∧
      -- (c) `M_F ⊆ M'` (the `M'/M_F` nilpotent part is deferred — quotient API).
      MF M ≤ derivedInG M ∧
      -- (d) if `K ≠ 1` (i.e. `M` is not of type `F`), then `F(M) ⊆ M'`.
      (¬ S14.IsTypeF M → fittingInAmbient M ≤ derivedInG M) := by
  sorry

/-- **BG Corollary 15.6** (mmd L4174): for a type-P maximal subgroup, `Kstar` is
nontrivial cyclic and lies in `M_F`, while `M_F` itself is not cyclic. -/
theorem typeP_kstar_in_mf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ MF M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧ ¬ IsCyclic ↥(MF M) := by
  sorry

/-! ## Theorems 15.7--15.9: TI failure and final local constraints -/

/-- **BG Theorem 15.7** (mmd L4180): if `F(M)` is not TI in `G`, then `M` is in
`M_F ∪ M_P1`, the relevant intersection is cyclic inside `M_F = M_sigma`, and
one of the three local cases of the theorem holds. -/
theorem fitting_not_ti_cases [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnotTI : ¬ FittingIsTI M) :
    (S14.IsTypeF M ∨ S14.IsTypeP1 M) ∧ MF M = OddOrder.BG.Ch3.S10.Msigma M ∧
      ∃ X : Subgroup G,
        X ≤ MF M ∧ X ≠ ⊥ ∧ IsCyclic ↥X ∧
        derivedInG M = fittingInAmbient M ∧
        (∃ p : ℕ, p.Prime ∧ p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
          p ∉ OddOrder.BG.Ch3.S10.beta M ∧
          (IsMulCommutative ↥(MF M) ∨
            ¬ IsMulCommutative ↥(MF M) ∧
              (S14.IsTypeF M ∨ S14.IsTypeP1 M))) := by
  sorry

/-- **BG Theorem 15.8** (mmd L4221; Feit--Thompson 1991): in the §14.12 setup,
nonempty `tau_2(H)` forces `tau_2(M)=empty` and makes `tau_2(N)` a singleton. -/
theorem tau2_transfer_constraint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M H N K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hN : N ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hHtau : (tau2 H).Nonempty) :
    tau2 M = ∅ ∧ ∃ q : ℕ, q.Prime ∧ tau2 N = {q} := by
  sorry

/-- **BG Corollary 15.9** (mmd L4240): final local landing point for a centralizer
escaping `M`.  This is the Sibley/Feit--Thompson package used by §16. -/
theorem centralizer_escape_final_local [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M N : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ sigmaSharp M) (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNnotF : ¬ S14.IsTypeF N) :
    S14.IsTypeF M ∧ S14.IsTypeP2 N ∧
      ∃ E : Subgroup G,
        E ≤ M ∧ Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
          (E.subgroupOf M) ∧ IsCyclic ↥E ∧
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) ∧
        ∃ r : ℕ, r.Prime ∧ r ∈ tau2 N ∧
          Subgroup.normalizer (Subgroup.closure ({x} : Set G)) ≤ E ⊓ N := by
  sorry

end OddOrder.BG.Ch4.S15
