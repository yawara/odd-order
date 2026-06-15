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

/-- `M_F ≤ M`: basic containment, directly from the `sSup` construction.  (The §15
well-definedness that the `sSup` is again Hall is `maxNilpotentNormalHall_isHall` below; this
containment is the more elementary half.) -/
theorem maxNilpotentNormalHall_le (M : Subgroup G) : maxNilpotentNormalHall M ≤ M :=
  sSup_le fun _ hN => hN.1

/-- `M` normalizes `M_F` (so `(M_F).subgroupOf M ⊴ M`): the `sSup` of `M`-normal
candidates is again `M`-normal.  Like `maxNilpotentNormalHall_le`, this is part of the
`§14`-independent §15 well-definedness (the Hall property is `maxNilpotentNormalHall_isHall`);
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

/-- **`M_F ≤ M_σ`** (BG §15, mmd L4116 "it is easy to see ... `M_F` ... lies in `M_σ`").
Every nilpotent normal Hall subgroup `N` of `M` is a `σ(M)`-group: for a prime `p ∣ |N|`, the
Sylow `p`-subgroup of `N` is characteristic in `N` (nilpotent) hence normal in `M`, and a full
Sylow `p`-subgroup of `M` (`N` Hall), so it maps to `O_p(M)`; minimality of `M` and simplicity
of `G` give `N_G(O_p(M)) ≤ M`, i.e. `p ∈ σ(M)`.  Then `N ≤ O_{σ(M)}(M) = M_σ` by maximality of
the `σ(M)`-core.  `§14`-independent. -/
theorem maxNilpotentNormalHall_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNM, hNnorm, hNnil, hNHall⟩ := hN
  haveI := hNnorm
  haveI := hNnil
  set N' : Subgroup ↥M := N.subgroupOf M with hN'def
  have hcardN' : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  -- `N'` is a `σ(M)`-group: every prime divisor of `|N|` lies in `σ(M)`.
  have hpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) N' := by
    intro p hp
    have hpN : p ∈ (Nat.card ↥N).primeFactors := by rwa [hcardN'] at hp
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hpM : p ∈ (Nat.card ↥M).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨‹Fact p.Prime›.1,
        (Nat.dvd_of_mem_primeFactors hpN).trans
          (hcardN' ▸ Subgroup.card_subgroup_dvd_card N'), Nat.card_pos.ne'⟩
    -- `p ∤ [M : N']` (Hall), so the `p`-part of `|M|` is concentrated in `N'`.
    have hpidx : ¬ p ∣ N'.index := fun hdvd =>
      hNHall.2 p (Nat.mem_primeFactors.mpr
        ⟨‹Fact p.Prime›.1, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpN
    have hfact : (Nat.card ↥M).factorization p = (Nat.card ↥N').factorization p := by
      conv_lhs => rw [← Subgroup.card_mul_index N']
      rw [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
    -- The Sylow `p`-subgroup of the nilpotent `N'` is characteristic, hence normal in `M`,
    -- and (Hall) a full Sylow `p`-subgroup of `M`.
    obtain ⟨SN⟩ := (inferInstance : Nonempty (Sylow p ↥N'))
    haveI hSNnorm : (SN : Subgroup ↥N').Normal :=
      OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent SN
    haveI hSNchar : (SN : Subgroup ↥N').Characteristic :=
      Sylow.characteristic_of_normal SN hSNnorm
    have hScard : Nat.card ↥((SN : Subgroup ↥N').map N'.subtype) =
        p ^ (Nat.card ↥M).factorization p := by
      rw [Subgroup.card_map_of_injective N'.subtype_injective, SN.card_eq_multiplicity, hfact]
    haveI hmapnorm : ((SN : Subgroup ↥N').map N'.subtype).Normal := inferInstance
    let P : Sylow p ↥M := Sylow.ofCard ((SN : Subgroup ↥N').map N'.subtype) hScard
    have hPnorm : (P : Subgroup ↥M).Normal := hmapnorm
    have hPmap : (P : Subgroup ↥M).map M.subtype = OddOrder.GroupTheory.opiCoreInG {p} M :=
      OddOrder.BG.Ch3.S10.sylowMap_eq_opiCoreInG_singleton_of_normal P hPnorm
    have hPne : OddOrder.GroupTheory.opiCoreInG {p} M ≠ ⊥ :=
      OddOrder.BG.Ch3.S10.opiCoreInG_singleton_ne_bot_of_sylowMap_eq hpM P hPmap
    rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
    refine ⟨hpM, P, ?_⟩
    rw [hPmap]
    exact OddOrder.BG.Ch2.S09.normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot hG hM hPne
  calc N = N'.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ (OddOrder.Isaacs.Ch03.oPiCore (OddOrder.BG.Ch3.S10.sigma M) ↥M).map M.subtype :=
        Subgroup.map_mono hpi.le_oPiCore
    _ = OddOrder.BG.Ch3.S10.Msigma M := rfl

/-- **`M_F = M_σ ⟺ M_σ` is nilpotent** (`§14`-independent).  Forward: `M_F` is always nilpotent
(`maxNilpotentNormalHall_isNilpotent`).  Backward: `maxNilpotentNormalHall_le_Msigma` (always)
and `Msigma_le_maxNilpotentNormalHall_of_nilpotent` give equality by antisymmetry. -/
theorem maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M ↔
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  refine ⟨fun h => h ▸ maxNilpotentNormalHall_isNilpotent M, fun hnil => ?_⟩
  exact le_antisymm (maxNilpotentNormalHall_le_Msigma hG hM)
    (Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hM hnil)

/-- **`M_F ≤ M'`** (the `H ⊆ M'` part of BG Corollary 15.5(c), `H = M_F`): the containment chain
`M_F ≤ M_σ ≤ M' ≤ M` via `maxNilpotentNormalHall_le_Msigma` and `Msigma_le_derived`.
`§14`-independent.  (The `M'/M_F` nilpotency of 15.5(c) remains deferred — quotient API.) -/
theorem maxNilpotentNormalHall_le_derived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M ≤ derivedInG M :=
  (maxNilpotentNormalHall_le_Msigma hG hM).trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)

/-- **General helper (§14-independent, reusable).**  In a finite group, the `sSup` of a set `s`
of normal `π`-subgroups is again a `π`-subgroup.  (Mirrors the `Finset.sup_induction` argument of
`Ch03.oPiCore.isPiGroup`, but for an arbitrary set rather than the defining family of `oPiCore`.)
Used for the §15 well-definedness "`M_F` is Hall": the supremum defining `M_F` collapses to a join
of normal subgroups, whose order has no new prime factors. -/
theorem isPiGroup_sSup_of_forall_normal {H : Type*} [Group H] [Finite H] (π : Set ℕ)
    (s : Set (Subgroup H)) (hnorm : ∀ N ∈ s, N.Normal)
    (hpi : ∀ N ∈ s, Ch03.Subgroup.IsPiGroup π N) :
    Ch03.Subgroup.IsPiGroup π (sSup s) := by
  classical
  haveI hSubF : Fintype {N : Subgroup H // N ∈ s} := Fintype.ofFinite _
  -- Carry both normality and the `π`-group property through the induction.
  set q : Subgroup H → Prop := fun K => K.Normal ∧ Ch03.Subgroup.IsPiGroup π K with hq_def
  suffices hgoal : q (sSup s) by exact hgoal.2
  -- Rewrite the `sSup` as a `Finset.sup` over the (finite) subtype `{N // N ∈ s}`.
  have hsup : sSup s =
      (Finset.univ : Finset {N : Subgroup H // N ∈ s}).sup (fun N => (N.val : Subgroup H)) := by
    rw [Finset.sup_eq_iSup]
    simp only [iSup_pos, Finset.mem_univ]
    rw [← sSup_eq_iSup']
  rw [hsup]
  refine Finset.sup_induction (p := q) ?_ ?_ ?_
  · -- `⊥` is a normal `π`-group (no prime factors).
    refine ⟨inferInstance, ?_⟩
    intro r hr
    simp only [Subgroup.card_bot, Nat.primeFactors_one, Finset.notMem_empty] at hr
  · -- closure under join of two normal `π`-subgroups.
    rintro a₁ ⟨ha₁N, ha₁Pi⟩ a₂ ⟨ha₂N, ha₂Pi⟩
    haveI := ha₁N
    haveI := ha₂N
    exact ⟨inferInstance, Ch03.Subgroup.IsPiGroup.sup_of_normal ha₁Pi ha₂Pi⟩
  · -- each generator is a normal `π`-group by hypothesis.
    intro b _
    exact ⟨hnorm b.val b.2, hpi b.val b.2⟩

/-- **BG §15 well-definedness: `M_F` is a Hall subgroup of `M`** (general finite-group fact,
§14-independent; no minimal-simple hypothesis needed).  `M_F = maxNilpotentNormalHall M` is, as a
relative subgroup `(M_F).subgroupOf M ⊴ M`, a `π(M_F)`-Hall subgroup of `M`, where
`π(M_F) = (Nat.card ↥(M_F)).primeFactors`.

Proof: `(M_F).subgroupOf M` is the join (in `↥M`) of the normal subgroups `N.subgroupOf M`
ranging over the candidates `N` of the `sSup` defining `M_F`; this join has no prime factor beyond
those of the candidates (`isPiGroup_sSup_of_forall_normal`).  Hence every prime `p ∣ |M_F|` divides
some candidate `|N₀|`, and that candidate is `π(N₀)`-Hall in `↥M` with `p ∈ π(N₀)`, so
`p ∤ [M : N₀.subgroupOf M]`; since `N₀.subgroupOf M ≤ (M_F).subgroupOf M`, also `p ∤ [M : M_F]`.
The index of `(M_F).subgroupOf M` therefore shares no prime with `|M_F|`, i.e. `M_F` is Hall. -/
theorem maxNilpotentNormalHall_isHall [Finite G] (M : Subgroup G) :
    Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
      ((maxNilpotentNormalHall M).subgroupOf M) := by
  classical
  set H : Subgroup G := maxNilpotentNormalHall M with hHdef
  set Hbar : Subgroup ↥M := H.subgroupOf M with hHbar
  -- The defining set of `M_F`, and its image in `↥M`.
  set S : Set (Subgroup G) := {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧
      Group.IsNilpotent ↥(N.subgroupOf M) ∧
      Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)} with hSdef
  have hHsSup : H = sSup S := rfl
  set T : Set (Subgroup ↥M) := (fun N => N.subgroupOf M) '' S with hTdef
  -- `card Hbar = card H` (since `H ≤ M`).
  have hHle : H ≤ M := maxNilpotentNormalHall_le M
  have hcardHbar : Nat.card ↥Hbar = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
  -- `⨆ x ∈ T, map x = ⨆ N ∈ S, N`, since `map (N.subgroupOf M) = N` for `N ≤ M ∈ S`.
  have hiSup : (⨆ x ∈ T, x.map M.subtype) = ⨆ N ∈ S, N := by
    rw [hTdef, iSup_image]
    refine iSup_congr fun N => iSup_congr fun hN => ?_
    exact Subgroup.map_subgroupOf_eq_of_le hN.1
  -- Key identification: `Hbar = sSup T`.
  have hHbar_eq : Hbar = sSup T := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hHbar, Subgroup.map_subgroupOf_eq_of_le hHle, hHsSup,
      (Subgroup.gc_map_comap M.subtype).l_sSup, hiSup, ← sSup_eq_iSup]
  -- Every element of `T` is normal in `↥M` and a `Pri`-group, where `Pri` is the set of primes
  -- occurring in some candidate's order.
  set Pri : Set ℕ := {p | ∃ N ∈ S, p ∈ (Nat.card ↥N).primeFactors} with hPridef
  have hTnorm : ∀ x ∈ T, x.Normal := by
    rintro x ⟨N, hN, rfl⟩; exact hN.2.1
  have hTpi : ∀ x ∈ T, Ch03.Subgroup.IsPiGroup Pri x := by
    rintro x ⟨N, hN, rfl⟩
    intro p hp
    -- `card (N.subgroupOf M) = card N`, so a prime factor of it is one of `N`.
    have hcardN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.1).toEquiv
    exact ⟨N, hN, by rwa [hcardN] at hp⟩
  -- Hence `Hbar` is a `Pri`-group.
  have hHbarpi : Ch03.Subgroup.IsPiGroup Pri Hbar := by
    rw [hHbar_eq]; exact isPiGroup_sSup_of_forall_normal Pri T hTnorm hTpi
  -- Assemble the Hall property.
  refine ⟨fun p hp => ?_, fun p hp hpπ => ?_⟩
  · -- Prime factors of `|Hbar| = |H|` are exactly `π(M_F)`.
    rwa [hcardHbar] at hp
  · -- `p ∈ π(M_F)` and `p ∣ [M : Hbar]`: derive a contradiction.
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    -- `p ∈ π(M_F)`, so `p ∣ |Hbar|`, so `p ∈ Π`: pick a candidate `N₀` with `p ∣ |N₀|`.
    have hpHbar : p ∈ (Nat.card ↥Hbar).primeFactors := by
      rw [hcardHbar]; exact hpπ
    obtain ⟨N₀, hN₀, hpN₀⟩ := hHbarpi p hpHbar
    -- `N₀.subgroupOf M` is `π(N₀)`-Hall with `p ∈ π(N₀)`, so `p ∤ [M : N₀.subgroupOf M]`.
    have hpN₀Hall : ¬ p ∣ (N₀.subgroupOf M).index := by
      intro hdvd
      exact hN₀.2.2.2.2 p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpN₀
    -- `N₀.subgroupOf M ≤ Hbar`, so `[M : Hbar] ∣ [M : N₀.subgroupOf M]`, so `p ∤ [M : Hbar]`.
    have hN₀_le_H : N₀ ≤ H := hHsSup ▸ le_sSup hN₀
    have hle : N₀.subgroupOf M ≤ Hbar := by
      rw [hHbar]; exact Subgroup.subgroupOf_mono M hN₀_le_H
    exact hpN₀Hall ((Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.index_dvd_of_le hle))

/-- The Fitting subgroup of `M`, viewed in the ambient group as in BG §8/§15. -/
noncomputable abbrev fittingInAmbient (M : Subgroup G) : Subgroup G :=
  OddOrder.BG.Ch2.S08.fittingInG M

/-- **`F(H) = H` for a nilpotent subgroup `H`** (`§14`-independent, reusable): the Fitting
subgroup of a nilpotent group is the whole group (`fitting ↥H = ⊤`), so its ambient realization
`fittingInAmbient H` is just `H`.  Used by Corollary 15.5 (the `M_F = M_σ` case, where `M_σ` is
nilpotent so `F(M_σ) = M_σ = M_F`) and the `M_F` cyclic ⟹ `F(M)` cyclic step of Corollary 15.6. -/
theorem fittingInAmbient_eq_self_of_isNilpotent [Finite G] {H : Subgroup G}
    [Group.IsNilpotent ↥H] : fittingInAmbient H = H := by
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup ↥H) :=
    nilpotent_of_mulEquiv Subgroup.topEquiv.symm
  have htop : OddOrder.Isaacs.Ch01.fitting ↥H = ⊤ :=
    top_le_iff.mp OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  show (OddOrder.Isaacs.Ch01.fitting ↥H).map H.subtype = H
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-! ### The Aut-abelian core (`§14`-independent, reusable)

The next two lemmas package the elementary fact behind the "`M_F` not cyclic" half of
Corollary 15.6: if a normal subgroup `N ⊴ H` is **cyclic**, then `Aut(N)` is abelian, so the
conjugation map `H → Aut(N)` (kernel `C_H(N)`) sends `H'` to `1`, i.e. `H' ≤ C_H(N)`.
Specialised to `N = F(M)` and combined with the self-centralizing property of the Fitting
subgroup (`centralizer_fitting_le_fitting`), `F(M)` cyclic forces `M'' = 1`. -/

/-- The conjugation action commutator of `H` on itself is the ordinary derived subgroup:
`actionCommutator (MulAut.conj) = commutator H`.  (Both are the closure of the commutator
elements `g * (a g⁻¹ a⁻¹) = ⁅g, a⁆`.) -/
private theorem actionCommutator_conj_eq_commutator {H : Type*} [Group H] :
    OddOrder.Isaacs.Ch04.actionCommutator (MulAut.conj : H →* MulAut H) = commutator H := by
  rw [commutator_eq_closure]
  unfold OddOrder.Isaacs.Ch04.actionCommutator
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, commutatorSet_def]
  constructor
  · rintro ⟨g, a, rfl⟩
    exact ⟨g, a, by rw [commutatorElement_def, MulAut.conj_apply]; group⟩
  · rintro ⟨g₁, g₂, rfl⟩
    exact ⟨g₁, g₂, by rw [commutatorElement_def, MulAut.conj_apply]; group⟩

open OddOrder.BG.Ch1.OperatorQuotientAction in
/-- **Aut-abelian core**: if `N ⊴ H` is cyclic, then `H' ≤ C_H(N)`.  Conjugation gives a
homomorphism `H → Aut(↥N)` with kernel `C_H(N)`; `↥N` cyclic makes `Aut(↥N)` abelian, so the
derived subgroup `H'` lands in the kernel.  Reuses the BG Thm 4.12 machinery
(`actionCommutator_le_centralizer_of_isCyclic_isAInvariant`) with `φ = MulAut.conj`. -/
theorem commutator_le_centralizer_of_normal_isCyclic {H : Type*} [Group H]
    {N : Subgroup H} [IsCyclic ↥N] (hN : N.Normal) :
    commutator H ≤ Subgroup.centralizer (N : Set H) := by
  have hinv : OddOrder.Isaacs.Ch03.IsAInvariant (MulAut.conj : H →* MulAut H) N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [MulAut.conj_apply]
    exact hN.conj_mem g hg a
  have h := actionCommutator_le_centralizer_of_isCyclic_isAInvariant
    (φ := (MulAut.conj : H →* MulAut H)) (S := N) hN hinv
  rwa [actionCommutator_conj_eq_commutator] at h

/-- **BG §15, `F(M)` cyclic ⟹ `M'' = 1`** (`§14`-independent).  If the ambient Fitting subgroup
`F(M)` is cyclic then `M' ≤ C_M(F(M)) ≤ F(M)` (Aut-abelian core + Fitting self-centralizing),
so `M'` is abelian and `M'' = 1`.  This is the engine of Corollary 15.6's "`M_F` not cyclic"
clause. -/
theorem fittingInAmbient_cyclic_imp_derivedDerived_eq_bot [Finite G] {M : Subgroup G}
    [IsSolvable ↥M] (hcyc : IsCyclic ↥(fittingInAmbient M)) :
    derivedInG (derivedInG M) = ⊥ := by
  -- `fitting ↥M` is cyclic (transport of `hcyc` along `fittingInAmbient M ≅ fitting ↥M`)
  haveI hfitcyc : IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting ↥M) := by
    have e : ↥(OddOrder.Isaacs.Ch01.fitting ↥M) ≃* ↥(fittingInAmbient M) :=
      Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting ↥M) M.subtype M.subtype_injective
    exact isCyclic_of_surjective e.symm e.symm.surjective
  -- `commutator ↥M ≤ centralizer (fitting ↥M) ≤ fitting ↥M`
  have hcomm_le : commutator ↥M ≤ OddOrder.Isaacs.Ch01.fitting ↥M :=
    (commutator_le_centralizer_of_normal_isCyclic
      (inferInstance : (OddOrder.Isaacs.Ch01.fitting ↥M).Normal)).trans
      OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting
  -- push to the ambient group: `M' = ⁅M, M⁆ ≤ F(M)`
  have hderiv_le : derivedInG M ≤ fittingInAmbient M := Subgroup.map_mono hcomm_le
  -- `F(M)` cyclic ⟹ abelian ⟹ `F(M) ≤ C_G(F(M))`
  have hself : (fittingInAmbient M : Subgroup G) ≤ Subgroup.centralizer (fittingInAmbient M) := by
    haveI := hcyc
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h : (⟨y, hy⟩ : ↥(fittingInAmbient M)) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨y, hy⟩ := mul_comm' _ _
    calc y * x = ↑((⟨y, hy⟩ : ↥(fittingInAmbient M)) * ⟨x, hx⟩) := by rw [Subgroup.coe_mul]
      _ = ↑((⟨x, hx⟩ : ↥(fittingInAmbient M)) * ⟨y, hy⟩) := by rw [h]
      _ = x * y := by rw [Subgroup.coe_mul]
  -- `M'' = ⁅M', M'⁆ ≤ ⁅F(M), F(M)⁆ = 1`
  rw [show derivedInG (derivedInG M) = ⁅derivedInG M, derivedInG M⁆ from
        Subgroup.map_subtype_commutator (derivedInG M)]
  refine le_bot_iff.mp (le_trans (Subgroup.commutator_mono hderiv_le hderiv_le) ?_)
  exact le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hself)

/-- **§14-independent engine for BG Corollary 15.6's `K* ⊆ M''` clause.**  Given the type-`P`
complement structure `M = K M'` with `K ∩ M' = 1` (BG Theorem 14.7(h), here as the relative-
complement hypothesis `hcompl` inside `↥M`) and the coprimality of `|M'|` and `|K|`, Lemma 6.3
(`centralizer_inf_le_derivedInG_of_isComplement'`, proved) yields `C_{M'}(K) ⊆ M''`; since
`K* = C_{M_σ}(K) = M_σ ⊓ C_G(K) ⊆ C_{M'}(K)` (because `M_σ ⊆ M'`), this gives `K* ⊆ M''`.

The complement/coprimality data are the only `§14` inputs; everything else is unconditional, so
Corollary 15.6 reduces its `K* ⊆ M''` clause to a single citation once Theorem 14.7(h) (or the
`IsComplement' (derivedInG M) K` strengthening of Lemma 15.1) lands.  Mirrors the Lemma 6.3
transport in `S12_E.Msigma_E_relations`, with `M'` in place of `M_σ` and `K` in place of `E`. -/
theorem Msigma_inf_centralizer_le_derivedDerived_of_isComplement' [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M))) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≤
      derivedInG (derivedInG M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMσ_le_deriv : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hderivM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `H := (derivedInG M).subgroupOf M = commutator ↥M`, normal in `↥M`.
  have hid : (derivedInG M).subgroupOf M = commutator ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
  haveI hHnorm : ((derivedInG M).subgroupOf M).Normal := by rw [hid]; infer_instance
  have hH_le : (derivedInG M).subgroupOf M ≤ commutator ↥M := le_of_eq hid
  -- Lemma 6.3 inside `↥M`:  `C_{↥M}(K') ⊓ H ≤ derivedInG H`.
  have h632 := OddOrder.BG.Ch1.S06.centralizer_inf_le_derivedInG_of_isComplement'
    (G := ↥M) hcompl hH_le hcop
  -- Transport identity:  `(derivedInG H).map M.subtype = derivedInG (derivedInG M)`.
  have hderiv_transport :
      (derivedInG ((derivedInG M).subgroupOf M)).map M.subtype =
        derivedInG (derivedInG M) := by
    rw [show derivedInG ((derivedInG M).subgroupOf M)
          = ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆
          from Subgroup.map_subtype_commutator _,
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hderivM,
      show ⁅(derivedInG M : Subgroup G), derivedInG M⁆ = derivedInG (derivedInG M)
          from (Subgroup.map_subtype_commutator _).symm]
  -- Pointwise: every `x ∈ M_σ ⊓ C_G(K)` lands in `derivedInG (derivedInG M)`.
  intro x hx
  obtain ⟨hxMσ, hxC⟩ := hx
  have hxM : x ∈ M := hMσM hxMσ
  have hxmem : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M)
        ⊓ (derivedInG M).subgroupOf M := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩
    · intro k' hk'
      have hkK : ((k' : ↥M) : G) ∈ K := Subgroup.mem_subgroupOf.mp hk'
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (k' : G) hkK)
    · exact Subgroup.mem_subgroupOf.mpr (hMσ_le_deriv hxMσ)
  have hmapped := Subgroup.mem_map_of_mem M.subtype (h632 hxmem)
  rwa [hderiv_transport] at hmapped

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

/-! ### Lemma 15.1 helpers -/

/-- **`K ≠ ⊥` for a Hall `κ(M)`-subgroup of `M` forces `IsTypeP M`** (`§14`-independent bridge).
A nontrivial Hall `κ(M)`-subgroup has a prime divisor, which lies in `κ(M)`; hence `κ(M)` is
nonempty, i.e. `M` is type `P`.  This converts the `K ≠ ⊥` case split of Lemma 15.1 into the
`IsTypeP M` hypothesis that the §14 results (`typeP_duality`, `typeP_structure`) require. -/
theorem isTypeP_of_isHall_kappa_subgroupOf_ne_bot [Finite G] {M K : Subgroup G}
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKne : K.subgroupOf M ≠ ⊥) :
    S14.IsTypeP M := by
  have hcard : Nat.card ↥(K.subgroupOf M) ≠ 1 := fun h => hKne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  exact ⟨p, hK.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩)⟩

/-- **Abstract second-derived containment** (`§14`-independent, reusable): if `N ⊴ H` and the
derived subgroup of the quotient `H ⧸ N` is abelian, then `⁅H', H'⁆ ≤ N` (the second derived
subgroup of `H`, as a subgroup of `H`, lies in `N`).  The quotient map `mk'` sends `⁅H', H'⁆`
onto `(H/N)''`, which is trivial because `(H/N)'` is abelian; hence `⁅H', H'⁆ ≤ ker mk' = N`.
This is the "(M/M_σ)' abelian ⟹ M'' ≤ M_σ" step of Lemma 15.1(a). -/
theorem commutator_commutator_le_of_quotient_commutator_commutative {H : Type*} [Group H]
    {N : Subgroup H} [hN : N.Normal] (hab : IsMulCommutative ↥(commutator (H ⧸ N))) :
    ⁅commutator H, commutator H⁆ ≤ N := by
  -- `(H/N)'' = ⁅(H/N)', (H/N)'⁆ = ⊥` since `(H/N)'` is abelian.
  have hdd_bot : ⁅commutator (H ⧸ N), commutator (H ⧸ N)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hab.is_comm.comm (⟨y, hy⟩ : ↥(commutator (H ⧸ N))) ⟨x, hx⟩
    exact congrArg Subtype.val this
  -- `(H/N)' = (H').map mk'` and `(H/N)'' = ⁅H', H'⁆.map mk'` (mk' surjective).
  have hsurj : (QuotientGroup.mk' N).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hmap1 : (commutator H).map (QuotientGroup.mk' N) = commutator (H ⧸ N) := by
    rw [map_commutator_eq, hsurj, _root_.commutator_def]
  have hmap2 : (⁅commutator H, commutator H⁆).map (QuotientGroup.mk' N) =
      ⁅commutator (H ⧸ N), commutator (H ⧸ N)⁆ := by
    rw [Subgroup.map_commutator, hmap1]
  rw [hdd_bot, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap2
  exact hmap2

/-- **`IsMulCommutative` of a commutator subgroup transports along a `MulEquiv`** (`§14`-
independent, reusable): if `A ≃* B` and `A'` is abelian, then `B'` is abelian.  The equivalence
maps `A'` onto `B'`, so `↥A' ≃* ↥B'`. -/
theorem isMulCommutative_commutator_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsMulCommutative ↥(commutator A)) : IsMulCommutative ↥(commutator B) := by
  have hmap : (commutator A).map (e : A →* B) = commutator B := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, _root_.commutator_def]
  exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv
    ((MulEquiv.subgroupMap e (commutator A)).trans (MulEquiv.subgroupCongr hmap)) hA

/-- **Lemma 15.1(a), the `M'' ≤ M_σ` conjunct** (`§14`-independent): the second derived subgroup
of a maximal subgroup `M` is contained in `M_σ`.  Equivalently `(M/M_σ)'` is abelian; this is
Corollary 12.10(b) (`E' = (M/M_σ)'` abelian via the complement `M = M_σ ⋊ E`).  Proof: pick a
`SubgroupESetup` complement `E`, get `IsMulCommutative (derivedInG E)` from Cor 12.10(b), transport
it to `(↥M ⧸ N)'` abelian along `↥M ⧸ N ≃* E` (`IsComplement'.QuotientMulEquiv`), then apply the
abstract `commutator_commutator_le_of_quotient_commutator_commutative` and push to the ambient. -/
theorem derivedDerived_le_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    derivedInG (derivedInG M) ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  -- §12 complement setup and `(M/M_σ)' = E'` abelian (Cor 12.10(b)).
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := OddOrder.BG.Ch3.S12.exists_subgroupESetup hG hM
  obtain ⟨_, ⟨_, hE'ab⟩, _⟩ := OddOrder.BG.Ch3.S12.nilpotent_sigmaComplement_abelian hG hsetup
  set N : Subgroup ↥M := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M with hNdef
  haveI hNnorm : N.Normal := by rw [hNdef, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  -- `derivedInG E ≅ commutator ↥E`, so `commutator ↥E` is abelian.
  have hcommE_ab : IsMulCommutative ↥(commutator ↥E) := by
    have e : ↥(commutator ↥E) ≃* ↥(derivedInG E) :=
      Subgroup.equivMapOfInjective (commutator ↥E) E.subtype E.subtype_injective
    exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv e.symm hE'ab
  -- transport `commutator ↥E` abelian to `commutator (↥M ⧸ N)` abelian via the complement iso.
  have hquot_ab : IsMulCommutative ↥(commutator (↥M ⧸ N)) := by
    have hcompl : (E.subgroupOf M).IsComplement' N := hsetup.isComplement'_subgroupOf.symm
    have e1 : (↥M ⧸ N) ≃* ↥(E.subgroupOf M) := hcompl.QuotientMulEquiv
    have e2 : ↥(E.subgroupOf M) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hsetup.E_le
    exact isMulCommutative_commutator_of_mulEquiv (e1.trans e2).symm hcommE_ab
  -- abstract lemma: `⁅commutator ↥M, commutator ↥M⁆ ≤ N`, then push to the ambient.
  have hle : ⁅commutator ↥M, commutator ↥M⁆ ≤ N :=
    commutator_commutator_le_of_quotient_commutator_commutative hquot_ab
  -- `derivedInG (derivedInG M) = ⁅commutator ↥M, commutator ↥M⁆.map M.subtype`.
  have hderiv_eq : derivedInG (derivedInG M) =
      (⁅commutator ↥M, commutator ↥M⁆).map M.subtype := by
    rw [show derivedInG (derivedInG M) = ⁅derivedInG M, derivedInG M⁆ from
        Subgroup.map_subtype_commutator (derivedInG M),
      derivedInG, Subgroup.map_commutator]
  rw [hderiv_eq]
  calc (⁅commutator ↥M, commutator ↥M⁆).map M.subtype
      ≤ N.map M.subtype := Subgroup.map_mono hle
    _ = OddOrder.BG.Ch3.S10.Msigma M := by
        rw [hNdef, Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le M)]

/-- **`K = ⊥` forces `κ(M) = ∅`** (`§14`-independent): if the Hall `κ(M)`-subgroup `K ≤ M` of `M`
is trivial, then `M` has no `κ(M)`-prime, so `κ(M) = ∅`, i.e. `M` is type `F`.  (A `κ(M)`-prime
would divide `|M|` — `κ(M) ⊆ π(M)` — and the Hall `κ(M)`-subgroup would be nontrivial.) -/
theorem isTypeF_of_isHall_kappa_eq_bot [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥) :
    S14.IsTypeF M := by
  by_contra hF
  -- `¬ IsTypeF M` means `κ(M) ≠ ∅`, so there is a `κ(M)`-prime `p`.
  rw [S14.IsTypeF, ← ne_eq, ← Set.nonempty_iff_ne_empty] at hF
  obtain ⟨p, hp⟩ := hF
  -- `p ∈ κ(M)`, so `p` is prime with a line `P ∈ ℰ_p¹(G)`, `P ≤ M`, `M_σ ⊓ C_G(P) ≠ 1`.
  have hpp : p.Prime := hp.1
  obtain ⟨_, P, hP, hPM, _⟩ := hp.2
  haveI : Fact p.Prime := ⟨hpp⟩
  -- `p ∣ |P|` (since `|P| = p`) and `P ≤ M`, so `p ∣ |M|`.
  have hpdvdP : p ∣ Nat.card ↥P := by
    obtain ⟨_, hPcard⟩ := hP
    rw [hPcard, pow_one]
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvdP.trans (Subgroup.card_dvd_of_le hPM), Nat.card_pos.ne'⟩
  -- `p ∤ [M : K.subgroupOf M]` (Hall), so `p ∣ |K.subgroupOf M|`, contradicting `K = ⊥`.
  have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hdvd =>
    hK.2 p (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hp
  have hpKcard : p ∣ Nat.card ↥(K.subgroupOf M) := by
    have hsplit : Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    rcases (Nat.Prime.dvd_mul hpp).mp (hsplit ▸ (Nat.dvd_of_mem_primeFactors hpM)) with h | h
    · exact h
    · exact absurd h hpidx
  rw [hKbot, Subgroup.bot_subgroupOf, Subgroup.card_bot] at hpKcard
  exact (Nat.Prime.one_lt hpp).ne' (Nat.dvd_one.mp hpKcard)

/-- **`K = ⊥ → U` is a `σ(M)'`-complement and `M = U ⊔ M_σ`** (`§14`-independent Hall complement).
When `κ(M) = ∅` (i.e. `K = ⊥`), `(κ(M) ∪ σ(M))' = σ(M)'`, so `U ≤ M` is a `σ(M)'`-Hall subgroup of
`M`; it must coincide with the §12 complement `E` (both `σ(M)'`-Hall in `M`, with `U ≤ E`), and
`M_σ ⊔ E = M`.  Returns the `SubgroupESetup` exhibiting `U` as the complement (`E = U`), which
also feeds the type-`F` half of Lemma 15.1(d)(e) (Theorem 12.12 with `E := U`). -/
theorem subgroupESetup_of_isHall_kappa_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ E₁ E₂ E₃ : Subgroup G, OddOrder.BG.Ch3.S12.SubgroupESetup M U E₁ E₂ E₃ := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  have hF : S14.IsTypeF M := isTypeF_of_isHall_kappa_eq_bot hKM hK hKbot
  have hκ : S14.kappa M = ∅ := hF
  -- `U` is a `σ'`-Hall subgroup of `M`.
  have hUσ' : Ch03.IsHallSubgroup (σᶜ) (U.subgroupOf M) := by
    have heq : (S14.kappa M ∪ σ)ᶜ = σᶜ := by rw [hκ, Set.empty_union]
    rwa [heq] at hU
  have hU_pi : Subgroup.IsPiSubgroup (σᶜ) U := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hp
    exact hUσ'.1 p hp
  -- §12 complement `E ⊇ U`, `σ'`-Hall.
  obtain ⟨E, E₁, E₂, E₃, hsetup, hUE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hUM hU_pi
  -- `U = E`:  `E` is a `σ'`-group, `U` is `σ'`-Hall, and `U ≤ E`, so `|E| ∣ |U|` and `|U| ∣ |E|`.
  have hUEeq : U = E := by
    have hEpi : Ch03.Subgroup.IsPiGroup (σᶜ) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact hE_pi q hq
    have hEdvdU : Nat.card ↥E ∣ Nat.card ↥U := by
      have hd := hUσ'.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hd
    exact Subgroup.eq_of_le_of_card_ge hUE
      (Nat.dvd_antisymm hEdvdU (Subgroup.card_dvd_of_le hUE)).le
  -- transport the `SubgroupESetup` from `E` to `U`.
  exact ⟨E₁, E₂, E₃, hUEeq ▸ hsetup⟩

/-! ## Lemma 15.1: the `U M_sigma` auxiliary structure -/

/-- **Forward lemma: the `§14`-gated structural content of BG Lemma 15.1** (faithful to mmd L4116,
proof deferred).  Bundles the conjuncts of Lemma 15.1 that depend on the still-`sorry` §14 results
(Proposition 14.2(a)'s normal complement `M = K U M_σ`, Theorem 14.7(d)(h)) and Theorem 12.12:

* `K ≠ ⊥ → M' = U M_σ ∧ U` abelian (mmd 15.1(b), Theorem 14.7(h) + Corollary 12.10(b));
* mmd 15.1(c): the `C_{M_σ}(X) ≠ 1` ⟹ `𝓜(C_G(X)) = {M}`, `X` cyclic `τ₂` funnel (Corollary 14.3 +
  Theorem 12.5(d) + Corollary 12.10(b));
* mmd 15.1(d): `⟨C_U(x) | x ∈ M_σ#⟩` abelian (Theorem 12.12(a) for `K = 1`; `U` abelian for
  `K ≠ 1`);
* mmd 15.1(e): the Frobenius subgroup `U₀ M_σ` (Theorem 12.12(b) for `K = 1`; the componentwise
  construction for `K ≠ 1`).

These are isolated here so that `typeP_auxiliary_structure` discharges conjuncts 3 (`M_σ ≤ M'`) and
4 (`M'' ≤ M_σ`) with no `sorry` of its own, citing this lemma only for the §14-gated parts.  Once
§14 (Prop 14.2(a), Thm 14.7(h)) and the Theorem 12.12 `K ≠ 1` Frobenius construction land, this
forward lemma is the single discharge point. -/
theorem typeP_auxiliary_structure_gated [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    (K ≠ ⊥ → derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧ IsMulCommutative ↥U) ∧
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

/-- **BG Lemma 15.1** (mmd L4116): auxiliary structure around the `U`-factor of an
**arbitrary** maximal subgroup `M = KUM_σ`.  The quotient assertion `M'/M_sigma` abelian is
encoded as `M'' <= M_sigma`, avoiding premature quotient API commitments.

Faithfulness fix (Lane G): the previous scaffold added a spurious `IsTypeP M` hypothesis;
mmd Lemma 15.1 holds for every `M ∈ ℳ` (the `K ≠ 1` clauses are guarded inline), and the
general form is what Theorem A(2) and Theorem B cite.

`K ≠ 1` exposure (Lane G): the `K ≠ ⊥` clause now also records `M = K M'` as the relative
complement `IsComplement' (M'.subgroupOf M) (K.subgroupOf M)` together with the `(|M'|, |K|)`
coprimality — both are mmd 15.1(a)+(b) (`M = KUM_σ`, `K ≠ 1 → M' = UM_σ`, with `|K|` a
`κ(M)`-number and `|M'|` a `κ(M)'`-number).  This supplies exactly the hypotheses of
`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'` (the §14-independent `K* ⊆ M''`
engine), so Corollary 15.6's `K* ⊆ M''` clause becomes a single citation once §14 lands.

Faithfulness fix (Lane G 2026-06-15): added `hKM : K ≤ M` and `hUM : U ≤ M`.  In BG, `K` and
`U` are *subgroups of* `M` (Hall `κ(M)`- and `(κ∪σ)'`-subgroups of `M`); without these the
`κ`/`σ`-prime bookkeeping degenerates (e.g. `K ⊓ M = 1` with `K ≠ 1` makes `K ≠ ⊥ → …` false).
The sole caller (`fitting_decomposition`) constructs `K = K'.map M.subtype`, `U = U'.map M.subtype`,
so both containments hold there.

Proof status (Lane G 2026-06-15):
* **Conjunct 3** (`M_σ ≤ M'`, Thm 10.2(c)) and **conjunct 4** (`M'' ≤ M_σ` via
  `derivedDerived_le_Msigma`, Cor 12.10(b)) are **sorry-free** (`#print axioms
  derivedDerived_le_Msigma` = `[propext, Classical.choice, Quot.sound]`), citing no `sorry`.
* **Conjunct 1** (`U M_σ ⊴ M`): the `K = ⊥` branch is sorry-free
  (`subgroupESetup_of_isHall_kappa_eq_bot` ⟹ `U M_σ = M`); the `K ≠ ⊥` branch reduces to
  `M' = U M_σ` (forward lemma).
* **Conjunct 2** (`K` cyclic): `K = ⊥` sorry-free; `K ≠ ⊥` cites the (sorried) §14 `typeP_duality`
  (Thm 14.7(d)), with `IsTypeP M` derived from `K ≠ ⊥` (`isTypeP_of_isHall_kappa_subgroupOf_ne_bot`).
* **Conjunct 5** (`K ≠ ⊥` package): `IsComplement'` + coprimality cite the (sorried) §14
  `typeP_duality` (Thm 14.7(h)); `M' = U M_σ` and `U` abelian come from the forward lemma.
* **Conjuncts 6** (Cor 14.3 funnel — the `X` cyclic-`τ₂` step needs `X` abelian, which routes
  through Hall-`τ₂`-conjugacy for `K = ⊥`), **7**, and **8** are gated on the still-`sorry` §14
  results (Prop 14.2(a) normal complement, Thm 14.7) and Theorem 12.12.

All of the `§14`-structural content is isolated in the single faithful forward lemma
`typeP_auxiliary_structure_gated`; this theorem itself introduces no `sorry` of its own. -/
theorem typeP_auxiliary_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      IsCyclic ↥K ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      derivedInG (derivedInG M) ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      (K ≠ ⊥ → derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
        IsMulCommutative ↥U ∧
        Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
        Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
          (Nat.card ↥(K.subgroupOf M))) ∧
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
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  -- The §14-gated structural facts (forward lemma).
  obtain ⟨hM'gated, hX, hCab, hFrob⟩ :=
    typeP_auxiliary_structure_gated hG hM hKM hUM hK hU
  -- **Conjunct 5** (`K ≠ ⊥` package): `M' = U M_σ`, `U` abelian (forward), plus the complement /
  -- coprimality from Theorem 14.7(h) (`typeP_duality`, with `IsTypeP` from `K ≠ ⊥`).
  have hconj5 : K ≠ ⊥ → derivedInG M = U ⊔ Mσ ∧ IsMulCommutative ↥U ∧
      Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
      Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) := by
    intro hKne
    obtain ⟨hM'eq, hUab⟩ := hM'gated hKne
    -- `IsTypeP M` from `K ≠ ⊥` (`K ≤ M` makes `K.subgroupOf M ≠ ⊥`).
    have hKofne : K.subgroupOf M ≠ ⊥ := by
      rw [ne_eq, Subgroup.subgroupOf_eq_bot]
      exact fun hd => hKne (hd.eq_bot_of_le hKM)
    have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
    obtain ⟨hcompl, hcop, _⟩ := typeP_duality hG hM hP hK hKstar
    exact ⟨hM'eq, hUab, hcompl, hcop⟩
  -- **Conjunct 2** (`K` cyclic).
  have hconj2 : IsCyclic ↥K := by
    by_cases hKne : K = ⊥
    · rw [hKne]; infer_instance
    · have hKofne : K.subgroupOf M ≠ ⊥ := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hd => hKne (hd.eq_bot_of_le hKM)
      have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
      obtain ⟨_, _, _Mstar, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ := typeP_duality hG hM hP hK hKstar
      haveI := hcyc
      exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  -- **Conjunct 1** (`M ≤ N_G(U M_σ)`): `U M_σ = M` (`K = ⊥`) or `= M'` (`K ≠ ⊥`), both normal.
  have hconj1 : M ≤ Subgroup.normalizer ((U ⊔ Mσ : Subgroup G) : Set G) := by
    by_cases hKne : K = ⊥
    · -- `K = ⊥ → U M_σ = M`, so `N_G(U M_σ) = N_G(M) ⊇ M`.
      obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
        subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKne hU
      have hUMσ : U ⊔ Mσ = M := by rw [sup_comm]; exact hsetup.E_compl_sup
      rw [hUMσ]; exact Subgroup.le_normalizer
    · -- `K ≠ ⊥ → U M_σ = M'`, and `M ≤ N_G(M')` (`M' ⊴ M`).
      obtain ⟨hM'eq, _, _, _⟩ := hconj5 hKne
      rw [← hM'eq]
      exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M
  exact ⟨hconj1, hconj2, OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM,
    derivedDerived_le_Msigma hG hM, hconj5, hX, hCab, hFrob⟩

/-! ## Theorem 15.2: `M_F != M_sigma` forces type `P1` -/

/-- **BG Theorem 15.2** (mmd L4112): if `M_F` is strictly smaller than `M_sigma`,
then `M` is type `P1` and has the normal `q`-subgroup / minimal chief factor
structure described in the text. -/
theorem mf_ne_msigma_typeP1_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    S14.IsTypeP1 M ∧
      ∃ Q Q0 D : Subgroup G, ∃ p q : ℕ,
        p.Prime ∧ q.Prime ∧ Nat.card ↥K = p ∧ Nat.card ↥Kstar = q ∧
        q ∈ S14.piSet (MF M) ∧ q ∈ OddOrder.BG.Ch3.S10.beta M ∧
        Kstar ≤ MF M ∧
        Q ≤ MF M ∧ M ≤ Subgroup.normalizer (Q : Set G) ∧
        Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
          (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) ∧
        Group.IsNilpotent ↥D ∧
        Q0 = Q ⊓ Subgroup.centralizer (D : Set G) ∧
        M ≤ Subgroup.normalizer (Q0 : Set G) ∧
        Nat.card ↥(Q.subgroupOf (Q ⊔ Q0)) = q ^ p ∧
        OddOrder.BG.Ch3.S10.Msigma M = derivedInG M ∧
        derivedInG (derivedInG M) ≤ fittingInAmbient M ∧
        -- mmd 15.2(g) "F(M) ⊂ M_σ": the Fitting subgroup is contained in the σ-core.
        fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
        -- mmd 15.2(g) "F(M) = Q C_M(Q)": the Fitting subgroup is the product of the normal
        -- `q`-subgroup `Q` and its `M`-centralizer (`Q` self-centralizing up to `C_M(Q)`).
        fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) ∧
        -- mmd 15.2(f): `M_F ⊇ Q̄`, an elementary abelian section of order `q^p` (rank `p ≥ 3`),
        -- so `M_F` is non-cyclic.  Breaks the 15.5↔15.6 circularity (Corollary 15.6's proof needs
        -- this without citing Corollary 15.5).
        ¬ IsCyclic ↥(MF M) := by
  sorry

/-- **§14-independent Frattini factorization** (BG Corollary 15.3 proof, mmd L4213 "by the
Frattini argument").  If `Q ⊴ M`, `QH ⊴ M`, `Q ∩ H = 1`, `|Q|` and `|H|` are coprime, and `M`
is solvable, then `M = N_M(H)·Q`: every `m ∈ M` factors as `m = n·a` with `n ∈ N_G(H)` and
`a ∈ Q`.

Proof: inside `L = QH`, both `H` and the conjugate `H^{m⁻¹} = m⁻¹Hm` are complements of the
normal subgroup `Q` (coprime orders, so `Q` is a normal Hall subgroup of `L`), hence are
conjugate by some `q ∈ Q` (Schur–Zassenhaus conjugacy, `IsComplement'.exists_conj_of_coprime`):
`H^q = H^{m⁻¹}`.  Then `mq ∈ N_G(H)` and `m = (mq)·q⁻¹`.

This discharges the `hfratt` hypothesis of `mf_hall_centralizer_control_of_inputs` (Cor 15.3)
once Theorem 15.2 supplies the normal `q`-subgroup `Q` with `M_σ/Q` nilpotent (issue 8010). -/
theorem frattini_factorization [Finite G] {M Q H : Subgroup G}
    (hQM : Q ≤ M) (hHM : H ≤ M)
    (hQnorm : (Q.subgroupOf M).Normal)
    (hQHnorm : ((Q ⊔ H).subgroupOf M).Normal)
    (hdisj : Disjoint Q H)
    (hcop : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥H))
    (hsolv : IsSolvable ↥M) :
    ∀ m ∈ M, ∃ n a : G, n ∈ Subgroup.normalizer (H : Set G) ∧ a ∈ Q ∧ m = n * a := by
  classical
  have hQL : Q ≤ Q ⊔ H := le_sup_left
  have hHL : H ≤ Q ⊔ H := le_sup_right
  have hLM : Q ⊔ H ≤ M := sup_le hQM hHM
  have hMNQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnorm
  have hMNL : M ≤ Subgroup.normalizer ((Q ⊔ H : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hQHnorm
  -- `Q ⊴ L` (as a subgroup of `↥(Q ⊔ H)`).
  haveI hQnL : (Q.subgroupOf (Q ⊔ H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr (le_trans hLM hMNQ)
  -- `↥(Q ⊔ H)` is solvable, hence so is its quotient by `Q.subgroupOf (Q ⊔ H)`.
  haveI hLsolv : IsSolvable ↥(Q ⊔ H) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hLM)
  -- A complement-builder inside `↥(Q ⊔ H)`: a `K ≤ L` with `Q ⊓ K = ⊥` and `Q ⊔ K = Q ⊔ H`
  -- complements `Q` in `L`.
  have mk_compl : ∀ K : Subgroup G, K ≤ Q ⊔ H → (Q ⊓ K : Subgroup G) = ⊥ → Q ⊔ K = Q ⊔ H →
      Subgroup.IsComplement' (Q.subgroupOf (Q ⊔ H)) (K.subgroupOf (Q ⊔ H)) := by
    intro K hKL hQK hQKL
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hxQ hxK
      rw [Subgroup.mem_subgroupOf] at hxQ hxK
      have hxQK : (x : G) ∈ Q ⊓ K := ⟨hxQ, hxK⟩
      rw [hQK, Subgroup.mem_bot] at hxQK
      exact Subtype.ext hxQK
    · have hsup : Q.subgroupOf (Q ⊔ H) ⊔ K.subgroupOf (Q ⊔ H) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQL hKL, hQKL, Subgroup.subgroupOf_self]
      have := Subgroup.normal_mul (Q.subgroupOf (Q ⊔ H)) (K.subgroupOf (Q ⊔ H))
      rw [hsup, Subgroup.coe_top] at this
      exact this.symm
  intro m hmM
  have hminvM : m⁻¹ ∈ M := M.inv_mem hmM
  -- `conj m⁻¹` fixes `Q` and `L` (both normal in `M`, and `m⁻¹ ∈ M`).
  have hmiQ : MulAut.conj m⁻¹ • Q = Q := conj_smul_eq_self_of_mem_normalizer (hMNQ hminvM)
  have hmiL : MulAut.conj m⁻¹ • (Q ⊔ H) = Q ⊔ H :=
    conj_smul_eq_self_of_mem_normalizer (hMNL hminvM)
  -- `H' := m⁻¹Hm = conj m⁻¹ • H` is a complement of `Q` in `L`.
  have hH'L : MulAut.conj m⁻¹ • H ≤ Q ⊔ H := by
    rw [← hmiL]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hHL
  have hQH'disj : (Q ⊓ MulAut.conj m⁻¹ • H : Subgroup G) = ⊥ := by
    rw [← hmiQ, ← Subgroup.smul_inf, disjoint_iff.mp hdisj, Subgroup.smul_bot]
  have hQH'sup : Q ⊔ MulAut.conj m⁻¹ • H = Q ⊔ H := by
    rw [← hmiQ, ← Subgroup.smul_sup, hmiQ, hmiL]
  -- The two complements `H` and `H'`.
  have hcompl_H : Subgroup.IsComplement' (Q.subgroupOf (Q ⊔ H)) (H.subgroupOf (Q ⊔ H)) :=
    mk_compl H hHL (disjoint_iff.mp hdisj) rfl
  have hcompl_H' : Subgroup.IsComplement' (Q.subgroupOf (Q ⊔ H))
      ((MulAut.conj m⁻¹ • H).subgroupOf (Q ⊔ H)) :=
    mk_compl (MulAut.conj m⁻¹ • H) hH'L hQH'disj hQH'sup
  -- Coprimality `(|Q.subgroupOf L|, (Q.subgroupOf L).index)`: index `= |H|` by `hcompl_H`.
  have hcardQ : Nat.card ↥(Q.subgroupOf (Q ⊔ H)) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  have hcardH : Nat.card ↥(H.subgroupOf (Q ⊔ H)) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hcop' : Nat.Coprime (Nat.card ↥(Q.subgroupOf (Q ⊔ H)))
      (Q.subgroupOf (Q ⊔ H)).index := by
    rw [hcardQ, hcompl_H.symm.index_eq_card, hcardH]; exact hcop
  -- Schur–Zassenhaus conjugacy: `H` and `H'` are conjugate by some `q' ∈ Q.subgroupOf L`.
  obtain ⟨q', hq'mem, hq'eq⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop' (Or.inr inferInstance) hcompl_H hcompl_H'
  -- Lift the conjugacy back to `G` along `L.subtype`: `conj q'.val • H = conj m⁻¹ • H`.
  set q : G := (q' : G) with hqdef
  have hqQ : q ∈ Q := Subgroup.mem_subgroupOf.mp hq'mem
  have hintertwine : (Q ⊔ H).subtype.comp (MulAut.conj q').toMonoidHom =
      ((MulAut.conj q).toMonoidHom).comp (Q ⊔ H).subtype := by
    ext x; rfl
  have hmapH : (H.subgroupOf (Q ⊔ H)).map (Q ⊔ H).subtype = H := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hHL]
  have hmapH' : ((MulAut.conj m⁻¹ • H).subgroupOf (Q ⊔ H)).map (Q ⊔ H).subtype =
      MulAut.conj m⁻¹ • H := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hH'L]
  have hlift : MulAut.conj q • H = MulAut.conj m⁻¹ • H := by
    have hlifted := congrArg (·.map (Q ⊔ H).subtype) hq'eq
    simp only at hlifted
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map, hmapH, hmapH'] at hlifted
    rw [Subgroup.pointwise_smul_def]
    exact hlifted
  -- `n := m·q ∈ N_G(H)`, `a := q⁻¹ ∈ Q`, `m = n·a`.
  refine ⟨m * q, q⁻¹, ?_, Q.inv_mem hqQ, by group⟩
  apply mem_normalizer_of_conj_smul_eq_self
  rw [map_mul, mul_smul, hlift, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

/-- **§14-independent assembly engine for BG Corollary 15.3** (mmd L4204).  Packages the
*logic* of Corollary 15.3 with its `§14`/`§15` inputs taken as named hypotheses, so that once
those land (Lane H), the wrapper `mf_hall_centralizer_control` discharges each by a single
citation and applies this skeleton (the gated-endpoint pattern, cf.
`typeP_kstar_in_mf_of_inputs`).  Hypothesis provenance (mmd L4209-4213):

* `ha` (the `C_M(H) = C_{M_σ}(H)·X` decomposition) ← Proposition 14.2(b1)(e) (`C_M(H)` is a
  `κ(M)'`-group) + Lemma 15.1(c) (the `X` cyclic-`τ₂` extraction);
* `hconj` (any `G`-conjugacy of `H`-elements is realized inside `M`) ← Theorem 14.4 (find
  `c ∈ C_G(x)` with `M^{gc} = M`) + self-normalizing `N_G(M) = M`
  (`normalizer_eq_self_of_mem_maximalSubgroups`); the witness is `m = gc`;
* `hfratt` (the Frattini factorization `M = N_M(H)·Q` when `H ⋬ M`) ← Theorem 15.2's normal
  `Q = O_q(M)` with `M_σ/Q` nilpotent (so `QH ⊴ M`, `Q ∩ H = 1`) + the Frattini argument.

The nontrivial step is the `H ⋬ M` glue: writing the realizing `m = n·a` (`n ∈ N_M(H)`,
`a ∈ Q`), the element `w = a x a⁻¹` lies in `H` (it is `n⁻¹ y n`) and `w x⁻¹ ∈ Q` (`Q ⊴ M`,
`x ∈ M`), so `w x⁻¹ ∈ Q ∩ H = 1`, whence `w = x` and `y = n x n⁻¹`. -/
theorem mf_hall_centralizer_control_of_inputs [Finite G]
    {M H : Subgroup G} (hHM : H ≤ M)
    (ha : ∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X)
    (hconj : ∀ x ∈ H, ∀ y ∈ H, ∀ g : G, y = g * x * g⁻¹ → ∃ m ∈ M, y = m * x * m⁻¹)
    (hfratt : ¬ (H.subgroupOf M).Normal → ∃ Q : Subgroup G, Q ≤ M ∧ (Q.subgroupOf M).Normal ∧
      Disjoint Q H ∧
      ∀ m ∈ M, ∃ n a : G, n ∈ Subgroup.normalizer (H : Set G) ∧ a ∈ Q ∧ m = n * a) :
    (∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X) ∧
    (∀ x ∈ H, ∀ y ∈ H, (∃ g : G, y = g * x * g⁻¹) →
      ∃ n ∈ Subgroup.normalizer (H : Set G), y = n * x * n⁻¹) := by
  refine ⟨ha, ?_⟩
  rintro x hx y hy ⟨g, hg⟩
  obtain ⟨m, hmM, hmy⟩ := hconj x hx y hy g hg
  by_cases hHnorm : (H.subgroupOf M).Normal
  · -- `H ⊴ M`:  `m ∈ M ⊆ N_G(H)`, so `n = m` works directly.
    exact ⟨m, ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnorm) hmM, hmy⟩
  · -- `H ⋬ M`:  Frattini-factor `m = n·a` and run the commutator argument.
    obtain ⟨Q, hQM, hQnorm, hQH, hfact⟩ := hfratt hHnorm
    obtain ⟨n, a, hnN, haQ, hmna⟩ := hfact m hmM
    refine ⟨n, hnN, ?_⟩
    -- `y = n · (a x a⁻¹) · n⁻¹`.
    have hyw : y = n * (a * x * a⁻¹) * n⁻¹ := by rw [hmy, hmna]; group
    -- `w := a x a⁻¹ = n⁻¹ y n ∈ H`.
    have hwH : a * x * a⁻¹ ∈ H := by
      have hmem := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (H : Set G)).inv_mem hnN) y).mp hy
      rw [inv_inv] at hmem
      have hweq : a * x * a⁻¹ = n⁻¹ * y * n := by rw [hyw]; group
      rw [hweq]; exact hmem
    -- `w x⁻¹ = a (x a⁻¹ x⁻¹) ∈ Q`  (`Q ⊴ M`, `x ∈ M`).
    have hwxQ : (a * x * a⁻¹) * x⁻¹ ∈ Q := by
      have hxnorm : x ∈ Subgroup.normalizer (Q : Set G) :=
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnorm) (hHM hx)
      have hxax : x * a⁻¹ * x⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hxnorm a⁻¹).mp (Q.inv_mem haQ)
      have hrw : (a * x * a⁻¹) * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
      rw [hrw]; exact Subgroup.mul_mem _ haQ hxax
    -- `w x⁻¹ ∈ Q ∩ H = ⊥`, so `w = x` and `y = n x n⁻¹`.
    have hwxH : (a * x * a⁻¹) * x⁻¹ ∈ H := Subgroup.mul_mem _ hwH (H.inv_mem hx)
    have hwx1 : (a * x * a⁻¹) * x⁻¹ = 1 := by
      have : (a * x * a⁻¹) * x⁻¹ ∈ Q ⊓ H := Subgroup.mem_inf.mpr ⟨hwxQ, hwxH⟩
      rw [disjoint_iff.mp hQH] at this
      exact Subgroup.mem_bot.mp this
    have hwx : a * x * a⁻¹ = x := by
      have := mul_eq_one_iff_eq_inv.mp hwx1
      rw [this]; group
    rw [hyw, hwx]

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

/-- **General helper (§14-independent, reusable).**  A nonidentity maximal subgroup of a minimal
simple group is self-normalizing: `N_G(M) = M`.  If `M ⊊ N_G(M)`, maximality forces `N_G(M) = G`,
so `M ⊴ G`; simplicity then gives `M = ⊥` or `M = ⊤`, both excluded.  This is the step of BG
Corollary 15.3(b) that turns `M^{gc} = M` into `gc ∈ M`. -/
theorem normalizer_eq_self_of_mem_maximalSubgroups [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMne : M ≠ ⊥) :
    Subgroup.normalizer M = M := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp
      ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal M hnorm with hbot | htop
    · exact absurd hbot hMne
    · exact absurd htop (mem_maximalSubgroups.mp hM).1

/-- **§15 helper (§14-independent, reusable).**  The `G`-normalizer of `M_σ` is `M`:
`N_G(M_σ) = M`.  Since `M_σ = O_{σ(M)}(M)` is normal in `M` (`le_normalizer_opiCoreInG`),
`M ≤ N_G(M_σ)`; if the containment were proper, maximality would force `N_G(M_σ) = G`, so
`M_σ ⊴ G`, and simplicity would give `M_σ ∈ {⊥, ⊤}` — both excluded (`Msigma_ne_bot`,
`M_σ ≤ M ⊊ G`).  This turns the `N_G(M_σ)`-fusion of Corollary 15.3(b) at `H := M_σ` into the
`M`-fusion of BG Theorem D(1). -/
theorem normalizer_Msigma_eq_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) = M := by
  have hle : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  refine le_antisymm ?_ hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : (OddOrder.BG.Ch3.S10.Msigma M).Normal :=
      Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
    · exact absurd hbot (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    · exact absurd (top_le_iff.mp (htop ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
        (mem_maximalSubgroups.mp hM).1

/-- **General helper (§14-independent, reusable).**  A subgroup `K` of a finite group that
contains a full Sylow `p`-subgroup for every prime `p` is the whole group.  (No nilpotency:
each Sylow's order is the `p`-part of `|G|`, so `K.index` is divisible by no prime and equals `1`.)
This is the assembly step of BG Corollary 15.4 — once every Sylow subgroup of the nilpotent Hall
subgroup `H` has been placed inside `M_σ`, this forces `H ⊆ M_σ` (applied inside `↥H`). -/
theorem eq_top_of_forall_sylow_le {H : Type*} [Group H] [Finite H] {K : Subgroup H}
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p H), (P : Subgroup H) ≤ K) : K = ⊤ := by
  rw [← Subgroup.index_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  haveI := Fact.mk hp
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  exact P.not_dvd_index (hpdvd.trans (Subgroup.index_dvd_of_le (h p P)))

/-- **§15 helper (§14-independent, reusable).**  A nonidentity Sylow `p`-subgroup `S` of `G`
whose `G`-normalizer lies in a maximal subgroup `M` is contained in `M_σ`.  This is the σ-theory
content of the first step of BG Corollary 15.4 ("`S ⊆ M_σ`"): `N_G(S) ≤ M` exhibits `S` as a
Sylow witness for `p ∈ σ(M)` (`mem_sigma_iff`), and `M_σ`, the `σ(M)`-Hall subgroup of `M`
(`Msigma_isHall`), absorbs the `σ(M)`-subgroup `S` (`sigma_subgroup_le_Msigma_of_isHall`). -/
theorem sylow_le_Msigma_of_normalizer_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hSne : (S : Subgroup G) ≠ ⊥)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M) :
    (S : Subgroup G) ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  have hSM : (S : Subgroup G) ≤ M := le_trans Subgroup.le_normalizer hN
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := (S : Subgroup G))).mp S.isPGroup'
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hSne hn
  have hpdvdM : p ∣ Nat.card ↥M := by
    have h1 : Nat.card (S : Subgroup G) ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hSM
    rw [hn] at h1
    exact (dvd_pow_self p hn0).trans h1
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
    exact ⟨Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdM, Nat.card_pos.ne'⟩,
      S.subtype hSM, by
        rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSM]; exact hN⟩
  refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) hSM (fun q hq => ?_)
  rw [hn, Nat.primeFactors_prime_pow hn0 Fact.out, Finset.mem_singleton] at hq
  exact hq ▸ hpσ

/-- **§15 helper for BG Corollary 15.4.**  A full Sylow `p`-subgroup `S` of `G` contained in
`M_σ` is a `π(S)`-Hall subgroup of `M_σ` (where `π(S) = {p}`).  This packages the hypothesis
shape `mf_hall_centralizer_control` (Corollary 15.3) requires when instantiated at `H := S`:
`S` is a `p`-group so `π(S) = {p}`, and `S` is a Sylow `p` of `M_σ` (a Sylow of `G` inside a
subgroup is a Sylow of that subgroup), so `p ∤ [M_σ : S]`. -/
theorem sylow_isHall_piSet_subgroupOf_Msigma [Finite G] {M : Subgroup G}
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (hSne : (S : Subgroup G) ≠ ⊥)
    (hSMσ : (S : Subgroup G) ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    Ch03.IsHallSubgroup (S14.piSet (S : Subgroup G))
      ((S : Subgroup G).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
  -- `π(S) = {p}`: `S` is a nontrivial `p`-group.
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := (S : Subgroup G))).mp S.isPGroup'
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [pow_zero, Subgroup.card_eq_one] at hn; exact hSne hn
  have hpiS : S14.piSet (S : Subgroup G) = {p} := by
    ext r
    rw [S14.piSet, Set.mem_setOf_eq, hn, Nat.primeFactors_prime_pow hn0 Fact.out,
      Finset.mem_singleton, Set.mem_singleton_iff]
  -- `card (S.subgroupOf M_σ) = card S`, so its prime factors are `{p} = π(S)`.
  have hcardK : Nat.card ↥((S : Subgroup G).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) =
      Nat.card ↥(S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSMσ).toEquiv
  -- `p ∤ [M_σ : S]`: `S` restricts to a Sylow `p`-subgroup of `M_σ`.
  have hpndvd : ¬ p ∣ ((S : Subgroup G).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := by
    have := (S.subtype hSMσ).not_dvd_index
    rwa [Sylow.coe_subtype] at this
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rw [hpiS]; rw [hcardK, hn, Nat.primeFactors_prime_pow hn0 Fact.out,
      Finset.mem_singleton] at hr; exact hr
  · rw [hpiS, Set.mem_singleton_iff]
    rintro rfl; exact hpndvd (Nat.mem_primeFactors.mp hr).2.1

/-- **KEY LEMMA for BG Corollary 15.4** (mmd L4215, the bracketed step of the proof).  Let
`M` be a maximal subgroup, `S` a nonidentity full Sylow `p`-subgroup of `G` with `S ≤ M_σ`, and
`Q` a Sylow `q`-subgroup of `M` whose image in `G` centralizes `S` (i.e. lies in `C_M(S)`).
Then `Q ≤ M_σ`.

Proof (BG): by Corollary 15.3(a) (`mf_hall_centralizer_control` at `H := S`),
`C_M(S) = (C_{M_σ}(S)) ⊔ X` with `X` cyclic and `π(X) ⊆ τ₂(M)`.  Write `A = C_{M_σ}(S)`, a
`σ(M)`-group; `A ⊴ C := C_M(S)`.  If `q ∈ σ(M)`, then `Q ≤ M_σ` since `M_σ` is the normal Hall
`σ(M)`-subgroup.  If `q ∉ σ(M)`: `Q ⊓ A = 1` (coprime), so `Q` embeds into the cyclic group
`C/A` (a quotient of `X`), forcing `Q` cyclic **and** `q ∣ |X|`, hence `q ∈ τ₂(M)`, i.e.
`r_q(M) = 2`.  But `Q` is a Sylow `q` of `M`, so `r_q(M) = r_q(Q) ≤ 1` (cyclic) — contradiction.
So `q ∈ σ(M)` and `Q ≤ M_σ`. -/
theorem sylow_le_Msigma_of_le_centralizer_sylow [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (hSne : (S : Subgroup G) ≠ ⊥)
    (hSMσ : (S : Subgroup G) ≤ OddOrder.BG.Ch3.S10.Msigma M)
    {q : ℕ} [Fact q.Prime] (Q : Sylow q ↥M) (hQne : (Q : Subgroup ↥M) ≠ ⊥)
    (hQC : (Q : Subgroup ↥M).map M.subtype ≤ Subgroup.centralizer (S : Set G)) :
    (Q : Subgroup ↥M).map M.subtype ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  set Qbar : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hQbar
  have hQbar_le_M : Qbar ≤ M := Subgroup.map_subtype_le _
  -- `Qbar` is a `q`-group, nontrivial.
  have hQbar_pg : IsPGroup q ↥Qbar :=
    Q.isPGroup'.map M.subtype
  have hcardQbar : Nat.card ↥Qbar = Nat.card ↥(Q : Subgroup ↥M) := by
    rw [hQbar, Subgroup.card_map_of_injective M.subtype_injective]
  have hQbar_ne : Qbar ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardQbar
    exact hQne (Subgroup.card_eq_one.mp hcardQbar.symm)
  obtain ⟨m, hm⟩ := hQbar_pg.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl; rw [pow_zero] at hm; exact hQbar_ne (Subgroup.card_eq_one.mp hm)
  have hq_dvd_Qbar : q ∣ Nat.card ↥Qbar := hm ▸ dvd_pow_self q hm0
  -- Whether `q ∈ σ(M)`.
  by_cases hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M
  · -- `q ∈ σ(M)`: `Qbar` is a `σ(M)`-group inside `M`, hence `≤ M_σ`.
    refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) hQbar_le_M (fun r hr => ?_)
    have hrq : r = q := by
      have hrdvd : r ∣ q ^ m := hm ▸ (Nat.mem_primeFactors.mp hr).2.1
      exact (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hr) Fact.out).mp
        ((Nat.prime_of_mem_primeFactors hr).dvd_of_dvd_pow hrdvd)
    exact hrq ▸ hqσ
  · -- `q ∉ σ(M)`: derive a contradiction (so this branch is vacuous, but we conclude `≤ M_σ`).
    exfalso
    -- Corollary 15.3(a): `C_M(S) = C_{M_σ}(S) ⊔ X`, `X` cyclic with `π(X) ⊆ τ₂(M)`.
    obtain ⟨⟨X, hXcyc, hXτ₂, hCeq⟩, _⟩ :=
      mf_hall_centralizer_control hG hM
        (sylow_isHall_piSet_subgroupOf_Msigma S hSne hSMσ) hSne
    set A : Subgroup G := Subgroup.centralizer (S : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M with hA
    set C : Subgroup G := Subgroup.centralizer (S : Set G) ⊓ M with hC
    -- `Qbar ≤ C`.
    have hQbar_C : Qbar ≤ C := le_inf hQC hQbar_le_M
    -- `A ≤ C`.
    have hA_C : A ≤ C := inf_le_inf_left _ (OddOrder.BG.Ch3.S10.Msigma_le M)
    -- `A ⊴ C`: `C` normalizes `A = C_G(S) ⊓ M_σ` (centralizer normalizes itself, `M` normalizes
    -- `M_σ`).
    have hC_norm_A : C ≤ Subgroup.normalizer A := by
      have h1 : C ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G)) :=
        inf_le_left.trans Subgroup.le_normalizer
      have h2 : C ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
        inf_le_right.trans
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    haveI hA_normal : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr
        (by rw [inf_eq_left.mpr hA_C]; exact hC_norm_A)
    -- `q ∤ |A|`: `A ≤ M_σ` is a `σ(M)`-group and `q ∉ σ(M)`.
    have hq_ndvd_A : ¬ q ∣ Nat.card ↥A := by
      intro hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out,
          hdvd.trans (Subgroup.card_dvd_of_le (inf_le_right)), Nat.card_pos.ne'⟩))
    -- `Qbar ⊓ A = ⊥`: coprime orders.
    have hQbar_inf_A : Qbar ⊓ A = ⊥ := by
      have hcop : Nat.Coprime (Nat.card ↥Qbar) (Nat.card ↥A) := by
        rw [hm, Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hm0)]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hq_ndvd_A
      exact Subgroup.inf_eq_bot_of_coprime hcop
    -- `X ≤ C` (from `C = A ⊔ X`).
    have hX_C : X ≤ C := le_sup_right.trans hCeq.ge
    -- Work inside `↥C`, with `a = A∩C`, `x = X∩C`, `Qc = Qbar∩C` as subgroups of `↥C`.
    -- `a ⊔ x = ⊤`: `(A ⊔ X) ∩ C = C ∩ C = ⊤`.
    have haxtop : A.subgroupOf C ⊔ X.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA_C hX_C, show A ⊔ X = C from hCeq.symm,
        Subgroup.subgroupOf_self]
    -- `Qc ⊓ a = ⊥`.
    have hQc_inf_a : Qbar.subgroupOf C ⊓ A.subgroupOf C = ⊥ := by
      rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hQbar_inf_A,
        MonoidHom.comap_bot]
      exact C.ker_subtype
    -- The composite `Qc ↪ ↥C ⧸ a` is injective.
    have hinj : Function.Injective
        ((QuotientGroup.mk' (A.subgroupOf C)).comp (Qbar.subgroupOf C).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      have hmem : (Qbar.subgroupOf C).subtype y ∈ Qbar.subgroupOf C ⊓ A.subgroupOf C :=
        ⟨y.2, hy⟩
      rw [hQc_inf_a, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext hmem
    -- `↥C ⧸ a` is cyclic: it is a quotient image of the cyclic `↥x` (image of `X ≤ C`).
    haveI hxcyc : IsCyclic ↥(X.subgroupOf C) := by
      haveI : IsCyclic ↥X := hXcyc
      exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hX_C).symm.surjective
    haveI hquot_cyc : IsCyclic (↥C ⧸ A.subgroupOf C) := by
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (A.subgroupOf C)).comp (X.subgroupOf C).subtype) := by
        rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
        have h1 : (A.subgroupOf C ⊔ X.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) =
            ⊤ := by
          rw [haxtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        have hkerbot : (A.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        rw [Subgroup.map_sup, hkerbot, bot_sup_eq] at h1
        rw [h1]
      exact isCyclic_of_surjective _ hsurj
    -- Hence `Qc` is cyclic (iso to a subgroup of the cyclic `↥C ⧸ a`).
    haveI hQc_cyc : IsCyclic ↥(Qbar.subgroupOf C) :=
      isCyclic_of_surjective _ (MonoidHom.ofInjective hinj).symm.surjective
    -- `Qbar` is cyclic (`Qbar ≅ Qc`).
    haveI hQbar_cyc : IsCyclic ↥Qbar :=
      isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hQbar_C).surjective
    -- `Q` is cyclic (`Q ≅ Qbar`).
    haveI hQ_cyc : IsCyclic ↥(Q : Subgroup ↥M) :=
      isCyclic_of_surjective _
        (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm.surjective
    -- `q ∈ τ₂(M)`: `q ∣ |Qbar| ∣ a.index ∣ |X|`, and `π(X) ⊆ τ₂(M)`.
    have hcardQc : Nat.card ↥(Qbar.subgroupOf C) = Nat.card ↥Qbar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQbar_C).toEquiv
    have hdvd1 : Nat.card ↥Qbar ∣ (A.subgroupOf C).index := by
      rw [← hcardQc, Subgroup.index_eq_card]
      exact Subgroup.card_dvd_of_injective _ hinj
    have hdvd2 : (A.subgroupOf C).index ∣ Nat.card ↥X := by
      have hidx : (A.subgroupOf C).index = (A.subgroupOf C).relIndex (X.subgroupOf C) := by
        rw [← Subgroup.relIndex_top_right, ← haxtop, Subgroup.relIndex_sup_left]
      have hcardx : Nat.card ↥(X.subgroupOf C) = Nat.card ↥X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_C).toEquiv
      rw [hidx, ← hcardx]
      exact Subgroup.relIndex_dvd_card (A.subgroupOf C) (X.subgroupOf C)
    have hq_dvd_X : q ∣ Nat.card ↥X := (hq_dvd_Qbar.trans hdvd1).trans hdvd2
    have hqτ₂ : q ∈ tau2 M := hXτ₂ (Nat.mem_primeFactors.mpr ⟨Fact.out, hq_dvd_X, Nat.card_pos.ne'⟩)
    -- Contradiction: `r_q(M) = 2` (from `τ₂`) but `Q` is a cyclic Sylow `q` of `M`.
    have hrank2 : pRank ↥M q = 2 := ((mem_tau2_iff M q).mp hqτ₂).2
    have hrankQ : pRank ↥(Q : Subgroup ↥M) q = 2 := (pRank_sylow_eq Q).trans hrank2
    obtain ⟨B, _, hBnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank
        (G := ↥(Q : Subgroup ↥M)) (p := q) (le_of_eq hrankQ.symm)
    exact hBnc (Subgroup.isCyclic B)

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
  classical
  haveI := hHnil
  -- Step 1: pick a prime `p₀ ∣ |H|` and the (unique, normal) Sylow `p₀`-subgroup `S` of `↥H`.
  obtain ⟨p₀, hp₀⟩ : ∃ p, p ∈ (Nat.card ↥H).primeFactors := by
    have hne1 : Nat.card ↥H ≠ 1 := fun h => hHne (Subgroup.card_eq_one.mp h)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩⟩
  haveI : Fact p₀.Prime := ⟨Nat.prime_of_mem_primeFactors hp₀⟩
  set S : Sylow p₀ ↥H := default with hSdef
  set Sbar : Subgroup G := (S : Subgroup ↥H).map H.subtype with hSbar
  have hSbar_le_H : Sbar ≤ H := Subgroup.map_subtype_le _
  have hS_normal : (S : Subgroup ↥H).Normal := Ch01.Sylow.normal_of_isNilpotent S
  -- `S ≠ ⊥`: `p₀ ∣ |↥H|` so `p₀ ∣ |S|`.
  have hn1 : (Nat.card ↥H).factorization p₀ ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne'
      (Nat.mem_primeFactors.mp hp₀).2.1).ne'
  have hScard_dvd : p₀ ∣ Nat.card ↥(S : Subgroup ↥H) := by
    rw [S.card_eq_multiplicity]; exact dvd_pow_self p₀ hn1
  have hcardSbar : Nat.card ↥Sbar = Nat.card ↥(S : Subgroup ↥H) := by
    rw [hSbar, Subgroup.card_map_of_injective H.subtype_injective]
  have hSbar_ne : Sbar ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardSbar
    rw [← hcardSbar] at hScard_dvd
    exact (Nat.Prime.one_lt Fact.out).ne (Nat.dvd_one.mp hScard_dvd).symm
  -- Step 2: `Sbar` is a full Sylow `p₀`-subgroup of `G` (since `H` is a Hall subgroup of `G`).
  have hSbar_pg : IsPGroup p₀ ↥Sbar := S.isPGroup'.map H.subtype
  have hSbarOf : Sbar.subgroupOf H = (S : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hp₀_ndvd_index : ¬ p₀ ∣ Sbar.index := by
    have hrel : Sbar.relIndex H * H.index = Sbar.index := Subgroup.relIndex_mul_index hSbar_le_H
    rw [← hrel]
    refine (Nat.Prime.not_dvd_mul Fact.out ?_ ?_)
    · -- `p₀ ∤ [H : Sbar] = [↥H : S]`.
      rw [Subgroup.relIndex, hSbarOf]; exact S.not_dvd_index
    · -- `p₀ ∤ [G : H]` because `p₀ ∈ π(H)` and `H` is Hall.
      intro hdvd
      exact (hHall.2 p₀ (Nat.mem_primeFactors.mpr
        ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩)) hp₀
  -- Package `Sbar` as a Sylow `p₀`-subgroup of `G`.
  set Sp : Sylow p₀ G := hSbar_pg.toSylow hp₀_ndvd_index with hSp
  have hSpcoe : (Sp : Subgroup G) = Sbar := hSbar_pg.toSylow_coe hp₀_ndvd_index
  -- Step 3: choose `M ∈ ℳ(N_G(Sbar))`.
  have hNlt : Subgroup.normalizer ((Sp : Subgroup G) : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hSpnormal : (Sp : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hSpnormal with hbot | htop'
    · exact hSbar_ne (hSpcoe ▸ hbot)
    · haveI : IsSolvable ↥(Sp : Subgroup G) := by
        haveI := Sp.isPGroup'.isNilpotent; infer_instance
      rw [htop'] at this
      haveI := this
      exact hG.notSolvable (solvable_of_surjective
        (f := (Subgroup.topEquiv (G := G)).toMonoidHom) (Subgroup.topEquiv (G := G)).surjective)
  obtain ⟨M, hMco, hNM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer ((Sp : Subgroup G) : Set G))).resolve_left
      hNlt.ne
  have hM : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMco
  have hSbar_le_M : Sbar ≤ M := hSpcoe ▸ (Subgroup.le_normalizer.trans hNM)
  -- `Sbar ≤ M_σ`.
  have hSbar_Mσ : Sbar ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    have := sylow_le_Msigma_of_normalizer_le hG hM Sp (hSpcoe ▸ hSbar_ne) hNM
    rwa [hSpcoe] at this
  -- Step 4: every Sylow subgroup of `↥H` maps into `M_σ`.  Then `H ≤ M_σ`.
  -- Suffices: `(Msigma M).subgroupOf H = ⊤`, i.e. each Sylow of `↥H` lies in `(Msigma M).subgroupOf H`.
  have hH_Mσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    have htop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf H = ⊤ := by
      refine eq_top_of_forall_sylow_le (fun q _ P => ?_)
      -- Goal: `(P : Subgroup ↥H) ≤ (Msigma M).subgroupOf H`, i.e. `P.map H.subtype ≤ Msigma M`.
      rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap]
      set Pbar : Subgroup G := (P : Subgroup ↥H).map H.subtype with hPbar
      have hPbar_le_H : Pbar ≤ H := Subgroup.map_subtype_le _
      have hP_normal : (P : Subgroup ↥H).Normal := Ch01.Sylow.normal_of_isNilpotent P
      -- If `P` is trivial the goal is immediate.
      by_cases hPtriv : (P : Subgroup ↥H) = ⊥
      · rw [hPbar, hPtriv, Subgroup.map_bot]; exact bot_le
      by_cases hqp : q = p₀
      · -- `q = p₀`: `P = S` (unique Sylow of nilpotent `↥H`), so `Pbar = Sbar ≤ M_σ`.
        subst hqp
        haveI : Unique (Sylow q ↥H) := P.unique_of_normal hP_normal
        have hPS : P = S := Subsingleton.elim _ _
        rw [hPbar, hPS]; exact hSbar_Mσ
      · -- `q ≠ p₀`: `[P, S] = 1`, so `Pbar ≤ C_G(Sbar) ≤ M`, a Sylow `q` of `M`; KEY LEMMA.
        have hdisj : Disjoint (P : Subgroup ↥H) (S : Subgroup ↥H) :=
          IsPGroup.disjoint_of_ne q p₀ hqp _ _ P.isPGroup' S.isPGroup'
        -- `Pbar ≤ C_G(Sbar)`.
        have hPbar_cent : Pbar ≤ Subgroup.centralizer (Sbar : Set G) := by
          rw [hPbar]
          rintro _ ⟨z, hz, rfl⟩
          rw [Subgroup.mem_centralizer_iff]
          rintro _ ⟨w, hw, rfl⟩
          have hcomm : Commute z w :=
            Subgroup.commute_of_normal_of_disjoint _ _ hP_normal hS_normal hdisj z w hz hw
          have hcg : (H.subtype z) * (H.subtype w) = (H.subtype w) * (H.subtype z) := by
            rw [← map_mul, ← map_mul, hcomm]
          exact hcg.symm
        -- `Pbar ≤ M`.
        have hPbar_M : Pbar ≤ M :=
          hPbar_cent.trans ((Subgroup.centralizer_le_normalizer _).trans (hSpcoe ▸ hNM))
        -- `Pbar` is a nontrivial full Sylow `q` of `G`.
        have hPbar_pg : IsPGroup q ↥Pbar := P.isPGroup'.map H.subtype
        have hcardP : Nat.card ↥Pbar = Nat.card ↥(P : Subgroup ↥H) := by
          rw [hPbar, Subgroup.card_map_of_injective H.subtype_injective]
        have hPbar_ne : Pbar ≠ ⊥ := by
          intro hb
          rw [hb, Subgroup.card_bot] at hcardP
          exact hPtriv (Subgroup.card_eq_one.mp hcardP.symm)
        obtain ⟨c, hc⟩ := hPbar_pg.exists_card_eq
        have hc0 : c ≠ 0 := by
          rintro rfl; rw [pow_zero] at hc; exact hPbar_ne (Subgroup.card_eq_one.mp hc)
        have hqdvdH : q ∣ Nat.card ↥H :=
          (hc ▸ dvd_pow_self q hc0).trans (Subgroup.card_dvd_of_le hPbar_le_H)
        have hPbarOf : Pbar.subgroupOf H = (P : Subgroup ↥H) :=
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
        have hq_ndvd : ¬ q ∣ Pbar.index := by
          have hrel : Pbar.relIndex H * H.index = Pbar.index := Subgroup.relIndex_mul_index hPbar_le_H
          rw [← hrel]
          refine Nat.Prime.not_dvd_mul Fact.out ?_ ?_
          · rw [Subgroup.relIndex, hPbarOf]; exact P.not_dvd_index
          · intro hdvd
            exact (hHall.2 q (Nat.mem_primeFactors.mpr
              ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩))
              (Nat.mem_primeFactors.mpr ⟨Fact.out, hqdvdH, Nat.card_pos.ne'⟩)
        set Pp : Sylow q G := hPbar_pg.toSylow hq_ndvd with hPp
        have hPpcoe : (Pp : Subgroup G) = Pbar := hPbar_pg.toSylow_coe hq_ndvd
        -- Restrict `Pp` to a (nontrivial) Sylow `q`-subgroup `Q'` of `↥M`.
        obtain ⟨Q', hQ'⟩ :=
          OddOrder.BG.Ch3.S10.exists_sylow_subgroupOf_of_le Pp (hPpcoe ▸ hPbar_M)
        have hQ'map : (Q' : Subgroup ↥M).map M.subtype = Pbar := by
          rw [hQ', Subgroup.map_subgroupOf_eq_of_le (hPpcoe ▸ hPbar_M), hPpcoe]
        have hQ'ne : (Q' : Subgroup ↥M) ≠ ⊥ := by
          intro hb
          rw [hb, Subgroup.map_bot] at hQ'map
          exact hPbar_ne hQ'map.symm
        -- KEY LEMMA: `Q'.map M.subtype ≤ M_σ`.
        have hQ'C : (Q' : Subgroup ↥M).map M.subtype ≤ Subgroup.centralizer (Sp : Set G) := by
          have hset : (Sp : Set G) = (Sbar : Set G) := SetLike.coe_set_eq.mpr hSpcoe
          rw [hQ'map, hset]; exact hPbar_cent
        have hfinal := sylow_le_Msigma_of_le_centralizer_sylow hG hM Sp (hSpcoe ▸ hSbar_ne)
          (hSpcoe ▸ hSbar_Mσ) Q' hQ'ne hQ'C
        rw [hQ'map] at hfinal
        rw [hPbar]; exact hfinal
    intro y hy
    have hmem : (⟨y, hy⟩ : ↥H) ∈ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf H := by
      rw [htop]; trivial
    exact hmem
  exact ⟨M, mem_maximalSubgroupsContaining.mpr
    ⟨hMco, hH_Mσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)⟩, hH_Mσ⟩

/-! ### Corollary 15.5 helpers (`§14`-independent, reusable)

The `F(M) = F(M_σ) × O_{σ'}(F(M))` decomposition splits into two case-independent pieces:
the nilpotent Hall splitting of `F(M)` (`opiCoreInG_sup_compl_eq_of_isNilpotent` applied to the
nilpotent `F(M)`), and the identification `O_σ(F(M)) = F(M_σ)` (`opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma`, BG Corollary 15.5's "Lemma 1").
The `τ₂`/cyclic content of the `σ'`-part is then supplied case by case in `fitting_decomposition`. -/

/-- **Ambient nilpotent Hall splitting**: for a finite nilpotent subgroup `H`, the ambient
realizations of `O_π(H)` and `O_{π'}(H)` join to all of `H`.  (Image under `H.subtype` of the
`↥H`-internal `O_π(↥H) ⊔ O_{π'}(↥H) = ⊤`.)  Combined with `opiCoreInG_commutator_compl_eq_bot`
and `inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl`, this is the direct-product splitting
`H = O_π(H) × O_{π'}(H)` of a nilpotent group into its Hall `π`/`π'` parts. -/
theorem opiCoreInG_sup_compl_eq_of_isNilpotent [Finite G] (π : Set ℕ) {H : Subgroup G}
    [Group.IsNilpotent ↥H] :
    opiCoreInG π H ⊔ opiCoreInG πᶜ H = H := by
  refine le_antisymm (sup_le (opiCoreInG_le π H) (opiCoreInG_le πᶜ H)) ?_
  have htop : (Ch03.oPiCore π ↥H ⊔ Ch03.oPiCore {p | p ∉ π} ↥H).map H.subtype =
      opiCoreInG π H ⊔ opiCoreInG πᶜ H := by
    rw [Subgroup.map_sup]; rfl
  calc H = (⊤ : Subgroup ↥H).map H.subtype := by
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ ≤ (Ch03.oPiCore π ↥H ⊔ Ch03.oPiCore {p | p ∉ π} ↥H).map H.subtype :=
        Subgroup.map_mono
          (OddOrder.BG.Ch3.S10.top_le_oPiCore_sup_compl_of_isNilpotent (K := ↥H) π)
    _ = opiCoreInG π H ⊔ opiCoreInG πᶜ H := htop

/-- **Normalizing a subgroup normalizes its centralizer** (`§14`-independent, reusable):
`N_G(H) ≤ N_G(C_G(H))`.  If `g` normalizes `H`, conjugation by `g` permutes the elements of `H`,
hence preserves the set of elements commuting with all of `H`. -/
theorem normalizer_le_normalizer_centralizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (Subgroup.centralizer (H : Set G)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ {z : G}, z ∈ Subgroup.normalizer (H : Set G) →
      ∀ c, c ∈ Subgroup.centralizer (H : Set G) → z * c * z⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
    intro z hz c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : z⁻¹ * x * z ∈ H := (Subgroup.mem_normalizer_iff''.mp hz x).mp hx
    have hcx : (z⁻¹ * x * z) * c = c * (z⁻¹ * x * z) :=
      Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (z * c * z⁻¹) = z * ((z⁻¹ * x * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * x * z)) * z⁻¹ := by rw [hcx]
      _ = (z * c * z⁻¹) * x := by group
  intro c
  refine ⟨fun hc => key hg c hc, fun hc => ?_⟩
  have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normalizer (H : Set G)).inv_mem hg
  have := key hginv (g * c * g⁻¹) hc
  simpa [mul_assoc] using this

/-- **Commuting nilpotent join is nilpotent** (`§14`-independent, reusable): if two subgroups
`A`, `B` are each nilpotent and elementwise commute (`⁅A, B⁆ = ⊥`), then `A ⊔ B` is nilpotent.
The join is the range of the homomorphism `↥A × ↥B → G`, `(a, b) ↦ a · b` (well-defined since
`A`, `B` commute), so it is a quotient image of the nilpotent direct product `↥A × ↥B`. -/
theorem isNilpotent_sup_of_commutator_eq_bot {A B : Subgroup G}
    [Group.IsNilpotent ↥A] [Group.IsNilpotent ↥B] (hcomm : ⁅A, B⁆ = ⊥) :
    Group.IsNilpotent ↥(A ⊔ B) := by
  have hAcB : A ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcomm' : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := by
    intro a b
    exact (Subgroup.mem_centralizer_iff.mp (hAcB a.2) (b : G) b.2).symm
  set f : ↥A × ↥B →* G := (A.subtype).noncommCoprod (B.subtype) hcomm' with hf
  have hrange : f.range = A ⊔ B := by
    rw [hf, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  haveI : Group.IsNilpotent ↥(f.range) :=
    nilpotent_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact hrange ▸ this

/-- **BG Corollary 15.5, "Lemma 1"**: `O_{σ(M)}(F(M)) = F(M_σ)` (`§14`-independent).
`≤`: `O_σ(F(M)) ≤ O_σ(M) = M_σ` (`opiCoreInG_fittingInG_le_opiCoreInG`); it is nilpotent (subgroup
of `F(M)`) and normal in `M` (characteristic in `F(M) ◁ M`), hence normal in `M_σ`, so a nilpotent
normal subgroup of `M_σ` lands in `F(M_σ)`.  `≥`: `F(M_σ)` is characteristic in `M_σ ◁ M` hence
normal in `M`, nilpotent, so `F(M_σ) ≤ F(M)` (`fittingInG_le_fittingInG_of_le_normalizer`); it is a
`σ`-group (`≤ M_σ`) and normal in `F(M)`, so `F(M_σ) ≤ O_σ(F(M))`. -/
theorem opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma [Finite G]
    {M : Subgroup G} :
    opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M) =
      fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) := by
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  -- `M` normalizes both `M_σ` and `O_σ(F(M))`.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M
  have hMσ_le_M : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  refine le_antisymm ?_ ?_
  · -- `O_σ(F(M)) ≤ F(M_σ)`.
    set N : Subgroup G := opiCoreInG σ (fittingInAmbient M) with hN
    -- `N ≤ M_σ`.
    have hN_Mσ : N ≤ OddOrder.BG.Ch3.S10.Msigma M := by
      have := OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_le_opiCoreInG σ M
      rwa [show opiCoreInG σ M = OddOrder.BG.Ch3.S10.Msigma M from rfl] at this
    -- `N ◁ M` (characteristic in `F(M)`), hence `N ◁ M_σ`.
    have hM_norm_N : M ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((OddOrder.GroupTheory.opiCoreInG_le σ (fittingInAmbient M)).trans
          (OddOrder.BG.Ch2.S08.fittingInG_le M))).mp
        (OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σ M)
    have hNnorm_Mσ : (N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN_Mσ).mpr (hMσ_le_M.trans hM_norm_N)
    -- `N` is nilpotent (subgroup of the nilpotent `F(M)`).
    haveI : Group.IsNilpotent ↥N := by
      haveI : Group.IsNilpotent ↥(fittingInAmbient M) := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
      exact nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.GroupTheory.opiCoreInG_le σ (fittingInAmbient M)))
    -- Nilpotent normal subgroup of `M_σ` lands in `F(M_σ)`.
    haveI : Group.IsNilpotent ↥(N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
      nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hN_Mσ).symm
    haveI := hNnorm_Mσ
    calc N = (N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).map
              (OddOrder.BG.Ch3.S10.Msigma M).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hN_Mσ).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥(OddOrder.BG.Ch3.S10.Msigma M)).map
              (OddOrder.BG.Ch3.S10.Msigma M).subtype :=
          Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
      _ = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) := rfl
  · -- `F(M_σ) ≤ O_σ(F(M))`.
    -- `F(M_σ) ≤ F(M)` (`F(M_σ)` characteristic in `M_σ ◁ M`, nilpotent).
    have hFMσ_le_FM : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ fittingInAmbient M :=
      OddOrder.BG.Ch2.S08.fittingInG_le_fittingInG_of_le_normalizer hMσ_le_M hM_norm_Mσ
    -- `F(M_σ) ≤ M_σ`, a `σ`-group.
    have hFMσ_le_Mσ : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤
        OddOrder.BG.Ch3.S10.Msigma M := OddOrder.BG.Ch2.S08.fittingInG_le _
    have hFMσ_pi : Subgroup.IsPiSubgroup σ (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)) :=
      fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hFMσ_le_Mσ) Nat.card_pos.ne' hr)
    -- `F(M_σ) ◁ F(M)` (since `M` normalizes `F(M_σ)` and `F(M) ≤ M`).
    have hM_norm_FMσ : M ≤ Subgroup.normalizer
        ((fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) : Subgroup G) : Set G) := fun x hx =>
      OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem_normalizer (hM_norm_Mσ hx)
    have hFMσ_norm_FM : ((fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)).subgroupOf
        (fittingInAmbient M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFMσ_le_FM).mpr
        ((OddOrder.BG.Ch2.S08.fittingInG_le M).trans hM_norm_FMσ)
    exact OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hFMσ_le_FM
      hFMσ_norm_FM hFMσ_pi

/-- Lattice absorption used in BG Corollary 15.5 (Case I): if `C = A ⊔ X` with `A ≤ B`, then
`C ⊔ B = X ⊔ B`.  Pure lattice fact (kept generic to avoid `whnf` on the underlying `Subgroup`
`set`-locals in the main proof). -/
theorem sup_eq_sup_of_eq_sup_of_le {α : Type*} [Lattice α] {C A X B : α}
    (hC : C = A ⊔ X) (hA : A ≤ B) : C ⊔ B = X ⊔ B := by
  subst hC
  rw [sup_right_comm, sup_eq_right.mpr hA, sup_comm]

/-- **Nilpotent normal subgroup lands in the ambient Fitting subgroup** (`§14`-independent,
reusable): if `N ≤ M`, `N.subgroupOf M ⊴ M`, and `N` is nilpotent, then `N ≤ F(M)`
(`fittingInAmbient M`).  The relative `N.subgroupOf M` is a nilpotent normal subgroup of `↥M`,
so it lies in `fitting ↥M` (`nilpotent_normal_le_fitting`); mapping back gives the claim. -/
theorem le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent [Finite G] {M N : Subgroup G}
    (hNM : N ≤ M) (hNnorm : (N.subgroupOf M).Normal) [Group.IsNilpotent ↥N] :
    N ≤ fittingInAmbient M := by
  haveI := hNnorm
  haveI : Group.IsNilpotent ↥(N.subgroupOf M) :=
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNM).symm
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    _ = fittingInAmbient M := rfl

/-- **BG Corollary 15.5** (mmd L4225): the decomposition `F(M) = F(M_σ) × Y` with
`Y = O_{σ(M)'}(F(M))` a cyclic `τ₂(M)`-subgroup, together with `F(M) = C_M(M_F)·M_F`,
`M'' ⊆ F(M)`, `M_F ⊆ M'`, and `K ≠ 1 → F(M) ⊆ M'`.  Direct products are encoded by the
commuting/trivial-intersection package.

Faithfulness fix (Lane G): the previous scaffold parametrized an arbitrary `H ≤ M_F` (mmd
fixes `H = M_F`) and used `M_F(M_σ)` where the textbook has the Fitting subgroup `F(M_σ)`
(`fittingInAmbient (Msigma M)`); the dropped conjuncts (a)/(b)/(d) are restored.  The `M'/M_F`
nilpotent clause of (c) is still deferred (quotient API).

`M_F` cyclic ⟹ `F(M)` cyclic exposure (Lane G 2026-06-15): the final conjunct records the
derived consequence that Corollary 15.6's proof cites ("if `M_F` is cyclic, then `F(M)` is
cyclic by Corollary 15.5").  It follows from (a)/(b): when `M_σ` is nilpotent, `F(M_σ) = M_σ =
M_F` (`fittingInAmbient_eq_self_of_isNilpotent`), so `F(M) = M_F × Y` is a product of coprime
cyclic factors (`isCyclic_prod_iff`); otherwise `M_F` is non-cyclic (Theorem 15.2) and the
implication is vacuous.  This supplies the `hFcyc` hypothesis of `typeP_kstar_in_mf_of_inputs`. -/
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
      (¬ S14.IsTypeF M → fittingInAmbient M ≤ derivedInG M) ∧
      -- The derived consequence Corollary 15.6's proof cites ("`F(M)` is cyclic by Cor 15.5"):
      -- via the `F(M) = F(M_σ) × Y` decomposition (both factors cyclic, coprime orders when
      -- `M_σ` is nilpotent so `F(M_σ) = M_σ = M_F`; otherwise `M_F` is non-cyclic, vacuous).
      (IsCyclic ↥(MF M) → IsCyclic ↥(fittingInAmbient M)) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  set F := fittingInAmbient M with hF
  set FMσ := fittingInAmbient Mσ with hFMσ
  -- `Y := O_{σ'}(F(M))`, the `σ'`-Hall part of the Fitting subgroup.
  set Y : Subgroup G := opiCoreInG σᶜ F with hY
  haveI hFnil : Group.IsNilpotent ↥F := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  -- ## Case-independent facts.
  -- Lemma 1: `O_σ(F(M)) = F(M_σ)`.
  have hL1 : opiCoreInG σ F = FMσ :=
    opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
  -- Nilpotent Hall splitting `O_σ(F) ⊔ Y = F`.
  have hsplit : opiCoreInG σ F ⊔ Y = F := opiCoreInG_sup_compl_eq_of_isNilpotent σ
  -- Conjunct 3: `Y ≤ F`.
  have h3 : Y ≤ F := OddOrder.GroupTheory.opiCoreInG_le σᶜ F
  -- Conjunct 6: `F = F(M_σ) ⊔ Y`.
  have h6 : F = FMσ ⊔ Y := by rw [← hL1, hsplit]
  -- Conjunct 7: `F(M_σ) ⊓ Y = ⊥`.
  have h7 : FMσ ⊓ Y = ⊥ := by
    rw [← hL1, hY]
    exact OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σ F)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F)
  -- Conjunct 8: `⁅F(M_σ), Y⁆ = ⊥`.
  have h8 : ⁅FMσ, Y⁆ = ⊥ := by
    rw [← hL1, hY]; exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot σ F
  -- Conjunct 9: `M_F ≤ M'`.
  have h9 : MF M ≤ derivedInG M := maxNilpotentNormalHall_le_derived hG hM
  -- `Y` is a `σ'`-group, `M_σ` is a `σ`-group, so they are coprime.
  have hYpi : Subgroup.IsPiSubgroup σᶜ Y := OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F
  -- `M ≤ N_G(M_σ)` and `M ≤ N_G(Y)` (the latter since `Y` is characteristic in `F(M) ◁ M`).
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M
  have hMσ_le_M : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hM_norm_Y : M ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M))).mp
      (by rw [hY]; exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σᶜ M)
  -- ## Lemma 15.1 inputs (a `κ`-Hall `K` and a `(κ∪σ)ᶜ`-Hall `U`), via Hall's theorem in `↥M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hK
  have hKof : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hKHall : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKof]; exact hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((S14.kappa M ∪ σ)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hU
  have hUof : U.subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((S14.kappa M ∪ σ)ᶜ) (U.subgroupOf M) := by
    rw [hUof]; exact hU'
  -- Lemma 15.1 conclusion (with `Kstar := M_σ ⊓ C_M(K)`).
  obtain ⟨_, _, _, hMddσ, hKguard, _, _, _⟩ :=
    typeP_auxiliary_structure hG hM (hK ▸ Subgroup.map_subtype_le K')
      (hU ▸ Subgroup.map_subtype_le U') hKHall rfl hUHall
  -- Conjunct 4 / 10 helper: `M'' ≤ M_σ` (Lemma 15.1, unconditional).
  have hMdd_Mσ : derivedInG (derivedInG M) ≤ Mσ := hMddσ
  -- ## Case split on whether `M_σ` is nilpotent (`M_F = M_σ`).
  by_cases hcase : MF M = Mσ
  · -- ### Case I: `M_σ` nilpotent, `M_F = M_σ`, `F(M_σ) = M_σ`.
    haveI hMσnil : Group.IsNilpotent ↥Mσ :=
      (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp hcase
    have hFMσ_eq : FMσ = Mσ := fittingInAmbient_eq_self_of_isNilpotent
    -- `M_σ ≤ F(M)` (nilpotent normal subgroup of `M`).
    have hMσ_le_F : Mσ ≤ F := by rw [← hFMσ_eq]; rw [h6]; exact le_sup_left
    -- `[M_σ, Y] = ⊥`, so `Y` centralizes `M_σ`; together with `Y ≤ M`, `Y ≤ C_G(M_σ) ⊓ M`.
    have hMσY : ⁅Mσ, Y⁆ = ⊥ := by rw [← hFMσ_eq]; exact h8
    have hY_cent : Y ≤ Subgroup.centralizer (Mσ : Set G) := by
      rw [Subgroup.commutator_comm] at hMσY
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMσY
    have hY_le_M : Y ≤ M := h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
    -- Corollary 15.3(a) at `H := M_σ`: `C_M(M_σ) = (C_G(M_σ) ⊓ M_σ) ⊔ X`, `X` cyclic `τ₂`.
    have hMσne : Mσ ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    have hHallMσ : Ch03.IsHallSubgroup (S14.piSet Mσ) (Mσ.subgroupOf Mσ) := by
      rw [Subgroup.subgroupOf_self, Ch03.IsHallSubgroup.top_iff]
      intro p hp; exact hp
    obtain ⟨⟨X, hXcyc, hXτ₂, hCeq⟩, _⟩ := mf_hall_centralizer_control hG hM hHallMσ hMσne
    -- `C := C_G(M_σ) ⊓ M`, `A := C_G(M_σ) ⊓ M_σ`.
    set C : Subgroup G := Subgroup.centralizer (Mσ : Set G) ⊓ M with hCdef
    set A : Subgroup G := Subgroup.centralizer (Mσ : Set G) ⊓ Mσ with hAdef
    have hY_C : Y ≤ C := le_inf hY_cent hY_le_M
    have hA_C : A ≤ C := inf_le_inf_left _ hMσ_le_M
    have hX_C : X ≤ C := le_sup_right.trans hCeq.ge
    -- `A ⊴ C` (so we can form the cyclic quotient `C/A`).
    have hC_norm_A : C ≤ Subgroup.normalizer (A : Set G) := by
      have h1 : C ≤ Subgroup.normalizer (Subgroup.centralizer (Mσ : Set G)) :=
        inf_le_left.trans Subgroup.le_normalizer
      have h2 : C ≤ Subgroup.normalizer (Mσ : Set G) := inf_le_right.trans hM_norm_Mσ
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    haveI hA_normal : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr
        (by rw [inf_eq_left.mpr hA_C]; exact hC_norm_A)
    -- `A ≤ M_σ` is a `σ`-group; `Y` is a `σ'`-group; hence `|A|` and `|Y|` are coprime.
    have hA_pi : ∀ r ∈ (Nat.card ↥A).primeFactors, r ∈ σ := fun r hr =>
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (inf_le_right : A ≤ Mσ))
          Nat.card_pos.ne' hr)
    have hY_pi' : ∀ r ∈ (Nat.card ↥Y).primeFactors, r ∉ σ := fun r hr =>
      (Set.mem_compl_iff _ _).mp (hYpi r hr)
    -- `Y ⊓ A = ⊥` (coprime orders).
    have hY_inf_A : Y ⊓ A = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime
        ((Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne'
          hA_pi hY_pi').symm)
    -- Embed `Y` into the cyclic quotient `C/A` (`C/A` is a quotient image of the cyclic `X`).
    have haxtop : A.subgroupOf C ⊔ X.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA_C hX_C, show A ⊔ X = C from hCeq.symm,
        Subgroup.subgroupOf_self]
    have hYc_inf_a : Y.subgroupOf C ⊓ A.subgroupOf C = ⊥ := by
      rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hY_inf_A,
        MonoidHom.comap_bot]
      exact C.ker_subtype
    have hinj : Function.Injective
        ((QuotientGroup.mk' (A.subgroupOf C)).comp (Y.subgroupOf C).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      have hmem : (Y.subgroupOf C).subtype y ∈ Y.subgroupOf C ⊓ A.subgroupOf C := ⟨y.2, hy⟩
      rw [hYc_inf_a, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]; exact Subtype.ext hmem
    haveI hxcyc : IsCyclic ↥(X.subgroupOf C) := by
      haveI : IsCyclic ↥X := hXcyc
      exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hX_C).symm.surjective
    haveI hquot_cyc : IsCyclic (↥C ⧸ A.subgroupOf C) := by
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (A.subgroupOf C)).comp (X.subgroupOf C).subtype) := by
        rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
        have h1 : (A.subgroupOf C ⊔ X.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) =
            ⊤ := by
          rw [haxtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        have hkerbot : (A.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        rw [Subgroup.map_sup, hkerbot, bot_sup_eq] at h1
        rw [h1]
      exact isCyclic_of_surjective _ hsurj
    -- Conjunct 1: `Y` is cyclic (`Y ≅ Y.subgroupOf C ↪ C/A` cyclic).
    haveI hYcyc' : IsCyclic ↥(Y.subgroupOf C) :=
      isCyclic_of_surjective _ (MonoidHom.ofInjective hinj).symm.surjective
    have hYcyc : IsCyclic ↥Y :=
      isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hY_C).surjective
    -- Conjunct 2: `π(Y) ⊆ τ₂` (`q ∣ |Y| ∣ [C:A] ∣ |X|`, `π(X) ⊆ τ₂`).
    have hYτ₂ : (↑(Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tau2 M := by
      intro q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hcardYc : Nat.card ↥(Y.subgroupOf C) = Nat.card ↥Y :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY_C).toEquiv
      have hdvd1 : Nat.card ↥Y ∣ (A.subgroupOf C).index := by
        rw [← hcardYc, Subgroup.index_eq_card]
        exact Subgroup.card_dvd_of_injective _ hinj
      have hdvd2 : (A.subgroupOf C).index ∣ Nat.card ↥X := by
        have hidx : (A.subgroupOf C).index = (A.subgroupOf C).relIndex (X.subgroupOf C) := by
          rw [← Subgroup.relIndex_top_right, ← haxtop, Subgroup.relIndex_sup_left]
        have hcardx : Nat.card ↥(X.subgroupOf C) = Nat.card ↥X :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_C).toEquiv
        rw [hidx, ← hcardx]
        exact Subgroup.relIndex_dvd_card (A.subgroupOf C) (X.subgroupOf C)
      have hqX : q ∈ (Nat.card ↥X).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp,
          ((Nat.dvd_of_mem_primeFactors hq).trans hdvd1).trans hdvd2, Nat.card_pos.ne'⟩
      exact hXτ₂ hqX
    -- Conjunct 4: `M'' ⊆ F(M)` (`M'' ≤ M_σ ≤ F(M)`, `M_σ` nilpotent).
    have h4 : derivedInG (derivedInG M) ≤ F := hMdd_Mσ.trans hMσ_le_F
    -- Conjunct 5: `F(M) = (C_G(M_F) ⊓ M) ⊔ M_F = (C_G(M_σ) ⊓ M) ⊔ M_σ`.
    have h5 : F = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := by
      rw [hcase]
      -- `M ≤ N_G(C_G(M_σ))`: normalizing `M_σ` normalizes its centralizer.
      have hM_norm_CMσ : M ≤ Subgroup.normalizer (Subgroup.centralizer (Mσ : Set G)) :=
        hM_norm_Mσ.trans (normalizer_le_normalizer_centralizer Mσ)
      -- `C := C_G(M_σ) ⊓ M ⊴ M`.
      have hC_norm : M ≤ Subgroup.normalizer (C : Set G) :=
        (le_inf hM_norm_CMσ Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
      haveI hC_normal : (C.subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hC_norm
      refine le_antisymm ?_ ?_
      · -- `F ⊆ (C_G(M_σ) ⊓ M) ⊔ M_σ`: `F = M_σ ⊔ Y`, `M_σ ≤ M_σ`, `Y ≤ C`.
        rw [h6, hFMσ_eq]
        exact sup_le (le_sup_right) (hY_C.trans le_sup_left)
      · -- `(C_G(M_σ) ⊓ M) ⊔ M_σ ⊆ F`: `M_σ ≤ F`, and `C ⊔ M_σ` is nilpotent normal (`= X ⊔ M_σ`).
        refine sup_le ?_ hMσ_le_F
        -- `C ⊔ M_σ ⊴ M` and is nilpotent, hence `⊆ F(M)`.
        have hCMσ_le_M : C ⊔ Mσ ≤ M := sup_le inf_le_right hMσ_le_M
        have hCMσ_norm : ((C ⊔ Mσ).subgroupOf M).Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCMσ_le_M]
          exact le_trans (le_inf hC_norm hM_norm_Mσ)
            (Subgroup.normalizer_inf_normalizer_le_normalizer_sup C Mσ)
        -- `C ⊔ M_σ = X ⊔ M_σ` (since `C = A ⊔ X` and `A ≤ M_σ`).
        have hA_le_Mσ : A ≤ Mσ := inf_le_right
        have hCMσ_eq : C ⊔ Mσ = X ⊔ Mσ := sup_eq_sup_of_eq_sup_of_le hCeq hA_le_Mσ
        -- `X ⊔ M_σ` nilpotent: `X` cyclic, `M_σ` nilpotent, `[X, M_σ] = ⊥` (`X ≤ C_G(M_σ)`).
        have hXcent : ⁅X, Mσ⁆ = ⊥ := by
          have hXle : X ≤ Subgroup.centralizer (Mσ : Set G) := hX_C.trans inf_le_left
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXle
        haveI hXcyc' : IsCyclic ↥X := hXcyc
        letI : CommGroup ↥X := IsCyclic.commGroup
        haveI : Group.IsNilpotent ↥X := CommGroup.isNilpotent
        haveI hCMσ_nil : Group.IsNilpotent ↥(C ⊔ Mσ) := by
          rw [hCMσ_eq]; exact isNilpotent_sup_of_commutator_eq_bot hXcent
        haveI := hCMσ_norm
        have hCMσ_le_F : C ⊔ Mσ ≤ F :=
          le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent hCMσ_le_M hCMσ_norm
        exact le_sup_left.trans hCMσ_le_F
    -- Conjunct 10: `¬ TypeF → F(M) ⊆ M'`.  `M = K M'`, `M/M' ≅ K` (`κ`-group), `π(Y) ⊆ τ₂`,
    -- and `κ ∩ τ₂ = ∅`, so `Y ≤ M'`; with `M_σ ≤ M'` this gives `F ⊆ M'`.
    have h10 : ¬ S14.IsTypeF M → F ≤ derivedInG M := by
      intro hnotF
      have hP : S14.IsTypeP M := by
        rw [S14.isTypeF_iff_not_isTypeP] at hnotF; exact not_not.mp hnotF
      -- `K ≠ ⊥`: some `κ`-prime divides `|M|`, but a trivial `κ`-Hall would push it to the index.
      have hKne : K ≠ ⊥ := by
        obtain ⟨p, hpκ⟩ := hP
        obtain ⟨hpprime, -, P, hPmem, hPM, -⟩ := id hpκ
        haveI : Fact p.Prime := ⟨hpprime⟩
        -- `p ∣ |M|` (a rank-one elementary abelian `p`-subgroup `P ≤ M`).
        have hpcardP : Nat.card ↥P = p := by
          have := (OddOrder.GroupTheory.mem_elemAbelianOfRank.mp hPmem).2
          rwa [pow_one] at this
        have hpM : p ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpprime,
            hpcardP ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩
        intro hKbot
        -- `K = ⊥` ⟹ `(K.subgroupOf M).index = |↥M|`, so `p` divides the index of the `κ`-Hall.
        have hidx : (K.subgroupOf M).index = Nat.card ↥M := by
          rw [hKbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
        have hpidx : p ∈ (K.subgroupOf M).index.primeFactors := by rw [hidx]; exact hpM
        exact hKHall.2 p hpidx hpκ
      obtain ⟨hMderiv, _, hcompl, _⟩ := hKguard hKne
      -- `Y ≤ M'`: image of the normal `τ₂`-subgroup `Y` in the abelian `M/M'` (order `|K|`, a
      -- `κ`-number) is trivial because `τ₂ ∩ κ = ∅`.
      have hY_le_deriv : Y ≤ derivedInG M := by
        have hYM : Y ≤ M := h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
        set Hsub : Subgroup ↥M := Y.subgroupOf M with hHsub
        set D : Subgroup ↥M := (derivedInG M).subgroupOf M with hDdef
        have hDcomm : D = commutator ↥M :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
        haveI hDnorm : D.Normal := by rw [hDcomm]; infer_instance
        -- `[M : M'] = |K|` (complement), a `κ`-number.
        have hDindex : D.index = Nat.card ↥(K.subgroupOf M) := hcompl.symm.index_eq_card
        -- `Coprime |Y| [M:M']` (`π(Y) ⊆ τ₂`, `π(K) ⊆ κ`, `τ₂ ∩ κ = ∅`).
        have hKpi : ∀ r ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors, r ∈ S14.kappa M :=
          fun r hr => hKHall.1 r hr
        have hcop : Nat.Coprime (Nat.card ↥Hsub) D.index := by
          rw [hDindex]
          refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne'
            Nat.card_pos.ne' (π := tau2 M) (fun r hr => ?_) (fun r hr => ?_)
          · -- `π(Y) ⊆ τ₂`.
            have : r ∈ (Nat.card ↥Y).primeFactors := by
              rwa [hHsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv] at hr
            exact hYτ₂ this
          · -- `κ ∩ τ₂ = ∅`: a `κ`-prime has rank one, a `τ₂`-prime has rank two.
            intro hrτ₂
            have hrκ : r ∈ S14.kappa M := hKpi r hr
            have hr1 : pRank ↥M r = 1 := by
              rcases S14.kappa_subset_tau1_union_tau3 hrκ with h | h
              · exact ((mem_tau1_iff M r).mp h).2.2
              · exact ((mem_tau3_iff M r).mp h).2.2
            have hr2 : pRank ↥M r = 2 := ((mem_tau2_iff M r).mp hrτ₂).2
            rw [hr1] at hr2; exact absurd hr2 (by norm_num)
        -- `Y.subgroupOf M ≤ commutator ↥M`: image in the abelianization is trivial.
        haveI hHnorm : Hsub.Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hM_norm_Y
        have hcard_img_dvd_Y : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) ∣ Nat.card ↥Hsub :=
          Subgroup.card_map_dvd Hsub (QuotientGroup.mk' D)
        have hcard_img_dvd_idx : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) ∣ D.index := by
          rw [Subgroup.index_eq_card]
          exact Subgroup.card_subgroup_dvd_card _
        have hcard_img_one : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop hcard_img_dvd_Y hcard_img_dvd_idx
        have himg_bot : Hsub.map (QuotientGroup.mk' D) = ⊥ :=
          Subgroup.card_eq_one.mp hcard_img_one
        have hHsub_le_D : Hsub ≤ D := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg_bot
          exact himg_bot
        -- Transport back to `G`: `Y ≤ M'`.
        calc Y = Hsub.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hYM).symm
          _ ≤ D.map M.subtype := Subgroup.map_mono hHsub_le_D
          _ = derivedInG M := Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)
      rw [h6, hFMσ_eq]
      exact sup_le ((OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)) hY_le_deriv
    -- Conjunct 11: `M_F` cyclic → `F(M)` cyclic (`F = M_F × Y`, both cyclic coprime).
    have h11 : IsCyclic ↥(MF M) → IsCyclic ↥F := by
      intro hMFcyc
      haveI := hMFcyc
      haveI := hYcyc
      -- `F = M_F ⊔ Y` with `M_F ⊓ Y = ⊥`, `[M_F, Y] = ⊥`, coprime orders.
      have hMFY_inf : MF M ⊓ Y = ⊥ := by rw [hcase, ← hFMσ_eq]; exact h7
      have hMFY_comm : ⁅(MF M : Subgroup G), Y⁆ = ⊥ := by rw [hcase, ← hFMσ_eq]; exact h8
      have hFeq : F = MF M ⊔ Y := by rw [h6, hFMσ_eq, hcase]
      have hcop : Nat.Coprime (Nat.card ↥(MF M)) (Nat.card ↥Y) := by
        refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne'
          (π := σ) (fun r hr => ?_) hY_pi'
        rw [hcase] at hr
        exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr
      -- Cyclic product (orderOf approach, mirroring `S06.isCyclic_sup`).
      obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥(MF M))
      obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := ↥Y)
      have hMF_le : MF M ≤ MF M ⊔ Y := le_sup_left
      have hY_le : Y ≤ MF M ⊔ Y := le_sup_right
      have hoa : orderOf (Subgroup.inclusion hMF_le a) = Nat.card ↥(MF M) := by
        rw [orderOf_injective _ (Subgroup.inclusion_injective _) a,
          orderOf_eq_card_of_forall_mem_zpowers ha]
      have hob : orderOf (Subgroup.inclusion hY_le b) = Nat.card ↥Y := by
        rw [orderOf_injective _ (Subgroup.inclusion_injective _) b,
          orderOf_eq_card_of_forall_mem_zpowers hb]
      have hMFnorm_Y : MF M ≤ Subgroup.normalizer (Y : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMFY_comm).trans
          (OddOrder.Isaacs.Ch07.centralizer_le_normalizer Y)
      have hcardsup : Nat.card ↥(MF M ⊔ Y) = Nat.card ↥(MF M) * Nat.card ↥Y := by
        have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card (MF M) Y
        rw [hMFY_inf, Subgroup.card_bot, mul_one] at hprod
        rwa [show ((MF M : Set G) * (Y : Set G)) = ((MF M ⊔ Y : Subgroup G) : Set G) from
          (Subgroup.coe_mul_of_left_le_normalizer_right (MF M) Y hMFnorm_Y).symm] at hprod
      have hcomm : Commute (Subgroup.inclusion hMF_le a) (Subgroup.inclusion hY_le b) := by
        have hab : ((a : G)) * (b : G) = (b : G) * (a : G) :=
          (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMFY_comm a.2) (b : G) b.2).symm
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]; exact hab)
      rw [hFeq]
      refine isCyclic_of_orderOf_eq_card
        (Subgroup.inclusion hMF_le a * Subgroup.inclusion hY_le b) ?_
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hoa, hob]; exact hcop),
        hoa, hob, hcardsup]
    exact ⟨Y, hYcyc, hYτ₂, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · -- ### Case II: `M_σ` not nilpotent, `M_F ≠ M_σ`, so `M` is type `P1` and `F(M) ⊆ M_σ`.
    obtain ⟨_hP1, Q, _Q0, _D, _p, _q, _, _, _, _, _, _, _, hQsubMF, _, _, _, _, _, _, hMσderiv,
        _, hFsubMσ, hFQ, hMFnc⟩ :=
      mf_ne_msigma_typeP1_structure hG hM hcase hKHall rfl
    -- In Case II: `F(M) ⊆ M_σ`, so `Y = O_{σ'}(F(M)) = ⊥` and `F(M) = F(M_σ)`.
    -- `Y = ⊥`: `F(M) ⊆ M_σ` is a `σ`-group, so its `σ'`-Hall core is trivial.
    have hYbot : Y = ⊥ := by
      rw [hY]
      refine OddOrder.GroupTheory.opiCoreInG_compl_eq_bot_of_isPiSubgroup ?_
      intro r hr
      exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hFsubMσ) Nat.card_pos.ne' hr)
    -- `F(M) = F(M_σ)`: `F(M) ◁ M` nilpotent `⊆ M_σ ⟹ ◁ M_σ ⟹ ⊆ F(M_σ)`; `F(M_σ) ⊆ F(M)` (Lemma 1).
    have hFMσ_eq : F = FMσ := by
      refine le_antisymm ?_ ?_
      · -- `F ⊆ M_σ`, `F ◁ M_σ` (since `F ◁ M`), `F` nilpotent ⟹ `F ⊆ F(M_σ)`.
        have hF_norm_Mσ : (F.subgroupOf Mσ).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hFsubMσ).mpr
            (hMσ_le_M.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
              (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
              (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)))
        exact le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent hFsubMσ hF_norm_Mσ
      · -- `F(M_σ) ⊆ O_σ(F(M)) ⊆ F(M)`.
        rw [← hL1]; exact OddOrder.GroupTheory.opiCoreInG_le σ F
    -- Now assemble.  With `Y = ⊥`, conjuncts (a) and the `× Y` split collapse.
    have hYcyc : IsCyclic ↥Y := by rw [hYbot]; infer_instance
    have hYτ₂ : (↑(Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tau2 M := by
      rw [hYbot, Subgroup.card_bot]; simp
    -- Conjunct 4: `M'' ⊆ F(M)`.
    have h4 : derivedInG (derivedInG M) ≤ F := by
      have hMdd_F : derivedInG (derivedInG M) ≤ fittingInAmbient M := ‹_›
      exact hMdd_F
    -- Conjunct 5 (Case II, `M_F ≠ M_σ`): `F(M) = (C_G(M_F) ⊓ M) ⊔ M_F` (mmd 15.2(g)
    -- "(b) `F(M) = C_M(H)H`" with `H = M_F`).
    have h5 : F = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := by
      have hMF_le_F : MF M ≤ F := maxNilpotentNormalHall_le_fittingInG M
      have hQ_le_MF : Q ≤ MF M := hQsubMF
      -- `C_M(M_F) ⊆ C_M(Q) ⊆ Q ⊔ C_M(Q) = F(M)` (Theorem 15.2(g) equality `hFQ`).
      have hCMF_le_F : Subgroup.centralizer (MF M : Set G) ⊓ M ≤ F := by
        have hsub : Subgroup.centralizer (MF M : Set G) ⊓ M ≤
            Subgroup.centralizer (Q : Set G) ⊓ M := by
          refine inf_le_inf_right _ ?_
          intro x hx
          rw [Subgroup.mem_centralizer_iff] at hx ⊢
          exact fun g hg => hx g (hQ_le_MF hg)
        rw [hF, hFQ]; exact hsub.trans le_sup_right
      refine le_antisymm ?_ (sup_le hCMF_le_F hMF_le_F)
      -- `⊆` (mmd 15.2(g)): the `σ'`-free, type-`P1` structural step `F(M) ⊆ C_M(M_F)·M_F`.
      -- Strategy (general, §14-independent): `M_F` is the full Hall `π(M_F)`-part of `F(M)`, so the
      -- nilpotent `F(M)` splits as `F(M) = M_F × O_{π(M_F)'}(F(M))`, and the second factor
      -- centralizes `M_F` (distinct Hall components of a nilpotent group commute).
      set π : Set ℕ := ↑(Nat.card ↥(MF M)).primeFactors with hπ
      -- `F ≤ M` and `M ≤ N_G(F)` (`F` is normal in `M`).
      have hF_le_M : F ≤ M := OddOrder.BG.Ch2.S08.fittingInG_le M
      have hM_norm_F : M ≤ Subgroup.normalizer (F : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
          (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)
      -- `M_F ≤ O_π(F)`: `M_F ≤ F`, `(M_F).subgroupOf F ⊴ F` (as `F ≤ M ≤ N_G(M_F)`), `M_F` a `π`-group.
      have hMF_norm_F : (((MF M).subgroupOf F)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMF_le_F).mpr
          (hF_le_M.trans (maxNilpotentNormalHall_le_normalizer M))
      have hMF_pi : Subgroup.IsPiSubgroup π (MF M) := fun p hp => by
        rw [hπ]; exact Finset.mem_coe.mpr hp
      have hMF_le_Oπ : MF M ≤ OddOrder.GroupTheory.opiCoreInG π F :=
        OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hMF_le_F hMF_norm_F hMF_pi
      -- `O_π(F) ≤ M_F`: `O_π(F)` is a normal `π`-subgroup of `↥M`, and `M_F` is `π`-Hall in `↥M`.
      have hOπ_le_F : OddOrder.GroupTheory.opiCoreInG π F ≤ F :=
        OddOrder.GroupTheory.opiCoreInG_le π F
      have hOπ_le_M : OddOrder.GroupTheory.opiCoreInG π F ≤ M := hOπ_le_F.trans hF_le_M
      haveI hObar_norm : ((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOπ_le_M).mpr
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer π hM_norm_F)
      have hObar_pi : Ch03.Subgroup.IsPiGroup π ((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M) := by
        intro p hp
        have hcardO : Nat.card ↥((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M) =
            Nat.card ↥(OddOrder.GroupTheory.opiCoreInG π F) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOπ_le_M).toEquiv
        exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG π F p (by rwa [hcardO] at hp)
      have hObar_le_Hbar : (OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M ≤ (MF M).subgroupOf M :=
        Ch03.Subgroup.IsPiGroup.normal_le_hall hObar_pi (maxNilpotentNormalHall_isHall M)
      have hMF_le_M : MF M ≤ M := maxNilpotentNormalHall_le M
      have hOπ_le_MF : OddOrder.GroupTheory.opiCoreInG π F ≤ MF M := by
        have := Subgroup.map_mono (f := M.subtype) hObar_le_Hbar
        rwa [Subgroup.map_subgroupOf_eq_of_le hOπ_le_M,
          Subgroup.map_subgroupOf_eq_of_le hMF_le_M] at this
      have hOπ_eq_MF : OddOrder.GroupTheory.opiCoreInG π F = MF M :=
        le_antisymm hOπ_le_MF hMF_le_Oπ
      -- `F = O_π(F) ⊔ O_{π'}(F) = M_F ⊔ O_{π'}(F)`.
      have hsplit : OddOrder.GroupTheory.opiCoreInG π F ⊔
          OddOrder.GroupTheory.opiCoreInG πᶜ F = F :=
        opiCoreInG_sup_compl_eq_of_isNilpotent π
      -- `O_{π'}(F)` centralizes `M_F = O_π(F)`, and lies in `M`, so `≤ C_G(M_F) ⊓ M`.
      have hcomm : ⁅OddOrder.GroupTheory.opiCoreInG π F,
          OddOrder.GroupTheory.opiCoreInG πᶜ F⁆ = ⊥ :=
        OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot π F
      have hOπ'_cent : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤
          Subgroup.centralizer (MF M : Set G) := by
        have hcomm' : ⁅OddOrder.GroupTheory.opiCoreInG πᶜ F,
            OddOrder.GroupTheory.opiCoreInG π F⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]; exact hcomm
        rw [← hOπ_eq_MF]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
      have hOπ'_le_M : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤ M :=
        (OddOrder.GroupTheory.opiCoreInG_le πᶜ F).trans hF_le_M
      have hOπ'_le : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤
          Subgroup.centralizer (MF M : Set G) ⊓ M := le_inf hOπ'_cent hOπ'_le_M
      -- Assemble: `F = M_F ⊔ O_{π'}(F) ≤ (C_G(M_F) ⊓ M) ⊔ M_F`.
      calc F = OddOrder.GroupTheory.opiCoreInG π F ⊔
                OddOrder.GroupTheory.opiCoreInG πᶜ F := hsplit.symm
        _ = MF M ⊔ OddOrder.GroupTheory.opiCoreInG πᶜ F := by rw [hOπ_eq_MF]
        _ ≤ MF M ⊔ (Subgroup.centralizer (MF M : Set G) ⊓ M) := sup_le_sup_left hOπ'_le _
        _ = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := sup_comm _ _
    -- Conjunct 10: `¬ TypeF → F(M) ⊆ M'`.  `F(M) ⊆ M_σ = M'` (Theorem 15.2).
    have h10 : ¬ S14.IsTypeF M → F ≤ derivedInG M := fun _ => hFsubMσ.trans hMσderiv.le
    -- Conjunct 11: `M_F` cyclic → `F(M)` cyclic.  Vacuous: `M_F` is non-cyclic (Theorem 15.2).
    have h11 : IsCyclic ↥(MF M) → IsCyclic ↥F := fun h => absurd h hMFnc
    exact ⟨Y, hYcyc, hYτ₂, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- **§14-independent assembly of BG Corollary 15.6** from its §14/§15 inputs taken as
hypotheses.  This packages the *logic* of Corollary 15.6 (mmd L4232) with no fragile citation of
the still-`sorry` §14 scaffold: once §14 lands, `typeP_kstar_in_mf` discharges each hypothesis by
a single citation and applies this skeleton.  Hypothesis provenance (mmd L4434 dependency table):

* `hKne` (`K* ≠ 1`) ← Proposition 14.2(c) (`typeP_structure`, conjunct `Kstar ≠ ⊥`);
* `hcyc` (`K K*` cyclic) ← Theorem 14.7(d) (`typeP_duality`, conjunct `IsCyclic (K ⊔ Kstar)`);
* `hKsubMF` (`K* ⊆ M_F`) ← Theorem 15.2(b)(c) (case-split on `M_F = M_σ`);
* `hcompl`/`hcop` (`M = K M'`, `K ∩ M' = 1`, coprime) ← Theorem 14.7(h) / Lemma 15.1's `K ≠ 1`
  clause;
* `hFcyc` (`M_F` cyclic ⟹ `F(M)` cyclic) ← Corollary 15.5 (the consequence its proof of 15.6
  cites).

The two nontrivial steps are unconditional: `K* ⊆ M''`
(`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'`) and the `M_F`-not-cyclic
contradiction (`fittingInAmbient_cyclic_imp_derivedDerived_eq_bot`, giving `M'' = 1`, against
`K* ⊆ M''` and `K* ≠ 1`). -/
theorem typeP_kstar_in_mf_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKne : Kstar ≠ ⊥) (hcyc : IsCyclic ↥(K ⊔ Kstar)) (hKsubMF : Kstar ≤ MF M)
    (hcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M)))
    (hFcyc : IsCyclic ↥(MF M) → IsCyclic ↥(fittingInAmbient M)) :
    Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ MF M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧ ¬ IsCyclic ↥(MF M) := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI := hcyc
  -- `K* ⊆ M''`:  the §14-independent conjunct-4 engine.
  have hKsubdd : Kstar ≤ derivedInG (derivedInG M) := by
    rw [hKstar]
    exact Msigma_inf_centralizer_le_derivedDerived_of_isComplement' hG hM hcompl hcop
  refine ⟨hKne, Subgroup.isCyclic_of_le (le_sup_right : Kstar ≤ K ⊔ Kstar), hKsubMF,
    hKsubdd, ?_⟩
  -- `M_F` not cyclic:  else `F(M)` cyclic ⟹ `M'' = 1`, but `K* ⊆ M''` and `K* ≠ 1`.
  intro hcycMF
  have hMdd : derivedInG (derivedInG M) = ⊥ :=
    fittingInAmbient_cyclic_imp_derivedDerived_eq_bot (hFcyc hcycMF)
  exact hKne (le_bot_iff.mp (hMdd ▸ hKsubdd))

/-- **BG Corollary 15.6** (mmd L4174): for a type-P maximal subgroup, `Kstar` is
nontrivial cyclic and lies in `M_F`, while `M_F` itself is not cyclic. -/
theorem typeP_kstar_in_mf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M)
    (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ MF M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧ ¬ IsCyclic ↥(MF M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `(κ ∪ σ)ᶜ`-subgroup `U` of `M` exists by solvability (Hall's theorem); this is the
  -- `U`-factor of the type-`P` decomposition `M = K U M_σ` needed to invoke Proposition 14.2.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K* ≠ 1`:  Proposition 14.2(c) (`typeP_structure`).
  have hKne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  -- `K K*` cyclic and the `M = K M'` complement / coprime data:  Theorem 14.7(d),(h).
  obtain ⟨hcompl, hcop, _Mstar, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    typeP_duality hG hM hP hK hKstar
  -- `K* ⊆ M_F`:  Theorem 15.2 when `M_F ≠ M_σ`, else `K* ⊆ M_σ = M_F` directly.
  have hKsubMF : Kstar ≤ MF M := by
    by_cases hMF : MF M = OddOrder.BG.Ch3.S10.Msigma M
    · rw [hKstar, hMF]; exact inf_le_left
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ :=
        mf_ne_msigma_typeP1_structure hG hM hMF hK hKstar
      exact hk
  -- `M_F` cyclic ⟹ `F(M)` cyclic:  Corollary 15.5 (`fitting_decomposition`, last conjunct).
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hFcyc⟩ := fitting_decomposition hG hM
  exact typeP_kstar_in_mf_of_inputs hG hM hKstar hKne hcyc hKsubMF hcompl hcop hFcyc

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

/-- **BG Theorem 15.8** (mmd L4264; Feit--Thompson 1991): in the Corollary 14.12 setup,
nonempty `tau_2(H)` forces `tau_2(M) = ∅`, `q := |K|` prime, and `tau_2(H) = {q}`.

Faithfulness fix (Lane G): the previous scaffold had a spurious third maximal `N` and concluded
`tau_2(N) = {q}` (mmd: the singleton is `tau_2(H)`) and dropped `q = |K|`. -/
theorem tau2_transfer_constraint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M H K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hP2 : S14.IsTypeP2 M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hHtau : (tau2 H).Nonempty) :
    tau2 M = ∅ ∧ ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q ∧ tau2 H = {q} := by
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
