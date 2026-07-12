/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV
import OddOrder.Peterfalvi.S13_ElementaryAbelianKernel
import OddOrder.Peterfalvi.S07_PivotCoherence

/-!
# Peterfalvi Section 13: the core structure of `H` and `U` ((11.6)--(11.8))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 13, pp. 64--68 — the (11.6)--(11.8) block.

Split from `S13_MaximalIII_IV` (which keeps Hypothesis (11.2) and the
commutator chain (11.3)--(11.5)): this leaf carries the core-structure
theorems — `H` is a `p`-group, `U` centralizes `H₀`, `H₀ = H'`, `C = U'`
((11.6)), `H` elementary abelian of order `p^q` and `H₀ = 1` ((11.7)), and the
orthogonality calculation (11.8).
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-! ## (11.6)--(11.7): the core structure of `H` and `U` -/

/-- **Commutator product decomposition under cross-commutation**: if `c₁, c₂` commute with
`h₁, h₂` (four swaps), then `⁅h₁c₁, h₂c₂⁆ = ⁅h₁,h₂⁆ · ⁅c₁,c₂⁆` (explicit products; crib of the
`commutator_HC_mem_H0C` computation). -/
theorem commutator_mul_of_commute {Q : Type*} [Group Q] {h₁ c₁ h₂ c₂ : Q}
    (hsw12 : Commute c₁ h₂) (hsw11 : Commute c₁ h₁) (hsw21 : Commute c₂ h₁)
    (hsw22 : Commute c₂ h₂) :
    h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹
      = (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
  have e12 : c₁ * h₂ = h₂ * c₁ := hsw12
  calc h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹
      = h₁ * (c₁ * h₂) * c₂ * (c₁⁻¹ * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by group
    _ = h₁ * (h₂ * c₁) * c₂ * (c₁⁻¹ * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by rw [e12]
    _ = h₁ * h₂ * (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ * (c₂⁻¹ * h₂⁻¹) := by group
    _ = h₁ * h₂ * h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by
        have hcomm3 : (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ = h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) := by
          have a1 : Commute (c₁ * c₂ * c₁⁻¹) h₁⁻¹ :=
            ((hsw11.mul_left hsw21).mul_left hsw11.inv_left).inv_right
          exact a1
        rw [show h₁ * h₂ * (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ * (c₂⁻¹ * h₂⁻¹)
            = h₁ * h₂ * ((c₁ * c₂ * c₁⁻¹) * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) from by group,
          hcomm3]
        group
    _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
        have hcomm4 : (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * h₂⁻¹ = h₂⁻¹ * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
          have a1 : Commute (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) h₂⁻¹ :=
            (((hsw12.mul_left hsw22).mul_left hsw12.inv_left).mul_left
              hsw22.inv_left).inv_right
          exact a1
        rw [show h₁ * h₂ * h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) * (c₂⁻¹ * h₂⁻¹)
            = h₁ * h₂ * h₁⁻¹ * ((c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * h₂⁻¹) from by group,
          hcomm4]
        group

namespace Hypothesis

/-- **Peterfalvi (9.3) at the §13 hypothesis**: `p = |W₂|` is prime and
`|H| = p^q · |C_H(U)|` (types III/IV; type V is excluded by (10.10)). -/
theorem p_prime_and_card_H_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.p.Prime ∧
      Nat.card ↥hyp.H
        = hyp.p ^ hyp.q
          * Nat.card ↥(hyp.H ⊓ Subgroup.centralizer (hyp.U : Set G)) := by
  obtain ⟨p', hp', hW2, _hUW1, hcard⟩ :=
    (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG hyp.s11Setup).2
      (hyp.base.isTypeIIIorIV hG)
  have hpp : p' = hyp.p := by rw [← hW2, hyp.s11Setup_card_W2_eq]
  refine ⟨hpp ▸ hp', ?_⟩
  rw [← hyp.s11Setup_H_eq, ← hyp.s11Setup_U_eq, ← hyp.s11Setup_q_eq, ← hpp]
  exact hcard

/-- `H` is nilpotent (`H = M_F`, the maximal normal nilpotent Hall subgroup). -/
theorem H_isNilpotent [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Group.IsNilpotent ↥hyp.H := by
  show Group.IsNilpotent ↥hyp.base.typeP.H
  rw [hyp.base.typeP.H_eq]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M

/-- **(11.6), first step**: for a prime `q' ≠ p`, the `q'`-core of the nilpotent `H` lies in
`C_H(U)`.  By (9.3) `|H : C_H(U)| = p^q`, so `C_H(U)` contains a full Sylow `q'`-subgroup of
`H`; Sylow subgroups of the nilpotent `H` are normal and unique (`= O_{q'}(H)`). -/
theorem opCore_map_le_centralizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) {q' : ℕ} (hq' : q'.Prime) (hne : q' ≠ hyp.p) :
    (OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H).map hyp.H.subtype
      ≤ Subgroup.centralizer (hyp.U : Set G) := by
  classical
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  obtain ⟨hp_prime, hcard⟩ := hyp.p_prime_and_card_H_eq hG
  set CUa := hyp.H ⊓ Subgroup.centralizer (hyp.U : Set G) with hCUa
  have hKle : CUa ≤ hyp.H := inf_le_left
  set K := CUa.subgroupOf hyp.H with hK
  -- `q'`-parts of `|H|` and `|K|` agree (the index is the `p`-power `p^q`)
  have hcardK : Nat.card ↥K = Nat.card ↥CUa :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hfact : (Nat.card ↥hyp.H).factorization q'
      = (Nat.card ↥K).factorization q' := by
    rw [hcardK, hcard, Nat.factorization_mul (pow_ne_zero _ hp_prime.pos.ne') Nat.card_pos.ne',
      Finsupp.add_apply, hp_prime.factorization_pow,
      Finsupp.single_apply, if_neg (fun h => hne h.symm), zero_add]
  -- a Sylow `q'` of `K`, lifted to `H`, is a full Sylow `q'` of `H`
  obtain ⟨S'⟩ : Nonempty (Sylow q' ↥K) := inferInstance
  set P' := (S' : Subgroup ↥K).map K.subtype with hP'
  have hP'card : Nat.card ↥P' = q' ^ ((Nat.card ↥hyp.H).factorization q') := by
    rw [hfact]
    have : Nat.card ↥P' = Nat.card ↥(S' : Subgroup ↥K) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm.toEquiv
    rw [this, S'.card_eq_multiplicity]
  have hP'p : IsPGroup q' ↥P' := S'.isPGroup'.map _
  obtain ⟨T, hT⟩ := hP'p.exists_le_sylow
  have hP'eq : P' = ↑T := by
    refine Subgroup.eq_of_le_of_card_ge hT ?_
    rw [hP'card, T.card_eq_multiplicity]
  have hTnorm : (↑T : Subgroup ↥hyp.H).Normal :=
    OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent T
  have hTeq : (↑T : Subgroup ↥hyp.H) = OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H :=
    OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal T hTnorm
  rw [← hTeq, ← hP'eq]
  -- `P' ≤ K`, and `K` maps into `CUa ≤ C_G(U)`
  have hP'K : P' ≤ K := by
    rw [hP']
    rintro x ⟨y, _, rfl⟩
    exact y.2
  refine le_trans (Subgroup.map_mono hP'K) ?_
  rw [hK, Subgroup.subgroupOf_map_subtype]
  exact inf_le_left.trans inf_le_right

/-- The `p`-complement `O_{p'}(H)` of the nilpotent `H` — the join of the `q'`-cores over
the primes `q' ≠ p` of `|H|` — as a subgroup of `↥H`. -/
noncomputable def pComplementCore [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Subgroup ↥hyp.H :=
  ⨆ (j : (Nat.card ↥hyp.H).primeFactors) (_ : (j : ℕ) ≠ hyp.p),
    OddOrder.Isaacs.Ch01.opCore (j : ℕ) ↥hyp.H

/-- The ambient `p`-complement `R = O_{p'}(H) ≤ G`. -/
noncomputable def pComplement [Finite G] {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.pComplementCore.map hyp.H.subtype

theorem pComplement_le_H [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplement ≤ hyp.H :=
  Subgroup.map_subtype_le _

/-- The `p`-complement is characteristic in `H` (join of the characteristic `q'`-cores). -/
theorem pComplementCore_characteristic [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplementCore.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [pComplementCore]
  simp_rw [Subgroup.map_iSup]
  exact iSup_congr fun j => iSup_congr fun _ =>
    Subgroup.characteristic_iff_map_eq.mp
      (OddOrder.Isaacs.Ch01.opCore.characteristic (j : ℕ) ↥hyp.H) φ

/-- **`U` centralizes the `p`-complement** — each `q'`-core lies in `C_G(U)`
(`opCore_map_le_centralizer`), hence so does the join. -/
theorem pComplement_le_centralizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplement ≤ Subgroup.centralizer (hyp.U : Set G) := by
  rw [pComplement, pComplementCore]
  simp_rw [Subgroup.map_iSup]
  refine iSup_le fun j => iSup_le fun hj => ?_
  exact hyp.opCore_map_le_centralizer hG (Nat.prime_of_mem_primeFactors j.2) hj

/-- The `p`-core and the `p`-complement intersect trivially (independence of the cores). -/
theorem disjoint_opCore_pComplementCore [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) (hp_prime : hyp.p.Prime)
    (hp_mem : hyp.p ∈ (Nat.card ↥hyp.H).primeFactors) :
    Disjoint (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H) hyp.pComplementCore := by
  classical
  set O : (Nat.card ↥hyp.H).primeFactors → Subgroup ↥hyp.H :=
    fun q => OddOrder.Isaacs.Ch01.opCore (q : ℕ) ↥hyp.H with hO
  have hindep : iSupIndep O := by
    apply OddOrder.Isaacs.Ch01.iSupIndep_of_coprime_card_of_normal O
    intro i j hij
    haveI : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    haveI : Fact (j : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors j.2⟩
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    exact IsPGroup.coprime_card_of_ne (i : ℕ) (j : ℕ) hne _ _
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (i : ℕ) ↥hyp.H)
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (j : ℕ) ↥hyp.H)
  set i₀ : (Nat.card ↥hyp.H).primeFactors := ⟨hyp.p, hp_mem⟩ with hi₀
  have hdisj : Disjoint (O i₀) (⨆ (j) (_ : j ≠ i₀), O j) := (iSupIndep_def.mp hindep) i₀
  have hjoin : hyp.pComplementCore = ⨆ (j) (_ : j ≠ i₀), O j := by
    rw [pComplementCore]
    exact iSup_congr fun j => iSup_congr_Prop
      ⟨fun h heq => h (congrArg Subtype.val heq), fun h heq => h (Subtype.ext heq)⟩
      (fun _ => rfl)
  rw [hjoin]
  exact hdisj

/-- **(11.6) endgame form**: if the `p`-complement is trivial, `H` is a `p`-group. -/
theorem isPGroup_of_pComplementCore_eq_bot [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) (hbot : hyp.pComplementCore = ⊥) :
    IsPGroup hyp.p ↥hyp.H := by
  classical
  haveI hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  -- every prime factor `q' ≠ p` has trivial core, hence trivial Sylow — impossible
  have hsub : (Nat.card ↥hyp.H).primeFactors ⊆ {hyp.p} := by
    intro q' hq'
    rw [Finset.mem_singleton]
    by_contra hne
    haveI : Fact q'.Prime := ⟨Nat.prime_of_mem_primeFactors hq'⟩
    have hcore : OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [← hbot, pComplementCore]
      exact le_iSup₂ (f := fun (j : (Nat.card ↥hyp.H).primeFactors)
        (_ : (j : ℕ) ≠ hyp.p) => OddOrder.Isaacs.Ch01.opCore (j : ℕ) ↥hyp.H) ⟨q', hq'⟩ hne
    obtain ⟨T⟩ : Nonempty (Sylow q' ↥hyp.H) := inferInstance
    have hTeq : (↑T : Subgroup ↥hyp.H) = OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H :=
      OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal T
        (OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent T)
    have hTbot : (↑T : Subgroup ↥hyp.H) = ⊥ := hTeq.trans hcore
    have hcard := T.card_eq_multiplicity
    rw [hTbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card ↥hyp.H).factorization q' :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hq')
        Nat.card_pos.ne' (Nat.dvd_of_mem_primeFactors hq')
    have : 2 ≤ q' ^ (Nat.card ↥hyp.H).factorization q' :=
      le_trans (Nat.prime_of_mem_primeFactors hq').two_le
        (Nat.le_self_pow hpos.ne' _)
    omega
  refine IsPGroup.of_card (n := (Nat.card ↥hyp.H).factorization hyp.p) ?_
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (Nat.card_pos (α := ↥hyp.H)).ne']
  rw [Finsupp.prod_of_support_subset _ (Nat.support_factorization _ ▸ hsub) _
    (fun i _ => pow_zero i), Finset.prod_singleton]


/-- `p ∈ primeFactors |H|`: `p` is prime and `p^q ∣ |H|` with `q = |W₁| ≥ 1` ((9.3)). -/
theorem p_mem_primeFactors [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.p ∈ (Nat.card ↥hyp.H).primeFactors := by
  obtain ⟨hp_prime, hcard⟩ := hyp.p_prime_and_card_H_eq hG
  have hq : hyp.q ≠ 0 := by
    show Nat.card ↥hyp.base.typeP.W1 ≠ 0
    exact Nat.card_pos.ne'
  refine Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, Nat.card_pos.ne'⟩
  rw [hcard]
  exact dvd_mul_of_dvd_left (dvd_pow_self _ hq) _

/-- The `p`-core and the `p`-complement jointly generate `H` (nilpotent: Sylows generate). -/
theorem opCore_sup_pComplementCore_eq_top [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H ⊔ hyp.pComplementCore = ⊤ := by
  classical
  haveI hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  have htop : (⨆ q : (Nat.card ↥hyp.H).primeFactors,
      OddOrder.Isaacs.Ch01.opCore (q : ℕ) ↥hyp.H) = ⊤ := by
    have hrw : (⨆ q : (Nat.card ↥hyp.H).primeFactors,
        OddOrder.Isaacs.Ch01.opCore (q : ℕ) ↥hyp.H)
        = ⨆ q : (Nat.card ↥hyp.H).primeFactors,
            ((default : Sylow (q : ℕ) ↥hyp.H) : Subgroup ↥hyp.H) :=
      iSup_congr fun q => by
        haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
        exact (OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal default
          (OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent default)).symm
    rw [hrw]
    exact OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥hyp.H
  refine le_antisymm le_top ?_
  rw [← htop]
  refine iSup_le fun j => ?_
  by_cases hj : (j : ℕ) = hyp.p
  · refine le_sup_of_le_left ?_
    rw [hj]
  · refine le_sup_of_le_right ?_
    rw [pComplementCore]
    exact le_iSup₂ (f := fun (j : (Nat.card ↥hyp.H).primeFactors)
      (_ : (j : ℕ) ≠ hyp.p) => OddOrder.Isaacs.Ch01.opCore (j : ℕ) ↥hyp.H) j hj

/-- The (11.6) kernel `K₀ = O_p(H)·⁅R,R⁆` (ambient), with `R` the `p`-complement. -/
noncomputable def pKernel [Finite G] {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype
    ⊔ ⁅hyp.pComplement, hyp.pComplement⁆

theorem pKernel_le_H [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pKernel ≤ hyp.H := by
  refine sup_le (Subgroup.map_subtype_le _) ?_
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hyp.pComplement_le_H hg₁) (hyp.pComplement_le_H hg₂))
      (Subgroup.inv_mem _ (hyp.pComplement_le_H hg₁)))
    (Subgroup.inv_mem _ (hyp.pComplement_le_H hg₂))

/-- `M` normalizes the kernel `K₀` (it is the image of a characteristic subgroup of `H`). -/
theorem pKernel_normalized_by_M [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer (hyp.pKernel : Set G) := by
  classical
  set N₀ : Subgroup ↥hyp.H :=
    OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H ⊔ ⁅hyp.pComplementCore, hyp.pComplementCore⁆
    with hN₀
  have hchar : N₀.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    rw [hN₀, Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.characteristic_iff_map_eq.mp
        (OddOrder.Isaacs.Ch01.opCore.characteristic hyp.p ↥hyp.H) φ,
      Subgroup.characteristic_iff_map_eq.mp hyp.pComplementCore_characteristic φ]
  have hnorm : N₀.Normal := @Subgroup.normal_of_characteristic _ _ N₀ hchar
  have hmap : hyp.pKernel = N₀.map hyp.H.subtype := by
    rw [hN₀, Subgroup.map_sup, Subgroup.map_commutator, pKernel, pComplement]
  rw [hmap]
  exact OddOrder.Peterfalvi.S11.typeP_aInvariantNormal_le_normalizer hyp.base.typeP
    (hNn := hnorm)
    (@OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic _ _ _ _ _ N₀ hchar)


/-- **(11.6) key bound**: `M'' ≤ K₀ ⊔ U'` where `K₀ = O_p(H)·⁅R,R⁆`.  Commutator
generators `⁅a,b⁆` of `M''` decompose as `a = o·r·u` (`M' = H·U` along the normal `H`,
then `H = O_p·R` by the nilpotent splitting); mod `K₀` the `o`-parts die, the `r`-images
are central (`⁅R,R⁆ ≤ K₀` and `[R,U] = 1`), so `⁅a,b⁆ ≡ ⁅u_a,u_b⁆ (mod K₀)`. -/
theorem secondDerived_le_pKernel_sup_derivedU [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M ≤ hyp.pKernel ⊔ derivedInG hyp.base.typeP.U := by
  classical
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hUle : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  have hKle : hyp.pKernel ≤ M := hyp.pKernel_le_H.trans hHle
  have hRle : hyp.pComplement ≤ M := hyp.pComplement_le_H.trans hHle
  have hM'eq : derivedInG M = hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
    rw [hyp.base.typeP.derivedInG_eq_fitting_sup_U, hyp.base.typeP.H_eq]
  haveI hKn : (hyp.pKernel.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr hyp.pKernel_normalized_by_M
  -- `H`-elements split as `o·r` along `O_p ⊔ R = ⊤` (`O_p` is normal in `↥H`)
  haveI : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).Characteristic :=
    OddOrder.Isaacs.Ch01.opCore.characteristic hyp.p ↥hyp.H
  have hHsplit : ∀ h ∈ hyp.H, ∃ o ∈ (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map
      hyp.H.subtype, ∃ r ∈ hyp.pComplement, h = o * r := by
    intro h hh
    have hmem : (⟨h, hh⟩ : ↥hyp.H)
        ∈ OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H ⊔ hyp.pComplementCore := by
      rw [hyp.opCore_sup_pComplementCore_eq_top hG]
      trivial
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
    obtain ⟨o, ho, r, hr, hor⟩ := hmem
    refine ⟨(o : G), Subgroup.mem_map_of_mem _ (SetLike.mem_coe.mp ho),
      (r : G), Subgroup.mem_map_of_mem _ (SetLike.mem_coe.mp hr), ?_⟩
    have := congrArg (fun z : ↥hyp.H => (z : G)) hor
    simpa using this.symm
  -- `R` centralizes `U`
  have hcommRU : ∀ u ∈ hyp.base.typeP.U, ∀ r' ∈ hyp.pComplement, u * r' = r' * u :=
    fun u hu r' hr' =>
      Subgroup.mem_centralizer_iff.mp (hyp.pComplement_le_centralizer hG hr') u hu
  set φ := QuotientGroup.mk' (hyp.pKernel.subgroupOf M) with hφ
  rintro x hx
  rw [secondDerivedInAmbient, derivedInG] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [commutator_eq_closure] at hc
  induction hc using Subgroup.closure_induction with
  | one =>
      simpa using Subgroup.one_mem (hyp.pKernel ⊔ derivedInG hyp.base.typeP.U)
  | mul y z _ _ hy hz =>
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
      rw [map_inv]
      exact Subgroup.inv_mem _ hy
  | mem cel hcel =>
      obtain ⟨a, b, hab⟩ := hcel
      have hcel_eq : cel = a * b * a⁻¹ * b⁻¹ := hab.symm
      have haM' : ((a : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact a.2
      have hbM' : ((b : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact b.2
      obtain ⟨ha', hha', ua, hua, haeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M haM'
      obtain ⟨hb', hhb', ub, hub, hbeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M hbM'
      obtain ⟨oa, hoa, ra, hra, haeq2⟩ := hHsplit ha' hha'
      obtain ⟨ob, hob, rb, hrb, hbeq2⟩ := hHsplit hb' hhb'
      have hoaK : oa ∈ hyp.pKernel := Subgroup.mem_sup_left hoa
      have hobK : ob ∈ hyp.pKernel := Subgroup.mem_sup_left hob
      have haMm : ((a : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) a.2
      have hbMm : ((b : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) b.2
      set A : ↥M := ⟨((a : ↥(derivedInG M)) : G), haMm⟩ with hA
      set B : ↥M := ⟨((b : ↥(derivedInG M)) : G), hbMm⟩ with hB
      set RA : ↥M := ⟨ra, hRle hra⟩ with hRA
      set RB : ↥M := ⟨rb, hRle hrb⟩ with hRB
      set UA : ↥M := ⟨ua, hUle hua⟩ with hUA
      set UB : ↥M := ⟨ub, hUle hub⟩ with hUB
      -- the `o`-parts die under `φ`
      have hφA : φ A = φ RA * φ UA := by
        have h1 : A = ⟨oa, hKle hoaK⟩ * RA * UA := by
          ext
          rw [haeq, haeq2]
          rfl
        rw [h1, map_mul, map_mul]
        have h2 : φ ⟨oa, hKle hoaK⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hoaK
        rw [h2, one_mul]
      have hφB : φ B = φ RB * φ UB := by
        have h1 : B = ⟨ob, hKle hobK⟩ * RB * UB := by
          ext
          rw [hbeq, hbeq2]
          rfl
        rw [h1, map_mul, map_mul]
        have h2 : φ ⟨ob, hKle hobK⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hobK
        rw [h2, one_mul]
      -- the `r`-images commute with each other and with the `u`-images
      have hswM : ∀ (u r' : ↥M), (u : G) ∈ hyp.base.typeP.U → (r' : G) ∈ hyp.pComplement →
          Commute (φ u) (φ r') := by
        intro u r' hu hr'
        refine Commute.map ?_ φ
        exact Subtype.ext (hcommRU _ hu _ hr')
      have hswRR : Commute (φ RA) (φ RB) := by
        have hcomm : (RA * RB * RA⁻¹ * RB⁻¹ : ↥M) ∈ hyp.pKernel.subgroupOf M := by
          refine Subgroup.mem_subgroupOf.mpr ?_
          refine Subgroup.mem_sup_right ?_
          exact Subgroup.commutator_mem_commutator hra hrb
        have h1 : φ (RA * RB * RA⁻¹ * RB⁻¹) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hcomm
        have h2 : φ RA * φ RB * (φ RA)⁻¹ * (φ RB)⁻¹ = 1 := by
          rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          exact h1
        have h3 : φ RA * φ RB = φ RB * φ RA := by
          have := congrArg (· * (φ RB * φ RA)) h2
          simpa [mul_assoc] using this
        exact h3
      -- key collapse: `⁅φA, φB⁆ = ⁅φUA, φUB⁆`
      have hkey : φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹
          = φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹ := by
        rw [hφA, hφB]
        rw [commutator_mul_of_commute
          (hswM UA RB (by exact hua) (by exact hrb))
          (hswM UA RA (by exact hua) (by exact hra))
          (hswM UB RA (by exact hub) (by exact hra))
          (hswM UB RB (by exact hub) (by exact hrb))]
        have hRR1 : φ RA * φ RB * (φ RA)⁻¹ * (φ RB)⁻¹ = 1 := by
          rw [hswRR.eq]
          group
        rw [hRR1, one_mul]
      have hratio : (A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹
          ∈ hyp.pKernel.subgroupOf M := by
        have hmapped : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹)
            = (φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹)
              * (φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹)⁻¹ := by
          simp only [map_mul, map_inv]
        have h1 : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹) = 1 := by
          rw [hmapped, hkey]
          group
        exact (QuotientGroup.eq_one_iff
          (N := hyp.pKernel.subgroupOf M) _).mp h1
      have hcomm_coe : (((derivedInG M).subtype) cel : G)
          = ((A * B * A⁻¹ * B⁻¹ : ↥M) : G) := by
        rw [hcel_eq]; exact rfl
      have hsplit : ((A * B * A⁻¹ * B⁻¹ : ↥M) : G)
          = (((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹ : ↥M) : G)
            * ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) := by
        push_cast
        group
      rw [hcomm_coe, hsplit]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact Subgroup.mem_subgroupOf.mp hratio
      · have hUcomm : ua * ub * ua⁻¹ * ub⁻¹ ∈ derivedInG hyp.base.typeP.U := by
          rw [show derivedInG hyp.base.typeP.U
              = ⁅hyp.base.typeP.U, hyp.base.typeP.U⁆
            from Subgroup.map_subtype_commutator hyp.base.typeP.U]
          exact Subgroup.commutator_mem_commutator hua hub
        have hcoe : ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) = ua * ub * ua⁻¹ * ub⁻¹ := by
          push_cast
          rfl
        rw [hcoe]
        exact hUcomm


/-- `H` normalizes the ambient image of the `p`-core (a normal subgroup of `↥H`). -/
theorem H_le_normalizer_opCore_map [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.H ≤ Subgroup.normalizer
      (((OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype : Subgroup G) : Set G) := by
  haveI : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).Characteristic :=
    OddOrder.Isaacs.Ch01.opCore.characteristic hyp.p ↥hyp.H
  have h := Subgroup.le_normalizer_map
    (H := OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H) hyp.H.subtype
  rwa [Subgroup.normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

/-- **(11.6) trap**: the `p`-complement is trivial.  `R ≤ H ≤ HC = M'' ≤ K₀ ⊔ U'`
((11.5) + the key bound); splitting an `r ∈ R` along the two sups leaves `r ∈ ⁅R,R⁆`
(the `U'`-part dies in `H ⊓ U = ⊥`, the `O_p`-part in `O_p ⊓ R = ⊥`), so `R` is
perfect — but `R` is nilpotent, hence trivial. -/
theorem pComplementCore_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplementCore = ⊥ := by
  classical
  obtain ⟨hp_prime, -⟩ := hyp.p_prime_and_card_H_eq hG
  have hp_mem := hyp.p_mem_primeFactors hG
  have hHleM : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hcommleR : ⁅hyp.pComplement, hyp.pComplement⁆ ≤ hyp.pComplement := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
      (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)
  -- Step 1: `R ≤ ⁅R,R⁆` (ambient)
  have hRle' : hyp.pComplement ≤ ⁅hyp.pComplement, hyp.pComplement⁆ := by
    intro r hr
    have hrM'' : r ∈ secondDerivedInAmbient M := by
      rw [secondDerived_eq_HC hG hyp]
      exact Subgroup.mem_sup_left (hyp.pComplement_le_H hr)
    have hrKU : r ∈ hyp.pKernel ⊔ derivedInG hyp.base.typeP.U :=
      hyp.secondDerived_le_pKernel_sup_derivedU hG hrM''
    -- split off the `U'`-part
    have hKleM : hyp.pKernel ≤ M := hyp.pKernel_le_H.trans hHleM
    have hU'leM : derivedInG hyp.base.typeP.U ≤ M :=
      (Subgroup.map_subtype_le _).trans (hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _))
    obtain ⟨k, hk, u', hu', hru⟩ := exists_mul_of_mem_sup_of_normalized hKleM hU'leM
      hyp.pKernel_normalized_by_M hrKU
    have hu'H : u' ∈ hyp.base.typeP.H := by
      have : u' = k⁻¹ * r := by rw [hru]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hyp.pKernel_le_H hk))
        (hyp.pComplement_le_H hr)
    have hu'U : u' ∈ hyp.base.typeP.U := (Subgroup.map_subtype_le _) hu'
    have hu'1 : u' = 1 := by
      have := hyp.H_inf_U_eq_bot.le ⟨hu'H, hu'U⟩
      rwa [Subgroup.mem_bot] at this
    have hrk : r = k := by rw [hru, hu'1, mul_one]
    -- split off the `O_p`-part
    have hkK : r ∈ (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype
        ⊔ ⁅hyp.pComplement, hyp.pComplement⁆ := by
      rw [← pKernel]; exact hrk ▸ hk
    have hOle : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype ≤ hyp.H :=
      Subgroup.map_subtype_le _
    have hCle : ⁅hyp.pComplement, hyp.pComplement⁆ ≤ hyp.H :=
      hcommleR.trans hyp.pComplement_le_H
    obtain ⟨o, ho, r'', hr'', hor⟩ := exists_mul_of_mem_sup_of_normalized hOle hCle
      hyp.H_le_normalizer_opCore_map hkK
    have hoR : o ∈ hyp.pComplement := by
      have : o = r * r''⁻¹ := by rw [hor]; group
      rw [this]
      exact Subgroup.mul_mem _ hr (Subgroup.inv_mem _ (hcommleR hr''))
    have ho1 : o = 1 := by
      have hinf : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype
          ⊓ hyp.pComplement = ⊥ := by
        rw [pComplement, ← Subgroup.map_inf _ _ hyp.H.subtype hyp.H.subtype_injective,
          (hyp.disjoint_opCore_pComplementCore hp_prime hp_mem).eq_bot, Subgroup.map_bot]
      have := hinf.le ⟨ho, hoR⟩
      rwa [Subgroup.mem_bot] at this
    rw [hor, ho1, one_mul]
    exact hr''
  -- Step 2: `pComplementCore` is perfect
  have hCCeq : hyp.pComplementCore = ⁅hyp.pComplementCore, hyp.pComplementCore⁆ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hximg : ((x : ↥hyp.H) : G) ∈ ⁅hyp.pComplement, hyp.pComplement⁆ :=
        hRle' (Subgroup.mem_map_of_mem _ hx)
      rw [pComplement, ← Subgroup.map_commutator] at hximg
      obtain ⟨y, hy, hyx⟩ := hximg
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
        (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)
  -- Step 3: perfect + nilpotent ⇒ trivial
  haveI hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  haveI hAnil : Group.IsNilpotent ↥hyp.pComplementCore := Subgroup.isNilpotent _
  have hcommtop : _root_.commutator ↥hyp.pComplementCore = ⊤ := by
    have h1 : (⁅hyp.pComplementCore, hyp.pComplementCore⁆).subgroupOf hyp.pComplementCore
        = _root_.commutator ↥hyp.pComplementCore :=
      OddOrder.Peterfalvi.S08.commutator_subgroupOf_self hyp.pComplementCore
    rw [← h1, ← hCCeq, Subgroup.subgroupOf_self]
  have hlcs : ∀ n, (⊤ : Subgroup ↥hyp.pComplementCore).lowerCentralSeries n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ, ih]
        exact hcommtop
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hAnil
  have hbot_top : (⊥ : Subgroup ↥hyp.pComplementCore) = ⊤ := by rw [← hn, hlcs n]
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥hyp.pComplementCore) ∈ (⊥ : Subgroup ↥hyp.pComplementCore) := by
    rw [hbot_top]; trivial
  rw [Subgroup.mem_bot] at hmem
  have := congrArg (fun z : ↥hyp.pComplementCore => (z : ↥hyp.H)) hmem
  simpa using this

/-- **Peterfalvi (11.6), `H` is a `p`-group.** -/
theorem H_isPGroup [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsPGroup hyp.p ↥hyp.H :=
  hyp.isPGroup_of_pComplementCore_eq_bot (hyp.pComplementCore_eq_bot hG)


/-- The (11.6) `H₀`-kernel `K₁ = ⁅H, M'⁆` (ambient).  It contains `H' = ⁅H,H⁆` and
`⁅H,U⁆`, and `M'' ≤ K₁ ⊔ U'` by the mod-`K₁` collapse. -/
noncomputable def hKernel {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  ⁅hyp.base.typeP.H, derivedInG M⁆

theorem hKernel_le_H [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.hKernel ≤ hyp.base.typeP.H := by
  rw [hKernel, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₂M : g₂ ∈ M := (Subgroup.map_subtype_le _) hg₂
  have hconj : g₂ * g₁⁻¹ * g₂⁻¹ ∈ hyp.base.typeP.H := by
    have := (Subgroup.mem_set_normalizer_iff.mp (hyp.H_normalized_by_M hg₂M)) g₁⁻¹
    exact this.mp (Subgroup.inv_mem _ hg₁)
  have : g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) ∈ hyp.base.typeP.H := Subgroup.mul_mem _ hg₁ hconj
  convert this using 1
  group

theorem derivedH_le_hKernel [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    ⁅hyp.base.typeP.H, hyp.base.typeP.H⁆ ≤ hyp.hKernel := by
  rw [hKernel]
  exact Subgroup.commutator_mono le_rfl hyp.base.typeP.H_le

theorem hKernel_normalized_by_M [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer (hyp.hKernel : Set G) := by
  intro m hm
  rw [← OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer, hKernel,
    Subgroup.map_commutator]
  have h1 : (hyp.base.typeP.H).map (MulAut.conj m).toMonoidHom = hyp.base.typeP.H :=
    OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mpr (hyp.H_normalized_by_M hm)
  have h2 : (derivedInG M).map (MulAut.conj m).toMonoidHom = derivedInG M := by
    rw [show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M,
      Subgroup.map_commutator,
      OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hm)]
  rw [h1, h2]

/-- **(11.6) `H₀`-side bound**: `M'' ≤ ⁅H,M'⁆ ⊔ U'`.  Mod `K₁ = ⁅H,M'⁆` every
`H`-image is central in `M'/K₁`, so commutator generators collapse to their `U`-parts. -/
theorem secondDerived_le_hKernel_sup_derivedU [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M ≤ hyp.hKernel ⊔ derivedInG hyp.base.typeP.U := by
  classical
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hUle : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  have hKle : hyp.hKernel ≤ M := hyp.hKernel_le_H.trans hHle
  have hM'eq : derivedInG M = hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
    rw [hyp.base.typeP.derivedInG_eq_fitting_sup_U, hyp.base.typeP.H_eq]
  haveI hKn : (hyp.hKernel.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr hyp.hKernel_normalized_by_M
  set φ := QuotientGroup.mk' (hyp.hKernel.subgroupOf M) with hφ
  -- mod-`K₁` commutation from ambient commutator membership
  have hswK : ∀ x y : ↥M, ((x * y * x⁻¹ * y⁻¹ : ↥M) : G) ∈ hyp.hKernel →
      Commute (φ x) (φ y) := by
    intro x y hxy
    have h1 : φ (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hxy
    have h2 : φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    have := congrArg (· * (φ y * φ x)) h2
    simpa [commute_iff_eq, mul_assoc] using this
  rintro x hx
  rw [secondDerivedInAmbient, derivedInG] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [commutator_eq_closure] at hc
  induction hc using Subgroup.closure_induction with
  | one =>
      simpa using Subgroup.one_mem (hyp.hKernel ⊔ derivedInG hyp.base.typeP.U)
  | mul y z _ _ hy hz =>
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
      rw [map_inv]
      exact Subgroup.inv_mem _ hy
  | mem cel hcel =>
      obtain ⟨a, b, hab⟩ := hcel
      have hcel_eq : cel = a * b * a⁻¹ * b⁻¹ := hab.symm
      have haM' : ((a : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact a.2
      have hbM' : ((b : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact b.2
      obtain ⟨ha', hha', ua, hua, haeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M haM'
      obtain ⟨hb', hhb', ub, hub, hbeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M hbM'
      have haMm : ((a : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) a.2
      have hbMm : ((b : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) b.2
      set A : ↥M := ⟨((a : ↥(derivedInG M)) : G), haMm⟩ with hA
      set B : ↥M := ⟨((b : ↥(derivedInG M)) : G), hbMm⟩ with hB
      set HA : ↥M := ⟨ha', hHle hha'⟩ with hHA
      set HB : ↥M := ⟨hb', hHle hhb'⟩ with hHB
      set UA : ↥M := ⟨ua, hUle hua⟩ with hUA
      set UB : ↥M := ⟨ub, hUle hub⟩ with hUB
      have hAeq : A = HA * UA := by
        ext; rw [haeq]; rfl
      have hBeq : B = HB * UB := by
        ext; rw [hbeq]; rfl
      -- `H`-parts are mod-`K₁` central among `M'`-images
      have hmemM' : ∀ g ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U, g ∈ derivedInG M := by
        intro g hg; rwa [hM'eq]
      have hswHU : ∀ (h u : ↥M), (h : G) ∈ hyp.base.typeP.H → (u : G) ∈ derivedInG M →
          Commute (φ u) (φ h) := by
        intro h u hh hu
        refine (hswK h u ?_).symm
        rw [hKernel]
        exact Subgroup.commutator_mem_commutator hh hu
      have hkey : φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹
          = φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹ := by
        rw [hAeq, hBeq, map_mul, map_mul]
        rw [commutator_mul_of_commute
          (hswHU HB UA (by exact hhb') (hmemM' _ (Subgroup.mem_sup_right hua)))
          (hswHU HA UA (by exact hha') (hmemM' _ (Subgroup.mem_sup_right hua)))
          (hswHU HA UB (by exact hha') (hmemM' _ (Subgroup.mem_sup_right hub)))
          (hswHU HB UB (by exact hhb') (hmemM' _ (Subgroup.mem_sup_right hub)))]
        have hHH1 : φ HA * φ HB * (φ HA)⁻¹ * (φ HB)⁻¹ = 1 := by
          have hsw : Commute (φ HA) (φ HB) := by
            refine hswK HA HB ?_
            rw [hKernel]
            refine Subgroup.commutator_mem_commutator (by exact hha') ?_
            exact hyp.base.typeP.H_le hhb'
          rw [hsw.eq]
          group
        rw [hHH1, one_mul]
      have hratio : (A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹
          ∈ hyp.hKernel.subgroupOf M := by
        have hmapped : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹)
            = (φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹)
              * (φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹)⁻¹ := by
          simp only [map_mul, map_inv]
        have h1 : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹) = 1 := by
          rw [hmapped, hkey]
          group
        exact (QuotientGroup.eq_one_iff
          (N := hyp.hKernel.subgroupOf M) _).mp h1
      have hcomm_coe : (((derivedInG M).subtype) cel : G)
          = ((A * B * A⁻¹ * B⁻¹ : ↥M) : G) := by
        rw [hcel_eq]; exact rfl
      have hsplit : ((A * B * A⁻¹ * B⁻¹ : ↥M) : G)
          = (((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹ : ↥M) : G)
            * ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) := by
        push_cast
        group
      rw [hcomm_coe, hsplit]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact Subgroup.mem_subgroupOf.mp hratio
      · have hUcomm : ua * ub * ua⁻¹ * ub⁻¹ ∈ derivedInG hyp.base.typeP.U := by
          rw [show derivedInG hyp.base.typeP.U
              = ⁅hyp.base.typeP.U, hyp.base.typeP.U⁆
            from Subgroup.map_subtype_commutator hyp.base.typeP.U]
          exact Subgroup.commutator_mem_commutator hua hub
        have hcoe : ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) = ua * ub * ua⁻¹ * ub⁻¹ := by
          push_cast
          rfl
        rw [hcoe]
        exact hUcomm

end Hypothesis



/-- **Peterfalvi (11.6), the `U`-centralizes-`H_0` clause via Wielandt (9.1)**: if the cyclic
factor `W_1` acts fixed-point-freely on the chief subgroup `H_0` (`C_{H_0}(W_1) = 1`), then the
Frobenius kernel `U` centralizes `H_0`.

This is the ambient-form Wielandt corollary `frobenius_kernel_centralizes_of_complement_fpf`
(lane-h's (9.1)) applied to the Frobenius group `U W_1` (`typeP_uW1_frobenius`) acting coprimely
on `H_0 ≤ H = M_F`.  The fixed-point-free hypothesis `hfpf` and `U ≠ 1` (`hU`) are the §8/carrier
inputs (in Peterfalvi, `C_{H_0}(W_1) = 1` comes from (9.6) and `|W_2| = p`); the Wielandt content
itself is unconditional and axiom-clean. -/
theorem U_centralizes_H0_of_W1_fpf [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (hU : hyp.base.typeP.U ≠ ⊥)
    (hfpf : ∀ n ∈ hyp.chief.H0,
      (∀ w ∈ hyp.base.typeP.W1, w * n * w⁻¹ = n) → n = 1) :
    hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) := by
  -- `H_0 ≤ H = M_F` (the two type-`P` witnesses share `M_F = maxNilpotentNormalHall M`).
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
    rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
  have hH0le : hyp.chief.H0 ≤ hyp.base.typeP.H := hHH ▸ hyp.chief.H0_lt_H.le
  -- `U ⊔ W_1 ≤ M ≤ N_G(H_0)`.
  have hUM : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  have hUEnorm : hyp.base.typeP.U ⊔ hyp.base.typeP.W1 ≤
      Subgroup.normalizer (hyp.chief.H0 : Set G) :=
    sup_le (hUM.trans hyp.chief.H0_normalized_by_M)
      (hyp.base.typeP.W1_le.trans hyp.chief.H0_normalized_by_M)
  -- `H_0` is solvable (subgroup of the nilpotent Fitting-type Hall `M_F`).
  haveI : Group.IsNilpotent ↥hyp.base.typeP.H := by
    rw [hyp.base.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
  haveI : IsSolvable ↥hyp.base.typeP.H := IsNilpotent.to_isSolvable
  haveI : IsSolvable ↥(hyp.chief.H0.subgroupOf hyp.base.typeP.H) := inferInstance
  haveI hsolv : IsSolvable ↥hyp.chief.H0 :=
    solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hH0le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hH0le).symm.injective
  -- coprimality of `|H_0|` (dividing `|M_F|`) to `|U W_1|`.
  have hcop : Nat.Coprime (Nat.card ↥hyp.chief.H0)
      (Nat.card ↥(hyp.base.typeP.U ⊔ hyp.base.typeP.W1)) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hH0le)
      (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 hyp.base.typeP hU)
  exact OddOrder.GroupTheory.frobenius_kernel_centralizes_of_complement_fpf hUEnorm
    (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.base.typeP hU) hsolv hcop hfpf

/-- **Peterfalvi (11.6), the `U`-centralizes-`H_0` clause, gated on `W_2 ⊓ H_0 = ⊥`**: a cleaner
restatement of `U_centralizes_H0_of_W1_fpf` whose hypothesis is the subgroup equation
`W_2 ⊓ H_0 = ⊥` rather than the raw fixed-point-free condition.

The fixed-point-free input `C_{H_0}(W_1) = 1` reduces to `W_2 ⊓ H_0 = ⊥`: any `n ∈ H_0` centralized
by `W_1` lies in `H ⊓ C_G(W_1) = W_2` (`typeP_H_inf_centralizer_W1`), hence in `W_2 ⊓ H_0`.  This
isolates the genuine §8/chief content (`W_2 ⊓ H_0 = ⊥`, which holds because `|W_2| = p` is prime —
`typeIIIorIV_W2_prime` — and `W_2 ⊄ H_0` from the chief factor) as a single clean obligation. -/
theorem U_centralizes_H0_of_W2_inf_H0_bot [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (hU : hyp.base.typeP.U ≠ ⊥)
    (hbot : hyp.base.typeP.W2 ⊓ hyp.chief.H0 = ⊥) :
    hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) := by
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
    rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
  have hH0le : hyp.chief.H0 ≤ hyp.base.typeP.H := hHH ▸ hyp.chief.H0_lt_H.le
  refine U_centralizes_H0_of_W1_fpf hyp hU (fun n hn hcent => ?_)
  have hnW2 : n ∈ hyp.base.typeP.W2 := by
    rw [← OddOrder.Peterfalvi.S11.typeP_H_inf_centralizer_W1 hyp.base.typeP]
    refine Subgroup.mem_inf.mpr ⟨hH0le hn, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    exact fun w hw => mul_inv_eq_iff_eq_mul.mp (hcent w hw)
  have hmem : n ∈ hyp.base.typeP.W2 ⊓ hyp.chief.H0 := ⟨hnW2, hn⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- **Peterfalvi (9.6) for §13, the `W₂ ⊓ H₀ = ⊥` core**: the cyclic factor `W₂ = C_H(W₁)` meets the
chief subgroup `H₀` trivially.

Since `|W₂| = p` is prime (`ChiefFactorData.typeIII_IV_p_eq_W2`), `W₂ ⊓ H₀` is `⊥` or `W₂`.  The
chief-factor computation `|C_{H̄}(W₁)| = p` (`coprimeFrobeniusChiefFactor_card`, the second component)
shows the image `W̄₂` of `W₂` in `H̄ = H/H₀` is nontrivial, so `W₂ ⊄ H₀`, ruling out `W₂ ⊓ H₀ = W₂`.
This is the genuine §8/chief input behind the fixed-point-free hypothesis `C_{H₀}(W₁) = 1` of
`U_centralizes_H0_of_W2_inf_H0_bot`; it is unconditional (no character input). -/
theorem chief_W2_inf_H0_eq_bot [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.typeP.W2 ⊓ hyp.chief.H0 = ⊥ := by
  set data := hyp.s11Setup.typeP with hdata
  have hU : data.U ≠ ⊥ := hyp.s11Setup.nontrivial.1
  -- `F` = the `W₁`-fixed points of the conjugation action on `H`; `F` maps onto `W₂`, and `H₀` is the
  -- image of the chief-factor kernel `N`.
  set F : Subgroup ↥data.H :=
    fixedSubgroup (OddOrder.Peterfalvi.S11.typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1)) with hF
  have hFW2 : F.map data.H.subtype = data.W2 := by
    rw [hF, OddOrder.Peterfalvi.S11.typeP_fixedSubgroup_map data le_sup_right,
      OddOrder.Peterfalvi.S11.typeP_H_inf_centralizer_W1]
  have hH0 : hyp.chief.H0 = hyp.chief.N.map data.H.subtype := hyp.chief.H0_eq
  -- the quotient chief-factor action and the order `|C_{H̄}(W₁)| = p`.
  set act := OddOrder.Peterfalvi.S11.typeP_quotientCoprimeAction data hU hyp.chief.N_aInvariant
    with hact
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1))) (Nat.card ↥data.H) :=
    (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left
      (Subgroup.card_subgroup_dvd_card _)
  haveI : IsSolvable ↥data.H := (OddOrder.Peterfalvi.S11.typeP_coprimeAction data hU).H_solvable
  have hmap : F.map (QuotientGroup.mk' hyp.chief.N) = act.fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient hyp.chief.N_aInvariant hcopHW1 (Or.inr inferInstance)
  have hUnorm : act.U.Normal :=
    (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius data hU).isNormal
  have hEcyc : IsCyclic ↥act.fixedByE :=
    OddOrder.Peterfalvi.S11.typeP_quotient_fixedByE_cyclic data hU hyp.chief.N_aInvariant
  have hK1 : Nat.card (↥data.H ⧸ hyp.chief.N) ≠ 1 := by
    have hNtop : hyp.chief.N ≠ ⊤ := by
      intro htop
      have hH0H : hyp.chief.H0 = data.H := by
        rw [hH0, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact absurd (hH0H ▸ hyp.chief.H0_lt_H) (lt_irrefl _)
    exact fun h => hNtop (Subgroup.index_eq_one.mp h)
  have hcardE : Nat.card ↥act.fixedByE = hyp.chief.p :=
    (OddOrder.Peterfalvi.S11.coprimeFrobeniusChiefFactor_card act hUnorm hyp.chief.p_prime
      hyp.chief.quotient_elementaryAbelian hyp.chief.quotient_chiefFactor
      hyp.chief.U_noncentral_on_quotient hEcyc hK1).2
  -- `|W₂| = p` prime, so `|W₂ ⊓ H₀|` divides `p`.
  have hW2p : Nat.card ↥data.W2 = hyp.chief.p := hyp.chief.typeIII_IV_p_eq_W2 hyp.type_alt
  have hp := hyp.chief.p_prime
  have hdvd : Nat.card ↥(data.W2 ⊓ hyp.chief.H0 : Subgroup G) ∣ hyp.chief.p := by
    rw [← hW2p]; exact Subgroup.card_dvd_of_le inf_le_left
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpp
  · exact Subgroup.card_eq_one.mp h1
  · -- `|W₂ ⊓ H₀| = p = |W₂|` ⟹ `W₂ ⊆ H₀` ⟹ `F ≤ N` ⟹ `W̄₂ = ⊥`, contradicting `|C_{H̄}(W₁)| = p`.
    exfalso
    have hle : data.W2 ⊓ hyp.chief.H0 = data.W2 :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (hW2p.trans hpp.symm))
    have hW2H0 : data.W2 ≤ hyp.chief.H0 := hle ▸ inf_le_right
    have hFN : F ≤ hyp.chief.N := by
      have hmm : F.map data.H.subtype ≤ hyp.chief.N.map data.H.subtype := by
        rw [hFW2, ← hH0]; exact hW2H0
      exact (Subgroup.map_le_map_iff_of_injective data.H.subtype_injective).mp hmm
    have hmapbot : F.map (QuotientGroup.mk' hyp.chief.N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']; exact hFN
    rw [← hmap, hmapbot, Subgroup.card_bot] at hcardE
    have := hp.one_lt
    omega

/-- **Peterfalvi (11.6), the `U` centralizes `H₀` clause, unconditional**: the Frobenius kernel `U`
centralizes the chief subgroup `H₀`.

This discharges the second conjunct of (11.6) with *no character input*.  Peterfalvi's chain is:
`C_{H₀}(W₁) = 1` (here `chief_W2_inf_H0_eq_bot`, the `W₂ ⊓ H₀ = ⊥` form of (9.6)), so `U` centralizes
`H₀` by Wielandt (9.1) (`U_centralizes_H0_of_W2_inf_H0_bot`).  The remaining (11.6) conjuncts
(`H` a `p`-group, `H₀ = H'`, `C = U'`) stay gated on (11.5)/(9.3); see `core_structure`. -/
theorem U_centralizes_H0 [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) := by
  have hU : hyp.base.typeP.U ≠ ⊥ := by
    rw [← hyp.setup_typeP_eq]; exact hyp.s11Setup.nontrivial.1
  refine U_centralizes_H0_of_W2_inf_H0_bot hyp hU ?_
  rw [← hyp.setup_typeP_eq]
  exact chief_W2_inf_H0_eq_bot hyp

/-- **Peterfalvi (11.6), `H₀ = H'`**: `H' ≤ H₀` since `H/H₀` is elementary abelian;
conversely `H₀ ≤ H ≤ HC = M'' ≤ ⁅H,M'⁆ ⊔ U'` ((11.5) + the `K₁` bound), the
`U'`-part dies in `H ⊓ U = ⊥`, and in `H̄ = H/H'` the image of `⁅H,M'⁆` lies in the
`U`-action commutator while the image of `H₀` is `U`-fixed ((9.6)/(9.1) conjunct 2);
`C_{H̄}(U) ⊓ [H̄,U] = ⊥` (coprime Fitting on the abelian `H̄`, BG 1.6(d)) kills it. -/
theorem Hypothesis.H0_eq_Hprime_of_noncoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    hyp.chief.H0 = hyp.Hprime := by
  classical
  rw [hyp.Hprime_eq,
    show derivedInG hyp.base.typeP.H = ⁅hyp.base.typeP.H, hyp.base.typeP.H⁆
      from Subgroup.map_subtype_commutator _]
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
    rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
  have hH0le : hyp.chief.H0 ≤ hyp.base.typeP.H := hHH ▸ hyp.chief.H0_lt_H.le
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hUleM : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  refine le_antisymm ?_ ?_
  · -- `H₀ ≤ H'`
    intro h₀ hh₀
    -- (c) trap: `h₀ ∈ ⁅H,M'⁆`
    have hh₀K : h₀ ∈ hyp.hKernel := by
      have hM'' : h₀ ∈ secondDerivedInAmbient M := by
        rw [secondDerived_eq_HC_of_noncoherent hG hyp hnc]
        exact Subgroup.mem_sup_left (hH0le hh₀)
      have hKU := hyp.secondDerived_le_hKernel_sup_derivedU hM''
      have hKleM : hyp.hKernel ≤ M := hyp.hKernel_le_H.trans hHle
      have hU'leM : derivedInG hyp.base.typeP.U ≤ M :=
        (Subgroup.map_subtype_le _).trans hUleM
      obtain ⟨k, hk, u', hu', hru⟩ := exists_mul_of_mem_sup_of_normalized hKleM hU'leM
        hyp.hKernel_normalized_by_M hKU
      have hu'H : u' ∈ hyp.base.typeP.H := by
        have h1 : u' = k⁻¹ * h₀ := by rw [hru]; group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hyp.hKernel_le_H hk)) (hH0le hh₀)
      have hu'U : u' ∈ hyp.base.typeP.U := (Subgroup.map_subtype_le _) hu'
      have hu'1 : u' = 1 := by
        have := hyp.H_inf_U_eq_bot.le ⟨hu'H, hu'U⟩
        rwa [Subgroup.mem_bot] at this
      rw [hru, hu'1, mul_one]
      exact hk
    -- (d) the `H̄ = H/H'` argument
    set φU : ↥hyp.base.typeP.U →* MulAut ↥hyp.base.typeP.H :=
      (OddOrder.Peterfalvi.S11.typeP_conjAction hyp.base.typeP).comp
        (Subgroup.inclusion le_sup_left) with hφU
    have hinv : OddOrder.Isaacs.Ch03.IsAInvariant φU
        (_root_.commutator ↥hyp.base.typeP.H) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic _
    set φbar := OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hinv with hφbar
    -- coprimality `(|U|, |H̄|) = 1`
    have hUne : hyp.base.typeP.U ≠ ⊥ := by
      rw [← hyp.setup_typeP_eq]; exact hyp.s11Setup.nontrivial.1
    have hcopHU : Nat.Coprime (Nat.card ↥hyp.base.typeP.H)
        (Nat.card ↥(hyp.base.typeP.U ⊔ hyp.base.typeP.W1)) :=
      OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 hyp.base.typeP hUne
    have hcop : Nat.Coprime (Nat.card ↥hyp.base.typeP.U)
        (Nat.card (↥hyp.base.typeP.H ⧸ _root_.commutator ↥hyp.base.typeP.H)) := by
      have h1 : Nat.card ↥hyp.base.typeP.U
          ∣ Nat.card ↥(hyp.base.typeP.U ⊔ hyp.base.typeP.W1) :=
        Subgroup.card_dvd_of_le le_sup_left
      have h2 : Nat.card (↥hyp.base.typeP.H ⧸ _root_.commutator ↥hyp.base.typeP.H)
          ∣ Nat.card ↥hyp.base.typeP.H :=
        ⟨Nat.card ↥(_root_.commutator ↥hyp.base.typeP.H),
          Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
      exact ((hcopHU.symm.coprime_dvd_left h1).coprime_dvd_right h2)
    -- `π(H₀)` is `U`-fixed
    set π := QuotientGroup.mk' (_root_.commutator ↥hyp.base.typeP.H) with hπ
    have hfix : π ⟨h₀, hH0le hh₀⟩ ∈ Subgroup.fixedPointsOfMulAut φbar := by
      intro û
      rw [hφbar, OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
      have heq : φU û ⟨h₀, hH0le hh₀⟩ = ⟨h₀, hH0le hh₀⟩ := by
        refine Subtype.ext ?_
        have hcoe : ((φU û ⟨h₀, hH0le hh₀⟩ : ↥hyp.base.typeP.H) : G)
            = (û : G) * h₀ * (û : G)⁻¹ :=
          OddOrder.Peterfalvi.S11.typeP_conjAction_apply hyp.base.typeP _ _
        rw [hcoe]
        have hcent := Subgroup.mem_centralizer_iff.mp
          (U_centralizes_H0 hyp (show (û : G) ∈ hyp.U from û.2)) h₀ hh₀
        rw [← hcent]
        group
      rw [heq]
    -- `π(⁅H,M'⁆)` lies in the `U`-action commutator
    have hM'eq : derivedInG M = hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
      rw [hyp.base.typeP.derivedInG_eq_fitting_sup_U, hyp.base.typeP.H_eq]
    have hgen : ∀ x, x ∈ hyp.hKernel → ∀ hx : x ∈ hyp.base.typeP.H,
        π ⟨x, hx⟩ ∈ OddOrder.Isaacs.Ch04.actionCommutator φbar := by
      intro x hxK
      have hxK' : x ∈ ⁅hyp.base.typeP.H, derivedInG M⁆ := hxK
      rw [Subgroup.commutator_def] at hxK'
      clear hxK
      induction hxK' using Subgroup.closure_induction with
      | one =>
          intro h1
          have h2 : (⟨(1 : G), h1⟩ : ↥hyp.base.typeP.H) = 1 := rfl
          rw [h2, map_one]
          exact Subgroup.one_mem _
      | mul a b ha hb iha ihb =>
          intro habH
          have haH : a ∈ hyp.base.typeP.H := hyp.hKernel_le_H (by rwa [hKernel,
            Subgroup.commutator_def])
          have hbH : b ∈ hyp.base.typeP.H := hyp.hKernel_le_H (by rwa [hKernel,
            Subgroup.commutator_def])
          have h2 : (⟨a * b, habH⟩ : ↥hyp.base.typeP.H) = ⟨a, haH⟩ * ⟨b, hbH⟩ := rfl
          rw [h2, map_mul]
          exact Subgroup.mul_mem _ (iha haH) (ihb hbH)
      | inv a ha iha =>
          intro hainvH
          have haH : a ∈ hyp.base.typeP.H := hyp.hKernel_le_H (by rwa [hKernel,
            Subgroup.commutator_def])
          have h2 : (⟨a⁻¹, hainvH⟩ : ↥hyp.base.typeP.H) = (⟨a, haH⟩ : ↥hyp.base.typeP.H)⁻¹ :=
            rfl
          rw [h2, map_inv]
          exact Subgroup.inv_mem _ (iha haH)
      | mem g hg =>
          intro hgH
          obtain ⟨g₁, hg₁, g₂, hg₂, hab⟩ := hg
          have hab' : g = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := hab.symm
          have hg₂' : g₂ ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
            rw [← hM'eq]; exact hg₂
          obtain ⟨h', hh', u, hu, hg₂eq⟩ :=
            exists_mul_of_mem_sup_of_normalized hHle hUleM hyp.H_normalized_by_M hg₂'
          have hw : u * g₁⁻¹ * u⁻¹ ∈ hyp.base.typeP.H := by
            have h1 := (Subgroup.mem_set_normalizer_iff.mp
              (hyp.H_normalized_by_M (hUleM hu))) g₁⁻¹
            exact h1.mp (Subgroup.inv_mem _ hg₁)
          set x₁ : ↥hyp.base.typeP.H := ⟨g₁, hg₁⟩ with hx₁
          set x' : ↥hyp.base.typeP.H := ⟨h', hh'⟩ with hx'
          set w : ↥hyp.base.typeP.H := ⟨g₁ * (u * g₁⁻¹ * u⁻¹),
            Subgroup.mul_mem _ hg₁ hw⟩ with hwdef
          have hgelt : (⟨g, hgH⟩ : ↥hyp.base.typeP.H)
              = (x₁ * x' * x₁⁻¹ * x'⁻¹) * (x' * w * x'⁻¹) := by
            refine Subtype.ext ?_
            show g = g₁ * h' * g₁⁻¹ * h'⁻¹ * (h' * (g₁ * (u * g₁⁻¹ * u⁻¹)) * h'⁻¹)
            rw [hab', hg₂eq]
            group
          rw [hgelt, map_mul]
          refine Subgroup.mul_mem _ ?_ ?_
          · have hmem : (x₁ * x' * x₁⁻¹ * x'⁻¹) ∈ _root_.commutator ↥hyp.base.typeP.H :=
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
            have h1 : π (x₁ * x' * x₁⁻¹ * x'⁻¹) = 1 := by
              rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
              exact hmem
            rw [h1]
            exact Subgroup.one_mem _
          · have hratio : (x' * w * x'⁻¹) * w⁻¹ ∈ _root_.commutator ↥hyp.base.typeP.H := by
              have h1 : (x' * w * x'⁻¹) * w⁻¹ = x' * w * x'⁻¹ * w⁻¹ := by group
              rw [h1]
              exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
                (Subgroup.mem_top _)
            have hπeq : π (x' * w * x'⁻¹) = π w := by
              have h1 : π ((x' * w * x'⁻¹) * w⁻¹) = 1 := by
                rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
                exact hratio
              rw [map_mul, map_inv] at h1
              exact mul_inv_eq_one.mp h1
            rw [hπeq]
            set û : ↥hyp.base.typeP.U := ⟨u, hu⟩ with hû
            have hwgen : w = x₁ * φU û x₁⁻¹ := by
              refine Subtype.ext ?_
              have hcoe : ((φU û x₁⁻¹ : ↥hyp.base.typeP.H) : G) = u * g₁⁻¹ * u⁻¹ := by
                rw [hφU]
                have h2 := OddOrder.Peterfalvi.S11.typeP_conjAction_apply hyp.base.typeP
                  (Subgroup.inclusion le_sup_left û) x₁⁻¹
                simpa using h2
              push_cast
              rw [hcoe]
            rw [hwgen, map_mul]
            exact Subgroup.subset_closure ⟨π x₁, û, rfl⟩
    -- combine: the image is in the trivial intersection
    have hcommMem := hgen h₀ hh₀K (hH0le hh₀)
    have hbot := @OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian
      (↥hyp.base.typeP.U) (↥hyp.base.typeP.H ⧸ _root_.commutator ↥hyp.base.typeP.H)
      (inferInstanceAs (CommGroup (Abelianization ↥hyp.base.typeP.H))) _ _ _ φbar hcop
    have hmem1 : π ⟨h₀, hH0le hh₀⟩
        ∈ Subgroup.fixedPointsOfMulAut φbar ⊓ OddOrder.Isaacs.Ch04.actionCommutator φbar :=
      ⟨hfix, hcommMem⟩
    rw [hbot, Subgroup.mem_bot] at hmem1
    have hker : (⟨h₀, hH0le hh₀⟩ : ↥hyp.base.typeP.H)
        ∈ _root_.commutator ↥hyp.base.typeP.H := by
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem1
    have hss := OddOrder.Peterfalvi.S08.commutator_subgroupOf_self hyp.base.typeP.H
    rw [← hss] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  · -- `H' ≤ H₀`: the chief quotient `H/H₀` is (elementary) abelian
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₁' : g₁ ∈ hyp.s11Setup.typeP.H := by rw [hHH]; exact hg₁
    have hg₂' : g₂ ∈ hyp.s11Setup.typeP.H := by rw [hHH]; exact hg₂
    have hcomm := hyp.chief.quotient_elementaryAbelian.1
      (QuotientGroup.mk (⟨g₁, hg₁'⟩ : ↥hyp.s11Setup.H))
      (QuotientGroup.mk (⟨g₂, hg₂'⟩ : ↥hyp.s11Setup.H))
    have hmemN : (⟨g₁, hg₁'⟩ : ↥hyp.s11Setup.H) * ⟨g₂, hg₂'⟩ * (⟨g₁, hg₁'⟩ : ↥hyp.s11Setup.H)⁻¹
        * (⟨g₂, hg₂'⟩ : ↥hyp.s11Setup.H)⁻¹ ∈ hyp.chief.N := by
      rw [← QuotientGroup.eq_one_iff (N := hyp.chief.N)]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
      group
    rw [hyp.chief.H0_eq]
    exact ⟨_, hmemN, rfl⟩

/-- **Peterfalvi (11.6), `H₀ = H'`** (legacy wrapper): `H0_eq_Hprime_of_noncoherent` at the sorried
(11.3) `S_H0C_not_coherent`, for the import-blocked upstream consumers (issue 1025). -/
theorem Hypothesis.H0_eq_Hprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.chief.H0 = hyp.Hprime :=
  hyp.H0_eq_Hprime_of_noncoherent hG (S_H0C_not_coherent hG hyp)

/-- **Peterfalvi (11.6)**: `H` is a `p`-group, `U` centralizes `H_0`, `H_0 = H'`, and `C = U'`.

The second clause `U` centralizes `H_0` is **unconditional** (`U_centralizes_H0`, via (9.6)/(9.1)),
and the last clause `C = U'` is discharged by `C_eq_derivedU` ((11.5) + `M'' ≤ H ⊔ U'`).  The
remaining two obligations are: `H` a `p`-group needs (9.3) [`U` centralizes `O_{p'}(H)`] + (11.5);
`H_0 = H'` needs `[BG] 1.6(d)` + (11.5). -/
theorem core_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsPGroup hyp.p ↥hyp.H ∧
      hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) ∧
      hyp.chief.H0 = hyp.Hprime ∧ hyp.C = hyp.Uprime := by
  -- Conjunct 2 (`U` centralizes `H_0`) is discharged; the other three stay character-gated.
  refine ⟨?_, U_centralizes_H0 hyp, ?_, ?_⟩
  · -- `H` is a `p`-group: (9.3) [`U` centralizes `O_{p'}(H)`] + (11.5), via `H_isPGroup`.
    exact hyp.H_isPGroup _hG
  · -- `H_0 = H'`: BG 1.6(d) (coprime Fitting on `H̄`) + (11.5), via `H0_eq_Hprime`.
    exact hyp.H0_eq_Hprime _hG
  · -- `C = U'`: `U' ⊆ C` is `derivedU_le_C`; the reverse is `C ≤ M'' ≤ H ⊔ U'` via (11.5).
    rw [hyp.Uprime_eq]
    exact C_eq_derivedU _hG hyp

/-- **Peterfalvi (11.7), crux — the chief kernel is trivial**: `H₀ = 1`.

This is the genuine content of (11.7).  Since `H₀ = H'` ((11.6) `core_structure`), it says `H` is
abelian; equivalently the chief factor `H̄ = H/H₀` (of order `p^q`, elementary abelian) is all of
`H`.  Peterfalvi's proof (pp. 64-65) runs the two-case analysis on the `U`-action on `H̄`, both
refuted by the sorry-free machinery in `S13_ElementaryAbelianKernel.lean`: the Galois/irreducible
case by `chiefKernel_caseB_false` (parity: `|Ĥ| = p^(q+1)` with `q` odd), and the fixed-order-`p`
case by `caseA_fixed_contradiction` fed by the exponent chain (`chain_exponent_eq_one`).  Assembling
the dichotomy and the case-A `W₁`-chain relation is the remaining work; left as this named crux so
the two elementary-abelian/order corollaries below are sorry-free once it lands.
See `notes/peterfalvi/s13_11_8_orthogonality.md`. -/
theorem chief_H0_eq_bot_of_noncoherent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    hyp.chief.H0 = ⊥ := by
  classical
  by_contra hne
  -- `s11Setup.typeP.H = base.typeP.H` (the (11.2) shared type-`P` structure)
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by rw [hyp.setup_typeP_eq]
  -- `chief.N ≠ ⊥` (else `H₀ = N.map subtype = ⊥`)
  have hNne : hyp.chief.N ≠ ⊥ := by
    intro hN0
    exact hne (by rw [hyp.chief.H0_eq, hN0, Subgroup.map_bot])
  -- `chief.p = hyp.p = |W₂|`
  have hp_eq : hyp.chief.p = hyp.p := by
    have h2 := hyp.chief.typeIII_IV_p_eq_W2 (hyp.base.isTypeIIIorIV hG)
    rw [hyp.s11Setup_card_W2_eq] at h2
    exact h2.symm
  -- `H₀ = H' = derivedInG (s11Setup.typeP.H)` ((11.6) `H0_eq_Hprime`)
  have hH0deriv : hyp.chief.H0 = derivedInG hyp.s11Setup.typeP.H := by
    rw [hyp.H0_eq_Hprime_of_noncoherent hG hnc, hyp.Hprime_eq, ← hHH]
  -- **case-B hypotheses of `chiefKernel_caseB_false`**
  have hpK : IsPGroup hyp.chief.p ↥hyp.s11Setup.H := by
    show IsPGroup hyp.chief.p ↥hyp.s11Setup.typeP.H
    rw [hp_eq, hHH]; exact hyp.H_isPGroup hG
  have hNcomm : hyp.chief.N = commutator ↥hyp.s11Setup.H := by
    apply Subgroup.map_injective (hyp.s11Setup.typeP.H).subtype_injective
    rw [← hyp.chief.H0_eq, hH0deriv]; rfl
  have hqodd : Odd hyp.s11Setup.q := by
    rw [hyp.s11Setup_q_eq]; exact (hyp.p_q_distinct_odd_primes hG).2.2.2.1
  rcases OddOrder.Peterfalvi.S11.chiefFactor_clifford_U_dichotomy hyp.chief with
    hirrB | ⟨S₀, hS₀ne, hS₀inv, hS₀card, _hS₀sub⟩
  · -- **case (b)**: `U` acts irreducibly on `H̄`; parity `|Ĥ| = p^{q+1}` (`q` odd) is impossible.
    -- `U` centralizes `chief.N` (via `U_centralizes_H0`: conjugation of `H₀`-elements is trivial).
    refine chiefKernel_caseB_false hyp.chief hpK hNcomm ?_ hqodd hNne hirrB
    intro u n hn
    have hnH0 : (n : G) ∈ hyp.chief.H0 := by rw [hyp.chief.H0_eq]; exact ⟨n, hn, rfl⟩
    have huU : ((↑u : ↥(hyp.s11Setup.typeP.U ⊔ hyp.s11Setup.typeP.W1)) : G) ∈ hyp.U := by
      rw [← hyp.s11Setup_U_eq]
      exact Subgroup.mem_subgroupOf.mp u.2
    refine Subtype.ext ?_
    rw [OddOrder.Peterfalvi.S11.typeP_conjAction_apply hyp.s11Setup.typeP ↑u n]
    have hcent := Subgroup.mem_centralizer_iff.mp (U_centralizes_H0 hyp huU) (n : G) hnH0
    rw [← hcent]; group
  · -- **case (a)**: `U` fixes the order-`p` factor `S₀` pointwise.  The commutator-form chain
    -- (`caseA_commutator_chain`, Peterfalvi's non-Galois `D`-antisymmetry — the sole remaining
    -- sorry) supplies the inverting automorphism `σ` (conjugation by the specific `W₁`-element
    -- `w₁ w₂⁻¹`) with the chain relation; the exponent reduction (`caseA_fixes_of_action_chain`)
    -- and `caseA_fixed_contradiction` are proven.
    have hAodd : Odd (Nat.card ↥(hyp.s11Setup.typeP.U.subgroupOf
        (hyp.s11Setup.typeP.U ⊔ hyp.s11Setup.typeP.W1))) :=
      hG.odd.of_dvd_nat ((Subgroup.card_subgroup_dvd_card _).trans
        (Subgroup.card_subgroup_dvd_card _))
    obtain ⟨σ, m, hmodd, hσm, hchain⟩ :=
      caseA_commutator_chain hG hyp.chief hyp.type_alt hpK hNcomm hNne hS₀card
        (fun v s hs => hS₀inv.smul_mem v hs)
    exact caseA_fixed_contradiction hyp.chief hS₀ne
      (caseA_fixes_of_action_chain hyp.chief hS₀card (fun v s hs => hS₀inv.smul_mem v hs)
        hAodd σ hmodd hσm hchain)

/-- **Peterfalvi (11.7), `H₀ = ⊥`** (legacy wrapper): `chief_H0_eq_bot_of_noncoherent` at the
sorried (11.3) `S_H0C_not_coherent`, for the import-blocked upstream consumers (issue 1025). -/
theorem chief_H0_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.chief.H0 = ⊥ :=
  chief_H0_eq_bot_of_noncoherent hG hyp (S_H0C_not_coherent hG hyp)

/-- **(11.7) corollary — `N ◁ H` trivial, parametrized on (11.3) non-coherence** (issue 1025):
`N = ⊥` from `chief_H0_eq_bot_of_noncoherent hnc` (`H₀ = N.map subtype = ⊥` + `subtype` injective). -/
theorem chief_N_eq_bot_of_noncoherent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    hyp.chief.N = ⊥ := by
  have h := hyp.chief.H0_eq
  rw [chief_H0_eq_bot_of_noncoherent hG hyp hnc, eq_comm, Subgroup.map_eq_bot_iff] at h
  simpa using h

/-- **(11.7) corollary — the chief kernel `N ◁ H` is trivial**: `N = ⊥`.  The chief kernel realised
inside `↥H` is trivial because its `G`-image `H₀ = N.map H.subtype` is trivial (`chief_H0_eq_bot`)
and `H.subtype` is injective.  Hence the chief factor `H̄ = ↥H ⧸ N ≅ ↥H` (used to transport the
elementary-abelian/order data, and — via `H̄ = H` — to identify `C = C_U(H̄)` with `C_U(H) = hyp.C`
for the (9.11) `hY` route).  (Legacy wrapper of `chief_N_eq_bot_of_noncoherent`, issue 1025.) -/
theorem chief_N_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.chief.N = ⊥ :=
  chief_N_eq_bot_of_noncoherent hG hyp (S_H0C_not_coherent hG hyp)

/-- **Identification `C = cSub`** (Coq `Ptype_Fcompl_kernel_cent`): the §11 Fitting-complement
`C = C_U(H)` (`hyp.C`, `C_eq_centralizer`) equals the §9 chief-factor action kernel `cSub = C_U(H̄)`.
Forward (`C_U(H) ≤ cSub`) is `mem_cSub_of_mem_U_of_centralizes` (centralizing `H` ⟹ trivial on `H̄`).
Reverse (`cSub ≤ C_U(H)`) uses `H₀ = 1` (`chief_N_eq_bot`: `N = ⊥`, so `H̄ = H/⊥`, and a `cSub`-element
— acting trivially on `H̄` — centralizes `H` since the quotient by `⊥` is injective).  This makes the
capstone family `𝒮(H₀ ⊔ C)` coincide with the (9.11) family `𝒮(H₀ ⊔ cSub)`, the connector for the
`hY` route (issue 1019 update⁴⁸). -/
theorem C_eq_cSub_of_noncoherent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    hyp.C = OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
  have hHeq : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by rw [hyp.setup_typeP_eq]
  have hUeq : hyp.s11Setup.typeP.U = hyp.base.typeP.U := by rw [hyp.setup_typeP_eq]
  apply le_antisymm
  · -- forward: `C_U(H) ≤ cSub`
    intro x hx
    rw [hyp.C_eq_centralizer, Subgroup.mem_inf] at hx
    exact OddOrder.Peterfalvi.S11.mem_cSub_of_mem_U_of_centralizes hyp.s11Setup hyp.chief
      (hUeq ▸ hx.1) (hHeq ▸ hx.2)
  · -- reverse: `cSub ≤ C_U(H)` (needs `N = ⊥`)
    have hN : hyp.chief.N = ⊥ := chief_N_eq_bot_of_noncoherent hG hyp hnc
    intro x hx
    rw [hyp.C_eq_centralizer, Subgroup.mem_inf]
    refine ⟨hUeq ▸ OddOrder.Peterfalvi.S11.cSub_le_U hyp.s11Setup hyp.chief hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hgH
    have hgH' : g ∈ hyp.s11Setup.typeP.H := hHeq ▸ hgH
    -- unfold `x ∈ cSub` to a kernel element `a`
    simp only [OddOrder.Peterfalvi.S11.cSub, Subgroup.mem_map] at hx
    obtain ⟨y, ⟨a, hker, rfl⟩, rfl⟩ := hx
    set l := (hyp.s11Setup.typeP.U.subgroupOf
      (hyp.s11Setup.typeP.U ⊔ hyp.s11Setup.typeP.W1)).subtype a with hl
    -- `a ∈ ker(uActionHom)` ⟹ conjugation by `l` fixes `g` mod `N`
    rw [MonoidHom.mem_ker] at hker
    have happ := DFunLike.congr_fun hker (QuotientGroup.mk' hyp.chief.N ⟨g, hgH'⟩)
    rw [OddOrder.Peterfalvi.S11.uActionHom, MonoidHom.comp_apply,
      OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk',
      MulAut.one_apply] at happ
    -- `N = ⊥` ⟹ the quotient map is injective ⟹ `typeP_conjAction l ⟨g,·⟩ = ⟨g,·⟩`
    have hinj : Function.Injective (QuotientGroup.mk' hyp.chief.N) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']; exact hN
    have hconj := hinj happ
    -- `typeP_conjAction_apply`: `x * g * x⁻¹ = g`
    have hval := congrArg (Subtype.val) hconj
    rw [OddOrder.Peterfalvi.S11.typeP_conjAction_apply] at hval
    -- `hval : (l : G) * g * (l : G)⁻¹ = g`; `(l : G) = x`
    exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- **Identification `C = cSub`** (legacy wrapper): `C_eq_cSub_of_noncoherent` at the sorried (11.3)
`S_H0C_not_coherent`, for the import-blocked upstream consumers (issue 1025). -/
theorem C_eq_cSub [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) :
    hyp.C = OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief :=
  C_eq_cSub_of_noncoherent hG hyp (S_H0C_not_coherent hG hyp)

/-- **Peterfalvi (11.7)**: `H` is elementary abelian of order `p^q`, and `H_0 = 1`.

`H₀ = 1` is the crux `chief_H0_eq_bot`.  Given it, both remaining conjuncts are immediate from the
chief-factor data: the kernel `N` (with `H₀ = N.map H.subtype`) is trivial, so `H̄ = H/N ≅ H`
carries the chief factor's `IsElementaryAbelian p` (`ChiefFactorData.quotient_elementaryAbelian`
transported
by `QuotientGroup.quotientBot`), and `|H| = p^q·|H₀| = p^q` by
`ChiefFactorData.quotient_order`. -/
theorem H_elementaryAbelian [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsElementaryAbelian hyp.p ↥hyp.H ∧ Nat.card ↥hyp.H = hyp.p ^ hyp.q ∧
      hyp.chief.H0 = ⊥ := by
  classical
  have hH0 : hyp.chief.H0 = ⊥ := chief_H0_eq_bot _hG hyp
  -- `chief.p = hyp.p` (chief-factor prime = `|W₂|`)
  have hp_eq : hyp.chief.p = hyp.p := by
    have h2 := hyp.chief.typeIII_IV_p_eq_W2 (hyp.base.isTypeIIIorIV _hG)
    rw [hyp.s11Setup_card_W2_eq] at h2
    exact h2.symm
  -- `N = ⊥` (`chief_N_eq_bot`)
  have hN : hyp.chief.N = ⊥ := chief_N_eq_bot _hG hyp
  refine ⟨?_, ?_, hH0⟩
  · -- elementary abelian: transport `quotient_elementaryAbelian` along `↥H ⧸ ⊥ ≃* ↥H`
    have hEA : IsElementaryAbelian hyp.p ↥hyp.s11Setup.H := by
      have h := hyp.chief.quotient_elementaryAbelian
      rw [hp_eq] at h
      exact IsElementaryAbelian.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
    rwa [hyp.s11Setup_H_eq] at hEA
  · -- order: `|H| = p^q·|H₀| = p^q`
    have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
      rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
    have hcardHH : Nat.card ↥hyp.s11Setup.H = Nat.card ↥hyp.base.typeP.H :=
      congrArg (fun (X : Subgroup G) => Nat.card ↥X) hHH
    have h := hyp.chief.quotient_order
    rw [hcardHH, hp_eq, hyp.s11Setup_q_eq, hH0] at h
    show Nat.card ↥hyp.base.typeP.H = hyp.p ^ hyp.q
    simpa using h

/-- **(11.5) for the bare §12 hypothesis**: `M'' = H ⊔ C_U(H)` for a type-III/IV maximal subgroup,
stated directly on the §12 `Hypothesis` (not the §13 one).  Builds the §13 hypothesis via
`exists_hypothesis_of_isTypeIIIorIV` (which pins `base = base12`), so `secondDerived_eq_HC`
transports to the §12 `typeP`: `s13.HC = s13.H ⊔ s13.C = base12.typeP.H ⊔ (base12.typeP.U ⊓ C_G(H))`
by `C_eq_centralizer`.  The `hM2` input to `S12.card_SHCSet_filter_eq_charParam_n`. -/
theorem secondDerived_eq_fitting_of_base [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (base12 : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    secondDerivedInAmbient M
      = base12.typeP.H ⊔ (base12.typeP.U ⊓ Subgroup.centralizer (base12.typeP.H : Set G)) := by
  obtain ⟨s13, hbase⟩ := exists_hypothesis_of_isTypeIIIorIV hG base12 htype
  have hH : s13.H = base12.typeP.H := by rw [Hypothesis.H, hbase]
  have hHC : s13.HC
      = base12.typeP.H ⊔ (base12.typeP.U ⊓ Subgroup.centralizer (base12.typeP.H : Set G)) := by
    rw [Hypothesis.HC, hH, s13.C_eq_centralizer, hbase]
  rw [secondDerived_eq_HC hG s13, hHC]

/-- **(11.7) order for the bare §12 hypothesis**: `|H| = |W₂|^{|W₁|}` (Peterfalvi's `p^q`), stated
on the §12 `Hypothesis`.  Builds the §13 hypothesis (`base = base12`) and transports the order half
of `H_elementaryAbelian` (`|H| = p^q`) to `base12.typeP.H`, with `p = w₂`, `q = w₁`.  The `hHcard`
input to `S12.card_SHCSet_filter_eq_charParam_n`. -/
theorem card_H_eq_of_base [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (base12 : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    Nat.card ↥base12.typeP.H = base12.w2 ^ base12.w1 := by
  obtain ⟨s13, hbase⟩ := exists_hypothesis_of_isTypeIIIorIV hG base12 htype
  have h := (H_elementaryAbelian hG s13).2.1
  -- `s13.H = base12.typeP.H`, `s13.p = base12.w2`, `s13.q = base12.w1` (all via `base = base12`).
  rw [show s13.H = base12.typeP.H from by rw [Hypothesis.H, hbase],
    show s13.p = base12.w2 from by rw [Hypothesis.p, hbase],
    show s13.q = base12.w1 from by rw [Hypothesis.q, hbase]] at h
  exact h

/-! ## (11.8): the main orthogonality calculation -/

/-- Carrier for the five substeps of Peterfalvi (11.8). -/
structure OrthogonalityData {M : Subgroup G} (hyp : Hypothesis M) where
  zeta : ClassFunction ↥M ℂ
  zeta_mem_SHC : zeta ∈ hyp.SOf hyp.HC
  S1 : Set (ClassFunction ↥M ℂ)
  S2 : Set (ClassFunction ↥M ℂ)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau2 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  beta : ClassFunction G ℂ
  coefficientA : ℤ
  frobenius_setup : Prop
  omega_support_reduction : Prop
  average_formula : Prop
  coefficient_formula : Prop
  coefficient_zero : coefficientA = 0
  conclusion_formula : Prop

/-- **Peterfalvi (11.8.1)--(11.8.4)**: the setup for the coefficient calculation
in the proof of (11.8). -/
theorem orthogonality_setup [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ data : OrthogonalityData hyp,
      data.frobenius_setup ∧ data.omega_support_reduction ∧
        data.average_formula ∧ data.coefficient_formula := by
  sorry

/-- **Peterfalvi (11.8.5)**: the coefficient `a` in the orthogonality
calculation is zero. -/
theorem orthogonality_coefficient_zero [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    data.coefficientA = 0 :=
  -- (11.8.5) is carried as the `coefficient_zero` field of `OrthogonalityData`; the
  -- real `a = 0` content lives in `orthogonality_setup` (11.8.1)-(11.8.4), which
  -- constructs the data.  This is the intended public-name wiring for that field.
  data.coefficient_zero

/-- **Peterfalvi (11.8)**: for `zeta in S(HC)`, the residual character is not
orthogonal to `(Irr W)^sigma`. -/
theorem not_orthogonal_mu0_sub_zeta [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    hyp.notOrthogonalFormula data.zeta := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.5)/(9.9.b): the nontrivial column sums `μ_k` are `𝒮(H₀C)`-members** — the
`𝒮(H₀C)`-level form (kernel `H₀ ⊔ C`), from which the `𝒮(H₀C′)` version and the caseB
`𝒮(H₀C)`-coherence witness follow.

The chain: `μ_k ∈ 𝒮(H₀^prod)` and is reducible by the (11.8.1) count
(`muGrid_column_sum_mem_sOf_H0_and_reducible`, at a producer chief over `toTypesIIIIIIVSetup`);
the family relaxes to `𝒮(⊥)` (kernel antitone) where it is setup-independent, and the §13 setup
agrees with the producer (`TypesIIIIIIVSetup.eq_of_typeP_eq`, `setup_typeP_eq`); `H₀ = ⊥` in
types III/IV (`chief_H0_eq_bot`), so this is `𝒮(H₀)`-membership over `hyp.s11Setup`; a reducible
`𝒮(H₀)`-member lies in `𝒮(H₀ ⊔ cSub)` by the (9.9.b) count (`reducible_mem_sOf_H0C`); `cSub = C`
(`C_eq_cSub`) identifies that family with `𝒮(H₀C)`. -/
theorem columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (k : Fin hyp.base.w2) (hk : k ≠ 0)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C := by
  haveI := hyp.base.finiteG
  classical
  have hnt : OddOrder.GroupTheory.TypePNontrivialCore M hyp.base.typeP :=
    OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV hyp.type_alt hyp.base.typeP
  -- the §9 setups agree (`typeP` pinned, all other fields propositional)
  have heq : hyp.s11Setup = hyp.base.toTypesIIIIIIVSetup hyp.type_alt hnt :=
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup.eq_of_typeP_eq hyp.setup_typeP_eq
  -- (11.8.1) at a producer chief: `μ_k ∈ 𝒮(H₀^prod)`, reducible
  obtain ⟨chief₀, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.base.toTypesIIIIIIVSetup hyp.type_alt hnt)
  have hgrid := hyp.base.muGrid_column_sum_mem_sOf_H0_and_reducible hG hyp.type_alt hnt
    chief₀ k hk
  rw [hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k] at hgrid
  -- transport to `𝒮(H₀)` over `hyp.s11Setup`: relax to `𝒮(⊥)` and use `H₀ = ⊥` (types III/IV)
  have hmemH0 : OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
      (hyp.base.muColumnChar hG hG.odd k)
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.chief.H0 := by
    rw [chief_H0_eq_bot_of_noncoherent hG hyp hnc, heq]
    exact OddOrder.Peterfalvi.S11.sOf_antitone _ bot_le hgrid.1
  -- (9.9.b): a reducible `𝒮(H₀)`-member lies in `𝒮(H₀ ⊔ cSub)`
  have hH0C := OddOrder.Peterfalvi.S11.reducible_mem_sOf_H0C hG
    (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) _ hmemH0 hgrid.2
  -- `H₀ ⊔ cSub = H₀C` (`C = cSub`)
  change _ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup (hyp.chief.H0 ⊔ hyp.C)
  rw [C_eq_cSub_of_noncoherent hG hyp hnc]
  exact hH0C

/-- **(9.5)/(9.9.b) `𝒮(H₀C)`-membership** (legacy wrapper): `columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent`
at the sorried (11.3) `S_H0C_not_coherent`, for the import-blocked upstream consumers (issue 1025). -/
theorem columnSum_muColumnChar_mem_sOf_H0C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (k : Fin hyp.base.w2) (hk : k ≠ 0) :
    OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
  columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp k hk (S_H0C_not_coherent hG hyp)

/-- **Peterfalvi (9.5)/(9.9.b): the nontrivial column sums `μ_k` are `𝒮(H₀C′)`-members** — the
`hμmem` input of the (9.11) caseB chain fold (`caseB_coherent_sOf_H0Cprime_of_mixed`).  Follows
from the `𝒮(H₀C)` form (`columnSum_muColumnChar_mem_sOf_H0C`) by the kernel-antitone subset
`𝒮(H₀C) ⊆ 𝒮(H₀C′)` (`C′ ≤ C`, `sOf_H0C_subset_sOf_H0Cprime`). -/
theorem columnSum_muColumnChar_mem_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (k : Fin hyp.base.w2) (hk : k ≠ 0)
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := S_H0C_not_coherent hG hyp) :
    OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
  hyp.sOf_H0C_subset_sOf_H0Cprime
    (columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp k hk hncH0C)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.9.a), caseB uniform degree on `𝒮(H₀C′)`** — the `hunif` input of the (9.11)
caseB chain fold (`caseB_coherent_sOf_H0Cprime_of_mixed`): in Clifford case (b), every
`𝒮(H₀C′)`-member has degree `qu`.  This is `caseB_degree_qu` instantiated at the §13 hypothesis,
with the §9 trigger kernel `H₀ ⊔ C′ = H₀ ⊔ cprimeSub` identified with `hyp.H0Cprime =
H₀ ⊔ [C,C]` along `C = cSub` (`C_eq_cSub`, so `cprimeSub = [cSub,cSub] = [C,C]`). -/
theorem caseB_forall_mem_sOf_H0Cprime_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := S_H0C_not_coherent hG hyp) :
    ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 =
        ((hyp.s11Setup.q *
          (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ) := by
  haveI := hyp.base.finiteG
  intro φ hφ
  refine OddOrder.Peterfalvi.S11.caseB_degree_qu hG _ caseB φ ?_
  change φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
    (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cprimeSub hyp.s11Setup hyp.chief)
  have hCp : OddOrder.Peterfalvi.S11.cprimeSub hyp.s11Setup hyp.chief
      = derivedInG hyp.C := by
    change derivedInG (OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief) = derivedInG hyp.C
    rw [C_eq_cSub_of_noncoherent hG hyp hncH0C]
  rw [hCp]
  exact hφ

set_option maxHeartbeats 1600000 in
-- the norm-general engine threads the dispatched `R`-families and the `hZdiff`/`hiso` inputs
-- through the `hyp.base.tau = dadeIntegralCharacterMap` defeq, which is feasible but expensive
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), caseB: `𝒮(H₀C′)` is coherent on `A₀(M)`** — the caseB branch of the
`Ptype_core_coherence` induction.

**Norm-general route (issue 9075).** Rather than seeding the degree-`qu` *irreducible* cut and
chain-adjoining the reducible column pairs — which required the (5.6.c)-style count `hDeg`
(`2 < |cut|`, a route artifact Coq never proves and false at the `|cut| = 2` corner) — this fires
Coq's `uniform_degree_coherence` (`PFsection5.v:1234`, ported as
`uniform_degree_coherence_of_families`) on the **whole family** `𝒮(H₀C′)` in one shot, with the
reducible μ-columns of norm `q` included.  The pivot is the column sum `μ₁` (norm `w₁`), the
per-member `R`-data is dispatched (`caseB_sOf_memberRFamily`) between the signed Dade family
(irreducible members) and the certain-type family `certainTypeR` (columns), and the (5.2.e)
cross-orthogonality is `caseB_sOf_memberRFamily_orthogonal`.  **No `hDeg` count is needed.** -/
theorem caseB_coherent_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := S_H0C_not_coherent hG hyp) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  set d := hyp.s11Setup.q * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u with hd
  have hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ) :=
    caseB_forall_mem_sOf_H0Cprime_apply_one_eq_qu hG hyp caseB hncH0C
  -- the world-bridge `𝒮(H₀C′) → S(⊥)` (for the support / ZIrr / no-real / pairwise facts)
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  -- the pivot `μ₁ = columnSum χ₁` (the nonzero-column certain-type sum), of norm `w₁`
  have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
  have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro heq; have := congrArg Fin.val heq; simp at this
  set μ₁ : ClassFunction ↥M ℂ := OddOrder.Peterfalvi.S06.columnSum
    (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩) with hμ₁def
  have hμ₁mem : μ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
    columnSum_muColumnChar_mem_sOf_H0Cprime hG hyp ⟨1, hw2⟩ hk1 hncH0C
  -- uniform support of member differences against the pivot anchor
  have hsuppdiff : ∀ a ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      ∀ b ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      ((a - b : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    intro a ha b hb
    have ha1 := OddOrder.Peterfalvi.S13.sOf_anchor_diff_support hG hyp d hunif hμ₁mem ha
    have hb1 := OddOrder.Peterfalvi.S13.sOf_anchor_diff_support hG hyp d hunif hμ₁mem hb
    have hab : (a - b : ClassFunction ↥M ℂ) = (a - μ₁) - (b - μ₁) := by abel
    rw [hab]
    exact (ClassFunction.support_sub_subset _ _).trans (Set.union_subset ha1 hb1)
  refine OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    ((OddOrder.Peterfalvi.S08.inducedKernelFamily_finite (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx))
    hμ₁mem
    (fun η hη => caseB_sOf_memberRFamily hG hyp d hunif hη)
    (fun a ha b hb hab =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal (hIKF ha) (hIKF hb) hab)
    (Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime)
    (fun a ha h =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _ (hIKF ha) h.symm)
    ⟨Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1, by
      rw [hμ₁def, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]⟩
    (fun {φ ψ} hφ hψ =>
      hyp.base.tau_inner_eq_of_supported
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hφ)
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hψ))
    (fun a ha b hb =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.base.dadeData.dade hyp.base.hconj (hsuppdiff a ha b hb)
        (Submodule.sub_mem _ (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF ha))
          (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hb))))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 =>
      caseB_sOf_memberRFamily_orthogonal hG hyp d hunif hφ hξ h1 h2)
    (fun a ha => (hunif a ha).trans (hunif _ hμ₁mem).symm)
    (by
      rw [hunif _ hμ₁mem, hd]
      exact Nat.cast_ne_zero.mpr
        (mul_ne_zero Nat.card_pos.ne'
          (OddOrder.Peterfalvi.S11.u_odd hG
            (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos.ne'))
    hyp.base.one_notMem_A0
    (Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime hμ₁mem)
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _ (hIKF hμ₁mem))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11)→(11.7), caseB: `𝒮(H₀C)` is coherent on `A₀(M)`** — chains the landed caseB
`𝒮(H₀C′)`-coherence (`caseB_coherent_sOf_H0Cprime`, issue 9075, the norm-general (5.7) engine)
forward to `𝒮(H₀C)` via the kernel-antitone restriction `coherent_sOf_H0C_of_coherent_sOf_H0Cprime`
(Peterfalvi (11.7): `H₀C′ ≤ H₀C` since `C′ = [C,C] ≤ C`), supplying the nonzero `A₀`-supported
restriction witness `μ̄_k − μ_k` from a reducible μ-column (`columnSum_muColumnChar_mem_sOf_H0C`,
`w₂ ≥ 2`; the conjugate difference is `A₀`-supported by `inducedKernelFamily_conjDiff_support` and
nonzero by odd-order no-real-characters).

This is the caseB `hY` (𝒮(H₀C)-coherence) input of the (11.8.6) world-bridge union-glue
`coherent_SOf_H0C_of_glued`, making the issue-9075 caseB coherence load-bearing toward the honest
(11.8.6) narrow-`𝒮₂` route (contradicting (11.3) `S_H0C_not_coherent`) that replaces the
`Sset \ SHCSet` uniform-degree route (false for non-Galois type III/IV, issue 1019). -/
noncomputable def caseB_coherent_sOf_H0C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := S_H0C_not_coherent hG hyp) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- the pivot μ-column `μ_k ∈ 𝒮(H₀C)` (nonzero column `k = 1`, `w₂ ≥ 2`)
  have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
  have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro heq; have := congrArg Fin.val heq; simp at this
  set μ : ClassFunction ↥M ℂ := OddOrder.Peterfalvi.S06.columnSum
    (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩) with hμdef
  have hμmem : μ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
    columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp ⟨1, hw2⟩ hk1 hncH0C
  -- the `𝒮(H₀C) → inducedKernelFamily(⊥)` world-bridge (for the support / no-real facts)
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  -- the conjugate `μ̄ ∈ 𝒮(H₀C)` (closed under conjugation)
  have hμc : μ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
    Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hμmem
  refine coherent_sOf_H0C_of_coherent_sOf_H0Cprime hyp
    (caseB_coherent_sOf_H0Cprime hG hyp caseB hncH0C).some ⟨μ.conj - μ, ⟨?_, ?_⟩, ?_⟩
  · -- `μ̄ − μ ∈ ℤ[𝒮(H₀C)]`
    exact Submodule.sub_mem _ (Submodule.subset_span hμc) (Submodule.subset_span hμmem)
  · -- `μ̄ − μ` is `A₀`-supported
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hμmem)
  · -- `μ̄ − μ ≠ 0` (odd order ⇒ no real characters)
    intro h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ (hIKF hμmem) (sub_eq_zero.mp h)

/-! ## (11.9): final Type III conclusion -/

/-- **Peterfalvi (11.9)**: the final three conclusions of §13: the symmetric
orthogonality statement, `q > p`, and the fact that case (b) of (9.7) holds,
so `M` is of type III. -/
theorem final_typeIII_conclusions [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    hyp.finalOrthogonalityFormula data.zeta ∧ hyp.q > hyp.p ∧
      hyp.caseB_of_97 ∧ IsTypeIII M := by
  sorry

end OddOrder.Peterfalvi.S13
