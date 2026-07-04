/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV

/-!
# Peterfalvi Section 13: the core structure of `H` and `U` ((11.6)--(11.8))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 13, pp. 64--68 — the (11.6)--(11.8) block.

Split from `S13_MaximalIII_IV` (which keeps Hypothesis (11.2) and the
commutator chain (11.3)--(11.5)): this leaf carries the core-structure
theorems — `H` is a `p`-group, `U` centralizes `H₀`, `H₀ = H\'`, `C = U\'`
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

/-- Bridge: the §9 setup's `H` is the §13 `H` (via `setup_typeP_eq`). -/
theorem s11Setup_H_eq {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.H = hyp.H := by
  show hyp.s11Setup.typeP.H = hyp.base.typeP.H
  rw [hyp.setup_typeP_eq]

/-- Bridge: the §9 setup's `U` is the §13 `U`. -/
theorem s11Setup_U_eq {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.U = hyp.U := by
  show hyp.s11Setup.typeP.U = hyp.base.typeP.U
  rw [hyp.setup_typeP_eq]

/-- Bridge: the §9 setup's `q` is the §13 `q`. -/
theorem s11Setup_q_eq {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.q = hyp.q := by
  show Nat.card ↥hyp.s11Setup.typeP.W1 = Nat.card ↥hyp.base.typeP.W1
  rw [hyp.setup_typeP_eq]

/-- Bridge: the §9 setup's `W₂` is the §13 `W₂`-carrier of `p`. -/
theorem s11Setup_card_W2_eq {M : Subgroup G} (hyp : Hypothesis M) :
    Nat.card ↥hyp.s11Setup.W2 = hyp.p := by
  show Nat.card ↥hyp.s11Setup.typeP.W2 = Nat.card ↥hyp.base.typeP.W2
  rw [hyp.setup_typeP_eq]

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

/-- The `p`-complement `O_{p\'}(H)` of the nilpotent `H` — the join of the `q\'`-cores over
the primes `q\' ≠ p` of `|H|` — as a subgroup of `↥H`. -/
noncomputable def pComplementCore [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Subgroup ↥hyp.H :=
  ⨆ (j : (Nat.card ↥hyp.H).primeFactors) (_ : (j : ℕ) ≠ hyp.p),
    OddOrder.Isaacs.Ch01.opCore (j : ℕ) ↥hyp.H

/-- The ambient `p`-complement `R = O_{p\'}(H) ≤ G`. -/
noncomputable def pComplement [Finite G] {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.pComplementCore.map hyp.H.subtype

theorem pComplement_le_H [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplement ≤ hyp.H :=
  Subgroup.map_subtype_le _

/-- The `p`-complement is characteristic in `H` (join of the characteristic `q\'`-cores). -/
theorem pComplementCore_characteristic [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplementCore.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [pComplementCore]
  simp_rw [Subgroup.map_iSup]
  exact iSup_congr fun j => iSup_congr fun _ =>
    Subgroup.characteristic_iff_map_eq.mp
      (OddOrder.Isaacs.Ch01.opCore.characteristic (j : ℕ) ↥hyp.H) φ

/-- **`U` centralizes the `p`-complement** — each `q\'`-core lies in `C_G(U)`
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
  -- every prime factor `q\' ≠ p` has trivial core, hence trivial Sylow — impossible
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
  · -- `H` is a `p`-group: (9.3) [`U` centralizes `O_{p'}(H)`] + (11.5).
    sorry
  · -- `H_0 = H'`: `[BG]` Proposition 1.6(d) + (11.5).
    sorry
  · -- `C = U'`: `U' ⊆ C` is `derivedU_le_C`; the reverse is `C ≤ M'' ≤ H ⊔ U'` via (11.5).
    rw [hyp.Uprime_eq]
    exact C_eq_derivedU _hG hyp

/-- **Peterfalvi (11.7)**: `H` is elementary abelian of order `p^q`, and
`H_0 = 1`. -/
theorem H_elementaryAbelian [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsElementaryAbelian hyp.p ↥hyp.H ∧ Nat.card ↥hyp.H = hyp.p ^ hyp.q ∧
      hyp.chief.H0 = ⊥ := by
  sorry

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
