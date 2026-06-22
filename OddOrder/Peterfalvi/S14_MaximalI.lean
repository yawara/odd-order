/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV
import OddOrder.Peterfalvi.S10_CoherenceWiring
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import Mathlib.RepresentationTheory.Irreducible

/-!
# Peterfalvi Section 14: Maximal Subgroups of Type I

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 14, pp. 69--74.

This section proves that every maximal subgroup of type I is a Frobenius group
with kernel `M_F`.  The proof first sets up the Dade isometry attached to a
type-I maximal subgroup, proves orthogonality and constancy properties for the
families `R(chi)`, and then excludes a minimal counterexample with a non-cyclic
Sylow subgroup in `M / M_F`.

The scaffold records the named endpoints (12.1)--(12.17).  The detailed
character decompositions, rho maps, and integer congruence calculations are kept
as proposition fields until the lower-level Dade/rho API is ready for this
maximal-subgroup layer.
-/

namespace OddOrder.Peterfalvi.S14
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (12.1): the type-I hypothesis -/

/-- **Peterfalvi (12.1)**: setup for a maximal subgroup `L` of type I.

`Sset` is the family `{Ind_H^L theta | theta in Irr H, theta != 1_H}`.
`R chi` is the union of the two-element image blocks `R_1(phi)` appearing in
(12.2).  The fields whose names end in `Formula` name the character calculations
proved across (12.2)--(12.5). -/
structure Hypothesis (L : Subgroup G) where
  maximal : L ∈ maximalSubgroups G
  typeI : TypeIData L
  Sset : Set (ClassFunction ↥L ℂ)
  A : Set ↥L
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  R : ClassFunction ↥L ℂ → Set (ClassFunction G ℂ)
  decompositionFormula : ClassFunction ↥L ℂ → Prop
  dadeDomainFormula : ClassFunction ↥L ℂ → Prop
  characterOrthogonalToR : ClassFunction G ℂ → Prop
  rhoConstantFormula : ClassFunction G ℂ → Prop
  integerValueFormula : ClassFunction G ℂ → Prop

namespace Hypothesis

/-- Peterfalvi's `H = L_F`. -/
def H {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  hyp.typeI.typeF.H

/-- Peterfalvi's `H'`, represented as an ambient subgroup. -/
def Hprime {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  derivedInG hyp.H

/-- Peterfalvi's ambient `A(L)` set from Definition (8.3). -/
def ambientA {L : Subgroup G} (hyp : Hypothesis L) : Set G :=
  typeIA L hyp.typeI

end Hypothesis

/-! ## (12.2): character decomposition and Dade domain -/

/-- Carrier for the decomposition of `chi in S` used in Peterfalvi (12.2). -/
structure CharacterDecompositionData {L : Subgroup G} (hyp : Hypothesis L)
    (chi : ClassFunction ↥L ℂ) where
  chi_mem : chi ∈ hyp.Sset
  components : Set (ClassFunction ↥L ℂ)
  components_nonempty : components.Nonempty
  R1 : ClassFunction ↥L ℂ → Set (ClassFunction G ℂ)
  equal_degree : Prop
  equal_degree_holds : equal_degree
  tau_restriction_domain : Prop
  tau_restriction_domain_holds : tau_restriction_domain
  difference_image_formula : Prop
  difference_image_formula_holds : difference_image_formula
  R_eq_union : Prop
  R_eq_union_holds : R_eq_union

/-- **Peterfalvi (12.2)**: each `chi in S` decomposes into irreducible components
of equal degree, and the restricted Dade map has the stated two-element image
blocks. -/
theorem character_decomposition_and_dade_domain [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ data : CharacterDecompositionData hyp chi,
      data.chi_mem = hchi ∧ data.tau_restriction_domain ∧
        data.difference_image_formula ∧ data.R_eq_union := by
  sorry

/-! ## (12.3)--(12.5): orthogonality and rho-constancy -/

/-- Carrier for Peterfalvi (12.3), comparing two non-conjugate type-I maximal
subgroups. -/
structure CrossOrthogonalityData {L1 L2 : Subgroup G}
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2) where
  chi1 : ClassFunction ↥L1 ℂ
  chi1_mem : chi1 ∈ hyp1.Sset
  chi2 : ClassFunction ↥L2 ℂ
  chi2_mem : chi2 ∈ hyp2.Sset
  R1 : Set (ClassFunction G ℂ)
  R1_eq : R1 = hyp1.R chi1
  R2 : Set (ClassFunction G ℂ)
  R2_eq : R2 = hyp2.R chi2
  orthogonal : Prop
  orthogonal_holds : orthogonal

/-- **Peterfalvi (12.3)**: for non-conjugate type-I maximal subgroups, the
families `R(chi)` are mutually orthogonal. -/
theorem nonconjugate_typeI_R_orthogonal [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L1 L2 : Subgroup G}
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2) :
    ∃ data : CrossOrthogonalityData hyp1 hyp2, data.orthogonal := by
  sorry

/-- **Peterfalvi (12.4)**: a class function orthogonal to every type-I
`R(chi)` is constant on each coset `xH` with `x in L - H`. -/
theorem orthogonal_character_constant_on_coset [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {psi : ClassFunction G ℂ} (horth : hyp.characterOrthogonalToR psi)
    {x : G} (hxL : x ∈ L) (hxH : x ∉ hyp.H) :
    ∀ h : G, h ∈ hyp.H → psi (x * h) = psi x := by
  sorry

/-- **Peterfalvi (12.5)**: after the rho-reduction, the resulting character is
constant on `H - H'`. -/
theorem rho_constant_on_H_minus_Hprime [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {psi : ClassFunction G ℂ} (hrho : hyp.rhoConstantFormula psi) :
    ∀ h : G, h ∈ hyp.H → h ∉ hyp.Hprime → psi h = psi 1 := by
  sorry

/-! ## (12.6)--(12.7): type-I Frobenius structure -/

/-- Carrier for Peterfalvi (12.7): a type-I maximal subgroup is Frobenius with
kernel `M_F`. -/
structure TypeIFrobeniusData (M : Subgroup G) where
  typeI : TypeIData M
  complement : Subgroup ↥M
  kernel_eq_MF : Prop
  kernel_eq_MF_holds : kernel_eq_MF
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥M (typeI.typeF.H.subgroupOf M) complement

/-- **Structural input for Peterfalvi (12.6) — Frobenius case.**

When `L` is already Frobenius with kernel `H`, the Sibley Dade setup of (6.8) takes its
case-(c1) (Frobenius) branch, so a `SibleyTarget` for `(τ, S, A)` is available.  Exhibiting it
is the remaining structural obligation; once it lands, and once lane B supplies the (6.8) proof
body of `S08.sibleySetup_is_coherent`, `frobenius_typeI_coherent` is unconditional. -/
noncomputable def sibleyTarget_frobI [Fintype G] {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis L)
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    CoherenceWiring.SibleyTarget hyp.tau hyp.Sset hyp.A := sorry

/-- **Peterfalvi (12.6)**: if `L` is already Frobenius with kernel `H`, then the
family `S` is coherent.

Wired to the (6.8) capstone through the coherence-wiring bridge: given the Frobenius-case
structural witness `sibleyTarget_frobI`, coherence is exactly (6.8).  The proof carries no
`sorry` of its own; its gaps are `sibleyTarget_frobI` (Frobenius structure) and (6.8) (lane B). -/
theorem frobenius_typeI_coherent [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis L)
    (hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) :=
  CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_frobI hyp hfrob)

/-- **Peterfalvi (12.7)**: every maximal subgroup of type I is Frobenius, with
kernel equal to `M_F`. -/
theorem typeI_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M) :
    ∃ data : TypeIFrobeniusData M, data.kernel_eq_MF := by
  sorry

/-! ## (12.8)--(12.12): minimal counterexample analysis -/

/-- **Peterfalvi (12.8), the prime set `π`**: `q ∈ π` when some type-`I` maximal subgroup `M'`
has a **noncyclic Sylow `q`-subgroup in `M' / M'_F`**.  Encoded by a Sylow `q`-subgroup `P ≤ M'`
(`q`-group with `q ∤ [M' : P]`) that is noncyclic and satisfies `q ∣ [M' : M'_F]` — so `P` is not
contained in `M'_F` and its image in `M'/M'_F` is a noncyclic Sylow `q`-subgroup. -/
def InPi (q : ℕ) : Prop :=
  ∃ M' : Subgroup G, M' ∈ maximalSubgroups G ∧ IsTypeI M' ∧
    ∃ P : Subgroup G, P ≤ M' ∧ IsPGroup q ↥P ∧ ¬ q ∣ P.relIndex M' ∧
      ¬ IsCyclic ↥P ∧ q ∣ (maxNilpotentNormalHall M').relIndex M'

/-- **Peterfalvi (12.8)**: the minimal counterexample hypothesis for (12.7).

`M` is a type-`I` maximal subgroup whose Fitting kernel is `K = M_F` (`K' = [K, K]`), and `P₀`
is a Sylow `p`-subgroup of `M` that is noncyclic with `p ∣ [M : M_F]` (so the image of `P₀` in
`M/M_F` is a noncyclic Sylow `p`-subgroup, i.e. `p ∈ π`); `p` is the smallest element of `π`. -/
structure CounterexampleHypothesis where
  p : ℕ
  p_prime : p.Prime
  M : Subgroup G
  K : Subgroup G
  Kprime : Subgroup G
  P0 : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  M_typeI : IsTypeI M
  K_eq_MF : K = maxNilpotentNormalHall M
  Kprime_eq : Kprime = derivedInG K
  P0_le_M : P0 ≤ M
  /-- `P₀` is a `p`-group… -/
  P0_pGroup : IsPGroup p ↥P0
  /-- …and a Sylow `p`-subgroup of `M` (`p ∤ [M : P₀]`). -/
  P0_sylow : ¬ p ∣ P0.relIndex M
  /-- The Sylow `p`-subgroup of `M/M_F` is noncyclic (so `P₀` is noncyclic). -/
  P0_noncyclic : ¬ IsCyclic ↥P0
  /-- …and `p ∣ [M : M_F]` (so `P₀ ⊄ M_F`; together with the Hall property this gives `p ∤ |M_F|`). -/
  p_dvd_index : p ∣ K.relIndex M
  /-- `p` is the smallest prime in `π`. -/
  minimal_p : ∀ q : ℕ, q.Prime → InPi (G := G) q → p ≤ q

/-- The rank-two witness extracted in Peterfalvi (12.9), with all fields stated faithfully.

`L` is the second maximal subgroup with `P₀ ⊆ L_s` (`L_s = mainSubgroup L L_type`); `x` is the
order-`p` element of `Ω₁(P₀)^#` whose centralizer in `K = M_F` escapes `K'`, controls `N_G(⟨x⟩)`,
and escapes `L`. -/
structure RankTwoWitnessData (ctr : CounterexampleHypothesis (G := G)) where
  L : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  /-- Peterfalvi's type attached to `L` (so `L_s = mainSubgroup L L_type`). -/
  L_type : PeterfalviType
  L_hasType : HasPeterfalviType L_type L
  /-- `P₀ ⊆ L_s`. -/
  P0_le_Ls : ctr.P0 ≤ mainSubgroup L L_type
  x : G
  x_mem_P0 : x ∈ ctr.P0
  x_ne_one : x ≠ 1
  /-- `x ∈ Ω₁(P₀)^#`: `x` has order dividing `p`. -/
  x_mem_omega1 : x ^ ctr.p = 1
  /-- `C_K(x) ⊄ K'` (equivalently `C_{K/K'}(x) ≠ 1`). -/
  CKx_not_le_Kprime : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)
  /-- `N_G(⟨x⟩) ⊆ M`. -/
  normalizer_closure_x_le_M :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M
  /-- `C_G(x) ⊄ L`. -/
  centralizer_x_not_le_L : ¬ (Subgroup.centralizer ({x} : Set G) ≤ L)

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Group-theoretic core of Peterfalvi (12.9)** (fully general, `§8`-independent).

If a **noncyclic abelian** group `A` acts **coprimely** on a finite group `K` whose
abelianization is nontrivial (`[K, K] ≠ K`), then some **nontrivial** `a ∈ A` has a fixed
subgroup `C_K(a)` that is *not* contained in the derived subgroup `[K, K]`.

This is the abstract content of the centralizer step of (12.9): there Peterfalvi takes
`A = Ω₁(P₀)` (elementary abelian of rank `2`, hence noncyclic) acting by conjugation on
`K = M_F`, with `[K, K] = K'`, and concludes `∃ x ∈ Ω₁(P₀)^#` with `C_K(x) ⊄ K'`
(equivalently `C_{K/K'}(x) ≠ 1`).

Proof.  `[K, K]` is characteristic, hence `A`-invariant, so `A` acts on the quotient
`K / [K, K]`.  By **BG Proposition 1.16(1)** (Isaacs 6.21,
`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) applied to that quotient action,
`K / [K, K] = ⟨ C_{K/[K,K]}(a) ∣ a ≠ 1 ⟩`.  Since `K / [K, K]` is nontrivial, some
`a ≠ 1` has `C_{K/[K,K]}(a) ≠ 1`; the witnessing coset lifts, by the coprime fixed-point
lifting (**Isaacs Cor 3.28**, `coprime_fixedPoints_quotient`), to an element of `C_K(a)`
outside `[K, K]`. -/
theorem exists_ne_one_actionFixedBy_not_le_commutator
    {A K : Type*} [Group A] [Finite A] [IsMulCommutative A] [Group K] [Finite K]
    (φ : A →* MulAut K) (hCop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hSolv : IsSolvable A ∨ IsSolvable K) (hNC : ¬ IsCyclic A)
    (hK' : commutator K ≠ ⊤) :
    ∃ a : A, a ≠ 1 ∧ ¬ (Ch06.actionFixedBy φ a ≤ commutator K) := by
  classical
  -- `[K, K]` is characteristic, hence `A`-invariant; let `ψ` be the induced quotient action.
  have hN_inv : Ch03.IsAInvariant φ (commutator K) := Ch03.IsAInvariant.of_characteristic φ
  set ψ := quotientMulAutHom hN_inv with hψ
  -- Coprimality on the quotient: `|K / [K,K]|` divides `|K|`.
  have hCopQ : Nat.Coprime (Nat.card A) (Nat.card (K ⧸ commutator K)) :=
    hCop.coprime_dvd_right (commutator K).card_quotient_dvd_card
  -- BG 1.16(1) on the quotient action: the nontrivial fixed-point closure is everything.
  have htop : Ch06.nontrivialActionFixedByClosure ψ = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic' ψ hCopQ hNC
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ a, a ≠ 1 → C_K(a) ≤ [K, K]`.  Show the quotient closure is `⊥`.
  have hquot_bot : Ch06.nontrivialActionFixedByClosure ψ ≤ ⊥ := by
    rw [Ch06.nontrivialActionFixedByClosure_le_iff]
    intro a ha q hq
    -- `q ∈ C_{K/K'}(a)`: `q` is fixed by every element of `⟨a⟩`.
    have hq_zp : q ∈ Ch06.actionFixedPoints ψ (Subgroup.zpowers a) := by
      rw [← Ch06.actionFixedBy_eq_actionFixedPoints_zpowers]; exact hq
    -- Lift `q = mk' g` and assemble the coset-fixed hypothesis on `⟨a⟩`.
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator K) q
    have hg_fix : ∀ b : ↥(Subgroup.zpowers a), ∃ n ∈ commutator K, φ (b : A) g = g * n := by
      intro b
      have hb := (Ch06.mem_actionFixedPoints.mp hq_zp) b
      rw [hψ, quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
      exact ⟨g⁻¹ * φ (b : A) g, by simpa using (commutator K).inv_mem hb, by group⟩
    -- Coprime fixed-point lifting (Isaacs Cor 3.28) on the cyclic group `⟨a⟩`.
    have hCop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers a)) (Nat.card K) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have hSolv' : IsSolvable ↥(Subgroup.zpowers a) ∨ IsSolvable K := by
      rcases hSolv with hA | hK
      · haveI := hA; exact Or.inl inferInstance
      · exact Or.inr hK
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      Ch04.coprime_fixedPoints_quotient hCop' hSolv'
        (Ch03.IsAInvariant.of_characteristic (φ.comp (Subgroup.zpowers a).subtype)) hg_fix
    -- `c` is fixed by `a`, hence `c ∈ C_K(a) ≤ [K, K]` by `hcon`.
    have hca : φ a c = c := hc_fix ⟨a, Subgroup.mem_zpowers a⟩
    have hc_mem : c ∈ commutator K := hcon a ha (Ch06.mem_actionFixedBy.mpr hca)
    -- Then `g = c * n⁻¹ ∈ [K, K]`, so the coset `q = mk' g` is trivial.
    have hg_mem : g ∈ commutator K := by
      have : g = c * n⁻¹ := by rw [hcn]; group
      rw [this]; exact (commutator K).mul_mem hc_mem ((commutator K).inv_mem hn)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hg_mem
  -- `⊤ ≤ ⊥` forces `K / [K, K]` trivial, i.e. `[K, K] = ⊤`, contradicting `hK'`.
  have hbot : (⊤ : Subgroup (K ⧸ commutator K)) = ⊥ := le_bot_iff.mp (htop ▸ hquot_bot)
  apply hK'
  rw [Subgroup.eq_top_iff']
  intro k
  have hk1 : QuotientGroup.mk' (commutator K) k ∈ (⊥ : Subgroup (K ⧸ commutator K)) := by
    rw [← hbot]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact hk1

/-- **Conjugation form of the (12.9) centralizer core** (ambient subgroups, directly the
form consumed by (12.9)).  If a **noncyclic abelian** subgroup `A ≤ G` normalizes a finite
subgroup `K` of **coprime** order whose abelianization is nontrivial (`⁅K, K⁆ ≠ K`), then
some `x ∈ A`, `x ≠ 1`, has `C_K(x) = C_G(x) ⊓ K` **not** contained in `⁅K, K⁆`.

Specialization of `exists_ne_one_actionFixedBy_not_le_commutator` to the conjugation action
`A → MulAut K` (`Subgroup.normalizerMonoidHom`): the abstract fixed subgroup `C_K(a)` becomes
`C_G(a) ⊓ K` and `commutator ↥K` maps to `⁅K, K⁆` under `K.subtype`. -/
theorem exists_mem_centralizer_inf_not_le_commutator
    {A K : Subgroup G} [Finite ↥A] [IsMulCommutative ↥A] [Finite ↥K]
    (hAK : A ≤ Subgroup.normalizer K) (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥K))
    (hSolv : IsSolvable ↥A ∨ IsSolvable ↥K) (hNC : ¬ IsCyclic ↥A) (hK' : ⁅K, K⁆ ≠ K) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 ∧ ¬ (Subgroup.centralizer {x} ⊓ K ≤ ⁅K, K⁆) := by
  classical
  -- The conjugation action `φ : A → MulAut K` and the `K.subtype`-image of `[↥K, ↥K]`.
  set φ : ↥A →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hAK)
    with hφ
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hg; exact ⟨⟨g, hg⟩, rfl⟩
  have hmap : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, htop_map]
  -- `[↥K, ↥K] ≠ ⊤`: else its `K.subtype`-image would be `⁅K, K⁆ = K`.
  have hKtop : commutator ↥K ≠ ⊤ := by
    intro h; exact hK' (by rw [← hmap, h, htop_map])
  obtain ⟨a, ha_ne, hnle⟩ :=
    exists_ne_one_actionFixedBy_not_le_commutator φ hCop hSolv hNC hKtop
  -- Translate the abstract conclusion to ambient subgroups.
  obtain ⟨n, hn_fix, hn_out⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨(a : G), a.2, fun h => ha_ne (Subtype.ext h), SetLike.not_le_iff_exists.mpr
    ⟨(n : G), ?_, ?_⟩⟩
  · -- `n ∈ C_G(a) ⊓ K`: `a` conjugates `n` to itself, and `n ∈ K`.
    rw [Ch06.mem_actionFixedBy] at hn_fix
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) :=
      congrArg (Subtype.val) hn_fix
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, n.2⟩
    rintro y rfl
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `n ∉ ⁅K, K⁆`: else `n ∈ [↥K, ↥K]`, contradicting `hn_out`.
    rw [← hmap]
    intro hmem
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hmem
    exact hn_out (by rw [show n = m from Subtype.ext hmn.symm]; exact hm)

/-- **Peterfalvi (12.9), the order-`p` centralizer witness** (the genuine, `§8`-free heart of
(12.9)).  Given the counterexample data with `P₀` abelian, coprime to `K = M_F`, normalizing `K`,
and `K` not perfect, there is an element `x ∈ Ω₁(P₀)^#` (order dividing `p`) with `C_K(x) ⊄ K'`.

Proof: apply the centralizer core `exists_mem_centralizer_inf_not_le_commutator` to the abelian
noncyclic `P₀` acting by conjugation on `K`, yielding `y ∈ P₀^#` with `C_K(y) ⊄ K'`; then pass to
the order-`p` power `x = y ^ (|y| / p)` — its centralizer contains `C_K(y)`, so still escapes `K'`. -/
theorem exists_orderP_centralizer_witness [Finite G]
    (ctr : CounterexampleHypothesis (G := G))
    (habelian : IsMulCommutative ↥ctr.P0)
    (hcoprime : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K))
    (hP0_norm : ctr.P0 ≤ Subgroup.normalizer ctr.K)
    (hKperfect : ⁅ctr.K, ctr.K⁆ ≠ ctr.K) :
    ∃ x : G, x ∈ ctr.P0 ∧ x ≠ 1 ∧ x ^ ctr.p = 1 ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  haveI := habelian
  haveI : Group.IsNilpotent ↥ctr.P0 := ctr.P0_pGroup.isNilpotent
  -- `K' = ⁅K, K⁆`.
  have hKprime : ctr.Kprime = ⁅ctr.K, ctr.K⁆ :=
    ctr.Kprime_eq.trans (Subgroup.map_subtype_commutator ctr.K)
  -- Centralizer core (A = P₀, abelian noncyclic, coprime, normalizing K, K not perfect).
  obtain ⟨y, hyP0, hy_ne, hy_cent⟩ :=
    exists_mem_centralizer_inf_not_le_commutator (A := ctr.P0) (K := ctr.K)
      hP0_norm hcoprime (Or.inl inferInstance) ctr.P0_noncyclic hKperfect
  -- `y` has `p`-power order `p ^ k` with `k ≥ 1`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp ctr.P0_pGroup) ⟨y, hyP0⟩
  have hoy : orderOf y = ctr.p ^ k :=
    (orderOf_injective ctr.P0.subtype ctr.P0.subtype_injective ⟨y, hyP0⟩).trans hk
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hoy; exact absurd hoy hy_ne
    · exact h
  have hp_dvd : ctr.p ∣ orderOf y := hoy ▸ dvd_pow_self ctr.p (by omega)
  have hord_pos : 0 < orderOf y := hoy ▸ pow_pos ctr.p_prime.pos k
  -- The order-`p` power `x = y ^ (|y| / p)`.
  set n := orderOf y / ctr.p with hn
  have hnp : n * ctr.p = orderOf y := Nat.div_mul_cancel hp_dvd
  have hn_pos : 0 < n := by
    rw [hn]; exact Nat.div_pos (Nat.le_of_dvd hord_pos hp_dvd) ctr.p_prime.pos
  have hn_lt : n < orderOf y := by
    rw [hn]; exact Nat.div_lt_self hord_pos ctr.p_prime.one_lt
  refine ⟨y ^ n, ctr.P0.pow_mem hyP0 n, ?_, ?_, ?_⟩
  · -- `y ^ n ≠ 1`: else `|y| ∣ n < |y|`, impossible.
    rw [Ne, ← orderOf_dvd_iff_pow_eq_one]
    exact Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
  · -- `(y ^ n) ^ p = y ^ (n * p) = y ^ |y| = 1`.
    rw [← pow_mul, hnp, pow_orderOf_eq_one]
  · -- `C_K(y ^ n) ⊇ C_K(y) ⊄ K'`.
    rw [hKprime]
    intro hle
    apply hy_cent
    refine le_trans (inf_le_inf_right ctr.K ?_) hle
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro z rfl
    exact Commute.pow_left (hg y rfl) n

/-- **Peterfalvi (12.9), the rank-two input for `P₀`** — the residual §8 obligation `(8.12.a)`
(a BG §16 consequence, **absent** from the repo): every Sylow subgroup of the type-`I` complement
`U` (`M = M_F ⋊ U`) is abelian of rank `≤ 2`; here, with `P₀` noncyclic (Hypothesis `(12.8)`,
`ctr.P0_noncyclic`), this forces `P₀` abelian of rank exactly `2`.

(The other structural inputs `P₀` coprime to `K`, `P₀ ≤ N_G(K)`, `⁅K, K⁆ ≠ K` are discharged in
`exists_rankTwoWitness` from `(8.11)` [`M_F` Hall] and `M_F ◁ M` nilpotent + nontrivial.) -/
theorem counterexample_P0_K_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 := by
  sorry

/-- A `p`-Hall subgroup `H` (its order having only `p`-primary divisors among `π = π(|H|)`) with
`p ∣ |H|` contains a Sylow `p`-subgroup of the ambient group `G`.

A Sylow `p`-subgroup `R` of `↥H` maps to a subgroup `R.map H.subtype ≤ H` of `G` of the same
order `p ^ v_p(|H|)`.  Since `H` is Hall, `p ∤ [G : H]`, so `v_p(|H|) = v_p(|G|)`; hence
`R.map H.subtype` is a Sylow `p`-subgroup of `G` contained in `H`. -/
theorem exists_sylow_le_of_hall [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors H) (hp : p ∣ Nat.card ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H := by
  classical
  -- A Sylow `p`-subgroup `R` of `↥H`.
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥H))
  -- The `p`-multiplicity of `|H|` equals that of `|G|`, because `H` is Hall and `p ∣ |H|`.
  have hfact : (Nat.card ↥H).factorization p = (Nat.card G).factorization p := by
    have hcop : Nat.Coprime (Nat.card ↥H) H.index := hHall.coprime_index
    have hp_notdvd : ¬ p ∣ H.index :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hp)
    have hidx0 : H.index.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_notdvd
    have hsplit : (Nat.card G).factorization p =
        (Nat.card ↥H).factorization p + H.index.factorization p := by
      rw [← H.card_mul_index, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
        Subgroup.index_ne_zero_of_finite]
      rfl
    rw [hsplit, hidx0, add_zero]
  -- `R.map H.subtype` is a `p ^ v_p(|G|)`-subgroup of `G`, i.e. a Sylow `p`-subgroup.
  have hcardR : Nat.card ↥(R : Subgroup ↥H) = p ^ (Nat.card G).factorization p := by
    rw [R.card_eq_multiplicity, hfact]
  have hcardQ : Nat.card ↥((R : Subgroup ↥H).map H.subtype) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hcardR]
  exact ⟨Sylow.ofCard ((R : Subgroup ↥H).map H.subtype) hcardQ,
    by rw [Sylow.coe_ofCard]; exact Subgroup.map_subtype_le _⟩

/-- **Peterfalvi (12.9), existence of the second maximal `L`** — a §8 obligation
(`(8.17.a)` `bgTheoremE_cover_data`: `p ∈ π(G)` is covered by some `π((M_i)_s)`, giving a maximal
`L` with `p ∣ |L_s|`; then `(8.11)`/`L_s ⊇ Sylow_p(G)` and Sylow conjugation place `P₀ ⊆ L_s`). -/
theorem exists_second_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ (L : Subgroup G) (Lt : PeterfalviType), L ∈ maximalSubgroups G ∧ L ≠ ctr.M ∧
      HasPeterfalviType Lt L ∧ ctr.P0 ≤ mainSubgroup L Lt := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `p ∈ π(G)`: `p ∣ [M : M_F] ∣ |M| ∣ |G|`.
  have hp_in_G : ctr.p ∈ (Nat.card G).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨ctr.p_prime, ?_, Nat.card_pos.ne'⟩
    refine dvd_trans ctr.p_dvd_index (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card ctr.M))
    exact Subgroup.relIndex_dvd_card (H := ctr.K) (K := ctr.M)
  -- `p ∤ |M_F| = |K|`: `(8.11)` makes `M_F` Hall, and `p ∣ [M : M_F] ∣ [G : M_F]`.
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hpK : ¬ ctr.p ∣ Nat.card ↥ctr.K := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    exact ctr.p_prime.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm)
  -- BG Theorem E cover data: `p ∈ π((M_i)_s)` for some representative `M_i = L₀`.  Repackage the
  -- representative as genuine local variables `L₀, Lt` (so we may later `cases` on the type label).
  obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  obtain ⟨i, hi⟩ := (data.primeFactors_cover ctr.p ctr.p_prime).mp hp_in_G
  obtain ⟨L₀, Lt, hL₀max, hL₀typed, hi'⟩ :
      ∃ (L₀ : Subgroup G) (Lt : PeterfalviType), L₀ ∈ maximalSubgroups G ∧
        HasPeterfalviType Lt L₀ ∧
        ctr.p ∈ (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors :=
    ⟨data.reps i, data.tau i, data.maximal i, data.typed i, hi⟩
  have hp_Ls : ctr.p ∣ Nat.card ↥(mainSubgroup L₀ Lt) := (Nat.mem_primeFactors.mp hi').2.1
  -- `(8.11)`: `(L₀)_s` is Hall, hence contains a Sylow `p`-subgroup `Q` of `G`.
  have hLsHall : Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors
      (mainSubgroup L₀ Lt) :=
    (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hL₀max hL₀typed).2
  obtain ⟨Q, hQle⟩ := exists_sylow_le_of_hall hLsHall hp_Ls
  -- A Sylow `p`-subgroup `Q'` of `G` over `P₀`, then conjugate `Q` to `Q'`.
  obtain ⟨Q', hQ'le⟩ := ctr.P0_pGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  -- `P₀ ≤ Q' = ↑(g • Q) = conj g • ↑Q ≤ conj g • (L₀)_s`.
  have hP0_le : ctr.P0 ≤ MulAut.conj g • mainSubgroup L₀ Lt := by
    refine hQ'le.trans ?_
    have hQ'eq : (Q' : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    rw [hQ'eq]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQle
  -- Assemble: `L = conj g • L₀`, type `Lt`, with `P₀ ⊆ (conj g • L₀)_s`.
  refine ⟨MulAut.conj g • L₀, Lt, mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hL₀max)), ?_,
    hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed, ?_⟩
  · -- `conj g • L₀ ≠ M`: else `M` has type `Lt`; if `Lt = I` then `p ∣ |K|` (false), else `M` is
    -- both type I and non-I (false).
    rintro hEq
    have hMtype : HasPeterfalviType Lt ctr.M :=
      hEq ▸ hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed
    -- transport the divisibility `p ∣ |(L₀)_s|` to `p ∣ |M_s|`.
    have hp_Ms : ctr.p ∣ Nat.card ↥(mainSubgroup ctr.M Lt) := by
      have hcard : Nat.card ↥(mainSubgroup ctr.M Lt) = Nat.card ↥(mainSubgroup L₀ Lt) := by
        rw [← hEq, ← mainSubgroup_pointwise_smul, card_pointwise_smul]
      rw [hcard]; exact hp_Ls
    -- `ctr.M` has type `Lt` and type I.  Type `I` forces `p ∣ |K|` (false); any non-I label
    -- makes `ctr.M` non-I, contradicting type I via `not_isTypeI_of_isTypeNonI`.
    have hMnotNonI : ¬ IsTypeNonI ctr.M := fun h =>
      OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG ctr.M_maximal h ctr.M_typeI
    cases Lt with
    | I => exact hpK (by rw [ctr.K_eq_MF]; exact hp_Ms)
    | II => exact hMnotNonI (Or.inl hMtype)
    | III => exact hMnotNonI (Or.inr (Or.inl hMtype))
    | IV => exact hMnotNonI (Or.inr (Or.inr (Or.inl hMtype)))
    | V => exact hMnotNonI (Or.inr (Or.inr (Or.inr hMtype)))
  · -- `P₀ ⊆ mainSubgroup (conj g • L₀) Lt`.
    rw [← mainSubgroup_pointwise_smul]; exact hP0_le

/-- **Peterfalvi (12.9), centralizer control** — **discharged** from `(8.12.b)`
(`typeI_or_typeII_centralizer_unique`) + `G` simple.

Applying `(8.12.b)` with `U = M` and `X = {x}` (`x ∈ M^#`, and `C_K(x) ⊄ K'` gives
`M_F ⊓ C_G(x) ≠ 1`) yields `C_G(x) ≤ M` together with `IsUniquelyMaximal (C_G(x))` — `M` is the
*unique* maximal subgroup over `C_G(x)`.  Hence: `N_G(⟨x⟩) ⊇ C_G(x)` is a proper subgroup
(`⟨x⟩` is a proper nontrivial subgroup of the nonabelian simple `G`, so not normal), so it lies
in a maximal subgroup over `C_G(x)`, which must be `M`; and any maximal `L ≠ M` cannot contain
`C_G(x)`. -/
theorem centralizer_control_of_CKx [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hLM : L ≠ ctr.M)
    {Lt : PeterfalviType} (hLt : HasPeterfalviType Lt L) (hPL : ctr.P0 ≤ mainSubgroup L Lt)
    {x : G} (hx : x ∈ ctr.P0) (hxne : x ≠ 1)
    (hCKx : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)) :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ≤ L) := by
  classical
  haveI : IsSimpleGroup G := hG.simple
  have hMcoatom : IsCoatom ctr.M := ctr.M_maximal
  have hLcoatom : IsCoatom L := hL
  have hxM : x ∈ ctr.M := ctr.P0_le_M hx
  -- `M_F ⊓ C_G(x) ≠ ⊥` from `C_K(x) ⊄ K'`.
  have hCKne : maxNilpotentNormalHall ctr.M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot; apply hCKx; rw [ctr.K_eq_MF, inf_comm, hbot]; exact bot_le
  have hxsharp : ({x} : Set G) ⊆ sharpSubgroup ctr.M := by
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact ⟨hxM, fun h => hxne (Set.mem_singleton_iff.mp h)⟩
  -- (8.12.b): `C_G(x) ≤ M` and uniquely maximal.
  obtain ⟨hCxleM, huniq⟩ := OddOrder.Peterfalvi.S10.typeI_or_typeII_centralizer_unique hG
    ctr.M_maximal (Or.inl ctr.M_typeI) (le_refl ctr.M) ({x} : Set G) (Set.singleton_nonempty x)
    hxsharp hCKne
  refine ⟨?_, fun hCxleL => hLM (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hLcoatom hCxleL).symm⟩
  -- `N_G(⟨x⟩) ⊆ M`.
  have hCx_le_Nx : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.centralizer_closure]; exact Subgroup.centralizer_le_normalizer _
  have hcl_le_M : Subgroup.closure ({x} : Set G) ≤ ctr.M := Subgroup.closure_le _ |>.mpr (by
    simpa using hxM)
  have hNx_lt : Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hb | ht
    · exact hxne (by simpa [hb] using Subgroup.subset_closure (Set.mem_singleton x))
    · exact hMcoatom.1 (top_le_iff.mp (ht ▸ hcl_le_M))
  obtain ⟨N, hNco, hNx_le_N⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNx_lt
  exact hNx_le_N.trans (le_of_eq
    (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hNco (hCx_le_Nx.trans hNx_le_N)).symm)

/-- **Peterfalvi (12.9)**: the counterexample has an abelian rank-two Sylow
witness and an element whose centralizers force a second maximal subgroup.

Honest assembly: the structural inputs `(8.12.a)`/`(8.11)` (`counterexample_P0_K_structure`) give
`P₀` abelian of rank `2`, coprime to `K`, normalizing `K`, with `K` not perfect; the genuine
`§8`-free `exists_orderP_centralizer_witness` then produces the order-`p` element `x` with
`C_K(x) ⊄ K'`; `(8.17.a)` (`exists_second_maximal`) supplies `L`; and `(8.12.b)`
(`centralizer_control_of_CKx`) the centralizer conditions. -/
theorem exists_rankTwoWitness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 ∧ Nonempty (RankTwoWitnessData ctr) := by
  obtain ⟨hab, hrank⟩ := counterexample_P0_K_structure hG ctr
  refine ⟨hab, hrank, ?_⟩
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  -- `P₀` coprime to `K`: `(8.11)` makes `M_F` Hall (`p ∤ |M_F|` from `p ∣ [M : M_F] ∣ [G : M_F]`).
  have hcop : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K) := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    have hcop_p : Nat.Coprime ctr.p (Nat.card ↥ctr.K) :=
      Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
    rw [hn]; exact hcop_p.pow_left n
  -- `P₀ ≤ N_G(K)` from `M_F ◁ M` (`maxNilpotentNormalHall_le_normalizer`).
  have hnorm : ctr.P0 ≤ Subgroup.normalizer ctr.K := by
    rw [ctr.K_eq_MF]
    exact ctr.P0_le_M.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M)
  -- `⁅K, K⁆ ≠ K`: `K = M_F` is nilpotent and nontrivial, hence not perfect.
  have hperf : ⁅ctr.K, ctr.K⁆ ≠ ctr.K := by
    obtain ⟨tiData⟩ := ctr.M_typeI
    have hKH : ctr.K = tiData.typeF.H := ctr.K_eq_MF.trans tiData.typeF.H_eq.symm
    haveI : Nontrivial ↥ctr.K :=
      ctr.K.nontrivial_iff_ne_bot.mpr (hKH ▸ tiData.typeF.H_nontrivial)
    haveI : Group.IsNilpotent ↥ctr.K :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent ctr.M
    have hlt : commutator ↥ctr.K < ⊤ :=
      IsSolvable.commutator_lt_top_of_nontrivial (G := ↥ctr.K)
    intro hEq
    have htop_map : (⊤ : Subgroup ↥ctr.K).map ctr.K.subtype = ctr.K := by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    exact hlt.ne (Subgroup.map_injective ctr.K.subtype_injective
      (by rw [Subgroup.map_subtype_commutator, hEq, htop_map]))
  obtain ⟨x, hxP0, hxne, hxp, hCKx⟩ := exists_orderP_centralizer_witness ctr hab hcop hnorm hperf
  obtain ⟨L, Lt, hLmax, hLne, hLt, hPL⟩ := exists_second_maximal hG ctr
  obtain ⟨hNx, hCx⟩ := centralizer_control_of_CKx hG ctr hLmax hLne hLt hPL hxP0 hxne hCKx
  exact ⟨{ L := L, L_maximal := hLmax, L_type := Lt, L_hasType := hLt, P0_le_Ls := hPL,
           x := x, x_mem_P0 := hxP0, x_ne_one := hxne, x_mem_omega1 := hxp,
           CKx_not_le_Kprime := hCKx, normalizer_closure_x_le_M := hNx,
           centralizer_x_not_le_L := hCx }⟩

/-- **Peterfalvi (12.10)**: the maximal subgroup `L` supplied by (12.9) is
Frobenius with kernel `L_F`. -/
theorem witness_L_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ frob : TypeIFrobeniusData data.L, frob.kernel_eq_MF := by
  sorry

/-- **Peterfalvi (12.11)**: `M inter L` complements `K` in `M` and lies in the
Fitting kernel `H` of the witness subgroup `L`. -/
theorem intersection_complement_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) ∧
      ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L := by
  sorry

/-- **(12.12) Case A core.**  A finite group `E` acting faithfully on a one-dimensional
`𝔽_p`-space `V` is cyclic, with `|E| ∣ |V| - 1 = p - 1`.  This is the reducible / rank-one case
of Peterfalvi (12.12): `End_{𝔽_p}(V) ≅ 𝔽_p` (every endomorphism of a line is a homothety), so
`E ↪ End(V)ˣ ≅ (ℤ/p)ˣ`, a cyclic group of order `p - 1`. -/
theorem isCyclic_and_card_dvd_of_faithful_one_dim
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank (ZMod p) V = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `End_{𝔽_p}(V) ≅ 𝔽_p` via `algebraMap` (bijective in dimension one: every endo is `c • id`).
  have hsurj : Function.Surjective (algebraMap (ZMod p) (Module.End (ZMod p) V)) := by
    intro u
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim u
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc, Module.End.one_eq_id]⟩
  have hinj : Function.Injective (algebraMap (ZMod p) (Module.End (ZMod p) V)) :=
    (algebraMap (ZMod p) (Module.End (ZMod p) V)).injective
  let eRing : ZMod p ≃+* Module.End (ZMod p) V := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  -- `E ↪ End(V)ˣ ≃ (ℤ/p)ˣ`.
  let φ : E →* (ZMod p)ˣ :=
    (Units.mapEquiv eRing.toMulEquiv).symm.toMonoidHom.comp (MonoidHom.toHomUnits ρ)
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hfaith
    have h1 : (MonoidHom.toHomUnits ρ) a = (MonoidHom.toHomUnits ρ) b :=
      (Units.mapEquiv eRing.toMulEquiv).symm.injective (by simpa [φ] using hab)
    simpa using congrArg (Units.val) h1
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  haveI : IsCyclic φ.range := inferInstance
  have hcardV : Nat.card V = p := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, pow_one, Nat.card_eq_fintype_card,
      ZMod.card]
  refine ⟨isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm.toMonoidHom
      (MonoidHom.ofInjective hφinj).symm.surjective, ?_⟩
  rw [hcardV]
  calc Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    _ ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]

/-- **(12.12) irreducible-case core.**  An odd-order group `E` acting faithfully and
irreducibly on a two-dimensional `𝔽_p`-space `V` (with `p ∤ |E|`) is cyclic, with
`|E| ∣ |V| - 1 = p² - 1`.  This is the rank-two irreducible case of Peterfalvi (12.12):
BG Theorem 2.6(a) (`odd_two_dim_abelian`) abelianizes `E`, and the commutativity-free Singer
mechanism (`isCyclic_and_card_dvd_of_faithful_irreducible_comm`) then realizes `E` inside the
units of the Singer field `𝔽_p[E] ⧸ I ≅ 𝔽_{p²}`. -/
theorem isCyclic_and_card_dvd_of_odd_two_dim_irreducible
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- BG 2.6(a): a faithful odd two-dimensional representation has abelian image.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  -- Give `V` the `𝔽_p[E]`-module structure of the representation *directly* (this is
  -- definitionally `ρ.asModule`'s instance, but stated on `V` so that instance synthesis does
  -- not choke on the `ρ.asModule` notation — which it does once `IsIrreducible ρ` is around).
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  exact isCyclic_and_card_dvd_of_faithful_irreducible_comm (M := V) hcomm hfaith'

/-- **Peterfalvi (12.12)**: the Frobenius complement in the witness subgroup is
cyclic, with order dividing `p - 1` or `p + 1`. -/
theorem complement_cyclic_order_dvd [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (frob : TypeIFrobeniusData L) :
    IsCyclic ↥frob.complement ∧
      ((Nat.card ↥frob.complement ∣ ctr.p - 1) ∨
        (Nat.card ↥frob.complement ∣ ctr.p + 1)) := by
  sorry

/-! ## (12.13)--(12.16): Dade notation and contradiction -/

/-- **Peterfalvi (12.13)**: notation for the final Dade calculation in the
minimal counterexample. -/
structure DadeNotation {L : Subgroup G} (hyp : Hypothesis L) where
  e : ℕ
  e_eq_index : Prop
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  chi : ClassFunction ↥L ℂ
  chi_mem : chi ∈ hyp.Sset
  chi_degree_eq_e : chi 1 = (e : ℂ)
  psi : ClassFunction G ℂ
  psi_eq_tau1_chi : psi = tau1 chi
  rhoFormula : Prop
  rhoMFormula : Prop

/-- **Peterfalvi (12.14)**: the character `psi` is constant on the coset `xK`. -/
theorem psi_constant_on_xK [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (hyp : Hypothesis L) (witness : RankTwoWitnessData ctr)
    (dade : DadeNotation hyp) :
    ∀ g : G, g ∈ ctr.K → dade.psi (witness.x * g) = dade.psi witness.x := by
  sorry

/-- **Peterfalvi (12.15)**: the rho image is unchanged on `K#`, constant on
`K - K'`, and has integer values there. -/
theorem rhoM_integer_values [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    {hyp : Hypothesis L} (dade : DadeNotation hyp) :
    dade.rhoMFormula ∧
      (∀ g : G, g ∈ ctr.K → g ∉ ctr.Kprime → ∃ z : ℤ, dade.psi g = (z : ℂ)) := by
  sorry

/-- **Peterfalvi (12.16)**: the minimal counterexample of (12.8) is impossible. -/
theorem counterexample_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    False := by
  sorry

/-! ## (12.17): forcing case (b) of Theorem (8.8) -/

/-- **Peterfalvi (12.17)**: the all-type-I case of Theorem (8.8) is impossible,
so the case-(b) data of (8.8) exists. -/
theorem theorem88_caseB_holds [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) := by
  sorry

end OddOrder.Peterfalvi.S14
