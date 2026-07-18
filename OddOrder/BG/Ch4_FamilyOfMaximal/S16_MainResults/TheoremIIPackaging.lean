/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TamelyImbedded
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_Lemma1413

/-! # BG Theorem II (Tii): the system of supporting subgroups for `A(M)`

**Bender–Glauberman, *Local Analysis for the Odd Order Theorem*** (LMS LNS 188), Chapter IV
§16, **Theorem II (Tii)** (mmd:4571) and the **Remark** after it (mmd:4575): for an arbitrary
maximal subgroup `M` of a minimal simple group `G` of odd order, the subset `X = A(M) = ASet M U`
is *tamely imbedded* — when the escaping set `D = escapingSharpSet M X` is nonempty it admits a
finite `SystemOfSupportingSubgroups`.

This file assembles the family and delivers `TamelyImbedded M (ASet M U)`.

## The family

Following the book, the supporting maximal subgroups `M₁,…,Mₙ` are a set of `G`-conjugacy
representatives of the *neighbour maximals*
`𝓐 = { N(x) : x ∈ D }`, where `N(x)` is the unique maximal subgroup over `C_G(x)` (Theorem D(4)).
Each `N(x)` is of Type I or II, and `Hᵢ = M_{iF} = M_{iσ} = maxNilpotentNormalHall Mᵢ`.

## Clause status

`(Ti)` is reused from `theoremII_tame_embedding`.  The `(Tii)` clauses `maximal`, `typeIorII`,
`(a) coprime_orders`, `(b) factorization`/`inf_M_supporting`, and `(e) escape_centralizer` are
assembled here from Theorem D(4), Theorem E(2) (`sigma_reps_pairwise_disjoint`), Lemma 14.13(b)
(`signalizer_neighbour_conjugator_in_M`), and Theorem D(3)
(`signalizer_centralizer_isComplement`).  The clauses `(c) coprime_centralizer` and
`(d) a0_ti`, and the universally-quantified `(Tiii)`, enter as named hypotheses of the
`_of_clauses` packaging theorems (their proofs are the remaining §16 residuals — Lemma 14.13(a)
plus the `A₀(Mᵢ)` TI structure and the arbitrary-system Frobenius forcing).
-/

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## A conjugacy transversal of a set of subgroups -/

/-- **Conjugacy representatives of a set of subgroups.**  For any set `S` of subgroups of a group
with finitely many subgroups, there is a subset `reps ⊆ S` of pairwise non-conjugate subgroups such
that every member of `S` is `G`-conjugate to one of them.  (The transversal of the equivalence
relation `IsConjugateSubgroup` restricted to `S`.)  Used to build the finite family `M₁,…,Mₙ` of
supporting subgroups in Theorem II (Tii). -/
theorem exists_conjugacy_reps [Finite (Subgroup G)] (S : Set (Subgroup G)) :
    ∃ reps : Set (Subgroup G), reps ⊆ S ∧
      (∀ Mi ∈ reps, ∀ Mj ∈ reps, S14.IsConjugateSubgroup Mi Mj → Mi = Mj) ∧
      (∀ N ∈ S, ∃ Mi ∈ reps, S14.IsConjugateSubgroup N Mi) := by
  classical
  let T := {N : Subgroup G // N ∈ S}
  let σ : Setoid T :=
    ⟨fun a b => S14.IsConjugateSubgroup a.1 b.1,
      ⟨fun a => S14.IsConjugateSubgroup.refl a.1, fun h => S14.IsConjugateSubgroup.symm h,
        fun h₁ h₂ => S14.IsConjugateSubgroup.trans h₁ h₂⟩⟩
  refine ⟨Set.range (fun c : Quotient σ => ((Quotient.out c).1 : Subgroup G)), ?_, ?_, ?_⟩
  · rintro Mi ⟨c, rfl⟩; exact (Quotient.out c).2
  · rintro Mi ⟨c, rfl⟩ Mj ⟨d, rfl⟩ hconj
    have hrel : σ.r (Quotient.out c) (Quotient.out d) := hconj
    have hcd : c = d := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq d]; exact Quotient.sound hrel
    rw [hcd]
  · intro N hN
    refine ⟨((Quotient.mk σ ⟨N, hN⟩).out.1 : Subgroup G), ⟨Quotient.mk σ ⟨N, hN⟩, rfl⟩, ?_⟩
    have hexact : σ.r ((Quotient.mk σ ⟨N, hN⟩).out) ⟨N, hN⟩ :=
      Quotient.exact (Quotient.out_eq (Quotient.mk σ ⟨N, hN⟩))
    exact IsConjugateSubgroup.symm hexact

/-! ## Conjugation of centralizers and `A(M)` -/

/-- `C_G(m x m⁻¹) = m · C_G(x) · m⁻¹` (as a pointwise-conjugated subgroup). -/
theorem centralizer_conj_smul_eq (m x : G) :
    Subgroup.centralizer ({m * x * m⁻¹} : Set G) =
      MulAut.conj m • Subgroup.centralizer ({x} : Set G) := by
  ext c
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hval : (MulAut.conj m)⁻¹ • c = m⁻¹ * c * m := by
    change (MulAut.conj m).symm c = _; rw [MulAut.conj_symm_apply]
  rw [hval]
  constructor
  · intro hc
    have hkey : m * (m⁻¹ * c * m * x) * m⁻¹ = m * (x * (m⁻¹ * c * m)) * m⁻¹ := by
      rw [show m * (m⁻¹ * c * m * x) * m⁻¹ = c * (m * x * m⁻¹) by group,
        show m * (x * (m⁻¹ * c * m)) * m⁻¹ = (m * x * m⁻¹) * c by group]
      exact hc
    exact mul_left_cancel (mul_right_cancel hkey)
  · intro hc
    calc c * (m * x * m⁻¹)
        = m * (m⁻¹ * c * m * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * c * m)) * m⁻¹ := by rw [hc]
      _ = (m * x * m⁻¹) * c := by group

/-- Conjugating a subgroup by an inner automorphism preserves triviality. -/
theorem conj_smul_eq_bot_iff (m : G) (H : Subgroup G) :
    (MulAut.conj m • H : Subgroup G) = ⊥ ↔ H = ⊥ := by
  have hmap : (MulAut.conj m • H : Subgroup G) = H.map (MulAut.conj m : G →* G) := by
    rw [Subgroup.pointwise_smul_def]; rfl
  rw [hmap, Subgroup.map_eq_bot_iff,
    (MonoidHom.ker_eq_bot_iff (MulAut.conj m : G →* G)).mpr (MulAut.conj m).injective, le_bot_iff]

/-- **`A(M)` is invariant under `M`-conjugation.**  `A(M) = ASet M U = \widehat{M_σ} ∩ (U M_σ)`;
both factors are stable under conjugation by `m ∈ M` (`M_σ ◁ M` gives the `\widehat{M_σ}` factor,
and the normality of `U M_σ` in `M` — Theorem A(3), passed as `hnorm` — gives the other). -/
theorem aSet_conj_closed {M U : Subgroup G}
    (hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal) (hUM : U ≤ M)
    {m x : G} (hm : m ∈ M) (hx : x ∈ ASet M U) : m * x * m⁻¹ ∈ ASet M U := by
  obtain ⟨⟨hxM, hxC⟩, hxUMσ⟩ := hx
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hmxM : m * x * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)
  -- `conj m` fixes `M_σ` (normal in `M`).
  have hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hmNMσ : m ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hMσM).mp hMσnorm) hm
  have hconjMσ : MulAut.conj m • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M :=
    conj_smul_eq_self_of_mem_normalizer hmNMσ
  refine ⟨⟨hmxM, ?_⟩, ?_⟩
  · -- `M_σ ⊓ C_G(mxm⁻¹) = conj m • (M_σ ⊓ C_G(x)) ≠ ⊥`.
    have heq : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({m * x * m⁻¹} : Set G) =
        MulAut.conj m • (OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [Subgroup.smul_inf, hconjMσ, ← centralizer_conj_smul_eq]
    rw [heq, ne_eq, conj_smul_eq_bot_iff]
    exact hxC
  · -- `mxm⁻¹ ∈ U ⊔ M_σ` (normality of `U M_σ` in `M`).
    have hxsub : (⟨x, hxM⟩ : ↥M) ∈ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hxUMσ
    have hconj := hnorm.conj_mem _ hxsub ⟨m, hm⟩
    have : m * x * m⁻¹ ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
      have := Subgroup.mem_subgroupOf.mp hconj
      simpa using this
    exact this

/-- **The `G`-level product from a `subgroupOf`-complement inside `C`.**  If `A, B ≤ C` complement
each other in `C` (`IsComplement' (A.subgroupOf C) (B.subgroupOf C)`), then `C` is the pointwise
product `A · B` of the two subsets.  Used to write `C_G(y) = C_{Hᵢ}(y) · C_M(y)` from the Theorem
D(3) complement (`signalizer_centralizer_isComplement`). -/
theorem coe_eq_mul_of_isComplement' {C A B : Subgroup G} (hAC : A ≤ C) (hBC : B ≤ C)
    (h : Subgroup.IsComplement' (A.subgroupOf C) (B.subgroupOf C)) :
    (C : Set G) = (A : Set G) * (B : Set G) := by
  ext g
  rw [Set.mem_mul]
  constructor
  · intro hg
    obtain ⟨⟨s, t⟩, hst⟩ := h.2 ⟨g, hg⟩
    have hsA : ((s : ↥C) : G) ∈ A := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp s.2)
    have htB : ((t : ↥C) : G) ∈ B := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp t.2)
    refine ⟨((s : ↥C) : G), hsA, ((t : ↥C) : G), htB, ?_⟩
    have := congrArg (Subtype.val) hst
    simpa using this
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact SetLike.mem_coe.mpr (C.mul_mem (hAC ha) (hBC hb))

/-! ## Data attached to a neighbour maximal `N(x)` -/

/-- **The maximality, Type I/II classification, and Theorem D(4) complement of a neighbour maximal.**
If `Mi = N(x)` is the unique maximal over `C_G(x)` for some escaping `x ∈ D = escapingSharpSet M X`,
then `Mi` is maximal, of Peterfalvi Type I or II, and `M ∩ Mi` complements `M_{iσ}` in `Mi`
(BG Theorem D(4) plus Proposition 16.1). -/
theorem neighbour_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Mi : Subgroup G}
    (hMi : ∃ x ∈ escapingSharpSet M (ASet M U),
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {Mi}) :
    Mi ∈ maximalSubgroups G ∧ (IsTypeI Mi ∨ IsTypeII Mi) ∧
      Subgroup.IsComplement' ((M ⊓ Mi).subgroupOf Mi)
        ((OddOrder.BG.Ch3.S10.Msigma Mi).subgroupOf Mi) := by
  obtain ⟨x, ⟨hxA, hx1, hesc⟩, hMℳ⟩ := hMi
  have hxσ : x ∈ S14.sigmaSharp M :=
    mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU (Or.inl rfl) hxA hx1 hesc
  have hMimem : Mi ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
    rw [hMℳ]; rfl
  have hMimax : Mi ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hMimem).1
  obtain ⟨_, _, _, hD4⟩ := theoremD_msigma_conjugacy_and_centralizers hG hM
  obtain ⟨_R, _hR, N, hQN, _⟩ := hD4 x hxσ hesc
  obtain ⟨hNmem, _, _, _, hNtype, hNcompl, _⟩ := hQN
  have hNMi : N = Mi := by
    have h := hNmem; rw [hMℳ, Set.mem_singleton_iff] at h; exact h
  rw [hNMi] at hNtype hNcompl
  have htype : IsTypeI Mi ∨ IsTypeII Mi := by
    obtain ⟨hIiff, hIIiff, _⟩ := proposition_type_classification hG hMimax
    rcases hNtype with hF | hP2
    · exact Or.inl (hIiff.mpr hF)
    · exact Or.inr (hIIiff.mpr hP2)
  exact ⟨hMimax, htype, hNcompl⟩

/-! ## Clause (c): coprimality of `|Hᵢ|` and `|C_M(x)|` -/

/-- **In a Frobenius group `M = M_σ ⋊ E`, an element of `M` commuting with a nonidentity
`M_σ`-element lies in `M_σ`.**  `Isaacs Thm 6.4 (1)⇒(4)` (`centralizer_kernel_le`) applied to the
kernel `M_σ` (as `(M_σ).subgroupOf M ◁ ↥M`). -/
theorem mem_Msigma_of_commute_frobenius [Finite G] {M : Subgroup G} {A : Subgroup ↥M}
    (h_frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) A)
    {a z : G} (haM : a ∈ M) (hzMσ : z ∈ OddOrder.BG.Ch3.S10.Msigma M) (hz1 : z ≠ 1)
    (hcomm : z * a = a * z) : a ∈ OddOrder.BG.Ch3.S10.Msigma M := by
  have hzM : z ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hzMσ
  have hzsub : (⟨z, hzM⟩ : ↥M) ∈ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hzMσ
  have hz1' : (⟨z, hzM⟩ : ↥M) ≠ 1 := fun h => hz1 (by simpa using congrArg Subtype.val h)
  have hker := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le h_frob ⟨z, hzM⟩ hzsub hz1'
  have hacomm : (⟨a, haM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨z, hzM⟩ : ↥M)} : Set ↥M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hcomm.symm
  exact Subgroup.mem_subgroupOf.mp (hker hacomm)

/-- **BG Theorem II (Tii)(c)** (mmd:4571, proof at mmd:4573): `(|Hᵢ|, |C_M(x)|) = 1` for every
`x ∈ A(M)#`, where `Hᵢ = M_{iσ}` and `Mᵢ = N(x_i)` is a neighbour maximal.

If a prime `q` divides both `|M_{iσ}|` and `|C_M(x)| = |M ∩ C_G(x)|`, then `q ∈ σ(Mᵢ) ∩ π(M)`;
Lemma 14.13(a) (`non_disjoint_signalizer_frobenius`) makes `M` a Frobenius group with kernel `M_σ`.
Then `A(M) ⊆ M_σ` and `C_M(x) ⊆ M_σ` (`mem_Msigma_of_commute_frobenius`), so `q ∈ σ(M)`; hence
`σ(Mᵢ) ∩ σ(M) ≠ ∅` forces `Mᵢ` conjugate to `M` (Theorem E(2)).  But `Mᵢ = N(x_i)` has a
`τ₂(Mᵢ)`-prime `p ∈ π(⟨x_i⟩)` (Theorem 14.4(c)) which lies in `σ(M) = σ(Mᵢ)` — impossible, as
`τ₂(Mᵢ) ⊆ σ(Mᵢ)′`. -/
theorem coprime_centralizer_of_neighbour [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Mi : Subgroup G} (hMimax : Mi ∈ maximalSubgroups G)
    (hMinb : ∃ x ∈ escapingSharpSet M (ASet M U),
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {Mi})
    (x : G) (hxA : x ∈ ASet M U) (hx1 : x ≠ 1) :
    Nat.Coprime (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma Mi))
      (Nat.card ↥(M ⊓ Subgroup.centralizer ({x} : Set G))) := by
  by_contra hcop
  rw [Nat.Prime.not_coprime_iff_dvd] at hcop
  obtain ⟨q, hq, hqi, hqCM⟩ := hcop
  have hqσMi : q ∈ OddOrder.BG.Ch3.S10.sigma Mi :=
    (primeFactors_Msigma_eq_sigma hG hMimax q).mp
      (Nat.mem_primeFactors.mpr ⟨hq, hqi, Nat.card_pos.ne'⟩)
  -- the seed `x_i` of `Mi`
  obtain ⟨xi, ⟨hxiA, hxi1, hxiesc⟩, hMℳi⟩ := hMinb
  have hxiσ : xi ∈ S14.sigmaSharp M :=
    mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU (Or.inl rfl) hxiA hxi1 hxiesc
  have hgtxi : 1 < (S14.maximalSigmaSubgroupsOfElement xi).ncard := by
    by_contra h; push_neg at h
    exact hxiesc (centralizer_le_of_maximalSigma_le_one hG hM hxiσ.1 hxi1 h)
  -- `FT_signalizerBase x_i = Mi`
  have hbr : 1 < (S14.maximalSigmaSubgroupsOfElement xi).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({xi} : Set G))).Nonempty :=
    ⟨hgtxi, ⟨Mi, by rw [hMℳi]; rfl⟩⟩
  have huniqMi : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({xi} : Set G)), L = Mi :=
    fun L hL => by rw [hMℳi, Set.mem_singleton_iff] at hL; exact hL
  have hbase : FT_signalizerBase xi = Mi := by
    rw [show FT_signalizerBase xi = hbr.2.choose from dif_pos hbr]
    exact huniqMi _ hbr.2.choose_spec
  -- `q ∈ π(M)` and Lemma 14.13(a)
  have hqπM : q ∈ S14.piSet M :=
    Nat.mem_primeFactors.mpr ⟨hq, hqCM.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩
  have hnd : (OddOrder.BG.Ch3.S10.sigma (FT_signalizerBase xi) ∩ S14.piSet M).Nonempty :=
    ⟨q, by rw [hbase]; exact hqσMi, hqπM⟩
  obtain ⟨_hFM, _ht2M, U', _hUcompl, hfrob⟩ :=
    non_disjoint_signalizer_frobenius hG hM hxiσ hgtxi hnd
  -- the `τ₂(Mi)`-prime `p` from the signalizer structure at `x_i`
  obtain ⟨N, ⟨hNmax, hNC, _, _, hNt2, _, _⟩, -⟩ :=
    signalizer_structure_of_mem_sigmaSharp hG hM hxiσ hgtxi
  have hNMi : N = Mi := by
    have h : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({xi} : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hNmax, hNC⟩
    rw [hMℳi, Set.mem_singleton_iff] at h; exact h
  have hp_prime : (orderOf xi).minFac.Prime :=
    Nat.minFac_prime (fun h => hxi1 (orderOf_eq_one_iff.mp h))
  set p : ℕ := (orderOf xi).minFac with hpdef
  have hpord : p ∈ (orderOf xi).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, Nat.minFac_dvd _,
      by rw [← Nat.card_zpowers xi]; exact Nat.card_pos.ne'⟩
  have hppi : p ∈ S14.piSet (Subgroup.closure ({xi} : Set G)) := by
    change p ∈ (Nat.card ↥(Subgroup.closure ({xi} : Set G))).primeFactors
    rwa [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hpt2Mi : p ∈ tau2 Mi := hNMi ▸ hNt2 p hppi
  have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
    S14.isPiElement_sigma_of_mem_Msigma hxiσ.1 p hpord
  -- `x ∈ M_σ` and `C_M(x) ⊆ M_σ` (Frobenius), so `q ∈ σ(M)`
  obtain ⟨⟨hxM, hxCne⟩, _⟩ := hxA
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hxCne
  obtain ⟨⟨z, hz⟩, hz1⟩ := hxCne
  obtain ⟨hzMσ, hzC⟩ := Subgroup.mem_inf.mp hz
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    mem_Msigma_of_commute_frobenius hfrob hxM hzMσ hz1' hzx
  have hMCle : M ⊓ Subgroup.centralizer ({x} : Set G) ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    intro w hw
    obtain ⟨hwM, hwC⟩ := Subgroup.mem_inf.mp hw
    have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
    exact mem_Msigma_of_commute_frobenius hfrob hwM hxMσ hx1 hwx.symm
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    (primeFactors_Msigma_eq_sigma hG hM q).mp
      (Nat.mem_primeFactors.mpr
        ⟨hq, hqCM.trans (Subgroup.card_dvd_of_le hMCle), Nat.card_pos.ne'⟩)
  -- `Mi` conjugate to `M`, hence `σ(Mi) = σ(M)`
  have hconj : ∃ g : G, MulAut.conj g • Mi = M := by
    by_contra hnc
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMimax hM hnc) hqσMi hqσM
  obtain ⟨g, hg⟩ := hconj
  have hσeq : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma Mi := by
    have := S14.sigma_conj_smul_eq g Mi; rwa [hg] at this
  exact ((OddOrder.BG.Ch3.S12.mem_tau2_iff Mi p).mp hpt2Mi).1 (hσeq ▸ hpσM)

/-! ## Clause (Tiii): a Type-II supporting subgroup forces `M` Frobenius of Type I -/

/-- **BG Theorem II (Tiii)** (mmd:4573): if a supporting maximal `Mᵢ = N(xᵢ)` (a neighbour of an
escaping `xᵢ ∈ D`) is of Type II, then `M` is a Frobenius group of Type I with cyclic complement
and non-`TI` Fitting subgroup (`FrobeniusTypeIWithNonTIFitting M`).

`Mᵢ` Type II `= IsTypeP2 Mᵢ`, and `Mᵢ = N(xᵢ)` is the Theorem D(4) signalizer neighbour of `xᵢ`, so
Theorem D(4)'s `IsTypeP2 N → IsTypeF M ∧ ¬ FittingIsTI M ∧ (M = M_σ ⋊ E Frobenius, E cyclic)` clause
applies directly, and `IsTypeF M ⇒ IsTypeI M` (Proposition 16.1) with `M_F = M_σ` (Type-I). -/
theorem frobeniusTypeI_of_neighbour_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Mi : Subgroup G} (hMitype2 : IsTypeII Mi)
    (hMinb : ∃ x ∈ escapingSharpSet M (ASet M U),
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {Mi}) :
    FrobeniusTypeIWithNonTIFitting M := by
  obtain ⟨x, ⟨hxA, hx1, hesc⟩, hMℳ⟩ := hMinb
  have hxσ : x ∈ S14.sigmaSharp M :=
    mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU (Or.inl rfl) hxA hx1 hesc
  have hMimem : Mi ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
    rw [hMℳ]; rfl
  have hMimax : Mi ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hMimem).1
  obtain ⟨_, _, _, hD4⟩ := theoremD_msigma_conjugacy_and_centralizers hG hM
  obtain ⟨_R, _hR, N, hQN, _⟩ := hD4 x hxσ hesc
  obtain ⟨hNmem, _, _, _, _, _, hP2imp⟩ := hQN
  have hNMi : N = Mi := by
    have h := hNmem; rw [hMℳ, Set.mem_singleton_iff] at h; exact h
  have hMiP2 : S14.IsTypeP2 Mi := (proposition_type_classification hG hMimax).2.1.mp hMitype2
  have hNP2 : S14.IsTypeP2 N := by rw [hNMi]; exact hMiP2
  obtain ⟨hFM, hnotTI, E, _hEM, hEcyc, hEcompl, hEfrob⟩ := hP2imp hNP2
  have hMFeq : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG hM (Or.inl hFM)
  refine ⟨(proposition_type_classification hG hM).1.mpr hFM, ⟨E, hEcyc, ?_, ?_⟩, hnotTI⟩
  · rw [hMFeq]; exact hEcompl
  · rw [hMFeq]; exact hEfrob

/-! ## Theorem II (Tii): the system exists -/

/-- **BG Theorem II (Tii)** (mmd:4571): when the escaping set `D = escapingSharpSet M (A(M))` is
nonempty, `A(M) = ASet M U` admits a system of supporting subgroups.

The family `M₁,…,Mₙ` is a set of `G`-conjugacy representatives of the neighbour maximals
`𝓐 = {N(x) : x ∈ D}` (Theorem D(4)).  This theorem assembles the clauses `maximal`, `typeIorII`,
`(a) coprime_orders`, `(b) factorization`/`inf_M_supporting`, and `(e) escape_centralizer` from
Theorem D(3)/(4), Theorem E(2) (`sigma_disjoint_of_nonconjugate`), and Lemma 14.13(b)
(`signalizer_neighbour_conjugator_in_M`).  The clauses `(c) coprime_centralizer` (`hc`) and
`(d) a0_ti` (`hd`) — whose book proofs are Lemma 14.13(a) and the `A₀(Mᵢ)` `TI` structure —
enter as hypotheses (see `TheoremIIPackaging` docstring). -/
theorem exists_systemOfSupportingSubgroups [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (_hne : escapingSharpSet M (ASet M U) ≠ ∅)
    (hc : ∀ Mi ∈ maximalSubgroups G, (IsTypeI Mi ∨ IsTypeII Mi) →
      (∃ x ∈ escapingSharpSet M (ASet M U),
        maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {Mi}) →
      ∀ x ∈ ASet M U, x ≠ 1 →
        Nat.Coprime (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma Mi))
          (Nat.card ↥(M ⊓ Subgroup.centralizer ({x} : Set G))))
    (hd : ∀ Mi ∈ maximalSubgroups G, (IsTypeI Mi ∨ IsTypeII Mi) →
      (∃ x ∈ escapingSharpSet M (ASet M U),
        maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {Mi}) →
      ∃ Ki : Subgroup G, Ch03.IsHallSubgroup (S14.kappa Mi) (Ki.subgroupOf Mi) ∧
        (A0Set Mi Ki \ (OddOrder.BG.Ch3.S10.Msigma Mi : Set G)).Nonempty ∧
        IsTISubset (A0Set Mi Ki \ (OddOrder.BG.Ch3.S10.Msigma Mi : Set G)) Mi) :
    ∃ sys : SystemOfSupportingSubgroups M (ASet M U),
      ((∃ i, IsTypeII (sys.Mfam i)) → FrobeniusTypeIWithNonTIFitting M) := by
  classical
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  -- Theorem A(3): `U ⊔ M_σ ◁ M`.
  have hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hUM (OddOrder.BG.Ch3.S10.Msigma_le M))).mpr
      (theoremA_ungated_conjuncts hG hM hKM hUM hK rfl hU).2.2.1
  -- The neighbour set `𝓐` and its conjugacy transversal.
  let 𝓐 : Set (Subgroup G) :=
    {N | ∃ x ∈ escapingSharpSet M (ASet M U),
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N}}
  obtain ⟨reps, hrepsA, hrepsInj, hrepsCover⟩ := exists_conjugacy_reps 𝓐
  -- Enumerate `reps` as `Fin n → Subgroup G`.
  let n := Nat.card ↥reps
  let e : Fin n ≃ ↥reps := (Finite.equivFin ↥reps).symm
  set Mfam : Fin n → Subgroup G := fun i => ((e i : ↥reps) : Subgroup G) with hMfamdef
  have hMfam_reps : ∀ i, Mfam i ∈ reps := fun i => (e i).2
  have hMfam_neighbour : ∀ i, ∃ x ∈ escapingSharpSet M (ASet M U),
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {Mfam i} :=
    fun i => hrepsA (hMfam_reps i)
  have hMfam_data : ∀ i, Mfam i ∈ maximalSubgroups G ∧
      (IsTypeI (Mfam i) ∨ IsTypeII (Mfam i)) ∧
      Subgroup.IsComplement' ((M ⊓ Mfam i).subgroupOf (Mfam i))
        ((OddOrder.BG.Ch3.S10.Msigma (Mfam i)).subgroupOf (Mfam i)) :=
    fun i => neighbour_data hG hM hKM hUM hK hU (hMfam_neighbour i)
  have hMfam_hall_eq : ∀ i, maxNilpotentNormalHall (Mfam i) = OddOrder.BG.Ch3.S10.Msigma (Mfam i) :=
    fun i => (proposition_type_classification hG (hMfam_data i).1).2.2.2.2.2.mpr
      ((hMfam_data i).2.1.imp_right Or.inl)
  refine ⟨{
    n := n
    Mfam := Mfam
    maximal := fun i => (hMfam_data i).1
    typeIorII := fun i => (hMfam_data i).2.1
    coprime_orders := ?_
    factorization := ?_
    inf_M_supporting := ?_
    coprime_centralizer := ?_
    a0_ti := ?_
    escape_centralizer := ?_ }, ?_⟩
  · -- **(a)** `(|Hᵢ|, |Hⱼ|) = 1`: distinct reps are non-conjugate, so `σ(Mᵢ) ∩ σ(Mⱼ) = ∅`.
    intro i j hij
    rw [hMfam_hall_eq i, hMfam_hall_eq j]
    have hne : Mfam i ≠ Mfam j := by
      intro h; exact hij (e.injective (Subtype.ext h))
    have hnc : ¬ ∃ g : G, MulAut.conj g • Mfam i = Mfam j := fun hconj =>
      hne (hrepsInj (Mfam i) (hMfam_reps i) (Mfam j) (hMfam_reps j) hconj)
    have hdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG (hMfam_data i).1
      (hMfam_data j).1 hnc
    by_contra hcop
    rw [Nat.Prime.not_coprime_iff_dvd] at hcop
    obtain ⟨p, hp, hpi, hpj⟩ := hcop
    have hpσi : p ∈ OddOrder.BG.Ch3.S10.sigma (Mfam i) :=
      (primeFactors_Msigma_eq_sigma hG (hMfam_data i).1 p).mp
        (Nat.mem_primeFactors.mpr ⟨hp, hpi, Nat.card_pos.ne'⟩)
    have hpσj : p ∈ OddOrder.BG.Ch3.S10.sigma (Mfam j) :=
      (primeFactors_Msigma_eq_sigma hG (hMfam_data j).1 p).mp
        (Nat.mem_primeFactors.mpr ⟨hp, hpj, Nat.card_pos.ne'⟩)
    exact Set.disjoint_left.mp hdisj hpσi hpσj
  · -- **(b) factorization** `Mᵢ = Hᵢ (M ∩ Mᵢ)`: the Theorem D(4) complement (symmetrised).
    intro i
    rw [hMfam_hall_eq i]
    exact (hMfam_data i).2.2.symm
  · -- **(b) disjointness** `M ∩ Hᵢ = 1`: the disjoint part of the same complement.
    intro i
    rw [hMfam_hall_eq i]
    have hle : (M ⊓ Mfam i) ⊓ OddOrder.BG.Ch3.S10.Msigma (Mfam i) ≤ Mfam i :=
      inf_le_left.trans inf_le_right
    have hsub : ((M ⊓ Mfam i) ⊓ OddOrder.BG.Ch3.S10.Msigma (Mfam i)).subgroupOf (Mfam i) = ⊥ := by
      change ((M ⊓ Mfam i) ⊓ OddOrder.BG.Ch3.S10.Msigma (Mfam i)).comap (Mfam i).subtype = ⊥
      rw [Subgroup.comap_inf]
      exact (hMfam_data i).2.2.disjoint.eq_bot
    have h1 : (M ⊓ Mfam i) ⊓ OddOrder.BG.Ch3.S10.Msigma (Mfam i) = ⊥ := by
      have hmap := congrArg (Subgroup.map (Mfam i).subtype) hsub
      rwa [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hmap
    have hMσMi : OddOrder.BG.Ch3.S10.Msigma (Mfam i) ≤ Mfam i := OddOrder.BG.Ch3.S10.Msigma_le _
    calc M ⊓ OddOrder.BG.Ch3.S10.Msigma (Mfam i)
        = M ⊓ (Mfam i ⊓ OddOrder.BG.Ch3.S10.Msigma (Mfam i)) := by rw [inf_eq_right.mpr hMσMi]
      _ = (M ⊓ Mfam i) ⊓ OddOrder.BG.Ch3.S10.Msigma (Mfam i) := by rw [inf_assoc]
      _ = ⊥ := h1
  · -- **(c)** `(|Hᵢ|, |C_M(x)|) = 1`: the hypothesis `hc`.
    intro i x hxA hx1
    rw [hMfam_hall_eq i]
    exact hc (Mfam i) (hMfam_data i).1 (hMfam_data i).2.1 (hMfam_neighbour i) x hxA hx1
  · -- **(d)** `A₀(Mᵢ) − Hᵢ` nonempty `TI`: the hypothesis `hd`.
    intro i
    obtain ⟨Ki, hKihall, hKine, hKiti⟩ :=
      hd (Mfam i) (hMfam_data i).1 (hMfam_data i).2.1 (hMfam_neighbour i)
    rw [hMfam_hall_eq i]
    exact ⟨Ki, hKihall, hKine, hKiti⟩
  · -- **(e)** the escaping-centralizer decomposition, via Lemma 14.13(b).
    intro x hxD
    obtain ⟨hxA, hx1, hesc⟩ := hxD
    have hxσ : x ∈ S14.sigmaSharp M :=
      mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU (Or.inl rfl) hxA hx1 hesc
    have hgtx : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard := by
      by_contra h; push_neg at h
      exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxσ.1 hx1 h)
    obtain ⟨Nx, hNx⟩ :=
      maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape hG hM hxσ hesc
    have hNxA : Nx ∈ 𝓐 := ⟨x, ⟨hxA, hx1, hesc⟩, hNx⟩
    obtain ⟨Mi', hMi'rep, g, hg0⟩ := hrepsCover Nx hNxA
    -- the index `i` with `Mfam i = Mi'`
    let i : Fin n := e.symm ⟨Mi', hMi'rep⟩
    have hi : Mfam i = Mi' := by
      change ((e (e.symm ⟨Mi', hMi'rep⟩) : ↥reps) : Subgroup G) = Mi'
      rw [Equiv.apply_symm_apply]
    -- the rep's own seed, for Lemma 14.13(b)
    obtain ⟨xi, hxiD, hMℳi⟩ := hMfam_neighbour i
    obtain ⟨hxiA, hxi1, hxiesc⟩ := hxiD
    have hxiσ : xi ∈ S14.sigmaSharp M :=
      mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU (Or.inl rfl) hxiA hxi1 hxiesc
    have hgtxi : 1 < (S14.maximalSigmaSubgroupsOfElement xi).ncard := by
      by_contra h; push_neg at h
      exact hxiesc (centralizer_le_of_maximalSigma_le_one hG hM hxiσ.1 hxi1 h)
    -- Lemma 14.13(b): move the conjugator `Nx → Mfam i` into `M`.
    have hgeq : MulAut.conj g • Nx = Mfam i := hg0.trans hi.symm
    obtain ⟨m, hmM, hmconj⟩ :=
      signalizer_neighbour_conjugator_in_M hG hM hxiσ hgtxi hMℳi hxσ hesc hNx hgeq
    -- `y = m x m⁻¹` and its centralizer.
    have hCy_eq : Subgroup.centralizer ({m * x * m⁻¹} : Set G) =
        MulAut.conj m • Subgroup.centralizer ({x} : Set G) := centralizer_conj_smul_eq m x
    have hCxNx : Subgroup.centralizer ({x} : Set G) ≤ Nx :=
      (mem_maximalSubgroupsContaining.mp (by rw [hNx]; rfl)).2
    have hCyMi : Subgroup.centralizer ({m * x * m⁻¹} : Set G) ≤ Mfam i := by
      rw [hCy_eq, ← hmconj]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCxNx
    have hyA : m * x * m⁻¹ ∈ ASet M U := aSet_conj_closed hnorm hUM hmM hxA
    have hyM : m * x * m⁻¹ ∈ M := hyA.1.1
    have hy1 : m * x * m⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have e0 : m⁻¹ * (m * x * m⁻¹) * m = x := by group
      rw [h] at e0; simpa using e0.symm
    have hyesc : ¬ Subgroup.centralizer ({m * x * m⁻¹} : Set G) ≤ M := by
      intro hle
      rw [hCy_eq] at hle
      have hMfix : MulAut.conj m • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hmM)
      rw [← hMfix] at hle
      exact hesc (Subgroup.pointwise_smul_le_pointwise_smul_iff.mp hle)
    -- the Theorem D(3) centralizer decomposition at `y`.
    have hdecomp : (Subgroup.centralizer ({m * x * m⁻¹} : Set G) : Set G) =
        ((OddOrder.BG.Ch3.S10.Msigma (Mfam i) : Set G) ∩
            (Subgroup.centralizer ({m * x * m⁻¹} : Set G) : Set G)) *
          ((M : Set G) ∩ (Subgroup.centralizer ({m * x * m⁻¹} : Set G) : Set G)) := by
      have hcompl := (signalizer_centralizer_isComplement (hMfam_data i).2.2.symm hCyMi hyM).symm
      have h := coe_eq_mul_of_isComplement'
        (C := Subgroup.centralizer ({m * x * m⁻¹} : Set G))
        (A := OddOrder.BG.Ch3.S10.Msigma (Mfam i) ⊓ Subgroup.centralizer ({m * x * m⁻¹} : Set G))
        (B := M ⊓ Subgroup.centralizer ({m * x * m⁻¹} : Set G))
        inf_le_right inf_le_right hcompl
      rw [Subgroup.coe_inf, Subgroup.coe_inf] at h
      exact h
    refine ⟨m * x * m⁻¹, ⟨hyA, hy1, hyesc⟩, ⟨m, rfl⟩, i, hCyMi, ?_⟩
    rw [hMfam_hall_eq i]
    exact hdecomp
  · -- **(Tiii)** a Type-II supporting member forces `M` Frobenius of Type I with non-`TI` Fitting.
    rintro ⟨i, hII⟩
    exact frobeniusTypeI_of_neighbour_typeII hG hM hKM hUM hK hU hII (hMfam_neighbour i)

/-! ## Theorem II: `A(M)` is tamely imbedded -/

/-- **BG Theorem II** (mmd:4571) + **Remark** (mmd:4575): for an arbitrary maximal subgroup `M` of a
minimal simple group `G` of odd order, `A(M) = ASet M U` is a *tamely imbedded subset* of `G`
(`TamelyImbedded M (ASet M U)`).

* **(Ti)** — `G`-conjugate elements of `A(M)` are `M`-conjugate — is the conjunct-1 output of
  `theoremII_tame_embedding` (BG Theorem D(1) + Theorem B(5)/C(9)).
* **(Tii)+(Tiii)** — a nonempty escaping set yields a `SystemOfSupportingSubgroups` whose Type-II
  members force `M` Frobenius of Type I with non-`TI` Fitting — is
  `exists_systemOfSupportingSubgroups` (clause (Tiii) discharged internally via Theorem D(4),
  `frobeniusTypeI_of_neighbour_typeII`).

The clause `(c)` is discharged internally (`coprime_centralizer_of_neighbour`, via Lemma 14.13(a)).
The sole remaining §16 residual is the hypothesis `hd` (clause (d), the `A₀(Mᵢ)` `TI` structure of
Theorem B(5)/C(9) at `Mᵢ`; provable for Type-I `Mᵢ` but the Type-II "`A₀(Mᵢ)` is `TI`" theorem is not
yet in the repository). -/
theorem theoremII_tamelyImbedded [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hd : ∀ Mi ∈ maximalSubgroups G, (IsTypeI Mi ∨ IsTypeII Mi) →
      (∃ x ∈ escapingSharpSet M (ASet M U),
        maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {Mi}) →
      ∃ Ki : Subgroup G, Ch03.IsHallSubgroup (S14.kappa Mi) (Ki.subgroupOf Mi) ∧
        (A0Set Mi Ki \ (OddOrder.BG.Ch3.S10.Msigma Mi : Set G)).Nonempty ∧
        IsTISubset (A0Set Mi Ki \ (OddOrder.BG.Ch3.S10.Msigma Mi : Set G)) Mi) :
    TamelyImbedded M (ASet M U) := by
  refine ⟨?_, ?_⟩
  · -- (Ti)
    exact (theoremII_tame_embedding hG hM hKM hUM hK hU (Or.inl rfl)).1
  · -- (Tii)+(Tiii)
    refine fun hne => exists_systemOfSupportingSubgroups hG hM hKM hUM hK hU hne ?_ hd
    exact fun Mi hMimax _htype hnb x hxA hx1 =>
      coprime_centralizer_of_neighbour hG hM hKM hUM hK hU hMimax hnb x hxA hx1

end OddOrder.BG.Ch4.S16
