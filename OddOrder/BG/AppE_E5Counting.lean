/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_CorollaryE5

/-!
# BG Corollary E.5: final assembly and the `(E.33)`/`(E.34)` counting

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 164–166.

This leaf finishes Corollary E.5 (issue 3028 WP5) on top of the staged material of
`OddOrder/BG/AppE_CorollaryE5.lean`:

* **Assembly glue** — deriving, from E.5's raw hypothesis block, every input of the
  proved `(ii) ∧ hdc ⟹ (i)` engine `e5_derived_index_eq_of_ii_hdc`: the suitable
  complement `E ⊇ K₁` (15.9(c)), `M_σ` nilpotency (Prop 16.1 taxonomy, type `F`),
  `N_G(⟨x⟩) ≤ N` (the `ℳ(C_G(x)) = {N}` singleton), the non-cyclicity of
  `R = C_{O_p(M)}(x)` (`p ∈ τ₂(N)`, rank transfer along the Sylow `R` of `N`), and the
  nonabelian Sylow `p`-subgroup demanded by the Theorem 12.7 canonical-line machinery.
* **The counting** (BG p. 166) — with `(i)` in hand, a maximal subgroup `N*` neither of
  type I nor of type II would be conjugate to the type-`P` partner of `N`
  (Theorem 14.7(g)); the four disjoint conjugacy-saturation families
  `𝒞_G(M̃), 𝒞_G(Ñ*), 𝒞_G(Ñ), 𝒞_G(Ẑ)` then measure more than `|G|`
  (`(E.33)` = Lemma 14.5(c), `(E.34)` = the `Ẑ` TI-count), a contradiction.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S16
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- **`M' = M_σ` under a cyclic `σ`-complement** (BG p. 165, *"Since `M` is a Frobenius
group…"*, implicit): if the maximal `M` splits as `M = M_σ ⋊ E` with `E` cyclic, then the
quotient `M/M_σ` is a surjective image of `E`, hence cyclic, hence abelian — so
`M' ≤ M_σ`; the reverse inclusion is BG `M_σ ≤ M'` (`Msigma_le_derived`).  Both halves
of E.5's alternative use this to convert `|M/M'|` into `[M : M_σ] = |E|`. -/
theorem derivedInG_eq_Msigma_of_cyclic_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hEM : E ≤ M) (hEcyc : IsCyclic ↥E)
    (hEcompl : Subgroup.IsComplement'
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M)) :
    derivedInG M = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  set Mσ' : Subgroup ↥M := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M with hMσ'def
  haveI hMσnorm : Mσ'.Normal := by
    rw [hMσ'def, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]
    infer_instance
  haveI : IsCyclic ↥(E.subgroupOf M) := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hEM).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hEM).symm.surjective
  -- The quotient `M/M_σ` is a surjective image of the cyclic complement.
  haveI : IsCyclic (↥M ⧸ Mσ') := by
    refine isCyclic_of_surjective
      ((QuotientGroup.mk' Mσ').comp (E.subgroupOf M).subtype) (fun q => ?_)
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective Mσ' q
    have hsuptop : Mσ' ⊔ E.subgroupOf M = ⊤ := hEcompl.sup_eq_top
    obtain ⟨s, hs, e, he, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hsuptop ▸ Subgroup.mem_top m)
    refine ⟨⟨e, he⟩, ?_⟩
    have hker : (QuotientGroup.mk' Mσ') s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
    have h1 : (QuotientGroup.mk' Mσ') m = (QuotientGroup.mk' Mσ') e := by
      rw [← hprod, map_mul, hker, one_mul]
    exact h1.symm
  -- Cyclic quotient ⟹ abelian ⟹ `[M, M] ≤ M_σ`.
  letI : CommGroup (↥M ⧸ Mσ') := IsCyclic.commGroup
  have hcomm : _root_.commutator ↥M ≤ Mσ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h2 := map_commutatorElement (QuotientGroup.mk' Mσ') a b
    have h3 : (QuotientGroup.mk' Mσ') ⁅a, b⁆ = 1 := by
      rw [h2]
      exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
    exact (QuotientGroup.eq_one_iff _).mp h3
  refine le_antisymm ?_ (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)
  calc derivedInG M = (_root_.commutator ↥M).map M.subtype := rfl
    _ ≤ Mσ'.map M.subtype := Subgroup.map_mono hcomm
    _ = OddOrder.BG.Ch3.S10.Msigma M :=
        Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le M)

/-- **BG's *"By (ii), `O_p(M)` is not abelian"*** (p. 165), Sylow form: under E.5's (ii)
the Sylow `p`-subgroup `O_p(M)` of `G` is nonabelian — were it abelian, `S = Ω₁(O_p(M))`
would be abelian, and any subgroup of index `p` (which exists: `x ∈ S ≠ 1`) would be a
normal abelian subgroup of index `p`, violating (ii).  This supplies the
`∃ Sylow p G` nonabelian input of the Theorem 12.7 canonical-line machinery. -/
theorem e5_exists_nonabelian_sylow_of_ii [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {x : G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M)
    (hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M))
    (hxOp : x ∈ opiCoreInG {p} M) (hord : orderOf x = p)
    (hii : ¬ ∃ A : Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1),
      A.Normal ∧ IsMulCommutative ↥A ∧ A.index = p) :
    ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSeq⟩ := e5_exists_sylow_eq_opiCore hG hM hp hpσ hMσnil
  refine ⟨S, fun habel => ?_⟩
  rw [hSeq] at habel
  -- `O_p(M)` abelian ⟹ `Ω₁(O_p(M))` abelian, and (ii) fails.
  apply hii
  set Ω : Subgroup ↥(opiCoreInG {p} M) := Omega ↥(opiCoreInG {p} M) p 1 with hΩdef
  haveI hΩcomm : IsMulCommutative ↥Ω :=
    ⟨⟨fun a b => Subtype.ext (habel.is_comm.comm
      (a : ↥(opiCoreInG {p} M)) (b : ↥(opiCoreInG {p} M)))⟩⟩
  have hpg : IsPGroup p ↥Ω := (isPGroup_opiCoreInG_singleton M).to_subgroup _
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  -- `x ∈ Ω`, so `m ≥ 1`.
  have hxΩ : (⟨x, hxOp⟩ : ↥(opiCoreInG {p} M)) ∈ Ω := by
    refine Omega.mem_of_pow_eq_one ?_
    have hxp : x ^ p = 1 := hord ▸ pow_orderOf_eq_one x
    exact Subtype.ext (by simpa using hxp)
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero, Subgroup.card_eq_one] at hm
    have h1 : (⟨x, hxOp⟩ : ↥(opiCoreInG {p} M)) = 1 := Subgroup.mem_bot.mp (hm ▸ hxΩ)
    have h2 : x = 1 := by simpa using congrArg Subtype.val h1
    rw [h2, orderOf_one] at hord
    exact hp.one_lt.ne' hord.symm
  -- A subgroup of order `p^(m-1)`: normal (ambient abelian), abelian, of index `p`.
  obtain ⟨A, hA⟩ := Sylow.exists_subgroup_card_pow_prime p
    (n := m - 1) (by rw [hm]; exact pow_dvd_pow p (by omega))
  have hidx : A.index = p := by
    have hmul := A.card_mul_index
    rw [hA, hm] at hmul
    have hpow : p ^ m = p ^ (m - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at hmul
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) hmul
  refine ⟨A, Subgroup.normal_of_isMulCommutative A,
    ⟨⟨fun a b => Subtype.ext (hΩcomm.is_comm.comm (a : ↥Ω) (b : ↥Ω))⟩⟩, hidx⟩

/-- **`O_p(M)` absorbs every `p`-subgroup of `M`** (for `p ∈ σ(M)` with `M_σ` nilpotent):
`O_p(M)` is then the unique Sylow `p`-subgroup of `M` (it carries the full `p`-part of
`|G|`, hence of `|M|` — `e5_opiCore_sylow_card`), and it is normal in `M`, so every
`p`-subgroup lands inside it. -/
theorem le_opiCoreInG_singleton_of_isPGroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q : Subgroup G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M)
    (hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M))
    (hQM : Q ≤ M) (hQpg : IsPGroup p ↥Q) :
    Q ≤ opiCoreInG {p} M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnorm : ((opiCoreInG {p} M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (opiCoreInG_le _ _)).mpr
      (OddOrder.GroupTheory.le_normalizer_opiCoreInG {p} M)
  refine le_of_isPGroup_of_not_dvd_relIndex hp hQM (opiCoreInG_le _ _) hnorm hQpg ?_
  -- `p ∤ [M : O_p(M)]`: `|O_p(M)|` is already the full `p`-part of `|G| ⊇ |M|`.
  intro hdvd
  have hOpcard : Nat.card ↥(opiCoreInG {p} M) = p ^ (Nat.card G).factorization p :=
    e5_opiCore_sylow_card hG hM hp hpσ hMσnil
  have hmul : Nat.card ↥((opiCoreInG {p} M).subgroupOf M)
      * ((opiCoreInG {p} M).subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (opiCoreInG_le {p} M)).toEquiv,
    hOpcard] at hmul
  obtain ⟨t, ht⟩ := hdvd
  have hdvdG : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G := by
    refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card M)
    rw [← hmul, Subgroup.relIndex] at *
    exact ⟨t, by rw [ht]; ring⟩
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hdvdG
  omega

/-- **BG's *"Since `p ∈ τ₂(N)`, `r(R) = 2`"*** (p. 165, printed `τ₂(M)`, read `τ₂(N)`),
in the non-cyclicity form the `(E.31)` machinery consumes: `R = O_p(M) ⊓ N` is not
cyclic.  Theorem 12.7 supplies a rank-2 elementary abelian `A ≤ M ∩ N`; `A` is a
`p`-subgroup of `M`, hence lands in the unique Sylow `O_p(M)`
(`le_opiCoreInG_singleton_of_isPGroup`), so `A ≤ R` — and a cyclic `R` cannot contain
the noncyclic `A`. -/
theorem e5_R_noncyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N Emn E₁ E₂ E₃ : Subgroup G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hsetup : SubgroupESetup N Emn E₁ E₂ E₃)
    (hEmn : Emn = M ⊓ N) (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M) (hp2 : p ∈ tau2 N)
    (hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M)) :
    ¬ IsCyclic ↥(opiCoreInG {p} M ⊓ N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetup hp2
  obtain ⟨hAelem, hAcard⟩ := mem_elemAbelianOfRank.mp hA
  have hAMN : A ≤ M ⊓ N := hEmn ▸ hAE
  have hApg : IsPGroup p ↥A := IsPGroup.of_card hAcard
  have hAOp : A ≤ opiCoreInG {p} M :=
    le_opiCoreInG_singleton_of_isPGroup hG hM hp hpσ hMσnil
      (hAMN.trans inf_le_left) hApg
  have hAR : A ≤ opiCoreInG {p} M ⊓ N := le_inf hAOp (hAMN.trans inf_le_right)
  intro hRcyc
  -- A cyclic `R` would make the rank-2 elementary abelian `A` cyclic.
  haveI := hRcyc
  haveI : IsCyclic ↥(A.subgroupOf (opiCoreInG {p} M ⊓ N)) := inferInstance
  have hAcyc : IsCyclic ↥A := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hAR).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hAR).surjective
  exact OddOrder.GroupTheory.IsElementaryAbelian.not_isCyclic_of_card_prime_sq
    hp hAelem hAcard hAcyc

/-- **`N_G(⟨x⟩) ≤ N`** (BG p. 165, implicit in *"`E = K₁`"*): the centralizer
`C_G(x) = C_G(⟨x⟩)` sits inside `N_G(⟨x⟩)`, which is proper (`⟨x⟩` is neither `⊥` —
`x ≠ 1` — nor `⊤` — else `G` is cyclic, hence solvable, in the simple `G`), so any
maximal subgroup over `N_G(⟨x⟩)` contains `C_G(x)` and the singleton
`ℳ(C_G(x)) = {N}` pins it to `N`. -/
theorem normalizer_zpowers_le_of_centralizer_singleton [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {N : Subgroup G} {x : G} (hx1 : x ≠ 1)
    (hsingleton :
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N}) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ N := by
  have hCle : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [← OddOrder.BG.Ch4.S14.centralizer_zpowers_eq_singleton' x]
    exact Subgroup.centralizer_le_normalizer _
  have hne : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : (Subgroup.zpowers x).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop2
    · exact hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers x))
    · refine hG.notSolvable ?_
      haveI : IsCyclic G := ⟨⟨x, fun g =>
        Subgroup.mem_zpowers_iff.mp (htop2 ▸ Subgroup.mem_top g)⟩⟩
      letI : CommGroup G := IsCyclic.commGroup
      infer_instance
  obtain ⟨L, hLco, hLle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hne
  have hLmem : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hLco, hCle.trans hLle⟩
  rw [hsingleton, Set.mem_singleton_iff] at hLmem
  exact hLmem ▸ hLle

/-- **E.5's `(ii) ∧ hdc ⟹ (i)`, assembled from the raw hypothesis block** (BG p. 165):
under E.5's hypotheses with alternative (ii) (strengthened by the corrected E.4's `hdc`),
the index `[M : M_σ] = |M/M'|` is prime.

This derives every input of the WP4 engine `e5_derived_index_eq_of_ii_hdc` from the
Corollary 15.9 replay: the `(E.29)` neighbour bundle (`e5_neighbour_data`), the type-`F`
Frobenius complement (`centralizer_escape_final_local`), `M_σ` nilpotency (Prop 16.1
taxonomy), the suitable complement `E ⊇ K₁` with `E ⊓ N = K₁` (15.9(c)), the
`(E.30)`–`(E.32)` displays, and `N_G(⟨x⟩) ≤ N`. -/
theorem e5_msigma_index_prime_of_ii_hdc [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M N : Subgroup G} {x : G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hp : p.Prime)
    (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hord : orderOf x = p)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNnotF : N ∉ OddOrder.BG.Ch4.S14.maximalTypeFFamily G)
    (hii : ¬ ∃ A : Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1),
      A.Normal ∧ IsMulCommutative ↥A ∧ A.index = p)
    (hdc : ∀ n : ℕ,
      ⁅OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer
            ((Subgroup.upperCentralSeries ↥(Omega ↥(opiCoreInG {p} M) p 1) 2 :
                Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1)) :
              Set ↥(Omega ↥(opiCoreInG {p} M) p 1)))
          (⊤ : Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1)) n,
        Subgroup.centralizer
          ((Subgroup.upperCentralSeries ↥(Omega ↥(opiCoreInG {p} M) p 1) 2 :
              Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1)) :
            Set ↥(Omega ↥(opiCoreInG {p} M) p 1))⁆ ≤
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer
            ((Subgroup.upperCentralSeries ↥(Omega ↥(opiCoreInG {p} M) p 1) 2 :
                Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1)) :
              Set ↥(Omega ↥(opiCoreInG {p} M) p 1)))
          (⊤ : Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1)) (n + 2)) :
    ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index.Prime := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hord, h, orderOf_one])
  -- The `(E.29)` neighbour bundle.
  obtain ⟨hNmax, hP2N, hCN, hCNσx, hcompl, hptau2, hsingleton, K₁, U₁, hK₁MN, hU₁MN, hU₁ne,
    hK₁hallN, hU₁hallN, hkprime, hU₁ab, hK₁normU₁, hsupMN, E₂, E₃, hsetup, hU₁eq⟩ :=
    e5_neighbour_data hG hM hp hxM hord hesc hNmem hNnotF
  -- Corollary 15.9: `M` type `F` with cyclic Frobenius complement `E₀`.
  have hNnotF' : ¬ OddOrder.BG.Ch4.S14.IsTypeF N := fun hF => hNnotF ⟨hNmax, hF⟩
  obtain ⟨hFM, -, -, E₀, hE₀M, hE₀compl, hE₀cyc, hE₀frob⟩ :=
    centralizer_escape_final_local hG hM hNmax ⟨hxM, hx1⟩ hesc hNmem hNnotF'
  -- `M_σ` nilpotent (Prop 16.1 taxonomy, type-`F` branch).
  haveI hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp
      (maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG hM (Or.inl hFM))
  -- The primes: `p ∈ σ(M)`, `p ∈ (κ(N) ∪ σ(N))'`, `p` odd.
  have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma hxM p (by
      rw [hord]
      exact Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.pos.ne'⟩)
  have hpκσN : p ∈ (OddOrder.BG.Ch4.S14.kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ :=
    mem_kappa_sigma_compl_of_mem_tau2 hptau2
  have hxN : x ∈ N := hCN (Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff.mp hy])
  -- `(E.30)`: `O_p(M) ⊓ N = C_{O_p(M)}(x)`, and `x ∈ O_p(M)`.
  obtain ⟨hxOp, habs, hReq⟩ := e5_R_eq_centralizer hp hxM hord hxN hCN hMσnil hU₁MN
    hU₁hallN hU₁ab hK₁normU₁ hsupMN hpκσN
  -- `k := |K₁| ∈ κ(N)`, so `k ≠ p`.
  have hK₁N : K₁ ≤ N := hK₁MN.trans inf_le_right
  have hK₁M : K₁ ≤ M := hK₁MN.trans inf_le_left
  have hU₁N : U₁ ≤ N := hU₁MN.trans inf_le_right
  have hkκ : Nat.card ↥K₁ ∈ OddOrder.BG.Ch4.S14.kappa N := by
    refine hK₁hallN.1 (Nat.card ↥K₁) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁N).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hkprime, dvd_rfl, Nat.card_pos.ne'⟩
  have hkp : Nat.card ↥K₁ ≠ p := by
    intro h
    rw [Set.mem_compl_iff, Set.mem_union] at hpκσN
    exact hpκσN (Or.inl (h ▸ hkκ))
  -- BG Theorem A(4): `C_{U₁}(c) = 1` for `c ∈ K₁^#`.
  haveI : Fact (Nat.card ↥K₁).Prime := ⟨hkprime⟩
  haveI : IsCyclic ↥K₁ := isCyclic_of_prime_card (p := Nat.card ↥K₁) rfl
  have hCU₁ : ∀ c ∈ K₁, c ≠ 1 → U₁ ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    OddOrder.BG.Ch4.S14.typeP_hall_inf_centralizer_kappaElement_eq_bot hG hNmax hP2N.1
      hK₁N hU₁N hK₁hallN rfl hU₁hallN
  -- `K₁ ⊓ M_σ = ⊥`, hence `K₁` is a `σ(M)'`-group.
  have hxU₁ : x ∈ U₁ := habs ⟨hxOp, hxN⟩
  have hinfMσ : K₁ ⊓ OddOrder.BG.Ch3.S10.Msigma M = ⊥ :=
    e5_kappaHall_inf_Msigma_eq_bot hp hxM hord hx1 hMσnil hkprime rfl hkp hxU₁ hCU₁
  have hK₁σ' : ∀ r ∈ (Nat.card ↥K₁).primeFactors, r ∈ (OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    e5_kappaHall_pi_sigma_compl hG hM hK₁M hkprime rfl hinfMσ
  -- The suitable complement `E ⊇ K₁` (15.9(c)), and the collapse `E ⊓ N = K₁`.
  obtain ⟨E, hEM, hEcompl, hEcyc, hEfrob, hK₁E⟩ :=
    e5_exists_suitable_complement hG hM hK₁M hK₁σ' hE₀compl hE₀cyc hE₀M hE₀frob
  have hK₁ne : K₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hkprime
    exact hkprime.one_lt.ne' rfl
  have hMNle : M ⊓ N ≤ Subgroup.normalizer ((U₁ : Subgroup G) : Set G) := by
    rw [hsupMN]
    exact sup_le hK₁normU₁ Subgroup.le_normalizer
  have hU₁norm : (U₁.subgroupOf (M ⊓ N)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hk := Subgroup.mem_normalizer_iff.mp (hMNle k.2) (n : G)
    simpa using hk.mp hn
  have hENK₁ : E ⊓ N = K₁ :=
    inf_eq_kappaHall_of_le_cyclic hEM hEcyc hK₁E hK₁N hK₁ne hU₁norm hsupMN hCU₁
  -- `N_G(⟨x⟩) ≤ N` and the `K₁`-normalization of `⟨x⟩` (`(E.32)`).
  have hNxN := normalizer_zpowers_le_of_centralizer_singleton hG hx1 hsingleton
  have hnonab := e5_exists_nonabelian_sylow_of_ii hG hM hp hpσM hMσnil hxOp hord hii
  have hxEmn : x ∈ M ⊓ N := ⟨(OddOrder.BG.Ch3.S10.Msigma_le M) hxM, hxN⟩
  obtain ⟨hNnormx, -⟩ :=
    e5_zpowers_eq_canonical_line hG hsetup hp hptau2 hnonab hxEmn hord hCNσx
  have hK₁norm : ∀ g ∈ K₁, MulAut.conj g • (Subgroup.zpowers x) = Subgroup.zpowers x :=
    fun g hg => OddOrder.GroupTheory.conj_smul_eq_self_of_mem_normalizer (hNnormx (hK₁N hg))
  -- `(E.31)`: the decomposition `C_{O_p(M)}(x) = ⟨x⟩ × R₁` with `R₁` cyclic nontrivial.
  have hodd : Odd p := hG.odd.of_dvd_nat (hord ▸ orderOf_dvd_natCard x)
  have hRle : opiCoreInG {p} M ⊓ N ≤ M ⊓ N :=
    le_inf (inf_le_left.trans (opiCoreInG_le _ _)) inf_le_right
  have hRpg : IsPGroup p ↥(opiCoreInG {p} M ⊓ N) :=
    (isPGroup_opiCoreInG_singleton M).to_le inf_le_left
  have hRnoncyc := e5_R_noncyclic hG hM hsetup rfl hp hpσM hptau2 hMσnil
  have hNnormMσ : N ≤ Subgroup.normalizer
      ((OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
    have hMσNnorm : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (OddOrder.BG.Ch3.S10.Msigma_le N)).mp hMσNnorm
  obtain ⟨R₁, hR₁R, hR₁cyc, hR₁ne, hdisjR, hReqR⟩ :=
    e5_centralizer_decomposition hG hsetup hp hodd hptau2 hnonab hxEmn hord hCNσx
      hRle hRpg ⟨hxOp, hxN⟩ hRnoncyc hNnormMσ
  -- Feed the WP4 engine.
  have hEnorm : E ≤ Subgroup.normalizer ((opiCoreInG {p} M : Subgroup G) : Set G) :=
    hEM.trans (OddOrder.GroupTheory.le_normalizer_opiCoreInG {p} M)
  have hcardE : ¬ p ∣ Nat.card ↥E := by
    intro hdvd
    have h1 : Nat.card ↥(E.subgroupOf M) =
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
      hEcompl.symm.index_eq_card.symm
    have h2 : p ∣ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := by
      rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv]
      exact hdvd
    exact (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).2 p
      (Nat.mem_primeFactors.mpr ⟨hp, h2, Subgroup.index_ne_zero_of_finite⟩) hpσM
  have hOple : opiCoreInG {p} M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) (opiCoreInG_le _ _) ?_
    intro q hq
    obtain ⟨n, hn⟩ := (isPGroup_opiCoreInG_singleton (q := p) M).exists_card_eq
    rw [hn] at hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp
      (hqprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
    exact hqp ▸ hpσM
  have hEfrobElem : ∀ e ∈ E, e ≠ 1 → ∀ r ∈ opiCoreInG {p} M, r ≠ 1 → e * r * e⁻¹ ≠ r := by
    intro e heE he1 r hrOp hr1 heq
    have hrMσ : r ∈ OddOrder.BG.Ch3.S10.Msigma M := hOple hrOp
    have heM : e ∈ M := hEM heE
    have hrM : r ∈ M := (OddOrder.BG.Ch3.S10.Msigma_le M) hrMσ
    refine hEfrob.conj_frobenius ⟨e, heM⟩ (Subgroup.mem_subgroupOf.mpr heE)
      (fun h => he1 (by simpa using congrArg Subtype.val h)) ⟨r, hrM⟩
      (Subgroup.mem_subgroupOf.mpr hrMσ)
      (fun h => hr1 (by simpa using congrArg Subtype.val h)) ?_
    exact Subtype.ext heq
  have hcent : opiCoreInG {p} M ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.zpowers x ⊔ R₁ := by
    rw [← hReq]
    exact hReqR
  have hidx := e5_derived_index_eq_of_ii_hdc hG hp hkprime hkp hord hxOp hEnorm hcardE
    hK₁E rfl hEfrobElem hK₁norm (hR₁R.trans inf_le_left) hR₁cyc hR₁ne hdisjR hcent
    hM hEM hEcompl hNxN hENK₁ hii hdc
  -- `M' = M_σ` (cyclic complement), so `[M : M_σ] = k` is prime.
  have hder := derivedInG_eq_Msigma_of_cyclic_complement hG hM hEM hEcyc hEcompl
  rw [← hder, hidx]
  exact hkprime

end OddOrder.BG.AppE
