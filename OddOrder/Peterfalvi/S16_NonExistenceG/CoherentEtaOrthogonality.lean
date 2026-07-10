/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupL
import OddOrder.Peterfalvi.S16_GridExpansion
import OddOrder.Peterfalvi.S16_PairingCoherence

/-!
# Peterfalvi (13.19, pp. 85–87): coherent images and the eta-grid

This upstream leaf contains the generic type-I coherent-image orthogonality and Dade-support
avoidance results used on both the `L`- and `M`-sides of Section 16.  It is independent of the
Section 16 `MHypothesis` carrier and of the downstream comparison argument.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), the M-side `η`-grid orthogonality of `ψ^{τ₁} = ζ_M^ν`.**

The distinguished coherent image `ψ^{τ₁} = ζ_M^ν` (`= (dataM.h78 hG).nu (ζ_{zetaDistinct})`)
is orthogonal to the entire `η`-grid.  This is the sorry-free (3.6)–(3.8)/(13.19.b) engine
`eta_orthogonal_of_norm_one_pair_vanish` (`S16_GridExpansion`) applied to the conjugate pair
`(ζ_M^ν, ζ̄_M^ν)`: the unit norms (`nu_zeta_norm_one`), the conjugate distinctness
`⟨ζ_M^ν, ζ̄_M^ν⟩ = 0` (`nu_zeta_inner_nu_conj_eq_zero`), and the `ℤ[Irr G]` memberships
(`coh.extension_mem_ZIrr` on `ζ ∈ 𝒮`) are all supplied by the `TypeICoherent78Data` coherence
bundle.  The single genuine §13/§14 input is `hDadeAvoid` = **Peterfalvi (13.19.a)**: the M-side
Dade support `Ã(M)` avoids the regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`, so the
conjugate difference `ζ_M^ν − ζ̄_M^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`)
vanishes on `Ŵ^G`. -/
theorem caseB_eta_orthogonal_psi [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)) = 0 := by
  classical
  -- distinctness datum for the distinguished index `zetaDistinct = 0` and its conjugate `i'`
  have hjne : (dataM.h78 hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  obtain ⟨i', hi'_ne, hi'⟩ := dataM.exists_conjIndex_at hG hjne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
      ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zetaDistinct_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i') ∈ ZIrr G := by
    have hi'ne_data : i' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hi'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hi'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG (dataM.h78 hG).zetaDistinct_ne_ind1H
  have hconj1 := dataM.nu_zeta_norm_one hG hi'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hjne hi'_ne hi'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hjne hi'_ne hi'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), the `η`-grid orthogonality of *every* coherent image `ζ_k^ν`**
(the Coq `o_tauLeta` for the whole family, not just the distinguished index).  For any family
member `k ≠ ind1H`, the coherent image `ζ_k^ν = (dataM.h78 hG).nu (ζ_k)` is orthogonal to the
entire `η`-grid.  Identical (3.6)–(3.8)/(13.19.b) engine as `caseB_eta_orthogonal_psi`, but with
the distinguished index `zetaDistinct` replaced by an arbitrary `k`: `ζ_k^ν` has unit norm
(`nu_zeta_norm_one`), its conjugate partner `ζ_{k'}^ν` (`exists_conjIndex_at`, generic in the
index) is a distinct unit-norm virtual character (`nu_zeta_inner_nu_conj_eq_zero`), and the
conjugate difference `ζ_k^ν − ζ_{k'}^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`,
also generic) vanishes on `Ŵ^G` by the same (13.19.a) Dade-support avoidance `hDadeAvoid`. -/
theorem caseB_eta_orthogonal_nu_zeta_at [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport)
    {k : Fin (dataM.n + 1)} (hk : k ≠ (dataM.h78 hG).ind1H) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)) = 0 := by
  classical
  -- the kernel-index datum for `k` and its conjugate partner `k'`
  have hkne : k ≠ dataM.ind1H := by rwa [dataM.h78_ind1H_eq] at hk
  obtain ⟨k', hk'_ne, hk'⟩ := dataM.exists_conjIndex_at hG hkne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k) ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hkne))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k') ∈ ZIrr G := by
    have hk'ne_data : k' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hk'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hk'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG hk
  have hconj1 := dataM.nu_zeta_norm_one hG hk'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hkne hk'_ne hk'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hkne hk'_ne hk'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), σ-decomposition ingredient**: the Fitting core `M_F`
(`dataM.kernel`) of the type-`I` maximal `M`, non-conjugate to the `W`-containing maximals
`S`, `T`, has order coprime to `p·q`.  In the Coq proof of `tiA_PWG` this is `coHp`/`coHq`
(`coprime #|H| p`, `coprime #|H| q` with `H = M_F`), derived from `FT_Dade_support_partition`:
`p, q ∈ σ(S) ∪ σ(T)` are disjoint from `σ(M)` for non-conjugate maximals (`nc.not_conj`).
Deep named §13/BG §10 obligation. -/
theorem card_kernel_coprime_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    Nat.Coprime (Nat.card ↥dataM.kernel) (hyp.base.p * hyp.base.q) := by
  classical
  -- `M`, `S`, `T` are maximal; `M` type I, `S`/`T` type II
  have hMI : IsTypeI M := ⟨dataM.typeIHyp.typeI⟩
  have hSII : IsTypeII hyp.base.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.S_maximal hyp.base.S_typeP2
  have hTII : IsTypeII hyp.base.T := T_typeII hG hyp
  -- `M_F = M_σ`, `S_σ = P`, `T_σ = Q`
  have hMF : dataM.kernel = OddOrder.BG.Ch3.S10.Msigma M := by
    change dataM.typeIHyp.typeI.typeF.H = _
    rw [dataM.typeIHyp.typeI.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hMmax (Or.inl hMI)
  have hMsS : OddOrder.BG.Ch3.S10.Msigma hyp.base.S = hyp.base.P := by
    rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hyp.base.S_maximal (Or.inr hSII)]
    exact hyp.base.P_eq_SF.symm
  have hMsT : OddOrder.BG.Ch3.S10.Msigma hyp.base.T = hyp.base.Q := by
    rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hyp.base.T_maximal (Or.inr hTII)]
    exact hyp.base.Q_eq_TF.symm
  -- `p ∈ σ(S)` (as `p = |W₂| ∣ |P| = |S_σ|`), `q ∈ σ(T)`
  have hpσS : hyp.base.p ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.S := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.S_maximal, hMsS]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.p_eq_card_W2]
    exact Subgroup.card_dvd_of_le (OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base)
  have hqσT : hyp.base.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.T := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.T_maximal, hMsT]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.q_eq_card_W1]
    exact Subgroup.card_dvd_of_le (OddOrder.Peterfalvi.S15.W1_le_Q hG hyp.base)
  -- `M` is not conjugate to `S` or `T` (type I vs type non-I) ⟹ `σ`-disjointness
  have hMnS : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.S :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.S_maximal
      (Or.inl hSII)
  have hMnT : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.T :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.T_maximal
      (Or.inl hTII)
  have hdS := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.S_maximal hMnS
  have hdT := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.T_maximal hMnT
  -- hence `p, q ∉ σ(M) = π(|M_F|)`, so `p, q ∤ |M_F|`
  have hpMF : ¬ hyp.base.p ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdS
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.p).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, hdvd, Nat.card_pos.ne'⟩)) hpσS
  have hqMF : ¬ hyp.base.q ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdT
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.q).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, hdvd, Nat.card_pos.ne'⟩)) hqσT
  exact Nat.Coprime.mul_right
    (hyp.base.p_prime.coprime_iff_not_dvd.mpr hpMF).symm
    (hyp.base.q_prime.coprime_iff_not_dvd.mpr hqMF).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), Dade-support ingredient**: every element `y` of the Dade support
`Ã(M) = ⋃_{x∈A(M)} (x·R(x))^G` has order *not* coprime to `|M_F|` (it is `π(M_F)`-singular).
Indeed `y` is conjugate to `x·r` with `x ∈ A(M) = M_F^#` (type-I, `1 ≠ x ∈ M_F`) and
`r ∈ R(x)` a signalizer commuting with `x` of order coprime to `|M_F|`, so
`1 < orderOf x ∣ orderOf y` and `orderOf x ∣ |M_F|`.  Deep named §8/§13 obligation
(the Dade signalizer `π`-part structure). -/
theorem dadeSupport_not_coprime_card_kernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (dataM : TypeICoherent78Data M)
    {y : G} (hy : y ∈ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ¬ Nat.Coprime (orderOf y) (Nat.card ↥dataM.kernel) := by
  classical
  -- `y` is conjugate to `a·h` with `a ∈ A = M_F#`, `h ∈ H(a)` (the (8.14) signalizer)
  rw [dataM.h78_hyp_eq hG, OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff] at hy
  obtain ⟨a, h, hh, hconj⟩ := hy
  -- `a.1 ∈ M_F`, `a.1 ≠ 1` (`A = typeIA = M_F ∖ {1}`)
  have ha2 : a.1 ∈ (dataM.kernel : Set G) \ {1} := by
    rw [← dataM.typeIA_eq_sharp hG]; exact a.2
  have haK : a.1 ∈ dataM.kernel := ha2.1
  have hane : a.1 ≠ 1 := fun h1 => ha2.2 (Set.mem_singleton_iff.mpr h1)
  have hord_ne : orderOf a.1 ≠ 1 := fun h1 => hane (orderOf_eq_one_iff.mp h1)
  have hord_dvd : orderOf a.1 ∣ Nat.card ↥dataM.kernel := dataM.kernel.orderOf_dvd_natCard haK
  -- `h` commutes with `a.1`: `H(a) ≤ C_G(a.1)` by `(2.2.b)` `C_G(a.1) = H(a) ⊔ C_L(a.1)`
  have hh_cent : h ∈ Subgroup.centralizer ({a.1} : Set G) := by
    rw [(dataM.typeIHyp.dadeData.dade).centralizer_eq_sup a]
    exact Subgroup.mem_sup_left hh
  have hcomm : Commute a.1 h := (Subgroup.mem_centralizer_singleton_iff.mp hh_cent).symm
  -- `orderOf a.1` coprime `orderOf h`: `(2.2.c)` `(|H(a)|, |C_L(a.1)|) = 1`
  have hcop_orders : Nat.Coprime (orderOf a.1) (orderOf h) := by
    have hcc := (dataM.typeIHyp.dadeData.dade).centralizer_coprime a a
    have hord_h : orderOf h ∣ Nat.card ↥((dataM.typeIHyp.dadeData.dade).H a) :=
      ((dataM.typeIHyp.dadeData.dade).H a).orderOf_dvd_natCard hh
    have haCent : a.1 ∈ OddOrder.Peterfalvi.S04.centralizerIn M a.1 :=
      OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
        ⟨(dataM.typeIHyp.dadeData.dade).mem_L a.2, rfl⟩
    have hord_a : orderOf a.1 ∣ Nat.card ↥(OddOrder.Peterfalvi.S04.centralizerIn M a.1) :=
      (OddOrder.Peterfalvi.S04.centralizerIn M a.1).orderOf_dvd_natCard haCent
    exact (Nat.Coprime.coprime_dvd_right hord_a
      (Nat.Coprime.coprime_dvd_left hord_h hcc)).symm
  -- `orderOf y = orderOf(a.1·h) = orderOf a.1 · orderOf h`, so `orderOf a.1 ∣ orderOf y`
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hsemi : SemiconjBy c (a.1 * h) y := by
    change c * (a.1 * h) = y * c; rw [← hc]; group
  have hordy : orderOf y = orderOf a.1 * orderOf h := by
    rw [← SemiconjBy.orderOf_eq c hsemi,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders]
  have hdvd_y : orderOf a.1 ∣ orderOf y := by rw [hordy]; exact dvd_mul_right _ _
  -- `1 < orderOf a.1 ∣ gcd(orderOf y, |M_F|) = 1` is a contradiction
  intro hcop
  have hcop' : Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) = 1 := hcop
  have hgcd : orderOf a.1 ∣ Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) :=
    Nat.dvd_gcd hdvd_y hord_dvd
  rw [hcop'] at hgcd
  exact hord_ne (Nat.dvd_one.mp hgcd)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), the M-side Dade-support avoidance.**  For a type-`I` maximal
`M` not conjugate to the `W`-containing maximals `S`, `T`, the Dade support `Ã(M)` avoids the
regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`.  This is the Coq `tiA_PWG`
(`'A~(L) :&: PWG = set0`, PFsection13): every `x ∈ Ŵ^G` is conjugate to a `w ∈ W`, so (as
`|W₁| = q`, `|W₂| = p` are prime and `W = W₁·W₂` commutes) `orderOf x ∣ p·q`, hence `orderOf x`
is coprime to `|M_F|` (`card_kernel_coprime_pq`); but every element of `Ã(M)` is
`π(M_F)`-singular (`dadeSupport_not_coprime_card_kernel`), a contradiction.  The two named
ingredients are the genuine BG §10-level σ-decomposition inputs. -/
theorem mSide_dadeSupport_avoids_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    ∀ x ∈ conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  intro x hx hdade
  obtain ⟨w, ⟨hwW, _hwne⟩, g, hgx⟩ := hx
  -- `orderOf x = orderOf w` (conjugation preserves order)
  have hsemi : SemiconjBy g w x := by
    change g * w = x * g
    rw [← hgx]; group
  have hordx : orderOf x = orderOf w := (SemiconjBy.orderOf_eq g hsemi).symm
  -- decompose `w = a·b` with `a ∈ W₁`, `b ∈ W₂` inside the commutative `W`
  letI := hyp.base.W_cyclic
  letI : CommGroup ↥hyp.base.W := IsCyclic.commGroup
  have hwWmem : w ∈ hyp.base.W := hwW
  have hW1le : hyp.base.W1 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
  have hwmem : (⟨w, hwWmem⟩ : ↥hyp.base.W) ∈
      (hyp.base.W1.subgroupOf hyp.base.W) ⊔ (hyp.base.W2.subgroupOf hyp.base.W) := by
    have h1 : (hyp.base.W1 ⊔ hyp.base.W2).subgroupOf hyp.base.W = ⊤ := by
      rw [← hyp.base.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hwmem
  have hcoe : (a : G) * (b : G) = w := by
    have h := congrArg (Subtype.val) hab; simpa using h
  have haW1 : (a : G) ∈ hyp.base.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : (b : G) ∈ hyp.base.W2 := Subgroup.mem_subgroupOf.mp hb
  -- `orderOf a ∣ q`, `orderOf b ∣ p` (Lagrange in the prime-order `W₁`, `W₂`)
  have haord : orderOf (a : G) ∣ hyp.base.q := by
    have h := hyp.base.W1.orderOf_dvd_natCard haW1
    rwa [← hyp.base.q_eq_card_W1] at h
  have hbord : orderOf (b : G) ∣ hyp.base.p := by
    have h := hyp.base.W2.orderOf_dvd_natCard hbW2
    rwa [← hyp.base.p_eq_card_W2] at h
  have hcomm : Commute (a : G) (b : G) := hyp.base.W1_commutes_W2 _ haW1 _ hbW2
  -- hence `orderOf x = orderOf w ∣ p·q`
  have hword : orderOf w ∣ hyp.base.p * hyp.base.q := by
    rw [← hcoe]
    refine hcomm.orderOf_mul_dvd_mul_orderOf.trans ?_
    rw [mul_comm hyp.base.p hyp.base.q]
    exact Nat.mul_dvd_mul haord hbord
  have hxord : orderOf x ∣ hyp.base.p * hyp.base.q := hordx ▸ hword
  -- `orderOf x` is coprime to `|M_F|`, contradicting `π(M_F)`-singularity of `Ã(M)`
  have hcop : Nat.Coprime (orderOf x) (Nat.card ↥dataM.kernel) :=
    Nat.Coprime.coprime_dvd_left hxord (card_kernel_coprime_pq hG hMmax dataM).symm
  exact dadeSupport_not_coprime_card_kernel hG dataM hdade hcop

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The canonical §7.8 beta attached to a coherent type-I bundle, exposed as a class function
independent of later choices of `Fintype G`. -/
noncomputable def coherentBeta [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (dataM : TypeICoherent78Data M) : ClassFunction G ℂ :=
  (dataM.h78 hG).beta

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), invariance of the `eta`-grid coefficients under the choice of
distinguished coherent-family member.**

Let `grid.phi` be the member chosen by the §13 type-I grid producer and let `zeta 0` be the member
chosen by the §7.8 coherent bundle.  Both lie in the same coherent family and have the common
degree `[M : M_F]`.  Hence their difference is supported in `A(M)`, so the Dade map sends it to the
difference of their coherent images.  Every coherent image is orthogonal to the `eta`-grid by
(13.19.b); consequently replacing `grid.phi` by `zeta 0` changes the associated Dade `beta` by a
function orthogonal to every `eta_ij`.

This is the choice-free synchronization needed by (14.11.2): it deliberately asserts equality of
the grid coefficients, not equality of the two `beta` class functions (which need not hold for
different distinguished family members). -/
theorem typeIGrid_betaL_inner_eta_eq_h78_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M)
    (grid : OddOrder.Peterfalvi.S15.TypeIOrthogonalityGridData
      hyp.base dataM.typeIHyp)
    (hphi : grid.phi ∈ dataM.typeIHyp.Sset) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner grid.betaL (hyp.base.eta i j) =
          ClassFunction.inner (coherentBeta hG dataM) (hyp.base.eta i j) := by
  classical
  intro fintypeG invertibleG i j
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  haveI := dataM.kernelIn_normal
  -- The two selected family members have the same degree, namely the complement index.
  have he : grid.e = dataM.kernelIn.index := by
    rw [← grid.e_eq_index]
    change ((maxNilpotentNormalHall M).subgroupOf M).index =
      ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M).index
    rw [dataM.typeIHyp.typeI.typeF.H_eq]
  have hdeg : dataM.zeta 0 (1 : ↥M) = grid.phi (1 : ↥M) := by
    rw [dataM.deg0, grid.phi_degree_eq_e, he]
  -- Their difference lies in the supported coherent lattice, so `tau = tau1` on it.
  have hsharp : dataM.typeIHyp.ambientA = (dataM.kernel : Set G) \ {1} := by
    simpa [OddOrder.Peterfalvi.S14.Hypothesis.ambientA] using dataM.typeIA_eq_sharp hG
  have hsupp : (dataM.zeta 0 - grid.phi).support ⊆ dataM.typeIHyp.A := by
    simpa [OddOrder.Peterfalvi.S14.Hypothesis.A,
      OddOrder.Peterfalvi.S14.Hypothesis.ambientA] using
      (OddOrder.Peterfalvi.S14.Sset_diff_support_subset_ambientA dataM.typeIHyp
        (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)) hphi hdeg hsharp)
  have hagree : dataM.typeIHyp.tau (dataM.zeta 0 - grid.phi) =
      dataM.coh.extension (dataM.zeta 0) - dataM.coh.extension grid.phi := by
    rw [← map_sub]
    exact (dataM.coh.extends_on_supported (dataM.zeta 0 - grid.phi)
      ⟨Submodule.sub_mem _
          (Submodule.subset_span (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)))
          (Submodule.subset_span hphi),
        hsupp⟩).symm
  -- The canonical §7.8 beta is `tau (Ind 1 - zeta 0)`.
  have hbeta : coherentBeta hG dataM = dataM.typeIHyp.tau
      (ClassFunction.induce ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)
        (trivialClassFunction ↥((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)) - dataM.zeta 0) := by
    rw [coherentBeta]
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.beta_def]
    change dataM.typeIHyp.toHypothesis71.τ _ = dataM.typeIHyp.tau _
    rw [dataM.typeIHyp.toHypothesis71_tau_apply]
    apply congrArg dataM.typeIHyp.tau
    change (dataM.h78 hG).hyp76.zeta (dataM.h78 hG).ind1H -
        (dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct = _
    rw [dataM.h78_ind1H_eq, dataM.h78_zeta_eq,
      dataM.h78_zetaDistinct_eq, dataM.h78_zeta_eq]
    change ClassFunction.induce dataM.kernelIn
        (dataM.θ dataM.ind1H : ClassFunction _ ℂ) - dataM.zeta 0 = _
    rw [dataM.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  -- Thus the difference of the two beta functions is the coherent-image difference.
  have hbetaDiff : grid.betaL - coherentBeta hG dataM =
      dataM.coh.extension (dataM.zeta 0) - dataM.coh.extension grid.phi := by
    rw [grid.betaL_eq, hbeta, ← hagree, ← map_sub]
    apply congrArg dataM.typeIHyp.tau
    change (ClassFunction.induce ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)
        (trivialClassFunction ↥((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)) - grid.phi) -
      (ClassFunction.induce ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)
        (trivialClassFunction ↥((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)) - dataM.zeta 0) =
      dataM.zeta 0 - grid.phi
    abel
  -- Realize `grid.phi` as one of the placed induced family members.
  obtain ⟨theta, htheta, hphi_eq⟩ := hphi
  obtain ⟨k, hk⟩ := dataM.cover theta
  have hkphi : dataM.zeta k = grid.phi := hk.trans hphi_eq.symm
  have hk_ne : k ≠ dataM.ind1H := by
    intro hk_ind
    apply OddOrder.Peterfalvi.S09.Cert.induce_ne_trivialChar_induce
      dataM.kernelIn theta htheta
    calc
      ClassFunction.induce dataM.kernelIn (theta : ClassFunction _ ℂ) = grid.phi := hphi_eq.symm
      _ = dataM.zeta k := hkphi.symm
      _ = dataM.zeta dataM.ind1H := by rw [hk_ind]
      _ = ClassFunction.induce dataM.kernelIn
          (trivialIrreducibleCharacter ↥dataM.kernelIn : ClassFunction _ ℂ) := by
        change ClassFunction.induce dataM.kernelIn
            (dataM.θ dataM.ind1H : ClassFunction _ ℂ) = _
        rw [dataM.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  have hDadeAvoid := mSide_dadeSupport_avoids_regular (hyp := hyp) hG hMmax dataM
  have hzero_ne : (0 : Fin (dataM.n + 1)) ≠ (dataM.h78 hG).ind1H := by
    rw [dataM.h78_ind1H_eq]
    exact Ne.symm dataM.ind1H_ne_zero
  have hk_ne' : k ≠ (dataM.h78 hG).ind1H := by
    rw [dataM.h78_ind1H_eq]
    exact hk_ne
  have horth_zero : ClassFunction.inner (dataM.coh.extension (dataM.zeta 0))
      (hyp.base.eta i j) = 0 := by
    have h := caseB_eta_orthogonal_nu_zeta_at
      hG hyp.base dataM hDadeAvoid hzero_ne i j
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  have horth_phi : ClassFunction.inner (dataM.coh.extension grid.phi)
      (hyp.base.eta i j) = 0 := by
    have h := caseB_eta_orthogonal_nu_zeta_at
      hG hyp.base dataM hDadeAvoid hk_ne' i j
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq] at h
    rw [← hkphi, OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  have hdiff : ClassFunction.inner (grid.betaL - coherentBeta hG dataM)
      (hyp.base.eta i j) = 0 := by
    rw [hbetaDiff, ClassFunction.inner_sub_left, horth_zero, horth_phi, sub_zero]
  rw [ClassFunction.inner_sub_left, sub_eq_zero] at hdiff
  exact hdiff

end OrthogonalitySwitchData
end OddOrder.Peterfalvi.S16
