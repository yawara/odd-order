/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_ECore

/-!
# BG §12: The Subgroup `E` — active scaffold leaf

**スコープ**: BG Chapter III §12 (pp. 79-90), mmd L3023-3483, 全 19 結果のうち
**残 16 結果の faithful statement + `sorry` scaffold** (Prop 12.4(a) / Thm 12.5–12.13 /
Cor 12.6–12.16 / Lem 12.11/12.18 ほか)。定義層 (`SubgroupESetup` 等) と証明済み結果
(12.1/12.2(a)/12.17/12.19+12.18 building block) は `S12_ECore.lean` (import 済)。
**大半は Lemma 10.13 にブロックされている** (D-lane triage: 着手可能 5 件は証明済み、
残 14 件が 10.13 待ち) — 10.13 着地後に Lane F がここを進める。

## Lane proof-gate notes

- Proposition 12.4 uses the Uniqueness Theorem, Lemma 12.3, Proposition 1.16,
  Proposition 10.11(b), and Theorem 10.2 (mmd L3095-L3126).
- Theorem 12.5 is the bridge from §11 into §12: Proposition 12.4 supplies
  Hypothesis 11.1, then Theorems 11.3, 11.5, 11.7, Corollary 11.6, and
  Lemma 12.3 give the six conclusions (mmd L3129-L3148).
- Theorem 12.12 packages the Frobenius-complement endpoint from Theorem 12.7,
  Lemma 12.8, Corollary 12.6, and Lemma 12.11 (mmd L3306-L3344). The internal
  cyclic `Z_p` construction remains deferred.
- Proposition 12.15, Corollary 12.16 are the direct §13--§14 gates
  (mmd L3385-L3453); Corollary 12.16(b) remains a deferred proof obligation.
- Lemma 12.18 uses Theorem 1.13, Theorem 3.7, Corollary 10.9(a), and the
  Uniqueness Theorem (mmd L3454-L3482). Do not replace it by downstream
  prime-action assumptions in §13.
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch1.S06 (actionCommutator_conj_map_subtype fixedPointsOfMulAut_conj_map_subtype)
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Proposition 12.4(a)** (mmd L3095): `A ∈ ℰ_p²(M)` なら `C_G(A) ⊆ M`。
(原典 (b): `N_G(A₀)` の uniqueness ⇒ `p∈σ(M), M_α=1, M_σ` nilpotent は後続。) -/
theorem centralizer_le_of_elemAb_rank_two [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  sorry

/-- **BG Theorem 12.13** (mmd L3347): `G` のすべての非可換 `p`-部分群は `𝒰` に属す。 -/
theorem nonabelian_pgroup_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative P) :
    IsUniquelyMaximal P := by
  sorry

/-- **BG Corollary 12.14** (mmd L3369): `p ∈ σ(M)`, `X ∈ ℰ_p¹(M)`、`p ∈ β(M)` または
`X ⊆ M_σ'` なら `ℳ(C_G(X)) = {M}`。 -/
theorem maximalContaining_centralizer_eq_singleton [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ S10.sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXM : X ≤ M)
    (hcase : p ∈ S10.beta M ∨ X ≤ derivedInG (S10.Msigma M)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  sorry

/-- **BG Corollary 12.16(a)** (mmd L3423): `M` の `σ(M)`-部分群 `Y` は `M_σ` に共役で写せる
(`∃ g ∈ M, Y^g ⊆ M_σ`)。(原典 (b) の rank/derived 評価は後続。) -/
theorem sigma_subgroup_conj_into_Msigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Y : Subgroup G} (hYM : Y ≤ M)
    (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y) :
    ∃ g ∈ M, MulAut.conj g • Y ≤ S10.Msigma M := by
  sorry

/-- **BG Lemma 12.17** (mmd L3448): `C_{M_σ}(E) ⊆ M_σ'` かつ `[M_σ, E] = M_σ`。
(原典の `M_σ ∩ M^g` cyclic 評価は後続。) -/
theorem Msigma_E_relations [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Subgroup.centralizer (E : Set G) ⊓ S10.Msigma M ≤ derivedInG (S10.Msigma M) ∧
    ⁅S10.Msigma M, E⁆ = S10.Msigma M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
  have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
  -- Complement data inside `↥M`: `M_σ` is a normal Hall subgroup of `M` with complement `E`.
  have hcomplement := h.isComplement'_subgroupOf
  haveI hMσ_norm : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  have hid : (derivedInG M).subgroupOf M = commutator ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
  have hMσ_le_comm : (S10.Msigma M).subgroupOf M ≤ commutator ↥M :=
    calc (S10.Msigma M).subgroupOf M
        ≤ (derivedInG M).subgroupOf M :=
          Subgroup.comap_mono (S10.Msigma_le_derived hG h.mem_maximal)
      _ = commutator ↥M := hid
  have hcop : Nat.Coprime (Nat.card ↥((S10.Msigma M).subgroupOf M)) (Nat.card ↥(E.subgroupOf M)) := by
    have h1 := (S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rwa [hcomplement.symm.index_eq_card] at h1
  -- Second conjunct `⁅M_σ, E⁆ = M_σ`: first conclusion of Lemma 6.3(a) inside `↥M`, mapped to `G`.
  have hsecond : ⁅(S10.Msigma M : Subgroup G), E⁆ = S10.Msigma M := by
    have h1 := OddOrder.BG.Ch1.S06.commutator_eq_self_of_isComplement'_le_commutator
      (G := ↥M) hcomplement hMσ_le_comm
    have h2 := congrArg (Subgroup.map M.subtype) h1
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hMσM,
      Subgroup.map_subgroupOf_eq_of_le h.E_le] at h2
  -- First conjunct `C_G(E) ⊓ M_σ ≤ M_σ'`: second conclusion of Lemma 6.3(a) inside `↥M`, mapped.
  have hderiv_transport :
      (derivedInG ((S10.Msigma M).subgroupOf M)).map M.subtype = derivedInG (S10.Msigma M) := by
    rw [show derivedInG ((S10.Msigma M).subgroupOf M)
          = ⁅(S10.Msigma M).subgroupOf M, (S10.Msigma M).subgroupOf M⁆
          from Subgroup.map_subtype_commutator _,
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hMσM,
      show ⁅(S10.Msigma M : Subgroup G), S10.Msigma M⁆ = derivedInG (S10.Msigma M)
          from (Subgroup.map_subtype_commutator _).symm]
  have h632 := OddOrder.BG.Ch1.S06.centralizer_inf_le_derivedInG_of_isComplement'
    (G := ↥M) hcomplement hMσ_le_comm hcop
  refine ⟨fun x hx => ?_, hsecond⟩
  obtain ⟨hxC, hxMσ⟩ := hx
  have hxM : x ∈ M := hMσM hxMσ
  have hx'mem : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer ((E.subgroupOf M : Subgroup ↥M) : Set ↥M)
        ⊓ (S10.Msigma M).subgroupOf M := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, Subgroup.mem_subgroupOf.mpr hxMσ⟩
    intro e' he'
    have heE : ((e' : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp he'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (e' : G) heE)
  have hmapped := Subgroup.mem_map_of_mem M.subtype (h632 hx'mem)
  rwa [hderiv_transport] at hmapped

/-- **BG Lemma 12.3** (mmd L3071): `M, M* ∈ ℳ`, `A ∈ ℰ_p²(M ∩ M*)`, `A₀ ∈ ℰ_p¹` (`A₀ ⊆ A`),
`N_G(A₀) ⊆ M*` なら `A` は `M_σ ∩ M*` と `M_α ∩ M*` を中心化する。 -/
theorem elemAb_centralizes_meet [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] {A A₀ : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAM : A ≤ M ⊓ Mstar) (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hA₀A : A₀ ≤ A)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    A ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) ∧
    A ≤ Subgroup.centralizer ((S10.Malpha M ⊓ Mstar : Subgroup G) : Set G) := by
  sorry

/-- If a subgroup `C ≤ Nsub` carries the **full `π`-part** of `Nsub` (their `π`-prime
factorizations agree), then a Hall `π`-subgroup of `C` is a Hall `π`-subgroup of `Nsub`. Used to
turn "centralizes a Sylow `p` of `M_σ` for every `p ∈ π`" into "centralizes a Hall `π`-subgroup". -/
private theorem exists_hall_subgroupOf_of_full_factorization [Finite G] {Nsub C : Subgroup G}
    [IsSolvable ↥C] (π : Set ℕ) (hCN : C ≤ Nsub)
    (hfull : ∀ r ∈ π, (Nat.card ↥C).factorization r = (Nat.card ↥Nsub).factorization r) :
    ∃ W : Subgroup G, W ≤ C ∧ Ch03.IsHallSubgroup π (W.subgroupOf Nsub) := by
  classical
  obtain ⟨W₀, hW₀_hall⟩ := Ch03.hall_E_exists (G := ↥C) π
  set W : Subgroup G := W₀.map C.subtype with hWdef
  have hWC : W ≤ C := Subgroup.map_subtype_le _
  have hWN : W ≤ Nsub := hWC.trans hCN
  have hcardW : Nat.card ↥W = Nat.card ↥W₀ :=
    (Nat.card_congr (Subgroup.equivMapOfInjective W₀ C.subtype C.subtype_injective).toEquiv).symm
  have hcardWN : Nat.card ↥(W.subgroupOf Nsub) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv
  -- `|W₀|` carries the full `π`-part of `|C|`.
  have hW₀_full : ∀ p ∈ π, (Nat.card ↥W₀).factorization p = (Nat.card ↥C).factorization p := by
    intro p hp
    by_cases hp_prime : p.Prime
    · have hidx : (W₀.index).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdvd
        exact hW₀_hall.2 p (Nat.mem_primeFactors.mpr
          ⟨hp_prime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hp
      have hmul := Subgroup.card_mul_index W₀
      have hsum : (Nat.card ↥W₀).factorization p + (W₀.index).factorization p
          = (Nat.card ↥C).factorization p := by
        rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply]
      omega
    · rw [Nat.factorization_eq_zero_of_non_prime _ hp_prime,
        Nat.factorization_eq_zero_of_non_prime _ hp_prime]
  refine ⟨W, hWC, ?_, ?_⟩
  · intro p hp
    rw [hcardWN, hcardW] at hp
    exact hW₀_hall.1 p hp
  · intro p hp
    by_contra hpπ
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ (W.subgroupOf Nsub).index := (Nat.mem_primeFactors.mp hp).2.1
    -- `|Nsub| = |W.subgroupOf Nsub| · index`; compare `factorization p`.
    have hmul := Subgroup.card_mul_index (W.subgroupOf Nsub)
    have hfac : (Nat.card ↥(W.subgroupOf Nsub)).factorization p + ((W.subgroupOf Nsub).index).factorization p
        = (Nat.card ↥Nsub).factorization p := by
      rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply]
    rw [hcardWN, hcardW, hW₀_full p hpπ, hfull p hpπ] at hfac
    have : ((W.subgroupOf Nsub).index).factorization p = 0 := by omega
    rw [Nat.factorization_eq_zero_iff] at this
    rcases this with h | h | h
    · exact h hprime
    · exact h hpdvd
    · exact absurd h Subgroup.index_ne_zero_of_finite

/-- **Coprime coordination** (used in Lemma 12.19): if `A` acts coprimely on a finite solvable
group `N` and **every** Sylow subgroup of `A` acts trivially on *some* Hall `π`-subgroup of `N`,
then `A` acts trivially on some Hall `π`-subgroup of `N`. Witness = the `A`-invariant Hall
`π`-subgroup `H₀` (Prop 1.5): each Sylow `D` fixes a conjugate `c • H₀` of `H₀` with `c` itself
`D`-fixed, so `D` fixes `H₀`; the elements fixing `H₀` form a subgroup containing every Sylow,
hence all of `A`. -/
private theorem exists_hall_actsTrivially_of_forall_sylow
    {N A : Type*} [Group N] [Finite N] [IsSolvable N] [Group A] [Finite A]
    {φ : A →* MulAut N} (hCop : Nat.Coprime (Nat.card A) (Nat.card N)) (π : Set ℕ)
    (hsylow : ∀ (q : ℕ), q.Prime → ∀ (D : Sylow q A),
      ∃ H : Subgroup N, Ch03.IsHallSubgroup π H ∧ ∀ a ∈ (D : Subgroup A), ∀ h ∈ H, (φ a) h = h) :
    ∃ H : Subgroup N, Ch03.IsHallSubgroup π H ∧ ∀ a : A, ∀ h ∈ H, (φ a) h = h := by
  classical
  obtain ⟨H₀, hH₀_hall, hH₀_inv⟩ :=
    OddOrder.BG.Ch1.S01.exists_aInvariant_hall (φ := φ) hCop π
  refine ⟨H₀, hH₀_hall, ?_⟩
  -- `K = { a | a fixes H₀ pointwise }` is a subgroup of `A`.
  let K : Subgroup A :=
    { carrier := {a | ∀ h ∈ H₀, (φ a) h = h}
      one_mem' := by intro h _; rw [map_one, MulAut.one_apply]
      mul_mem' := by
        intro a b ha hb h hh
        rw [map_mul, MulAut.mul_apply, hb h hh, ha h hh]
      inv_mem' := by
        intro a ha h hh
        rw [map_inv]
        nth_rewrite 1 [← ha h hh]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] }
  suffices hKtop : K = ⊤ by
    intro a h hh
    exact (show a ∈ K from hKtop ▸ Subgroup.mem_top a) h hh
  -- Every Sylow subgroup of `A` is contained in `K` (via Prop 1.5(c) conjugacy).
  have hsyl_le : ∀ (q : ℕ), q.Prime → ∀ (D : Sylow q A), (D : Subgroup A) ≤ K := by
    intro q hq D
    obtain ⟨H_D, hH_D_hall, hH_D_triv⟩ := hsylow q hq D
    let ψ : ↥(D : Subgroup A) →* MulAut N := φ.comp (D : Subgroup A).subtype
    have hcopD : Nat.Coprime (Nat.card ↥(D : Subgroup A)) (Nat.card N) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have hH₀_invD : Ch03.IsAInvariant ψ H₀ := fun a => hH₀_inv (a : A)
    have hH_D_invD : Ch03.IsAInvariant ψ H_D := by
      rw [Ch03.isAInvariant_iff_smul_mem]
      intro a h hh
      show (φ (a : A)) h ∈ H_D
      rw [hH_D_triv (a : A) a.2 h hh]; exact hh
    obtain ⟨c, hc_fix, hc_conj⟩ :=
      OddOrder.BG.Ch1.S01.aInvariant_hall_conj (φ := ψ) hcopD hH_D_hall hH₀_hall
        hH_D_invD hH₀_invD
    intro a ha h hh
    rw [← hc_conj] at hh
    obtain ⟨h', hh', rfl⟩ := hh
    have hac : (φ a) c = c := hc_fix ⟨a, ha⟩
    have hah : (φ a) h' = h' := hH_D_triv a ha h' hh'
    show (φ a) (c * h' * c⁻¹) = c * h' * c⁻¹
    rw [map_mul, map_mul, map_inv, hac, hah]
  -- `K ⊇` every Sylow ⇒ `K = ⊤`.
  rw [← Subgroup.index_eq_one]
  by_contra hne
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact q.Prime := ⟨hq_prime⟩
  obtain ⟨D⟩ := (inferInstance : Nonempty (Sylow q A))
  have hDcard : Nat.card ↥(D : Subgroup A) = q ^ (Nat.card A).factorization q :=
    D.card_eq_multiplicity
  have hDdvdK : Nat.card ↥(D : Subgroup A) ∣ Nat.card ↥K :=
    Subgroup.card_dvd_of_le (hsyl_le q hq_prime D)
  have hfull : (Nat.card A).factorization q ≤ (Nat.card ↥K).factorization q := by
    have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      Nat.card_pos.ne').mpr hDdvdK
    have := hle q
    rwa [hDcard, Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self hq_prime,
      smul_eq_mul, mul_one] at this
  have hmul := Subgroup.card_mul_index K
  have hfac : (Nat.card ↥K).factorization q + (K.index).factorization q
      = (Nat.card A).factorization q := by
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply]
  have hidx0 : (K.index).factorization q = 0 := by omega
  rw [Nat.factorization_eq_zero_iff] at hidx0
  rcases hidx0 with h | h | h
  · exact h hq_prime
  · exact h hq_dvd
  · exact absurd h Subgroup.index_ne_zero_of_finite

/-- **BG Lemma 12.19** (mmd L3480): `E'` は `M_σ` の Hall `β(M)'`-部分群を中心化する。 -/
theorem derivedE_centralizes_betaComplement [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    ∃ W : Subgroup G, W ≤ S10.Msigma M ∧
      Ch03.IsHallSubgroup (S10.beta M)ᶜ (W.subgroupOf (S10.Msigma M)) ∧
      derivedInG E ≤ Subgroup.centralizer (W : Set G) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
  have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
  haveI hMσsolv : IsSolvable ↥(S10.Msigma M) :=
    solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hMσM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMσM).surjective
  have hE'_le_E : derivedInG E ≤ E := Subgroup.map_subtype_le _
  have hE'M : derivedInG E ≤ M := hE'_le_E.trans h.E_le
  have hE'_le_M' : derivedInG E ≤ derivedInG M := by
    have h1 : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
    have h2 : derivedInG M = ⁅M, M⁆ := Subgroup.map_subtype_commutator M
    rw [h1, h2]; exact Subgroup.commutator_mono h.E_le h.E_le
  have hE'_norm_Mσ : derivedInG E ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    hE'M.trans (le_normalizer_opiCoreInG (S10.sigma M) M)
  -- coprime `(|E'|, |M_σ|)`.
  have hcop_MσE : Nat.Coprime (Nat.card ↥(S10.Msigma M)) (Nat.card ↥E) := by
    have h1 := (S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rw [h.isComplement'_subgroupOf.symm.index_eq_card] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at h1
  have hcop : Nat.Coprime (Nat.card ↥(derivedInG E)) (Nat.card ↥(S10.Msigma M)) :=
    hcop_MσE.symm.coprime_dvd_left (Subgroup.card_dvd_of_le hE'_le_E)
  -- conjugation action `φ : ↥E' →* MulAut ↥M_σ`.
  letI act : MulDistribMulAction ↥(derivedInG E) ↥(S10.Msigma M) :=
    MulDistribMulAction.compHom
      (M := ↥(Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G))) ↥(S10.Msigma M)
      (Subgroup.inclusion hE'_norm_Mσ)
  set φ : ↥(derivedInG E) →* MulAut ↥(S10.Msigma M) :=
    MulDistribMulAction.toMulAut ↥(derivedInG E) ↥(S10.Msigma M) with hφ
  have hφ_coe : ∀ (a : ↥(derivedInG E)) (x : ↥(S10.Msigma M)),
      ((S10.Msigma M).subtype ((φ a) x)) = (↑a) * ((S10.Msigma M).subtype x) * (↑a)⁻¹ :=
    fun _ _ => rfl
  -- Supply: each (prime) Sylow of `E'` acts `φ`-trivially on a Hall `β'`-subgroup of `M_σ`.
  have hsupply : ∀ (q : ℕ), q.Prime → ∀ (D : Sylow q ↥(derivedInG E)),
      ∃ H : Subgroup ↥(S10.Msigma M), Ch03.IsHallSubgroup (S10.beta M)ᶜ H ∧
        ∀ a ∈ (D : Subgroup ↥(derivedInG E)), ∀ x ∈ H, (φ a) x = x := by
    intro q hq D
    haveI : Fact q.Prime := ⟨hq⟩
    set X_G : Subgroup G := (D : Subgroup ↥(derivedInG E)).map (derivedInG E).subtype with hXGdef
    have hXG_le_E' : X_G ≤ derivedInG E := Subgroup.map_subtype_le _
    have hXG_le_M' : X_G ≤ derivedInG M := hXG_le_E'.trans hE'_le_M'
    have hXG_le_M : X_G ≤ M := hXG_le_E'.trans hE'M
    have hXG_pg : IsPGroup q ↥X_G :=
      D.2.of_equiv (Subgroup.equivMapOfInjective _ _ (derivedInG E).subtype_injective)
    set C : Subgroup G := Subgroup.centralizer (X_G : Set G) ⊓ S10.Msigma M with hCdef
    have hC_le_Mσ : C ≤ S10.Msigma M := inf_le_right
    haveI : IsSolvable ↥C :=
      solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe (hC_le_Mσ.trans hMσM)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (hC_le_Mσ.trans hMσM)).surjective
    have hfull : ∀ r ∈ (S10.beta M)ᶜ,
        (Nat.card ↥C).factorization r = (Nat.card ↥(S10.Msigma M)).factorization r := by
      intro r hr
      refine le_antisymm
        ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
          (Subgroup.card_dvd_of_le hC_le_Mσ) r) ?_
      by_cases hrMσ : r ∈ (Nat.card ↥(S10.Msigma M)).primeFactors
      · have hr_prime := Nat.prime_of_mem_primeFactors hrMσ
        haveI : Fact r.Prime := ⟨hr_prime⟩
        obtain ⟨R, hR_le_C, hR_card⟩ : ∃ R : Subgroup G, R ≤ C ∧
            Nat.card ↥R = r ^ (Nat.card ↥(S10.Msigma M)).factorization r := by
          by_cases hXG_bot : X_G = ⊥
          · obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow r ↥(S10.Msigma M)))
            refine ⟨(S : Subgroup ↥(S10.Msigma M)).map (S10.Msigma M).subtype, ?_, ?_⟩
            · rw [hCdef, hXG_bot]
              refine le_inf ?_ (Subgroup.map_subtype_le _)
              intro g _
              rw [Subgroup.mem_centralizer_iff]
              intro s hs
              rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hs
              subst hs; rw [one_mul, mul_one]
            · rw [← Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup ↥(S10.Msigma M))
                (S10.Msigma M).subtype (S10.Msigma M).subtype_injective).toEquiv]
              exact S.card_eq_multiplicity
          · have hqX : q ∈ (Nat.card ↥X_G).primeFactors := by
              obtain ⟨n, hn⟩ := hXG_pg.exists_card_eq
              have hX1 : Nat.card ↥X_G ≠ 1 := fun hh => hXG_bot (Subgroup.card_eq_one.mp hh)
              have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; exact hX1 hn
              exact Nat.mem_primeFactors.mpr ⟨hq, hn ▸ dvd_pow_self q hn0, Nat.card_pos.ne'⟩
            have hq_piE : q ∈ (Nat.card ↥E).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hq,
                ((Nat.mem_primeFactors.mp hqX).2.1).trans
                  ((Subgroup.card_dvd_of_le hXG_le_E').trans (Subgroup.card_dvd_of_le hE'_le_E)),
                Nat.card_pos.ne'⟩
            have hq_not_sigma : q ∉ S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hq_piE
            have hq_not_beta : q ∉ S10.beta M := fun hb =>
              hq_not_sigma (S10.alpha_subset_sigma hG h.mem_maximal (S10.beta_subset_alpha M hb))
            have hr_sigma : r ∈ S10.sigma M := S10.Msigma_isPiGroup M r hrMσ
            have hrq : r ≠ q := fun he => hq_not_sigma (he ▸ hr_sigma)
            obtain ⟨S, hS_cent⟩ := (S10.beta_complement_centralizes hG h.mem_maximal hrq hr
              hq_not_beta hXG_le_M hXG_pg (Or.inl hXG_le_M')).1
            refine ⟨(S : Subgroup ↥(S10.Msigma M)).map (S10.Msigma M).subtype, ?_, ?_⟩
            · refine le_inf ?_ (Subgroup.map_subtype_le _)
              intro g hgR
              rw [Subgroup.mem_centralizer_iff]
              intro s hsX
              exact (Subgroup.mem_centralizer_iff.mp (hS_cent hsX) g hgR).symm
            · rw [← Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup ↥(S10.Msigma M))
                (S10.Msigma M).subtype (S10.Msigma M).subtype_injective).toEquiv]
              exact S.card_eq_multiplicity
        have hdvd : Nat.card ↥R ∣ Nat.card ↥C := Subgroup.card_dvd_of_le hR_le_C
        have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvd r
        rwa [hR_card, Nat.factorization_pow, Finsupp.smul_apply,
          Nat.Prime.factorization_self hr_prime, smul_eq_mul, mul_one] at hle
      · have hz : (Nat.card ↥(S10.Msigma M)).factorization r = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          by_cases hrp : r.Prime
          · exact Or.inr (Or.inl (fun hd =>
              hrMσ (Nat.mem_primeFactors.mpr ⟨hrp, hd, Nat.card_pos.ne'⟩)))
          · exact Or.inl hrp
        rw [hz]; exact Nat.zero_le _
    obtain ⟨W_G, hW_G_le_C, hW_G_hall⟩ :=
      exists_hall_subgroupOf_of_full_factorization (S10.beta M)ᶜ hC_le_Mσ hfull
    refine ⟨W_G.subgroupOf (S10.Msigma M), hW_G_hall, ?_⟩
    intro a ha x hx
    have haXG : (a : G) ∈ X_G := ⟨a, ha, rfl⟩
    have hxW : ((S10.Msigma M).subtype x : G) ∈ W_G := Subgroup.mem_subgroupOf.mp hx
    have hcomm : (a : G) * (S10.Msigma M).subtype x = (S10.Msigma M).subtype x * (a : G) :=
      Subgroup.mem_centralizer_iff.mp ((hW_G_le_C.trans inf_le_left) hxW) (a : G) haXG
    apply (S10.Msigma M).subtype_injective
    rw [hφ_coe, hcomm]; group
  obtain ⟨H, hH_hall, hH_triv⟩ :=
    exists_hall_actsTrivially_of_forall_sylow (φ := φ) hcop (S10.beta M)ᶜ hsupply
  refine ⟨H.map (S10.Msigma M).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [show (H.map (S10.Msigma M).subtype).subgroupOf (S10.Msigma M) = H from
      Subgroup.comap_map_eq_self_of_injective (S10.Msigma M).subtype_injective H]
    exact hH_hall
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    obtain ⟨x, hxH, rfl⟩ := hy
    have htriv : (φ ⟨a, ha⟩) x = x := hH_triv ⟨a, ha⟩ x hxH
    have hco := hφ_coe ⟨a, ha⟩ x
    rw [htriv] at hco
    conv_lhs => rw [hco]
    group

/-! ## §12 τ₂(M) ≠ ∅ の場合 (mmd L3129-3344) — 最複雑 subsection -/

/-- **BG Theorem 12.5** (mmd L3129): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(M)` のとき
(a) `M_σ` nilpotent; (b) `M` は abelian Sylow `p` を持ち、`A` を含む Sylow `p`-部分群 `P` で
`N_G(P) ⊄ M`; (c) `M_σA ⊴ M`; (d) `C_{M_σ}(A)=1`; (e) `M^* ∈ ℳ(A)-{M}` で `M_σ ∩ M^* = 1`;
(f) `∃ A₁ ∈ ℰ¹(A)` で `C_{M_σ}(A₁)=1`。
(原典 (b) の `Ω₁(P)=A` は Omega の入れ子のため docstring で defer。) -/
theorem Msigma_nilpotent_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) :
    Group.IsNilpotent ↥(S10.Msigma M) ∧
    ((∀ P : Sylow p ↥M, IsMulCommutative (P : Subgroup ↥M)) ∧
      ∃ P : Subgroup G, P ≤ M ∧ IsPGroup p ↥P ∧ A ≤ P ∧
        (∀ T : Subgroup G, T ≤ M → IsPGroup p ↥T → P ≤ T → P = T) ∧
        ¬ (Subgroup.normalizer (P : Set G) ≤ M)) ∧
    M ≤ Subgroup.normalizer ((S10.Msigma M ⊔ A : Subgroup G) : Set G) ∧
    S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
    (∀ Mstar ∈ maximalSubgroupsContaining A, Mstar ≠ M → S10.Msigma M ⊓ Mstar = ⊥) ∧
    (∃ A₁ ∈ elemAbelianOfRank G p 1, A₁ ≤ A ∧
      S10.Msigma M ⊓ Subgroup.centralizer (A₁ : Set G) = ⊥) := by
  sorry

/-- **BG Corollary 12.6** (mmd L3150): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` のとき
(a) `A ⊴ E` かつ `ℰ_p¹(E)=ℰ¹(A)`; (b) `C_G(A) ⊆ N_M(A)=E`, `N_G(A) ⊄ M`;
(c) `X ∈ ℰ¹(A)` で `C_{M_σ}(X)≠1` なら `ℳ(C_G(X))={M}`; (d) `x ∈ E₃#` で `C_{M_σ}(x)=1`;
(e) `x ∈ C_{E₁}(A)#` で `C_{M_σ}(x)=1`; (f) `M^*` が `M` と非共役なら `M_σ ∩ M^*_σ = 1` かつ
`σ(M) ∩ σ(M^*) = ∅`。 -/
theorem elemAb_normal_in_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    (E ≤ Subgroup.normalizer (A : Set G) ∧
      (∀ X ∈ elemAbelianOfRank G p 1, X ≤ E ↔ X ≤ A)) ∧
    (Subgroup.centralizer (A : Set G) ≤ E ∧
      M ⊓ Subgroup.normalizer (A : Set G) = E ∧ ¬ (Subgroup.normalizer (A : Set G) ≤ M)) ∧
    (∀ X ∈ elemAbelianOfRank G p 1, X ≤ A →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
      maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
    (∀ x ∈ E₃, x ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) ∧
    (∀ x ∈ E₁, x ∈ Subgroup.centralizer (A : Set G) → x ≠ 1 →
      S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) ∧
    (∀ Mstar ∈ maximalSubgroups G, (¬ ∃ g : G, MulAut.conj g • M = Mstar) →
      S10.Msigma M ⊓ S10.Msigma Mstar = ⊥ ∧ Disjoint (S10.sigma M) (S10.sigma Mstar)) := by
  sorry

/-- **BG Theorem 12.7** (mmd L3171): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `G` が非可換 Sylow `p` を持つとき
(a) `τ₂(M)={p}`; (b) `A₀=C_A(M_σ)` は位数 `p` で `F(M)=M_σ × A₀`; (c) `X ∈ ℰ_p¹(E)-{A₀}` で
`C_{M_σ}(X)=1` かつ `C_G(X) ⊄ M`; (d) `A₀` は `E` 内に補群 `E₀`; (e) `x ∈ M_σ#` で
`π(C_{E₀}(x)) ⊆ τ₁(M)`。(内部直積 `F(M)=M_σ×A₀` は join + 自明交叉で表現。) -/
theorem tau2_singleton_of_nonabelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G)) :
    tau2 M = {p} ∧
    (∃ A₀ : Subgroup G, A₀ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ∧
      Nat.card ↥A₀ = p ∧
      (Ch2.S08.fittingInG M = S10.Msigma M ⊔ A₀ ∧ S10.Msigma M ⊓ A₀ = ⊥) ∧
      (∀ X ∈ elemAbelianOfRank G p 1, X ≤ E → X ≠ A₀ →
        S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
        ¬ (Subgroup.centralizer (X : Set G) ≤ M)) ∧
      (∃ E₀ : Subgroup G, E₀ ≤ E ∧ A₀ ⊓ E₀ = ⊥ ∧ A₀ ⊔ E₀ = E ∧
        ∀ x ∈ S10.Msigma M, x ≠ 1 →
          ∀ r ∈ (Nat.card ↥(E₀ ⊓ Subgroup.centralizer ({x} : Set G))).primeFactors,
            r ∈ tau1 M)) := by
  sorry

/-- **BG Lemma 12.8** (mmd L3223): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `S` を `A` を含む `G` の Sylow
`p`-部分群とし `S` abelian とする。(a) `E₂` abelian normal in `E`; (b) `E₂` は `G` の Hall
`τ₂(M)`-部分群; (c) `S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E`; (d) 正規化子の鎖の等式;
(e) `X ∈ ℰ¹(E₁)` で `C_{M_σ}(X)=1` なら `X ⊆ Z(E)`; (f) `X ≤ N_G(S)` で `C_S(X), [S,X] ⊴ N_G(S)`。 -/
theorem E2_abelian_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (S : Sylow p G) (hAS : A ≤ (S : Subgroup G)) (hSab : IsMulCommutative (S : Subgroup G)) :
    (IsMulCommutative ↥E₂ ∧ E ≤ Subgroup.normalizer (E₂ : Set G)) ∧
    Ch03.IsHallSubgroup (tau2 M) E₂ ∧
    ((S : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤ Ch2.S08.fittingInG E ∧
      Ch2.S08.fittingInG E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E) ∧
    (Subgroup.normalizer (A : Set G) = Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) = Subgroup.normalizer (E₂ : Set G) ∧
      Subgroup.normalizer (E₂ : Set G) = Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) =
        Subgroup.normalizer ((Ch2.S08.fittingInG E : Subgroup G) : Set G)) ∧
    (∀ X : Subgroup G, (∃ q : ℕ, q.Prime ∧ X ∈ elemAbelianOfRank G q 1) → X ≤ E₁ →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      X ≤ E ∧ E ≤ Subgroup.centralizer (X : Set G)) ∧
    (∀ X : Subgroup G, X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer (((S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G)) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((⁅(S : Subgroup G), X⁆ : Subgroup G) : Set G)) := by
  sorry

/-- **BG Corollary 12.9** (mmd L3260): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `q ∈ τ₁(M)`, `Q ∈ ℰ_q¹(E)`,
`C_{M_σ}(Q)=1`, `[A,Q]≠1` のとき `A₀=[A,Q]`, `A₁=C_A(Q)` で
(a) `A₀ ∈ ℰ¹(A)` かつ `A₀=C_A(M_σ) ⊴ M`; (b) `A₀` は `A₁` と `G` 内で非共役; (c) `A₁ ∈ ℰ¹(A)` かつ
`C_G(A₁) ⊄ M`。 -/
theorem commutator_decomp_of_tau1_action [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : p ∈ tau2 M) (hq : q ∈ tau1 M)
    {A Q : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hCQ : S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥) (hAQ : ⁅A, Q⁆ ≠ ⊥) :
    (⁅A, Q⁆ ∈ elemAbelianOfRank G p 1 ∧ ⁅A, Q⁆ ≤ A ∧
      ⁅A, Q⁆ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ∧
      M ≤ Subgroup.normalizer ((⁅A, Q⁆ : Subgroup G) : Set G)) ∧
    (¬ ∃ g : G, MulAut.conj g • (⁅A, Q⁆ : Subgroup G) = A ⊓ Subgroup.centralizer (Q : Set G)) ∧
    ((A ⊓ Subgroup.centralizer (Q : Set G)) ∈ elemAbelianOfRank G p 1 ∧
      (A ⊓ Subgroup.centralizer (Q : Set G)) ≤ A ∧
      ¬ (Subgroup.centralizer ((A ⊓ Subgroup.centralizer (Q : Set G)) : Set G) ≤ M)) := by
  sorry

/-- **BG Corollary 12.10** (mmd L3270): (a) `M` の nilpotent `σ(M)'`-部分群は abelian;
(b) `E₂` と `E'` は abelian; (c) `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` で `E₂E₃ ⊆ C_E(A) ⊴ E` かつ
`π(E/C_E(A)) ⊆ τ₁(M)`; (d) `p ∈ σ(M)`, `P` noncyclic `p`-部分群 ⇒ `N_G(P) ⊆ M`;
(e) `x ∈ M#`, `π(⟨x⟩) ⊆ τ₂(M)`, `C_{M_σ}(x)≠1` ⇒ `ℳ(C_G(x))={M}`。 -/
theorem nilpotent_sigmaComplement_abelian [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (∀ N : Subgroup G, N ≤ M → Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) N →
      Group.IsNilpotent ↥N → IsMulCommutative ↥N) ∧
    (IsMulCommutative ↥E₂ ∧ IsMulCommutative ↥(derivedInG E)) ∧
    (∀ p : ℕ, p ∈ tau2 M → ∀ A ∈ elemAbelianOfRank G p 2, A ≤ E →
      E₂ ⊔ E₃ ≤ E ⊓ Subgroup.centralizer (A : Set G) ∧
      E ≤ Subgroup.normalizer ((E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ∧
      ∀ r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors,
        r ∈ tau1 M) ∧
    (∀ p : ℕ, p ∈ S10.sigma M → ∀ P : Subgroup G, P ≤ M → IsPGroup p ↥P →
      ¬ IsCyclic ↥P → Subgroup.normalizer (P : Set G) ≤ M) ∧
    (∀ x ∈ M, x ≠ 1 → (∀ r ∈ (orderOf x).primeFactors, r ∈ tau2 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ →
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {M}) := by
  sorry

/-- **BG Lemma 12.11** (mmd L3284): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M^* ∈ ℳ(N_G(A))` のとき
(a) `τ₂(M) ⊆ σ(M^*) - β(M^*)`; (b) `π(E/C_E(A)) ⊆ τ₁(M^*) ∪ τ₂(M^*)`;
(c) `q ∈ π(E/C_E(A)) ∩ π(C_E(A))` なら `q ∈ τ₂(M^*)`, `G` の Sylow `p` が `M^*` で正規,
`M^*` は `G` の abelian Sylow `q` を含む。 -/
theorem tau2_transfer_to_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G))) :
    tau2 M ⊆ S10.sigma Mstar \ S10.beta Mstar ∧
    (∀ r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors,
      r ∈ tau1 Mstar ∪ tau2 Mstar) ∧
    (∀ q : ℕ, q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors →
      q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors →
      q ∈ tau2 Mstar ∧
      (∃ P : Sylow p G, Mstar ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      (∃ Q : Sylow q G, (Q : Subgroup G) ≤ Mstar ∧ IsMulCommutative (Q : Subgroup G))) := by
  sorry

/-- **BG Theorem 12.12** (mmd L3306): すべての `(τ₁(M)∪τ₃(M))`-元 `e ∈ E#` で `C_{M_σ}(e)=1`
なら (a) `E` は abelian normal `A₀` を含み `∀ x ∈ M_σ#, C_E(x) ⊆ A₀`;
(b) `E` は `E` と同 exponent の `E₀` を含み `E₀M_σ` は kernel `M_σ` の Frobenius 群。 -/
theorem frobenius_factorization_of_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    (∃ A₀ : Subgroup G, A₀ ≤ E ∧ IsMulCommutative ↥A₀ ∧
      E ≤ Subgroup.normalizer ((A₀ : Subgroup G) : Set G) ∧
      ∀ x ∈ S10.Msigma M, x ≠ 1 → E ⊓ Subgroup.centralizer ({x} : Set G) ≤ A₀) ∧
    (∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent ↥E₀ = Monoid.exponent ↥E ∧
      Ch06.IsFrobeniusGroup ↥(S10.Msigma M ⊔ E₀)
        ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀))
        (E₀.subgroupOf (S10.Msigma M ⊔ E₀))) := by
  sorry

/-! ## §12 σ(M) の埋め込みと一意性 (mmd L3385-3479) -/

/-- **BG Proposition 12.15** (mmd L3387): `q ∈ σ(M)`, `X` を `M` の非自明 `q`-部分群、
`M* ∈ ℳ(N_G(X)) - {M}`、`S` を `X` を含む `M ∩ M*` の Sylow `q`-部分群とすると
(a) `M*` は `M` と非共役; (b) `N_G(S) ⊆ M`; (c) `S` は `M*` の Sylow `q`;
(d) `q ∈ σ(M*)` なら `M*=(M∩M*)M*_β`, `τ₁(M*)⊆τ₁(M)∪α(M)`, `M_β=M_α≠1`;
(e) `q ∉ σ(M*)` なら `q ∈ τ₂(M*)`, `π(M)∩σ(M*)⊆β(M*)`, `M∩M*` は `M*_σ` の補群。 -/
theorem sigma_subgroup_maximal_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q ↥X)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstarne : Mstar ≠ M) {S : Subgroup G} (hSle : S ≤ M ⊓ Mstar) (hXS : X ≤ S)
    (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → S ≤ T → S = T) :
    (¬ ∃ g : G, MulAut.conj g • M = Mstar) ∧
    Subgroup.normalizer (S : Set G) ≤ M ∧
    (∀ T : Subgroup G, T ≤ Mstar → IsPGroup q ↥T → S ≤ T → S = T) ∧
    (q ∈ S10.sigma Mstar →
      Mstar = (M ⊓ Mstar) ⊔ S10.Mbeta Mstar ∧
      tau1 Mstar ⊆ tau1 M ∪ S10.alpha M ∧
      S10.Mbeta M = S10.Malpha M ∧ S10.Malpha M ≠ ⊥) ∧
    (q ∉ S10.sigma Mstar →
      q ∈ tau2 Mstar ∧
      (∀ r ∈ (Nat.card ↥M).primeFactors, r ∈ S10.sigma Mstar → r ∈ S10.beta Mstar) ∧
      S10.Msigma Mstar ⊓ (M ⊓ Mstar) = ⊥ ∧ S10.Msigma Mstar ⊔ (M ⊓ Mstar) = Mstar) := by
  sorry

/-- For an `α(M)'`-subgroup `X` of `M` (`X ≠ 1`) with `ℳ(N_G(X)) ≠ {M}`, the centralizer
`C_{M_α}(X)` has rank `≤ 1`. Contrapositive of Lemma 10.3: rank `≥ 2` would make `C_M(X)`
uniquely maximal with unique maximal `M`; then `C_M(X) ≤ N_G(X)` (a proper subgroup of the simple
`G`) forces `N_G(X)` uniquely maximal with the same maximal `M`, i.e. `ℳ(N_G(X)) = {M}`. The
`M_α`-analogue of `rank_centralizer_Msigma_inf_le_one`; used twice in Lemma 12.18. -/
theorem rank_centralizer_Malpha_le_one_of_not_uniqueMaximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G}
    (hXM : X ≤ M) (hXne : X ≠ ⊥) (hXpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ X)
    (hMNX : maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    rank ↥(Subgroup.centralizer (X : Set G) ⊓ S10.Malpha M) ≤ 1 := by
  by_contra hcon
  have hr2 : 2 ≤ rank ↥(Subgroup.centralizer (X : Set G) ⊓ S10.Malpha M) := by omega
  have hMcoatom : IsCoatom M := mem_maximalSubgroups.mp hM
  have hU : IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M) :=
    S10.centralizer_isUniquelyMaximal_of_two_le_rank hG hM hXM hXpi hr2
  have hCN : Subgroup.centralizer (X : Set G) ⊓ M ≤ Subgroup.normalizer (X : Set G) :=
    inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
  -- `N_G(X) < ⊤` (else `X ⊴ G`, impossible in the simple group `G` for `1 ≠ X ≤ M < ⊤`).
  have hNXlt : Subgroup.normalizer (X : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hNtop
    haveI hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal X inferInstance with hXbot | hXtop
    · exact hXne hXbot
    · exact hMcoatom.1 (top_le_iff.mp (hXtop ▸ hXM))
  have hUNX : IsUniquelyMaximal (Subgroup.normalizer (X : Set G)) := hU.of_le_of_lt_top hCN hNXlt
  -- the unique maximal of `N_G(X)` is `M`.
  have huniqNX : hUNX.uniqueMaximalSubgroup = M :=
    (hU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hUNX.uniqueMaximalSubgroup_isCoatom
        (hCN.trans hUNX.le_uniqueMaximalSubgroup)).trans
      (hU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hMcoatom inf_le_right).symm
  exact hMNX (hUNX.maximalSubgroupsContaining_eq_singleton.trans (by rw [huniqNX]))

/-- For `p ∈ τ₁(M)` and a nonidentity `p`-subgroup `P ≤ M`, the normalizer `N_G(P)` is not
uniquely contained in `M`: `ℳ(N_G(P)) ≠ {M}`. If it were `{M}`, then `M ∈ ℳ(N_G(P))` and Lemma
12.2(a) would give `p ∈ σ(M) ∪ τ₂(M)`, contradicting `p ∈ τ₁(M)` (`τ₁ ∩ σ = ∅`, and `r_p(M) = 1 ≠ 2
= r_p(M)` if `p ∈ τ₂`). Supplies the input `ℳ(N_G(P)) ≠ {M}` for the rank bound `(12.6)` in
Lemma 12.18(a). -/
theorem maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1 [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ}
    [Fact p.Prime] (hp : p ∈ tau1 M) {P : Subgroup G} (hPM : P ≤ M) (hPne : P ≠ ⊥)
    (hPp : IsPGroup p ↥P) :
    maximalSubgroupsContaining (Subgroup.normalizer (P : Set G)) ≠ {M} := by
  intro hsingle
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G)) := by
    rw [hsingle]; exact Set.mem_singleton M
  rcases prime_mem_sigma_or_tau2 hG hM hPM hPne hPp hMmem with hσ | hτ2
  · exact hp.1 hσ
  · exact absurd (hτ2.2.symm.trans hp.2.2) (by norm_num)

/-- **Thompson critical-subgroup mechanism for Lemma 12.18(a)** (BG Theorem 1.13). If a `q`-group
`Q` normalizes but does not centralize an `r`-group `R` (`q ≠ r`, ambient order odd), then `R` has
a characteristic subgroup `R₁` of exponent `r` that `Q` does not centralize either. Theorem 1.13
supplies a characteristic `R₁ ⊴ R` of exponent `r` with `C_{Aut R}(R₁)` an `r`-group; were `Q` to
centralize `R₁`, conjugation would land each `x ∈ Q` in `C_{Aut R}(R₁)`, so (coprimality of
`q`-order and `r`-order) the induced automorphism is trivial, forcing `Q` to centralize all of
`R`. -/
theorem exists_charSubgroup_exponent_not_centralized [Finite G]
    (hodd : Odd (Nat.card G)) {q r : ℕ} [Fact q.Prime] [Fact r.Prime] (hqr : q ≠ r)
    {R Q : Subgroup G} (hRr : IsPGroup r ↥R) (hRne : R ≠ ⊥)
    (hQq : IsPGroup q ↥Q) (hQnorm : Q ≤ Subgroup.normalizer (R : Set G))
    (hnc : ¬ Q ≤ Subgroup.centralizer (R : Set G)) :
    ∃ R₁ : Subgroup G, R₁ ≤ R ∧ (R₁.subgroupOf R).Characteristic ∧
      Monoid.exponent ↥R₁ = r ∧ ¬ Q ≤ Subgroup.centralizer (R₁ : Set G) := by
  classical
  haveI : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
  -- `r ∣ |G|`, hence `r` is odd, so `r ≠ 2`.
  have hr_dvd : r ∣ Nat.card G := by
    obtain ⟨n, hn⟩ := hRr.exists_card_eq
    have hcard1 : 1 < Nat.card ↥R := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; omega
    exact (hn ▸ dvd_pow_self r hn0).trans (Subgroup.card_subgroup_dvd_card R)
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hodd
    obtain ⟨c, hc⟩ := hr_dvd
    omega
  -- Theorem 1.13 applied to the `r`-group `↥R`.
  obtain ⟨H, hHchar, -, -, hHexp, hHaut⟩ :=
    OddOrder.BG.Ch1.S01.thompson_critical_omega (G := ↥R) hr2 hRr
  set R₁ : Subgroup G := H.map R.subtype with hR₁_def
  have hR₁R : R₁ ≤ R := Subgroup.map_subtype_le H
  have hsubgroupOf : R₁.subgroupOf R = H :=
    Subgroup.comap_map_eq_self_of_injective R.subtype_injective H
  refine ⟨R₁, hR₁R, ?_, ?_, ?_⟩
  · rw [hsubgroupOf]; exact hHchar
  · rw [hR₁_def, ← Monoid.exponent_eq_of_mulEquiv
      (Subgroup.equivMapOfInjective H R.subtype R.subtype_injective)]
    exact hHexp
  · -- if `Q` centralized `R₁`, conjugation would be trivial on `R`.
    intro hQcent
    apply hnc
    letI act : MulDistribMulAction ↥Q ↥R :=
      MulDistribMulAction.compHom
        (M := ↥(Subgroup.normalizer (R : Set G))) ↥R (Subgroup.inclusion hQnorm)
    set φ : ↥Q →* MulAut ↥R := MulDistribMulAction.toMulAut ↥Q ↥R with hφ
    have hφ_coe : ∀ (a : ↥Q) (x : ↥R),
        (R.subtype ((φ a) x)) = (↑a) * (R.subtype x) * (↑a)⁻¹ := fun _ _ => rfl
    -- each `a ∈ Q` induces the trivial automorphism of `R`.
    have hφ1 : ∀ a : ↥Q, φ a = 1 := by
      intro a
      have hmem : φ a ∈ autCentralizer H := by
        rw [mem_autCentralizer]
        intro h hh
        apply R.subtype_injective
        rw [hφ_coe]
        have hR1mem : (R.subtype h : G) ∈ R₁ := Subgroup.mem_map_of_mem R.subtype hh
        have hcomm := Subgroup.mem_centralizer_iff.mp (hQcent a.2) (R.subtype h) hR1mem
        rw [← hcomm]; group
      have hord_r : ∃ m, orderOf (φ a) = r ^ m := by
        obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hHaut ⟨φ a, hmem⟩
        refine ⟨m, ?_⟩
        rw [← hm]
        exact orderOf_injective (autCentralizer H).subtype
          (autCentralizer H).subtype_injective ⟨φ a, hmem⟩
      have hord_dvd : orderOf (φ a) ∣ orderOf a := orderOf_map_dvd φ a
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQq a
      obtain ⟨m, hm⟩ := hord_r
      have hcoprq : Nat.Coprime r q := (Nat.coprime_primes Fact.out Fact.out).mpr hqr.symm
      have hcop : Nat.Coprime (r ^ m) (q ^ k) := (hcoprq.pow_left m).pow_right k
      have hdvd : r ^ m ∣ q ^ k := by rw [← hm, ← hk]; exact hord_dvd
      have hr1 : r ^ m = 1 := by
        have h := Nat.dvd_gcd (dvd_refl (r ^ m)) hdvd
        rwa [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h
      have hord1 : orderOf (φ a) = 1 := by rw [hm, hr1]
      exact orderOf_eq_one_iff.mp hord1
    -- conjugation by every `x ∈ Q` fixes every `y ∈ R`, i.e. `Q ≤ C_G(R)`.
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hfix := hφ_coe ⟨x, hx⟩ ⟨y, hy⟩
    rw [hφ1 ⟨x, hx⟩] at hfix
    simp only [MulAut.one_apply] at hfix
    have hyx : y = x * y * x⁻¹ := hfix
    calc y * x = (x * y * x⁻¹) * x := by rw [← hyx]
      _ = x * y := by group

/-- **PQ-invariant Sylow subgroup of `M_α` for Lemma 12.18(a)**. For `r ∈ α(M)` and an
`α(M)'`-subgroup `X ≤ M`, `M_α` has an `X`-invariant Sylow `r`-subgroup `R` with `r(R) ≥ 3`
containing any prescribed `X`-invariant `r`-subgroup `P₀` of `M_α`, since `R` carries the full
`r`-rank `r_r(M) ≥ 3` of `M` (`r ∈ α(M)` ⟹ a Sylow `r` of `M` lies in the Hall `α`-subgroup
`M_α`). The coprime-action construction mirrors Lemma 10.3
(`aInvariant_pSubgroup_le_aInvariant_sylow`). Applied with `X = P ⊔ Q` and `P₀ = ⊥`
(first conjunct) resp. `P₀ = ⟨z⟩` (second conjunct) in Lemma 12.18(a). -/
theorem exists_invariant_sylow_Malpha_rank_three [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {r : ℕ} [Fact r.Prime]
    (hrα : r ∈ S10.alpha M) {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ X) {P₀ : Subgroup G}
    (hP₀a : P₀ ≤ S10.Malpha M) (hP₀r : IsPGroup r ↥P₀)
    (hP₀inv : X ≤ Subgroup.normalizer (P₀ : Set G)) :
    ∃ R : Subgroup G, R ≤ S10.Malpha M ∧ IsPGroup r ↥R ∧
      X ≤ Subgroup.normalizer (R : Set G) ∧ 3 ≤ rank ↥R ∧ P₀ ≤ R := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI : IsSolvable ↥(S10.Malpha M) :=
    solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe (S10.Malpha_le M)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (S10.Malpha_le M)).surjective
  have hX_norm_Ma : X ≤ Subgroup.normalizer (S10.Malpha M : Set G) :=
    hXM.trans (le_normalizer_opiCoreInG (S10.alpha M) M)
  have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥(S10.Malpha M)) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (S10.alpha M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne' hXpi
      (fun q hq hqc => hqc (S10.Malpha_isPiGroup M q hq))
  letI act : MulDistribMulAction ↥X ↥(S10.Malpha M) :=
    MulDistribMulAction.compHom
      (M := ↥(Subgroup.normalizer (S10.Malpha M : Set G))) ↥(S10.Malpha M)
      (Subgroup.inclusion hX_norm_Ma)
  set φ : ↥X →* MulAut ↥(S10.Malpha M) :=
    MulDistribMulAction.toMulAut ↥X ↥(S10.Malpha M) with hφ
  have hφ_coe : ∀ (a : ↥X) (x : ↥(S10.Malpha M)),
      ((S10.Malpha M).subtype ((φ a) x)) = (↑a) * ((S10.Malpha M).subtype x) * (↑a)⁻¹ :=
    fun _ _ => rfl
  have hφ_inv_coe : ∀ (a : ↥X) (x : ↥(S10.Malpha M)),
      ((S10.Malpha M).subtype (((φ a)⁻¹) x)) = (↑a)⁻¹ * ((S10.Malpha M).subtype x) * (↑a) := by
    intro a x
    rw [← map_inv]; simpa using hφ_coe a⁻¹ x
  have hP₀'_pgrp : IsPGroup r ↥(P₀.subgroupOf (S10.Malpha M)) :=
    hP₀r.of_equiv (Subgroup.subgroupOfEquivOfLe hP₀a).symm
  have hP₀'_inv : Ch03.IsAInvariant φ (P₀.subgroupOf (S10.Malpha M)) := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hcoe : ((φ a) g : G) = (↑a) * (g : G) * (↑a)⁻¹ := hφ_coe a g
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.mp (hP₀inv a.2) _).mp hg
  obtain ⟨S, hS_inv, hP₀S⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow (G := ↥(S10.Malpha M)) (A := ↥X)
      (φ := φ) hcop (Or.inr inferInstance) (p := r) (P := P₀.subgroupOf (S10.Malpha M))
      hP₀'_pgrp hP₀'_inv
  set R : Subgroup G := (S : Subgroup ↥(S10.Malpha M)).map (S10.Malpha M).subtype with hRdef
  have hR_pgrp : IsPGroup r ↥R :=
    S.2.of_equiv (Subgroup.equivMapOfInjective _ _ (S10.Malpha M).subtype_injective)
  have hX_norm_R : X ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      exact ⟨(φ ⟨a, ha⟩) x, hS_inv.smul_mem ⟨a, ha⟩ hxS, hφ_coe ⟨a, ha⟩ x⟩
    · rintro ⟨x, hxS, hx⟩
      refine ⟨((φ ⟨a, ha⟩)⁻¹) x, hS_inv.inv_smul_mem ⟨a, ha⟩ hxS, ?_⟩
      rw [hφ_inv_coe ⟨a, ha⟩ x, hx]
      change a⁻¹ * (a * y * a⁻¹) * a = y
      group
  have eR : ↥(S : Subgroup ↥(S10.Malpha M)) ≃* ↥R :=
    hRdef ▸ Subgroup.equivMapOfInjective _ (S10.Malpha M).subtype (S10.Malpha M).subtype_injective
  have hRpr : pRank ↥M r ≤ pRank ↥R r := by
    have h1 : pRank ↥(S : Subgroup ↥(S10.Malpha M)) r ≤ pRank ↥R r :=
      pRank_le_of_injective (f := eR.toMonoidHom) eR.injective
    rw [pRank_sylow_eq S] at h1
    obtain ⟨T⟩ : Nonempty (Sylow r ↥M) := inferInstance
    have hTle : ((T : Subgroup ↥M).map M.subtype) ≤ S10.Malpha M :=
      S10.sylow_le_Malpha_of_mem_alpha_of_isHall (S10.Malpha_isHall hG hM) hrα T
    have eT : ↥(T : Subgroup ↥M) ≃* ↥((T : Subgroup ↥M).map M.subtype) :=
      Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective
    have hTeq : pRank ↥M r = pRank ↥((T : Subgroup ↥M).map M.subtype) r := by
      rw [← pRank_sylow_eq T]
      exact le_antisymm (pRank_le_of_injective (f := eT.toMonoidHom) eT.injective)
        (pRank_le_of_injective (f := eT.symm.toMonoidHom) eT.symm.injective)
    have hTpr : pRank ↥((T : Subgroup ↥M).map M.subtype) r ≤ pRank ↥(S10.Malpha M) r :=
      pRank_le_of_injective (f := Subgroup.inclusion hTle) (Subgroup.inclusion_injective hTle)
    omega
  refine ⟨R, Subgroup.map_subtype_le _, hR_pgrp, hX_norm_R,
    le_trans (le_trans ((S10.mem_alpha_iff M r).mp hrα).2 hRpr) (pRank_le_rank r), ?_⟩
  calc P₀ = (P₀.subgroupOf (S10.Malpha M)).map (S10.Malpha M).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hP₀a).symm
    _ ≤ R := Subgroup.map_mono hP₀S

/-- For subgroups `A`, `B` with `A` normalizing `B` and `A ⊓ B = ⊥`, `|A ⊔ B| = |A|·|B|`
(applying the disjoint-normal product formula inside `↥(A ⊔ B)`, where `B` is normal). Used in
Lemma 12.18(a) to confine the primes of `P ⊔ Q` (resp. `Q ⊔ R₁`) to `{p, q}` (resp. `{q, r}`);
public because the second-conjunct file `S12_Lemma1218` reuses it for `Q ⊔ N`. -/
theorem card_sup_eq_mul_of_le_normalizer_of_disjoint {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hdisj : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hBle : B ≤ A ⊔ B := le_sup_right
  haveI hBn : (B.subgroupOf (A ⊔ B)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have hdisj' : A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxA hxB
    have hxAB : (x : G) ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [hdisj, Subgroup.mem_bot] at hxAB
    rw [Subgroup.mem_bot]; exact Subtype.ext hxAB
  have htop : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAle hBle, Subgroup.subgroupOf_self]
  have h := OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal
    (T := A.subgroupOf (A ⊔ B)) (M := B.subgroupOf (A ⊔ B)) hdisj'
  rw [htop, Nat.card_congr (Subgroup.topEquiv).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv] at h
  exact h

/-- **Fixed-point-free decomposition for Lemma 12.18(a)**. If `P` normalizes both `Q` and `R`,
`Q` normalizes `R`, `Q ⊓ R = ⊥`, and `P` centralizes nothing nontrivial in either `Q` or `R`,
then `P` centralizes nothing nontrivial in `Q ⊔ R`. (Each `g ∈ Q ⊔ R` factors as `u·v`,
`u ∈ Q`, `v ∈ R`; if `g` is `P`-central then `Q ⊓ R = ⊥` forces `u, v` to be `P`-central, hence
trivial.) Provides the fixed-point-freeness hypothesis for Theorem 3.7 in Lemma 12.18(a). -/
theorem inf_centralizer_sup_eq_bot_of_le_normalizer {G : Type*} [Group G]
    {P Q R : Subgroup G} (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPR : P ≤ Subgroup.normalizer (R : Set G)) (hQR : Q ≤ Subgroup.normalizer (R : Set G))
    (hdisj : Q ⊓ R = ⊥)
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hCR : R ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    (Q ⊔ R) ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgQR, hgC⟩ := hg
  rw [Subgroup.mem_centralizer_iff] at hgC
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Q R hQR, Set.mem_mul] at hgQR
  obtain ⟨u, hu, v, hv, rfl⟩ := hgQR
  have key : ∀ a ∈ P, a * u * a⁻¹ = u ∧ a * v * a⁻¹ = v := by
    intro a ha
    have hau : a * u * a⁻¹ ∈ Q := (Subgroup.mem_set_normalizer_iff.mp (hPQ ha) u).mp hu
    have hav : a * v * a⁻¹ ∈ R := (Subgroup.mem_set_normalizer_iff.mp (hPR ha) v).mp hv
    have hcomm : a * (u * v) = (u * v) * a := hgC a ha
    have hconj : (a * u * a⁻¹) * (a * v * a⁻¹) = u * v := by
      have h1 : a * (u * v) * a⁻¹ = u * v := by rw [hcomm]; group
      calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
        _ = u * v := h1
    have hwQ : u⁻¹ * (a * u * a⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hu) hau
    have hwR : u⁻¹ * (a * u * a⁻¹) ∈ R := by
      have h2 : a * u * a⁻¹ = u * v * (a * v * a⁻¹)⁻¹ := by
        rw [eq_comm, mul_inv_eq_iff_eq_mul]; exact hconj.symm
      have heq : u⁻¹ * (a * u * a⁻¹) = v * (a * v * a⁻¹)⁻¹ := by rw [h2]; group
      rw [heq]; exact R.mul_mem hv (R.inv_mem hav)
    have hw1 : u⁻¹ * (a * u * a⁻¹) = 1 := by
      have hmem : u⁻¹ * (a * u * a⁻¹) ∈ Q ⊓ R := ⟨hwQ, hwR⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    have hu_fix : a * u * a⁻¹ = u := by rw [inv_mul_eq_one] at hw1; exact hw1.symm
    refine ⟨hu_fix, ?_⟩
    rw [hu_fix] at hconj
    exact mul_left_cancel hconj
  have huC : u ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro a ha
    have h := (key a ha).1; rwa [mul_inv_eq_iff_eq_mul] at h
  have hvC : v ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro a ha
    have h := (key a ha).2; rwa [mul_inv_eq_iff_eq_mul] at h
  have hu1 : u = 1 := by
    have hmem : u ∈ Q ⊓ Subgroup.centralizer (P : Set G) := ⟨hu, huC⟩
    rwa [hCQ, Subgroup.mem_bot] at hmem
  have hv1 : v = 1 := by
    have hmem : v ∈ R ⊓ Subgroup.centralizer (P : Set G) := ⟨hv, hvC⟩
    rwa [hCR, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot, hu1, hv1, mul_one]

/-- **BG Lemma 12.18(a), first conclusion**: under the hypotheses of Lemma 12.18 with `M_α ≠ 1`
and `q ∉ α(M)`, we have `C_{M_α}(P) ≠ 1`. (The order count `(12.7)` is unnecessary for this half:
Theorem 3.7 already yields `C_{R₁}(P) ≠ 1` for the characteristic subgroup `R₁ ⊆ R ⊆ M_α`, whence
`C_{M_α}(P) ⊇ C_{R₁}(P) ≠ 1`.) -/
theorem tau1_Malpha_centralizer_P_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) (hp : p ∈ tau1 M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPM : P ≤ M) {Q : Subgroup G} (hQM : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q ↥Q)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQP : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hαne : S10.Malpha M ≠ ⊥) (hqα : q ∉ S10.alpha M) :
    S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- `P` facts.
  obtain ⟨hPea, hPcard1⟩ := mem_elemAbelianOfRank.mp hP
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have hPcard : Nat.card ↥P = p := by rw [hPcard1, pow_one]
  have hPne : P ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hPcard
    have := (Fact.out : p.Prime).one_lt; omega
  have hpα : p ∉ S10.alpha M := by
    intro hpa; have h3 := ((S10.mem_alpha_iff M p).mp hpa).2; rw [hp.2.2] at h3; omega
  -- `α(M)'`-subgroup hypotheses for `P` and `Q`.
  have hPpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ P := by
    intro s hs; rw [hPcard, (Fact.out : p.Prime).primeFactors, Finset.mem_singleton] at hs
    exact hs ▸ hpα
  have hQpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ Q := by
    intro s hs
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    rw [hk] at hs
    have hsp := Nat.prime_of_mem_primeFactors hs
    have hsq : s = q :=
      (Nat.prime_dvd_prime_iff_eq hsp Fact.out).mp (hsp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hs))
    exact hsq ▸ hqα
  -- `(12.6)` and `(12.5)`.
  have h126 : rank ↥(Subgroup.centralizer (P : Set G) ⊓ S10.Malpha M) ≤ 1 :=
    rank_centralizer_Malpha_le_one_of_not_uniqueMaximal hG hM hPM hPne hPpi
      (maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1 hG hM hp hPM hPne hPp)
  have h125 : rank ↥(Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M) ≤ 1 :=
    rank_centralizer_Malpha_le_one_of_not_uniqueMaximal hG hM hQM hQne hQpi hMNQ
  -- some `r ∈ α(M)`.
  obtain ⟨r, hrα⟩ : ∃ r, r ∈ S10.alpha M := by
    have hne1 : Nat.card ↥(S10.Malpha M) ≠ 1 := fun h => hαne (Subgroup.card_eq_one.mp h)
    obtain ⟨r, hrp, hrdvd⟩ := (Nat.card ↥(S10.Malpha M)).exists_prime_and_dvd hne1
    exact ⟨r, S10.Malpha_isPiGroup M r (Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, Nat.card_pos.ne'⟩)⟩
  haveI : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors ((S10.mem_alpha_iff M r).mp hrα).1⟩
  have hqr : q ≠ r := fun h => hqα (h ▸ hrα)
  have hrp_ne : r ≠ p := fun h => hpα (h ▸ hrα)
  -- `X := P ⊔ Q` is an `α(M)'`-subgroup of `M`.
  have hXM : (P ⊔ Q : Subgroup G) ≤ M := sup_le hPM hQM
  have hPQdisj : P ⊓ Q = ⊥ := by
    apply OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hPp
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqp).pow_left k
  have hXcard : Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hQinv hPQdisj
  have hXpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ (P ⊔ Q) := by
    intro s hs
    rw [hXcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hs
    rcases Finset.mem_union.mp hs with h | h
    · exact hPpi s h
    · exact hQpi s h
  -- `R` = a `PQ`-invariant Sylow `r`-subgroup of `M_α` with `r(R) ≥ 3`.
  obtain ⟨R, hRMa, hRr, hXnormR, hRrank, -⟩ :=
    exists_invariant_sylow_Malpha_rank_three hG hM hrα hXM hXpi bot_le
      (IsPGroup.of_card (n := 0) (by simp))
      (fun x _ => Subgroup.mem_normalizer_iff.mpr fun h => by
        simp [Subgroup.mem_bot, conj_eq_one_iff])
  have hPnormR : P ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hXnormR
  have hQnormR : Q ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hXnormR
  have hRMle : R ≤ M := hRMa.trans (S10.Malpha_le M)
  -- `Q` does not centralize `R` (else `R ≤ C_{M_α}(Q)` has rank `≥ 3 > 1`).
  have hQncR : ¬ Q ≤ Subgroup.centralizer (R : Set G) := by
    intro hQcR
    have hRleCQ : R ≤ Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M := by
      refine le_inf (fun x hxR => ?_) hRMa
      rw [Subgroup.mem_centralizer_iff]
      intro y hyQ
      have hy := hQcR hyQ
      rw [Subgroup.mem_centralizer_iff] at hy
      exact (hy x hxR).symm
    have hrk : (3 : ℕ) ≤ rank ↥(Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M) :=
      le_trans hRrank (rank_le_of_injective (Subgroup.inclusion_injective hRleCQ))
    omega
  have hRne : R ≠ ⊥ := by
    rintro rfl
    refine hQncR fun x _ => ?_
    rw [Subgroup.coe_bot, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy; rw [one_mul, mul_one]
  -- `R₁` = Thompson characteristic subgroup of `R`, exponent `r`, not centralized by `Q`.
  obtain ⟨R₁, hR₁R, hR₁char, hR₁exp, hQncR₁⟩ :=
    exists_charSubgroup_exponent_not_centralized hG.odd hqr hRr hRne hQq hQnormR hQncR
  haveI : (R₁.subgroupOf R).Characteristic := hR₁char
  have hR₁r : IsPGroup r ↥R₁ := by
    obtain ⟨n, hn⟩ := hRr.exists_card_eq
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Fact.out).mp (hn ▸ Subgroup.card_dvd_of_le hR₁R)
    exact IsPGroup.of_card hm
  have hR₁M : R₁ ≤ M := hR₁R.trans hRMle
  have hNRle : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (R₁ : Set G) := by
    have h := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
      (K := R) (W := R₁.subgroupOf R)
    rwa [Subgroup.map_subgroupOf_eq_of_le hR₁R] at h
  have hPnormR₁ : P ≤ Subgroup.normalizer (R₁ : Set G) := hPnormR.trans hNRle
  have hQnormR₁ : Q ≤ Subgroup.normalizer (R₁ : Set G) := hQnormR.trans hNRle
  have hQR₁disj : Q ⊓ R₁ = ⊥ := by
    apply OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hQq
    obtain ⟨k, hk⟩ := hR₁r.exists_card_eq
    rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqr.symm).pow_left k
  -- `QR₁` is not nilpotent (`Q` does not centralize `R₁`, but coprime orders would commute).
  have hQR₁nn : ¬ Group.IsNilpotent ↥(Q ⊔ R₁) := by
    intro hnil
    apply hQncR₁
    intro x hxQ
    rw [Subgroup.mem_centralizer_iff]
    intro y hyR₁
    have hx' : x ∈ Q ⊔ R₁ := Subgroup.mem_sup_left hxQ
    have hy' : y ∈ Q ⊔ R₁ := Subgroup.mem_sup_right hyR₁
    have hoxq : ∃ a, orderOf x = q ^ a := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hQq ⟨x, hxQ⟩
      exact ⟨a, by rw [← ha]; exact orderOf_injective Q.subtype Q.subtype_injective ⟨x, hxQ⟩⟩
    have hoyr : ∃ b, orderOf y = r ^ b := by
      obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hR₁r ⟨y, hyR₁⟩
      exact ⟨b, by rw [← hb]; exact orderOf_injective R₁.subtype R₁.subtype_injective ⟨y, hyR₁⟩⟩
    have hcop : Nat.Coprime (orderOf (⟨x, hx'⟩ : ↥(Q ⊔ R₁))) (orderOf (⟨y, hy'⟩ : ↥(Q ⊔ R₁))) := by
      have hxo : orderOf (⟨x, hx'⟩ : ↥(Q ⊔ R₁)) = orderOf x :=
        (orderOf_injective (Q ⊔ R₁).subtype (Q ⊔ R₁).subtype_injective ⟨x, hx'⟩).symm
      have hyo : orderOf (⟨y, hy'⟩ : ↥(Q ⊔ R₁)) = orderOf y :=
        (orderOf_injective (Q ⊔ R₁).subtype (Q ⊔ R₁).subtype_injective ⟨y, hy'⟩).symm
      rw [hxo, hyo]
      obtain ⟨a, ha⟩ := hoxq; obtain ⟨b, hb⟩ := hoyr
      rw [ha, hb]
      exact (((Nat.coprime_primes Fact.out Fact.out).mpr hqr).pow_left a).pow_right b
    have hcomm := S10.commute_of_coprime_orderOf_of_isNilpotent hcop
    have hxy : x * y = y * x := by simpa using congrArg Subtype.val hcomm
    exact hxy.symm
  -- `C_{R₁}(P) ≠ 1` (else Theorem 3.7 makes `QR₁` nilpotent).
  have hCR₁Pne : R₁ ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
    intro hCR₁P
    apply hQR₁nn
    have hFPFbot : (Q ⊔ R₁) ⊓ Subgroup.centralizer (P : Set G) = ⊥ :=
      inf_centralizer_sup_eq_bot_of_le_normalizer hQinv hPnormR₁ hQnormR₁ hQR₁disj hCQP hCR₁P
    have hYM : (Q ⊔ R₁) ⊔ P ≤ M := sup_le (sup_le hQM hR₁M) hPM
    haveI : IsSolvable ↥((Q ⊔ R₁) ⊔ P) :=
      solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYM).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hYM).surjective
    have hQR₁card : Nat.card ↥(Q ⊔ R₁) = Nat.card ↥Q * Nat.card ↥R₁ :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint hQnormR₁ hQR₁disj
    have hQR₁cop : (Nat.card ↥(Q ⊔ R₁)).Coprime p := by
      rw [hQR₁card]
      have h1 : (Nat.card ↥Q).Coprime p := by
        obtain ⟨k, hk⟩ := hQq.exists_card_eq
        rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqp).pow_left k
      have h2 : (Nat.card ↥R₁).Coprime p := by
        obtain ⟨k, hk⟩ := hR₁r.exists_card_eq
        rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hrp_ne).pow_left k
      exact Nat.coprime_comm.mp
        (Nat.Coprime.mul_right (Nat.coprime_comm.mp h1) (Nat.coprime_comm.mp h2))
    refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      (N := Q ⊔ R₁) (R := P) ?_ ?_ ?_ hPne ⟨p, Fact.out, hPcard⟩ ?_
    · exact (le_inf hQinv hPnormR₁).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Q R₁)
    · rw [disjoint_iff, inf_comm]
      exact OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hPp hQR₁cop
    · exact fun h => hQne (le_bot_iff.mp (le_sup_left.trans h.le))
    · intro a haP ha1 n hn hn1 hfix
      have hcomm_an : Commute a n := mul_inv_eq_iff_eq_mul.mp hfix
      have hzpa : Subgroup.zpowers a = P := by
        have hle : Subgroup.zpowers a ≤ P := by rw [Subgroup.zpowers_le]; exact haP
        have horder : orderOf a = p := by
          have hdvd : orderOf a ∣ p := hPcard ▸ Subgroup.orderOf_dvd_natCard P haP
          rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) ha1
          · exact h
        have hcard : Nat.card ↥(Subgroup.zpowers a) = Nat.card ↥P := by
          rw [Nat.card_zpowers, horder, hPcard]
        exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
      have hnC : n ∈ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hbP
        rw [← hzpa] at hbP
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbP
        exact (hcomm_an.zpow_left k).eq
      have hmem : n ∈ (Q ⊔ R₁) ⊓ Subgroup.centralizer (P : Set G) := ⟨hn, hnC⟩
      rw [hFPFbot, Subgroup.mem_bot] at hmem
      exact hn1 hmem
  -- `C_{M_α}(P) ⊇ C_{R₁}(P) ≠ 1`.
  intro hCMaP
  apply hCR₁Pne
  rw [eq_bot_iff]
  calc R₁ ⊓ Subgroup.centralizer (P : Set G)
      ≤ S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) :=
        inf_le_inf_right _ (hR₁R.trans hRMa)
    _ = ⊥ := hCMaP

/- **BG Lemma 12.18** `tau1_Malpha_interaction` lives in the dedicated leaf
`S12_Lemma1218.lean` (second conjunct of (a) is the hard core; part (b) reduction there). -/

end OddOrder.BG.Ch3.S12
