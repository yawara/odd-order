/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
import OddOrder.BG.Ch1_Preliminary.S03d_Thm34
import OddOrder.BG.Ch1_Preliminary.S06_Additional

/-!
# BG Theorem 3.8 — `⁅K, R⁆ ⊆ F(K)` for a coprime action (LMS LNS 188, §3, mmd L1221-1259)

**Statement.** Let `G = KR` be a solvable group of odd order with `K ⊴ G` and
1. `(|R|, |K|) = 1`;
2. `C_K(x) = C_K(R)` for all `x ∈ R^#`; and
3. `C_{F(K)}(R) = 1`.

Then `⁅K, R⁆ ⊆ F(K)`.

This is the unique §3 prerequisite of BG Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) that was
not yet formalized (the `S03` group covers 3.4/3.5/3.6/3.7/3.10 only).  See `issues/8011-thm38.md`
for the full proof plan (mmd L1221-1259, induction on `|RK|` + a chief-factor module argument).

## This file (in progress, issue 8011)

The proof's step 4 (chief-factor dichotomy) is structurally identical to BG Theorem 3.7's
(`S03c_Thm37`), so most of the chief-factor machinery is reused.  The `q = p` case is a direct
citation of `S03c.samePrime_kernel_le_chiefFactorCentralizer`; the `q ≠ p` case (leaf B, the
linchpin) replaces Theorem 3.7's Frobenius argument with **Theorem 3.4** (`S03d.thm34`).  This
file currently lands the abstract `q ≠ p` core
(`commutator_acts_trivially_via_thm34`), the `thm34`-analog of
`S03c.kernel_acts_trivially_of_coprime_fixedPointFree`.
-/

namespace OddOrder.BG.Ch1.S03h

open scoped Pointwise

/-- **Abstract `q ≠ p` core for BG Theorem 3.8** (the `thm34`-analog of
`S03c.kernel_acts_trivially_of_coprime_fixedPointFree`).  Let `G = KR` be a finite solvable group
of odd order acting on a finite abelian group `M` that is an `𝔽_s`-vector space, with `K ⊴ G`
complementing the prime-order `R`, with `(|K|, |R|) = 1` and `s ∤ |G|`.  If `R` acts in a
fixed-point-free manner on `M` (`C_M(R) = 1`), then the commutator `⁅R, K⁆` acts trivially on `M`.

Proof: present the action as a representation `ρ : Representation (ZMod s) G (Additive M)`
(`Representation.ofDistribMulAction`); the fixed-point-freeness `C_M(R) = 1` becomes
`C_{Additive M}(R) = 0`, and **BG Theorem 3.4** (`S03d.thm34`) gives `ρ g = 1` for every
`g ∈ ⁅R, K⁆`, i.e. `g` acts trivially.  Mirrors
`S03c.kernel_acts_trivially_of_coprime_fixedPointFree` with the Frobenius input replaced by the
`(KR, R prime)` Theorem 3.4 hypotheses. -/
theorem commutator_acts_trivially_via_thm34 {s : ℕ} [Fact s.Prime]
    {G M : Type*} [Finite G] [Group G] [IsSolvable G] [CommGroup M] [Finite M]
    [MulDistribMulAction G M] [Module (ZMod s) (Additive M)]
    {K R : Subgroup G} [K.Normal]
    (hcompl : K.IsComplement' R)
    (hHall : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R))
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p)
    (hodd : Odd (Nat.card G))
    (hchar : ¬ s ∣ Nat.card G)
    (hFPF : ∀ m : M, (∀ r : R, (r : G) • m = m) → m = 1) :
    ∀ x ∈ ⁅R, K⁆, ∀ m : M, (x : G) • m = m := by
  set ρ : Representation (ZMod s) G (Additive M) :=
    Representation.ofDistribMulAction (ZMod s) G (Additive M) with hρ
  have hρ_apply : ∀ (g : G) (a : Additive M), ρ g a = g • a := by
    intro g a; rw [hρ]; rfl
  have hchar' : (Nat.card G : ZMod s) ≠ 0 :=
    fun h => hchar ((ZMod.natCast_eq_zero_iff _ _).1 h)
  haveI : FiniteDimensional (ZMod s) (Additive M) := Module.Finite.of_finite
  -- `C_M(R) = 1` ⟹ the representation's `R`-invariants are `0`.
  have hCR : ∀ v : Additive M, (∀ r : R, ρ (r : G) v = v) → v = 0 := by
    intro v hv
    have hfix : ∀ r : R, (r : G) • Additive.toMul v = Additive.toMul v := by
      intro r
      have h := hv r
      rw [hρ_apply] at h
      exact congrArg Additive.toMul h
    have h0 : Additive.ofMul (Additive.toMul v) = Additive.ofMul (1 : M) :=
      congrArg Additive.ofMul (hFPF _ hfix)
    simpa using h0
  -- BG Theorem 3.4: every `g ∈ ⁅R, K⁆` acts as the identity on `M`.
  have hKtriv := S03d.thm34 ρ K R hcompl hHall hRp hodd hchar' hCR
  intro x hx m
  have happ : ρ (x : G) (Additive.ofMul m) = Additive.ofMul m := by
    rw [hKtriv x hx]; rfl
  rw [hρ_apply] at happ
  exact congrArg Additive.toMul happ

open OddOrder.GroupTheory in
/-- **Coprime (`q ≠ p`) branch of BG Theorem 3.8's chief-factor analysis** (leaf B).  For a
`G`-chief factor `X/Y` elementary abelian of prime `s`, with `L ⊴ G` centralizing `X/Y` and `R`
acting fixed-point-freely on `X/Y`, if `G = KR` modulo `L` satisfies the Theorem 3.4 hypotheses
(`K/L` complements the prime-order `R/L`, coprime orders, `G/L` odd, `s ∤ |G/L|`), then `⁅R, K⁆`
centralizes `X/Y` (i.e. `⁅R, K⁆ ≤ chiefFactorCentralizer X Y`).  The `q ≠ p` analog of
`S03c.coprime_kernel_le_chiefFactorCentralizer`, with the Frobenius argument replaced by Theorem
3.4 (`commutator_acts_trivially_via_thm34`).  Note the conclusion is on `⁅R, K⁆` (not `K`):
Theorem 3.4 only controls the commutator. -/
theorem commutator_le_chiefFactorCentralizer_via_thm34
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {K R X Y : Subgroup G}
    [K.Normal] [X.Normal] [Y.Normal] {s : ℕ} [Fact s.Prime]
    (hVelem : IsElementaryAbelian s (↥X ⧸ Y.subgroupOf X))
    {L : Subgroup G} [L.Normal] (hLcent : L ≤ chiefFactorCentralizer X Y)
    (hcompl : (K.map (QuotientGroup.mk' L)).IsComplement' (R.map (QuotientGroup.mk' L)))
    (hHall : Nat.Coprime (Nat.card ↥(K.map (QuotientGroup.mk' L)))
      (Nat.card ↥(R.map (QuotientGroup.mk' L))))
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' L)) = p)
    (hodd : Odd (Nat.card (G ⧸ L)))
    (hchar : ¬ s ∣ Nat.card (G ⧸ L))
    (hFPF : letI := S03c.chiefFactorConjAction X Y
            ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1) :
    ⁅R, K⁆ ≤ chiefFactorCentralizer X Y := by
  haveI : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  haveI : IsSolvable (G ⧸ L) := solvable_of_surjective (QuotientGroup.mk'_surjective L)
  haveI : (K.map (QuotientGroup.mk' L)).Normal :=
    (inferInstance : K.Normal).map (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)
  letI : CommGroup (↥X ⧸ Y.subgroupOf X) :=
    { (inferInstance : Group (↥X ⧸ Y.subgroupOf X)) with mul_comm := hVelem.comm }
  letI := hVelem.zmodModule
  letI := S03c.chiefFactorConjAction X Y
  have hL : ∀ l : G, l ∈ L → ∀ v : ↥X ⧸ Y.subgroupOf X, l • v = v := by
    intro l hl v
    exact (S03c.chiefFactorConjAction_smul_eq_self_iff_mem l).mpr (hLcent hl) v
  letI := mulDistribMulActionQuotientOfTrivial L hL
  have hFPF' : ∀ v : ↥X ⧸ Y.subgroupOf X,
      (∀ r : R.map (QuotientGroup.mk' L), (r : G ⧸ L) • v = v) → v = 1 := by
    intro v hv
    refine hFPF v (fun r => ?_)
    rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL (r : G) v]
    exact hv ⟨QuotientGroup.mk' L (r : G), ⟨r, r.2, rfl⟩⟩
  have hKtriv := commutator_acts_trivially_via_thm34 hcompl hHall hRp hodd hchar hFPF'
  intro x hx
  refine (S03c.chiefFactorConjAction_smul_eq_self_iff_mem x).mp (fun v => ?_)
  rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL (x : G) v]
  have hxmem : QuotientGroup.mk' L x ∈
      ⁅R.map (QuotientGroup.mk' L), K.map (QuotientGroup.mk' L)⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ hx
  exact hKtriv (QuotientGroup.mk' L x) hxmem v

/-- **Fixed-point-freeness from condition (3) of BG Theorem 3.8** (the `hFPF` input to
`commutator_le_chiefFactorCentralizer_via_thm34`).  The `thm34`-analog of
`S03c.chiefFactor_fixedPointFree`: instead of a Frobenius structure, the fixed-point-freeness comes
from condition (3) `C_{F(K)}(R) = 1` (`hC3`).  For a chief factor `X/Y` with `X ⊆ F(K)` and `R` of
order coprime to `|K|`, `R` acts fixed-point-freely on `X/Y` (via `chiefFactorConjAction`).

Proof (mirrors `S03c.chiefFactor_fixedPointFree`): an `R`-fixed coset of `X/Y` lifts (coprime
action, `coprime_fixedPoints_quotient_of_coprime_normal`) to an `R`-fixed `c ∈ X ⊆ F(K)`; being
`R`-fixed means `c ∈ C_G(R)`, so `c ∈ C_{F(K)}(R) = 1` (`hC3`), whence `c = 1` and the coset is
trivial.  `F(K)` is written `(fitting ↥K).map K.subtype` (its `Ch2.S08.fittingInG` form would import
downstream into `Ch1`). -/
theorem chiefFactor_fixedPointFree_of_centralizer_fitting_eq_bot
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {K R X Y : Subgroup G}
    [X.Normal] [Y.Normal]
    (hXF : X ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype)
    (hXK : X ≤ K) (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hC3 : Subgroup.centralizer (R : Set G) ⊓
      (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype = ⊥) :
    letI := S03c.chiefFactorConjAction X Y
    ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1 := by
  letI := S03c.chiefFactorConjAction X Y
  set ψ : ↥R →* MulAut G := MulAut.conj.comp R.subtype with hψ
  have hXinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ X :=
    fun a => Subgroup.Normal.conj_smul_eq_self (a : G) X
  have hYinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ Y :=
    fun a => Subgroup.Normal.conj_smul_eq_self (a : G) Y
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant hXinv.restrict (Y.subgroupOf X) :=
    hXinv.subgroupOf hYinv
  have hcopX : Nat.Coprime (Nat.card ↥R) (Nat.card ↥X) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hXK)
  have hCop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥(Y.subgroupOf X)) :=
    hcopX.coprime_dvd_right (Subgroup.card_subgroup_dvd_card (Y.subgroupOf X))
  have hSolv : IsSolvable ↥R ∨ IsSolvable ↥(Y.subgroupOf X) := Or.inr inferInstance
  have hrestrict : ∀ (a : ↥R) (x : ↥X),
      (hXinv.restrict a) x = ConjAct.toConjAct (a : G) • x := fun _ _ => rfl
  intro v hv
  induction v using QuotientGroup.induction_on with
  | _ x =>
    have hgfix : ∀ a : ↥R, ∃ n ∈ Y.subgroupOf X, (hXinv.restrict a) x = x * n := by
      intro a
      have hva := hv a
      rw [S03c.chiefFactorConjAction_smul_mk, QuotientGroup.eq] at hva
      refine ⟨x⁻¹ * (hXinv.restrict a) x, ?_, by group⟩
      rw [hrestrict]
      simpa using (Y.subgroupOf X).inv_mem hva
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal hCop hSolv hN_inv hgfix
    have hc_one : (c : G) = 1 := by
      have hcF : (c : G) ∈ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := hXF c.2
      have hcR : (c : G) ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hcr : ConjAct.toConjAct r • (c : ↥X) = c := by
          rw [← hrestrict ⟨r, hr⟩ c]; exact hc_fix ⟨r, hr⟩
        have hval : ConjAct.toConjAct r • (c : G) = (c : G) := congrArg Subtype.val hcr
        rw [ConjAct.toConjAct_smul] at hval
        -- `r * c * r⁻¹ = c` ⟹ `r * c = c * r`
        rw [mul_inv_eq_iff_eq_mul] at hval
        exact hval
      have hmem : (c : G) ∈ Subgroup.centralizer (R : Set G) ⊓
          (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := ⟨hcR, hcF⟩
      rw [hC3, Subgroup.mem_bot] at hmem
      exact hmem
    have hc1 : c = 1 := Subtype.ext (by simpa using hc_one)
    have hx_eq : x = n⁻¹ := by
      rw [hc1] at hcn; rw [eq_comm, mul_eq_one_iff_eq_inv] at hcn; exact hcn
    rw [QuotientGroup.eq_one_iff, hx_eq]
    exact (Y.subgroupOf X).inv_mem hn

open OddOrder.GroupTheory in
/-- **Per-factor dichotomy for BG Theorem 3.8** (`thm34`-analog of
`S03c.kernel_le_chiefFactorCentralizer_dichotomy`).  For a `G`-chief factor `X/Y` (`X ⊆ K`)
elementary abelian of prime `s`, with `L ⊴ G` centralizing `X/Y`, `K/L` a `q`-group, `R` acting
fixed-point-freely on `X/Y`, and the `G/L = (K/L)(R/L)` Theorem 3.4 data, the commutator `⁅R, K⁆`
centralizes `X/Y`.

* `s = q`: `K/L` is an `s`-group, so `S03c.samePrime_kernel_le_chiefFactorCentralizer` gives
  `K ≤ chiefFactorCentralizer`, hence `⁅R, K⁆ ≤ K ≤ chiefFactorCentralizer`.
* `s ≠ q`: `commutator_le_chiefFactorCentralizer_via_thm34` (leaf B). -/
theorem commutator_le_chiefFactorCentralizer_dichotomy_thm38
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {K R X Y : Subgroup G}
    [K.Normal] [X.Normal] [Y.Normal] {s q : ℕ} [Fact s.Prime] [Fact q.Prime]
    (hChief : IsChiefFactor X Y)
    (hVelem : IsElementaryAbelian s (↥X ⧸ Y.subgroupOf X))
    {L : Subgroup G} [L.Normal] (hLcent : L ≤ chiefFactorCentralizer X Y)
    (hKbar : IsPGroup q (K.map (QuotientGroup.mk' L)))
    (hcompl : (K.map (QuotientGroup.mk' L)).IsComplement' (R.map (QuotientGroup.mk' L)))
    (hHall : Nat.Coprime (Nat.card ↥(K.map (QuotientGroup.mk' L)))
      (Nat.card ↥(R.map (QuotientGroup.mk' L))))
    (hRp : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' L)) = r)
    (hodd : Odd (Nat.card (G ⧸ L)))
    (hchar : s ≠ q → ¬ s ∣ Nat.card (G ⧸ L))
    (hFPF : letI := S03c.chiefFactorConjAction X Y
            ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1) :
    ⁅R, K⁆ ≤ chiefFactorCentralizer X Y := by
  by_cases hsq : s = q
  · -- `s = q`: `K` centralizes `X/Y` (same-prime branch), so `⁅R, K⁆ ≤ K ≤ chiefFactorCentralizer`.
    subst hsq
    have hKcent := S03c.samePrime_kernel_le_chiefFactorCentralizer hChief hVelem hLcent hKbar
    have hRKle : ⁅R, K⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro r _ k hk
      rw [commutatorElement_def]
      exact K.mul_mem (‹K.Normal›.conj_mem k hk r) (K.inv_mem hk)
    exact hRKle.trans hKcent
  · -- `s ≠ q`: the coprime (Theorem 3.4) branch.
    exact commutator_le_chiefFactorCentralizer_via_thm34 hVelem hLcent hcompl hHall hRp hodd
      (hchar hsq) hFPF

open OddOrder.GroupTheory in
/-- **BG Theorem 3.8, reduced case** (step 4 of mmd L1247-1259): if `G = KR` is solvable of odd
order with `K ⊴ G` complementing the prime-order `R`, `(|K|, |R|) = 1`, the quotient `K/F(K)` is a
`p`-group, and `C_{F(K)}(R) = 1` (condition (3)), then `⁅K, R⁆ ⊆ F(K)`.

Proof: for every `G`-chief factor `U/V` with `U ⊆ F(K)`, the per-factor dichotomy
(`commutator_le_chiefFactorCentralizer_dichotomy_thm38`) gives `⁅R, K⁆ ⊆ C_K(U/V)`.  Since `⁅K, R⁆`
need not be normal in `G`, take `N = ⟨⁅K, R⁆⟩^G` (its normal closure); each `chiefFactorCentralizer`
is normal in `G` and contains `⁅K, R⁆`, so `N ⊆ chiefFactorCentralizer U V`.  BG Proposition 1.2
reverse (`S01.chiefFactorCentralizer_subset_le_fitting_of_isSolvable`) then gives `N ⊆ F(K)`, whence
`⁅K, R⁆ ⊆ N ⊆ F(K)`.  `F(K) = (fitting ↥K).map K.subtype`. -/
theorem commutator_le_fitting_of_reduced
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {K R : Subgroup G} [K.Normal]
    (hodd : Odd (Nat.card G))
    (hcompl : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R))
    (hRprime : ∃ r : ℕ, r.Prime ∧ Nat.card ↥R = r)
    {p : ℕ} [Fact p.Prime]
    (hKbar : IsPGroup p
      (K.map (QuotientGroup.mk' ((OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype))))
    (hC3 : Subgroup.centralizer (R : Set G) ⊓
      (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype = ⊥) :
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  set L : Subgroup G := (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype with hLdef
  haveI hLnorm : L.Normal := ConjAct.normal_of_characteristic_of_normal
  have hLK : L ≤ K := by rw [hLdef]; exact Subgroup.map_subtype_le _
  have hRL_disj : Disjoint (R : Subgroup G) L :=
    hcompl.isCompl.disjoint.symm.mono_right hLK
  -- The `G/L = (K/L)(R/L)` Theorem 3.4 data (shared across chief factors).
  have hcompl' : (K.map (QuotientGroup.mk' L)).IsComplement' (R.map (QuotientGroup.mk' L)) :=
    hcompl.map_mk' hcop L
  have hHall' : Nat.Coprime (Nat.card ↥(K.map (QuotientGroup.mk' L)))
      (Nat.card ↥(R.map (QuotientGroup.mk' L))) :=
    (hcop.coprime_dvd_left (Subgroup.card_map_dvd K (QuotientGroup.mk' L))).coprime_dvd_right
      (Subgroup.card_map_dvd R (QuotientGroup.mk' L))
  -- `|R/L| = |R|` (prime): `|R/L|` divides `|R|` and is `≠ 1` (else `R ≤ L`, against `R ⊓ L = ⊥`).
  have hRcardL : Nat.card ↥(R.map (QuotientGroup.mk' L)) = Nat.card ↥R := by
    obtain ⟨r, hr, hrcard⟩ := hRprime
    have hdvd : Nat.card ↥(R.map (QuotientGroup.mk' L)) ∣ Nat.card ↥R :=
      Subgroup.card_map_dvd R (QuotientGroup.mk' L)
    rcases (Nat.dvd_prime hr).mp (hrcard ▸ hdvd) with h1 | hr'
    · exfalso
      have hRbot : R.map (QuotientGroup.mk' L) = ⊥ := Subgroup.card_eq_one.mp h1
      have hRL : (R : Subgroup G) ≤ L := by
        intro x hx
        have hxm : QuotientGroup.mk' L x ∈ R.map (QuotientGroup.mk' L) :=
          Subgroup.mem_map_of_mem _ hx
        rw [hRbot, Subgroup.mem_bot] at hxm
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxm
      have hReq : (R : Subgroup G) = ⊥ := by
        rw [disjoint_iff] at hRL_disj; rwa [inf_of_le_left hRL] at hRL_disj
      rw [hReq, Subgroup.card_bot] at hrcard
      exact hr.one_lt.ne' hrcard.symm
    · rw [hrcard]; exact hr'
  have hRp' : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' L)) = r := by
    obtain ⟨r, hr, hrcard⟩ := hRprime; exact ⟨r, hr, hRcardL.trans hrcard⟩
  have hodd' : Odd (Nat.card (G ⧸ L)) := Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card L)
  -- `F(K) ≤ F(G)`, hence `F(K)` centralizes every chief factor of `G` (Prop 1.2 forward).
  have hLfitG : L ≤ OddOrder.Isaacs.Ch01.fitting G :=
    OddOrder.Isaacs.Ch01.fitting_map_subtype_le_fitting
  -- `N = ⟨⁅K, R⁆⟩^G`: normal, `≤ K`.
  set N : Subgroup G := Subgroup.normalClosure ((⁅K, R⁆ : Subgroup G) : Set G) with hNdef
  haveI hNnorm : N.Normal := Subgroup.normalClosure_normal
  have hKR_le_K : (⁅K, R⁆ : Subgroup G) ≤ K := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_le]
    intro r _ k hk
    rw [commutatorElement_def]
    exact K.mul_mem (‹K.Normal›.conj_mem k hk r) (K.inv_mem hk)
  have hNK : N ≤ K := Subgroup.normalClosure_le_normal hKR_le_K
  -- `N ≤ F(K)` via Proposition 1.2 reverse: `N` centralizes every chief factor `U/V` with `U ⊆ F(K)`.
  have hNF : N ≤ L := by
    refine OddOrder.BG.Ch1.S01.chiefFactorCentralizer_subset_le_fitting_of_isSolvable hNK ?_
    intro U V hVnorm hChief hUF
    haveI := hChief.normal_top
    haveI := hChief.normal_bot
    apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨s, hs, hVelem⟩ := S03c.chiefFactor_isElementaryAbelian hChief
    haveI : Fact s.Prime := ⟨hs⟩
    have hUK : U ≤ K := hUF.trans hLK
    have hLcent : L ≤ OddOrder.GroupTheory.chiefFactorCentralizer U V :=
      hLfitG.trans (OddOrder.BG.Ch1.S01.fitting_le_chiefFactorCentralizer hChief)
    have hFPF := chiefFactor_fixedPointFree_of_centralizer_fitting_eq_bot (Y := V) hUF hUK
      hcop.symm hC3
    have hchar : s ≠ p → ¬ s ∣ Nat.card (G ⧸ L) := by
      intro hsp
      -- `|G/L| = |K/L| · |R/L|`, with `|K/L| = p^n` and `|R/L| = r` prime.
      have hGL : Nat.card (G ⧸ L) = Nat.card ↥(K.map (QuotientGroup.mk' L)) *
          Nat.card ↥(R.map (QuotientGroup.mk' L)) := hcompl'.card_mul.symm
      -- `s ∤ |K/L|` (a `p`-power, `s ≠ p`).
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hKbar
      have hsK : ¬ s ∣ Nat.card ↥(K.map (QuotientGroup.mk' L)) := by
        rw [hn]
        exact (Nat.Prime.coprime_iff_not_dvd hs).mp
          (((Nat.coprime_primes hs Fact.out).mpr hsp).pow_right n)
      -- `s ∣ |U/V|` (nontrivial `s`-group), hence `s ∣ |K|`.
      have hUVnt : 1 < Nat.card (↥U ⧸ V.subgroupOf U) := by
        have hpos : 0 < Nat.card (↥U ⧸ V.subgroupOf U) := Nat.card_pos
        have hne1 : Nat.card (↥U ⧸ V.subgroupOf U) ≠ 1 := by
          rw [← Subgroup.index_eq_card, Ne, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
          exact fun hUV => hChief.lt.ne (le_antisymm hChief.le hUV)
        omega
      have hsUV : s ∣ Nat.card (↥U ⧸ V.subgroupOf U) := by
        obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := s)).mp hVelem.isPGroup
        rw [hm] at hUVnt ⊢
        exact dvd_pow_self s (by rintro rfl; exact absurd hm.symm (by simpa using hUVnt.ne'))
      have hsK_dvd : s ∣ Nat.card ↥K :=
        hsUV.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hUK))
      -- `s ∤ |R/L| = r` (else `s = r ∣ |K|`, against `(|K|, |R|) = 1`).
      have hsR : ¬ s ∣ Nat.card ↥(R.map (QuotientGroup.mk' L)) := by
        rw [hRcardL]
        intro hsr
        have hgcd : s ∣ Nat.gcd (Nat.card ↥K) (Nat.card ↥R) := Nat.dvd_gcd hsK_dvd hsr
        rw [hcop] at hgcd
        exact hs.one_lt.ne' (Nat.dvd_one.mp hgcd)
      rw [hGL]
      exact fun hd => (hs.prime.dvd_mul.mp hd).elim hsK hsR
    have hdich := commutator_le_chiefFactorCentralizer_dichotomy_thm38 hChief hVelem hLcent hKbar
      hcompl' hHall' hRp' hodd' hchar hFPF
    have hxRK : x ∈ (⁅R, K⁆ : Subgroup G) := by rw [Subgroup.commutator_comm] at hx; exact hx
    exact hdich hxRK
  exact fun y hy => hNF (Subgroup.subset_normalClosure hy)

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 3.8, step 1** (base case of the `|RK|` induction, mmd L1233): if `R` (normalizing
`K`) centralizes the Fitting subgroup of `K̄ = ↥K / F(K)`, then `R` centralizes `K̄` itself
(Proposition 1.4), i.e. `⁅K, R⁆ ⊆ F(K)`.

The conjugation action `φ : R → MulAut ↥K` descends to `K̄` (`quotientMulAutHom`); the centralizing
hypothesis is `F(K̄) ≤ fixedPoints`, so Proposition 1.4
(`actionCommutator_eq_bot_of_fitting_le_fixedPoints`) makes the action commutator on `K̄` trivial.
By `actionCommutator_quotient_eq_map` this is the image of `actionCommutator φ`, so
`actionCommutator φ ≤ F(K)`; finally `actionCommutator_conj_map_subtype` identifies its image under
`K.subtype` with `⁅K, R⁆`. -/
theorem commutator_le_fitting_of_centralizes_fittingQuotient
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {K R : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hcent : OddOrder.Isaacs.Ch01.fitting (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K) ≤
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom
        (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic
          ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK))))) :
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  set φ : ↥R →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK) with hφ
  have hFinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting ↥K) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  have hcopK : Nat.Coprime (Nat.card ↥R)
      (Nat.card (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K)) :=
    hcop.coprime_dvd_right (Subgroup.card_quotient_dvd_card _)
  have hbot : OddOrder.Isaacs.Ch04.actionCommutator (quotientMulAutHom hFinv) = ⊥ :=
    OddOrder.BG.Ch1.S01.actionCommutator_eq_bot_of_fitting_le_fixedPoints hcopK hcent
  rw [OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map] at hbot
  have hle : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ OddOrder.Isaacs.Ch01.fitting ↥K := by
    rw [← QuotientGroup.ker_mk' (OddOrder.Isaacs.Ch01.fitting ↥K)]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  calc ⁅K, R⁆ = (OddOrder.Isaacs.Ch04.actionCommutator φ).map K.subtype :=
        (OddOrder.BG.Ch1.S06.actionCommutator_conj_map_subtype hRK).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := Subgroup.map_mono hle

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **BG Proposition 1.5(d), subgroup form** (`C_{G/N}(A) = C_G(A)·N / N`): for a coprime action
`φ : A → MulAut G` and an `A`-invariant normal `N`, the fixed points of the induced action on
`G/N` are exactly the image of the fixed points in `G`.  The `⊇` direction is immediate; the `⊆`
direction is the lifting in `coprime_fixedPoints_quotient` (Proposition 1.5(d), element form). -/
theorem fixedPointsOfMulAut_quotientMulAutHom_eq_map
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) (hSolv : IsSolvable A ∨ IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    Subgroup.fixedPointsOfMulAut (quotientMulAutHom hN) =
      (Subgroup.fixedPointsOfMulAut φ).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    -- `q` fixed in `G/N` lifts to a fixed `c ≡ q (mod N)` (`coprime_fixedPoints_quotient`).
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [Subgroup.mem_fixedPointsOfMulAut] at hq
    have hg_fix : ∀ a : A, ∃ n ∈ N, (φ a) g = g * n := by
      intro a
      have hga := hq a
      rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hga
      exact ⟨g⁻¹ * (φ a) g, by simpa using N.inv_mem hga, by group⟩
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hCop hSolv hN hg_fix
    refine Subgroup.mem_map.mpr ⟨c, Subgroup.mem_fixedPointsOfMulAut.mpr hc_fix, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcn]
    simpa using N.inv_mem hn
  · -- image of a fixed point is fixed (immediate).
    rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    rw [Subgroup.mem_fixedPointsOfMulAut] at hc
    rw [Subgroup.mem_comap, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    rw [quotientMulAutHom_apply_mk', hc a]

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Converse of step 1** (mmd L1243, the `R₀`-centralizes-`K̄` direction): if `⁅K, R⁆ ⊆ F(K)`
(`R` centralizes `K̄`), then `R` fixes every element of `K̄ = ↥K / F(K)` (the induced action's
fixed points are `⊤`).  This is the reverse of `commutator_le_fitting_of_centralizes_fittingQuotient`:
`⁅K, R⁆ = (actionCommutator φ).map K.subtype ⊆ F(K)` forces `actionCommutator φ ⊆ F(K) = ker`, so
the induced quotient action commutator is `⊥` (`actionCommutator_quotient_eq_map`), i.e. the action
on `K̄` is trivial (`actionCommutator_eq_bot_iff_acts_trivially`). -/
theorem fixedPoints_quotient_eq_top_of_commutator_le_fitting
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype) :
    Subgroup.fixedPointsOfMulAut (quotientMulAutHom
      (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic
        (H := OddOrder.Isaacs.Ch01.fitting ↥K)
        ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)))) = ⊤ := by
  set φ : ↥R →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK) with hφ
  have hFinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting ↥K) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  -- `actionCommutator φ ≤ F(K)`, by injectivity of `K.subtype` from `⁅K, R⁆ ⊆ F(K)`.
  have hac_le : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ OddOrder.Isaacs.Ch01.fitting ↥K := by
    have h := OddOrder.BG.Ch1.S06.actionCommutator_conj_map_subtype hRK
    rw [← h] at hcomm
    exact Subgroup.map_le_map_iff_of_injective K.subtype_injective |>.mp hcomm
  -- The induced quotient action commutator is `⊥`.
  have hbot : OddOrder.Isaacs.Ch04.actionCommutator (quotientMulAutHom hFinv) = ⊥ := by
    rw [OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hac_le
  -- Trivial action ⟹ fixed points are `⊤`.
  rw [Subgroup.eq_top_iff']
  intro g
  rw [Subgroup.mem_fixedPointsOfMulAut]
  intro a
  exact (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hbot a g

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 3.8, step 3** (mmd L1241-1245, the condition-(2) reduction from `R₀` to `R`): if
`R₀` (normalizing `K`) already centralizes `K̄ = ↥K / F(K)` (`⁅K, R₀⁆ ⊆ F(K)`) and `R₀` has the
*same fixed points on `K`* as `R` — i.e. `C_G(R₀) ⊓ K = C_G(R) ⊓ K`, which is exactly condition (2)
`C_K(x) = C_K(R)` for `R₀ = ⟨x⟩` — then `R` itself centralizes `K̄`, i.e. `⁅K, R⁆ ⊆ F(K)`.

Chain: `fixedPoints_quotient_eq_top_of_commutator_le_fitting` turns `⁅K, R₀⁆ ⊆ F(K)` into
`fixedPoints(R₀ on K̄) = ⊤`; Proposition 1.5(d) (`fixedPointsOfMulAut_quotientMulAutHom_eq_map`)
rewrites both `R₀`- and `R`-quotient fixed points as push-forwards of the fixed points on `K`;
condition (2) (`fixedPointsOfMulAut_conj_map_subtype` + injectivity of `K.subtype`) identifies the
`R₀`- and `R`-fixed points on `K`, transporting `⊤` to the `R`-quotient; finally step 1
(`commutator_le_fitting_of_centralizes_fittingQuotient`, with `F(K̄) ≤ ⊤` trivial) concludes. -/
theorem commutator_le_fitting_of_sameFixedPoints
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {K R R₀ : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hR₀K : R₀ ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hcop₀ : Nat.Coprime (Nat.card ↥R₀) (Nat.card ↥K))
    (hCeq : Subgroup.centralizer (R₀ : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K)
    (hcent0 : ⁅K, R₀⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype) :
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  have hsolvK : IsSolvable ↥K := inferInstance
  -- `R₀` fixes all of `K̄` (converse of step 1).
  have htop0 := fixedPoints_quotient_eq_top_of_commutator_le_fitting hR₀K hcent0
  -- Proposition 1.5(d) for both `R₀` and `R`: quotient fixed points are push-forwards.
  have hmap0 := fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hR₀K)) hcop₀ (Or.inr hsolvK)
    (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (H := OddOrder.Isaacs.Ch01.fitting ↥K)
      ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hR₀K)))
  have hmapR := fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)) hcop (Or.inr hsolvK)
    (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (H := OddOrder.Isaacs.Ch01.fitting ↥K)
      ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)))
  -- Condition (2): `R₀`- and `R`-fixed points on `K` coincide.
  have hconj0 := OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hR₀K
  have hconjR := OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hRK
  have hfix_eq : Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hR₀K)) =
      Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hconj0, hconjR, hCeq]
  -- Transport `⊤` from the `R₀`-quotient to the `R`-quotient.
  rw [hmap0, hfix_eq, ← hmapR] at htop0
  exact commutator_le_fitting_of_centralizes_fittingQuotient hRK hcop (by rw [htop0]; exact le_top)

/-- **Condition (2) of BG Theorem 3.8, subgroup consequence** (mmd L1224, L1237-1239): from
`C_K(x) = C_K(R)` for all `x ∈ R^#` (in the `⊓ K` form), every nontrivial subgroup `R₀ ≤ R` has
the *same* fixed points on `K`, i.e. `C_K(R₀) = C_K(R)`.  (`⊆`: pick a witness `x ∈ R₀^#` and apply
condition (2) at `x`, using `C_K(R₀) ≤ C_K(x)`; `⊇`: antitonicity of the centralizer, `R₀ ≤ R`.) -/
theorem centralizer_inf_eq_of_le_of_cond2
    {G : Type*} [Group G] {K R R₀ : Subgroup G} (hR₀R : R₀ ≤ R) (hR₀ : R₀ ≠ ⊥)
    (hcond2 : ∀ x ∈ (R : Set G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K) :
    Subgroup.centralizer (R₀ : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K := by
  haveI : Nontrivial ↥R₀ := (Subgroup.nontrivial_iff_ne_bot R₀).mpr hR₀
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥R₀)
  refine le_antisymm ?_ ?_
  · calc Subgroup.centralizer (R₀ : Set G) ⊓ K
        ≤ Subgroup.centralizer ({(y : G)} : Set G) ⊓ K :=
          inf_le_inf_right K (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr y.2))
      _ = Subgroup.centralizer (R : Set G) ⊓ K :=
          hcond2 (y : G) (hR₀R y.2) (mt OneMemClass.coe_eq_one.mp hy)
  · exact inf_le_inf_right K (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR₀R))

end OddOrder.BG.Ch1.S03h
