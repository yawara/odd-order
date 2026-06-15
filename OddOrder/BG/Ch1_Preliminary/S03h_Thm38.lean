/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
import OddOrder.BG.Ch1_Preliminary.S03d_Thm34

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

end OddOrder.BG.Ch1.S03h
