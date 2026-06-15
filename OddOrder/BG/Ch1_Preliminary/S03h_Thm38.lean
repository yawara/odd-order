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

end OddOrder.BG.Ch1.S03h
