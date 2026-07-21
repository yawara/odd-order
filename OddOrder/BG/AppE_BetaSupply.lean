/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_EigenvalueCombinatorics

/-!
# BG `(E.23)`: the `β`-eigenvalue supply from the 2-step centralizer hypothesis

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, p. 163, display `(E.23)`.

BG asserts `(E.23)` — `wₐ^β ≡ wₐ^{t₀tᵃ} (mod Hₐ₊₁)` — with *"Similarly one can
show"*.  As printed this is **false**: it needs the 2-step centralizer relations
`⁅Hₐ, T⁆ ≤ Hₐ₊₂` (equivalently, `S` non-exceptional / `dc(S) ≥ 1`), which the
hypotheses of Proposition E.4 do not force — the Lazard group of the exceptional
filiform `Q₆` is a machine-checked counterexample
(`OddOrder/BG/AppE_FiliformRefutation.lean`; master note
`notes/bg/appE_e4_counterexample_2026_07_21.md`).

This leaf proves the *corrected* supply: **given** the 2-step hypothesis `hdc`
(the missing non-exceptionality assumption, issue 9402), an endomorphism `σ`
scaling a complement generator `q` by `t` and the hyperplane `T` by `t₀`
(both mod `H₁`) scales every chain term `Hₐ` by `t₀tᵃ` (mod `Hₐ₊₁`).  The level
step is `caseA_eigenvalue_step`; the extension from the commutator generators
`⁅x, qᵐc⁆` of `Hₐ₊₁` to the full subgroup runs by closure induction, using the
centrality of `Hₐ₊₁/Hₐ₊₂` (`chain_map_le_center`).

Throughout, `H a` abbreviates the chain `iterCommutator T ⊤ a` (`H 0 = T`,
`H (a+1) = ⁅H a, ⊤⁆`; for BG's `S`, `H a = γₐ₊₁(S)` by `(E.8)`).
-/

namespace OddOrder.BG.AppE

open OddOrder.Isaacs.Ch04
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {T : Subgroup G}

/-- Second-slot scaling passes to powers: if `σ q ≡ qᵗ (mod H₁)` then
`σ (qᵐ) ≡ (qᵐ)ᵗ (mod H₁)` — `H₁` is normal, so the whole computation happens in
`G/H₁`, where it is `zpow` arithmetic. -/
theorem scale_zpow_of_scale [T.Characteristic] (σ : G →* G) {q : G} {t : ℤ}
    (hσq : (q ^ t)⁻¹ * σ q ∈ iterCommutator T (⊤ : Subgroup G) 1) (m : ℤ) :
    ((q ^ m) ^ t)⁻¹ * σ (q ^ m) ∈ iterCommutator T (⊤ : Subgroup G) 1 := by
  haveI : (iterCommutator T (⊤ : Subgroup G) 1).Normal := iterCommutator_normal 1
  set N := iterCommutator T (⊤ : Subgroup G) 1
  have h1 : ((q ^ t : G) : G ⧸ N) = ((σ q : G) : G ⧸ N) := QuotientGroup.eq.mpr hσq
  refine QuotientGroup.eq.mp ?_
  show (((q ^ m) ^ t : G) : G ⧸ N) = ((σ (q ^ m) : G) : G ⧸ N)
  calc (((q ^ m) ^ t : G) : G ⧸ N)
      = (((q ^ t : G) : G ⧸ N)) ^ m := by
        rw [← zpow_mul, mul_comm m t, zpow_mul, QuotientGroup.mk_zpow]
    _ = (((σ q : G) : G ⧸ N)) ^ m := by rw [h1]
    _ = ((σ (q ^ m) : G) : G ⧸ N) := by rw [map_zpow, QuotientGroup.mk_zpow]

/-- **The corrected `(E.23)` supply** (BG p. 163, *"Similarly one can show"* —
plus the missing non-exceptionality hypothesis `hdc`, issue 9402).

If `σ` maps `T` into `T`, scales the complement generator `q` by `t` and all of
`T = H₀` by `t₀` (mod `H₁`), and the 2-step centralizer relations
`⁅Hₐ, T⁆ ≤ Hₐ₊₂` hold, then `σ` scales every `y ∈ Hₐ` by `t₀tᵃ` (mod `Hₐ₊₁`).

Induction on `a`: the base is `hbase`; for the step, every generator `⁅x, w⁆` of
`Hₐ₊₁ = ⁅Hₐ, ⊤⁆` has `w = qᵐc` (`hsup`, `T` normal), and `caseA_eigenvalue_step`
(with `hCaseA := hdc a`) scales it by `(t₀tᵃ)·t`; products and inverses of
generators follow because `Hₐ₊₁/Hₐ₊₂` is central in `G/Hₐ₊₂`
(`chain_map_le_center`). -/
theorem scale_iterCommutator_of_two_step [T.Characteristic] (σ : G →* G) {q : G}
    {t t₀ : ℤ} (hsup : (⊤ : Subgroup G) = Subgroup.zpowers q ⊔ T)
    (hσT : ∀ y ∈ T, σ y ∈ T)
    (hσq : (q ^ t)⁻¹ * σ q ∈ iterCommutator T (⊤ : Subgroup G) 1)
    (hbase : ∀ y ∈ T, (y ^ t₀)⁻¹ * σ y ∈ iterCommutator T (⊤ : Subgroup G) 1)
    (hdc : ∀ a : ℕ, ⁅iterCommutator T (⊤ : Subgroup G) a, T⁆ ≤
      iterCommutator T (⊤ : Subgroup G) (a + 2)) :
    ∀ (a : ℕ), ∀ y ∈ iterCommutator T (⊤ : Subgroup G) a,
      (y ^ (t₀ * t ^ a))⁻¹ * σ y ∈ iterCommutator T (⊤ : Subgroup G) (a + 1) := by
  intro a
  induction a with
  | zero =>
    intro y hy
    rw [iterCommutator_zero] at hy
    simpa using hbase y hy
  | succ a ih =>
    haveI : T.Normal := inferInstance
    haveI : (iterCommutator T (⊤ : Subgroup G) (a + 1 + 1)).Normal :=
      iterCommutator_normal _
    set N := iterCommutator T (⊤ : Subgroup G) (a + 1 + 1) with hNdef
    intro y hy
    have hy' : y ∈ Subgroup.closure
        {g : G | ∃ g₁ ∈ iterCommutator T (⊤ : Subgroup G) a,
          ∃ g₂ ∈ (⊤ : Subgroup G), ⁅g₁, g₂⁆ = g} := by
      rw [← Subgroup.commutator_def, ← iterCommutator_succ]
      exact hy
    clear hy
    induction hy' using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨x, hx, w, -, rfl⟩ := hg
      have hw : w ∈ (Subgroup.zpowers q : Set G) * (T : Set G) := by
        rw [← Subgroup.mul_normal, ← hsup]
        exact Subgroup.mem_top w
      obtain ⟨u, hu, c, hc, rfl⟩ := hw
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hstep := caseA_eigenvalue_step σ hx (ih x hx)
        (scale_zpow_of_scale σ hσq m) hc (hσT c hc) (hdc a)
      have hexp : t₀ * t ^ (a + 1) = t₀ * t ^ a * t := by ring
      rw [hexp]
      exact hstep
    | one => simp
    | mul x z hx hz px pz =>
      have hx' : x ∈ iterCommutator T (⊤ : Subgroup G) (a + 1) := by
        rw [iterCommutator_succ, Subgroup.commutator_def]
        exact hx
      have hz' : z ∈ iterCommutator T (⊤ : Subgroup G) (a + 1) := by
        rw [iterCommutator_succ, Subgroup.commutator_def]
        exact hz
      have hxc : ((x : G) : G ⧸ N) ∈ Subgroup.center (G ⧸ N) :=
        chain_map_le_center T (a + 1) (Subgroup.mem_map.mpr ⟨x, hx', rfl⟩)
      have hpx : ((σ x : G) : G ⧸ N) = ((x : G) : G ⧸ N) ^ (t₀ * t ^ (a + 1)) := by
        have h := (QuotientGroup.eq.mpr px).symm
        rwa [QuotientGroup.mk_zpow] at h
      have hpz : ((σ z : G) : G ⧸ N) = ((z : G) : G ⧸ N) ^ (t₀ * t ^ (a + 1)) := by
        have h := (QuotientGroup.eq.mpr pz).symm
        rwa [QuotientGroup.mk_zpow] at h
      have hcomm : Commute ((x : G) : G ⧸ N) ((z : G) : G ⧸ N) :=
        (Subgroup.mem_center_iff.mp hxc ((z : G) : G ⧸ N)).symm
      refine QuotientGroup.eq.mp ?_
      show (((x * z) ^ (t₀ * t ^ (a + 1)) : G) : G ⧸ N) = ((σ (x * z) : G) : G ⧸ N)
      rw [map_mul σ, QuotientGroup.mk_zpow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        hpx, hpz, hcomm.mul_zpow]
    | inv x hx px =>
      have hpx := (QuotientGroup.eq.mpr px).symm
      refine QuotientGroup.eq.mp ?_
      show ((x⁻¹ ^ (t₀ * t ^ (a + 1)) : G) : G ⧸ N) = ((σ x⁻¹ : G) : G ⧸ N)
      rw [map_inv σ, QuotientGroup.mk_inv, hpx, inv_zpow, QuotientGroup.mk_inv]

end OddOrder.BG.AppE
