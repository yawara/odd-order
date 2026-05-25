/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main

/-!
# BG §3: Actions of Frobenius Groups and Related Results

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §3 (pp. 17-32), mmd
`references/bg/local-analysis.mmd` L795-1358, **10 結果** (Lemma 3.1-3.10).

## 構造 (BG §3 全 10 結果)

- **§3A** Frobenius group basics (Lemma 3.1, Lemma 3.2)
- **§3B** Representation-theoretic Frobenius action (Lemma 3.3, Theorem 3.4,
  Theorem 3.5)
- **§3C** Z-group centralizer and p-length (Theorem 3.6)
- **§3D** Frobenius kernel nilpotence and Fitting control (Theorem 3.7,
  Theorem 3.8)
- **§3E** Regular actions and nilpotent targets (Proposition 3.9, Theorem 3.10)

## Current status

This file starts the BG §3 layer over the existing Isaacs Ch.6 Frobenius API.
The first implemented result is the BG Lemma 3.1 equivalence between the
Frobenius group structure on `G = K R` and the fixed-point-free conjugation
condition `C_K(x) = 1` for every nonidentity `x ∈ R`.

The representation-dependent results 3.3-3.6 and 3.10 will later depend on
BG §2 representation infrastructure; this initial file intentionally imports
only the Frobenius infrastructure needed for 3.1.

References:
- BG mmd `references/bg/local-analysis.mmd` L795-1358.
- Section note: `notes/bg/s03_frobenius_actions.md`.
- Isaacs Ch.6 Frobenius API:
  `OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean`.
-/

namespace OddOrder.BG.Ch1.S03

open OddOrder.Isaacs.Ch06

/-! ## §3A: Frobenius group basics (Lemma 3.1, Lemma 3.2) -/

/-- **BG Lemma 3.1 (centralizer direction)**: in a Frobenius group `G = K R`,
the `K`-centralizer of every nonidentity `x ∈ R` is trivial.

The BG notation `C_K(x)=1` is represented as
`Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥`. -/
theorem centralizer_complement_inf_kernel_eq_bot
    {G : Type*} [Group G] {K R : Subgroup G}
    (h : IsFrobeniusGroup G K R) :
    ∀ x ∈ R, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥ := by
  intro x hxR hx_ne
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hy_centralizes, hyK⟩ := hy
  rw [Subgroup.mem_bot]
  by_contra hy_ne
  rw [Subgroup.mem_centralizer_singleton_iff] at hy_centralizes
  have h_conj : x * y * x⁻¹ = y := by
    calc
      x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [← hy_centralizes]
      _ = y := mul_inv_cancel_right y x
  exact h.conj_frobenius x hxR hx_ne y hyK hy_ne h_conj

/-- **BG Lemma 3.1**: for nonidentity subgroups `K` and `R` with `K ⊴ G`,
`K` complemented by `R`, the Frobenius group structure on `G = K R` is
equivalent to `C_K(x)=1` for every nonidentity `x ∈ R`.

This is the local BG form of Isaacs Thm 6.4, specialized to a named kernel
`K` and complement `R`. -/
theorem isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot
    {G : Type*} [Group G] {K R : Subgroup G}
    (hK : K.Normal) (hC : Subgroup.IsComplement' K R)
    (hK_ne : K ≠ ⊥) (hR_ne : R ≠ ⊥) :
    IsFrobeniusGroup G K R ↔
      ∀ x ∈ R, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥ := by
  refine ⟨centralizer_complement_inf_kernel_eq_bot, ?_⟩
  intro hcentral
  exact
    { isNormal := hK
      isComplement := hC
      ne_bot_kernel := hK_ne
      ne_bot_complement := hR_ne
      conj_frobenius := by
        intro x hxR hx_ne y hyK hy_ne h_conj
        have h_comm : y * x = x * y := by
          have h_mul := congrArg (fun z => z * x) h_conj
          simpa only [mul_assoc, inv_mul_cancel, mul_one] using h_mul.symm
        have hy_centralizes : y ∈ Subgroup.centralizer ({x} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr h_comm
        have hy_inf : y ∈ Subgroup.centralizer ({x} : Set G) ⊓ K :=
          Subgroup.mem_inf.mpr ⟨hy_centralizes, hyK⟩
        rw [hcentral x hxR hx_ne, Subgroup.mem_bot] at hy_inf
        exact hy_ne hy_inf }

end OddOrder.BG.Ch1.S03
