/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction

/-!
# BG §14 Proposition 14.2 support lemmas (`κ`-free)

**Scope**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III, support for §14 Proposition 14.2 (mmd L3778).

Generic, `κ`-free utilities that BG Proposition 14.2 (`typeP_structure`, in
`S14_TypePCounting`, lane H) cites to transport the prime action and the
`M_σ`-centralizer witness across `M`-conjugacy:

* `smul_centralizer_singleton` / `smul_centralizer_subgroup`: conjugation transport for
  element- and subgroup-centralizers (`C_G(a)^m = C_G(a^m)`, `C_G(X)^m = C_G(X^m)`).
* `actsPrimeOn_conj`: `ActsPrimeOn N X → ActsPrimeOn N (X^m)` when `m ∈ N_G(N)`.
  Used in Proposition 14.2's `κ ⊆ τ₁` case (WLOG `K = E₁`: transport `E₁`'s prime
  action on `M_σ` to the `M`-conjugate Hall `κ`-subgroup `K`, since `M_σ ◁ M` and `m ∈ M`).

Stated entirely without reference to `κ(M)` (defined downstream in `S14_TypePCounting`)
so this leaf sits **below** that file in the import DAG; lane H imports it with one line.
See `issues/7000-s14-prop142-support.md`.
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Conjugation transport for an element centralizer**: `C_G(a)^m = C_G(m a m⁻¹)`. -/
theorem smul_centralizer_singleton (m a : G) :
    MulAut.conj m • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({m * a * m⁻¹} : Set G) := by
  have himg : ({m * a * m⁻¹} : Set G) = (MulAut.conj m).toMonoidHom '' ({a} : Set G) := by
    simp [MulAut.conj_apply]
  rw [himg]
  exact Subgroup.map_centralizer_eq_of_bijective ({a} : Set G)
    (MulAut.conj m).toMonoidHom (MulAut.conj m).bijective

/-- **Conjugation transport for a subgroup centralizer**: `C_G(X)^m = C_G(X^m)`. -/
theorem smul_centralizer_subgroup (m : G) (X : Subgroup G) :
    MulAut.conj m • Subgroup.centralizer (X : Set G)
      = Subgroup.centralizer ((MulAut.conj m • X : Subgroup G) : Set G) :=
  Subgroup.map_centralizer_eq_of_bijective (X : Set G) (MulAut.conj m).toMonoidHom
    (MulAut.conj m).bijective

/-- **`ActsPrimeOn` is invariant under conjugacy of the acting subgroup by a normalizer
element of `N`.** If `m ∈ N_G(N)` (e.g. `N = M_σ ◁ M` and `m ∈ M`) and `X` acts in a
prime manner on `N`, then so does the conjugate `X^m = conj m • X`.

Proof: for `g = m h₀ m⁻¹ ∈ X^m` with `g ≠ 1` (so `h₀ ≠ 1`), `ActsPrimeOn N X` gives
`C_N(h₀) = C_N(X)`; conjugating both sides by `m` and using `N^m = N` (`m ∈ N_G(N)`),
`C_N(h₀)^m = C_N(g)` and `C_N(X)^m = C_N(X^m)`, hence `C_N(g) = C_N(X^m)`.

Used in BG Proposition 14.2 (case `κ ⊆ τ₁`) to transport the prime action from the Hall
`τ₁`-piece `E₁` to the `M`-conjugate Hall `κ`-subgroup `K` (WLOG `K = E₁`). -/
theorem actsPrimeOn_conj {N X : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer N) (h : ActsPrimeOn N X) :
    ActsPrimeOn N (MulAut.conj m • X) := by
  have hNfix : MulAut.conj m • N = N := conj_smul_eq_self_of_mem_normalizer hm
  intro g hg hg1
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hg
  set h0 : G := (MulAut.conj m)⁻¹ • g with hh0
  have hg_conj : MulAut.conj m • h0 = g := by rw [hh0]; exact smul_inv_smul _ _
  have hmhm : m * h0 * m⁻¹ = g := by
    rw [← hg_conj]; simp [MulAut.smul_def, MulAut.conj_apply]
  have hh01 : h0 ≠ 1 := by
    intro hc; apply hg1; rw [← hg_conj, hc]; simp
  have hconj : MulAut.conj m • fixedByElement N h0 = MulAut.conj m • fixedBy N X := by
    rw [h h0 hg hh01]
  simp only [fixedByElement, fixedBy] at hconj ⊢
  rw [Subgroup.smul_inf, Subgroup.smul_inf, hNfix, smul_centralizer_singleton, hmhm,
    smul_centralizer_subgroup] at hconj
  exact hconj

end OddOrder.BG.Ch3.S13
