/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116

/-!
# BG §12: Theorem 12.12 — regular 場合の Frobenius 因子分解

**スコープ**: BG Theorem 12.12 (mmd L3336)。`SubgroupESetup M E E₁ E₂ E₃` の下で、
すべての `(τ₁(M)∪τ₃(M))`-元 `e ∈ E#` が `C_{M_σ}(e)=1` を満たす (regular) とき、
(a) `E` は abelian normal `A₀` を含み `∀ x ∈ M_σ#, C_E(x) ⊆ A₀`;
(b) `E` は `E` と同 exponent の補群 `E₀` を含み `M_σ E₀` は kernel `M_σ` の Frobenius 群。

本ファイルでは新規補題 **Proposition 3.9** (coprime FPF p-作用 ⟹ cyclic) を形式化し、
3 大ケース (τ₂(M)=∅ / nonabelian Sylow p / abelian Sylow) のための部品を順次構築する。
最終的に `frobenius_factorization_of_regular` (S12_E の scaffold) をここで充足・移植する。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.Isaacs.Ch06
open scoped Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Proposition 3.9: coprime fixed-point-free `p`-action ⟹ cyclic -/

/-- **Proposition 3.9** (Gorenstein 5.3.14): a finite `p`-group `R` (`p` odd) acting
coprimely and fixed-point-freely on a nontrivial finite group `H` is cyclic.

If `R` were not cyclic it would contain an elementary abelian subgroup `B` of order `p²`
(`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`); `B` is abelian and not cyclic,
so Isaacs 6.21 (`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) gives
`⟨ C_H(b) | b ∈ B^# ⟩ = H`. But the action is fixed-point-free, so each `C_H(b) = 1`,
forcing `H = 1`, a contradiction. The `12.12` application is the conjugation action of
`Q/Q₀` on a Sylow subgroup `S`, where `Q₀ = C_Q(S)` is the kernel. -/
theorem isCyclic_of_coprime_fpf_pgroup_action
    {R H : Type*} [Group R] [Group H] [Finite R] [Finite H] {p : ℕ} [Fact p.Prime]
    [Nontrivial H] (hR : IsPGroup p R) (hp_odd : Odd p)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card H)) (φ : R →* MulAut H)
    (hfpf : ∀ a : R, a ≠ 1 → actionFixedBy φ a = ⊥) :
    IsCyclic R := by
  by_contra hnc
  obtain ⟨B, hB_elem, hB_card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hR hp_odd hnc
  haveI : IsMulCommutative ↥B := ⟨⟨hB_elem.comm⟩⟩
  have hBnc : ¬ IsCyclic ↥B :=
    OddOrder.GroupTheory.IsElementaryAbelian.not_isCyclic_of_card_prime_sq Fact.out hB_elem hB_card
  have hcop' : Nat.Coprime (Nat.card ↥B) (Nat.card H) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B) hcop
  have htop : nontrivialActionFixedByClosure (φ.comp B.subtype) = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
      (φ.comp B.subtype) hcop' hBnc
  have hbot : nontrivialActionFixedByClosure (φ.comp B.subtype) ≤ ⊥ := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro b hb
    have hb' : B.subtype b ≠ 1 :=
      fun h => hb (B.subtype_injective (h.trans (map_one B.subtype).symm))
    exact (hfpf (B.subtype b) hb').le
  rw [htop, top_le_iff] at hbot
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  exact hx (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top x))

end OddOrder.BG.Ch3.S12
