/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# BG §3: standalone preliminaries for Theorem 3.6

Committable, reusable helper lemmas extracted from the Theorem 3.6 development (`S03f_Thm36`).
Kept separate from the (multi-session, `sorry`-bearing) assembly scaffold so that finished pieces
can land on their own.

## Main results

* `fitting_eq_opCore_of_oPiCore_compl_eq_bot`: if `O_{p'}(G) = ⊥` then `F(G) = O_p(G)`.  Used at
  BG Theorem 3.6 (3.9) (`V = F(H) = O_p(H)`).
-/

namespace OddOrder.BG.Ch1.S03f

/-- **`F(G) = O_p(G)` when `O_{p'}(G) = ⊥`** (BG Theorem 3.6 (3.9)).

The Fitting subgroup is the supremum of the `p`-cores `O_q(G)` over the prime factors `q` of `|G|`
(`fitting_eq_iSup_primeFactors`).  Each `O_q(G)` with `q ≠ p` is a normal `q`-group, hence a normal
`{p}ᶜ`-group, hence `≤ O_{p'}(G) = ⊥`; so only the `q = p` term survives and `F(G) = O_p(G)`. -/
theorem fitting_eq_opCore_of_oPiCore_compl_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (h : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) G = ⊥) :
    OddOrder.Isaacs.Ch01.fitting G = OddOrder.Isaacs.Ch01.opCore p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ (OddOrder.Isaacs.Ch01.opCore_le_fitting ⟨p, hp⟩ G)
  rw [OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors]
  refine iSup_le (fun q => ?_)
  haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
  by_cases hq : (q : ℕ) = p
  · subst hq; exact le_refl _
  · have hle : OddOrder.Isaacs.Ch01.opCore (q : ℕ) G
        ≤ OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) G := by
      refine OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
      intro r hr
      obtain ⟨nq, hnq⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup (q : ℕ) G).exists_card_eq
      rw [hnq] at hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrq : r = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
        (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
      simp [hrq, hq]
    rw [h] at hle
    exact le_trans hle bot_le

end OddOrder.BG.Ch1.S03f
