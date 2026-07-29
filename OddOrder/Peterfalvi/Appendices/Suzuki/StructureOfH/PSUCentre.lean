/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
import OddOrder.GroupTheory.SylowTransport
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.TorusCentralizer

/-!
# `Z(F)` has odd order in the `PSU(3, ℓ)` branch

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3 Proposition 1(c) / Ch. III §1 Proposition, p. 117.

Chapter I §3 Proposition 1(c) gives `F = O^{2′}(C_G(P))` with
`F/Z(F) ≅ PSU(3, ℓ)` and `C_Q(P) ≅ S₀`, the Sylow `2`-subgroup of `PSU(3, ℓ)`.
Since `C_Q(P)` is *itself* a Sylow `2`-subgroup of `C_G(P)` (hence of `F`, which
it generates as a normal closure), `F` and `F/Z(F)` have Sylow `2`-subgroups of
the same order, so `Z(F)` has odd order
(`Sylow.not_dvd_natCard_of_natCard_eq`).

This is what lets the Ch. III §1 Proposition lift a statement about
`C_{G₀}(Ω₁(S₀))` back to `F`: a commutator landing in `Z(F)` against a
`2`-element must be trivial (`commute_of_commutatorElement_mem_of_coprime_natCard`).

## Main results

* `CentralizerPSUData.odd_natCard_center_residual` — `|Z(F)|` is odd.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] [Finite G]

variable {hyp : Hypothesis G Omega} {X : Subgroup G}
  [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Omega)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Omega)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L}

/-- **`Z(F)` has odd order** in the `PSU(3, ℓ)` branch of Ch. I §3
Proposition 1(c).

`C_Q(P)` is a Sylow `2`-subgroup of `C = C_G(P)` and lies in
`F = O^{2′}(C) = ⟪C_Q(P)⟫^C`, so it is also a Sylow `2`-subgroup of `F`.  Its
order is `|RootGroup n|` (`cQEquivRoot`), which is exactly the order of a Sylow
`2`-subgroup of `PSU(3, ℓ) ≅ F/Z(F)` (`standardRootSylow`).  Equal Sylow orders
above and below the central quotient force `2 ∤ |Z(F)|`. -/
theorem CentralizerPSUData.odd_natCard_center_residual (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X)
    (det : CentralizerPSUData hyp X result data) :
    ¬ 2 ∣ Nat.card
      ↥(Subgroup.center ↥(Subgroup.primeComplementResidual 2
        (Subgroup.centralizer (X : Set G)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  set CQ : Subgroup ↥C := hyp.Q.subgroupOf C with hCQ
  set F : Subgroup ↥C := Subgroup.primeComplementResidual 2 C with hF
  obtain ⟨SP, hSP⟩ :=
    hyp.exists_sylow_two_eq_cQ_of_isPGroup hXV common.cQ_isPGroup
  -- `C_Q ≤ F`, so the Sylow `2`-subgroup of `C` is one of `F`
  have hle : CQ ≤ F := by
    rw [hF, common.residual_eq_normalClosure]
    exact Subgroup.le_normalClosure
  have hSPle : (SP : Subgroup ↥C) ≤ F := hSP ▸ hle
  set S : Sylow 2 ↥F := SP.subtype hSPle with hS
  -- its order is the order of the unitary root group
  have hScard : Nat.card ↥(S : Subgroup ↥F) = Nat.card (RootGroup data.n) := by
    have h1 : Nat.card ↥(S : Subgroup ↥F) = Nat.card ↥(SP : Subgroup ↥C) := by
      rw [hS, Sylow.coe_subtype]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSPle).toEquiv
    rw [h1, hSP]
    exact Nat.card_congr det.cQEquivRoot.toEquiv
  -- a Sylow `2`-subgroup of `F/Z(F) ≅ PSU(3, ℓ)` has the same order
  set T : Sylow 2 (↥F ⧸ Subgroup.center ↥F) := default with hT
  have hTcard : Nat.card ↥(T : Subgroup (↥F ⧸ Subgroup.center ↥F)) =
      Nat.card (RootGroup data.n) := by
    have hn : 0 < data.n := Nat.zero_lt_one.trans data.one_lt_n
    have hequiv := Sylow.transportMulEquiv det.residualQuotientEquiv T
      (standardRootSylow data.n hn)
    rw [Nat.card_congr hequiv.toEquiv, coe_standardRootSylow]
    exact (Nat.card_congr (rootEquivStandardRoot data.n).toEquiv).symm
  exact Sylow.not_dvd_natCard_of_natCard_eq S T (hScard.trans hTcard.symm)

end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
