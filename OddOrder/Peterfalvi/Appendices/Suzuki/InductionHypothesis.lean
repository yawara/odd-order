/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.Basic
import OddOrder.GroupTheory.PrimeComplementResidual

/-!
# Peterfalvi Part II, Chapter I §3, Lemma 1 — the induction base

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Chapter I §3, p. 105.

This file isolates the group-theoretic core of Lemma 1 from the classification
of the three target permutation groups. The target-group calculation supplies
that `|Ω| - 1` is a power of two. Proposition 1(c) then makes `Q` a Sylow
`2`-subgroup, and the prime-complement residual API identifies its normal
closure with `O^{2′}(G)`. Simplicity of the normal subgroup `L` finishes the
two equalities in Peterfalvi's statement.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

section /- 3: Application of the Induction Hypothesis (pp. 105–107) -/

/-- The target-group degree calculation used in **Peterfalvi Part II, Chapter I
§3, Lemma 1**: if `|Ω| - 1` is a power of two, regularity of `Q` on the
punctured permutation domain makes `Q` a `2`-group. -/
theorem Q_isPGroup_of_card_Omega_sub_one_eq_two_pow
    (hΩ : ∃ n : ℕ, Nat.card Ω - 1 = 2 ^ n) : IsPGroup 2 hyp.Q := by
  obtain ⟨n, hn⟩ := hΩ
  apply IsPGroup.of_card
  calc
    Nat.card hyp.Q = Nat.card Ω - 1 := by rw [hyp.card_Omega]; omega
    _ = 2 ^ n := hn

/-- Once `Q` is a `2`-group, **Peterfalvi Part II, Chapter I §1,
Proposition 1(c)** pins it down as an ambient Sylow `2`-subgroup. -/
theorem exists_sylow_two_eq_Q (hQp : IsPGroup 2 hyp.Q) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = hyp.Q := by
  obtain ⟨P, hPQ⟩ := hyp.exists_sylow_two_le_Q
  exact ⟨P, (P.is_maximal' hQp hPQ).symm⟩

/-- **Peterfalvi Part II, Chapter I §3, Lemma 1** (group-theoretic core).
Suppose the target-group part of Theorem A has supplied a simple normal
subgroup `L` of odd index and the genuine permutation-degree input that
`|Ω| - 1` is a power of two. Then `Q` is a `2`-group, lies in `L`, and

`L = O^{2′}(G) = ⟨Q^g | g ∈ G⟩`.

Here `O^{2′}(G)` is `Subgroup.primeComplementResidual 2 G`; the last group is
the supremum of the conjugates of `Q`. -/
theorem simple_normal_oddIndex_Q_core (L : Subgroup G)
    (hLnormal : L.Normal) (hLodd : Odd L.index) (hLsimple : IsSimpleGroup L)
    (hΩ : ∃ n : ℕ, Nat.card Ω - 1 = 2 ^ n) :
    IsPGroup 2 hyp.Q ∧
      hyp.Q ≤ L ∧
      L = Subgroup.primeComplementResidual 2 G ∧
      L = (⨆ g : G, hyp.Q.map (MulAut.conj g).toMonoidHom) := by
  have hQp := hyp.Q_isPGroup_of_card_Omega_sub_one_eq_two_pow hΩ
  obtain ⟨P, hP⟩ := hyp.exists_sylow_two_eq_Q hQp
  letI : L.Normal := hLnormal
  have hLcop : Nat.Coprime 2 L.index := Nat.coprime_two_left.mpr hLodd
  let R : Subgroup G := Subgroup.primeComplementResidual 2 G
  have hPR : (P : Subgroup G) ≤ R :=
    Subgroup.le_primeComplementResidual P
  have hQR : hyp.Q ≤ R := by simpa [hP] using hPR
  have hRL : R ≤ L :=
    Subgroup.primeComplementResidual_le_of_coprime_index hLcop
  have hQL : hyp.Q ≤ L := hQR.trans hRL
  have hRnormal : R.Normal := by
    dsimp [R]
    infer_instance
  have hRnormalL : (R.subgroupOf L).Normal :=
    Subgroup.Normal.subgroupOf hRnormal L
  have hQne : hyp.Q ≠ ⊥ := by
    intro hQbot
    have hbad : Even 1 := by simpa [hQbot] using hyp.Q_even
    norm_num at hbad
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hQne
    apply le_bot_iff.mp
    exact hQR.trans_eq hRbot
  have hRL_eq : R = L := by
    rcases (Subgroup.isSimpleGroup_iff.mp hLsimple).2 R hRL hRnormalL with hRbot | hRtop
    · exact (hRne hRbot).elim
    · exact hRtop
  have hRiSup : R = ⨆ g : G, hyp.Q.map (MulAut.conj g).toMonoidHom := by
    simpa [R, hP] using Subgroup.primeComplementResidual_eq_iSup_map_conj P
  exact ⟨hQp, hQL, hRL_eq.symm, hRL_eq.symm.trans hRiSup⟩

end

end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
