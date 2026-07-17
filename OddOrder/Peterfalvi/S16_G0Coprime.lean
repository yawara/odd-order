/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT
import OddOrder.Peterfalvi.S16_NonExistenceGCore
import OddOrder.GroupTheory.ConjClassSet
import OddOrder.GroupTheory.RepresentationTheory.SemilinearFieldModel

/-!
# Peterfalvi (14.11.3), support half: generic elements have order prime to `pq`

**Peterfalvi, Character Theory for the Odd Order Theorem, §14 (pp. 87–92).**

This file proves the *support analysis* half of Peterfalvi (14.11.3): every element of the
generic set `G₀ = G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]` has order prime to `pq`.
This is the group-theoretic input that lets the (3.9.a/c) Galois facts evaluate the `η`-grid
on `G₀` (`η_ij(g) ∈ ℤ`, conjugation pairing), feeding the parity bound `|ψ^{τ₁}(g)| ≥ 1`
of (14.11.3) and the `EtaGenericData` carrier of `S16_NonExistenceG`.

Textbook argument (p. 90): let `a` have order divisible by `p` (the `q` case is symmetric).
Its `p`-part is conjugate into `P#` (as `P ∈ Syl_p(G)`), so — replacing `a` by a conjugate —
`a ∈ C_G(x)` for some `x ∈ P#`.  By (8.6.a)/(13.2.e), `C_G(x) ≤ S`.  If `a ∈ S − S'` then `a`
is conjugate to an element of `W` by the coprime-coset partition (2.1) and the regularity
`C_{S'}(w) = W₂` (`w ∈ W₁#`); if `a ∈ S'` then `a ∈ P#` by (14.4)/(14.6)/(13.12) (the
case-(9.7.b) field structure makes `S' = P ⋊ U` Frobenius, so `C_{S'}(x) ≤ P`).  Hence every
element of order divisible by `p` or `q` lies in `(W#)^G ∪ (P#)^G ∪ (Q#)^G`.

Peterfalvi's `G₀` excludes all of `(W#)^G`, while the §16 carrier excludes only the regular
part `(W − (W₁∪W₂))^G`; the two agree because the singular part of `W#` is absorbed:
`W₁ ≤ Q` and `W₂ ≤ P` (`not_mem_conjClassSet_sharp_W` below).

Coq correspondent: `PFsection14.coprime_typeP_Galois_core` (its proof is the same chain:
`Sylow_Jsub` + `cent1_normedTI` + `mem_sdprod` + `Frobenius_cent1_ker` /
`partition_cent_rcoset` + `regPUW1`).
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.11.3), the `W`-orbit bridge**: an element avoiding the conjugates of the
regular set `W − (W₁ ∪ W₂)`, of `P#`, and of `Q#` avoids the conjugates of all of `W#`.
Indeed `W = W₁ × W₂` (cyclic join with trivial intersection), so
`W# = (W − (W₁∪W₂)) ⊔ W₁# ⊔ W₂#`, and the singular parts are absorbed by the kernels:
`W₁ ≤ Q` (`S15.W1_le_Q`) and `W₂ ≤ P` (`S15.W2_le_P`).  This reconciles the §16 generic set
(which excludes only the regular `W`-orbit) with Peterfalvi's (14.11.3) set (which excludes
`(W#)^G`). -/
theorem not_mem_conjClassSet_sharp_W [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {g : G}
    (hreg : g ∉ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    g ∉ conjClassSet (sharpSubgroup hyp.W) := by
  rintro ⟨w, ⟨hwW, hwne⟩, y, rfl⟩
  letI := hyp.W_cyclic
  letI : CommGroup ↥hyp.W := IsCyclic.commGroup
  have hW1le : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2le : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  -- decompose `w = x · z` with `x ∈ W₁`, `z ∈ W₂` inside the commutative `W`
  have hwmem : (⟨w, hwW⟩ : ↥hyp.W) ∈
      (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) := by
    have h1 : (hyp.W1 ⊔ hyp.W2).subgroupOf hyp.W = ⊤ := by
      rw [← hyp.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, z, hz, hxz⟩ := Subgroup.mem_sup.mp hwmem
  have hcoe : (x : G) * (z : G) = w := by
    have h := congrArg (Subtype.val) hxz
    simpa using h
  have hxW1 : (x : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp hx
  have hzW2 : (z : G) ∈ hyp.W2 := Subgroup.mem_subgroupOf.mp hz
  by_cases hx1 : x = 1
  · by_cases hz1 : z = 1
    · -- `w = 1`, contradicting `w ∈ W#`
      refine hwne ?_
      have hw1 : w = 1 := by rw [← hcoe, hx1, hz1]; simp
      simp [hw1]
    · -- `w = z ∈ W₂# ⊆ P#`
      refine hP ⟨w, ⟨?_, hwne⟩, y, rfl⟩
      have hwz : w = (z : G) := by rw [← hcoe, hx1]; simp
      exact hwz ▸ OddOrder.Peterfalvi.S15.W2_le_P hG hyp hzW2
  · by_cases hz1 : z = 1
    · -- `w = x ∈ W₁# ⊆ Q#`
      refine hQ ⟨w, ⟨?_, hwne⟩, y, rfl⟩
      have hwx : w = (x : G) := by rw [← hcoe, hz1]; simp
      exact hwx ▸ OddOrder.Peterfalvi.S15.W1_le_Q hG hyp hxW1
    · -- both parts nontrivial: `w` is regular
      refine hreg ⟨w, ⟨hwW, ?_⟩, y, rfl⟩
      rintro (hw1 | hw2)
      · -- `w ∈ W₁` forces `z ∈ W₁ ⊓ W₂ = ⊥`
        refine hz1 ?_
        have hzW1 : (z : G) ∈ hyp.W1 := by
          have hzeq : (z : G) = (x : G)⁻¹ * w := by
            rw [← hcoe]; group
          rw [hzeq]
          exact hyp.W1.mul_mem (hyp.W1.inv_mem hxW1) hw1
        have hbot : (z : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨hzW1, hzW2⟩
        rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot
      · -- `w ∈ W₂` forces `x ∈ W₁ ⊓ W₂ = ⊥`
        refine hx1 ?_
        have hxW2 : (x : G) ∈ hyp.W2 := by
          have hxeq : (x : G) = w * (z : G)⁻¹ := by
            rw [← hcoe]; group
          rw [hxeq]
          exact hyp.W2.mul_mem hw2 (hyp.W2.inv_mem hzW2)
        have hbot : (x : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨hxW1, hxW2⟩
        rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot

/-- **The Fitting core `P = S_F` is nontrivial**: it contains `W₂` of prime order `p`. -/
theorem P_ne_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) : hyp.P ≠ ⊥ := by
  intro hbot
  have hW2 := OddOrder.Peterfalvi.S15.W2_le_P hG hyp
  rw [hbot, le_bot_iff] at hW2
  have hp1 : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hW2, Subgroup.card_bot]
  exact hyp.p_prime.one_lt.ne' hp1

/-- **The Fitting core `Q = T_F` is nontrivial**: it contains `W₁` of prime order `q`. -/
theorem Q_ne_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) : hyp.Q ≠ ⊥ := by
  intro hbot
  have hW1 := OddOrder.Peterfalvi.S15.W1_le_Q hG hyp
  rw [hbot, le_bot_iff] at hW1
  have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hW1, Subgroup.card_bot]
  exact hyp.q_prime.one_lt.ne' hq1

/-- **`N_G(P) = S`**: the Fitting core `P = S_F` is normal in the maximal `S` and nontrivial,
so its normalizer is exactly `S` (`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`; a proper
normalizer would contradict maximality/simplicity). -/
theorem normalizer_P_eq_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.P : Set G) = hyp.S := by
  have hPne : maxNilpotentNormalHall hyp.S ≠ ⊥ := hyp.P_eq_SF ▸ P_ne_bot hG hyp
  rw [hyp.P_eq_SF]
  exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
    hyp.S_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hPne

/-- **`N_G(Q) = T`**: T-side dual of `normalizer_P_eq_S`. -/
theorem normalizer_Q_eq_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.Q : Set G) = hyp.T := by
  have hQne : maxNilpotentNormalHall hyp.T ≠ ⊥ := hyp.Q_eq_TF ▸ Q_ne_bot hG hyp
  rw [hyp.Q_eq_TF]
  exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
    hyp.T_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hQne

/-- **Peterfalvi (13.2.e)/(8.6.a), S-side**: for `x ∈ P#` the whole centralizer `C_G(x)`
lies in `S`.  `P` is a TI-subgroup (BG 15.7(a) via `fittingIsTI_of_isTypeP2`), a centralizing
element fixes `x ∈ P ∩ P^c` (`IsTISubset.centralizer_le`), and `N_G(P) = S`. -/
theorem centralizer_le_S_of_mem_sharp_P [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {x : G}
    (hx : x ∈ sharpSubgroup hyp.P) :
    Subgroup.centralizer ({x} : Set G) ≤ hyp.S := by
  have hTI : Subgroup.IsTI hyp.P := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
      hyp.S_maximal
      (OddOrder.Peterfalvi.S13.fittingIsTI_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI)
  have hle := OddOrder.GroupTheory.IsTISubset.centralizer_le hTI hx
  rwa [normalizer_P_eq_S hG hyp] at hle

/-- **Peterfalvi (13.2.e)/(8.6.a), T-side**: for `x ∈ Q#` the whole centralizer `C_G(x)`
lies in `T`.  Dual of `centralizer_le_S_of_mem_sharp_P` (`Q` TI via `fittingIsTI_T`, which
needs `T` type II — supplied by (14.9) `T_typeII` at the §16 consumer). -/
theorem centralizer_le_T_of_mem_sharp_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) {x : G}
    (hx : x ∈ sharpSubgroup hyp.Q) :
    Subgroup.centralizer ({x} : Set G) ≤ hyp.T := by
  have hTI : Subgroup.IsTI hyp.Q := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
      hyp.T_maximal (OddOrder.Peterfalvi.S15.fittingIsTI_T hG hyp hTII)
  have hle := OddOrder.GroupTheory.IsTISubset.centralizer_le hTI hx
  rwa [normalizer_Q_eq_T hG hyp] at hle

/-- **`q` is coprime to `|S'|`** ((8.4)-structure): `S' = P ⋊ U` with `|P| = p^q`
(`card_P_eq`, `p ≠ q`) killing the `P`-side, and `U ⋊ W₁` Frobenius
(`S11.typeP_uW1_frobenius`) killing the `U`-side (trivial if `U = ⊥`).  The coprimality
input for the (2.1) coset collapse in `orderOf_coprime_p_of_not_mem_conj`. -/
theorem coprime_q_card_derivedS [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Nat.Coprime hyp.q (Nat.card ↥(derivedInG hyp.S)) := by
  have hcard : Nat.card ↥(derivedInG hyp.S)
      = Nat.card ↥hyp.Sdata.H * Nat.card ↥hyp.Sdata.U := by
    have hmul := hyp.Sdata.derived_complement.card_mul
    rw [← hmul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv]
  rw [hcard]
  refine Nat.Coprime.mul_right ?_ ?_
  · -- `q` is coprime to `|P| = p^q`
    have hPcard : Nat.card ↥hyp.Sdata.H = hyp.p ^ hyp.q := by
      rw [hyp.Sdata.H_eq, ← hyp.P_eq_SF]
      exact hyp.card_P_eq hG hyp.Sdata_W2_eq
    rw [hPcard]
    exact Nat.Coprime.pow_right _
      ((Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm hyp.p_ne_q))
  · -- `q` is coprime to `|U|` (`U ⋊ W₁` Frobenius; trivial for `U = ⊥`)
    by_cases hU : hyp.Sdata.U = ⊥
    · rw [hU, Subgroup.card_bot]; exact Nat.coprime_one_right _
    · have hF := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hU
      have hc := hF.coprime_card_kernel_complement
      have h1 : Nat.card ↥(hyp.Sdata.U.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1))
          = Nat.card ↥hyp.Sdata.U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
      have h2 : Nat.card ↥(hyp.Sdata.W1.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1))
          = Nat.card ↥hyp.Sdata.W1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      have hq : Nat.card ↥hyp.Sdata.W1 = hyp.q := by
        rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
      have hcUW : Nat.Coprime (Nat.card ↥hyp.Sdata.U) hyp.q := by
        rw [← hq, ← h1, ← h2]; exact hc
      exact hcUW.symm

/-- **`p` is coprime to `|U|`** ((8.4)-structure): `(|H|, |U ⊔ W₁|) = 1`
(`S11.typeP_coprime_H_uW1`) with `p ∣ |H| = p^q` kills `|U|` (trivially if `U = ⊥`). -/
theorem coprime_p_card_U [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Nat.Coprime hyp.p (Nat.card ↥hyp.Sdata.U) := by
  by_cases hU : hyp.Sdata.U = ⊥
  · rw [hU, Subgroup.card_bot]; exact Nat.coprime_one_right _
  · have hcop := OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 hyp.Sdata hU
    have hPcard : Nat.card ↥hyp.Sdata.H = hyp.p ^ hyp.q := by
      rw [hyp.Sdata.H_eq, ← hyp.P_eq_SF]
      exact hyp.card_P_eq hG hyp.Sdata_W2_eq
    have hpH : hyp.p ∣ Nat.card ↥hyp.Sdata.H := by
      rw [hPcard]; exact dvd_pow_self _ hyp.q_prime.pos.ne'
    exact (Nat.Coprime.coprime_dvd_left hpH hcop).coprime_dvd_right
      (Subgroup.card_dvd_of_le le_sup_left)

/-- **The order factorization `|S| = p^q · (|U| · q)`** — `S = (P ⋊ U) ⋊ W₁` via the two
complement splittings (`derived_complement`, `M_complement`), with `|P| = p^q` and `|W₁| = q`. -/
theorem card_S_eq_pow_mul [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Nat.card ↥hyp.S = hyp.p ^ hyp.q * (Nat.card ↥hyp.Sdata.U * hyp.q) := by
  have hS' : Nat.card ↥(derivedInG hyp.S)
      = Nat.card ↥hyp.Sdata.H * Nat.card ↥hyp.Sdata.U := by
    have hmul := hyp.Sdata.derived_complement.card_mul
    rw [← hmul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv]
  have hS : Nat.card ↥hyp.S = Nat.card ↥(derivedInG hyp.S) * hyp.q := by
    have hDle : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
    have hmul := hyp.Sdata.M_complement.card_mul
    have h1 : Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S)
        = Nat.card ↥(derivedInG hyp.S) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
    have h2 : Nat.card ↥(hyp.Sdata.W1.subgroupOf hyp.S) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.W1_le).toEquiv,
        hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
    rw [← hmul, h1, h2]
  have hPcard : Nat.card ↥hyp.Sdata.H = hyp.p ^ hyp.q := by
    rw [hyp.Sdata.H_eq, ← hyp.P_eq_SF]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  rw [hS, hS', hPcard, mul_assoc]

/-- **`P` is a full Sylow `p`-subgroup of `G`** (as a Sylow object with underlying subgroup
`P`).  `P.subgroupOf S` is Sylow in `S` (`|S| = p^q·(|U|·q)` with `p ∤ |U|·q`), `p ∈ σ(S)`
(`N_G(P) = S`), and the BG §10 σ-Sylow theory (`isSylow_sylowMap_of_mem_sigma`) promotes it
to a Sylow of `G`. -/
theorem exists_sylow_coe_eq_P [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    haveI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
    ∃ S₀ : Sylow hyp.p G, (S₀ : Subgroup G) = hyp.P := by
  haveI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  have hPle : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _
  have hPcard : Nat.card ↥hyp.P = hyp.p ^ hyp.q := hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hPsub_card : Nat.card ↥(hyp.P.subgroupOf hyp.S) = hyp.p ^ hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv, hPcard]
  -- `P.subgroupOf S` sits inside a Sylow `Q` of `↥S`; cardinalities force equality.
  have hPsub_pg : IsPGroup hyp.p ↥(hyp.P.subgroupOf hyp.S) :=
    IsPGroup.of_card hPsub_card
  obtain ⟨Q, hQle⟩ := hPsub_pg.exists_le_sylow
  have hcop : Nat.Coprime hyp.p (Nat.card ↥hyp.Sdata.U * hyp.q) :=
    Nat.Coprime.mul_right (coprime_p_card_U hG hyp)
      ((Nat.coprime_primes hyp.p_prime hyp.q_prime).mpr hyp.p_ne_q)
  have hQeq : (Q : Subgroup ↥hyp.S) = hyp.P.subgroupOf hyp.S := by
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
    have hdvd : hyp.p ^ k ∣ hyp.p ^ hyp.q * (Nat.card ↥hyp.Sdata.U * hyp.q) := by
      rw [← hk, ← card_S_eq_pow_mul hG hyp]
      exact Subgroup.card_subgroup_dvd_card _
    have hkq : hyp.p ^ k ∣ hyp.p ^ hyp.q :=
      (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ hcop) hdvd)
    refine (Subgroup.eq_of_le_of_card_ge hQle ?_).symm
    rw [hPsub_card, hk]
    exact Nat.le_of_dvd (pow_pos hyp.p_prime.pos _) hkq
  -- `p ∈ σ(S)`: the Sylow `Q` maps to `P` with normalizer `S`.
  have hmap : (Q : Subgroup ↥hyp.S).map hyp.S.subtype = hyp.P := by
    rw [hQeq]
    exact Subgroup.map_subgroupOf_eq_of_le hPle
  have hpσ : hyp.p ∈ OddOrder.BG.Ch3.S10.sigma hyp.S := by
    refine ⟨Nat.mem_primeFactors.mpr ⟨hyp.p_prime, ?_, Nat.card_pos.ne'⟩, Q, ?_⟩
    · exact dvd_trans (dvd_pow_self _ hyp.q_prime.pos.ne')
        (hPcard ▸ Subgroup.card_dvd_of_le hPle)
    · rw [hmap]
      exact (normalizer_P_eq_S hG hyp).le
  obtain ⟨S₀, hS₀⟩ := OddOrder.BG.Ch3.S10.isSylow_sylowMap_of_mem_sigma hpσ Q
  exact ⟨S₀, by rw [hS₀, hmap]⟩

/-- **`P` absorbs the order-`p` elements of `G` up to conjugacy** — the element form of
`P ∈ Syl_p(G)` (`exists_sylow_coe_eq_P`): any order-`p` element generates a `p`-group, lies
in some Sylow, and Sylow conjugacy moves that Sylow onto `P`. -/
theorem exists_conj_mem_P_of_orderOf_eq_p [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {a : G}
    (ha : orderOf a = hyp.p) : ∃ y : G, y * a * y⁻¹ ∈ hyp.P := by
  haveI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_coe_eq_P hG hyp
  have hA : IsPGroup hyp.p ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨R, hR⟩ := hA.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G R S₀
  refine ⟨y, ?_⟩
  have hcoe : MulAut.conj y • (R : Subgroup G) = hyp.P := by
    have h := congrArg Sylow.toSubgroup hy
    rwa [Sylow.coe_subgroup_smul, hS₀] at h
  rw [← hcoe]
  exact ⟨a, hR (Subgroup.mem_zpowers a), rfl⟩

/-- **The concrete BG Frobenius group `F ⋊ U*` has Frobenius kernel `F`** — an element
commuting with a nontrivial additive point lies in the additive kernel.  The norm-one units
act by field multiplication (`normOneMulAction_apply`), which is fixed-point-free on `F#`:
`u·m = m` with `m ≠ 0` forces `u = 1`. -/
theorem commute_inl_mem_range_inl {p q : ℕ} [Fact p.Prime]
    {m : OddOrder.BG.AppC.NormSet.additiveFieldGroup p q} (hm : m ≠ 1)
    {w : OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup p q}
    (hcomm : w * SemidirectProduct.inl m = SemidirectProduct.inl m * w) :
    w ∈ (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup p q →*
        OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup p q).range := by
  -- compare left components: `w.left · φ(w.right)(m) = m · w.left`
  have hleft := congrArg SemidirectProduct.left hcomm
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hleft
  -- the additive group is commutative: cancel `w.left`
  have hfix : OddOrder.BG.AppC.NormSet.normOneMulAction p q w.right m = m := by
    have hcomm' : m * w.left = w.left * m := mul_comm _ _
    rw [hcomm'] at hleft
    exact mul_left_cancel hleft
  -- fixed point of field multiplication with `m ≠ 0` forces the unit to be `1`
  have hm0 : Multiplicative.toAdd m ≠ 0 := by
    intro h0
    exact hm (by simpa using congrArg Multiplicative.ofAdd h0)
  have humul : ((w.right : (GaloisField p q)ˣ) : GaloisField p q)
      * Multiplicative.toAdd m = Multiplicative.toAdd m := by
    have h := OddOrder.BG.AppC.NormSet.normOneMulAction_apply p q w.right
      (Multiplicative.toAdd m)
    rw [ofAdd_toAdd] at h
    rw [← h, hfix]
  have hu1 : ((w.right : (GaloisField p q)ˣ) : GaloisField p q) = 1 :=
    mul_right_cancel₀ hm0 (by rw [humul, one_mul])
  have hright : w.right = 1 := Subtype.ext (Units.ext hu1)
  refine ⟨w.left, ?_⟩
  have h := SemidirectProduct.inl_left_mul_inr_right w
  rwa [hright, map_one, mul_one] at h

/-- **Peterfalvi (14.6)/(13.12), the Frobenius-kernel property of `S' = PU`, transported from
the concrete (14.2.a) field model**: `C_{S'}(x) ≤ P` for `x ∈ P#`.  `S' = P ⊔ U` is the image
of the concrete `F ⋊ U*` under the injective `σ` (`FieldNormalizerData`), and in the model
every element commuting with a nontrivial kernel point lies in the kernel
(`commute_inl_mem_range_inl`).  This discharges the `hfrob` input of
`orderOf_coprime_p_of_not_mem_conj` as soon as the §13 supply provides the (14.2.a) carrier
(`fieldNormalizerData_of_repr`, issue 2035/9000 sphere). -/
theorem FieldNormalizerData.derived_inf_centralizer_le_P
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ sharpSubgroup hyp.base.P) :
    derivedInG hyp.base.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.P := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rintro g' ⟨hg'S', hg'cent⟩
  -- `S' = P ⊔ U` is the image of `kernel ⊔ complement` under `σ`
  have hg'mem : g' ∈ (fieldNormalizerKernel hyp ⊔ fieldNormalizerComplement hyp).map
      data.sigma := by
    rw [Subgroup.map_sup, data.sigma_P_eq_P, data.sigma_U_eq_U, ← hyp.base.S_deriv_eq_PU]
    exact hg'S'
  obtain ⟨w, -, rfl⟩ := hg'mem
  -- `x = σ (inl m)` for a nontrivial additive point `m`
  have hxmem : x ∈ (fieldNormalizerKernel hyp).map data.sigma := by
    rw [data.sigma_P_eq_P]; exact hx.1
  obtain ⟨wx, hwx, hxeq⟩ := hxmem
  have hwx' : wx ∈ (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp).range := hwx
  obtain ⟨m, rfl⟩ := hwx'
  have hmne : m ≠ 1 := by
    rintro rfl
    refine hx.2 ?_
    have hx1 : x = 1 := by rw [← hxeq, map_one, map_one]
    simp [hx1]
  -- pull the commutation back through the injective `σ`
  have hgx : data.sigma w * x = x * data.sigma w :=
    Subgroup.mem_centralizer_singleton_iff.mp hg'cent
  have hcomm : w * SemidirectProduct.inl m = SemidirectProduct.inl m * w := by
    apply data.sigma_injective
    rw [map_mul, map_mul, hxeq]
    exact hgx
  -- concrete Frobenius kernel + push forward
  obtain ⟨mw, hmw⟩ := commute_inl_mem_range_inl hmne hcomm
  rw [← data.sigma_P_eq_P]
  exact ⟨w, ⟨mw, hmw⟩, rfl⟩

/-- **Peterfalvi (14.11.3), S-side core**: an element avoiding the conjugates of `W#` and of
`P#` has order prime to `p`.

Contrapositive of the textbook chain (p. 90): if `p ∣ |g|`, the order-`p` power of `g` is
conjugate into `P#` (`exists_conj_mem_P_of_orderOf_eq_p`), so — conjugating `g` — `g ∈ C_G(a)
≤ S` for some `a ∈ P#` (`centralizer_le_S_of_mem_sharp_P`).  Decompose `g = d·w` along
`S = S' ⋊ W₁` (`Sdata.M_complement`).  If `w = 1` then `g = d ∈ C_{S'}(a) ≤ P#` (the `hfrob`
input — the case-(9.7.b) Frobenius kernel, discharged by
`FieldNormalizerData.derived_inf_centralizer_le_P` once the (14.2.a) carrier is supplied).
If `w ≠ 1` the coprime
coset collapse (2.1) (`exists_mem_centralizer_conj`, with `(q, |S'|) = 1` =
`coprime_q_card_derivedS`) conjugates `g` into `C_{S'}(w)·w = W₂·w ⊆ W#`
(`Sdata.centralizer_W1`).  Either way `g` meets an excluded orbit.
Coq: `PFsection14.coprime_typeP_Galois_core`. -/
theorem orderOf_coprime_p_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (hfrob : ∀ x ∈ sharpSubgroup hyp.P,
      derivedInG hyp.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.P) {g : G}
    (hW : g ∉ conjClassSet (sharpSubgroup hyp.W))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P)) :
    Nat.Coprime (orderOf g) hyp.p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hyp.p_prime]
  intro hdvd
  -- `g ≠ 1` and the order-`p` power `a₀` of `g`
  have hord_ne : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one, Nat.dvd_one] at hdvd
    exact hyp.p_prime.one_lt.ne' hdvd
  set a₀ : G := g ^ (orderOf g / hyp.p) with ha₀def
  have ha₀ord : orderOf a₀ = hyp.p := by
    rw [ha₀def, orderOf_pow, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
      Nat.div_div_self hdvd hord_ne]
  have ha₀ne : a₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha₀ord
    exact hyp.p_prime.one_lt.ne ha₀ord
  have hcomm : Commute g a₀ := (Commute.refl g).pow_right _
  -- conjugate the `p`-part into `P#`
  obtain ⟨y, hyP⟩ := exists_conj_mem_P_of_orderOf_eq_p hG hyp ha₀ord
  set a : G := y * a₀ * y⁻¹ with hadef
  have haP : a ∈ sharpSubgroup hyp.P := by
    refine ⟨hyP, ?_⟩
    intro h1
    refine ha₀ne ?_
    have ha1 : a = 1 := h1
    have : a₀ = y⁻¹ * a * y := by rw [hadef]; group
    rw [this, ha1, mul_one, inv_mul_cancel]
  -- the conjugate `g' = y g y⁻¹` centralizes `a`, hence lies in `S`
  set g' : G := y * g * y⁻¹ with hg'def
  have hg'ne : g' ≠ 1 := by
    intro h
    refine hg1 ?_
    have : g = y⁻¹ * g' * y := by rw [hg'def]; group
    rw [this, h, mul_one, inv_mul_cancel]
  have hg'cent : g' ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g' * a = y * (g * a₀) * y⁻¹ := by rw [hg'def, hadef]; group
      _ = y * (a₀ * g) * y⁻¹ := by rw [hcomm.eq]
      _ = a * g' := by rw [hg'def, hadef]; group
  have hg'S : g' ∈ hyp.S := centralizer_le_S_of_mem_sharp_P hG hyp haP hg'cent
  -- decompose `g' = d · w` along `S = S' ⋊ W₁`
  obtain ⟨⟨d, w⟩, hdw⟩ :=
    (Subgroup.IsComplement.existsUnique hyp.Sdata.M_complement
      (⟨g', hg'S⟩ : ↥hyp.S)).exists
  have hdmem : ((d : ↥hyp.S) : G) ∈ derivedInG hyp.S := Subgroup.mem_subgroupOf.mp d.2
  have hg'eq : ((d : ↥hyp.S) : G) * ((w : ↥hyp.S) : G) = g' := by
    have h := congrArg (fun x : ↥hyp.S => (x : G)) hdw
    simpa using h
  by_cases hw1 : (w : ↥hyp.S) = (1 : ↥hyp.S)
  · -- `w = 1`: `g' ∈ C_{S'}(a) ≤ P`, contradicting `g ∉ (P#)^G`
    have hg'derived : g' ∈ derivedInG hyp.S := by
      rw [← hg'eq, hw1]
      simpa using hdmem
    have hg'P : g' ∈ hyp.P := hfrob a haP ⟨hg'derived, hg'cent⟩
    refine hP ⟨g', ⟨hg'P, fun h => hg'ne h⟩, y⁻¹, ?_⟩
    rw [hg'def]; group
  · -- `w ≠ 1`: the (2.1) coset collapse conjugates `g` into `W₂ · w ⊆ W#`
    set w₀ : G := ((w : ↥hyp.S) : G) with hw₀def
    have hw₀W1 : w₀ ∈ hyp.W1 := by
      rw [← hyp.Sdata_W1_eq]
      exact Subgroup.mem_subgroupOf.mp w.2
    have hw₀ne : w₀ ≠ 1 := by
      intro h
      exact hw1 (Subtype.ext (by simpa [hw₀def] using h))
    have hw₀ord : orderOf w₀ = hyp.q := by
      have hdvd' : orderOf w₀ ∣ hyp.q := by
        rw [hyp.q_eq_card_W1]
        exact Subgroup.orderOf_dvd_natCard _ hw₀W1
      rcases (Nat.Prime.eq_one_or_self_of_dvd hyp.q_prime _ hdvd') with h1 | hq
      · exact absurd (orderOf_eq_one_iff.mp h1) hw₀ne
      · exact hq
    have hnorm : ∀ x ∈ derivedInG hyp.S, w₀ * x * w₀⁻¹ ∈ derivedInG hyp.S := by
      intro x hx
      have hw₀norm : w₀ ∈ Subgroup.normalizer (derivedInG hyp.S) :=
        OddOrder.BG.Ch3.S10.le_normalizer_derivedInG hyp.S (SetLike.coe_mem (w : ↥hyp.S))
      exact (Subgroup.mem_normalizer_iff.mp hw₀norm x).mp hx
    have hcop : Nat.Coprime (orderOf w₀) (Nat.card ↥(derivedInG hyp.S)) := by
      rw [hw₀ord]; exact coprime_q_card_derivedS hG hyp
    obtain ⟨c, hc, x, hx, hxeq⟩ :=
      OddOrder.GroupTheory.exists_mem_centralizer_conj hcop hnorm hdmem
    -- `C_{S'}(w₀) = W₂` ((8.4) regularity)
    have hcW2 : c ∈ hyp.W2 := by
      have hreg := hyp.Sdata.centralizer_W1 w₀ (hyp.Sdata_W1_eq ▸ hw₀W1) hw₀ne
      rw [← hyp.Sdata_W2_eq, ← hreg]
      exact hc
    have hW1le : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have hW2le : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have hcwW : c * w₀ ∈ hyp.W := hyp.W.mul_mem (hW2le hcW2) (hW1le hw₀W1)
    have hcwne : c * w₀ ≠ 1 := by
      intro h
      have hw₀W2 : w₀ ∈ hyp.W2 := by
        have hinv : w₀ = c⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [hinv]
        exact hyp.W2.inv_mem hcW2
      have hbot : w₀ ∈ hyp.W1 ⊓ hyp.W2 := ⟨hw₀W1, hw₀W2⟩
      rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
      exact hw₀ne hbot
    refine hW ⟨c * w₀, ⟨hcwW, fun h => hcwne h⟩, (x * y)⁻¹, ?_⟩
    have h1 : c * w₀ = x * g' * x⁻¹ := by
      rw [← hxeq, hg'eq]
    rw [h1, hg'def]; group

/-- **`p` is coprime to `|T'|`** (T-side dual of `coprime_q_card_derivedS`): `T' = Q ⋊ V`
with `|Q| = q^p` (`card_Q_eq`, `p ≠ q`) killing the `Q`-side, and `V ⋊ W₂` Frobenius
(`S11.typeP_uW1_frobenius` on the reconciled T-data) killing the `V`-side. -/
theorem coprime_p_card_derivedT [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) :
    Nat.Coprime hyp.p (Nat.card ↥(derivedInG hyp.T)) := by
  obtain ⟨tpd, htpdV, htpdW1, htpdW2⟩ :=
    OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp
  have hcard : Nat.card ↥(derivedInG hyp.T)
      = Nat.card ↥tpd.H * Nat.card ↥tpd.U := by
    have hmul := tpd.derived_complement.card_mul
    rw [← hmul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv]
  rw [hcard]
  refine Nat.Coprime.mul_right ?_ ?_
  · -- `p` is coprime to `|Q| = q^p`
    have hQcard : Nat.card ↥tpd.H = hyp.q ^ hyp.p := by
      rw [tpd.H_eq, ← hyp.Q_eq_TF]
      exact OddOrder.Peterfalvi.S15.card_Q_eq hG hyp hTII
    rw [hQcard]
    exact Nat.Coprime.pow_right _
      ((Nat.coprime_primes hyp.p_prime hyp.q_prime).mpr hyp.p_ne_q)
  · -- `p` is coprime to `|V|` (`V ⋊ W₂` Frobenius; trivial for `V = ⊥`)
    by_cases hV : tpd.U = ⊥
    · rw [hV, Subgroup.card_bot]; exact Nat.coprime_one_right _
    · have hF := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd hV
      have hc := hF.coprime_card_kernel_complement
      have h1 : Nat.card ↥(tpd.U.subgroupOf (tpd.U ⊔ tpd.W1)) = Nat.card ↥tpd.U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
      have h2 : Nat.card ↥(tpd.W1.subgroupOf (tpd.U ⊔ tpd.W1)) = Nat.card ↥tpd.W1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      have hp : Nat.card ↥tpd.W1 = hyp.p := by rw [htpdW1, ← hyp.p_eq_card_W2]
      have hcUW : Nat.Coprime (Nat.card ↥tpd.U) hyp.p := by
        rw [← hp, ← h1, ← h2]; exact hc
      exact hcUW.symm

/-- **`Q` is a full Sylow `q`-subgroup of `G`** (T-side dual of `exists_sylow_coe_eq_P`).
`Q.subgroupOf T` is Sylow in `T` (`|Q| = q^p` with `q` coprime to `[T : Q]` — `Q = T_F` is a
Hall subgroup of `T`), `q ∈ σ(T)` (`N_G(Q) = T`), and the BG §10 σ-Sylow theory promotes it
to a Sylow of `G`. -/
theorem exists_sylow_coe_eq_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) :
    haveI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
    ∃ S₀ : Sylow hyp.q G, (S₀ : Subgroup G) = hyp.Q := by
  haveI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hQle : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _
  have hQcard : Nat.card ↥hyp.Q = hyp.q ^ hyp.p :=
    OddOrder.Peterfalvi.S15.card_Q_eq hG hyp hTII
  have hQsub_card : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = hyp.q ^ hyp.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv, hQcard]
  have hQsub_pg : IsPGroup hyp.q ↥(hyp.Q.subgroupOf hyp.T) :=
    IsPGroup.of_card hQsub_card
  obtain ⟨R, hRle⟩ := hQsub_pg.exists_le_sylow
  -- `Q = T_F` is Hall in `T`, so `q` is coprime to the index `[T : Q]`
  have hHall : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf hyp.T))
      ((hyp.Q.subgroupOf hyp.T).index) := by
    have h := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T).coprime_index
    rwa [← hyp.Q_eq_TF] at h
  have hcopq : Nat.Coprime hyp.q ((hyp.Q.subgroupOf hyp.T).index) := by
    refine Nat.Coprime.coprime_dvd_left ?_ hHall
    rw [hQsub_card]
    exact dvd_pow_self _ hyp.p_prime.pos.ne'
  have hRQ : (R : Subgroup ↥hyp.T) = hyp.Q.subgroupOf hyp.T := by
    obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
    have hdvd : hyp.q ^ k ∣ hyp.q ^ hyp.p * ((hyp.Q.subgroupOf hyp.T).index) := by
      rw [← hk, ← hQsub_card, Subgroup.card_mul_index]
      exact Subgroup.card_subgroup_dvd_card _
    have hkq : hyp.q ^ k ∣ hyp.q ^ hyp.p :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ hcopq) hdvd
    refine (Subgroup.eq_of_le_of_card_ge hRle ?_).symm
    rw [hQsub_card, hk]
    exact Nat.le_of_dvd (pow_pos hyp.q_prime.pos _) hkq
  have hmap : (R : Subgroup ↥hyp.T).map hyp.T.subtype = hyp.Q := by
    rw [hRQ]
    exact Subgroup.map_subgroupOf_eq_of_le hQle
  have hqσ : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.T := by
    refine ⟨Nat.mem_primeFactors.mpr ⟨hyp.q_prime, ?_, Nat.card_pos.ne'⟩, R, ?_⟩
    · exact dvd_trans (dvd_pow_self _ hyp.p_prime.pos.ne')
        (hQcard ▸ Subgroup.card_dvd_of_le hQle)
    · rw [hmap]
      exact (normalizer_Q_eq_T hG hyp).le
  obtain ⟨S₀, hS₀⟩ := OddOrder.BG.Ch3.S10.isSylow_sylowMap_of_mem_sigma hqσ R
  exact ⟨S₀, by rw [hS₀, hmap]⟩

/-- **`Q` absorbs the order-`q` elements of `G` up to conjugacy** (T-side dual of
`exists_conj_mem_P_of_orderOf_eq_p`). -/
theorem exists_conj_mem_Q_of_orderOf_eq_q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) {a : G}
    (ha : orderOf a = hyp.q) : ∃ y : G, y * a * y⁻¹ ∈ hyp.Q := by
  haveI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_coe_eq_Q hG hyp hTII
  have hA : IsPGroup hyp.q ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨R, hR⟩ := hA.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G R S₀
  refine ⟨y, ?_⟩
  have hcoe : MulAut.conj y • (R : Subgroup G) = hyp.Q := by
    have h := congrArg Sylow.toSubgroup hy
    rwa [Sylow.coe_subgroup_smul, hS₀] at h
  rw [← hcoe]
  exact ⟨a, hR (Subgroup.mem_zpowers a), rfl⟩

/-- **Peterfalvi (14.11.3), T-side core**: an element avoiding the conjugates of `W#` and of
`Q#` has order prime to `q`.  Dual of `orderOf_coprime_p_of_not_mem_conj`, along
`T = T' ⋊ W₂`, `T' = Q ⋊ V`, `C_{T'}(w) = W₁` (`w ∈ W₂#`), with (14.4)/(13.12) in place of
(14.6)/(13.12) for the `hfrobT` Frobenius-kernel input. -/
theorem orderOf_coprime_q_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T)
    (hfrobT : ∀ x ∈ sharpSubgroup hyp.Q,
      derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q) {g : G}
    (hW : g ∉ conjClassSet (sharpSubgroup hyp.W))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    Nat.Coprime (orderOf g) hyp.q := by
  obtain ⟨tpd, htpdV, htpdW1, htpdW2⟩ :=
    OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hyp.q_prime]
  intro hdvd
  -- `g ≠ 1` and the order-`q` power `a₀` of `g`
  have hord_ne : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one, Nat.dvd_one] at hdvd
    exact hyp.q_prime.one_lt.ne' hdvd
  set a₀ : G := g ^ (orderOf g / hyp.q) with ha₀def
  have ha₀ord : orderOf a₀ = hyp.q := by
    rw [ha₀def, orderOf_pow, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
      Nat.div_div_self hdvd hord_ne]
  have ha₀ne : a₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha₀ord
    exact hyp.q_prime.one_lt.ne ha₀ord
  have hcomm : Commute g a₀ := (Commute.refl g).pow_right _
  -- conjugate the `q`-part into `Q#`
  obtain ⟨y, hyQ⟩ := exists_conj_mem_Q_of_orderOf_eq_q hG hyp hTII ha₀ord
  set a : G := y * a₀ * y⁻¹ with hadef
  have haQ : a ∈ sharpSubgroup hyp.Q := by
    refine ⟨hyQ, ?_⟩
    intro h1
    refine ha₀ne ?_
    have ha1 : a = 1 := h1
    have : a₀ = y⁻¹ * a * y := by rw [hadef]; group
    rw [this, ha1, mul_one, inv_mul_cancel]
  -- the conjugate `g' = y g y⁻¹` centralizes `a`, hence lies in `T`
  set g' : G := y * g * y⁻¹ with hg'def
  have hg'ne : g' ≠ 1 := by
    intro h
    refine hg1 ?_
    have : g = y⁻¹ * g' * y := by rw [hg'def]; group
    rw [this, h, mul_one, inv_mul_cancel]
  have hg'cent : g' ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g' * a = y * (g * a₀) * y⁻¹ := by rw [hg'def, hadef]; group
      _ = y * (a₀ * g) * y⁻¹ := by rw [hcomm.eq]
      _ = a * g' := by rw [hg'def, hadef]; group
  have hg'T : g' ∈ hyp.T := centralizer_le_T_of_mem_sharp_Q hG hyp hTII haQ hg'cent
  -- decompose `g' = d · w` along `T = T' ⋊ W₂`
  obtain ⟨⟨d, w⟩, hdw⟩ :=
    (Subgroup.IsComplement.existsUnique tpd.M_complement
      (⟨g', hg'T⟩ : ↥hyp.T)).exists
  have hdmem : ((d : ↥hyp.T) : G) ∈ derivedInG hyp.T := Subgroup.mem_subgroupOf.mp d.2
  have hg'eq : ((d : ↥hyp.T) : G) * ((w : ↥hyp.T) : G) = g' := by
    have h := congrArg (fun x : ↥hyp.T => (x : G)) hdw
    simpa using h
  by_cases hw1 : (w : ↥hyp.T) = (1 : ↥hyp.T)
  · -- `w = 1`: `g' ∈ C_{T'}(a) ≤ Q`, contradicting `g ∉ (Q#)^G`
    have hg'derived : g' ∈ derivedInG hyp.T := by
      rw [← hg'eq, hw1]
      simpa using hdmem
    have hg'Q : g' ∈ hyp.Q := hfrobT a haQ ⟨hg'derived, hg'cent⟩
    refine hQ ⟨g', ⟨hg'Q, fun h => hg'ne h⟩, y⁻¹, ?_⟩
    rw [hg'def]; group
  · -- `w ≠ 1`: the (2.1) coset collapse conjugates `g` into `W₁ · w ⊆ W#`
    set w₀ : G := ((w : ↥hyp.T) : G) with hw₀def
    have hw₀W2 : w₀ ∈ hyp.W2 := by
      rw [← htpdW1]
      exact Subgroup.mem_subgroupOf.mp w.2
    have hw₀ne : w₀ ≠ 1 := by
      intro h
      exact hw1 (Subtype.ext (by simpa [hw₀def] using h))
    have hw₀ord : orderOf w₀ = hyp.p := by
      have hdvd' : orderOf w₀ ∣ hyp.p := by
        rw [hyp.p_eq_card_W2]
        exact Subgroup.orderOf_dvd_natCard _ hw₀W2
      rcases (Nat.Prime.eq_one_or_self_of_dvd hyp.p_prime _ hdvd') with h1 | hp
      · exact absurd (orderOf_eq_one_iff.mp h1) hw₀ne
      · exact hp
    have hnorm : ∀ x ∈ derivedInG hyp.T, w₀ * x * w₀⁻¹ ∈ derivedInG hyp.T := by
      intro x hx
      have hw₀norm : w₀ ∈ Subgroup.normalizer (derivedInG hyp.T) :=
        OddOrder.BG.Ch3.S10.le_normalizer_derivedInG hyp.T (SetLike.coe_mem (w : ↥hyp.T))
      exact (Subgroup.mem_normalizer_iff.mp hw₀norm x).mp hx
    have hcop : Nat.Coprime (orderOf w₀) (Nat.card ↥(derivedInG hyp.T)) := by
      rw [hw₀ord]; exact coprime_p_card_derivedT hG hyp hTII
    obtain ⟨c, hc, x, hx, hxeq⟩ :=
      OddOrder.GroupTheory.exists_mem_centralizer_conj hcop hnorm hdmem
    -- `C_{T'}(w₀) = W₁` ((8.4) regularity, T-side)
    have hcW1 : c ∈ hyp.W1 := by
      have hw₀tpd : w₀ ∈ tpd.W1 := by rw [htpdW1]; exact hw₀W2
      have hreg := tpd.centralizer_W1 w₀ hw₀tpd hw₀ne
      rw [← htpdW2, ← hreg]
      exact hc
    have hW1le : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have hW2le : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have hcwW : c * w₀ ∈ hyp.W := hyp.W.mul_mem (hW1le hcW1) (hW2le hw₀W2)
    have hcwne : c * w₀ ≠ 1 := by
      intro h
      have hw₀W1 : w₀ ∈ hyp.W1 := by
        have hinv : w₀ = c⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [hinv]
        exact hyp.W1.inv_mem hcW1
      have hbot : w₀ ∈ hyp.W1 ⊓ hyp.W2 := ⟨hw₀W1, hw₀W2⟩
      rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
      exact hw₀ne hbot
    refine hW ⟨c * w₀, ⟨hcwW, fun h => hcwne h⟩, (x * y)⁻¹, ?_⟩
    have h1 : c * w₀ = x * g' * x⁻¹ := by
      rw [← hxeq, hg'eq]
    rw [h1, hg'def]; group

/-- **Peterfalvi (14.11.3), support half**: an element avoiding the conjugates of the regular
set `W − (W₁ ∪ W₂)`, of `P#`, and of `Q#` — i.e. any element of the generic set `G₀` off the
Dade support — has order prime to `pq`.  Assembles the `W`-orbit bridge with the two one-prime
cores.  This is the group-theoretic half of (14.11.3); the character half ((3.9.a/c) `η`-grid
integrality/pairing on `G₀`) consumes it through `EtaGenericData`. -/
theorem orderOf_coprime_pq_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T)
    (hfrob : ∀ x ∈ sharpSubgroup hyp.P,
      derivedInG hyp.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.P)
    (hfrobT : ∀ x ∈ sharpSubgroup hyp.Q,
      derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q) {g : G}
    (hreg : g ∉ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    Nat.Coprime (orderOf g) (hyp.p * hyp.q) := by
  have hW := not_mem_conjClassSet_sharp_W hG hyp hreg hP hQ
  exact Nat.Coprime.mul_right (orderOf_coprime_p_of_not_mem_conj hG hyp hfrob hW hP)
    (orderOf_coprime_q_of_not_mem_conj hG hyp hTII hfrobT hW hQ)

/-! ### The T-side (14.4)/(9.7.b) field-model carrier and its Frobenius-kernel transport

T-side dual of the (14.2.a) engine: `T' = Q ⋊ V ≅ F_{q^p} ⋊ V*` (in case (9.7.b) for `T`,
which (14.4) forces, with `D = 1` and `v = (q^p−1)/(q−1)`), so `C_{T'}(x) ≤ Q` for `x ∈ Q#`
transports from the concrete model exactly as on the S-side. -/

/-- The concrete T-side Frobenius group `F_{q^p} ⋊ V*` (BG Appendix C model with the T-side
parameters: kernel prime `q`, exponent `p`). -/
abbrev tFieldFrobeniusGroup (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup hyp.q hyp.p

/-- The additive kernel `F_{q^p} ≤ F_{q^p} ⋊ V*` of the T-side model. -/
noncomputable def tFieldKernel (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Subgroup (tFieldFrobeniusGroup hyp) :=
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.q hyp.p →*
        tFieldFrobeniusGroup hyp).range

/-- The norm-one complement `V* ≤ F_{q^p} ⋊ V*` of the T-side model. -/
noncomputable def tFieldComplement (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Subgroup (tFieldFrobeniusGroup hyp) :=
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  (SemidirectProduct.inr :
      OddOrder.BG.AppC.NormSet.normOneUnits hyp.q hyp.p →*
        tFieldFrobeniusGroup hyp).range

/-- **Minimal T-side (14.4)/(9.7.b) field-model carrier** — the T-side dual of the (14.2.a)
`FieldNormalizerData`: an injective realization of `T' = Q ⋊ V` as the concrete Frobenius
group `F_{q^p} ⋊ V*`, with the additive kernel matching `Q` and the norm-one complement
matching `V`.  Its supply is the (14.4)-case (9.7.b) resolution for `T` (`v = (q^p−1)/(q−1)`,
`D = 1` — the `T_side_caseB_facts`/issue-9000 sphere); its payoff is the transport
`TFieldModelData.derived_inf_centralizer_le_Q`, the `hfrobT` input of the (14.11.3) chain. -/
structure TFieldModelData (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) where
  sigma : tFieldFrobeniusGroup hyp →* G
  sigma_injective : Function.Injective sigma
  sigma_Q_eq_Q : (tFieldKernel hyp).map sigma = hyp.Q
  sigma_V_eq_V : (tFieldComplement hyp).map sigma = hyp.V

/-- **Peterfalvi (14.4)/(13.12)-dual, the Frobenius-kernel property of `T' = QV`, transported
from the T-side field model**: `C_{T'}(x) ≤ Q` for `x ∈ Q#`.  Mirror of
`FieldNormalizerData.derived_inf_centralizer_le_P` through `commute_inl_mem_range_inl`
(which is generic in the two primes).  Discharges the `hfrobT` input of
`orderOf_coprime_q_of_not_mem_conj` as soon as the (14.4) carrier is supplied. -/
theorem TFieldModelData.derived_inf_centralizer_le_Q [Finite G]
    {hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)} (data : TFieldModelData hyp)
    {x : G} (hx : x ∈ sharpSubgroup hyp.Q) :
    derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q := by
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  rintro g' ⟨hg'T', hg'cent⟩
  -- `T' = Q ⊔ V` is the image of `kernel ⊔ complement` under `σ`
  have hg'mem : g' ∈ (tFieldKernel hyp ⊔ tFieldComplement hyp).map data.sigma := by
    rw [Subgroup.map_sup, data.sigma_Q_eq_Q, data.sigma_V_eq_V, ← hyp.T_deriv_eq_QV]
    exact hg'T'
  obtain ⟨w, -, rfl⟩ := hg'mem
  -- `x = σ (inl m)` for a nontrivial additive point `m`
  have hxmem : x ∈ (tFieldKernel hyp).map data.sigma := by
    rw [data.sigma_Q_eq_Q]; exact hx.1
  obtain ⟨wx, hwx, hxeq⟩ := hxmem
  have hwx' : wx ∈ (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.q hyp.p →*
        tFieldFrobeniusGroup hyp).range := hwx
  obtain ⟨m, rfl⟩ := hwx'
  have hmne : m ≠ 1 := by
    rintro rfl
    refine hx.2 ?_
    have hx1 : x = 1 := by rw [← hxeq, map_one, map_one]
    simp [hx1]
  -- pull the commutation back through the injective `σ`
  have hgx : data.sigma w * x = x * data.sigma w :=
    Subgroup.mem_centralizer_singleton_iff.mp hg'cent
  have hcomm : w * SemidirectProduct.inl m = SemidirectProduct.inl m * w := by
    apply data.sigma_injective
    rw [map_mul, map_mul, hxeq]
    exact hgx
  -- concrete Frobenius kernel + push forward
  obtain ⟨mw, hmw⟩ := commute_inl_mem_range_inl hmne hcomm
  rw [← data.sigma_Q_eq_Q]
  exact ⟨w, ⟨mw, hmw⟩, rfl⟩

/-- **T-side field-model producer** (`(14.4)`-dual of `fieldNormalizerData_of_repr`): from the
`(9.7.b)` T-side field-algebra package — an additive field iso `e : Additive ↥Q ≃+ 𝔽_{q^p}`, a
norm-one Singer character `μ : ↥V →* 𝔽_{q^p}ˣ`, the `V`-conjugation closure `hVQ` on `Q`, and the
`(14.2)(a)`-dual equivariance `hcompat` (`e (ofMul (v x v⁻¹)) = μ v • e (ofMul x)`) — assemble the
injective realization `σ : F_{q^p} ⋊ V* →* G` with kernel `Q` and complement `V`, i.e. a
`TFieldModelData hyp`.  The `Q ⊓ V = ⊥` disjointness is the ungated `hyp.Q_inf_V_eq_bot` field.

This is the ungated heart of the T-side `(14.4)` reduction: it invokes the generic
`SemilinearFieldModel.fieldModelEmbedding` (`E = Q`, `C = V`, `r = q`, `s = p`), routing the lift
compatibility through the generic `hcompatLift_of_equivariant`.  Carries no `sorry`; its only
external inputs are the field-algebra data `(e, μ, hcompat)`, which the `(9.7.b)` resolution for
`T` (`exists_field_semilinear` + Singer, issue-9000 sphere) supplies. -/
theorem tFieldModelData_of_repr (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (e : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         Additive ↥hyp.Q ≃+ GaloisField hyp.q hyp.p)
    (μ : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         ↥hyp.V →* (GaloisField hyp.q hyp.p)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.q hyp.p)
    (hVQ : ∀ (v : ↥hyp.V) (x : ↥hyp.Q), (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.Q)
    (hcompat : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         ∀ (v : ↥hyp.V) (x : ↥hyp.Q),
           e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hVQ v x⟩ : ↥hyp.Q))
             = ((μ v : (GaloisField hyp.q hyp.p)ˣ) : GaloisField hyp.q hyp.p) *
                 e (Additive.ofMul x)) :
    Nonempty (TFieldModelData hyp) := by
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hcompatLift :=
    OddOrder.RepresentationTheory.SemilinearFieldModel.hcompatLift_of_equivariant
      e μ hμ_inj hμ_range hVQ hcompat
  obtain ⟨sigma, hinj, hker, hcomp⟩ :=
    OddOrder.RepresentationTheory.SemilinearFieldModel.fieldModelEmbedding
      e μ hμ_inj hμ_range hcompatLift hyp.Q_inf_V_eq_bot
  exact ⟨{ sigma := sigma
           sigma_injective := hinj
           sigma_Q_eq_Q := hker
           sigma_V_eq_V := hcomp }⟩

end OddOrder.Peterfalvi.S16
