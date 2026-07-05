import OddOrder.Peterfalvi.S15_SAndT
import OddOrder.GroupTheory.ConjClassSet

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
      (OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2)
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

/-- **Peterfalvi (14.11.3), S-side core**: an element avoiding the conjugates of `W#` and of
`P#` has order prime to `p`.

Contrapositive of the textbook chain (p. 90): if `p ∣ |g|`, the `p`-part of `g` is conjugate
into `P#` (`P ∈ Syl_p(G)`, BG σ-Hall), so wlog `g ∈ C_G(x) ≤ S` for some `x ∈ P#`
(`centralizer_le_S_of_mem_sharp_P`).  If `g ∉ S'` the coprime-coset partition (2.1) and the
regularity `S' ⊓ C_G(w) = W₂` (`w ∈ W₁#`, `TypePData.centralizer_W1`) conjugate `g` into
`W₂w ⊆ W#`; if `g ∈ S'` the case-(9.7.b) field structure ((14.6)/(13.12): `S' = P ⋊ U` is
Frobenius with kernel `P`) forces `g ∈ C_{S'}(x) ≤ P#`.  Either way `g` meets an excluded
orbit.  Coq: `PFsection14.coprime_typeP_Galois_core`.

Named §14 obligation: the `Syl_p` input and the Frobenius kernel step are the case-(9.7.b)
structure of `S` (issue 9000 typeP-Galois foundation); the coset step is Pf (2.1). -/
theorem orderOf_coprime_p_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {g : G}
    (hW : g ∉ conjClassSet (sharpSubgroup hyp.W))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P)) :
    Nat.Coprime (orderOf g) hyp.p := by
  sorry

/-- **Peterfalvi (14.11.3), T-side core**: an element avoiding the conjugates of `W#` and of
`Q#` has order prime to `q`.  Dual of `orderOf_coprime_p_of_not_mem_conj` (with
(14.4)/(13.12) in place of (14.6)/(13.12) for the `T' = Q ⋊ V` Frobenius step). -/
theorem orderOf_coprime_q_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) {g : G}
    (hW : g ∉ conjClassSet (sharpSubgroup hyp.W))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    Nat.Coprime (orderOf g) hyp.q := by
  sorry

/-- **Peterfalvi (14.11.3), support half**: an element avoiding the conjugates of the regular
set `W − (W₁ ∪ W₂)`, of `P#`, and of `Q#` — i.e. any element of the generic set `G₀` off the
Dade support — has order prime to `pq`.  Assembles the `W`-orbit bridge with the two one-prime
cores.  This is the group-theoretic half of (14.11.3); the character half ((3.9.a/c) `η`-grid
integrality/pairing on `G₀`) consumes it through `EtaGenericData`. -/
theorem orderOf_coprime_pq_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) {g : G}
    (hreg : g ∉ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    Nat.Coprime (orderOf g) (hyp.p * hyp.q) := by
  have hW := not_mem_conjClassSet_sharp_W hG hyp hreg hP hQ
  exact Nat.Coprime.mul_right (orderOf_coprime_p_of_not_mem_conj hG hyp hW hP)
    (orderOf_coprime_q_of_not_mem_conj hG hyp hTII hW hQ)

end OddOrder.Peterfalvi.S16
