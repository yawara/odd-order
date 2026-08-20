/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.InducedLambda
import OddOrder.Peterfalvi.Appendices.FeitSibleyCoherentImage

/-!
# Peterfalvi Part II, Ch. III, Theorem C: `Q` is a `2`-group

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, pp. 115–116.

> **Theorem C.** `Q` is a `2`-group.

The final assembly of the book's steps (1)–(13), all of whose ingredients are
supplied by the sibling leaves and by Appendix IV.  Assuming `Q₁ ≠ 1`, the
Feit–Sibley theorem makes `𝒮 = {χ ∈ Irr(H) | Q₁ ⊄ Ker χ}` coherent; the linear
character `λ` with `QK ⊆ Ker λ` induces to a sum `f₁ + f₂` of two irreducibles
of `G`, both orthogonal to every coherent member image, so the anchor
multiplicities `b₁, b₂ = ⟨Res f_j, χ₁⟩` obey

> `(b₁ + b₂)·|S|·d·(|Q₁| − 1) ≤ (|Q| + 1)·d`,

which forces `b₁ = 0` or `b₂ = 0` and hence `Q₁ ⊆ Ker f_j`.  That kernel is a
proper non-trivial normal subgroup, so `G` is not simple and Ch. I §3 gives
`Q₁ = 1` — the contradiction.

The book's own last paragraph, which rules out `f₁ = ±eᵢ` and thereby yields the
orthogonality used above, reads:

> Suppose that `f₁ = ±eᵢ` for some `i`.  By Lemma 2(c) of Appendix IV,
> `χ̄ᵢ ≠ χᵢ` and `χ̄ᵢ ∈ 𝒮`.  Therefore there is an element `e′ᵢ ∈ {eⱼ | j ≠ i}`
> such that `Ind_H^G(χᵢ − χ̄ᵢ) = eᵢ − e′ᵢ`. […] Then
> `(Ind_H^G λ, eᵢ − e′ᵢ) = (λ, χᵢ − χ̄ᵢ) = 0`, whence
> `Ind_H^G λ = ±(eᵢ + e′ᵢ)` and `|Q| + 1 = (Ind_H^G λ)(1) = ±2eᵢ(1)`, which is
> impossible since `|Q|` is even.

## Main results

* `Q1_eq_bot` — `Q₁ = 1`, the form the proof produces.
* `isPGroup_two_Q` — **Theorem C** as the book states it: `Q` is a `2`-group.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.RepresentationTheory

universe uG uΩ

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **`[G : H] = |Q| + 1`**: `H` is a point stabilizer of the doubly transitive
action on `Ω`, and `|Ω| = |Q| + 1`. -/
theorem index_H_eq :
    sc.toHypothesis.H.index = Nat.card ↥sc.toHypothesis.Q + 1 := by
  have := sc.toHypothesis.doubly_transitive
  have : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rw [sc.toHypothesis.H_def,
    MulAction.index_stabilizer_of_transitive G sc.toHypothesis.basept,
    sc.toHypothesis.card_Omega]

/-- **`[G : H]` is odd** (`= |Q| + 1` with `|Q|` even) — the parity that step
(10) plays against the even `±2eᵢ(1)`. -/
theorem odd_index_H : Odd sc.toHypothesis.H.index := by
  rw [sc.index_H_eq]
  obtain ⟨k, hk⟩ := sc.toHypothesis.Q_even
  exact ⟨k, by omega⟩

/-- **`(Ind_H^G θ)(1) = |Q| + 1` for a degree-one `θ`** — the book's
"`|Q| + 1 = (Ind_H^G λ)(1)`" (p. 116). -/
theorem induce_apply_one_eq [Fintype G]
    [Invertible (Nat.card ↥sc.toHypothesis.H : ℂ)]
    {θ : ClassFunction ↥sc.toHypothesis.H ℂ}
    (hdeg : (θ : ↥sc.toHypothesis.H → ℂ) 1 = 1) :
    ClassFunction.induce sc.toHypothesis.H θ (1 : G)
      = (Nat.card ↥sc.toHypothesis.Q : ℂ) + 1 := by
  rw [ClassFunction.induce_apply_one]
  rw [show θ (1 : ↥sc.toHypothesis.H) = 1 from hdeg, mul_one, sc.index_H_eq]
  push_cast
  ring

set_option backward.isDefEq.respectTransparency false in
/-- **`λ ∉ 𝒮`**: a class function with `QK` in its kernel kills
`Q₁ ≤ Q ≤ QK`, while members of `𝒮` do not. -/
theorem notMem_fs_Sset_of_leKer_QK
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ1 : sc.toHypothesis.Q1 ≠ ⊥)
    {θ : ClassFunction ↥sc.toHypothesis.H ℂ}
    (hker : ((sc.toHypothesis.QK.subgroupOf sc.toHypothesis.H :
      Subgroup ↥sc.toHypothesis.H) : Set ↥sc.toHypothesis.H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) :
    θ ∉ (sc.feitSibleyHypothesis ind hQ1).Sset := by
  rintro ⟨-, hnk⟩
  apply hnk
  intro x hx
  have hxQK : (x : G) ∈ sc.toHypothesis.QK :=
    sc.toHypothesis.Q_le_QK (sc.toHypothesis.Q1_le_Q hx)
  have hmem := hker (Subgroup.mem_subgroupOf.mpr hxQK)
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
  exact hmem

set_option maxHeartbeats 1600000 in
-- The `feitSibleyHypothesis` structure literal is repeatedly unfolded when moving
-- between the `sc`-side and `fs`-side statements of the imported lemmas.
/-- **Peterfalvi Part II, Ch. III, Theorem C** (pp. 115–116): under (C1),
`Q₁ = 1`, i.e. `Q` is a `2`-group.

The proof follows the book's steps (1)–(13), all previously landed: assuming
`Q₁ ≠ 1`, the Feit–Sibley Theorem makes `𝒮` coherent (step (3)); the linear
character `λ` with `QK ⊆ Ker λ` (step (4)) induces to `f₁ + f₂` (steps
(5)–(8)); the constituents are orthogonal to all member images (steps
(9)–(10)); the anchor multiplicities `b₁, b₂` then satisfy
`(b₁+b₂)·|S|·d·(|Q₁|−1) ≤ (|Q|+1)·d` (steps (11)–(12)), forcing some
`b_j = 0`, so `Q₁ ⊆ Ker f_j`; the kernel is a proper nontrivial normal
subgroup, so `G` is not simple, and Ch. I §3 gives `Q₁ = 1` — contradiction. -/
theorem Q1_eq_bot (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    sc.toHypothesis.Q1 = ⊥ := by
  classical
  by_contra hQ1
  -- instances, in both the `sc`-side and `fs`-side syntactic shapes
  let instG : Fintype G := Fintype.ofFinite G
  let instGi : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let instH : Fintype ↥sc.toHypothesis.H := Fintype.ofFinite _
  let : Fintype ↥(sc.feitSibleyHypothesis ind hQ1).H := instH
  let instHi : Invertible (Nat.card ↥sc.toHypothesis.H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(sc.feitSibleyHypothesis ind hQ1).H : ℂ) := instHi
  let instQi : Invertible
      (Nat.card ↥(sc.toHypothesis.Q.subgroupOf sc.toHypothesis.H) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((sc.feitSibleyHypothesis ind hQ1).Q.subgroupOf
      (sc.feitSibleyHypothesis ind hQ1).H) : ℂ) := instQi
  -- step (3): coherence
  obtain ⟨hcoh⟩ := sc.sset_isCoherent ind hQ1
  -- step (4): the linear character λ
  obtain ⟨θb, hθbne, hker, hdeg⟩ :=
    sc.toHypothesis.exists_linearCharacter_leKer_QK sc.V_ne_bot
  have hθ : IsIrreducibleCharacter (θb : ClassFunction ↥sc.toHypothesis.H ℂ) :=
    θb.isIrreducible
  have hne : (θb : ClassFunction ↥sc.toHypothesis.H ℂ)
      ≠ trivialClassFunction ↥sc.toHypothesis.H := by
    intro h
    exact hθbne (IrreducibleCharacter.ext (by
      rw [h, IrreducibleCharacter.coe_trivialIrreducibleCharacter]))
  -- steps (7)–(8): `Ind λ = f₁ + f₂`
  obtain ⟨f₁, f₂, hf₁, hf₂, hf12, hf₁t, hf₂t, hsum⟩ :=
    sc.exists_induce_eq_add_irreducible ind hQ1 hθ hdeg hker hne
  -- the fs-side hypotheses of the imported lemmas
  have hdodd : Odd (sc.feitSibleyHypothesis ind hQ1).d := sc.toHypothesis.D_odd
  have hQ1odd : Odd (Nat.card ↥(sc.feitSibleyHypothesis ind hQ1).Q1) :=
    sc.toHypothesis.odd_card_Q1
  have hidx : Odd (sc.feitSibleyHypothesis ind hQ1).H.index := sc.odd_index_H
  have hθS : (θb : ClassFunction ↥sc.toHypothesis.H ℂ)
      ∉ (sc.feitSibleyHypothesis ind hQ1).Sset :=
    sc.notMem_fs_Sset_of_leKer_QK ind hQ1 hker
  have hnil : Group.IsNilpotent ↥(sc.feitSibleyHypothesis ind hQ1).Q1 :=
    sc.toHypothesis.isNilpotent_Q1
  -- step (10): both constituents are orthogonal to all member images
  have hforth₁ : ∀ ψ ∈ (sc.feitSibleyHypothesis ind hQ1).Sset,
      ClassFunction.inner f₁ (hcoh.extension ψ) = 0 := fun ψ hψ =>
    (sc.feitSibleyHypothesis ind hQ1).inner_constituent_extension_eq_zero hcoh
      hdodd hQ1odd hidx hθ hdeg hθS hf₁ hf₂ hf12 hsum hψ
  have hsum' : ClassFunction.induce sc.toHypothesis.H
      (θb : ClassFunction ↥sc.toHypothesis.H ℂ) = f₂ + f₁ := by
    rw [hsum, add_comm]
  have hforth₂ : ∀ ψ ∈ (sc.feitSibleyHypothesis ind hQ1).Sset,
      ClassFunction.inner f₂ (hcoh.extension ψ) = 0 := fun ψ hψ =>
    (sc.feitSibleyHypothesis ind hQ1).inner_constituent_extension_eq_zero hcoh
      hdodd hQ1odd hidx hθ hdeg hθS hf₂ hf₁ hf12.symm hsum' hψ
  -- step (9): the anchor
  obtain ⟨χ₁, hχ₁S, hχ₁d, haOf⟩ :=
    (sc.feitSibleyHypothesis ind hQ1).exists_anchor hnil
  -- step (11): the anchor multiplicities
  have hres₁ : IsCharacter (ClassFunction.restrict
      (sc.feitSibleyHypothesis ind hQ1).H f₁) :=
    OddOrder.Peterfalvi.Appendices.FeitSibley.isCharacter_restrict _ hf₁.isCharacter
  have hres₂ : IsCharacter (ClassFunction.restrict
      (sc.feitSibleyHypothesis ind hQ1).H f₂) :=
    OddOrder.Peterfalvi.Appendices.FeitSibley.isCharacter_restrict _ hf₂.isCharacter
  obtain ⟨b₁, hb₁⟩ := hres₁.exists_natCast_inner_irreducible hχ₁S.1
  obtain ⟨b₂, hb₂⟩ := hres₂.exists_natCast_inner_irreducible hχ₁S.1
  -- the constituent degrees
  obtain ⟨n₁, hn₁pos, hn₁⟩ := hf₁.exists_apply_one_eq_pos_natCast
  obtain ⟨n₂, hn₂pos, hn₂⟩ := hf₂.exists_apply_one_eq_pos_natCast
  -- step (12): the degree estimates
  have hest₁ := (sc.feitSibleyHypothesis ind hQ1).mul_card_sub_le_of_inner_restrict
    hcoh hf₁ hforth₁ hn₁ hχ₁S hχ₁d hb₁
  have hest₂ := (sc.feitSibleyHypothesis ind hQ1).mul_card_sub_le_of_inner_restrict
    hcoh hf₂ hforth₂ hn₂ hχ₁S hχ₁d hb₂
  -- `n₁ + n₂ = |Q| + 1`
  have hval := sc.induce_apply_one_eq (θ := (θb : ClassFunction _ ℂ)) hdeg
  rw [hsum, ClassFunction.add_apply, hn₁, hn₂] at hval
  have hdeg_sum : n₁ + n₂ = Nat.card ↥sc.toHypothesis.Q + 1 := by
    exact_mod_cast hval
  -- the quotient-card arithmetic: `|H| − |H/Q₁| = |S|·d·(|Q₁|−1)`
  have hQ1leH : sc.toHypothesis.Q1 ≤ sc.toHypothesis.H :=
    sc.toHypothesis.Q1_le_Q.trans sc.toHypothesis.Q_le_H
  have hquot_mul : Nat.card (↥sc.toHypothesis.H ⧸
        sc.toHypothesis.Q1.subgroupOf sc.toHypothesis.H)
      * Nat.card ↥sc.toHypothesis.Q1 = Nat.card ↥sc.toHypothesis.H := by
    have h := (sc.toHypothesis.Q1.subgroupOf sc.toHypothesis.H).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1leH).toEquiv,
      Subgroup.index_eq_card] at h
    rw [mul_comm]
    exact h
  have hH_card : Nat.card ↥sc.toHypothesis.H
      = Nat.card ↥sc.toHypothesis.sylowTwoOfQ * Nat.card ↥sc.toHypothesis.Q1
        * Nat.card ↥sc.toHypothesis.D := by
    rw [sc.toHypothesis.card_H_eq, ← sc.toHypothesis.card_sylowTwoOfQ_mul_card_Q1]
  have hquot : Nat.card (↥sc.toHypothesis.H ⧸
        sc.toHypothesis.Q1.subgroupOf sc.toHypothesis.H)
      = Nat.card ↥sc.toHypothesis.sylowTwoOfQ * Nat.card ↥sc.toHypothesis.D := by
    have hpos : 0 < Nat.card ↥sc.toHypothesis.Q1 := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hquot_mul, hH_card]
    ring
  -- numerical shorthands
  set S := Nat.card ↥sc.toHypothesis.sylowTwoOfQ with hSdef
  set q1 := Nat.card ↥sc.toHypothesis.Q1 with hq1def
  set dd := Nat.card ↥sc.toHypothesis.D with hdddef
  -- the estimates in `sc`-side numerals
  have hK : Nat.card ↥sc.toHypothesis.H - Nat.card (↥sc.toHypothesis.H ⧸
        sc.toHypothesis.Q1.subgroupOf sc.toHypothesis.H)
      = S * dd * (q1 - 1) := by
    rw [hH_card, hquot, Nat.mul_sub]
    ring_nf
  have hest₁' : b₁ * (S * dd * (q1 - 1)) ≤ n₁ * dd := by rw [← hK]; exact hest₁
  have hest₂' : b₂ * (S * dd * (q1 - 1)) ≤ n₂ * dd := by rw [← hK]; exact hest₂
  -- `|Q| = S·q1`, `S ≥ 2`, `q1 ≥ 3`, `dd ≥ 1`
  have hQcard : Nat.card ↥sc.toHypothesis.Q = S * q1 :=
    (sc.toHypothesis.card_sylowTwoOfQ_mul_card_Q1).symm
  have hS2 : 2 ≤ S := by
    have h2 : 2 ∣ S * q1 := by
      rw [← hQcard]
      exact sc.toHypothesis.Q_even.two_dvd
    have hodd : ¬ 2 ∣ q1 := by
      have h := Nat.odd_iff.mp sc.toHypothesis.odd_card_Q1
      omega
    have hdS : 2 ∣ S := (Nat.prime_two.dvd_mul.mp h2).resolve_right hodd
    obtain ⟨k, hk⟩ := hdS
    have hSpos : 0 < S := Nat.card_pos
    omega
  have hq13 : 3 ≤ q1 := by
    have hodd := Nat.odd_iff.mp sc.toHypothesis.odd_card_Q1
    have hne1 : q1 ≠ 1 := by
      intro h1
      exact hQ1 (Subgroup.eq_bot_of_card_eq _ h1)
    have hpos : 0 < q1 := Nat.card_pos
    omega
  have hdd1 : 1 ≤ dd := Nat.card_pos
  -- some `b_j` vanishes
  have hble : b₁ + b₂ ≤ 1 := by
    by_contra hb2
    push Not at hb2
    obtain ⟨k, hk⟩ : ∃ k, q1 = k + 3 := ⟨q1 - 3, by omega⟩
    have hcomb : (b₁ + b₂) * (S * dd * (q1 - 1)) ≤ (S * q1 + 1) * dd := by
      calc (b₁ + b₂) * (S * dd * (q1 - 1))
          = b₁ * (S * dd * (q1 - 1)) + b₂ * (S * dd * (q1 - 1)) := by ring
        _ ≤ n₁ * dd + n₂ * dd := Nat.add_le_add hest₁' hest₂'
        _ = (n₁ + n₂) * dd := by ring
        _ = (S * q1 + 1) * dd := by rw [hdeg_sum, hQcard]
    have h2le : 2 * (S * dd * (q1 - 1)) ≤ (S * q1 + 1) * dd :=
      le_trans (Nat.mul_le_mul_right _ hb2) hcomb
    rw [hk] at h2le
    have hsub : k + 3 - 1 = k + 2 := by omega
    rw [hsub] at h2le
    nlinarith [hS2, hdd1, Nat.zero_le k]
  -- extract the kernel constituent
  have hmain : ∃ f : ClassFunction G ℂ, IsIrreducibleCharacter f ∧
      f ≠ trivialClassFunction G ∧
      ∀ x ∈ sc.toHypothesis.Q1,
        x ∈ OddOrder.Peterfalvi.S03.characterKernel f := by
    have hzero : ∀ (f : ClassFunction G ℂ),
        (∀ ψ ∈ (sc.feitSibleyHypothesis ind hQ1).Sset,
          ClassFunction.inner f (hcoh.extension ψ) = 0) →
        ClassFunction.inner (ClassFunction.restrict
          (sc.feitSibleyHypothesis ind hQ1).H f) χ₁ = 0 →
        ∀ χ ∈ (sc.feitSibleyHypothesis ind hQ1).Sset,
          ClassFunction.inner (ClassFunction.restrict
            (sc.feitSibleyHypothesis ind hQ1).H f) χ = 0 := by
      intro f hforth hb0 χ hχ
      obtain ⟨aχ, -, haχ⟩ := haOf χ hχ
      rw [(sc.feitSibleyHypothesis ind hQ1).inner_restrict_eq_mul hcoh hforth
        hχ₁S hχ haχ, hb0, mul_zero]
    rcases (show b₁ = 0 ∨ b₂ = 0 by omega) with hb0 | hb0
    · refine ⟨f₁, hf₁, hf₁t, fun x hx =>
        (sc.feitSibleyHypothesis ind hQ1).mem_characterKernel_of_forall_inner_restrict_eq_zero
          hf₁.isCharacter (hzero f₁ hforth₁ (by rw [hb₁, hb0]; norm_num)) hx⟩
    · refine ⟨f₂, hf₂, hf₂t, fun x hx =>
        (sc.feitSibleyHypothesis ind hQ1).mem_characterKernel_of_forall_inner_restrict_eq_zero
          hf₂.isCharacter (hzero f₂ hforth₂ (by rw [hb₂, hb0]; norm_num)) hx⟩
  obtain ⟨f, hf, hft, hfker⟩ := hmain
  -- step (13): the kernel is a proper nontrivial normal subgroup
  have hN_normal : (OddOrder.Peterfalvi.S03.characterKernelSubgroup
      hf.isCharacter).Normal := by
    constructor
    intro x hx g
    rw [OddOrder.Peterfalvi.S03.mem_characterKernelSubgroup,
      OddOrder.Peterfalvi.S03.mem_characterKernel] at hx ⊢
    rw [← hx]
    exact f.conj_eq x g
  have hN_ne_bot : OddOrder.Peterfalvi.S03.characterKernelSubgroup
      hf.isCharacter ≠ ⊥ := by
    intro h
    refine hQ1 (le_bot_iff.mp fun x hx => ?_)
    rw [← h]
    exact hfker x hx
  have hN_ne_top : OddOrder.Peterfalvi.S03.characterKernelSubgroup
      hf.isCharacter ≠ ⊤ := by
    intro h
    apply hft
    obtain ⟨n, hnpos, hn⟩ := hf.exists_apply_one_eq_pos_natCast
    have hconst : ∀ g : G, f g = (n : ℂ) := by
      intro g
      have hg : g ∈ OddOrder.Peterfalvi.S03.characterKernelSubgroup
          hf.isCharacter := h ▸ Subgroup.mem_top g
      rw [OddOrder.Peterfalvi.S03.mem_characterKernelSubgroup,
        OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hg
      rw [hg]
      exact hn
    have hnorm := hf.inner_self_eq_one
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum] at hnorm
    have hsum_const : (∑ g : G, f g * star (f g))
        = (Nat.card G : ℂ) * ((n : ℂ) * (n : ℂ)) := by
      rw [Finset.sum_congr rfl fun g _ => by rw [hconst g, star_natCast]]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    rw [hsum_const, ← mul_assoc, invOf_mul_self, one_mul] at hnorm
    have hn1 : n = 1 := by
      have h : (n * n : ℕ) = 1 := by exact_mod_cast hnorm
      nlinarith [hnpos]
    ext g
    rw [hconst g, hn1, trivialClassFunction_apply]
    norm_num
  -- `G` is not simple, so `Q₁ = 1` — contradiction
  have hG : ¬ IsSimpleGroup G := by
    intro hs
    rcases hs.eq_bot_or_eq_top_of_normal _ hN_normal with h | h
    · exact hN_ne_bot h
    · exact hN_ne_top h
  exact hQ1 (sc.Q1_eq_bot_of_not_isSimpleGroup ind hG)

/-- **Peterfalvi Part II, Ch. III, Theorem C** (pp. 115–116), as the book states
it: under (C1), `Q` is a `2`-group.

`Q₁` is the odd normal `2`-complement of the nilpotent `Q` (Ch. I §2), so
`Q₁ = 1` (`Q1_eq_bot`) leaves `Q` equal to its Sylow `2`-subgroup. -/
theorem isPGroup_two_Q (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    IsPGroup 2 ↥sc.toHypothesis.Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := sc.toHypothesis.isPGroup_sylowTwoOfQ.exists_card_eq
  refine IsPGroup.of_card (n := n) ?_
  rw [← sc.toHypothesis.card_sylowTwoOfQ_mul_card_Q1, sc.Q1_eq_bot ind,
    Subgroup.card_bot, mul_one, hn]

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
