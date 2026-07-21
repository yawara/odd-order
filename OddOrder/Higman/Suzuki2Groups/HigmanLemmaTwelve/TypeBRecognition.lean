/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoSummandSplit
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SummandIsomorphismBridge
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.SplitUniqueness

/-!
# Peterfalvi Appendix III, Theorem (e): isomorphic summands force type B

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Theorem (e), p. 141; G. Higman, *Suzuki 2-groups*,
pp. 90--92.

If some invariant two-summand split of `P ⧸ Z(P)` has `K`-equivariantly
isomorphic summands, then `P` is of type `B(n, θ, ε)`.  The proof re-runs
Higman's Lemma 12 dispatch on the two factor automorphisms `(θ, φ)`; in the
two type-B branches the classification engines conclude directly, while in
the type-C and type-D branches the isomorphic split is transported by the
split uniqueness (`OrderQModuleSplit.nonempty_summandEquiv_of_isomorphic`)
onto the canonical factor split, the summand-isomorphism bridge reads off
`μ = λ^{2^i}`, and the two-power congruences of the eigenvalue equation
`ν = λθ(λ) = μφ(μ)` collapse to `r ≡ 0` or `rL ≡ ±rR (mod n)` —
contradicting the case constraints.

This is the substantial half of the equivalence (e), the one consumed by
Part II, Ch. I §3, Lemma 5 (`W ≠ 1` forces type B).
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open Module
open scoped IsMulCommutative

noncomputable section

universe uP

variable {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}

/-- **Peterfalvi Appendix III, Theorem (e), recognition half, ξ-length-3
form.**  A ξ-length-3 Suzuki 2-group admitting an invariant two-summand split
of `P ⧸ Z(P)` with equivariantly isomorphic summands is of type `B`. -/
theorem isTypeB_of_isomorphicOrderQModuleSplit_of_xiLengthThree
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hfree : ∀ k : ↥Y, k ≠ 1 → ∀ q : P ⧸ Subgroup.center P,
      IsAInvariant.quotientMulAutHom
        (IsAInvariant.of_characteristic Y.subtype) k q = q → q = 1)
    (hcardK : Nat.card ↥Y = Nat.card ↥(Subgroup.center P) - 1)
    (isplit : IsomorphicOrderQModuleSplit Y.subtype (Subgroup.center P)
      (IsAInvariant.of_characteristic Y.subtype)) :
    IsTypeB.{uP, 0} P := by
  classical
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative ↑(frattini P) := IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  obtain ⟨factors, c, ePhi, nu, dataL0, dataR0, hn2, -, hnuPrim, hconj,
      hnuL0, hnuR0⟩ :=
    exists_complementaryFactorCoordinates_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  -- the canonical split of the same factors, and the split uniqueness
  have hZeq : Subgroup.center P = frattini P :=
    center_eq_frattini_of_xiLengthThree hP hncomm hmulti hxi hlen hprime
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hZnt : 1 < Nat.card ↥(Subgroup.center P) := by
    refine (Subgroup.one_lt_card_iff_ne_bot _).mpr ?_
    rw [hZeq]
    exact hPhiNeBot
  obtain ⟨esum⟩ :=
    (xiLengthThreeFactorSplit hP hncomm hmulti hxi hlen
      hprime factors).nonempty_summandEquiv_of_isomorphic
      isplit hfree hcardK hZnt
  revert hnuL0 hnuR0 hconj hnuPrim hn2 dataR0 dataL0 nu ePhi
  generalize Module.finrank (ZMod 2) (Additive ↑(frattini P)) = n
  intro ePhi nu dataL0 dataR0 hn2 hnuPrim hconj hnuL0 hnuR0
  have hK0 :=
    lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hK1 := lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hterm := lowerCentralTerm_one_eq_frattini_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hSq := lowerCentralSquaresLieInSecond_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hAgemo := agemo_one_eq_frattini_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  obtain ⟨-, hcentral⟩ :=
    commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant hP Y hxi.transitive
      (IsAInvariant.of_characteristic Y.subtype) hPhiNeBot
  have hinv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1 := by
    intro x hx
    rw [hterm]
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact hinvPhi ⟨hx, hx1⟩
  have hn0 : n ≠ 0 := by omega
  have n_pos : 0 < n := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hordnu : orderOf nu = 2 ^ n - 1 := hnuPrim.eq_orderOf.symm
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) n_pos
    omega
  have hνne : nu ≠ 0 := by
    intro h0
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [h0, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hpowcard : ∀ x : GaloisField 2 n, x ≠ 0 → x ^ (2 ^ n - 1) = 1 := by
    intro x hxne
    have hfin : Finite (GaloisField 2 n) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one x hxne
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  -- normalize each factor by the `A(n, θ) ≅ A(n, θ⁻¹)` flip
  have normalize : ∀ {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S}
      {hPhiS : frattini P ≤ S}
      (data : FactorCoordinateData hSinv hPhiS c ePhi nu),
      nu = data.lambda * data.theta data.lambda →
      ∃ data' : FactorCoordinateData hSinv hPhiS c ePhi nu,
        nu = data'.lambda * data'.theta data'.lambda ∧
        (data'.theta = 1 ∨
          ∃ r : ℕ, 0 < r ∧ 2 * r ≤ n ∧
            data'.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
            Odd (orderOf data'.theta)) := by
    intro S hSinv hPhiS data hnu
    cases data with
    | commutative d => exact ⟨.commutative d, hnu, Or.inl rfl⟩
    | noncommutative hnc d =>
        obtain ⟨d', r, hr0, hrhalf, hθ'⟩ := d.exists_flip_frobenius_le_half hn0
        exact ⟨.noncommutative hnc d', d'.kernel_eigenvalue_eq,
          Or.inr ⟨r, hr0, hrhalf, hθ', d'.theta_order_odd⟩⟩
  obtain ⟨dL, hnuL, hLcase⟩ := normalize dataL0 hnuL0
  obtain ⟨dR, hnuR, hRcase⟩ := normalize dataR0 hnuR0
  -- packaged inclusions and their shared inputs
  set L := dL.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0 with hLdef
  set R := dR.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0 with hRdef
  have hθLpkg : L.theta = dL.theta :=
    FactorCoordinateData.toInclusionData_theta hEA ePhi dL hK1 hterm hSq
      hAgemo hK0
  have hθRpkg : R.theta = dR.theta :=
    FactorCoordinateData.toInclusionData_theta hEA ePhi dR hK1 hterm hSq
      hAgemo hK0
  have hequivLR : ∀ α β : GaloisField 2 n,
      mixedTermBilinear L R (dL.lambda * α) (dR.lambda * β) =
        nu * mixedTermBilinear L R α β := fun α β =>
    mixedTermBilinear_lambda_equivariance hEA ePhi dL dR hK1 hterm hSq
      hAgemo hK0 hconj α β
  have hM0LR : ∃ α β : GaloisField 2 n, mixedTermBilinear L R α β ≠ 0 :=
    exists_mixedTermBilinear_ne_zero factors L R hxi hinvPhi
  -- the summand-isomorphism bridge: `μ = λ^{2^i}`
  have hbridge : ∃ i : Fin n, dR.lambda = dL.lambda ^ 2 ^ (i : ℕ) :=
    exists_frobenius_conjugate_of_summandEquiv hn0 L R
      (IsAInvariant.of_characteristic Y.subtype) hZeq c dL.lambda dR.lambda
      (fun γ => FactorCoordinateData.toInclusionData_incl_representation
        hEA ePhi dL hK1 hterm hSq hAgemo hK0 γ)
      (fun γ => FactorCoordinateData.toInclusionData_incl_representation
        hEA ePhi dR hK1 hterm hSq hAgemo hK0 γ)
      (xiLengthThreeFactorSplit hP hncomm hmulti hxi hlen
        hprime factors).leftInvariant
      (xiLengthThreeFactorSplit hP hncomm hmulti hxi hlen
        hprime factors).rightInvariant
      esum
  -- the dispatch on `(θ, φ)`
  rcases hLcase with hθL1 | ⟨rL, hrL0, hrLhalf, hθLfrob, hθLodd⟩
  · rcases hRcase with hθR1 | ⟨rR, hrR0, hrRhalf, hθRfrob, hθRodd⟩
    · -- `θ = φ = 1`: type B directly, as in `higmanLemmaTwelve`
      have hlam2 : dL.lambda ^ 2 = nu := by
        have h : dL.theta dL.lambda = dL.lambda := by
          rw [hθL1, RingAut.one_apply]
        calc dL.lambda ^ 2 = dL.lambda * dL.lambda := pow_two _
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      have hmu2 : dR.lambda ^ 2 = nu := by
        have h : dR.theta dR.lambda = dR.lambda := by
          rw [hθR1, RingAut.one_apply]
        calc dR.lambda ^ 2 = dR.lambda * dR.lambda := pow_two _
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      have heq : dR.lambda = dL.lambda :=
        CharTwo.sq_injective (hmu2.trans hlam2.symm)
      have hequiv' : ∀ α β : GaloisField 2 n,
          mixedTermBilinear L R (dL.lambda * α) (dL.lambda * β) =
            nu * mixedTermBilinear L R α β := by
        intro α β
        have h := hequivLR α β
        rwa [heq] at h
      exact isTypeB_of_mixedTerm_theta_one hEA hK1 hterm hSq hAgemo hK0 ePhi
        L R factors.right_normal factors.inf_eq_frattini factors.sup_eq_top
        factors.frattini_lt_right.le dL.lambda nu hordnu hlam2
        (hθLpkg.trans hθL1) (hθRpkg.trans hθR1) hequiv' hM0LR hinv hcentral
        n_pos hcard
    · -- `θ = 1`, `φ ≠ 1`: the type-C case is impossible with isomorphic
      -- summands: `ν = μ^{1+2^r} = λ^{2^i(1+2^r)}` and `ν = λ²` force a
      -- two-power carry, i.e. `r ≡ 0 (mod n)`.
      exfalso
      have hlam2 : dL.lambda ^ 2 = nu := by
        have h : dL.theta dL.lambda = dL.lambda := by
          rw [hθL1, RingAut.one_apply]
        calc dL.lambda ^ 2 = dL.lambda * dL.lambda := pow_two _
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      have hlamnuR : dR.lambda ^ (1 + 2 ^ rR) = nu := by
        have h : dR.theta dR.lambda = dR.lambda ^ 2 ^ rR := by
          rw [hθRfrob, frobeniusEquiv_pow_apply]
        calc dR.lambda ^ (1 + 2 ^ rR)
            = dR.lambda * dR.lambda ^ 2 ^ rR := by rw [pow_add, pow_one]
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      have hlamLne : dL.lambda ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num)] at hlam2
        exact hνne hlam2.symm
      obtain ⟨hordlam, -⟩ :=
        orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
          (by norm_num : (2 : ℕ) ≠ 0) hordnu hlam2
          (hpowcard _ hlamLne)
      obtain ⟨i, hi⟩ := hbridge
      have hrRn : rR < n := by omega
      have hrRz : (rR : ZMod n) ≠ 0 := by
        rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero, Nat.mod_eq_of_lt hrRn]
        omega
      have hpoweq : dL.lambda ^ (2 ^ (i : ℕ) + 2 ^ ((i : ℕ) + rR)) =
          dL.lambda ^ 2 ^ 1 := by
        have h1 : dL.lambda ^ (2 ^ (i : ℕ) + 2 ^ ((i : ℕ) + rR)) = nu := by
          have h2 : 2 ^ (i : ℕ) + 2 ^ ((i : ℕ) + rR) =
              2 ^ (i : ℕ) * (1 + 2 ^ rR) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
          rw [h2, pow_mul, ← hi, hlamnuR]
        have h3 : dL.lambda ^ 2 ^ 1 = nu := by
          rw [pow_one]
          exact hlam2
        rw [h1, h3]
      have hcong := higman_two_pow_add_congruence_of_pow_eq n_pos hordlam
        hpoweq
      obtain ⟨hab, -⟩ := higman_two_pow_add_eq_two_pow n_pos hcong
      apply hrRz
      push_cast at hab
      linear_combination -hab
  · rcases hRcase with hθR1 | ⟨rR, hrR0, hrRhalf, hθRfrob, hθRodd⟩
    · -- `θ ≠ 1`, `φ = 1`: mirror type-C case, impossible:
      -- `ν = λ^{1+2^r}` and `ν = μ² = λ^{2^{i+1}}` force `r ≡ 0 (mod n)`.
      exfalso
      have hmu2 : dR.lambda ^ 2 = nu := by
        have h : dR.theta dR.lambda = dR.lambda := by
          rw [hθR1, RingAut.one_apply]
        calc dR.lambda ^ 2 = dR.lambda * dR.lambda := pow_two _
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      have hlamnuL : dL.lambda ^ (1 + 2 ^ rL) = nu := by
        have h : dL.theta dL.lambda = dL.lambda ^ 2 ^ rL := by
          rw [hθLfrob, frobeniusEquiv_pow_apply]
        calc dL.lambda ^ (1 + 2 ^ rL)
            = dL.lambda * dL.lambda ^ 2 ^ rL := by rw [pow_add, pow_one]
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      have hlamLne : dL.lambda ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by simp)] at hlamnuL
        exact hνne hlamnuL.symm
      obtain ⟨hordlam, -⟩ :=
        orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
          (by simp : 1 + 2 ^ rL ≠ 0) hordnu hlamnuL
          (hpowcard _ hlamLne)
      obtain ⟨i, hi⟩ := hbridge
      have hrLn : rL < n := by omega
      have hrLz : (rL : ZMod n) ≠ 0 := by
        rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero, Nat.mod_eq_of_lt hrLn]
        omega
      have hpoweq : dL.lambda ^ (2 ^ 0 + 2 ^ rL) =
          dL.lambda ^ 2 ^ ((i : ℕ) + 1) := by
        have h1 : dL.lambda ^ (2 ^ 0 + 2 ^ rL) = nu := by
          rw [pow_zero]
          exact hlamnuL
        have h2 : dL.lambda ^ 2 ^ ((i : ℕ) + 1) = nu := by
          rw [pow_succ, pow_mul, ← hi]
          exact hmu2
        rw [h1, h2]
      have hcong := higman_two_pow_add_congruence_of_pow_eq n_pos hordlam
        hpoweq
      obtain ⟨hab, -⟩ := higman_two_pow_add_eq_two_pow n_pos hcong
      apply hrLz
      push_cast at hab
      linear_combination -hab
    · -- both `≠ 1`
      have hlamnuL : dL.lambda ^ (1 + 2 ^ rL) = nu := by
        have h : dL.theta dL.lambda = dL.lambda ^ 2 ^ rL := by
          rw [hθLfrob, frobeniusEquiv_pow_apply]
        calc dL.lambda ^ (1 + 2 ^ rL)
            = dL.lambda * dL.lambda ^ 2 ^ rL := by rw [pow_add, pow_one]
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      have hlamnuR : dR.lambda ^ (1 + 2 ^ rR) = nu := by
        have h : dR.theta dR.lambda = dR.lambda ^ 2 ^ rR := by
          rw [hθRfrob, frobeniusEquiv_pow_apply]
        calc dR.lambda ^ (1 + 2 ^ rR)
            = dR.lambda * dR.lambda ^ 2 ^ rR := by rw [pow_add, pow_one]
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      have hrLn : rL < n := by omega
      have hrRn : rR < n := by omega
      by_cases hrEq : rL = rR
      · -- `θ = φ ≠ 1`: type B directly, as in `higmanLemmaTwelve`
        subst hrEq
        have hlamLne : dL.lambda ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by simp)] at hlamnuL
          exact hνne hlamnuL.symm
        have hlamRne : dR.lambda ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by simp)] at hlamnuR
          exact hνne hlamnuR.symm
        have hmuEq : dR.lambda = dL.lambda :=
          eq_of_pow_eq_pow_orderOf hNpos (by simp) hordnu hlamnuL hlamnuR
            (hpowcard _ hlamLne) (hpowcard _ hlamRne)
        have hequiv' : ∀ α β : GaloisField 2 n,
            mixedTermBilinear L R (dL.lambda * α) (dL.lambda * β) =
              nu * mixedTermBilinear L R α β := by
          intro α β
          have h := hequivLR α β
          rwa [hmuEq] at h
        have hθeq : dR.theta = dL.theta := by
          rw [hθRfrob, hθLfrob]
        exact isTypeB_of_mixedTerm_theta_eq hEA hK1 hterm hSq hAgemo hK0
          ePhi L R factors.right_normal factors.inf_eq_frattini
          factors.sup_eq_top factors.frattini_lt_right.le dL.theta hθLfrob
          (by omega) hrLn hθLodd hθLpkg (hθRpkg.trans hθeq) dL.lambda nu
          hordnu hlamnuL hequiv' hM0LR hinv hcentral n_pos hcard
      · -- the independent (type-D) case is impossible with isomorphic
        -- summands: `λ^{1+2^rL} = ν = μ^{1+2^rR}` and `μ = λ^{2^i}` force
        -- `rR ≡ rL` or `rR + rL ≡ 0 (mod n)`.
        exfalso
        have hrLz : (rL : ZMod n) ≠ 0 := by
          rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
            Nat.mod_eq_of_lt hrLn]
          omega
        have hrRz : (rR : ZMod n) ≠ 0 := by
          rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
            Nat.mod_eq_of_lt hrRn]
          omega
        have hrszNe : (rL : ZMod n) ≠ (rR : ZMod n) := by
          intro h
          apply hrEq
          have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
          rwa [Nat.ModEq, Nat.mod_eq_of_lt hrLn, Nat.mod_eq_of_lt hrRn]
            at hmod
        have hsum : rL + rR < n := by omega
        have hrsz : (rL : ZMod n) + (rR : ZMod n) ≠ 0 := by
          rw [← Nat.cast_add, Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
            Nat.mod_eq_of_lt hsum]
          omega
        have hlamLne : dL.lambda ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by simp)] at hlamnuL
          exact hνne hlamnuL.symm
        obtain ⟨hordlam, -⟩ :=
          orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
            (by simp : 1 + 2 ^ rL ≠ 0) hordnu hlamnuL
            (hpowcard _ hlamLne)
        obtain ⟨i, hi⟩ := hbridge
        have hpoweq : dL.lambda ^ (2 ^ (i : ℕ) * (1 + 2 ^ rR)) =
            dL.lambda ^ (2 ^ 0 * (1 + 2 ^ rL)) := by
          have h1 : dL.lambda ^ (2 ^ (i : ℕ) * (1 + 2 ^ rR)) = nu := by
            rw [pow_mul, ← hi, hlamnuR]
          have h2 : dL.lambda ^ (2 ^ 0 * (1 + 2 ^ rL)) = nu := by
            rw [pow_zero, one_mul]
            exact hlamnuL
          rw [h1, h2]
        have hcong := higman_typeB_congruence_of_pow_eq n_pos hordlam hpoweq
        rcases higman_typeB_exponent_pm n_pos hrLz hrRz hcong with hpm | hpm
        · exact hrszNe hpm.symm
        · apply hrsz
          rw [add_comm]
          exact hpm

/-- **Peterfalvi Appendix III, Theorem (e), recognition half, `|P| = q³`
form.**  A Suzuki 2-group of order `q³` with a cyclic actor regular on the
involutions is of type `B` as soon as some invariant two-summand split of
`P ⧸ Z(P)` has equivariantly isomorphic summands.  This is the form consumed
by Part II, Ch. I §3, Lemma 5. -/
theorem isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube
    (hP : IsSuzuki2Group P)
    {K : Subgroup (MulAut P)} (hKcyc : IsCyclic ↥K)
    (hreg : ActsRegularlyOnInvolutions K)
    {m : ℕ} (hm : m ≠ 0)
    (hKcard : Nat.card ↥K = 2 ^ m - 1)
    (hcard : Nat.card P = (2 ^ m) ^ 3)
    (isplit : IsomorphicOrderQModuleSplit K.subtype (Subgroup.center P)
      (IsAInvariant.of_characteristic K.subtype)) :
    IsTypeB.{uP, 0} P := by
  obtain ⟨hP2, hncomm, hmulti, -⟩ := id hP
  have hxi : IsXiActor K := ⟨hKcyc, hreg.transitive⟩
  have hlen : HasXiLengthThree K.subtype :=
    hasXiLengthThree_of_card_eq_cube hP hKcyc hreg hm hKcard hcard
  obtain ⟨u₀, -, hu₀, -, -⟩ := id hmulti
  have hinvcard : (involutions P).ncard = Nat.card ↥K :=
    ncard_involutions_eq_card_of_regular hreg hu₀
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K →
      p ∣ (involutions P).ncard := by
    intro p _ hp
    rwa [hinvcard]
  -- `|Z(P)| = 2^m` via the split cardinalities
  have hZcard : Nat.card ↥(Subgroup.center P) = 2 ^ m := by
    have hcomm : ∀ x y : P ⧸ Subgroup.center P, x * y = y * x :=
      isplit.split.quotientEA.comm
    haveI : (isplit.split.left).Normal := normal_of_mul_comm hcomm _
    have hq : Nat.card (P ⧸ Subgroup.center P) =
        Nat.card ↥(Subgroup.center P) ^ 2 := by
      calc Nat.card (P ⧸ Subgroup.center P)
          = Nat.card ((P ⧸ Subgroup.center P) ⧸ isplit.split.left) *
            Nat.card ↥isplit.split.left :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup _
        _ = Nat.card ↥isplit.split.right * Nat.card ↥isplit.split.left := by
            rw [card_quotient_of_isCompl isplit.split.complementary]
        _ = Nat.card ↥(Subgroup.center P) ^ 2 := by
            rw [isplit.split.leftCard, isplit.split.rightCard, pow_two]
    have hP3 : Nat.card ↥(Subgroup.center P) ^ 3 = (2 ^ m) ^ 3 := by
      calc Nat.card ↥(Subgroup.center P) ^ 3
          = Nat.card (P ⧸ Subgroup.center P) *
            Nat.card ↥(Subgroup.center P) := by rw [hq]; ring
        _ = Nat.card P :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
        _ = (2 ^ m) ^ 3 := hcard
    exact Nat.pow_left_injective (by norm_num) hP3
  have hcardK : Nat.card ↥K = Nat.card ↥(Subgroup.center P) - 1 := by
    rw [hZcard, hKcard]
  -- fixed-point-freeness descends to the central quotient
  have hfreeP := fixedPointFree_of_actsRegularlyOnInvolutions hP2 hreg
  have hfree : ∀ k : ↥K, k ≠ 1 → ∀ q : P ⧸ Subgroup.center P,
      IsAInvariant.quotientMulAutHom
        (IsAInvariant.of_characteristic K.subtype) k q = q → q = 1 := by
    apply quotient_fixedPointFree_of_fixedPoints_le K.subtype
      (Subgroup.center P) (IsAInvariant.of_characteristic K.subtype)
    · exact card_coprime_of_card_eq_sub_one (Subgroup.center P) hcardK
    · intro k hk x hx
      rw [hfreeP k hk x hx]
      exact Subgroup.one_mem _
  exact isTypeB_of_isomorphicOrderQModuleSplit_of_xiLengthThree hP2 hncomm
    hmulti hxi hlen hprime hfree hcardK isplit

end

end OddOrder.Higman.Suzuki2Groups
