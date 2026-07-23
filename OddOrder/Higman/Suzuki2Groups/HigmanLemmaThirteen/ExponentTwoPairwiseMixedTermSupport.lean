/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoSupportCancellation
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.FactorPairRelationDefinition

/-!
# Higman Lemma 13: common support of two pairwise mixed terms

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exponent-two branch, two pairwise joins have the same left and right
factor parameters.  Outside the case where both parameters are the same
nontrivial automorphism, Higman's Lemma 12 gives a single right-variable
Frobenius monomial for both mixed terms.  Their two coefficients can therefore
be cancelled by one nonzero pair of scalars.

This is the coordinate-level support calculation.  A downstream leaf
identifies the two right coordinates with one actual ambient factor.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

noncomputable section

private theorem exists_common_right_monomial_profile
    {n : ℕ} (hn : 2 ≤ n)
    {theta phi : RingAut (GaloisField 2 n)}
    {lam mu nu : GaloisField 2 n}
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hsourceL : nu = lam * theta lam)
    (hsourceR : nu = mu * phi mu)
    (hunique : theta = 1 ∨ theta ≠ phi)
    (hrel : NormalizedFactorPairRelation n theta phi)
    (M₁ M₂ : GaloisField 2 n →ₗ[ZMod 2]
      (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (hequiv₁ : ∀ α β,
      M₁ (lam * α) (mu * β) = nu * M₁ α β)
    (hequiv₂ : ∀ α β,
      M₂ (lam * α) (mu * β) = nu * M₂ α β)
    (hM₁ : ∃ α β, M₁ α β ≠ 0)
    (hM₂ : ∃ α β, M₂ α β ≠ 0) :
    ∃ (j : ℕ) (c₁ c₂ : GaloisField 2 n),
      j < n ∧ c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
      (∀ β, M₁ 1 β = c₁ * β ^ 2 ^ j) ∧
      ∀ β, M₂ 1 β = c₂ * β ^ 2 ^ j := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hordnu : orderOf nu = 2 ^ n - 1 :=
    hnuPrimitive.eq_orderOf.symm
  have hNpos : 0 < 2 ^ n - 1 := by
    have hpow : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  have hnuNe : nu ≠ 0 := by
    intro hzero
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [hzero, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hpowcard : ∀ x : GaloisField 2 n, x ≠ 0 →
      x ^ (2 ^ n - 1) = 1 := by
    intro x hx
    have hfinite : Finite (GaloisField 2 n) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have fullOrderOf :
      ∀ {x : GaloisField 2 n} {k : ℕ}, k ≠ 0 →
        x ^ k = nu → orderOf x = 2 ^ n - 1 := by
    intro x k hk hx
    have hxne : x ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hk] at hx
      exact hnuNe hx.symm
    exact (orderOf_eq_and_coprime_of_pow_eq_orderOf
      hNpos hk hordnu hx (hpowcard x hxne)).1
  cases hrel with
  | typeB same =>
      have htheta : theta = 1 := by
        rcases hunique with htheta | hne
        · exact htheta
        · exact (hne same).elim
      have hphi : phi = 1 := same.symm.trans htheta
      have hlamSq : lam ^ 2 = nu := by
        calc
          lam ^ 2 = lam * lam := pow_two lam
          _ = lam * theta lam := by rw [htheta, RingAut.one_apply]
          _ = nu := hsourceL.symm
      have hmuSq : mu ^ 2 = nu := by
        calc
          mu ^ 2 = mu * mu := pow_two mu
          _ = mu * phi mu := by rw [hphi, RingAut.one_apply]
          _ = nu := hsourceR.symm
      have hlamMu : lam = mu := by
        apply CharTwo.sq_injective
        change lam ^ 2 = mu ^ 2
        rw [hlamSq, hmuSq]
      have hordlam : orderOf lam = 2 ^ n - 1 :=
        fullOrderOf (by norm_num) hlamSq
      have hlamSource : lam ^ (1 + 2 ^ 0) = nu := by
        simpa using hlamSq
      have hequiv₁' : ∀ α β,
          M₁ (lam * α) (lam * β) = nu * M₁ α β := by
        intro α β
        simpa only [hlamMu] using hequiv₁ α β
      have hequiv₂' : ∀ α β,
          M₂ (lam * α) (lam * β) = nu * M₂ α β := by
        intro α β
        simpa only [hlamMu] using hequiv₂ α β
      obtain ⟨c₁, hc₁, hform₁⟩ :=
        mixedTerm_monomial_of_theta_one hnpos M₁ lam nu
          hordlam hlamSource hequiv₁' hM₁
      obtain ⟨c₂, hc₂, hform₂⟩ :=
        mixedTerm_monomial_of_theta_one hnpos M₂ lam nu
          hordlam hlamSource hequiv₂' hM₂
      refine ⟨0, c₁, c₂, hnpos, hc₁, hc₂, ?_, ?_⟩
      · intro β
        simpa using hform₁ 1 β
      · intro β
        simpa using hform₂ 1 β
  | typeCLeft r hr htheta hphi hdim =>
      have h2r : 2 * r ≤ n := by omega
      have hlamNorm : lam ^ (1 + 2 ^ r) = nu := by
        have hthetaApply : theta lam = lam ^ 2 ^ r := by
          rw [htheta, frobeniusEquiv_pow_apply]
        calc
          lam ^ (1 + 2 ^ r) = lam * lam ^ 2 ^ r := by
            rw [pow_add, pow_one]
          _ = lam * theta lam := by rw [hthetaApply]
          _ = nu := hsourceL.symm
      have hmuSq : mu ^ 2 = nu := by
        calc
          mu ^ 2 = mu * mu := pow_two mu
          _ = mu * phi mu := by rw [hphi, RingAut.one_apply]
          _ = nu := hsourceR.symm
      have hmune : mu ≠ 0 := by
        intro hzero
        rw [hzero, zero_pow (by norm_num)] at hmuSq
        exact hnuNe hmuSq.symm
      have hordlam : orderOf lam = 2 ^ n - 1 :=
        fullOrderOf (by simp) hlamNorm
      obtain ⟨_, c₁, hc₁, hform₁⟩ :=
        mixedTerm_monomial_typeC hr h2r M₁ lam mu nu
          hordlam hlamNorm hmuSq (hpowcard mu hmune) hequiv₁ hM₁
      obtain ⟨_, c₂, hc₂, hform₂⟩ :=
        mixedTerm_monomial_typeC hr h2r M₂ lam mu nu
          hordlam hlamNorm hmuSq (hpowcard mu hmune) hequiv₂ hM₂
      refine ⟨r + 1, c₁, c₂, by omega, hc₁, hc₂, ?_, ?_⟩
      · intro β
        simpa using hform₁ 1 β
      · intro β
        simpa using hform₂ 1 β
  | typeCRight r hr htheta hphi hdim =>
      have h2r : 2 * r ≤ n := by omega
      have hlamSq : lam ^ 2 = nu := by
        calc
          lam ^ 2 = lam * lam := pow_two lam
          _ = lam * theta lam := by rw [htheta, RingAut.one_apply]
          _ = nu := hsourceL.symm
      have hmuNorm : mu ^ (1 + 2 ^ r) = nu := by
        have hphiApply : phi mu = mu ^ 2 ^ r := by
          rw [hphi, frobeniusEquiv_pow_apply]
        calc
          mu ^ (1 + 2 ^ r) = mu * mu ^ 2 ^ r := by
            rw [pow_add, pow_one]
          _ = mu * phi mu := by rw [hphiApply]
          _ = nu := hsourceR.symm
      have hlamne : lam ≠ 0 := by
        intro hzero
        rw [hzero, zero_pow (by norm_num)] at hlamSq
        exact hnuNe hlamSq.symm
      have hordmu : orderOf mu = 2 ^ n - 1 :=
        fullOrderOf (by simp) hmuNorm
      have hequiv₁' : ∀ α β,
          (LinearMap.flip M₁) (mu * α) (lam * β) =
            nu * (LinearMap.flip M₁) α β := by
        intro α β
        exact hequiv₁ β α
      have hequiv₂' : ∀ α β,
          (LinearMap.flip M₂) (mu * α) (lam * β) =
            nu * (LinearMap.flip M₂) α β := by
        intro α β
        exact hequiv₂ β α
      have hM₁' : ∃ α β, (LinearMap.flip M₁) α β ≠ 0 := by
        obtain ⟨α, β, hne⟩ := hM₁
        exact ⟨β, α, hne⟩
      have hM₂' : ∃ α β, (LinearMap.flip M₂) α β ≠ 0 := by
        obtain ⟨α, β, hne⟩ := hM₂
        exact ⟨β, α, hne⟩
      obtain ⟨_, c₁, hc₁, hform₁⟩ :=
        mixedTerm_monomial_typeC hr h2r (LinearMap.flip M₁)
          mu lam nu hordmu hmuNorm hlamSq (hpowcard lam hlamne)
          hequiv₁' hM₁'
      obtain ⟨_, c₂, hc₂, hform₂⟩ :=
        mixedTerm_monomial_typeC hr h2r (LinearMap.flip M₂)
          mu lam nu hordmu hmuNorm hlamSq (hpowcard lam hlamne)
          hequiv₂' hM₂'
      refine ⟨n - 1, c₁, c₂, Nat.sub_lt (by omega) (by omega),
        hc₁, hc₂, ?_, ?_⟩
      · intro β
        simpa using hform₁ β 1
      · intro β
        simpa using hform₂ β 1
  | typeDLeft r hr hrhalf htheta hphi hfive =>
      have hrn : r < n := by omega
      have hrz : (r : ZMod n) ≠ 0 := by
        rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
          Nat.mod_eq_of_lt hrn]
        omega
      have hsz : ((2 * r : ℕ) : ZMod n) ≠ 0 := by
        intro hs
        apply hrz
        push_cast at hs
        linear_combination hfive - 2 * hs
      have hrsz :
          (r : ZMod n) + ((2 * r : ℕ) : ZMod n) ≠ 0 := by
        intro hrs
        apply hrz
        push_cast at hrs
        linear_combination 2 * hrs - hfive
      have hrsne : (r : ZMod n) ≠ ((2 * r : ℕ) : ZMod n) := by
        intro hrs
        apply hrz
        push_cast at hrs
        linear_combination -hrs
      have hlamNorm : lam ^ (1 + 2 ^ r) = nu := by
        have hthetaApply : theta lam = lam ^ 2 ^ r := by
          rw [htheta, frobeniusEquiv_pow_apply]
        calc
          lam ^ (1 + 2 ^ r) = lam * lam ^ 2 ^ r := by
            rw [pow_add, pow_one]
          _ = lam * theta lam := by rw [hthetaApply]
          _ = nu := hsourceL.symm
      have hmuNorm : mu ^ (1 + 2 ^ (2 * r)) = nu := by
        have hphiApply : phi mu = mu ^ 2 ^ (2 * r) := by
          rw [hphi, htheta, ← pow_mul, Nat.mul_comm,
            frobeniusEquiv_pow_apply]
        calc
          mu ^ (1 + 2 ^ (2 * r)) =
              mu * mu ^ 2 ^ (2 * r) := by rw [pow_add, pow_one]
          _ = mu * phi mu := by rw [hphiApply]
          _ = nu := hsourceR.symm
      have profile
          (M : GaloisField 2 n →ₗ[ZMod 2]
            (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
          (hequiv : ∀ α β,
            M (lam * α) (mu * β) = nu * M α β)
          (hM : ∃ α β, M α β ≠ 0) :
          ∃ c : GaloisField 2 n, c ≠ 0 ∧
            ∀ β, M 1 β = c * β ^ 2 ^ (r % n) := by
        rcases mixedTerm_monomial_typeD hnpos hrz hsz hrsz hrsne
            M lam mu nu hordnu hlamNorm hmuNorm hequiv hM with
          hleft | hright
        · obtain ⟨_, _, c, hc, hform⟩ := hleft
          exact ⟨c, hc, fun β => by simpa using hform 1 β⟩
        · obtain ⟨hrfour, _, _⟩ := hright
          exfalso
          apply hrz
          push_cast at hrfour
          linear_combination -2 * hrfour - hfive
      obtain ⟨c₁, hc₁, hform₁⟩ := profile M₁ hequiv₁ hM₁
      obtain ⟨c₂, hc₂, hform₂⟩ := profile M₂ hequiv₂ hM₂
      exact ⟨r % n, c₁, c₂, Nat.mod_lt _ hnpos,
        hc₁, hc₂, hform₁, hform₂⟩
  | typeDRight r hr hrhalf hphi htheta hfive =>
      have hrn : r < n := by omega
      have hrz : (r : ZMod n) ≠ 0 := by
        rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
          Nat.mod_eq_of_lt hrn]
        omega
      have hsz : ((2 * r : ℕ) : ZMod n) ≠ 0 := by
        intro hs
        apply hrz
        push_cast at hs
        linear_combination hfive - 2 * hs
      have hrsz :
          (r : ZMod n) + ((2 * r : ℕ) : ZMod n) ≠ 0 := by
        intro hrs
        apply hrz
        push_cast at hrs
        linear_combination 2 * hrs - hfive
      have hrsne : (r : ZMod n) ≠ ((2 * r : ℕ) : ZMod n) := by
        intro hrs
        apply hrz
        push_cast at hrs
        linear_combination -hrs
      have hmuNorm : mu ^ (1 + 2 ^ r) = nu := by
        have hphiApply : phi mu = mu ^ 2 ^ r := by
          rw [hphi, frobeniusEquiv_pow_apply]
        calc
          mu ^ (1 + 2 ^ r) = mu * mu ^ 2 ^ r := by
            rw [pow_add, pow_one]
          _ = mu * phi mu := by rw [hphiApply]
          _ = nu := hsourceR.symm
      have hlamNorm : lam ^ (1 + 2 ^ (2 * r)) = nu := by
        have hthetaApply : theta lam = lam ^ 2 ^ (2 * r) := by
          rw [htheta, hphi, ← pow_mul, Nat.mul_comm,
            frobeniusEquiv_pow_apply]
        calc
          lam ^ (1 + 2 ^ (2 * r)) =
              lam * lam ^ 2 ^ (2 * r) := by rw [pow_add, pow_one]
          _ = lam * theta lam := by rw [hthetaApply]
          _ = nu := hsourceL.symm
      have profile
          (M : GaloisField 2 n →ₗ[ZMod 2]
            (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
          (hequiv : ∀ α β,
            M (lam * α) (mu * β) = nu * M α β)
          (hM : ∃ α β, M α β ≠ 0) :
          ∃ c : GaloisField 2 n, c ≠ 0 ∧
            ∀ β, M 1 β = c * β ^ 2 ^ (3 * r % n) := by
        have hequiv' : ∀ α β,
            (LinearMap.flip M) (mu * α) (lam * β) =
              nu * (LinearMap.flip M) α β := by
          intro α β
          exact hequiv β α
        have hM' : ∃ α β, (LinearMap.flip M) α β ≠ 0 := by
          obtain ⟨α, β, hne⟩ := hM
          exact ⟨β, α, hne⟩
        rcases mixedTerm_monomial_typeD hnpos hrz hsz hrsz hrsne
            (LinearMap.flip M) mu lam nu hordnu hmuNorm hlamNorm
            hequiv' hM' with hleft | hright
        · obtain ⟨_, _, c, hc, hform⟩ := hleft
          exact ⟨c, hc, fun β => by simpa using hform β 1⟩
        · obtain ⟨hrfour, _, _⟩ := hright
          exfalso
          apply hrz
          push_cast at hrfour
          linear_combination -2 * hrfour - hfive
      obtain ⟨c₁, hc₁, hform₁⟩ := profile M₁ hequiv₁ hM₁
      obtain ⟨c₂, hc₂, hform₂⟩ := profile M₂ hequiv₂ hM₂
      exact ⟨3 * r % n, c₁, c₂, Nat.mod_lt _ hnpos,
        hc₁, hc₂, hform₁, hform₂⟩

/-- **Higman Lemma 13 (p. 93), cancellation on one common right support.**

Suppose two nonzero mixed terms have the same normalized left/right
parameters and the same source eigenvalues.  Unless both parameters are the
same nontrivial automorphism, the Lemma 12 relation forces their restrictions
`β ↦ Mᵢ(1, β)` onto one common Frobenius monomial.  A nonzero pair of left
coefficients then cancels both maps on every right coordinate. -/
theorem exists_nontrivial_pair_cancel_common_right_mixedTerms
    {n : ℕ} (hn : 2 ≤ n)
    {theta phi : RingAut (GaloisField 2 n)}
    {lam mu nu : GaloisField 2 n}
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hsourceL : nu = lam * theta lam)
    (hsourceR : nu = mu * phi mu)
    (hunique : theta = 1 ∨ theta ≠ phi)
    (hrel : NormalizedFactorPairRelation n theta phi)
    (M₁ M₂ : GaloisField 2 n →ₗ[ZMod 2]
      (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (hequiv₁ : ∀ α β,
      M₁ (lam * α) (mu * β) = nu * M₁ α β)
    (hequiv₂ : ∀ α β,
      M₂ (lam * α) (mu * β) = nu * M₂ α β)
    (hM₁ : ∃ α β, M₁ α β ≠ 0)
    (hM₂ : ∃ α β, M₂ α β ≠ 0) :
    ∃ a b : GaloisField 2 n,
      (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ β, a * M₁ 1 β + b * M₂ 1 β = 0 := by
  obtain ⟨j, c₁, c₂, _, _, _, hform₁, hform₂⟩ :=
    exists_common_right_monomial_profile hn hnuPrimitive
      hsourceL hsourceR hunique hrel M₁ M₂
      hequiv₁ hequiv₂ hM₁ hM₂
  obtain ⟨a, b, hab, hcancel⟩ :=
    exists_nontrivial_pair_mul_add_mul_eq_zero c₁ c₂
  refine ⟨a, b, hab, fun β => ?_⟩
  rw [hform₁ β, hform₂ β]
  calc
    a * (c₁ * β ^ 2 ^ j) + b * (c₂ * β ^ 2 ^ j) =
        (a * c₁ + b * c₂) * β ^ 2 ^ j := by ring
    _ = 0 := by rw [hcancel, zero_mul]

end

end OddOrder.Higman.Suzuki2Groups
