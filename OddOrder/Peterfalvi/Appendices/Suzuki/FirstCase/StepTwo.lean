/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepOne
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerQuotient
import OddOrder.Peterfalvi.Appendices.NearFields

/-!
# Peterfalvi Part II, Ch. II, step (2): the rank-one centralizer quotient

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (2), p. 108.

By §3 Proposition 1(a), `L = C_G(P)` acts on the fixed points `Ω_P` with
kernel `N = C_{D_L}(Q_L)`, and the faithful quotient `L/N` satisfies (A1)
and (A2).  Under (B1) the quotient has 2-rank one — a four-subgroup of the
quotient would lift along the odd kernel to a four-subgroup of `C_G(P)` —
so Appendix C, Proposition 1 applies to `L/N`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction
open scoped Pointwise

/-- **Lifting a four-subgroup along an odd kernel**: if `A ⧸ N` contains an
elementary abelian subgroup of order `4` and `N` has odd order, so does
`A` — the Sylow `2`-subgroup of the preimage maps isomorphically. -/
theorem exists_four_subgroup_of_quotient {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (hNodd : Odd (Nat.card ↥N))
    (hbar : ∃ Ebar : Subgroup (A ⧸ N),
      Nat.card ↥Ebar = 4 ∧ ∀ x ∈ Ebar, x ^ 2 = 1) :
    ∃ E : Subgroup A, Nat.card ↥E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  classical
  obtain ⟨Ebar, hEcard, hEsq⟩ := hbar
  set E' : Subgroup A := Ebar.comap (QuotientGroup.mk' N) with hE'def
  -- `|E'| = 4 * |N|`
  have h1 : Nat.card ↥E' * E'.index = Nat.card A :=
    E'.card_mul_index
  have h2 : Nat.card ↥Ebar * Ebar.index = Nat.card (A ⧸ N) :=
    Ebar.card_mul_index
  have h3 : Nat.card A = Nat.card (A ⧸ N) * Nat.card ↥N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hidx : E'.index = Ebar.index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
  have hipos : E'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hE'card : Nat.card ↥E' = 4 * Nat.card ↥N := by
    have hmul : Nat.card ↥E' * E'.index =
        (4 * Nat.card ↥N) * E'.index := by
      rw [h1, h3, ← h2, hidx, hEcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hipos) hmul
  -- the Sylow `2`-subgroup of `E'` has order `4`
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥E') := inferInstance
  have hfact : (Nat.card ↥E').factorization 2 = 2 := by
    rw [hE'card, Nat.factorization_mul (by norm_num) Nat.card_pos.ne']
    have h4 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.factorization_pow_self Nat.prime_two
    have hodd : (Nat.card ↥N).factorization 2 = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro h2dvd
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2dvd)
    simp [h4, hodd]
  have hScard : Nat.card ↥(S : Subgroup ↥E') = 4 := by
    rw [S.card_eq_multiplicity, hfact]
    norm_num
  -- elements of `S` square into `S ∩ N = 1`
  have hSsq : ∀ y : ↥E', y ∈ (S : Subgroup ↥E') → y ^ 2 = 1 := by
    intro y hyS
    have hmemN : ((y : A)) ^ 2 ∈ N := by
      have hEb : QuotientGroup.mk' N (y : A) ∈ Ebar := y.2
      have hsq := hEsq _ hEb
      rw [← map_pow] at hsq
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact hsq
    have hyS2 : y ^ 2 ∈ (S : Subgroup ↥E') :=
      Subgroup.pow_mem _ hyS 2
    have hdvd4 : orderOf (y ^ 2) ∣ 4 := by
      have h : orderOf (y ^ 2) =
          orderOf (⟨y ^ 2, hyS2⟩ : ↥(S : Subgroup ↥E')) :=
        orderOf_injective ((S : Subgroup ↥E').subtype)
          (Subgroup.subtype_injective _) ⟨y ^ 2, hyS2⟩
      rw [h, ← hScard]
      exact orderOf_dvd_natCard _
    have hdvdN : orderOf (y ^ 2) ∣ Nat.card ↥N := by
      have hcoe : orderOf (((y : A)) ^ 2) = orderOf (y ^ 2) :=
        orderOf_injective E'.subtype
          (Subgroup.subtype_injective _) (y ^ 2)
      have h : orderOf (((y : A)) ^ 2) =
          orderOf (⟨((y : A)) ^ 2, hmemN⟩ : ↥N) :=
        orderOf_injective N.subtype
          (Subgroup.subtype_injective _) ⟨((y : A)) ^ 2, hmemN⟩
      rw [← hcoe, h]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 4 (Nat.card ↥N) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_left.mpr hNodd).pow_left 2
    have hone : orderOf (y ^ 2) = 1 :=
      Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd4 hdvdN)
    rwa [orderOf_eq_one_iff] at hone
  -- push forward to `A`
  refine ⟨(S : Subgroup ↥E').map E'.subtype, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.subtype_injective _)).toEquiv.symm]
    exact hScard
  · rintro x ⟨y, hyS, rfl⟩
    have hy2 := hSsq y hyS
    calc (E'.subtype y) ^ 2 = E'.subtype (y ^ 2) := (map_pow _ _ _).symm
      _ = 1 := by rw [hy2, map_one]

end OddOrder.Peterfalvi.Appendices.Suzuki
