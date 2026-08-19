/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularCosetSubgroup

/-!
# The `p'`-part map on an elementary subgroup is a homomorphism

Navarro (2.15) computes `θ̂(x) = θ(x_{p'})` on an elementary subgroup `E = P × Q`, where it becomes
`1_P × θ_Q`.  What makes that a character is that `x ↦ x_{p'}` is a *group homomorphism* on `E`,
onto the `p'`-part.

The point of this file is that no nilpotent-group Sylow decomposition is needed for the subgroups
`E = ⟨u⟩ P` that Brauer induction actually produces.  Two observations:

* **One exponent computes every `p'`-part.**  If `M ≡ 0 (mod |E|_p)` and `M ≡ 1 (mod |E|_{p'})`,
  then `z_{p'} = z ^ M` for *every* `z : E` — the `p`-part is killed by the first congruence and
  the `p'`-part is fixed by the second (`pRegularPart_eq_pow`).
* **`z ↦ z ^ M` is multiplicative on `⟨u⟩ P`.**  Writing `x = u ^ a v`, `y = u ^ b w` and using that
  `u` centralises `P`, everything reduces to `(v w) ^ M = v ^ M * w ^ M` for `v, w ∈ P`.  And `P`
  is a `q`-group, so either `q = p` (all three powers are `1`) or `q ≠ p` (all three powers are the
  identity).

## Main results

* `OddOrder.GroupTheory.pRegularPart_eq_pow` — a single exponent computes all `p'`-parts
* `OddOrder.GroupTheory.exists_pRegularPart_hom` — `x ↦ x_{p'}` is a homomorphism on `⟨u⟩ P`
* `OddOrder.GroupTheory.not_dvd_card_of_forall_isPRegular` — a subgroup of `p`-regular elements is
  a `p'`-group

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (2.15) (p. 28).
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] {p q : ℕ}

/-! ### One exponent for all `p'`-parts -/

section Exponent

variable [Finite G]

/-- A `p`-element has order dividing the `p`-part of `|G|`. -/
theorem orderOf_dvd_ordProj_of_isPElement (hp : p.Prime) {g : G} (hg : IsPElement p g) :
    orderOf g ∣ ordProj[p] (Nat.card G) := by
  obtain ⟨k, hk⟩ := hg
  rw [hk]
  exact pow_dvd_pow p
    ((Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp (hk ▸ orderOf_dvd_natCard g))

/-- **A single exponent computes every `p'`-part.**  Solve `M ≡ 0 (mod |G|_p)`,
`M ≡ 1 (mod |G|_{p'})` by the Chinese remainder theorem. -/
theorem exists_pRegular_exponent (hp : p.Prime) :
    ∃ M : ℕ, ordProj[p] (Nat.card G) ∣ M ∧ M ≡ 1 [MOD pRegularExponent p G] := by
  obtain ⟨M, hM0, hM1⟩ := Nat.chineseRemainder
    (coprime_ordProj_ordCompl (p := p) hp (Nat.card_pos (α := G)).ne') 0 1
  exact ⟨M, (Nat.modEq_zero_iff_dvd).mp hM0, hM1⟩

/-- **`z_{p'} = z ^ M`** for the exponent of `exists_pRegular_exponent`. -/
theorem pRegularPart_eq_pow (hp : p.Prime) {M : ℕ} (hM0 : ordProj[p] (Nat.card G) ∣ M)
    (hM1 : M ≡ 1 [MOD pRegularExponent p G]) (z : G) : pRegularPart p z = z ^ M := by
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  have hcomm := commute_pRegularPart_pPart (p := p) z
  have hp1 : pPart p z ^ M = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_ordProj_of_isPElement hp (isPElement_pPart hp z)).trans hM0)
  have hp2 : pRegularPart p z ^ M = pRegularPart p z := by
    have hdvd := orderOf_dvd_pRegularExponent hp (isPRegular_pRegularPart hp hfin)
    have := (pow_eq_pow_iff_modEq (x := pRegularPart p z) (n := M) (m := 1)).mpr
      (Nat.ModEq.of_dvd hdvd hM1)
    rwa [pow_one] at this
  conv_rhs => rw [← pRegularPart_mul_pPart hp hfin]
  rw [hcomm.mul_pow, hp1, hp2, mul_one]

end Exponent

/-! ### The projection on `⟨u⟩ P` -/

section Projection

variable [Finite G] {u : G} {P : Subgroup G}

omit [Finite G] in
/-- **The `p'`-part map is multiplicative on `⟨u⟩ P`.**  With `x = u ^ a v` and `y = u ^ b w` and
`u` central in `⟨u⟩ P`, everything comes down to `(v w) ^ M = v ^ M * w ^ M` on `P`, which the
hypothesis `hP` supplies. -/
theorem pow_mul_of_mem_pRegularProd (hcomm : ∀ v ∈ P, Commute u v) {M : ℕ}
    (hP : ∀ v ∈ P, ∀ w ∈ P, (v * w) ^ M = v ^ M * w ^ M) {x y : G}
    (hx : x ∈ pRegularProd u P hcomm) (hy : y ∈ pRegularProd u P hcomm) :
    (x * y) ^ M = x ^ M * y ^ M := by
  obtain ⟨a, v, hv, rfl⟩ := (mem_pRegularProd hcomm).mp hx
  obtain ⟨b, w, hw, rfl⟩ := (mem_pRegularProd hcomm).mp hy
  have hst : Commute (u ^ a) (u ^ b) := (Commute.refl u).zpow_zpow a b
  have hsv : Commute (u ^ a) v := (hcomm v hv).zpow_left a
  have hsw : Commute (u ^ a) w := (hcomm w hw).zpow_left a
  have htv : Commute (u ^ b) v := (hcomm v hv).zpow_left b
  have htw : Commute (u ^ b) w := (hcomm w hw).zpow_left b
  have hstvw : Commute (u ^ a * u ^ b) (v * w) := (hsv.mul_right hsw).mul_left (htv.mul_right htw)
  have hrearr : u ^ a * v * (u ^ b * w) = u ^ a * u ^ b * (v * w) := by
    calc u ^ a * v * (u ^ b * w) = u ^ a * (v * u ^ b) * w := by simp only [mul_assoc]
      _ = u ^ a * (u ^ b * v) * w := by rw [htv.eq]
      _ = u ^ a * u ^ b * (v * w) := by simp only [mul_assoc]
  have hc : Commute ((u ^ b) ^ M) (v ^ M) := (htv.pow_left M).pow_right M
  rw [hrearr, hstvw.mul_pow, hst.mul_pow, hsv.mul_pow, htw.mul_pow, hP v hv w hw]
  calc (u ^ a) ^ M * (u ^ b) ^ M * (v ^ M * w ^ M)
      = (u ^ a) ^ M * ((u ^ b) ^ M * v ^ M * w ^ M) := by simp only [mul_assoc]
    _ = (u ^ a) ^ M * (v ^ M * (u ^ b) ^ M * w ^ M) := by rw [hc.eq]
    _ = (u ^ a) ^ M * v ^ M * ((u ^ b) ^ M * w ^ M) := by simp only [mul_assoc]

/-- **The `p'`-part map on `⟨u⟩ P` as a group homomorphism into `G`.**  Here `P` is a `q`-group
for some prime `q`; whether or not `q = p`, the exponent `M` acts on `P` either as the constant `1`
or as the identity, and both are multiplicative. -/
theorem exists_pRegularPart_hom (hp : p.Prime) (hq : q.Prime) (hPq : IsPGroup q ↥P)
    (hcomm : ∀ v ∈ P, Commute u v) :
    ∃ f : ↥(pRegularProd u P hcomm) →* G,
      ∀ x : ↥(pRegularProd u P hcomm), f x = pRegularPart p (x : G) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨M, hM0, hM1⟩ := exists_pRegular_exponent (G := G) hp
  -- on `P` the exponent `M` is either annihilating (`q = p`) or the identity (`q ≠ p`)
  have hP : ∀ v ∈ P, ∀ w ∈ P, (v * w) ^ M = v ^ M * w ^ M := by
    have hpt : ∀ v ∈ P, v ^ M = pRegularPart p v := fun v hv =>
      (pRegularPart_eq_pow hp hM0 hM1 v).symm
    by_cases hqp : q = p
    · subst hqp
      have hone : ∀ v ∈ P, v ^ M = 1 := fun v hv => by
        have hfac := pRegularPart_mul_pPart hp (isOfFinOrder_of_finite v)
        rw [pPart_eq_self_of_isPElement hp (isPElement_of_mem_of_isPGroup hPq hv)] at hfac
        rw [hpt v hv]
        exact mul_right_cancel (b := v) (hfac.trans (one_mul v).symm)
      intro v hv w hw
      rw [hone _ (P.mul_mem hv hw), hone v hv, hone w hw, one_mul]
    · have hid : ∀ v ∈ P, v ^ M = v := by
        intro v hv
        obtain ⟨k, hk⟩ := isPElement_of_mem_of_isPGroup hPq hv
        have hreg : IsPRegular p v := by
          rw [IsPRegular, hk]
          exact fun hdvd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp
            (hp.dvd_of_dvd_pow hdvd)).symm
        rw [hpt v hv, pRegularPart_eq_self_of_isPRegular hp hreg]
      intro v hv w hw
      rw [hid _ (P.mul_mem hv hw), hid v hv, hid w hw]
  refine ⟨⟨⟨fun x => (x : G) ^ M, by simp⟩, ?_⟩, fun x => (pRegularPart_eq_pow hp hM0 hM1 _).symm⟩
  intro x y
  exact pow_mul_of_mem_pRegularProd hcomm hP x.2 y.2

end Projection

/-! ### A group of `p`-regular elements is a `p'`-group -/

/-- **Cauchy**: if every element of a finite group is `p`-regular, then `p` does not divide its
order. -/
theorem not_dvd_card_of_forall_isPRegular {H : Type*} [Group H] [Finite H] (hp : p.Prime)
    (h : ∀ x : H, IsPRegular p x) : ¬ p ∣ Nat.card H := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdvd
  exact h x (hx ▸ dvd_refl p)

end OddOrder.GroupTheory
