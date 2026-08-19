/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularElement

/-!
# The subgroup `⟨u⟩ P` for `P` centralising `u`

Gorenstein Lemma 7.6 is applied to `H = U P` with `U = ⟨u⟩` cyclic of `p'`-order and `P` a
`p`-subgroup centralising `u` (issue 9508, 段 F).  Because the two factors commute elementwise the
product set is already a subgroup, and because their orders are coprime the decomposition
`h = u ^ a v` is unique, giving `|H| = orderOf u · |P|`.

Both facts are what `PRegularCosetInduction` takes as the hypotheses `hgen` and `hcard`; here they
are supplied by construction.

## Main definitions

* `OddOrder.GroupTheory.pRegularProd` — the subgroup `⟨u⟩ P`

## Main results

* `OddOrder.GroupTheory.mem_pRegularProd` — every element is `u ^ a v`
* `OddOrder.GroupTheory.card_pRegularProd` — `|⟨u⟩ P| = orderOf u · |P|`

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] {p : ℕ} {u : G} {P : Subgroup G}

variable (u P) in
/-- **The subgroup `⟨u⟩ P`**, for `P` a subgroup centralised by `u`.  Integer exponents are used
so that no finiteness is needed; `mem_pRegularProd_nat` converts to natural ones. -/
def pRegularProd (hcomm : ∀ v ∈ P, Commute u v) : Subgroup G where
  carrier := {g : G | ∃ (a : ℤ) (v : G), v ∈ P ∧ g = u ^ a * v}
  one_mem' := ⟨0, 1, P.one_mem, by simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨a₁, v₁, hv₁, rfl⟩ ⟨a₂, v₂, hv₂, rfl⟩
    refine ⟨a₁ + a₂, v₁ * v₂, P.mul_mem hv₁ hv₂, ?_⟩
    have hc : Commute v₁ (u ^ a₂) := ((hcomm v₁ hv₁).symm).zpow_right a₂
    rw [zpow_add]
    calc u ^ a₁ * v₁ * (u ^ a₂ * v₂) = u ^ a₁ * (v₁ * u ^ a₂) * v₂ := by simp only [mul_assoc]
      _ = u ^ a₁ * (u ^ a₂ * v₁) * v₂ := by rw [hc.eq]
      _ = u ^ a₁ * u ^ a₂ * (v₁ * v₂) := by simp only [mul_assoc]
  inv_mem' := by
    rintro g ⟨a, v, hv, rfl⟩
    refine ⟨-a, v⁻¹, P.inv_mem hv, ?_⟩
    rw [mul_inv_rev, zpow_neg]
    exact ((((hcomm v hv).zpow_left a).inv_left).inv_right).symm.eq

@[simp]
theorem mem_pRegularProd (hcomm : ∀ v ∈ P, Commute u v) {g : G} :
    g ∈ pRegularProd u P hcomm ↔ ∃ (a : ℤ) (v : G), v ∈ P ∧ g = u ^ a * v := Iff.rfl

theorem self_mem_pRegularProd (hcomm : ∀ v ∈ P, Commute u v) : u ∈ pRegularProd u P hcomm :=
  ⟨1, 1, P.one_mem, by simp⟩

theorem le_pRegularProd (hcomm : ∀ v ∈ P, Commute u v) : P ≤ pRegularProd u P hcomm :=
  fun v hv => ⟨0, v, hv, by simp⟩

variable [Finite G]

/-- Over a finite group the exponents may be taken natural. -/
theorem mem_pRegularProd_nat (hcomm : ∀ v ∈ P, Commute u v) {g : G} :
    g ∈ pRegularProd u P hcomm ↔ ∃ (a : ℕ) (v : G), v ∈ P ∧ g = u ^ a * v := by
  refine ⟨?_, fun ⟨a, v, hv, hg⟩ => ⟨(a : ℤ), v, hv, by rwa [zpow_natCast]⟩⟩
  rintro ⟨a, v, hv, rfl⟩
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := u) (y := u ^ a)).mpr ⟨a, rfl⟩
  have hka : u ^ k = u ^ a := by simpa using hk
  exact ⟨k, v, hv, by rw [hka]⟩

/-- **`|⟨u⟩ P| = orderOf u · |P|`.**  The decomposition `h = u ^ a v` with `a < orderOf u` is
unique, because the `p'`-part of `h` is `u ^ a`. -/
theorem card_pRegularProd (hp : p.Prime) (hu : IsPRegular p u) (hPp : IsPGroup p ↥P)
    (hcomm : ∀ v ∈ P, Commute u v) :
    Nat.card ↥(pRegularProd u P hcomm) = orderOf u * Nat.card ↥P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hupos : 0 < orderOf u := orderOf_pos u
  -- the `p'`-part pins down the `u`-exponent
  have huniq : ∀ (a b : ℕ) (v w : G), v ∈ P → w ∈ P → u ^ a * v = u ^ b * w →
      u ^ a = u ^ b ∧ v = w := by
    intro a b v w hv hw h
    have hpa : pRegularPart p (u ^ a * v) = u ^ a := by
      refine ((eq_pPart_of_commute hp (((hcomm v hv).pow_left a).symm)
        (isPElement_of_mem_of_isPGroup hPp hv) (hu.pow a) rfl).2).symm
    have hpb : pRegularPart p (u ^ b * w) = u ^ b := by
      refine ((eq_pPart_of_commute hp (((hcomm w hw).pow_left b).symm)
        (isPElement_of_mem_of_isPGroup hPp hw) (hu.pow b) rfl).2).symm
    have hab : u ^ a = u ^ b := by rw [← hpa, ← hpb, h]
    refine ⟨hab, ?_⟩
    rw [hab] at h
    exact mul_left_cancel h
  -- the parametrisation
  refine (Nat.card_eq_of_bijective
    (fun q : Fin (orderOf u) × ↥P => (⟨u ^ (q.1 : ℕ) * (q.2 : G),
      (mem_pRegularProd_nat hcomm).mpr ⟨(q.1 : ℕ), (q.2 : G), q.2.2, rfl⟩⟩ :
        ↥(pRegularProd u P hcomm))) ?_).symm.trans ?_
  · constructor
    · rintro ⟨a, v⟩ ⟨b, w⟩ h
      obtain ⟨hab, hvw⟩ := huniq (a : ℕ) (b : ℕ) (v : G) (w : G) v.2 w.2 (Subtype.ext_iff.mp h)
      have : (a : ℕ) = (b : ℕ) := by
        rw [pow_eq_pow_iff_modEq] at hab
        exact (Nat.ModEq.eq_of_lt_of_lt hab a.2 b.2)
      exact Prod.ext (Fin.ext this) (Subtype.ext hvw)
    · rintro ⟨g, hg⟩
      obtain ⟨a, v, hv, rfl⟩ := (mem_pRegularProd_nat hcomm).mp hg
      refine ⟨(⟨a % orderOf u, Nat.mod_lt _ hupos⟩, ⟨v, hv⟩), ?_⟩
      refine Subtype.ext ?_
      simp only
      rw [pow_mod_orderOf]
  · rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

end OddOrder.GroupTheory
