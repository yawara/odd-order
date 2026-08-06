/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow

/-!
# A Sylow `2`-subgroup with a unique involution

Gorenstein Ch. 12, Lemma 1.7 and Navarro p. 143 both need the same input: **the product of two
involutions has odd order**.  The only property of the Sylow `2`-subgroup that enters is that it
has a *unique* involution — true for every generalized quaternion group, `Q₈` included.

`BrauerSuzukiInvolutions` proves this inside `QuaternionSylowSetup`, whose `hn : 3 ≤ n` restricts
it to `|S| ≥ 16`; Navarro's `Q₈` case needs `|S| = 8`.  This file carries the argument with the
uniqueness as a bare hypothesis, so both cases are instances.

## Main results

* `OddOrder.GroupTheory.exists_conj_subgroupLe_sylow` — a `2`-subgroup conjugates into `T`
* `OddOrder.GroupTheory.commute_involution_eq_of_unique_involution` — commuting involutions of `G`
  are equal
* `OddOrder.GroupTheory.odd_orderOf_mul_of_involution_of_unique_involution` — the product of two
  involutions has odd order
-/

open scoped Pointwise

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **A `2`-subgroup can be conjugated into a fixed Sylow `2`-subgroup.**  A `2`-group `K` lies in
some Sylow `2`-subgroup `P`, and all of them are conjugate. -/
theorem exists_conj_subgroupLe_sylow (T : Sylow 2 G) {K : Subgroup G} (hK : IsPGroup 2 K) :
    ∃ c : G, ∀ w ∈ K, c * w * c⁻¹ ∈ (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hKP⟩ := hK.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P T
  refine ⟨c, fun w hw => ?_⟩
  have hwP : w ∈ (P : Subgroup G) := hKP hw
  have hmem : MulAut.conj c • w ∈ MulAut.conj c • (P : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul w (MulAut.conj c) _ hwP
  rw [← Sylow.coe_subgroup_smul, hc] at hmem
  simpa only [MulAut.smul_def, MulAut.conj_apply] using hmem

variable (T : Sylow 2 G) {z : G}
  (hz : ∀ s ∈ (T : Subgroup G), s ^ 2 = 1 → s = 1 ∨ s = z)

include hz in
/-- **Any two commuting involutions of `G` are equal**, when the Sylow `2`-subgroup has a unique
involution.  The subgroup they generate is elementary abelian, hence a `2`-group, hence conjugate
into `T`; there both images are the unique involution `z`. -/
theorem commute_involution_eq_of_unique_involution {u v : G} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : Commute u v) : u = v := by
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have hv2 : v ^ 2 = 1 := by rw [← hv, pow_orderOf_eq_one]
  have hune : u ≠ 1 := by rintro rfl; simp [orderOf_one] at hu
  have hvne : v ≠ 1 := by rintro rfl; simp [orderOf_one] at hv
  set K := Subgroup.closure ({u, v} : Set G) with hKdef
  have huK : u ∈ K := Subgroup.subset_closure (by left; rfl)
  have hvK : v ∈ K := Subgroup.subset_closure (by right; rfl)
  have hcomm_gen : ∀ a ∈ ({u, v} : Set G), ∀ b ∈ ({u, v} : Set G), Commute a b := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact huv
    · exact huv.symm
    · exact Commute.refl _
  have habelian : ∀ a ∈ K, ∀ b ∈ K, Commute a b := by
    intro a ha b hb
    refine Subgroup.closure_induction₂ (fun x y hx hy => hcomm_gen x hx y hy)
      (fun x _ => Commute.one_left x) (fun x _ => Commute.one_right x)
      (fun x y w _ _ _ h1 h2 => h1.mul_left h2)
      (fun y w x _ _ _ h1 h2 => h1.mul_right h2)
      (fun x y _ _ h => h.inv_left) (fun x y _ _ h => h.inv_right) ha hb
  have hsq : ∀ g ∈ K, g ^ 2 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hu2
        · exact hv2
    | one => exact one_pow 2
    | mul a b ha hb h1 h2 => rw [(habelian a ha b hb).mul_pow, h1, h2, one_mul]
    | inv a ha h => rw [inv_pow, h, inv_one]
  have hpgroup : IsPGroup 2 K := by
    intro g
    refine ⟨1, ?_⟩
    have h := hsq (g : G) g.2
    apply Subtype.ext
    push_cast
    simpa using h
  obtain ⟨c, hconjS⟩ := exists_conj_subgroupLe_sylow T hpgroup
  have hconj_sq : ∀ {w : G}, w ^ 2 = 1 → (c * w * c⁻¹) ^ 2 = 1 := fun {w} hw => by
    rw [show c * w * c⁻¹ = MulAut.conj c w from rfl, ← map_pow, hw, map_one]
  have hconj_ne : ∀ {w : G}, w ≠ 1 → c * w * c⁻¹ ≠ 1 := fun {w} hw h => hw (by
    have : c * w = c := by
      calc c * w = c * w * c⁻¹ * c := by group
        _ = 1 * c := by rw [h]
        _ = c := one_mul c
    exact mul_left_cancel (this.trans (mul_one c).symm))
  have hu_z : c * u * c⁻¹ = z :=
    (hz _ (hconjS u huK) (hconj_sq hu2)).resolve_left (hconj_ne hune)
  have hv_z : c * v * c⁻¹ = z :=
    (hz _ (hconjS v hvK) (hconj_sq hv2)).resolve_left (hconj_ne hvne)
  exact mul_left_cancel (mul_right_cancel (hu_z.trans hv_z.symm))

include hz in
/-- **The product of two involutions has odd order** (Gorenstein Ch. 12, Lemma 1.7; the input to
Navarro's Burnside step on p. 144).  If `uv` had even order `2s`, then `z' = (uv)ˢ` is an
involution inverted by both `u` and `v`, hence — being an involution — centralised by them; so
`u = z' = v` and `uv = z'² = 1`, contradicting even order. -/
theorem odd_orderOf_mul_of_involution_of_unique_involution {u v : G} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : Odd (orderOf (u * v)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  set g := u * v with hgdef
  obtain ⟨s, hs⟩ := hodd
  have hgpos : 0 < orderOf g := orderOf_pos g
  have hspos : 0 < s := by omega
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have hv2 : v ^ 2 = 1 := by rw [← hv, pow_orderOf_eq_one]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hu2)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hv2)
  set z' := g ^ s with hz'def
  have hz'2 : z' ^ 2 = 1 := by
    rw [hz'def, ← pow_mul, show s * 2 = orderOf g from by omega, pow_orderOf_eq_one]
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz'2)
  have hz'ne : z' ≠ 1 := by
    rw [hz'def]
    intro h
    have hdvd : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd hspos hdvd
    omega
  have hz'ord : orderOf z' = 2 := by
    have hdvd : orderOf z' ∣ 2 := orderOf_dvd_of_pow_eq_one hz'2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz'ne
    · exact h
  have hg_inv_u : u * g * u⁻¹ = g⁻¹ := by
    rw [hgdef, huinv, mul_inv_rev, huinv, hvinv]
    calc u * (u * v) * u = (u * u) * v * u := by group
      _ = v * u := by rw [← sq, hu2, one_mul]
  have hg_inv_v : v * g * v⁻¹ = g⁻¹ := by
    rw [hgdef, hvinv, mul_inv_rev, huinv, hvinv]
    calc v * (u * v) * v = v * u * (v * v) := by group
      _ = v * u := by rw [← sq, hv2, mul_one]
  have commute_of_inv : ∀ w : G, w * g * w⁻¹ = g⁻¹ → Commute w z' := by
    intro w hw
    have hsemi : SemiconjBy w g g⁻¹ := mul_inv_eq_iff_eq_mul.mp hw
    have hsp : w * g ^ s = g⁻¹ ^ s * w := hsemi.pow_right s
    have hg_inv_s : g⁻¹ ^ s = z' := by rw [inv_pow, ← hz'def]; exact hz'inv
    rw [hg_inv_s, ← hz'def] at hsp
    exact hsp
  have hu_eq : u = z' :=
    commute_involution_eq_of_unique_involution T hz hu hz'ord (commute_of_inv u hg_inv_u)
  have hv_eq : v = z' :=
    commute_involution_eq_of_unique_involution T hz hv hz'ord (commute_of_inv v hg_inv_v)
  have hg1 : g = 1 := by rw [hgdef, hu_eq, hv_eq, ← sq, hz'2]
  rw [hg1, orderOf_one] at hs
  omega

end OddOrder.GroupTheory
