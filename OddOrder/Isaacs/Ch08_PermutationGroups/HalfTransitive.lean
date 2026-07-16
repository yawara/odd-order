/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Isaacs, Finite Group Theory — Ch. 8: half-transitive actions (Lem 8.10)

Formalizes **Isaacs Lem 8.10** (p. 231): a finite group covered by a
collection of proper normal subgroups with pairwise trivial intersections is
an elementary abelian `p`-group for some prime `p`
(`isElementaryAbelian_of_partition_normal`).

This is the partition lemma supporting the Passman–Isaacs half-transitivity
theorem (Isaacs Thm 8.9), to be added to this file.
-/

namespace OddOrder.Isaacs.Ch08

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- A group covered by two subgroups is one of them. -/
private lemma eq_top_or_eq_top_of_cover {H K : Subgroup G}
    (hcov : ∀ g : G, g ∈ H ∨ g ∈ K) : H = ⊤ ∨ K = ⊤ := by
  rcases Classical.em (H = ⊤) with h | hH
  · exact Or.inl h
  right
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, haH⟩ : ∃ a : G, a ∉ H := by
    by_contra hc
    exact hH (eq_top_iff.mpr fun a _ => not_exists_not.mp hc a)
  have haK : a ∈ K := (hcov a).resolve_left haH
  rcases hcov g with hgH | hgK
  · rcases hcov (a * g) with hH' | hK'
    · exact absurd (by simpa using H.mul_mem hH' (H.inv_mem hgH)) haH
    · simpa using K.mul_mem (K.inv_mem haK) hK'
  · exact hgK

/-- **Isaacs Lem 8.10** — a finite group that is the union of a collection of
proper normal subgroups intersecting pairwise trivially is an elementary
abelian `p`-group for some prime `p`. -/
theorem isElementaryAbelian_of_partition_normal [Finite G] {P : Set (Subgroup G)}
    (hproper : ∀ X ∈ P, X ≠ ⊤)
    (hnormal : ∀ X ∈ P, (X : Subgroup G).Normal)
    (hcover : ∀ g : G, ∃ X ∈ P, g ∈ X)
    (htriv : ∀ X ∈ P, ∀ Y ∈ P, X ≠ Y → X ⊓ Y = ⊥) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p G := by
  -- the hypotheses force `G` nontrivial
  rcases subsingleton_or_nontrivial G with hs | hnt
  · obtain ⟨X, hX, hmem⟩ := hcover 1
    exact absurd (eq_top_iff.mpr fun g _ => (hs.elim g 1) ▸ hmem)
      (hproper X hX)
  -- elements of distinct members commute (their commutator lies in `X ⊓ Y`)
  have hcomm : ∀ X ∈ P, ∀ Y ∈ P, X ≠ Y → ∀ x ∈ X, ∀ y ∈ Y, Commute x y := by
    intro X hX Y hY hXY x hx y hy
    have hc1 : x * y * x⁻¹ * y⁻¹ ∈ X := by
      have := X.mul_mem hx ((hnormal X hX).conj_mem x⁻¹ (X.inv_mem hx) y)
      simpa [mul_assoc] using this
    have hc2 : x * y * x⁻¹ * y⁻¹ ∈ Y := by
      exact Y.mul_mem ((hnormal Y hY).conj_mem y hy x) (Y.inv_mem hy)
    have hbot : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Y := ⟨hc1, hc2⟩
    rw [htriv X hX Y hY hXY, Subgroup.mem_bot] at hbot
    exact commutatorElement_eq_one_iff_commute.mp
      (by simpa [commutatorElement_def] using hbot)
  -- every member is central: `G ⊆ X ∪ C_G(X)`, and `G` is not the union of
  -- two proper subgroups
  have hcentral : ∀ X ∈ P, ∀ x ∈ X, x ∈ Subgroup.center G := by
    intro X hX
    have hcov2 : ∀ g : G, g ∈ X ∨ g ∈ Subgroup.centralizer (X : Set G) := by
      intro g
      obtain ⟨W, hW, hgW⟩ := hcover g
      rcases eq_or_ne W X with rfl | hWX
      · exact Or.inl hgW
      · exact Or.inr (Subgroup.mem_centralizer_iff.mpr fun x hx =>
          hcomm X hX W hW (Ne.symm hWX) x hx g hgW)
    rcases eq_top_or_eq_top_of_cover hcov2 with h | h
    · exact absurd h (hproper X hX)
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp (h ▸ Subgroup.mem_top g) x hx).symm
  -- hence `G` is abelian
  have hab : ∀ u v : G, u * v = v * u := fun u v => by
    obtain ⟨W, hW, hu⟩ := hcover u
    exact (Subgroup.mem_center_iff.mp (hcentral W hW u hu) v).symm
  -- elements of different orders lie in a common member
  have haux : ∀ x y : G, orderOf y < orderOf x → ∃ W ∈ P, x ∈ W ∧ y ∈ W := by
    intro x y hlt
    have hxo : (x * y) ^ orderOf y = x ^ orderOf y := by
      rw [Commute.mul_pow (show Commute x y from hab x y),
        pow_orderOf_eq_one, mul_one]
    have hne : x ^ orderOf y ≠ 1 := by
      intro h
      exact absurd (Nat.le_of_dvd (orderOf_pos y) (orderOf_dvd_of_pow_eq_one h))
        (by omega)
    obtain ⟨X, hX, hxX⟩ := hcover x
    obtain ⟨Z, hZ, hxyZ⟩ := hcover (x * y)
    have hXZ : X = Z := by
      by_contra hne'
      have hmem : x ^ orderOf y ∈ X ⊓ Z :=
        ⟨X.pow_mem hxX _, by rw [← hxo]; exact Z.pow_mem hxyZ _⟩
      rw [htriv X hX Z hZ hne', Subgroup.mem_bot] at hmem
      exact hne hmem
    refine ⟨X, hX, hxX, ?_⟩
    have := X.mul_mem (X.inv_mem hxX) (hXZ ▸ hxyZ)
    simpa using this
  -- elements sharing no member have equal orders
  have hkey : ∀ x y : G, (¬ ∃ W ∈ P, x ∈ W ∧ y ∈ W) → orderOf x = orderOf y := by
    intro x y hno
    rcases lt_trichotomy (orderOf x) (orderOf y) with h | h | h
    · obtain ⟨W, hW, hyW, hxW⟩ := haux y x h
      exact absurd ⟨W, hW, hxW, hyW⟩ hno
    · exact h
    · exact absurd (haux x y h) hno
  -- an element `x` of prime order `p`
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hgord : orderOf g ≠ 1 := by simpa [orderOf_eq_one_iff] using hg
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpp : (orderOf g).minFac.Prime := Nat.minFac_prime hgord
  set p := (orderOf g).minFac with hpdef
  set x := g ^ (orderOf g / p) with hxdef
  have hxord : orderOf x = p := orderOf_pow_orderOf_div hg0 (Nat.minFac_dvd _)
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    exact hpp.one_lt.ne' hxord.symm
  -- elements on opposite sides of the member containing `x` share no member
  obtain ⟨X, hX, hxX⟩ := hcover x
  obtain ⟨w, hwX⟩ : ∃ w : G, w ∉ X := by
    by_contra hc
    exact hproper X hX (eq_top_iff.mpr fun a _ => not_exists_not.mp hc a)
  have hsep : ∀ u ∈ X, u ≠ 1 → ∀ v, v ∉ X → ¬ ∃ W ∈ P, u ∈ W ∧ v ∈ W := by
    rintro u hu hu1 v hv ⟨W, hW, huW, hvW⟩
    rcases eq_or_ne W X with rfl | hWX
    · exact hv hvW
    · have hmem : u ∈ W ⊓ X := ⟨huW, hu⟩
      rw [htriv W hW X hX hWX, Subgroup.mem_bot] at hmem
      exact hu1 hmem
  -- every nonidentity element has order `p`
  have hordall : ∀ y : G, y ≠ 1 → orderOf y = p := by
    intro y hy1
    by_cases hyX : y ∈ X
    · have hyw : orderOf y = orderOf w := hkey y w (hsep y hyX hy1 w hwX)
      have hxw : orderOf x = orderOf w := hkey x w (hsep x hxX hx1 w hwX)
      rw [hyw, ← hxw, hxord]
    · exact ((hkey x y (hsep x hxX hx1 y hyX)).symm).trans hxord
  refine ⟨p, hpp, hab, fun u => ?_⟩
  rcases eq_or_ne u 1 with rfl | hu
  · exact one_pow p
  · rw [← hordall u hu]
    exact pow_orderOf_eq_one u

end OddOrder.Isaacs.Ch08
