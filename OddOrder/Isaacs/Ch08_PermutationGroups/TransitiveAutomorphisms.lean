/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.RegularNormal
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Isaacs, Finite Group Theory — Ch. 8: transitive automorphism actions (Lem 8.8)

Formalizes **Isaacs Lem 8.8** (pp. 229–230): if a group `A` acts via
automorphisms on a finite group `N` and the action on the nonidentity
elements of `N` is `k`-transitive with `k ≥ 1`, then

* (a) `N` is an elementary abelian `p`-group for some prime `p`
  (`isElementaryAbelian_of_isPretransitive_nonidentity`);
* (b) if `k > 1` then `p = 2` or `|N| = 3`
  (`isElementaryAbelian_two_or_natCard_eq_three`);
* (c) if `k > 2` then `|N| = 4`
  (`natCard_le_four_of_isMultiplyPretransitive_nonidentity`,
  `natCard_eq_four_of_isMultiplyPretransitive_nonidentity`).

Clause (c) is stated as `|N| ≤ 4`: in mathlib's convention
`IsMultiplyPretransitive` is vacuously true when `n` exceeds the cardinality
(there are no embeddings `Fin n ↪ Ω`), so `3`-transitivity alone does not
force `|N| ≥ 4`; the book's tacit `k ≤ |N - {1}|` (hence its clause `k = 3`)
has no separate content in this convention.
-/

namespace OddOrder.Isaacs.Ch08

open MulAction Function.Embedding OddOrder.GroupTheory

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

/-- An action by automorphisms preserves element orders. -/
lemma orderOf_smul (a : A) (x : N) : orderOf (a • x) = orderOf x :=
  orderOf_injective (MulDistribMulAction.toMulAut A N a).toMonoidHom
    (MulDistribMulAction.toMulAut A N a).injective x

section Transitive

variable [Finite N]

/-- **Isaacs Lem 8.8(a)** — if `A` acts via automorphisms on a nontrivial
finite group `N` and the action is transitive on the nonidentity elements,
then `N` is an elementary abelian `p`-group for some prime `p`. -/
theorem isElementaryAbelian_of_isPretransitive_nonidentity
    (A : Type*) [Group A] [MulDistribMulAction A N] [Nontrivial N]
    [IsPretransitive A {h : N // h ≠ 1}] :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p N := by
  haveI := Fintype.ofFinite N
  -- an element of prime order `p` (Cauchy for the least prime factor)
  have hcard : Fintype.card N ≠ 1 := Fintype.one_lt_card.ne'
  have hpp : (Fintype.card N).minFac.Prime := Nat.minFac_prime hcard
  haveI : Fact (Fintype.card N).minFac.Prime := ⟨hpp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := N) _ (Nat.minFac_dvd _)
  set p := (Fintype.card N).minFac
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hpp.one_lt.ne hx
  -- by transitivity, every nonidentity element has order `p`
  have horder : ∀ y : N, y ≠ 1 → orderOf y = p := by
    intro y hy
    obtain ⟨a, ha⟩ :=
      MulAction.exists_smul_eq A (⟨x, hx1⟩ : {h : N // h ≠ 1}) ⟨y, hy⟩
    have hval : a • x = y := congrArg Subtype.val ha
    rw [← hval, orderOf_smul, hx]
  -- hence `N` is a `p`-group, so its center is nontrivial
  have hpN : IsPGroup p N := by
    intro g
    rcases eq_or_ne g 1 with rfl | hg
    · exact ⟨0, one_pow _⟩
    · exact ⟨1, by rw [pow_one, ← horder g hg, pow_orderOf_eq_one]⟩
  haveI := hpN.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center N)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  -- a central nonidentity element is carried to every nonidentity element,
  -- and automorphisms preserve centrality, so all of `N` is central
  have hcentral : ∀ y : N, y ∈ Subgroup.center N := by
    intro y
    rcases eq_or_ne y 1 with rfl | hy
    · exact Subgroup.one_mem _
    · obtain ⟨a, ha⟩ :=
        MulAction.exists_smul_eq A (⟨z, hz1'⟩ : {h : N // h ≠ 1}) ⟨y, hy⟩
    -- y = a • z, and a • z is central
      have hval : a • z = y := congrArg Subtype.val ha
      rw [← hval, Subgroup.mem_center_iff]
      intro w
      have hw : w = a • (a⁻¹ • w) := (smul_inv_smul a w).symm
      rw [hw, ← smul_mul', ← smul_mul',
        Subgroup.mem_center_iff.mp hzc (a⁻¹ • w)]
  refine ⟨p, hpp, fun u v => ?_, fun u => ?_⟩
  · exact Subgroup.mem_center_iff.mp (hcentral v) u
  · rcases eq_or_ne u 1 with rfl | hu
    · exact one_pow p
    · rw [← horder u hu]
      exact pow_orderOf_eq_one u

end Transitive

section Helpers

/-- A finset smaller than the whole finite type omits some element. -/
private lemma exists_notMem_of_card_lt {α : Type*} [Fintype α] {s : Finset α}
    (h : s.card < Fintype.card α) : ∃ a, a ∉ s := by
  by_contra hc
  have hsub : Finset.univ ⊆ s := fun a _ => not_exists_not.mp hc a
  have := Finset.card_le_card hsub
  rw [Finset.card_univ] at this
  omega

end Helpers

section MultiplyTransitive

variable [Finite N]

/-- **Isaacs Lem 8.8(b)** — if `A` acts via automorphisms on a nontrivial
finite group `N` and the action on the nonidentity elements is
`2`-transitive, then `N` is an elementary abelian `2`-group or `|N| = 3`. -/
theorem isElementaryAbelian_two_or_natCard_eq_three
    (A : Type*) [Group A] [MulDistribMulAction A N] [Nontrivial N]
    [IsMultiplyPretransitive A {h : N // h ≠ 1} 2] :
    IsElementaryAbelian 2 N ∨ Nat.card N = 3 := by
  haveI : IsPretransitive A {h : N // h ≠ 1} :=
    isPretransitive_of_is_two_pretransitive
  obtain ⟨p, hpp, hEA⟩ :=
    isElementaryAbelian_of_isPretransitive_nonidentity (N := N) A
  rcases eq_or_ne p 2 with rfl | hp2
  · exact Or.inl hEA
  right
  -- nonidentity elements have order `p`
  have horder : ∀ y : N, y ≠ 1 → orderOf y = p := fun y hy =>
    ((Nat.Prime.eq_one_or_self_of_dvd hpp _
      (orderOf_dvd_of_pow_eq_one (hEA.pow_eq_one y))).resolve_left
      (by simpa [orderOf_eq_one_iff] using hy))
  have hp3 : 3 ≤ p := by
    rcases hpp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := hpp.two_le
      omega
  obtain ⟨x, hx1⟩ := exists_ne (1 : N)
  -- for odd `p`, `x` and `x⁻¹` are distinct nonidentity elements
  have hxinv : x⁻¹ ≠ x := by
    intro h
    have h2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel x
    have hdvd2 : p ∣ 2 := horder x hx1 ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.le_of_dvd two_pos hdvd2
    omega
  -- `|N| ≤ 3`: otherwise 2-transitivity moves `(x, x⁻¹)` to `(x, y)` with
  -- `y ∉ {1, x, x⁻¹}`, forcing `y = x⁻¹`
  have hle : Nat.card N ≤ 3 := by
    by_contra hgt
    rw [not_le] at hgt
    haveI := Fintype.ofFinite N
    classical
    obtain ⟨y, hy⟩ : ∃ y : N, y ∉ ({1, x, x⁻¹} : Finset N) := by
      refine exists_notMem_of_card_lt ?_
      calc ({1, x, x⁻¹} : Finset N).card ≤ 3 := by
            refine (Finset.card_insert_le _ _).trans ?_
            have := Finset.card_insert_le x ({x⁻¹} : Finset N)
            simp only [Finset.card_singleton] at this ⊢
            omega
        _ < Fintype.card N := by rw [← Nat.card_eq_fintype_card]; omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    obtain ⟨hy1, hyx, hyxi⟩ := hy
    set X : {h : N // h ≠ 1} := ⟨x, hx1⟩
    set Xinv : {h : N // h ≠ 1} := ⟨x⁻¹, inv_ne_one.mpr hx1⟩
    set Y : {h : N // h ≠ 1} := ⟨y, hy1⟩
    have h2t : ∀ {a b c d : {h : N // h ≠ 1}}, a ≠ b → c ≠ d →
        ∃ g : A, g • a = c ∧ g • b = d :=
      is_two_pretransitive_iff.mp inferInstance
    obtain ⟨g, hgx, hgxi⟩ := h2t (a := X) (b := Xinv) (c := X) (d := Y)
      (by simpa [X, Xinv, Subtype.ext_iff] using hxinv.symm)
      (by simpa [X, Y, Subtype.ext_iff] using (Ne.symm hyx))
    have hgx' : g • x = x := congrArg Subtype.val hgx
    have hgxi' : g • x⁻¹ = y := congrArg Subtype.val hgxi
    rw [smul_inv', hgx'] at hgxi'
    exact hyxi hgxi'.symm
  -- `p ∣ |N|` with `p ≥ 3` and `|N| ≤ 3` forces `|N| = 3`
  have hdvd : p ∣ Nat.card N := horder x hx1 ▸ orderOf_dvd_natCard x
  have hpos : 0 < Nat.card N := Nat.card_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- **Isaacs Lem 8.8(c)** — if `A` acts via automorphisms on a finite group
`N` and the action on the nonidentity elements is `3`-transitive, then
`|N| ≤ 4`.  (Under mathlib's vacuous-truth convention for multiple
transitivity this inequality is the full content of the book's clause; see
the module docstring.) -/
theorem natCard_le_four_of_isMultiplyPretransitive_nonidentity
    (A : Type*) [Group A] [MulDistribMulAction A N]
    [IsMultiplyPretransitive A {h : N // h ≠ 1} 3] :
    Nat.card N ≤ 4 := by
  by_contra hgt
  rw [not_le] at hgt
  haveI : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  haveI := Fintype.ofFinite N
  classical
  have hsub : Nat.card {h : N // h ≠ 1} = Nat.card N - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Set.card_ne_eq 1
  -- descend to 2-transitivity (legitimate: ≥ 4 nonidentity elements)
  haveI : IsMultiplyPretransitive A {h : N // h ≠ 1} 2 :=
    isMultiplyPretransitive_of_le (m := 2) (n := 3) (by omega) (by rw [hsub]; omega)
  rcases isElementaryAbelian_two_or_natCard_eq_three (N := N) A with hEA | h3
  swap
  · omega
  -- `p = 2`: pick `x ≠ 1`, `y ∉ {1, x}`; then `1, x, y, xy` are distinct
  obtain ⟨x, hx1⟩ := exists_ne (1 : N)
  obtain ⟨y, hy⟩ : ∃ y : N, y ∉ ({1, x} : Finset N) := by
    refine exists_notMem_of_card_lt ?_
    calc ({1, x} : Finset N).card ≤ 2 := by
          have := Finset.card_insert_le (1 : N) ({x} : Finset N)
          simp only [Finset.card_singleton] at this ⊢
          omega
      _ < Fintype.card N := by rw [← Nat.card_eq_fintype_card]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy1, hyx⟩ := hy
  have hxx : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hEA.pow_eq_one x)
  have hxy1 : x * y ≠ 1 := fun h =>
    hyx ((eq_inv_of_mul_eq_one_right h).trans hxx)
  have hxyx : x * y ≠ x := fun h =>
    hy1 (mul_left_cancel (h.trans (mul_one x).symm))
  have hxyy : x * y ≠ y := fun h =>
    hx1 (mul_right_cancel (h.trans (one_mul y).symm))
  obtain ⟨z, hz⟩ : ∃ z : N, z ∉ ({1, x, y, x * y} : Finset N) := by
    refine exists_notMem_of_card_lt ?_
    calc ({1, x, y, x * y} : Finset N).card ≤ 4 := by
          refine (Finset.card_insert_le _ _).trans ?_
          have h2 := Finset.card_insert_le x ({y, x * y} : Finset N)
          have h3 := Finset.card_insert_le y ({x * y} : Finset N)
          simp only [Finset.card_singleton] at h2 h3 ⊢
          omega
      _ < Fintype.card N := by rw [← Nat.card_eq_fintype_card]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hz1, hzx, hzy, hzxy⟩ := hz
  -- 3-transitivity moves `(x, y, xy)` to `(x, y, z)`, forcing `z = xy`
  set X : {h : N // h ≠ 1} := ⟨x, hx1⟩
  set Y : {h : N // h ≠ 1} := ⟨y, hy1⟩
  set XY : {h : N // h ≠ 1} := ⟨x * y, hxy1⟩
  set Z : {h : N // h ≠ 1} := ⟨z, hz1⟩
  have hYXY : Y ≠ XY := fun h => hxyy (congrArg Subtype.val h).symm
  have hYZ : Y ≠ Z := fun h => hzy (congrArg Subtype.val h).symm
  have hXmem₁ : X ∉ Set.range ⇑(embFinTwo hYXY) := by
    rintro ⟨i, hi⟩
    fin_cases i
    · exact hyx (congrArg Subtype.val hi)
    · exact hxyx (congrArg Subtype.val hi)
  have hXmem₂ : X ∉ Set.range ⇑(embFinTwo hYZ) := by
    rintro ⟨i, hi⟩
    fin_cases i
    · exact hyx (congrArg Subtype.val hi)
    · exact hzx (congrArg Subtype.val hi)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A
    (Fin.Embedding.cons (embFinTwo hYXY) hXmem₁)
    (Fin.Embedding.cons (embFinTwo hYZ) hXmem₂)
  have happ : ∀ i : Fin 3,
      g • (Fin.Embedding.cons (embFinTwo hYXY) hXmem₁) i =
        (Fin.Embedding.cons (embFinTwo hYZ) hXmem₂) i := fun i => by
    rw [← Function.Embedding.smul_apply, hg]
  have h0 : g • X = X := happ 0
  have h1 : g • Y = Y := happ 1
  have h2 : g • XY = Z := happ 2
  have hgx : g • x = x := congrArg Subtype.val h0
  have hgy : g • y = y := congrArg Subtype.val h1
  have hgxy : g • (x * y) = z := congrArg Subtype.val h2
  rw [smul_mul', hgx, hgy] at hgxy
  exact hzxy hgxy.symm

/-- **Isaacs Lem 8.8(c)**, book form — a `3`-transitive automorphism action
on the nonidentity elements of a group of order at least `4` forces the
order to be exactly `4`. -/
theorem natCard_eq_four_of_isMultiplyPretransitive_nonidentity
    (A : Type*) [Group A] [MulDistribMulAction A N]
    [IsMultiplyPretransitive A {h : N // h ≠ 1} 3]
    (h4 : 4 ≤ Nat.card N) : Nat.card N = 4 :=
  le_antisymm (natCard_le_four_of_isMultiplyPretransitive_nonidentity A) h4

end MultiplyTransitive

end OddOrder.Isaacs.Ch08
