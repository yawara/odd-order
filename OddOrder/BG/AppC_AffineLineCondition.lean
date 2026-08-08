/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.Basic

/-!
# The affine "midpoint line" condition (C) and Glauberman–Norton Proposition 6

Glauberman–Norton, *On a combinatorial problem associated with the odd order theorem*,
Proc. Amer. Math. Soc. **119** (1993), 1089–1094, §2 (`references/glauberman-norton/`).

This is the combinatorial core of BG Appendix C, Remark (IV) (issue 0179), and it is entirely
independent of the norm set: a purely affine statement over a prime field.

**Condition (C)** on a subset `S` of an affine space `A` over `𝔽_p` with direction `V`:

> whenever `b ∈ A`, `x ∈ V` and `b - x, b, b + x ∈ S`, then `b + k • x ∈ S` for all `k ∈ 𝔽_p`.

Equivalently: *any affine line meeting `S` in three points, one of them midway between the other
two, is contained in `S`.*

**Proposition 6.** If `p ≥ 5` and `|S| ≥ |A| / 2`, then `S = A`.

The hypothesis `p ≥ 5` is sharp: for `p = 2, 3` condition (C) is vacuous (a line has only `p`
points, so three points with one midway between the others already exhaust it), and small
counterexamples exist.

## Main results

- `CondCLine` / `CondC` — condition (C), on a line `ZMod p` and on a general `𝔽_p`-module.
- `eq_univ_of_condCLine` — Proposition 6, Case 1 (the line case, `r = 1`).
- `ncard_le_of_condCLine` — the contrapositive form used by Case 2: a proper (C)-subset of a
  line has at most `(p-1)/2` points.

## Implementation notes

The paper's Case 1 splits into `p = 5`, `p = 7` and `p ≥ 11`.  The argument below is uniform:
after normalizing `0, 1 ∈ S`, one shows `-2 ∈ S` and then derives a contradiction from whichever
of `4, -4` lies in `S`.  For `p = 5` this is not a separate case — there `-4 = 1`, so the first
branch fires on the already-known point `1`.
-/

namespace OddOrder.BG.AppC.Affine

variable {p : ℕ}

/-! ## Condition (C) -/

/-- **Condition (C)** of Glauberman–Norton Proposition 6, on the affine line `𝔽_p` itself:
a line meeting `S` in three points, one midway between the other two, lies in `S`.  On a line
"the line through them" is everything, so the conclusion is that `S` is everything — but the
statement is kept in the `b + k * x` form so that it is literally the restriction of `CondC`. -/
def CondCLine (S : Set (ZMod p)) : Prop :=
  ∀ b x : ZMod p, b - x ∈ S → b ∈ S → b + x ∈ S → ∀ k : ZMod p, b + k * x ∈ S

/-- **Condition (C)** of Glauberman–Norton Proposition 6 on an `𝔽_p`-module `V`, with the
affine space taken to be `V` itself.  A general affine space is a coset `a + V`, and condition
(C) transports along `v ↦ a + v`; see `AppC_GlaubermanNorton`. -/
def CondC {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (S : Set V) : Prop :=
  ∀ b x : V, b - x ∈ S → b ∈ S → b + x ∈ S → ∀ k : ZMod p, b + k • x ∈ S

variable [Fact p.Prime]

/-! ## Preliminaries on the line -/

/-- If `S` contains the whole line `{b + k * x | k}` for some `x ≠ 0`, then `S` is everything. -/
theorem eq_univ_of_forall_add_mul_mem {S : Set (ZMod p)} {b x : ZMod p} (hx : x ≠ 0)
    (h : ∀ k : ZMod p, b + k * x ∈ S) : S = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  have hy : y = b + ((y - b) * x⁻¹) * x := by field_simp; ring
  rw [hy]
  exact h _

/-- A numeral is nonzero in `ZMod p` as soon as `p` does not divide it. -/
theorem natCast_ne_zero_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : ((n : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  exact hn

theorem two_ne_zero_of_five_le (hp : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  simpa using h

theorem three_ne_zero_of_five_le (hp : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  have h : ((3 : ℕ) : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  simpa using h

theorem four_ne_zero_of_five_le (hp : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  have hp2 : p ≠ 2 := by omega
  have h2 := two_ne_zero_of_five_le hp
  have : (4 : ZMod p) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

/-! ## Case 1 of Proposition 6: the line -/

/-- Proposition 6, Case 1, normalized form: a (C)-subset of the line containing `0` and `1` and
more than half of the points is everything.

The steps are the paper's, p. 1091, with the case split on `p` removed (see the module
docstring): if `S ≠ 𝔽_p` then no pair `{x, -x}` with `x ≠ 0` lies in `S`, so `|S| ≤ (p+1)/2`;
the counting hypothesis forces equality, hence *exactly* one of `x, -x` lies in `S` for every
`x ≠ 0`.  Then `2 ∉ S` (else `0, 1, 2` fills the line), so `-2 ∈ S`, and whichever of `4, -4`
lies in `S` produces a filled line (`-4, -2, 0` or `-2, 1, 4`). -/
theorem eq_univ_of_condCLine_of_zero_one (hp : 5 ≤ p) {S : Set (ZMod p)} (hC : CondCLine S)
    (hcard : p < 2 * S.ncard) (h0 : (0 : ZMod p) ∈ S) (h1 : (1 : ZMod p) ∈ S) :
    S = Set.univ := by
  classical
  by_contra hne
  -- No pair `{x, -x}` with `x ≠ 0` is contained in `S`.
  have hpair : ∀ x : ZMod p, x ≠ 0 → x ∈ S → -x ∈ S → False := by
    intro x hx hxS hnxS
    refine hne (eq_univ_of_forall_add_mul_mem (b := 0) (x := x) hx ?_)
    intro k
    have := hC 0 x (by simpa using hnxS) h0 (by simpa using hxS) k
    simpa using this
  -- `S \ {0}` and its negative are disjoint subsets of the `p - 1` nonzero elements.
  set T : Set (ZMod p) := S \ {0} with hT
  set N : Set (ZMod p) := (fun x => -x) '' T with hN
  have hNcard : N.ncard = T.ncard := Set.ncard_image_of_injective _ neg_injective
  have hTsub : T ⊆ {x : ZMod p | x ≠ 0} := fun x hx => hx.2
  have hNsub : N ⊆ {x : ZMod p | x ≠ 0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact neg_ne_zero.mpr hy.2
  have hdisj : Disjoint T N := by
    rw [Set.disjoint_left]
    rintro y hyT ⟨z, hzT, hz⟩
    exact hpair y hyT.2 hyT.1 (by rw [← hz, neg_neg]; exact hzT.1)
  have hnz : ({x : ZMod p | x ≠ 0}).ncard = p - 1 := by
    have huniv : ({x : ZMod p | x ≠ 0}) = (Set.univ : Set (ZMod p)) \ {0} := by
      ext x; simp
    rw [huniv, Set.ncard_sdiff (by simp) (Set.toFinite _), Set.ncard_univ, Set.ncard_singleton,
      Nat.card_zmod]
  have hunion : (T ∪ N).ncard = T.ncard + N.ncard :=
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : 2 * T.ncard ≤ p - 1 := by
    have h := Set.ncard_le_ncard (Set.union_subset hTsub hNsub) (Set.toFinite _)
    rw [hunion, hNcard, hnz] at h
    omega
  -- `|S| ≤ |T| + 1`, so the counting hypothesis pins `2|T| = p - 1` exactly.
  have hST : S.ncard ≤ T.ncard + 1 := by
    have hsub : S ⊆ T ∪ {0} := by
      intro x hx
      rcases eq_or_ne x 0 with rfl | hx0
      · exact Or.inr rfl
      · exact Or.inl ⟨hx, hx0⟩
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (T ∪ {0} : Set (ZMod p)).ncard ≤ T.ncard + 1 := by
      refine (Set.ncard_union_le _ _).trans ?_
      simp
    omega
  have hp1 : p ≥ 1 := by omega
  have hexact : 2 * T.ncard = p - 1 := by omega
  -- Hence `T ∪ N` is *all* the nonzero elements: one of `x, -x` lies in `S` for every `x ≠ 0`.
  have hfull : T ∪ N = {x : ZMod p | x ≠ 0} := by
    refine Set.eq_of_subset_of_ncard_le (Set.union_subset hTsub hNsub) ?_ (Set.toFinite _)
    rw [hunion, hNcard, hnz]
    omega
  have hdich : ∀ x : ZMod p, x ≠ 0 → x ∈ S ∨ -x ∈ S := by
    intro x hx
    have : x ∈ T ∪ N := by rw [hfull]; exact hx
    rcases this with h | ⟨y, hy, hyx⟩
    · exact Or.inl h.1
    · exact Or.inr (by rw [← hyx, neg_neg]; exact hy.1)
  -- `2 ∉ S`, else `0, 1, 2` fills the line.
  have h2 : (2 : ZMod p) ∉ S := by
    intro hmem
    refine hne (eq_univ_of_forall_add_mul_mem (b := 1) (x := 1) one_ne_zero ?_)
    intro k
    have := hC 1 1 (by simpa using h0) h1 (by norm_num at hmem ⊢; exact hmem) k
    simpa using this
  have hm2 : (-2 : ZMod p) ∈ S := ((hdich 2 (two_ne_zero_of_five_le hp)).resolve_left h2)
  -- Whichever of `4, -4` lies in `S` fills a line.
  rcases hdich 4 (four_ne_zero_of_five_le hp) with h4 | hm4
  · -- `-2, 1, 4` is an arithmetic progression with difference `3`.
    refine hne (eq_univ_of_forall_add_mul_mem (b := 1) (x := 3) (three_ne_zero_of_five_le hp) ?_)
    intro k
    exact hC 1 3 (by norm_num; exact hm2) h1 (by norm_num; exact h4) k
  · -- `-4, -2, 0` is an arithmetic progression with difference `2`.
    refine hne
      (eq_univ_of_forall_add_mul_mem (b := -2) (x := 2) (two_ne_zero_of_five_le hp) ?_)
    intro k
    exact hC (-2) 2 (by norm_num; exact hm4) hm2 (by norm_num; exact h0) k

/-- The affine change of coordinates `k ↦ c + k * v` (`v ≠ 0`) used to normalize Case 1. -/
theorem eq_univ_of_condCLine (hp : 5 ≤ p) {S : Set (ZMod p)} (hC : CondCLine S)
    (hcard : p < 2 * S.ncard) : S = Set.univ := by
  classical
  -- `|S| ≥ 3`, so `S` has two distinct points `c ≠ b₀`.
  have h2 : 1 < S.ncard := by omega
  obtain ⟨c, b₀, hc, hb₀, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
  set v : ZMod p := b₀ - c with hv
  have hv0 : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  set f : ZMod p → ZMod p := fun k => c + k * v with hf
  have hfval : ∀ k : ZMod p, f k = c + k * v := fun _ => rfl
  have hfinj : Function.Injective f := by
    intro k₁ k₂ h
    rw [hfval, hfval] at h
    exact mul_right_cancel₀ hv0 (add_left_cancel h)
  have hfsurj : Function.Surjective f := by
    intro y
    refine ⟨(y - c) * v⁻¹, ?_⟩
    rw [hfval]
    field_simp
    ring
  set S' : Set (ZMod p) := f ⁻¹' S with hS'
  have hmem : ∀ k : ZMod p, k ∈ S' ↔ c + k * v ∈ S := by
    intro k; rw [hS', Set.mem_preimage, hfval]
  -- `S'` has the same size as `S`, contains `0` and `1`, and satisfies (C).
  have hcard' : S'.ncard = S.ncard := by
    have himg : f '' S' = S := Set.image_preimage_eq S hfsurj
    rw [← himg, Set.ncard_image_of_injective _ hfinj]
  have h0' : (0 : ZMod p) ∈ S' := by rw [hmem]; simpa using hc
  have h1' : (1 : ZMod p) ∈ S' := by
    rw [hmem]
    have : c + (1 : ZMod p) * v = b₀ := by rw [hv]; ring
    rw [this]; exact hb₀
  have hC' : CondCLine S' := by
    intro b x hsub hb hadd k
    rw [hmem] at hsub hb hadd ⊢
    have e1 : c + (b - x) * v = (c + b * v) - x * v := by ring
    have e2 : c + (b + x) * v = (c + b * v) + x * v := by ring
    have e3 : c + (b + k * x) * v = (c + b * v) + k * (x * v) := by ring
    rw [e1] at hsub
    rw [e2] at hadd
    rw [e3]
    exact hC (c + b * v) (x * v) hsub hb hadd k
  -- Conclude via the normalized case.
  have huniv := eq_univ_of_condCLine_of_zero_one hp hC' (by omega) h0' h1'
  ext y
  simp only [Set.mem_univ, iff_true]
  obtain ⟨k, rfl⟩ := hfsurj y
  have hk : k ∈ S' := by rw [huniv]; trivial
  rw [hmem] at hk
  rw [hfval]
  exact hk

/-- Contrapositive of Case 1, in the form Case 2 consumes it: a (C)-subset of the line that is
**not** everything has at most `(p-1)/2` points.

The parity step is where `p` odd is used: `2 * |S| ≤ p` with `p` odd upgrades to
`2 * |S| ≤ p - 1`. -/
theorem two_mul_ncard_le_of_condCLine_ne_univ (hp : 5 ≤ p) {S : Set (ZMod p)}
    (hC : CondCLine S) (hne : S ≠ Set.univ) : 2 * S.ncard ≤ p - 1 := by
  have hle : 2 * S.ncard ≤ p := by
    by_contra hcon
    exact hne (eq_univ_of_condCLine hp hC (by omega))
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hodd with ⟨m, hm⟩
  omega

end OddOrder.BG.AppC.Affine
