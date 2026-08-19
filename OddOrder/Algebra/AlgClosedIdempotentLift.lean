/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Nakayama
import OddOrder.Algebra.AlgClosedFractionField
import OddOrder.Algebra.IdempotentLift

/-!
# Idempotents lift over a coefficient ring whose fraction field is algebraically closed

Let `A` be a local integrally closed domain whose fraction field is algebraically closed, and let
`B` be a commutative `A`-algebra that is free of finite rank.  Then idempotents lift along
`B ↠ B/𝔪B`.

The fraction field is written `FractionRing A` rather than an abstract `K`, so that the hypothesis
is a genuine instance argument: an abstract `K` occurs only in the hypotheses and would have to be
threaded explicitly through every consumer.

The usual hypothesis for lifting idempotents is that `A` be `𝔪`-adically complete, so that Newton's
iteration `e ↦ 3e² - 2e³` converges.  That is unavailable for the coefficient rings that make the
*ordinary* side of modular representation theory split — the valuation ring of `ℂ_[p]` has
divisible value group, hence `𝔪² = 𝔪`, hence is not adically complete (issue 9506).  Such a ring
is still Henselian, and for a Henselian local ring idempotents do lift in every module-finite
algebra (Stacks 09XI), but that route needs Hensel's lemma in its *factorization* form, which
mathlib does not have — mathlib's `HenselianLocalRing` is the single-root form and is used nowhere
outside `RingTheory/Henselian.lean`.

Here the factorization form is not needed, because `exists_multiset_prod_X_sub_C` gives something
stronger than Hensel: **every monic polynomial over `A` splits into linear factors over `A`**.
Given `b` with `b² ≡ b`, take `f = X · charpoly(μ_b)`, split it as `∏ (X - λᵢ)`, and separate the
roots by whether `λᵢ ∈ 𝔪`.  Two linear factors from opposite sides differ by a unit, so the two
partial products `α`, `β` are coprime — no resultants and no lifting of factorizations.  Then
`αβ = f(b) = 0`, so a Bézout combination `u·α` is idempotent, and multiplying the Bézout identity
by `b` modulo `𝔪B` identifies it with `b`.

## Main results

* `OddOrder.exists_isIdempotentElem_sub_mem_of_multiset_prod_eq_zero` — the ring-theoretic core:
  a split annihilating polynomial with at least one root in `𝔪` produces the idempotent
* `OddOrder.map_maximalIdeal_le_jacobson_bot` — what makes the lift unique
* `OddOrder.exists_isIdempotentElem_sub_mem_of_isAlgClosed` — idempotents lift along
  `B ↠ B/𝔪B`
* `OddOrder.existsUnique_isIdempotentElem_sub_mem_of_isAlgClosed` — uniquely so
-/

namespace OddOrder

open IsLocalRing Polynomial

/-! ### Coprimality of multiset products -/

theorem isCoprime_multiset_prod_left {R : Type*} [CommSemiring R] {s : Multiset R} {x : R}
    (h : ∀ y ∈ s, IsCoprime y x) : IsCoprime s.prod x := by
  induction s using Multiset.induction_on with
  | empty => simpa using isCoprime_one_left
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a s)).mul_left
      (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

theorem isCoprime_multiset_prod_right {R : Type*} [CommSemiring R] {s : Multiset R} {x : R}
    (h : ∀ y ∈ s, IsCoprime x y) : IsCoprime x s.prod := by
  simpa only [isCoprime_comm] using
    isCoprime_multiset_prod_left (fun y hy => (isCoprime_comm).mp (h y hy))

/-! ### The extended maximal ideal lies in the Jacobson radical

This is what makes the lift *unique*; it needs only module-finiteness, no completeness. -/

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]

/-- **`1 + w` is a unit for `w ∈ 𝔪B`**, when `B` is module-finite over the local ring `A`.  If the
ideal `(1 + w)` were proper, the quotient `B/(1+w)` would be a nonzero finite `A`-module equal to
`𝔪` times itself — `1 = -w` there — which Nakayama forbids. -/
theorem isUnit_one_add_of_mem_map_maximalIdeal [Module.Finite A B] {w : B}
    (hw : w ∈ (maximalIdeal A).map (algebraMap A B)) : IsUnit (1 + w) := by
  rw [← Ideal.span_singleton_eq_top]
  by_contra hne
  set I : Ideal B := Ideal.span {1 + w} with hI
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : Module.Finite A (B ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap Ideal.Quotient.mk_surjective
  refine Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (M := B ⧸ I)
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A (B ⧸ I))) ?_
  have hmk : (Ideal.Quotient.mk I) w ∈ (maximalIdeal A).map (algebraMap A (B ⧸ I)) := by
    rw [IsScalarTower.algebraMap_eq A B (B ⧸ I), ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hw
  have hone : (1 : B ⧸ I) ∈ (maximalIdeal A).map (algebraMap A (B ⧸ I)) := by
    have h0 : (Ideal.Quotient.mk I) (1 + w) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [map_add, map_one] at h0
    rw [eq_neg_of_add_eq_zero_left h0]
    exact neg_mem hmk
  have htop : (maximalIdeal A).map (algebraMap A (B ⧸ I)) = ⊤ := (Ideal.eq_top_iff_one _).mpr hone
  rw [Ideal.smul_top_eq_map, htop]
  rfl

/-- **The extended maximal ideal is inside the Jacobson radical.** -/
theorem map_maximalIdeal_le_jacobson_bot [Module.Finite A B] :
    (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson (⊥ : Ideal B) := by
  intro x hx
  refine Ideal.mem_jacobson_bot.mpr fun y => ?_
  simpa [add_comm] using isUnit_one_add_of_mem_map_maximalIdeal (Ideal.mul_mem_right y _ hx)

/-! ### The core construction -/

/-- **Idempotents lift, given a split annihilating polynomial.**  If `∏_{λ ∈ s} (b - λ) = 0` with
`s` containing at least one element of `𝔪`, and `b² ≡ b` modulo `𝔪B`, then some idempotent of `B`
is congruent to `b`.

Splitting `s` into the roots inside `𝔪` and the roots outside makes the two partial products `α`,
`β` coprime — two linear factors from opposite sides differ by a unit of `A`.  A Bézout
combination `u·α` is then idempotent because `αβ = 0`, and multiplying `u·α + v·β = 1` by `b` in
`B/𝔪B` — where `α ≡ b` because every root of the first group is `≡ 0` and `b` is idempotent —
shows `u·α ≡ b`. -/
theorem exists_isIdempotentElem_sub_mem_of_multiset_prod_eq_zero
    {b : B} (hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B))
    {s : Multiset A} (hs : (s.map fun l => b - algebraMap A B l).prod = 0)
    (h0 : ∃ l ∈ s, l ∈ maximalIdeal A) :
    ∃ e : B, IsIdempotentElem e ∧ e - b ∈ (maximalIdeal A).map (algebraMap A B) := by
  classical
  set J : Ideal B := (maximalIdeal A).map (algebraMap A B) with hJ
  set F : A → B := fun l => b - algebraMap A B l with hF
  set sg := s.filter (fun l => l ∈ maximalIdeal A) with hsg
  set sh := s.filter (fun l => l ∉ maximalIdeal A) with hsh
  set α := (sg.map F).prod with hα
  set β := (sh.map F).prod with hβ
  have hsplit : sg + sh = s := Multiset.filter_add_not _ s
  have hab : α * β = 0 := by
    rw [hα, hβ, ← Multiset.prod_add, ← Multiset.map_add, hsplit]; exact hs
  -- Two linear factors from opposite sides of the partition differ by a unit.
  have hcop : IsCoprime α β := by
    refine isCoprime_multiset_prod_left fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp hy
    refine isCoprime_multiset_prod_right fun z hz => ?_
    obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hz
    have hlm : l ∈ maximalIdeal A := (Multiset.mem_filter.mp hl).2
    have hmm : m ∉ maximalIdeal A := (Multiset.mem_filter.mp hm).2
    have hsub : m - l ∉ maximalIdeal A := fun h => hmm (by
      simpa using (maximalIdeal A).add_mem hlm h)
    have hunit : IsUnit (m - l) := by
      by_contra hcon
      exact hsub ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon))
    obtain ⟨w, hw⟩ := hunit.map (algebraMap A B)
    refine ⟨(↑w⁻¹ : B), -(↑w⁻¹ : B), ?_⟩
    have hdiff : F l - F m = (w : B) := by simp only [hF, hw, map_sub]; ring
    calc (↑w⁻¹ : B) * F l + -(↑w⁻¹ : B) * F m = (↑w⁻¹ : B) * (F l - F m) := by ring
      _ = 1 := by rw [hdiff, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : u * α = 1 - v * β := by rw [← huv]; ring
  refine ⟨u * α, ?_, ?_⟩
  · calc (u * α) * (u * α) = (u * α) * (1 - v * β) := by rw [← h1]
      _ = u * α - (u * v) * (α * β) := by ring
      _ = u * α := by rw [hab]; ring
  -- Modulo `𝔪B` the first partial product is `b` itself, and the Bézout identity times `b` gives
  -- `u·α ≡ b`.
  rw [← Ideal.Quotient.eq]
  set q := Ideal.Quotient.mk J with hq
  set c := q b with hcdef
  have hc : c * c = c := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr hb
    rw [map_sub, map_mul] at this
    rw [hcdef, ← sub_eq_zero]; exact this
  have hzero : ∀ l ∈ sg, q (F l) = c := fun l hl => by
    have : algebraMap A B l ∈ J := Ideal.mem_map_of_mem _ (Multiset.mem_filter.mp hl).2
    rw [hF, map_sub, (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr this, sub_zero]
  have hcard : sg ≠ 0 := by
    obtain ⟨l, hls, hlm⟩ := h0
    exact fun h => absurd (h ▸ Multiset.mem_filter.mpr ⟨hls, hlm⟩) (Multiset.notMem_zero l)
  have hqa : q α = c := by
    have hall : ∀ x ∈ (sg.map F).map q, x = c := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp hy
      exact hzero l hl
    have hrep : (sg.map F).map q = Multiset.replicate (Multiset.card sg) c := by
      have hcard' : Multiset.card ((sg.map F).map q) = Multiset.card sg := by simp
      rw [← hcard']
      exact Multiset.eq_replicate_card.mpr hall
    rw [hα, map_multiset_prod, hrep, Multiset.prod_replicate]
    obtain ⟨n, hn⟩ : ∃ n, Multiset.card sg = n + 1 := by
      cases hn : Multiset.card sg with
      | zero => exact absurd (Multiset.card_eq_zero.mp hn) hcard
      | succ n => exact ⟨n, rfl⟩
    rw [hn]
    exact IsIdempotentElem.pow_succ_eq (n := n) hc
  have hbez : q u * c + q v * q β = 1 := by
    have := congrArg q huv
    rwa [map_add, map_mul, map_mul, map_one, hqa] at this
  have hcb : c * q β = 0 := by
    have := congrArg q hab
    rwa [map_mul, map_zero, hqa] at this
  rw [map_mul, hqa]
  linear_combination c * hbez - q u * hc - q v * hcb

/-! ### Lifting idempotents along `B ↠ B/𝔪B` -/

variable [IsIntegrallyClosed A]

/-- **Idempotents lift along `B ↠ B/𝔪B`** when the fraction field of `A` is algebraically closed
and `B` is free of finite rank over `A`.

`f = X · charpoly(μ_b)` is monic, kills `b` by Cayley–Hamilton, and splits into linear factors
over `A` (`exists_multiset_prod_X_sub_C`); prefixing the factor `X` puts `0` — an element of `𝔪` —
among the roots, which is what
`exists_isIdempotentElem_sub_mem_of_multiset_prod_eq_zero` asks for. -/
theorem exists_isIdempotentElem_sub_mem_of_isAlgClosed [IsDomain A]
    [IsAlgClosed (FractionRing A)] [Module.Free A B] [Module.Finite A B]
    {b : B} (hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B)) :
    ∃ e : B, IsIdempotentElem e ∧ e - b ∈ (maximalIdeal A).map (algebraMap A B) := by
  classical
  -- Cayley–Hamilton for multiplication by `b`
  set f : A[X] := (Algebra.lmul A B b).charpoly with hf
  have hfm : f.Monic := LinearMap.charpoly_monic _
  have hfb : (aeval b) f = 0 := by
    have hlm : (aeval (Algebra.lmul A B b)) f = 0 := LinearMap.aeval_self_charpoly _
    rw [Polynomial.aeval_algHom_apply] at hlm
    exact Algebra.lmul_injective (by rw [hlm, map_zero])
  obtain ⟨s, hs⟩ := exists_multiset_prod_X_sub_C (A := A) (FractionRing A) hfm
  refine exists_isIdempotentElem_sub_mem_of_multiset_prod_eq_zero hb (s := (0 : A) ::ₘ s) ?_
    ⟨0, Multiset.mem_cons_self _ _, Submodule.zero_mem _⟩
  have hval : ∀ t : Multiset A, (aeval b) (t.map fun a => X - C a).prod
      = (t.map fun l => b - algebraMap A B l).prod := by
    intro t
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun l _ => by simp
  rw [Multiset.map_cons, Multiset.prod_cons, ← hval s, ← hs, hfb, mul_zero]

/-- **Idempotents lift uniquely along `B ↠ B/𝔪B`.**  Uniqueness needs only that `𝔪B` sits inside
the Jacobson radical, which is Nakayama and holds for any module-finite `B`. -/
theorem existsUnique_isIdempotentElem_sub_mem_of_isAlgClosed [IsDomain A]
    [IsAlgClosed (FractionRing A)] [Module.Free A B] [Module.Finite A B]
    {b : B} (hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B)) :
    ∃! e : B, IsIdempotentElem e ∧ e - b ∈ (maximalIdeal A).map (algebraMap A B) := by
  obtain ⟨e, he, heb⟩ := exists_isIdempotentElem_sub_mem_of_isAlgClosed (A := A) hb
  refine ⟨e, ⟨he, heb⟩, fun f hf => ?_⟩
  refine eq_of_isIdempotentElem_of_sub_mem _
    (map_maximalIdeal_le_jacobson_bot (A := A) (B := B)) hf.1 he ?_
  have hrw : f - e = (f - b) - (e - b) := by ring
  rw [hrw]
  exact Ideal.sub_mem _ hf.2 heb

end OddOrder
