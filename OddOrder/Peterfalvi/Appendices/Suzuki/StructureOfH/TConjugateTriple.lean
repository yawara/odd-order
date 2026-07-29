/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm
import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure

/-!
# The canonical decomposition of `t x t` for `x ∈ Q ∖ {1}`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 118:

> Let `f, g : S# → S#` and `h : S# → D` be the mappings such that, for
> `x ∈ S#`, `txt = g(x)h(x)tf(x)`.  The existence of these mappings follows
> from the fact that `txt ∉ H ∪ (Ht) ∪ (tH)` and from Chapter I, §1,
> Proposition 4(a).

Here `S = Q` (Theorem C), so the maps are defined on `Q ∖ {1}`.  Writing the
canonical form `txt = A t f(x)` of Ch. I §1 Proposition 4(a)
(`existsUnique_canonicalForm`) and splitting `A ∈ H = Q ⋊ D` as
`A = g(x) h(x)` gives the decomposition; `f(x) ≠ 1` because `txt ∉ Ht` and
`g(x) ≠ 1` because `t x⁻¹ t ∉ Ht`.

Conjugating by `a ∈ K` — which `t` inverts — turns the decomposition of
`t x t` into the one of `t (a⁻¹ x a) t`, giving the book's identity (1):

> `f(xᵃ) = f(x)^{a⁻¹}`, `g(xᵃ) = g(x)^{a⁻¹}` and `h(xᵃ) = a h(x) a`.

## Main results

* `Hypothesis.existsUnique_tConjTriple` — existence and uniqueness of the
  triple.
* `Hypothesis.tConjLeft` / `tConjMiddle` / `tConjRight` — the maps `g`, `h`,
  `f` of the book.
* `Hypothesis.tConj_conj_mem_KSet` — the identity (1).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- For `1 ≠ x ∈ Q`, the conjugate `t x t` lies outside `H`: otherwise `x`
would fix both `basept` and `t • basept`, i.e. lie in `Q ⊓ D = 1`. -/
lemma t_conj_notMem_H_of_mem_Q {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.t * x * hyp.t ∉ hyp.H := by
  intro hmem
  have hxD : x ∈ hyp.D :=
    hyp.mem_D_iff.mpr ⟨hyp.Q_le_H hx, by rwa [hyp.t_inv_eq]⟩
  have hbot : x ∈ hyp.Q ⊓ hyp.D := ⟨hx, hxD⟩
  rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
  exact hx1 hbot

/-- `t x t ∉ H t`: otherwise `t = (t x t) t x⁻¹ ∈ H`. -/
lemma t_conj_notMem_mul_t {x : G} (hx : x ∈ hyp.Q) {A : G} (hA : A ∈ hyp.H) :
    hyp.t * x * hyp.t ≠ A * hyp.t := by
  intro heq
  refine hyp.t_not_mem_H ?_
  have h : hyp.t * x = A := by
    have := congrArg (fun z : G => z * hyp.t) heq
    simpa [mul_assoc, hyp.t_inv_eq, ← sq, hyp.t_sq] using this
  have : hyp.t = A * x⁻¹ := by rw [← h]; group
  rw [this]
  exact hyp.H.mul_mem hA (hyp.H.inv_mem (hyp.Q_le_H hx))

/-- **The canonical decomposition of `t x t`** (Peterfalvi Part II, Ch. III §2,
p. 118): for `1 ≠ x ∈ Q` there are unique `g, f ∈ Q ∖ {1}` and `h ∈ D` with
`t x t = g h t f`. -/
theorem existsUnique_tConjTriple {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    ∃! p : G × G × G,
      (p.1 ∈ hyp.Q ∧ p.1 ≠ 1) ∧ p.2.1 ∈ hyp.D ∧ (p.2.2 ∈ hyp.Q ∧ p.2.2 ≠ 1) ∧
        hyp.t * x * hyp.t = p.1 * p.2.1 * hyp.t * p.2.2 := by
  obtain ⟨A, hA, f, hf, hAf⟩ :=
    hyp.exists_canonicalForm (hyp.t_conj_notMem_H_of_mem_Q hx hx1)
  -- `A = g h` with `g ∈ Q`, `h ∈ D`
  obtain ⟨g, hg, d, hd, hgd⟩ : ∃ g ∈ hyp.Q, ∃ d ∈ hyp.D, A = g * d := by
    have hmem : A ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
      rw [hyp.Q_mul_D_eq_H]; exact hA
    obtain ⟨g, hg, d, hd, hgd⟩ := hmem
    exact ⟨g, hg, d, hd, hgd.symm⟩
  -- `f ≠ 1`
  have hf1 : f ≠ 1 := by
    intro h1
    exact hyp.t_conj_notMem_mul_t hx hA (by rw [hAf, h1, mul_one])
  -- `g ≠ 1`, since otherwise `t x⁻¹ t ∈ H t`
  have hg1 : g ≠ 1 := by
    intro h1
    refine hyp.t_conj_notMem_mul_t (hyp.Q.inv_mem hx)
      (show f⁻¹ * (hyp.t * d⁻¹ * hyp.t) ∈ hyp.H from
        hyp.H.mul_mem (hyp.H.inv_mem (hyp.Q_le_H hf))
          (hyp.D_le_H (by
            have := hyp.t_conj_mem_D (hyp.D.inv_mem hd)
            rwa [hyp.t_inv_eq] at this))) ?_
    have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
    have hinv : hyp.t * x⁻¹ * hyp.t = (hyp.t * x * hyp.t)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hyp.t_inv_eq]; group
    have hrhs : f⁻¹ * (hyp.t * d⁻¹ * hyp.t) * hyp.t = f⁻¹ * (hyp.t * d⁻¹) := by
      calc f⁻¹ * (hyp.t * d⁻¹ * hyp.t) * hyp.t
          = f⁻¹ * (hyp.t * d⁻¹) * (hyp.t * hyp.t) := by group
        _ = f⁻¹ * (hyp.t * d⁻¹) := by rw [htt, mul_one]
    rw [hinv, hAf, hgd, h1, one_mul, mul_inv_rev, mul_inv_rev, hyp.t_inv_eq, hrhs]
  refine ⟨(g, d, f), ⟨⟨hg, hg1⟩, hd, ⟨hf, hf1⟩, by rw [hAf, hgd]⟩, ?_⟩
  rintro ⟨g', d', f'⟩ ⟨⟨hg', -⟩, hd', ⟨hf', -⟩, heq'⟩
  have hA' : g' * d' ∈ hyp.H := by
    rw [← SetLike.mem_coe, ← hyp.Q_mul_D_eq_H]
    exact Set.mul_mem_mul hg' hd'
  obtain ⟨hAeq, hfeq⟩ :=
    hyp.canonicalForm_unique hA' hf' hA hf (heq'.symm.trans hAf)
  -- `Q ⊓ D = 1` gives uniqueness of the `Q`-`D` split
  have hgeq : g' = g := by
    have hkey : g⁻¹ * g' = d * d'⁻¹ := by
      have h' := congrArg (fun z : G => g⁻¹ * z * d'⁻¹) (hAeq.trans hgd)
      simpa [mul_assoc] using h'
    have hbot : g⁻¹ * g' ∈ hyp.Q ⊓ hyp.D :=
      ⟨hyp.Q.mul_mem (hyp.Q.inv_mem hg) hg',
        hkey ▸ hyp.D.mul_mem hd (hyp.D.inv_mem hd')⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    exact (inv_mul_eq_one.mp hbot).symm
  have hdeq : d' = d := by
    have := hAeq.trans hgd
    rw [hgeq] at this
    exact mul_left_cancel this
  exact Prod.ext hgeq (Prod.ext hdeq hfeq)

open Classical in
/-- The triple `(g(x), h(x), f(x))` of Peterfalvi Part II, Ch. III §2, p. 118
(junk value `(1, 1, 1)` off `Q ∖ {1}`). -/
noncomputable def tConjTriple (x : G) : G × G × G :=
  if h : x ∈ hyp.Q ∧ x ≠ 1 then (hyp.existsUnique_tConjTriple h.1 h.2).choose
  else (1, 1, 1)

/-- The map `g` of Peterfalvi Part II, Ch. III §2, p. 118. -/
noncomputable def tConjLeft (x : G) : G := (hyp.tConjTriple x).1

/-- The map `h` of Peterfalvi Part II, Ch. III §2, p. 118. -/
noncomputable def tConjMiddle (x : G) : G := (hyp.tConjTriple x).2.1

/-- The map `f` of Peterfalvi Part II, Ch. III §2, p. 118. -/
noncomputable def tConjRight (x : G) : G := (hyp.tConjTriple x).2.2

lemma tConjTriple_spec {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    (hyp.tConjLeft x ∈ hyp.Q ∧ hyp.tConjLeft x ≠ 1) ∧
      hyp.tConjMiddle x ∈ hyp.D ∧
      (hyp.tConjRight x ∈ hyp.Q ∧ hyp.tConjRight x ≠ 1) ∧
      hyp.t * x * hyp.t
        = hyp.tConjLeft x * hyp.tConjMiddle x * hyp.t * hyp.tConjRight x := by
  classical
  rw [tConjLeft, tConjMiddle, tConjRight, tConjTriple, dif_pos ⟨hx, hx1⟩]
  exact (hyp.existsUnique_tConjTriple hx hx1).choose_spec.1

lemma tConjLeft_mem {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.tConjLeft x ∈ hyp.Q := (hyp.tConjTriple_spec hx hx1).1.1

lemma tConjLeft_ne_one {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.tConjLeft x ≠ 1 := (hyp.tConjTriple_spec hx hx1).1.2

lemma tConjMiddle_mem {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.tConjMiddle x ∈ hyp.D := (hyp.tConjTriple_spec hx hx1).2.1

lemma tConjRight_mem {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.tConjRight x ∈ hyp.Q := (hyp.tConjTriple_spec hx hx1).2.2.1.1

lemma tConjRight_ne_one {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.tConjRight x ≠ 1 := (hyp.tConjTriple_spec hx hx1).2.2.1.2

/-- The defining identity `t x t = g(x) h(x) t f(x)`. -/
lemma t_conj_eq {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.t * x * hyp.t
      = hyp.tConjLeft x * hyp.tConjMiddle x * hyp.t * hyp.tConjRight x :=
  (hyp.tConjTriple_spec hx hx1).2.2.2

/-- Uniqueness: any decomposition of the required shape *is* the triple. -/
lemma tConjTriple_eq_of {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1)
    {g d f : G} (hg : g ∈ hyp.Q) (hg1 : g ≠ 1) (hd : d ∈ hyp.D)
    (hf : f ∈ hyp.Q) (hf1 : f ≠ 1)
    (heq : hyp.t * x * hyp.t = g * d * hyp.t * f) :
    hyp.tConjLeft x = g ∧ hyp.tConjMiddle x = d ∧ hyp.tConjRight x = f := by
  have h := (hyp.existsUnique_tConjTriple hx hx1).unique
    (y₁ := (hyp.tConjLeft x, hyp.tConjMiddle x, hyp.tConjRight x)) (y₂ := (g, d, f))
    (hyp.tConjTriple_spec hx hx1) ⟨⟨hg, hg1⟩, hd, ⟨hf, hf1⟩, heq⟩
  exact ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h,
    congrArg (fun p => p.2.2) h⟩

/-- **Identity (1)** (Peterfalvi Part II, Ch. III §2, p. 118): conjugating by
`a ∈ K` — which `t` inverts — turns the decomposition of `t x t` into the one
of `t xᵃ t`, where `xᵃ = a⁻¹ x a`.

> `f(xᵃ) = f(x)^{a⁻¹}`, `g(xᵃ) = g(x)^{a⁻¹}` and `h(xᵃ) = a h(x) a`. -/
theorem tConjTriple_conj {x a : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1)
    (ha : a ∈ hyp.KSet) :
    hyp.tConjLeft (a⁻¹ * x * a) = a * hyp.tConjLeft x * a⁻¹ ∧
      hyp.tConjMiddle (a⁻¹ * x * a) = a * hyp.tConjMiddle x * a ∧
      hyp.tConjRight (a⁻¹ * x * a) = a * hyp.tConjRight x * a⁻¹ := by
  have haD : a ∈ hyp.D := hyp.mem_D_of_mem_KSet ha
  have haH : a ∈ hyp.H := hyp.D_le_H haD
  have hconjQ : ∀ y ∈ hyp.Q, a * y * a⁻¹ ∈ hyp.Q :=
    fun y hy => hyp.Q_normal_in_H a haH y hy
  have hconjQ' : ∀ y ∈ hyp.Q, a⁻¹ * y * a ∈ hyp.Q := by
    intro y hy
    have := hyp.Q_normal_in_H a⁻¹ (hyp.H.inv_mem haH) y hy
    rwa [inv_inv] at this
  have hxa : a⁻¹ * x * a ∈ hyp.Q := hconjQ' x hx
  have hxa1 : a⁻¹ * x * a ≠ 1 := by
    intro h
    exact hx1 (by
      have := congrArg (fun z : G => a * z * a⁻¹) h
      simpa [mul_assoc] using this)
  obtain ⟨⟨hgQ, hg1⟩, hdD, ⟨hfQ, hf1⟩, heq⟩ := hyp.tConjTriple_spec hx hx1
  have hne : ∀ y : G, y ≠ 1 → a * y * a⁻¹ ≠ 1 := by
    intro y hy h
    exact hy (by
      have := congrArg (fun z : G => a⁻¹ * z * a) h
      simpa [mul_assoc] using this)
  refine hyp.tConjTriple_eq_of hxa hxa1 (hconjQ _ hgQ) (hne _ hg1)
    (hyp.D.mul_mem (hyp.D.mul_mem haD hdD) haD) (hconjQ _ hfQ) (hne _ hf1) ?_
  have hkey : hyp.t * (a⁻¹ * x * a) * hyp.t = a * (hyp.t * x * hyp.t) * a⁻¹ :=
    hyp.t_conj_conj_of_mem_KSet ha
  have hata : a * hyp.t * a = hyp.t := hyp.mul_t_mul_self_of_mem_KSet ha
  have hexp : (a * hyp.tConjLeft x * a⁻¹) * (a * hyp.tConjMiddle x * a) * hyp.t *
      (a * hyp.tConjRight x * a⁻¹)
      = a * hyp.tConjLeft x * hyp.tConjMiddle x * (a * hyp.t * a) *
        hyp.tConjRight x * a⁻¹ := by group
  rw [hkey, heq, hexp, hata]
  group

/-- Conjugation by the involution `t` is multiplicative. -/
lemma t_conj_mul (x y : G) :
    hyp.t * (x * y) * hyp.t = (hyp.t * x * hyp.t) * (hyp.t * y * hyp.t) := by
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  calc hyp.t * (x * y) * hyp.t = hyp.t * x * (hyp.t * hyp.t) * y * hyp.t := by
        rw [htt]; group
    _ = (hyp.t * x * hyp.t) * (hyp.t * y * hyp.t) := by group

/-! ## The values at `s`, `r` and `r⁻¹`

Peterfalvi Part II, Ch. III §2, p. 118: from the structure equation
`tst = r⁻¹tr` one reads off `trt = rts` and `tr⁻¹t = str⁻¹`, whence
`h(s) = h(r) = h(r⁻¹) = 1`. -/

/-- The distinguished involution lies in `Q₀`. -/
lemma distinguishedInvolution_mem_Q0 : hyp.distinguishedInvolution ∈ hyp.Q0 :=
  ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩

lemma distinguishedInvolution_mem_Q : hyp.distinguishedInvolution ∈ hyp.Q :=
  hyp.Q0_le_Q hyp.distinguishedInvolution_mem_Q0

/-- `s` centralizes `Q` (`Q₀ ≤ Z(Q)`), in particular it commutes with `r`. -/
lemma commute_distinguishedInvolution_of_mem_Q {y : G} (hy : y ∈ hyp.Q) :
    hyp.distinguishedInvolution * y = y * hyp.distinguishedInvolution :=
  (Subgroup.mem_centralizer_iff.mp
    (hyp.Q0_le_centralizer_Q hyp.distinguishedInvolution_mem_Q0) y hy).symm

/-- `r ≠ 1`: otherwise the structure equation gives `s = t ∉ H`. -/
lemma structureConjugator_ne_one : hyp.structureConjugator ≠ 1 := by
  intro h1
  refine hyp.t_not_mem_H ?_
  have heq := hyp.structure_equation
  rw [h1, inv_one, one_mul, mul_one] at heq
  have hs : hyp.distinguishedInvolution = hyp.t := by
    have := congrArg (fun z : G => hyp.t * z * hyp.t) heq
    have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
    calc hyp.distinguishedInvolution
        = (hyp.t * hyp.t) * hyp.distinguishedInvolution * (hyp.t * hyp.t) := by
          rw [htt, one_mul, mul_one]
      _ = hyp.t * (hyp.t * hyp.distinguishedInvolution * hyp.t) * hyp.t := by group
      _ = hyp.t * hyp.t * hyp.t := by rw [heq]
      _ = hyp.t := by rw [htt, one_mul]
  rw [← hs]
  exact hyp.distinguishedInvolution_mem_H

/-- **(3a)** `t r t = r t s` (Peterfalvi Part II, Ch. III §2, p. 118). -/
lemma t_conj_structureConjugator :
    hyp.t * hyp.structureConjugator * hyp.t
      = hyp.structureConjugator * hyp.t * hyp.distinguishedInvolution := by
  have heq := hyp.structure_equation
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  calc hyp.t * hyp.structureConjugator * hyp.t
      = hyp.structureConjugator *
          (hyp.structureConjugator⁻¹ * hyp.t * hyp.structureConjugator) * hyp.t := by
        group
    _ = hyp.structureConjugator *
          (hyp.t * hyp.distinguishedInvolution * hyp.t) * hyp.t := by rw [← heq]
    _ = hyp.structureConjugator * hyp.t * hyp.distinguishedInvolution *
          (hyp.t * hyp.t) := by group
    _ = hyp.structureConjugator * hyp.t * hyp.distinguishedInvolution := by
        rw [htt, mul_one]

/-- **(3b)** `t r⁻¹ t = s t r⁻¹` (Peterfalvi Part II, Ch. III §2, p. 118). -/
lemma t_conj_structureConjugator_inv :
    hyp.t * hyp.structureConjugator⁻¹ * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.structureConjugator⁻¹ := by
  have h := congrArg (fun z : G => z⁻¹) hyp.t_conj_structureConjugator
  simp only [mul_inv_rev, hyp.t_inv_eq] at h
  have hs : hyp.distinguishedInvolution⁻¹ = hyp.distinguishedInvolution := by
    have h2 := hyp.distinguishedInvolution_sq
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_left h2
  rw [hs] at h
  calc hyp.t * hyp.structureConjugator⁻¹ * hyp.t
      = hyp.t * (hyp.structureConjugator⁻¹ * hyp.t) := by group
    _ = hyp.distinguishedInvolution * (hyp.t * hyp.structureConjugator⁻¹) := h
    _ = hyp.distinguishedInvolution * hyp.t * hyp.structureConjugator⁻¹ := by group

/-- `h(s) = 1` (Peterfalvi Part II, Ch. III §2, p. 118): the structure equation
`tst = r⁻¹ · 1 · t · r` *is* the canonical decomposition of `t s t`. -/
lemma tConjTriple_distinguishedInvolution :
    hyp.tConjLeft hyp.distinguishedInvolution = hyp.structureConjugator⁻¹ ∧
      hyp.tConjMiddle hyp.distinguishedInvolution = 1 ∧
      hyp.tConjRight hyp.distinguishedInvolution = hyp.structureConjugator := by
  refine hyp.tConjTriple_eq_of hyp.distinguishedInvolution_mem_Q
    hyp.distinguishedInvolution_ne_one
    (hyp.Q.inv_mem hyp.structureConjugator_mem_Q)
    (inv_ne_one.mpr hyp.structureConjugator_ne_one) (one_mem _)
    hyp.structureConjugator_mem_Q hyp.structureConjugator_ne_one ?_
  rw [hyp.structure_equation, mul_one]

/-- `h(r) = 1` (Peterfalvi Part II, Ch. III §2, p. 118), from `t r t = r t s`. -/
lemma tConjTriple_structureConjugator :
    hyp.tConjLeft hyp.structureConjugator = hyp.structureConjugator ∧
      hyp.tConjMiddle hyp.structureConjugator = 1 ∧
      hyp.tConjRight hyp.structureConjugator = hyp.distinguishedInvolution := by
  refine hyp.tConjTriple_eq_of hyp.structureConjugator_mem_Q
    hyp.structureConjugator_ne_one hyp.structureConjugator_mem_Q
    hyp.structureConjugator_ne_one (one_mem _) hyp.distinguishedInvolution_mem_Q
    hyp.distinguishedInvolution_ne_one ?_
  rw [hyp.t_conj_structureConjugator, mul_one]

/-- `h(r⁻¹) = 1` (Peterfalvi Part II, Ch. III §2, p. 118), from
`t r⁻¹ t = s t r⁻¹`. -/
lemma tConjTriple_structureConjugator_inv :
    hyp.tConjLeft hyp.structureConjugator⁻¹ = hyp.distinguishedInvolution ∧
      hyp.tConjMiddle hyp.structureConjugator⁻¹ = 1 ∧
      hyp.tConjRight hyp.structureConjugator⁻¹ = hyp.structureConjugator⁻¹ := by
  refine hyp.tConjTriple_eq_of (hyp.Q.inv_mem hyp.structureConjugator_mem_Q)
    (inv_ne_one.mpr hyp.structureConjugator_ne_one)
    hyp.distinguishedInvolution_mem_Q hyp.distinguishedInvolution_ne_one
    (one_mem _) (hyp.Q.inv_mem hyp.structureConjugator_mem_Q)
    (inv_ne_one.mpr hyp.structureConjugator_ne_one) ?_
  rw [hyp.t_conj_structureConjugator_inv, mul_one]

/-- `(st)² = (st)^r` (Peterfalvi Part II, Ch. III §2, p. 118): the structure
equation rewrites `tst`, and `s` centralizes `Q ∋ r`. -/
lemma sq_st_eq_conj_structureConjugator :
    (hyp.distinguishedInvolution * hyp.t) ^ 2
      = hyp.structureConjugator⁻¹ * (hyp.distinguishedInvolution * hyp.t) *
          hyp.structureConjugator := by
  have hcomm := hyp.commute_distinguishedInvolution_of_mem_Q
    (hyp.Q.inv_mem hyp.structureConjugator_mem_Q)
  calc (hyp.distinguishedInvolution * hyp.t) ^ 2
      = hyp.distinguishedInvolution *
          (hyp.t * hyp.distinguishedInvolution * hyp.t) := by rw [pow_two]; group
    _ = hyp.distinguishedInvolution *
          (hyp.structureConjugator⁻¹ * hyp.t * hyp.structureConjugator) := by
        rw [hyp.structure_equation]
    _ = (hyp.distinguishedInvolution * hyp.structureConjugator⁻¹) * hyp.t *
          hyp.structureConjugator := by group
    _ = (hyp.structureConjugator⁻¹ * hyp.distinguishedInvolution) * hyp.t *
          hyp.structureConjugator := by rw [hcomm]
    _ = hyp.structureConjugator⁻¹ * (hyp.distinguishedInvolution * hyp.t) *
          hyp.structureConjugator := by group

/-- **`r² ≠ 1` when `st` has order `5`** (Peterfalvi Part II, Ch. III §2,
p. 118): iterating `(st)^r = (st)²` gives `(st)^{r²} = (st)⁴`, so `r² = 1`
would force `(st)³ = 1`. -/
lemma structureConjugator_sq_ne_one
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5) :
    hyp.structureConjugator ^ 2 ≠ 1 := by
  intro hr2
  set u : G := hyp.distinguishedInvolution * hyp.t with hu
  set r : G := hyp.structureConjugator with hr
  have hstep : u ^ 2 = r⁻¹ * u * r := hyp.sq_st_eq_conj_structureConjugator
  have hstep2 : u ^ 4 = r⁻¹ * (u ^ 2) * r := by
    have : (r⁻¹ * u * r) ^ 2 = r⁻¹ * u ^ 2 * r := by
      rw [pow_two, pow_two]; group
    calc u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (r⁻¹ * u * r) ^ 2 := by rw [hstep]
      _ = r⁻¹ * u ^ 2 * r := this
  have hcancel : r⁻¹ * (u ^ 2) * r = u := by
    rw [hstep]
    have hrr : r * r = 1 := by rw [← pow_two]; exact hr2
    calc r⁻¹ * (r⁻¹ * u * r) * r = (r * r)⁻¹ * u * (r * r) := by group
      _ = u := by rw [hrr, inv_one, one_mul, mul_one]
  have h4 : u ^ 4 = u := hstep2.trans hcancel
  have h3 : u ^ 3 = 1 := by
    have h' : u ^ 3 * u = 1 * u := by
      rw [one_mul, ← pow_succ]
      exact h4
    exact mul_right_cancel h'
  have hdvd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hu] at h5
  rw [h5] at hdvd
  omega

/-! ## The main computation (4)

Peterfalvi Part II, Ch. III §2, p. 118: for `k ∈ K#` and `ℓ ∈ K` determined by
`s k s k⁻¹ = s^ℓ`,

`t r r^{-k} t = r r^{-ℓ⁻¹} · ℓ²k² · t · r^{ℓ⁻¹k⁻²} r^{-k⁻¹}`,

so `h(r r^{-k}) = ℓ²k² ∈ K`.  Here `x^a = a⁻¹ x a`. -/

/-- **The identity (4)** (Peterfalvi Part II, Ch. III §2, p. 118), as a pure
computation in `G`: it uses only that `t` inverts `k` and `ℓ`, that `k` and `ℓ`
commute (`K` is cyclic), the structure equation `tst = r⁻¹tr` and the defining
relation `s k s k⁻¹ = s^ℓ`. -/
theorem t_conj_structureConjugator_mul_conj_inv {k l : G} (hk : k ∈ hyp.KSet)
    (hl : l ∈ hyp.KSet)
    (hskl : hyp.distinguishedInvolution * k * hyp.distinguishedInvolution * k⁻¹
      = l⁻¹ * hyp.distinguishedInvolution * l) :
    hyp.t * (hyp.structureConjugator * (k⁻¹ * hyp.structureConjugator⁻¹ * k))
        * hyp.t
      = (hyp.structureConjugator * (l * hyp.structureConjugator⁻¹ * l⁻¹)) *
          (l ^ 2 * k ^ 2) * hyp.t *
          ((k ^ 2 * (l * hyp.structureConjugator * l⁻¹) * (k ^ 2)⁻¹) *
            (k * hyp.structureConjugator⁻¹ * k⁻¹)) := by
  set s : G := hyp.distinguishedInvolution with hs
  set r : G := hyp.structureConjugator with hr
  set T : G := hyp.t with hT
  have htk : T * k * T = k⁻¹ := hk.2
  have htki : T * k⁻¹ * T = k := by
    have := (hyp.inv_mem_KSet hk).2
    rwa [inv_inv] at this
  have hkT : k * T = T * k⁻¹ := by
    have h := htki
    calc k * T = (T * k⁻¹ * T) * T := by rw [h]
      _ = T * k⁻¹ * (T * T) := by group
      _ = T * k⁻¹ := by
          rw [show T * T = 1 by rw [hT, ← sq]; exact hyp.t_sq, mul_one]
  have hlT : l * T = T * l⁻¹ := by
    have h : T * l⁻¹ * T = l := by
      have := (hyp.inv_mem_KSet hl).2
      rwa [inv_inv] at this
    calc l * T = (T * l⁻¹ * T) * T := by rw [h]
      _ = T * l⁻¹ * (T * T) := by group
      _ = T * l⁻¹ := by
          rw [show T * T = 1 by rw [hT, ← sq]; exact hyp.t_sq, mul_one]
  have hts : T * s * T = r⁻¹ * T * r := hyp.structure_equation
  have htrt : T * r * T = r * T * s := hyp.t_conj_structureConjugator
  have htrit : T * r⁻¹ * T = s * T * r⁻¹ := hyp.t_conj_structureConjugator_inv
  -- the left-hand side, expanded through `t`-conjugation
  have hL : T * (r * (k⁻¹ * r⁻¹ * k)) * T
      = (r * T * s) * (k * (s * T * r⁻¹) * k⁻¹) := by
    rw [hyp.t_conj_mul r (k⁻¹ * r⁻¹ * k), hyp.t_conj_mul (k⁻¹ * r⁻¹) k,
      hyp.t_conj_mul k⁻¹ r⁻¹, htrt, htrit, htk, htki]
  -- both sides reduce to the same word
  have hLnorm : (r * T * s) * (k * (s * T * r⁻¹) * k⁻¹)
      = r * l * r⁻¹ * T * r * l⁻¹ * k⁻¹ * r⁻¹ * k⁻¹ := by
    have e3 : (l * k) * T = T * l⁻¹ * k⁻¹ := by
      calc (l * k) * T = l * (k * T) := by group
        _ = l * (T * k⁻¹) := by rw [hkT]
        _ = (l * T) * k⁻¹ := by group
        _ = (T * l⁻¹) * k⁻¹ := by rw [hlT]
        _ = T * l⁻¹ * k⁻¹ := by group
    calc (r * T * s) * (k * (s * T * r⁻¹) * k⁻¹)
        = r * T * (s * k * s * k⁻¹) * (k * T * r⁻¹ * k⁻¹) := by group
      _ = r * T * (l⁻¹ * s * l) * (k * T * r⁻¹ * k⁻¹) := by rw [hskl]
      _ = r * (T * l⁻¹) * s * ((l * k) * T) * r⁻¹ * k⁻¹ := by group
      _ = r * (T * l⁻¹) * s * (T * l⁻¹ * k⁻¹) * r⁻¹ * k⁻¹ := by rw [e3]
      _ = r * (l * T) * s * (T * l⁻¹ * k⁻¹) * r⁻¹ * k⁻¹ := by rw [hlT]
      _ = r * l * (T * s * T) * l⁻¹ * k⁻¹ * r⁻¹ * k⁻¹ := by group
      _ = r * l * (r⁻¹ * T * r) * l⁻¹ * k⁻¹ * r⁻¹ * k⁻¹ := by rw [hts]
      _ = r * l * r⁻¹ * T * r * l⁻¹ * k⁻¹ * r⁻¹ * k⁻¹ := by group
  have hk2T : k ^ 2 * T * k ^ 2 = T := by
    calc k ^ 2 * T * k ^ 2 = k * (k * T) * k * k := by rw [pow_two]; group
      _ = k * (T * k⁻¹) * k * k := by rw [hkT]
      _ = (k * T) * k := by group
      _ = (T * k⁻¹) * k := by rw [hkT]
      _ = T := by group
  have hlTl : l * T * l = T := by
    calc l * T * l = (T * l⁻¹) * l := by rw [hlT]
      _ = T := by group
  have hRnorm : (r * (l * r⁻¹ * l⁻¹)) * (l ^ 2 * k ^ 2) * T *
      ((k ^ 2 * (l * r * l⁻¹) * (k ^ 2)⁻¹) * (k * r⁻¹ * k⁻¹))
      = r * l * r⁻¹ * T * r * l⁻¹ * k⁻¹ * r⁻¹ * k⁻¹ := by
    calc (r * (l * r⁻¹ * l⁻¹)) * (l ^ 2 * k ^ 2) * T *
          ((k ^ 2 * (l * r * l⁻¹) * (k ^ 2)⁻¹) * (k * r⁻¹ * k⁻¹))
        = r * l * r⁻¹ * (l * (k ^ 2 * T * k ^ 2) * l) * r * l⁻¹ * k⁻¹ * r⁻¹ *
            k⁻¹ := by group
      _ = r * l * r⁻¹ * (l * T * l) * r * l⁻¹ * k⁻¹ * r⁻¹ * k⁻¹ := by rw [hk2T]
      _ = r * l * r⁻¹ * T * r * l⁻¹ * k⁻¹ * r⁻¹ * k⁻¹ := by rw [hlTl]
  exact hL.trans (hLnorm.trans hRnorm.symm)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
