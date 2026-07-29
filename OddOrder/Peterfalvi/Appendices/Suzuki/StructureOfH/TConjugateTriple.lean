/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm
import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure
import OddOrder.Peterfalvi.Appendices.Suzuki.KCyclic

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

/-- The decomposition `H = Q ⋊ D` is unique (`Q ⊓ D = 1`). -/
lemma eq_of_mul_eq_mul_of_mem_Q_mem_D {g g' d d' : G} (hg : g ∈ hyp.Q)
    (hg' : g' ∈ hyp.Q) (hd : d ∈ hyp.D) (hd' : d' ∈ hyp.D)
    (heq : g * d = g' * d') : g = g' ∧ d = d' := by
  have hkey : g⁻¹ * g' = d * d'⁻¹ := by
    have h' := congrArg (fun z : G => g⁻¹ * z * d'⁻¹) heq
    have h'' : d * d'⁻¹ = g⁻¹ * g' := by simpa [mul_assoc] using h'
    exact h''.symm
  have hbot : g⁻¹ * g' ∈ hyp.Q ⊓ hyp.D :=
    ⟨hyp.Q.mul_mem (hyp.Q.inv_mem hg) hg',
      hkey ▸ hyp.D.mul_mem hd (hyp.D.inv_mem hd')⟩
  rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
  have hgg : g = g' := inv_mul_eq_one.mp hbot
  refine ⟨hgg, ?_⟩
  rw [hgg] at heq
  exact mul_left_cancel heq

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
  obtain ⟨hgeq, hdeq⟩ :=
    hyp.eq_of_mul_eq_mul_of_mem_Q_mem_D hg' hg hd' hd (hAeq.trans hgd)
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

/-- Uniqueness: any decomposition of the required shape *is* the triple.  The
non-triviality of the outer factors is automatic, so it is not required here. -/
lemma tConjTriple_eq_of {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1)
    {g d f : G} (hg : g ∈ hyp.Q) (hd : d ∈ hyp.D) (hf : f ∈ hyp.Q)
    (heq : hyp.t * x * hyp.t = g * d * hyp.t * f) :
    hyp.tConjLeft x = g ∧ hyp.tConjMiddle x = d ∧ hyp.tConjRight x = f := by
  obtain ⟨⟨hgQ, -⟩, hdD, ⟨hfQ, -⟩, href⟩ := hyp.tConjTriple_spec hx hx1
  have hA1 : hyp.tConjLeft x * hyp.tConjMiddle x ∈ hyp.H := by
    rw [← SetLike.mem_coe, ← hyp.Q_mul_D_eq_H]; exact Set.mul_mem_mul hgQ hdD
  have hA2 : g * d ∈ hyp.H := by
    rw [← SetLike.mem_coe, ← hyp.Q_mul_D_eq_H]; exact Set.mul_mem_mul hg hd
  obtain ⟨hAeq, hfeq⟩ :=
    hyp.canonicalForm_unique hA1 hfQ hA2 hf (href.symm.trans heq)
  obtain ⟨hgeq, hdeq⟩ :=
    hyp.eq_of_mul_eq_mul_of_mem_Q_mem_D hgQ hg hdD hd hAeq
  exact ⟨hgeq, hdeq, hfeq⟩

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
  refine hyp.tConjTriple_eq_of hxa hxa1 (hconjQ _ hgQ)
    (hyp.D.mul_mem (hyp.D.mul_mem haD hdD) haD) (hconjQ _ hfQ) ?_
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
    (hyp.Q.inv_mem hyp.structureConjugator_mem_Q) (one_mem _)
    hyp.structureConjugator_mem_Q ?_
  rw [hyp.structure_equation, mul_one]

/-- `h(r) = 1` (Peterfalvi Part II, Ch. III §2, p. 118), from `t r t = r t s`. -/
lemma tConjTriple_structureConjugator :
    hyp.tConjLeft hyp.structureConjugator = hyp.structureConjugator ∧
      hyp.tConjMiddle hyp.structureConjugator = 1 ∧
      hyp.tConjRight hyp.structureConjugator = hyp.distinguishedInvolution := by
  refine hyp.tConjTriple_eq_of hyp.structureConjugator_mem_Q
    hyp.structureConjugator_ne_one hyp.structureConjugator_mem_Q (one_mem _)
    hyp.distinguishedInvolution_mem_Q ?_
  rw [hyp.t_conj_structureConjugator, mul_one]

/-- `h(r⁻¹) = 1` (Peterfalvi Part II, Ch. III §2, p. 118), from
`t r⁻¹ t = s t r⁻¹`. -/
lemma tConjTriple_structureConjugator_inv :
    hyp.tConjLeft hyp.structureConjugator⁻¹ = hyp.distinguishedInvolution ∧
      hyp.tConjMiddle hyp.structureConjugator⁻¹ = 1 ∧
      hyp.tConjRight hyp.structureConjugator⁻¹ = hyp.structureConjugator⁻¹ := by
  refine hyp.tConjTriple_eq_of (hyp.Q.inv_mem hyp.structureConjugator_mem_Q)
    (inv_ne_one.mpr hyp.structureConjugator_ne_one)
    hyp.distinguishedInvolution_mem_Q (one_mem _)
    (hyp.Q.inv_mem hyp.structureConjugator_mem_Q) ?_
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

/-! ## The elements `r r^{-k}` and their middle factor -/

/-- For `k ∈ K`, the element `r r^{-k} = r · k⁻¹ r⁻¹ k` lies in `Q`. -/
lemma structureConjugator_mul_conj_inv_mem {k : G} (hk : k ∈ hyp.KSet) :
    hyp.structureConjugator * (k⁻¹ * hyp.structureConjugator⁻¹ * k) ∈ hyp.Q := by
  have hkH : k ∈ hyp.H := hyp.D_le_H (hyp.mem_D_of_mem_KSet hk)
  refine hyp.Q.mul_mem hyp.structureConjugator_mem_Q ?_
  have := hyp.Q_normal_in_H k⁻¹ (hyp.H.inv_mem hkH) _
    (hyp.Q.inv_mem hyp.structureConjugator_mem_Q)
  rwa [inv_inv] at this

/-- For `1 ≠ k ∈ K`, the element `r r^{-k}` is non-trivial: `r r^{-k} = 1` says
exactly that `k` centralizes `r`, and `C_Q(k) = 1` (Ch. I §2 Prop 1(a)). -/
lemma structureConjugator_mul_conj_inv_ne_one {k : G} (hk : k ∈ hyp.KSet)
    (hk1 : k ≠ 1) :
    hyp.structureConjugator * (k⁻¹ * hyp.structureConjugator⁻¹ * k) ≠ 1 := by
  intro h
  refine hyp.structureConjugator_ne_one ?_
  have hcomm : hyp.structureConjugator * k = k * hyp.structureConjugator := by
    have h1 : k⁻¹ * hyp.structureConjugator⁻¹ * k = hyp.structureConjugator⁻¹ := by
      have := congrArg (fun z : G => hyp.structureConjugator⁻¹ * z) h
      simpa [mul_assoc] using this
    have h2 : k⁻¹ * hyp.structureConjugator * k = hyp.structureConjugator := by
      have := congrArg (fun z : G => z⁻¹) h1
      simpa [mul_assoc] using this
    calc hyp.structureConjugator * k
        = (k * (k⁻¹ * hyp.structureConjugator * k)) * k⁻¹ * k := by group
      _ = k * hyp.structureConjugator := by rw [h2]; group
  have hmem : hyp.structureConjugator ∈
      hyp.Q ⊓ Subgroup.centralizer ({k} : Set G) :=
    ⟨hyp.structureConjugator_mem_Q,
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet hk hk1, Subgroup.mem_bot] at hmem
  exact hmem

/-- **The element `ℓ`** (Peterfalvi Part II, Ch. III §2, p. 118): for `1 ≠ k ∈ K`
the product `s k s k⁻¹` is an involution of `H` — both `s` and `k s k⁻¹` lie in
the elementary abelian `Q₀` — so by Ch. I §1 Proposition 3 it equals
`s^ℓ = ℓ⁻¹ s ℓ` for some `1 ≠ ℓ ∈ K`. -/
theorem exists_mem_KSet_conj_distinguishedInvolution {k : G} (hk : k ∈ hyp.KSet)
    (hk1 : k ≠ 1) :
    ∃ l ∈ hyp.KSet, l ≠ 1 ∧
      hyp.distinguishedInvolution * k * hyp.distinguishedInvolution * k⁻¹
        = l⁻¹ * hyp.distinguishedInvolution * l := by
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 :=
    hyp.distinguishedInvolution_mem_Q0
  have hkD : k ∈ hyp.D := hyp.mem_D_of_mem_KSet hk
  have hkH : k ∈ hyp.H := hyp.D_le_H hkD
  have hcQ0 : k * hyp.distinguishedInvolution * k⁻¹ ∈ hyp.Q0 := by
    refine ⟨?_, hyp.H.mul_mem (hyp.H.mul_mem hkH hsQ0.2) (hyp.H.inv_mem hkH)⟩
    calc (k * hyp.distinguishedInvolution * k⁻¹) ^ 2
        = k * hyp.distinguishedInvolution ^ 2 * k⁻¹ := conj_pow
      _ = 1 := by rw [hyp.distinguishedInvolution_sq, mul_one, mul_inv_cancel]
  have hbQ0 : hyp.distinguishedInvolution * (k * hyp.distinguishedInvolution * k⁻¹)
      ∈ hyp.Q0 := hyp.Q0.mul_mem hsQ0 hcQ0
  have hsinv : hyp.distinguishedInvolution⁻¹ = hyp.distinguishedInvolution := by
    have h2 := hyp.distinguishedInvolution_sq
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_left h2
  -- `s` is not centralized by `k`
  have hnc : k * hyp.distinguishedInvolution * k⁻¹ ≠ hyp.distinguishedInvolution := by
    intro h
    refine hyp.distinguishedInvolution_ne_one ?_
    have hmem : hyp.distinguishedInvolution ∈
        hyp.Q ⊓ Subgroup.centralizer ({k} : Set G) := by
      refine ⟨hyp.distinguishedInvolution_mem_Q,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc hyp.distinguishedInvolution * k
          = (k * hyp.distinguishedInvolution * k⁻¹) * k := by rw [h]
        _ = k * hyp.distinguishedInvolution := by group
    rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet hk hk1, Subgroup.mem_bot] at hmem
    exact hmem
  have hb1 : hyp.distinguishedInvolution * (k * hyp.distinguishedInvolution * k⁻¹)
      ≠ 1 := by
    intro h
    refine hnc ?_
    have h2 : hyp.distinguishedInvolution⁻¹
        = k * hyp.distinguishedInvolution * k⁻¹ := inv_eq_of_mul_eq_one_right h
    rw [← h2, hsinv]
  have himg := hyp.image_conj_KSet_eq_involutions_H
    hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
    hyp.distinguishedInvolution_ne_one
  have hmem : hyp.distinguishedInvolution * (k * hyp.distinguishedInvolution * k⁻¹)
      ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} :=
    ⟨hbQ0.1, hb1, hbQ0.2⟩
  rw [← himg] at hmem
  obtain ⟨l, hl, hleq0⟩ := hmem
  have hleq : l⁻¹ * hyp.distinguishedInvolution * l
      = hyp.distinguishedInvolution * (k * hyp.distinguishedInvolution * k⁻¹) :=
    hleq0
  refine ⟨l, hl, ?_, ?_⟩
  · intro h1
    rw [h1, inv_one, one_mul, mul_one] at hleq
    refine hyp.distinguishedInvolution_ne_one ?_
    have hks : k * hyp.distinguishedInvolution * k⁻¹ = 1 := by
      refine mul_left_cancel (a := hyp.distinguishedInvolution) ?_
      rw [mul_one, ← hleq]
    calc hyp.distinguishedInvolution
        = k⁻¹ * (k * hyp.distinguishedInvolution * k⁻¹) * k := by group
      _ = 1 := by rw [hks]; group
  · rw [show hyp.distinguishedInvolution * k * hyp.distinguishedInvolution * k⁻¹
      = hyp.distinguishedInvolution * (k * hyp.distinguishedInvolution * k⁻¹) by group,
      ← hleq]

/-- **`h(r r^{-k}) = ℓ² k² ∈ K`** (Peterfalvi Part II, Ch. III §2, p. 118,
identity (4)): the middle factor of the canonical decomposition of
`t r r^{-k} t` lies in `K`. -/
theorem exists_tConjMiddle_eq {k : G} (hk : k ∈ hyp.KSet) (hk1 : k ≠ 1) :
    ∃ l ∈ hyp.KSet,
      hyp.tConjMiddle
          (hyp.structureConjugator * (k⁻¹ * hyp.structureConjugator⁻¹ * k))
        = l ^ 2 * k ^ 2 := by
  obtain ⟨l, hl, -, hskl⟩ := hyp.exists_mem_KSet_conj_distinguishedInvolution hk hk1
  refine ⟨l, hl, ?_⟩
  have hkD : k ∈ hyp.D := hyp.mem_D_of_mem_KSet hk
  have hlD : l ∈ hyp.D := hyp.mem_D_of_mem_KSet hl
  have hkH : k ∈ hyp.H := hyp.D_le_H hkD
  have hlH : l ∈ hyp.H := hyp.D_le_H hlD
  have hrQ : hyp.structureConjugator ∈ hyp.Q := hyp.structureConjugator_mem_Q
  have hrQi : hyp.structureConjugator⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hrQ
  have hk2H : k ^ 2 ∈ hyp.H := hyp.H.pow_mem hkH 2
  have hgQ : hyp.structureConjugator *
      (l * hyp.structureConjugator⁻¹ * l⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem hrQ (hyp.Q_normal_in_H l hlH _ hrQi)
  have hdD : l ^ 2 * k ^ 2 ∈ hyp.D :=
    hyp.D.mul_mem (hyp.D.pow_mem hlD 2) (hyp.D.pow_mem hkD 2)
  have hfQ : (k ^ 2 * (l * hyp.structureConjugator * l⁻¹) * (k ^ 2)⁻¹) *
      (k * hyp.structureConjugator⁻¹ * k⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem (hyp.Q_normal_in_H (k ^ 2) hk2H _ (hyp.Q_normal_in_H l hlH _ hrQ))
      (hyp.Q_normal_in_H k hkH _ hrQi)
  exact (hyp.tConjTriple_eq_of (hyp.structureConjugator_mul_conj_inv_mem hk)
    (hyp.structureConjugator_mul_conj_inv_ne_one hk hk1) hgQ hdD hfQ
    (hyp.t_conj_structureConjugator_mul_conj_inv hk hl hskl)).2.1

/-! ## `h(x) ∈ K` on the book's system of representatives

Peterfalvi Part II, Ch. III §2, p. 118: `h(s) = h(r) = h(r⁻¹) = 1` and
`h(r r^{-k}) = ℓ²k² ∈ K`, and by the equivariance (1) the property `h(x) ∈ K`
passes along `K`-orbits. -/

/-- **`h(x) ∈ K` passes along `K`-orbits** (Peterfalvi Part II, Ch. III §2,
p. 118, identity (1)): `h(xᵃ) = a h(x) a`. -/
lemma tConjMiddle_conj_mem_K {y a : G} (hy : y ∈ hyp.Q) (hy1 : y ≠ 1)
    (ha : a ∈ hyp.K) (hmem : hyp.tConjMiddle y ∈ hyp.K) :
    hyp.tConjMiddle (a⁻¹ * y * a) ∈ hyp.K := by
  have haK : a ∈ hyp.KSet := by rw [← hyp.coe_K]; exact ha
  rw [(hyp.tConjTriple_conj hy hy1 haK).2.1]
  exact hyp.K.mul_mem (hyp.K.mul_mem ha hmem) ha

lemma tConjMiddle_distinguishedInvolution_mem_K :
    hyp.tConjMiddle hyp.distinguishedInvolution ∈ hyp.K := by
  rw [hyp.tConjTriple_distinguishedInvolution.2.1]
  exact hyp.K.one_mem

lemma tConjMiddle_structureConjugator_mem_K :
    hyp.tConjMiddle hyp.structureConjugator ∈ hyp.K := by
  rw [hyp.tConjTriple_structureConjugator.2.1]
  exact hyp.K.one_mem

lemma tConjMiddle_structureConjugator_inv_mem_K :
    hyp.tConjMiddle hyp.structureConjugator⁻¹ ∈ hyp.K := by
  rw [hyp.tConjTriple_structureConjugator_inv.2.1]
  exact hyp.K.one_mem

/-- **`h(r r^{-k}) ∈ K`** (Peterfalvi Part II, Ch. III §2, p. 118, identity (4)). -/
theorem tConjMiddle_structureConjugator_mul_conj_inv_mem_K {k : G} (hk : k ∈ hyp.K)
    (hk1 : k ≠ 1) :
    hyp.tConjMiddle
        (hyp.structureConjugator * (k⁻¹ * hyp.structureConjugator⁻¹ * k)) ∈ hyp.K := by
  have hkK : k ∈ hyp.KSet := by rw [← hyp.coe_K]; exact hk
  obtain ⟨l, hl, hval⟩ := hyp.exists_tConjMiddle_eq hkK hk1
  have hlK : l ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hl
  rw [hval]
  exact hyp.K.mul_mem (hyp.K.pow_mem hlK 2) (hyp.K.pow_mem hk 2)

/-- **The book's system of representatives** for the `K`-orbits of `S#`
(Peterfalvi Part II, Ch. III §2, p. 118): `s`, `r`, `r⁻¹` and the `q − 2`
elements `r r^{-k}` for `1 ≠ k ∈ K`. -/
def orbitReprSet : Set G :=
  {hyp.distinguishedInvolution, hyp.structureConjugator, hyp.structureConjugator⁻¹} ∪
    {x | ∃ k ∈ hyp.K, k ≠ 1 ∧
      x = hyp.structureConjugator * (k⁻¹ * hyp.structureConjugator⁻¹ * k)}

lemma orbitReprSet_subset_Q : hyp.orbitReprSet ⊆ (hyp.Q : Set G) := by
  rintro x (hx | ⟨k, hk, -, rfl⟩)
  · rcases hx with rfl | rfl | rfl
    · exact hyp.distinguishedInvolution_mem_Q
    · exact hyp.structureConjugator_mem_Q
    · exact hyp.Q.inv_mem hyp.structureConjugator_mem_Q
  · exact hyp.structureConjugator_mul_conj_inv_mem
      (by rw [← hyp.coe_K]; exact hk)

lemma one_notMem_orbitReprSet : (1 : G) ∉ hyp.orbitReprSet := by
  rintro (hx | ⟨k, hk, hk1, hx⟩)
  · rcases hx with h | h | h
    · exact hyp.distinguishedInvolution_ne_one h.symm
    · exact hyp.structureConjugator_ne_one h.symm
    · exact hyp.structureConjugator_ne_one (inv_eq_one.mp h.symm)
  · exact hyp.structureConjugator_mul_conj_inv_ne_one
      (by rw [← hyp.coe_K]; exact hk) hk1 hx.symm

/-- `h(y) ∈ K` at every representative. -/
theorem tConjMiddle_mem_K_of_mem_orbitReprSet {y : G} (hy : y ∈ hyp.orbitReprSet) :
    hyp.tConjMiddle y ∈ hyp.K := by
  rcases hy with hy | ⟨k, hk, hk1, rfl⟩
  · rcases hy with rfl | rfl | rfl
    · exact hyp.tConjMiddle_distinguishedInvolution_mem_K
    · exact hyp.tConjMiddle_structureConjugator_mem_K
    · exact hyp.tConjMiddle_structureConjugator_inv_mem_K
  · exact hyp.tConjMiddle_structureConjugator_mul_conj_inv_mem_K hk hk1

/-- **`h(x) ∈ K` for every `x ∈ Q ∖ {1}`** (Peterfalvi Part II, Ch. III §2,
p. 118), granted that `orbitReprSet` meets every `K`-orbit.

This is the whole content of the Proposition of §2: `t x t = g(x) h(x) t f(x)`
with `h(x) ∈ K` says `t S t ⊆ S K t S`. -/
theorem tConjMiddle_mem_K_of_orbitReprSet_covers
    (hcover : ∀ x ∈ hyp.Q, x ≠ 1 →
      ∃ a ∈ hyp.K, ∃ y ∈ hyp.orbitReprSet, x = a⁻¹ * y * a)
    {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    hyp.tConjMiddle x ∈ hyp.K := by
  obtain ⟨a, ha, y, hy, rfl⟩ := hcover x hx hx1
  have hyQ : y ∈ hyp.Q := hyp.orbitReprSet_subset_Q hy
  have hy1 : y ≠ 1 := fun h => hyp.one_notMem_orbitReprSet (h ▸ hy)
  exact hyp.tConjMiddle_conj_mem_K hyQ hy1 ha
    (hyp.tConjMiddle_mem_K_of_mem_orbitReprSet hy)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
