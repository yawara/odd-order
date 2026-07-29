/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm

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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
