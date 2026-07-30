/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm
import OddOrder.GroupTheory.RankOneBNPair

/-!
# Hypotheses (A1)–(A3) give a rank-one split BN-pair

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §1, p. 122:

> Suppose that `L` is a finite group acting doubly transitively on a set `X`, that
> `M` is the stabilizer in `L` of a point of `X`, `t` is an involution in `L − M`
> and `D = M ∩ M^t`.  Assume there is `Q ≤ M` with `M = Q ⋊ D` …

That is verbatim the standing hypothesis `Hypothesis G Ω` of Part II (p. 97), so the
whole of Ch. IV §1 — the mappings `f, g, h`, the identities (H1)–(H6), and the Lemma
that `f` determines `L` — applies to it.  This file supplies the bridge.

The only piece not already an axiom of `Hypothesis` is the unique factorization of
`G − H` as `H t Q`, which is Ch. I §1, Proposition 4 (a)
(`Hypothesis.existsUnique_canonicalForm`).  The two non-membership conditions come for
free: `t ∉ H` is an axiom, and `t x t ∉ H` for `x ∈ Q^#` is `Q ∩ D = 1`, since
`t x t ∈ H` together with `x ∈ H` says exactly `x ∈ D`.

## Main results

* `Hypothesis.rankOneSetup` — `Setup H Q D t`.
* `Hypothesis.exists_fgh` — the mappings `f, g, h` of Ch. IV §1 exist for `G`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp

/-- `M = Q ⋊ D` in the form used by Ch. IV §1: every element of `H` is uniquely a
product `q · d` with `q ∈ Q` and `d ∈ D`. -/
theorem existsUnique_Q_mul_D {a : G} (ha : a ∈ hyp.H) :
    ∃! p : ↥hyp.Q × ↥hyp.D, a = (p.1 : G) * (p.2 : G) := by
  have hmem : a ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
    rw [hyp.Q_mul_D_eq_H]; exact ha
  obtain ⟨q, hq, d, hd, hqd⟩ := hmem
  have hqd' : q * d = a := hqd
  refine ⟨⟨⟨q, hq⟩, ⟨d, hd⟩⟩, hqd'.symm, ?_⟩
  rintro ⟨⟨q', hq'⟩, ⟨d', hd'⟩⟩ heq
  -- `q'⁻¹ q = d' d⁻¹ ∈ Q ⊓ D = 1`
  have hz : q'⁻¹ * q ∈ hyp.Q ⊓ hyp.D := by
    refine ⟨hyp.Q.mul_mem (hyp.Q.inv_mem hq') hq, ?_⟩
    have e : q'⁻¹ * q = d' * d⁻¹ := by
      have h1 : q' * d' = q * d := by rw [← heq, hqd']
      calc q'⁻¹ * q = q'⁻¹ * (q * d) * d⁻¹ := by group
        _ = q'⁻¹ * (q' * d') * d⁻¹ := by rw [h1]
        _ = d' * d⁻¹ := by group
    rw [e]
    exact hyp.D.mul_mem hd' (hyp.D.inv_mem hd)
  rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hz
  have hqq : q' = q := inv_mul_eq_one.mp hz
  subst hqq
  have hdd : d' = d := by
    have h1 : q' * d' = q' * d := by rw [← heq, hqd']
    exact mul_left_cancel h1
  subst hdd
  rfl

/-- **Hypotheses (A1)–(A3) give a rank-one split BN-pair** in the sense of Ch. IV §1
(Peterfalvi Part II, p. 122), so every result of that section applies to `G`. -/
theorem rankOneSetup : OddOrder.GroupTheory.RankOneBNPair.Setup hyp.H hyp.Q hyp.D hyp.t where
  QM := hyp.Q_le_H
  DM := hyp.D_le_H
  invol := by rw [← sq]; exact hyp.t_sq
  Dstab := by
    intro d hd
    have := hyp.t_conj_mem_D hd
    rwa [hyp.t_inv_eq] at this
  DQ := by
    intro d hd q hq
    have := hyp.Q_normal_in_H d⁻¹ (hyp.H.inv_mem (hyp.D_le_H hd)) q hq
    rwa [inv_inv] at this
  split := fun _ ha => hyp.existsUnique_Q_mul_D ha
  fact := by
    intro y hy
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, huniq⟩ := hyp.existsUnique_canonicalForm hy
    refine ⟨⟨⟨p.1, hp1⟩, ⟨p.2, hp2⟩⟩, hp3, ?_⟩
    rintro ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ heq
    have hpair := huniq (x, z) ⟨hx, hz, heq⟩
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
      (Subtype.ext (congrArg Prod.snd hpair))
  tnotmem := hyp.t_not_mem_H
  tconj := by
    intro x hxQ hx1 hc
    refine hx1 ?_
    have hxD : x ∈ hyp.D := by
      rw [hyp.mem_D_iff, hyp.t_inv_eq]
      exact ⟨hyp.Q_le_H hxQ, hc⟩
    have hbot : x ∈ hyp.Q ⊓ hyp.D := ⟨hxQ, hxD⟩
    rwa [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot

/-- **The mappings `f`, `g`, `h` of Ch. IV §1 exist for `G`** (Peterfalvi Part II,
p. 122): for `x ∈ Q^#`, `t x t = g(x) h(x) t f(x)` with `f x, g x ∈ Q` and `h x ∈ D`.

Every identity of Ch. IV §1 — (H1)–(H6), and the Lemma that `f` determines `L` — is
now available for `G` through `Hypothesis.rankOneSetup`. -/
theorem exists_fgh :
    ∃ f g h : G → G,
      OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g h :=
  hyp.rankOneSetup.exists_fgh

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
