/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm
import OddOrder.Peterfalvi.Appendices.Suzuki.HypothesisTransport
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
* `Hypothesis.ofRankOneSetup` — the converse: a `Setup` whose `M` has trivial normal core
  and whose `Q`, `D` have the right parities is itself a standing hypothesis, on `L ⧸ M`.
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

/-! ### The converse: a rank-one setup *is* the standing hypothesis

`rankOneSetup` reads (A1)–(A3) as a rank-one split BN-pair.  The other direction also
holds, and Ch. IV §4 needs it: a `Setup` supplies the two-transitive action itself
(`Setup.isMultiplyPretransitive_two`, on `L ⧸ M`), so only the conditions that are not
combinatorial — faithfulness and the three numerical ones — have to be added. -/

section OfSetup

open OddOrder.GroupTheory.RankOneBNPair

variable {L : Type*} [Group L] [Finite L] {M Q D : Subgroup L} {t : L}

/-- **A rank-one split BN-pair with the right parities is a standing hypothesis**
(Peterfalvi Part II, Ch. IV §1, p. 122) — the converse of `Hypothesis.rankOneSetup`.

The permuted set is `L ⧸ M`, on which `L` is doubly transitive because `Q` is regular on
the complement of the base point.  What a `Setup` does not see, and what therefore has to
be supplied, is: faithfulness (`M` has trivial normal core), `|Q|` even, `|D|` odd, and
(A3).

Ch. IV §4, step (2) (p. 133) applies it to `U/Z(U)`, whose setup is inherited from `U`
(`setup_residualQuotient`); that is what "running §2 and §3 relative to `U`" means. -/
noncomputable def ofRankOneSetup (hS : Setup M Q D t) (hcore : M.normalCore = ⊥)
    (hQeven : Even (Nat.card Q)) (hDodd : Odd (Nat.card D))
    (hrank : ∃ E : Subgroup L, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    Hypothesis L (L ⧸ M) where
  basept := ((1 : L) : L ⧸ M)
  doubly_transitive := hS.isMultiplyPretransitive_two
  faithful := ⟨by
    intro g₁ g₂ hg
    have hker : g₁ * g₂⁻¹ ∈ (MulAction.toPermHom L (L ⧸ M)).ker := by
      rw [MonoidHom.mem_ker]
      ext a
      change (g₁ * g₂⁻¹) • a = a
      rw [mul_smul, hg (g₂⁻¹ • a), smul_inv_smul]
    rw [← Subgroup.normalCore_eq_ker, hcore, Subgroup.mem_bot] at hker
    exact mul_inv_eq_one.mp hker⟩
  H := M
  Q := Q
  D := D
  H_def := (MulAction.stabilizer_quotient M).symm
  t := t
  t_sq := by rw [sq]; exact hS.invol
  t_ne_one := fun hc => hS.tnotmem (by rw [hc]; exact M.one_mem)
  t_not_mem_H := hS.tnotmem
  D_def := hS.D_eq_inf_map_conj
  Q_le_H := hS.QM
  Q_normal_in_H := by
    intro m hm x hx
    obtain ⟨⟨q, d⟩, hqd, -⟩ := hS.split m hm
    have hdx : (d : L) * x * (d : L)⁻¹ ∈ Q := by
      have h := hS.DQ ((d : L)⁻¹) (D.inv_mem d.2) x hx
      rwa [inv_inv] at h
    have hrw : m * x * m⁻¹ = (q : L) * ((d : L) * x * (d : L)⁻¹) * (q : L)⁻¹ := by
      rw [hqd]; group
    rw [hrw]
    exact Q.mul_mem (Q.mul_mem q.2 hdx) (Q.inv_mem q.2)
  Q_inf_D_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨p₀, -, huniq⟩ := hS.split x (hS.QM hxQ)
    have e₁ := huniq (⟨x, hxQ⟩, ⟨1, D.one_mem⟩) (by simp)
    have e₂ := huniq (⟨1, Q.one_mem⟩, ⟨x, hxD⟩) (by simp)
    rw [Subgroup.mem_bot]
    exact congrArg (Subtype.val (p := fun z => z ∈ Q))
      (congrArg Prod.fst (e₁.trans e₂.symm))
  Q_mul_D_eq_H := by
    ext a
    constructor
    · rintro ⟨q, hq, d, hd, rfl⟩
      exact M.mul_mem (hS.QM hq) (hS.DM hd)
    · intro ha
      obtain ⟨⟨q, d⟩, hqd, -⟩ := hS.split a ha
      exact ⟨(q : L), q.2, (d : L), d.2, hqd.symm⟩
  Q_even := hQeven
  D_odd := hDodd
  two_rank_ge_two := hrank

/-! ### Moving the point set

`ofRankOneSetup` permutes `L ⧸ M`, which lives in `L`'s universe.  Ch. IV §4, step (2)
needs the permuted set in the universe of the *ambient* `Ω`, because that is the universe
`TheoremAInductionBelow G Ω` quantifies over.  There the point set is identified with the
standard `Unital ℓ` of `PSU(3, ℓ)` — a small type, liftable into any universe — so what is
needed is the same hypothesis read along a bijection of point sets. -/

/-- The action of `L` on any set identified with `L ⧸ M`, transported along the
identification. -/
@[reducible] noncomputable def rankOneSetupAction {Λ : Type*} (ε : (L ⧸ M) ≃ Λ) :
    MulAction L Λ :=
  MulAction.compHom Λ
    ((Equiv.permCongrHom ε).toMonoidHom.comp (MulAction.toPermHom L (L ⧸ M)))

/-- **`ofRankOneSetup` on a relabelled point set** — same group, same `H`, `Q`, `D`, `t`,
the permuted set carried along `ε`. -/
noncomputable def ofRankOneSetupOfEquiv {Λ : Type*} (hS : Setup M Q D t) (ε : (L ⧸ M) ≃ Λ)
    (hcore : M.normalCore = ⊥) (hQeven : Even (Nat.card Q)) (hDodd : Odd (Nat.card D))
    (hrank : ∃ E : Subgroup L, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := rankOneSetupAction ε
    Hypothesis L Λ :=
  letI := rankOneSetupAction ε
  (ofRankOneSetup hS hcore hQeven hDodd hrank).ofMulEquiv (MulEquiv.refl L) ε fun a x => by
    change ε (a • x) = ε ((MulAction.toPermHom L (L ⧸ M) a) (ε.symm (ε x)))
    rw [Equiv.symm_apply_apply]
    rfl

section OfEquivFields

variable {Λ : Type*} (hS : Setup M Q D t) (ε : (L ⧸ M) ≃ Λ) (hcore : M.normalCore = ⊥)
  (hQeven : Even (Nat.card Q)) (hDodd : Odd (Nat.card D))
  (hrank : ∃ E : Subgroup L, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)

omit [MulAction G Ω] [Finite G] hyp in
/-- Relabelling the point set does not move `H`. -/
@[simp] theorem ofRankOneSetupOfEquiv_H :
    letI := rankOneSetupAction ε
    (ofRankOneSetupOfEquiv hS ε hcore hQeven hDodd hrank).H = M := by
  ext x
  exact ⟨fun ⟨_, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

omit [MulAction G Ω] [Finite G] hyp in
/-- Relabelling the point set does not move `Q`. -/
@[simp] theorem ofRankOneSetupOfEquiv_Q :
    letI := rankOneSetupAction ε
    (ofRankOneSetupOfEquiv hS ε hcore hQeven hDodd hrank).Q = Q := by
  ext x
  exact ⟨fun ⟨_, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

omit [MulAction G Ω] [Finite G] hyp in
/-- Relabelling the point set does not move `D`. -/
@[simp] theorem ofRankOneSetupOfEquiv_D :
    letI := rankOneSetupAction ε
    (ofRankOneSetupOfEquiv hS ε hcore hQeven hDodd hrank).D = D := by
  ext x
  exact ⟨fun ⟨_, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

omit [MulAction G Ω] [Finite G] hyp in
/-- Relabelling the point set does not move `t`. -/
@[simp] theorem ofRankOneSetupOfEquiv_t :
    letI := rankOneSetupAction ε
    (ofRankOneSetupOfEquiv hS ε hcore hQeven hDodd hrank).t = t := rfl

end OfEquivFields

end OfSetup

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
