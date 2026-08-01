/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RankOneBNPairRigidity
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.Simplicity
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourCorollaryTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.RankOneSetup

/-!
# Ch. IV §4, step (2): the *intrinsic* standing hypothesis on `U/Z(U)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, step (2), p. 133.

`PSU3SectionFourModel` puts a standing hypothesis on `U/Z(U)` by *transporting* the
standard `PSU(3, ℓ)` one along Ch. I §3 Proposition 1(c).  Step (2) needs more than that:
it runs §2 and §3 "relative to `U`", with the mappings `f₁`, `h₁` of `U`, `U ∩ H` and `t`.
Those are the mappings of the rank-one setup `U/Z(U)` inherits from `U`
(`setup_residualQuotient`), so what step (2) really uses is the standing hypothesis whose
`H`, `Q`, `D`, `t` are the *images of the intrinsic subgroups* `U ∩ H`, `U ∩ Q`, `U ∩ D`
and `t`, not whatever the identification happens to produce.

`Hypothesis.ofRankOneSetup` builds exactly that from the setup, given faithfulness, `|Q̄|`
even, `|D̄|` odd and (A3).  This file supplies those four:

* faithfulness is `Setup.normalCore_eq_bot_of_isSimpleGroup`, because `U/Z(U)` is the
  simple group `PSU(3, ℓ)` (Ch. I §3 Lemma 1);
* `|Q̄| = |C_Q(X)|`, because `Z(U) ≤ D` meets `Q` trivially, so the quotient map is
  injective on `U ∩ Q = C_Q(X)`;
* `|D̄|` divides `|D|`, which is odd by (A2);
* (A3) is transported from the standard model — being a statement about the group alone,
  it does not care which identification is used.

The bridge `residualQuotientMulEquiv` is needed throughout because the model's
identification is stated for the residual as a subgroup of `C_G(X)` (`residual`) while the
setup lives on its image in `G` (`residualImage`).

## Main results

* `residualImageMulEquiv`, `residualQuotientMulEquiv` — `U` and `U/Z(U)` read in `G` agree
  with `U` and `U/Z(U)` read in `C_G(X)`.
* `isSimpleGroup_residualQuotient` — `U/Z(U)` is simple.
* `cQMulEquivMapQ`, `natCard_map_Q_residualQuotient` — `Q̄ ≃ C_Q(X)`, so `|Q̄| = |C_Q(X)|`.
* `odd_natCard_map_D_residualQuotient` — `|D̄|` is odd.
* `Hypothesis.intrinsicResidualQuotient` — the standing hypothesis on `U/Z(U)` in the
  intrinsic subgroups, which is what step (2) argues with.
* `natCard_Q0_intrinsicResidualQuotient`, `natCard_Q_intrinsicResidualQuotient`,
  `isSuzuki2Group_Q_intrinsicResidualQuotient` — the numerical and structural inputs of
  Ch. I §3 Lemma 5, for it.
* `intrinsicPointEquiv`, `intrinsicResidualQuotientULift` — the same hypothesis with its
  point set relabelled as the standard `Unital ℓ`, which lifts into `Ω`'s universe, and
  `theoremAInductionBelow_intrinsicResidualQuotient` — the induction hypothesis there.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair
open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {X : Subgroup G}

/-! ### `U` read in `G` versus `U` read in `C_G(X)`

`residual X` is `O^{2′}(C_G(X))` as a subgroup of `C_G(X)`, which is where Ch. I §3
Proposition 1(c) identifies `U/Z(U)`; `residualImage X` is the same group as a subgroup of
`G`, which is where the rank-one setup lives (a `Setup` needs `H`, `Q`, `D` and `t` inside
one group).  The two are isomorphic because `C_G(X).subtype` is injective. -/

/-- **`U` computed in `C_G(X)` and in `G` agree.** -/
noncomputable def residualImageMulEquiv (X : Subgroup G) :
    ↥(residual (G := G) X) ≃* ↥(residualImage (G := G) X) :=
  Subgroup.equivMapOfInjective _ (Subgroup.centralizer (X : Set G)).subtype
    (Subgroup.subtype_injective _)

/-- **`U/Z(U)` computed in `C_G(X)` and in `G` agree.** -/
noncomputable def residualQuotientMulEquiv (X : Subgroup G) :
    (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X)) ≃*
      (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) :=
  OddOrder.GroupTheory.quotientCenterCongr (residualImageMulEquiv (G := G) X)

/-! ### The two parities

`ofRankOneSetup` wants `|Q̄|` even and `|D̄|` odd for the *intrinsic* `Q̄ = π(U ∩ Q)` and
`D̄ = π(U ∩ D)`.  Both come from `U` itself, with no reference to the model: the quotient
map is injective on `U ∩ Q` (its kernel `Z(U)` lies in `D`, and `Q ∩ D = 1`), and `D̄` is a
quotient of a subgroup of `D`. -/

/-- **`U ∩ Q = C_Q(X)`** — one inclusion is `U ≤ C_G(X)`, the other is that a `2`-group
inside the centralizer lies in its `2′`-residual. -/
theorem Q_inf_residualImage_eq (hCQ : IsPGroup 2
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    hyp.Q ⊓ residualImage (G := G) X = hyp.Q ⊓ Subgroup.centralizer (X : Set G) :=
  le_antisymm (inf_le_inf_left _ (Subgroup.map_subtype_le _))
    (le_inf inf_le_left (hyp.inf_centralizer_le_residual hCQ))

/-- The quotient map is injective on `U ∩ Q`: its kernel is `Z(U)`, which lies in `D` by
hypothesis, and `Q ∩ D = 1` in a rank-one setup. -/
theorem Q_subgroupOf_inf_center_eq_bot (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    hyp.Q.subgroupOf (residualImage (G := G) X)
      ⊓ Subgroup.center ↥(residualImage (G := G) X) = ⊥ :=
  le_bot_iff.mp ((inf_le_inf_left _ hZD).trans_eq
    (hyp.rankOneSetup_residual hXD htX hCQ).Q_inf_D_eq_bot)

/-- **`Q̄ ≃ C_Q(X)`** — `π` is injective on `U ∩ Q` and `U ∩ Q = C_Q(X)`, so the two
descriptions of the root group of `U/Z(U)` agree.  This is what carries the facts Ch. I §3
Proposition 1(c) proves about `C_Q(X)` — its order and its being a Suzuki `2`-group — over
to the intrinsic standing hypothesis. -/
noncomputable def cQMulEquivMapQ (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
      ≃* ↥((hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)))) :=
  ((OddOrder.GroupTheory.subgroupOfMulEquivInf hyp.Q
        (Subgroup.centralizer (X : Set G))).trans
      (MulEquiv.subgroupCongr (hyp.Q_inf_residualImage_eq hCQ).symm)).trans
    ((OddOrder.GroupTheory.subgroupOfMulEquivInf hyp.Q (residualImage (G := G) X)).symm.trans
      (OddOrder.GroupTheory.mapMk'MulEquiv (hyp.Q_subgroupOf_inf_center_eq_bot hXD htX hCQ hZD)))

/-- **`|Q̄| = |C_Q(X)|`**, which is the form §2 and §3 want (`|Q̄| = ℓ³`). -/
theorem natCard_map_Q_residualQuotient (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Nat.card ↥((hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      = Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) :=
  (Nat.card_congr (hyp.cQMulEquivMapQ hXD htX hCQ hZD).toEquiv).symm

/-- **`|D̄|` is odd** — `D̄` is a quotient of `U ∩ D ≤ D`, and `|D|` is odd by (A2). -/
theorem odd_natCard_map_D_residualQuotient :
    Odd (Nat.card ↥((hyp.D.subgroupOf (residualImage (G := G) X)).map
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))) := by
  have hdvd₁ : Nat.card ↥((hyp.D.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ∣ Nat.card ↥(hyp.D.subgroupOf (residualImage (G := G) X)) :=
    Subgroup.card_dvd_of_surjective _
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' _) _)
  have hdvd₂ : Nat.card ↥(hyp.D.subgroupOf (residualImage (G := G) X))
      ∣ Nat.card ↥hyp.D := by
    rw [OddOrder.GroupTheory.natCard_subgroupOf]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Odd.of_dvd_nat hyp.D_odd (hdvd₁.trans hdvd₂)

/-- `|U/Z(U)| < |G|`, read in `G` — the bound the induction hypothesis restricts along. -/
theorem natCard_residualImageQuotient_lt (hXV : X ≤ hyp.V) (hX : X ≠ ⊥) :
    Nat.card (↥(residualImage (G := G) X) ⧸
      Subgroup.center ↥(residualImage (G := G) X)) < Nat.card G := by
  rw [← Nat.card_congr (residualQuotientMulEquiv (G := G) X).toEquiv]
  exact hyp.natCard_residualQuotient_lt hXV hX

section Model

variable [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Ω)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Ω)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Ω)) result.L}

/-- **`U/Z(U) ≃ PSU(3, ℓ)`, read in `G`** — Ch. I §3 Proposition 1(c) states the
identification for the residual inside `C_G(X)`; this moves it to the residual's image in
`G`, where the rank-one setup of step (2) lives. -/
noncomputable def residualQuotientImageEquiv (details : CentralizerPSUData hyp X result data) :
    (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) ≃*
      standardPermGroup data.n :=
  (residualQuotientMulEquiv (G := G) X).symm.trans details.residualQuotientEquiv

/-- **`U/Z(U)` is simple** (Peterfalvi Part II, Ch. I §3, Lemma 1, via Proposition 1(c)).

This is the faithfulness input of `Hypothesis.ofRankOneSetup`: a proper subgroup of a
simple group has trivial normal core, and `M̄ = π(U ∩ H)` is proper because `t̄ ∉ M̄`. -/
theorem isSimpleGroup_residualQuotient (details : CentralizerPSUData hyp X result data) :
    IsSimpleGroup (↥(residualImage (G := G) X) ⧸
      Subgroup.center ↥(residualImage (G := G) X)) :=
  letI := standardPermGroup_isSimpleGroup data.one_lt_n
  (hyp.residualQuotientImageEquiv details).isSimpleGroup

/-- **(A3) holds on `U/Z(U)`** — the standard model has `2`-rank at least two and that is
a property of the group alone, so any identification transports it. -/
theorem two_rank_ge_two_residualQuotient (details : CentralizerPSUData hyp X result data) :
    ∃ E : Subgroup (↥(residualImage (G := G) X) ⧸
        Subgroup.center ↥(residualImage (G := G) X)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  obtain ⟨E, hcard, hsq⟩ := (standardHypothesis data.n data.one_lt_n).two_rank_ge_two
  set e := (hyp.residualQuotientImageEquiv details).symm
  refine ⟨E.map (e : _ →* _), ?_, ?_⟩
  · rw [← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E _ e.injective).toEquiv).symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hsq x hx, map_one]

/-- **`|Q̄|` is even** — it equals `|C_Q(X)| = ℓ³` by `natCard_map_Q_residualQuotient`, and
`ℓ = 2ⁿ` with `n ≥ 2`. -/
theorem even_natCard_map_Q_residualQuotient (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Even (Nat.card ↥((hyp.Q.subgroupOf (residualImage (G := G) X)).map
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))) := by
  have hn := data.one_lt_n
  rw [hyp.natCard_map_Q_residualQuotient hXD htX hCQ hZD,
    details.natCard_cQ_eq_baseField_cube, natCard_baseField data.n (by omega)]
  obtain ⟨k, hk⟩ :=
    (dvd_pow_self (2 : ℕ) (by omega : data.n ≠ 0)).trans
      (dvd_pow_self ((2 : ℕ) ^ data.n) (by norm_num : (3 : ℕ) ≠ 0))
  exact ⟨k, by omega⟩

/-- **The standing hypothesis on `U/Z(U)`, in the intrinsic subgroups** (Peterfalvi
Part II, Ch. IV §4, step (2), p. 133).

This is what step (2) argues with: `H`, `Q`, `D` and `t` are the images of `U ∩ H`,
`U ∩ Q`, `U ∩ D` and `t`, so the mappings `Setup.exists_fgh` produces for it are the
book's `f₁` and `h₁` "relative to `U`, `U ∩ H` and `t`", and §2 and §3 applied to it are
§2 and §3 "relative to `U`".

`residualQuotientHypothesis` also puts a standing hypothesis on this group, but by
transporting the standard model's, so its `H`, `Q`, `D` are whatever the identification
produces; the two agree on everything that only depends on the group (`|Q̄|` and the
simplicity used here), which is why the numerical inputs of §2 and §3 can be quoted from
either. -/
noncomputable def intrinsicResidualQuotient (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Hypothesis (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))
      ((↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) ⧸
        (hyp.H.subgroupOf (residualImage (G := G) X)).map
          (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)))) :=
  letI := hyp.isSimpleGroup_residualQuotient details
  Hypothesis.ofRankOneSetup (hyp.setup_residualQuotient hXD htX hCQ hZD)
    (hyp.setup_residualQuotient hXD htX hCQ hZD).normalCore_eq_bot_of_isSimpleGroup
    (hyp.even_natCard_map_Q_residualQuotient details hXD htX hCQ hZD)
    hyp.odd_natCard_map_D_residualQuotient
    (hyp.two_rank_ge_two_residualQuotient details)

/-! ### The numerical inputs of §2 and §3, intrinsically

`exists_standardModel` takes `|Q̄₀| = ℓ` and `|Q̄| = |Q̄₀|³`.  For the intrinsic hypothesis
those are statements about `π(U ∩ Q₀)` and `π(U ∩ Q)`, and both reduce to `C_{Q₀}(X)` and
`C_Q(X)` for the same reason: `Z(U)` lies in `D`, which meets `Q ⊇ Q₀` trivially. -/

@[simp] theorem intrinsicResidualQuotient_H (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).H
      = (hyp.H.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) := rfl

@[simp] theorem intrinsicResidualQuotient_Q (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q
      = (hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) := rfl

/-- **`|Z(U)|` is odd, read in `G`** — Ch. I §3 Proposition 1(c) proves it for the residual
inside `C_G(X)` (`odd_natCard_center_residual`), and the two centres correspond. -/
theorem odd_natCard_center_residualImage (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data) :
    Odd (Nat.card ↥(Subgroup.center ↥(residualImage (G := G) X))) := by
  have hcard : Nat.card ↥(Subgroup.center ↥(residualImage (G := G) X))
      = Nat.card ↥(Subgroup.center ↥(residual (G := G) X)) := by
    rw [← OddOrder.GroupTheory.map_center_mulEquiv (residualImageMulEquiv (G := G) X)]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (residualImageMulEquiv (G := G) X).injective).toEquiv).symm
  have hnd := details.odd_natCard_center_residual hXV common
  rw [hcard]
  rcases Nat.even_or_odd (Nat.card ↥(Subgroup.center ↥(residual (G := G) X))) with he | ho
  · obtain ⟨r, hr⟩ := he
    have h2 : (2 : ℕ) ∣ Nat.card ↥(Subgroup.center ↥(residual (G := G) X)) := ⟨r, by omega⟩
    exact absurd h2 hnd
  · exact ho

/-- **`Q̄₀ = π(U ∩ Q₀)`** — the involutions of `M̄` are exactly the images of the
involutions of `U ∩ H`.

One direction is trivial.  For the other, `x̄² = 1` only says `x² ∈ Z(U)`; the lift is
`x^{|Z(U)|}`, which squares to `1` and has the same image because `|Z(U)|` is odd
(`sq_pow_natCard_eq_one_of_sq_mem`). -/
theorem Q0_intrinsicResidualQuotient_eq (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0
      = (hyp.Q0.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) := by
  classical
  have hodd := hyp.odd_natCard_center_residualImage hXV common details
  ext y
  rw [Hypothesis.mem_Q0_iff, hyp.intrinsicResidualQuotient_H details hXD htX hCQ hZD]
  constructor
  · rintro ⟨hy2, x, hxH, rfl⟩
    have hxsq : x ^ 2 ∈ Subgroup.center ↥(residualImage (G := G) X) := by
      refine (QuotientGroup.eq_one_iff (x ^ 2)).mp ?_
      rw [← QuotientGroup.mk'_apply, map_pow]
      exact hy2
    obtain ⟨hsq, hdiff⟩ := OddOrder.GroupTheory.sq_pow_natCard_eq_one_of_sq_mem hodd hxsq
    refine ⟨x ^ Nat.card ↥(Subgroup.center ↥(residualImage (G := G) X)), ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · have := congrArg (Subtype.val (p := fun z => z ∈ residualImage (G := G) X)) hsq
        push_cast at this
        exact this
      · exact hyp.H.pow_mem (Subgroup.mem_subgroupOf.mp hxH) _
    · exact (QuotientGroup.eq.mpr hdiff).symm
  · rintro ⟨x, hxQ0, rfl⟩
    have hxG : (x : G) ∈ hyp.Q0 := Subgroup.mem_subgroupOf.mp hxQ0
    have hxsq : (x : ↥(residualImage (G := G) X)) ^ 2 = 1 :=
      Subtype.ext (by push_cast; exact hxG.1)
    refine ⟨?_, ⟨(x : ↥(residualImage (G := G) X)),
      Subgroup.mem_subgroupOf.mpr hxG.2, rfl⟩⟩
    rw [← map_pow, hxsq, map_one]

/-- **`|Q̄₀| = ℓ`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133) — one of the two
numerical inputs of the Proposition of Ch. III §3, in the intrinsic subgroups. -/
theorem natCard_Q0_intrinsicResidualQuotient (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Nat.card ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0 = 2 ^ data.n := by
  have hn := data.one_lt_n
  have hmono : hyp.Q0.subgroupOf (residualImage (G := G) X)
      ≤ hyp.Q.subgroupOf (residualImage (G := G) X) := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hyp.Q0_le_Q (Subgroup.mem_subgroupOf.mp hz))
  have hbot : hyp.Q0.subgroupOf (residualImage (G := G) X)
      ⊓ Subgroup.center ↥(residualImage (G := G) X) = ⊥ :=
    le_bot_iff.mp (((inf_le_inf hmono hZD).trans_eq
      (hyp.rankOneSetup_residual hXD htX hCQ).Q_inf_D_eq_bot))
  have hinf : hyp.Q0 ⊓ residualImage (G := G) X
      = hyp.Q0 ⊓ Subgroup.centralizer (X : Set G) :=
    le_antisymm (inf_le_inf_left _ (Subgroup.map_subtype_le _))
      (le_inf inf_le_left ((inf_le_inf_right _ hyp.Q0_le_Q).trans
        (hyp.inf_centralizer_le_residual hCQ)))
  rw [hyp.Q0_intrinsicResidualQuotient_eq hXV common details hXD htX hCQ hZD,
    OddOrder.GroupTheory.natCard_map_mk'_of_inf_eq_bot hbot,
    OddOrder.GroupTheory.natCard_subgroupOf, hinf,
    ← OddOrder.GroupTheory.natCard_subgroupOf, details.natCard_cQ0_eq_baseField,
    natCard_baseField data.n (by omega)]

/-- **`|Q̄| = |Q̄₀|³`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133) — the other
numerical input of the Proposition of Ch. III §3, in the intrinsic subgroups. -/
theorem natCard_Q_intrinsicResidualQuotient (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Nat.card ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q
      = Nat.card ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0 ^ 3 := by
  have hn := data.one_lt_n
  rw [hyp.natCard_Q0_intrinsicResidualQuotient hXV common details hXD htX hCQ hZD,
    hyp.intrinsicResidualQuotient_Q details hXD htX hCQ hZD,
    hyp.natCard_map_Q_residualQuotient hXD htX hCQ hZD,
    details.natCard_cQ_eq_baseField_cube, natCard_baseField data.n (by omega)]

/-- **`Q̄` is a Suzuki `2`-group** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133) — the
third input of Ch. I §3 Lemma 5, in the intrinsic subgroups.

Ch. I §3 Proposition 1(c) proves it for `C_Q(X)` (`cQ_isSuzuki2Group`), and being a
Suzuki `2`-group is an isomorphism invariant (`IsSuzuki2Group.of_equiv`). -/
theorem isSuzuki2Group_Q_intrinsicResidualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
      ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q := by
  rw [hyp.intrinsicResidualQuotient_Q details hXD htX hCQ hZD]
  exact OddOrder.GroupTheory.SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv
    details.cQ_isSuzuki2Group (hyp.cQMulEquivMapQ hXD htX hCQ hZD)

/-! ### Moving the point set into `Ω`'s universe

The ambient induction hypothesis `TheoremAInductionBelow G Ω` quantifies over permuted
sets in `Ω`'s universe, so a standing hypothesis it can be applied below must have its
permuted set there.  The intrinsic one permutes `L̄ ⧸ M̄`, which lives in `G`'s universe;
but Ch. IV §1's identification `L̄ ⧸ M̄ ≅ Q̄ ∪ {a}` (`coordsEquiv`) together with
`Q̄ ≅ RootGroup ℓ` puts it in bijection with the standard `Unital ℓ`, a small type, which
lifts anywhere.  `ofRankOneSetupOfEquiv` then reads the same hypothesis there. -/

/-- **The point set of the intrinsic action is the standard `Unital ℓ`** — `L̄ ⧸ M̄` is
`Q̄ ∪ {a}` (Ch. IV §1, p. 123) and `Q̄ ≅ C_Q(X) ≅ RootGroup ℓ` (Ch. I §3 Prop 1(c)). -/
noncomputable def intrinsicPointEquiv (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    ((↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) ⧸
        (hyp.H.subgroupOf (residualImage (G := G) X)).map
          (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ≃ Unital data.n :=
  (coordsEquiv (hyp.setup_residualQuotient hXD htX hCQ hZD)).symm.trans
    (Equiv.optionCongr
      ((hyp.cQMulEquivMapQ hXD htX hCQ hZD).symm.trans details.cQEquivRoot).toEquiv)

/-- **The intrinsic standing hypothesis on `U/Z(U)`, permuting `Unital ℓ`** — the same
`H`, `Q`, `D`, `t` as `intrinsicResidualQuotient`, with the point set relabelled so that
it lies in `Ω`'s universe. -/
noncomputable def intrinsicResidualQuotientULift
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := Hypothesis.rankOneSetupAction
      ((hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm)
    Hypothesis (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))
      (ULift.{v} (Unital data.n)) :=
  letI := hyp.isSimpleGroup_residualQuotient details
  Hypothesis.ofRankOneSetupOfEquiv (hyp.setup_residualQuotient hXD htX hCQ hZD)
    ((hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm)
    (hyp.setup_residualQuotient hXD htX hCQ hZD).normalCore_eq_bot_of_isSimpleGroup
    (hyp.even_natCard_map_Q_residualQuotient details hXD htX hCQ hZD)
    hyp.odd_natCard_map_D_residualQuotient
    (hyp.two_rank_ge_two_residualQuotient details)

/-- **The induction hypothesis restricts to `U/Z(U)`** with the intrinsic point set.

`TheoremAInductionBelow` only looks at the order of the group, so this is `ih` composed
with `natCard_residualImageQuotient_lt`; what makes it typecheck at all is that the
permuted set has been moved into `Ω`'s universe. -/
theorem theoremAInductionBelow_intrinsicResidualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    (hXV : X ≤ hyp.V) (hX : X ≠ ⊥) (ih : TheoremAInductionBelow G Ω) :
    letI := Hypothesis.rankOneSetupAction
      ((hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm)
    TheoremAInductionBelow
      (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))
      (ULift.{v} (Unital data.n)) := by
  letI := Hypothesis.rankOneSetupAction
    ((hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm)
  intro A Λ _ _ _ hlt hA
  exact ih (hlt.trans (hyp.natCard_residualImageQuotient_lt hXV hX)) hA

end Model

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
