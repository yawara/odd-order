/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelAction
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3CorollaryTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourModel

/-!
# Ch. IV §4, step (2): the Proposition of Ch. III §3 on `U/Z(U)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, step (2), p. 133.

Step (2) runs §2 and §3 "relative to `U`", that is on the quotient `U/Z(U)` that
Ch. I §3 Proposition 1(c) identifies with the standard `PSU(3, ℓ)`.  The standing
hypothesis there is `residualQuotientHypothesis`, and every numerical input the
Proposition of Ch. III §3 takes — `|s t| = 3`, `n ≠ 0`, `|Q̄₀| = 2ⁿ`, `|Q̄| = |Q̄₀|³`
and the induction hypothesis — is already available for it.

So the Proposition itself is available, and this file says so: the caller obtains the
model on `U/Z(U)` and feeds it to `corollaryTwo_of_sectionThree`.

Step (2) also takes `f` and `h` "relative to `U`, `U ∩ H` and `t`", which presupposes
that `U` is itself a rank-one setup.  It is, for the same reason throughout: conjugation
by `P` fixes both decompositions of Ch. I, so their factors stay in `C_G(P)`, and the
`Q`-factor then lies in `C_Q(P) ≤ U` — from which the other factor follows by division
(`Setup.restrict`).

## Main results

* `Hypothesis.canonicalForm_mem_centralizer`, `Hypothesis.splitQD_mem_centralizer` —
  both decompositions of Ch. I keep their factors inside `C_G(X)`.
* `Hypothesis.fgh_mem_centralizer` — `f`, `g`, `h` map `C_Q(X)^#` into `C_Q(X)`,
  `C_Q(X)`, `C_D(X)`.
* `Hypothesis.rankOneSetup_subgroup` — a subgroup of `C_G(X)` containing `t` and
  `C_Q(X)` inherits the rank-one setup.
* `Hypothesis.rankOneSetup_residual` — in particular `U = O^{2′}(C_G(X))` does, which is
  what the book's `f₁`, `h₁` are the mappings of.
* `Hypothesis.setup_residualQuotient` — and so does `U/Z(U)`, where step (2) argues.
* `Hypothesis.exists_mem_K_conj_t_eq` — conjugating `t` by `K` realizes every `K`-translate
  of `t`, which is how step (2) matches the two distinguished involutions.
* `Hypothesis.isStandardModel_residualQuotient` — the Proposition of Ch. III §3 holds
  on `U/Z(U)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
open scoped Pointwise

section Centralizer

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G} {X : Subgroup G}

/-- **The book's `U`**: the residual `O^{2′}(C_G(X))`, as a subgroup of `G` rather than
of the centralizer. -/
abbrev residualImage (X : Subgroup G) : Subgroup G :=
  (Subgroup.primeComplementResidual 2
    (Subgroup.centralizer (X : Set G))).map (Subgroup.centralizer (X : Set G)).subtype

omit [MulAction G Ω] [Finite G] in
/-- An element fixed by conjugation by every member of `X` centralizes `X`. -/
theorem mem_centralizer_of_conj_eq {y : G} (hy : ∀ p ∈ X, p * y * p⁻¹ = y) :
    y ∈ Subgroup.centralizer (X : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
  calc p * y = (p * y * p⁻¹) * p := by group
    _ = y * p := by rw [hy p hp]

/-- **The canonical form of an element of `C_G(X)` has both factors in `C_G(X)`**
(Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

If `X ≤ D` centralizes `t`, conjugation by `p ∈ X` fixes `y` and carries its canonical
factorization `y = x t q` to another one — the factors stay where they belong because
`p ∈ H` and `Q ⊴ H`.  Uniqueness (Ch. I Prop 4(a)) therefore fixes `x` and `q`. -/
theorem canonicalForm_mem_centralizer (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    {y : G} (hyX : y ∈ Subgroup.centralizer (X : Set G))
    {x q : G} (hxH : x ∈ hyp.H) (hqQ : q ∈ hyp.Q) (hy : y = x * hyp.t * q) :
    x ∈ Subgroup.centralizer (X : Set G) ∧ q ∈ Subgroup.centralizer (X : Set G) := by
  have hkey : ∀ p ∈ X, p * x * p⁻¹ = x ∧ p * q * p⁻¹ = q := by
    intro p hp
    have hpH : p ∈ hyp.H := hyp.D_le_H (hXD hp)
    have hpt : p * hyp.t * p⁻¹ = hyp.t := by
      rw [Subgroup.mem_centralizer_iff.mp htX p hp]; group
    have hpy : p * y * p⁻¹ = y := by
      rw [Subgroup.mem_centralizer_iff.mp hyX p hp]; group
    have heq : p * x * p⁻¹ * hyp.t * (p * q * p⁻¹) = x * hyp.t * q := by
      calc p * x * p⁻¹ * hyp.t * (p * q * p⁻¹)
          = p * x * p⁻¹ * (p * hyp.t * p⁻¹) * (p * q * p⁻¹) := by rw [hpt]
        _ = p * (x * hyp.t * q) * p⁻¹ := by group
        _ = p * y * p⁻¹ := by rw [hy]
        _ = y := hpy
        _ = x * hyp.t * q := hy
    exact hyp.canonicalForm_unique
      (hyp.H.mul_mem (hyp.H.mul_mem hpH hxH) (hyp.H.inv_mem hpH))
      (hyp.Q_normal_in_H p hpH q hqQ) hxH hqQ heq
  exact ⟨mem_centralizer_of_conj_eq (X := X) fun p hp => (hkey p hp).1,
    mem_centralizer_of_conj_eq (X := X) fun p hp => (hkey p hp).2⟩

/-- **The `Q D`-decomposition of an element of `C_H(X)` has both factors in `C_G(X)`**
(Peterfalvi Part II, Ch. I Prop 6(a), p. 102, read through uniqueness).

`cQ_mul_cD_eq_cH` writes the element as a product from `C_Q(X)` and `C_D(X)`; the
`Q D`-decomposition being unique, that product *is* the given one. -/
theorem splitQD_mem_centralizer (hXD : X ≤ hyp.D)
    {a : G} (haH : a ∈ hyp.H) (haX : a ∈ Subgroup.centralizer (X : Set G))
    {q d : G} (hqQ : q ∈ hyp.Q) (hdD : d ∈ hyp.D) (ha : a = q * d) :
    q ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G) ∧
      d ∈ hyp.D ⊓ Subgroup.centralizer (X : Set G) := by
  have hmem : a ∈
      ((hyp.Q ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) *
        ((hyp.D ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
    rw [hyp.cQ_mul_cD_eq_cH hXD]
    exact Subgroup.mem_inf.mpr ⟨haH, haX⟩
  obtain ⟨q', hq', d', hd', hqd⟩ := hmem
  rw [SetLike.mem_coe] at hq' hd'
  obtain ⟨p₀, -, huniq⟩ := hyp.existsUnique_Q_mul_D haH
  have e₁ := huniq (⟨q, hqQ⟩, ⟨d, hdD⟩) ha
  have e₂ := huniq (⟨q', (Subgroup.mem_inf.mp hq').1⟩, ⟨d', (Subgroup.mem_inf.mp hd').1⟩)
    hqd.symm
  have hpair := e₁.trans e₂.symm
  have hq : q = q' :=
    congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) (congrArg Prod.fst hpair)
  have hd : d = d' :=
    congrArg (Subtype.val (p := fun z => z ∈ hyp.D)) (congrArg Prod.snd hpair)
  exact ⟨hq ▸ hq', hd ▸ hd'⟩

/-- **The mappings of Ch. IV §1 stay inside a centralizer** (Peterfalvi Part II,
Ch. IV §4, step (2), p. 133 — "the mappings `f` and `h` relative to `U`, `U ∩ H` and
`t`" presupposes exactly this).

`t x t` centralizes `X` when `x` does, so its canonical form `g(x) h(x) · t · f(x)` has
both factors in `C_G(X)` (`canonicalForm_mem_centralizer`); splitting `g(x) h(x)` is
`splitQD_mem_centralizer`. -/
theorem fgh_mem_centralizer
    (Hfgh : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    {x : G} (hxQ : x ∈ hyp.Q) (hx1 : x ≠ 1)
    (hxX : x ∈ Subgroup.centralizer (X : Set G)) :
    f x ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G) ∧
      g x ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G) ∧
      h x ∈ hyp.D ⊓ Subgroup.centralizer (X : Set G) := by
  classical
  obtain ⟨hfQ, hgQ, hhD⟩ := Hfgh.mem x hxQ hx1
  have hgh : g x * h x ∈ hyp.H := hyp.H.mul_mem (hyp.Q_le_H hgQ) (hyp.D_le_H hhD)
  have htxtX : hyp.t * x * hyp.t ∈ Subgroup.centralizer (X : Set G) :=
    mul_mem (mul_mem htX hxX) htX
  obtain ⟨hghX, hfX⟩ := hyp.canonicalForm_mem_centralizer hXD htX htxtX hgh hfQ
    (Hfgh.eq x hxQ hx1)
  obtain ⟨hgX, hhX⟩ := hyp.splitQD_mem_centralizer hXD hgh hghX hgQ hhD rfl
  exact ⟨Subgroup.mem_inf.mpr ⟨hfQ, hfX⟩, hgX, hhX⟩

/-- **A subgroup of `C_G(X)` containing `t` and `C_Q(X)` inherits the rank-one setup**
(Peterfalvi Part II, Ch. IV §4, step (2), p. 133 — "the mappings `f` and `h` relative to
`U`, `U ∩ H` and `t`").

`Setup.restrict` only asks that the `Q`-parts of the two decompositions land in `K`, and
`canonicalForm_mem_centralizer` / `splitQD_mem_centralizer` put them in `C_Q(X)`.  So a
`K` between `C_Q(X)` and `C_G(X)` that contains `t` — the book's
`U = O^{2′}(C_G(P))` — is a rank-one setup on `U ∩ H`, `U ∩ Q`, `U ∩ D`, `t`. -/
theorem rankOneSetup_subgroup (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    {K : Subgroup G} (hKC : K ≤ Subgroup.centralizer (X : Set G)) (htK : hyp.t ∈ K)
    (hQK : hyp.Q ⊓ Subgroup.centralizer (X : Set G) ≤ K) :
    OddOrder.GroupTheory.RankOneBNPair.Setup (hyp.H.subgroupOf K) (hyp.Q.subgroupOf K)
      (hyp.D.subgroupOf K) (⟨hyp.t, htK⟩ : ↥K) :=
  hyp.rankOneSetup.restrict htK
    (fun _ hyK _ _ hxH _ hqQ hy =>
      hQK (Subgroup.mem_inf.mpr
        ⟨hqQ, (hyp.canonicalForm_mem_centralizer hXD htX (hKC hyK) hxH hqQ hy).2⟩))
    (fun _ haK haH _ hqQ _ hdD ha =>
      hQK ((hyp.splitQD_mem_centralizer hXD haH (hKC haK) hqQ hdD ha).1))

/-! ### The residual `O^{2′}(C_G(X))`

The book's `U`.  Both conditions `rankOneSetup_subgroup` asks for hold for it: it
contains `C_Q(X)` — a `2`-group, hence inside a Sylow `2`-subgroup, hence inside the
residual — and it contains `t`, for the same reason. -/

/-- **`C_Q(X)` lies in `O^{2′}(C_G(X))`**, provided it is a `2`-group. -/
theorem inf_centralizer_le_residual
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    hyp.Q ⊓ Subgroup.centralizer (X : Set G)
      ≤ (Subgroup.primeComplementResidual 2
          (Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hCQ.exists_le_sylow
  intro x hx
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  exact ⟨⟨x, hxC⟩,
    Subgroup.le_primeComplementResidual S (hS (Subgroup.mem_subgroupOf.mpr hxQ)), rfl⟩

/-- **`t ∈ O^{2′}(C_G(X))`** whenever `t` centralizes `X`: `t` is an involution, so it
lies in a Sylow `2`-subgroup of `C_G(X)`, hence in the residual. -/
theorem t_mem_residual (htX : hyp.t ∈ Subgroup.centralizer (X : Set G)) :
    hyp.t ∈ (Subgroup.primeComplementResidual 2
        (Subgroup.centralizer (X : Set G))).map
      (Subgroup.centralizer (X : Set G)).subtype := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : ↥(Subgroup.centralizer (X : Set G)) := ⟨hyp.t, htX⟩ with htCdef
  have htsq : tC ^ 2 = 1 := Subtype.ext (by simpa [htCdef] using hyp.t_sq)
  have hT : IsPGroup 2 ↥(Subgroup.zpowers tC) := by
    have hdvd : orderOf tC ∣ 2 := orderOf_dvd_of_pow_eq_one htsq
    have hcard : Nat.card ↥(Subgroup.zpowers tC) = orderOf tC := Nat.card_zpowers tC
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, h1]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, h2]; norm_num)
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  exact ⟨tC, Subgroup.le_primeComplementResidual S (hS (Subgroup.mem_zpowers tC)), rfl⟩

/-- **The residual `U = O^{2′}(C_G(X))` is a rank-one setup on `U ∩ H`, `U ∩ Q`,
`U ∩ D`, `t`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

This is what "the mappings `f` and `h` relative to `U`, `U ∩ H` and `t`" means, and with
`Setup.exists_fgh` it produces those mappings. -/
theorem rankOneSetup_residual (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    OddOrder.GroupTheory.RankOneBNPair.Setup
      (hyp.H.subgroupOf (residualImage (G := G) X))
      (hyp.Q.subgroupOf (residualImage (G := G) X))
      (hyp.D.subgroupOf (residualImage (G := G) X))
      ⟨hyp.t, hyp.t_mem_residual htX⟩ :=
  hyp.rankOneSetup_subgroup hXD htX
    (by rintro _ ⟨u, -, rfl⟩; exact u.2) (hyp.t_mem_residual htX)
    (hyp.inf_centralizer_le_residual hCQ)

/-- **`U/Z(U)` inherits the rank-one setup too** (Peterfalvi Part II, Ch. IV §4,
step (2), p. 133).

Ch. I §3 Proposition 1(c) identifies `U/Z(U)` with `PSU(3, ℓ)`, and step (2) argues
there.  The centre is a legitimate kernel for `Setup.quotient` because step (1) puts it
inside `P`, hence inside `V ≤ D`. -/
theorem setup_residualQuotient (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    OddOrder.GroupTheory.RankOneBNPair.Setup
      ((hyp.H.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ((hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ((hyp.D.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))
        ⟨hyp.t, hyp.t_mem_residual htX⟩) :=
  (hyp.rankOneSetup_residual hXD htX hCQ).quotient hZD

/-! ### Matching the distinguished involution

Step (2) compares the setup `U/Z(U)` inherits from `U` with the one Ch. I §3
Proposition 1(c) transports from the standard `PSU(3, ℓ)`.  Once `H`, `Q` and `D` are
matched, the two involutions differ by an element of `K` — both being involutions forces
`t' = d t` with `d^t = d⁻¹` — and conjugating by `K` covers exactly those differences,
because squaring is onto `K` (`exists_sq_eq_of_mem_K`, `K` having odd order). -/

/-- **Conjugating `t` by `K` realizes every `K`-translate of `t`** (Peterfalvi Part II,
Ch. IV §4, step (2), p. 133).

For `e ∈ K` the conjugate is `e⁻¹ t e = e⁻² t`, because `t e t = e⁻¹` is the defining
property of `K`.  Squaring being onto `K` (`exists_sq_eq_of_mem_K`), every `d t` with
`d ∈ K` occurs. -/
theorem exists_mem_K_conj_t_eq {d : G} (hd : d ∈ hyp.K) :
    ∃ e ∈ hyp.K, e⁻¹ * hyp.t * e = d * hyp.t := by
  obtain ⟨e, he, hesq⟩ := hyp.exists_sq_eq_of_mem_K (hyp.K.inv_mem hd)
  refine ⟨e, he, ?_⟩
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  have heK : e ∈ hyp.KSet := by rw [← hyp.coe_K]; exact he
  have hte : hyp.t * e * hyp.t = e⁻¹ := heK.2
  have hdd : e⁻¹ * e⁻¹ = d := by
    rw [← inv_inv d, ← hesq]
    group
  calc e⁻¹ * hyp.t * e
      = e⁻¹ * (hyp.t * e * hyp.t) * hyp.t := by
        calc e⁻¹ * hyp.t * e = e⁻¹ * hyp.t * e * (hyp.t * hyp.t) := by
              rw [htt, mul_one]
          _ = e⁻¹ * (hyp.t * e * hyp.t) * hyp.t := by group
    _ = e⁻¹ * e⁻¹ * hyp.t := by rw [hte]
    _ = d * hyp.t := by rw [hdd]

end Centralizer

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {X : Subgroup G}
  [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Ω)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Ω)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Ω)) result.L}
  (details : CentralizerPSUData hyp X result data)

/-- **The Proposition of Ch. III §3 holds on `U/Z(U)`** (Peterfalvi Part II, Ch. IV §4,
step (2), p. 133).

`exists_standardModel` takes `|s t| = 3`, `n ≠ 0`, `|Q̄₀| = 2ⁿ`, `|Q̄| = |Q̄₀|³` and the
induction hypothesis; all five were transported to `U/Z(U)` in
`PSU3SectionFourModel`, the last one along `natCard_residualQuotient_lt`.  The two
standing bundles `LemmaFiveSetup` and `QuotientFieldModel` and the central `x₀ ≠ 1` are
also available there (`nonempty_standingData_residualQuotient`,
`exists_center_Q_ne_one_residualQuotient`), so a caller can discharge every argument. -/
theorem isStandardModel_residualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (ih : TheoremAInductionBelow G Ω) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∀ (sfive : (hyp.residualQuotientHypothesis details).LemmaFiveSetup data.n)
      (M : (hyp.residualQuotientHypothesis details).QuotientFieldModel data.n)
      (x₀ : ↥(Subgroup.center (hyp.residualQuotientHypothesis details).Q)), x₀ ≠ 1 →
      (hyp.residualQuotientHypothesis details).IsStandardModel sfive M x₀ := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  have ihq : TheoremAInductionBelow
      (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X))
      (ULift.{v} (Unital data.n)) :=
    hyp.theoremAInductionBelow_residualQuotient details hXV hX ih
  intro sfive M x₀ hx₀
  exact (hyp.residualQuotientHypothesis details).exists_standardModel sfive M
    (hyp.residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t details)
    (Nat.zero_lt_one.trans data.one_lt_n).ne'
    (hyp.natCard_residualQuotientHypothesis_Q0 details)
    (hyp.natCard_residualQuotientHypothesis_Q details) ihq x₀ hx₀

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
