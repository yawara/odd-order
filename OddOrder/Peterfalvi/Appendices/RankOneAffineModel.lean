/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki
import OddOrder.Peterfalvi.Appendices.SemilinearField
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Peterfalvi.Appendices.NearFieldClass
import OddOrder.GroupTheory.NearFieldFromSharplyTransitive
import OddOrder.GroupTheory.SolvableTwoTransitive
import OddOrder.GroupTheory.BrauerSuzuki
import OddOrder.GroupTheory.BrauerSuzukiEndgame
import OddOrder.GroupTheory.BrauerSuzukiQ8
import OddOrder.GroupTheory.BrauerSuzukiGeneral

/-!
# Peterfalvi Appendix II, Proposition 1 — the affine near-field model of a rank-one group

Split out of `NearFields.lean` (which exceeded the 2000-line file limit).  Contains the
`RankOneHypothesis` structure, the `AffineNearFieldModel`, the main theorem
`rankOne_affine_nearField`, and the supporting lemmas (`exists_regular_normal`, `brauerSuzuki`,
`q_regular_on_complement`, `exists_conj_regular`, `model_involution_data`).  See `NearFields.lean`
for the near-field basics, the twisted-field construction, and Proposition 2.

Same namespace `OddOrder.Peterfalvi.Appendices.NearFields` as `NearFields.lean`, so downstream
references are unchanged. -/

namespace OddOrder.Peterfalvi.Appendices.NearFields

section PropositionOne

open scoped Pointwise

/-- **Peterfalvi Appendix II, Proposition 1, hypotheses** (p. 137): the Part II hypotheses
**(A1)** and **(A2)** (p. 97) together with "`G` has 2-rank `1`".

The fields are exactly those of `Suzuki.Hypothesis` *except* (A3), which is replaced by its
negation.  This has to be a separate structure: `Suzuki.Hypothesis` carries
`two_rank_ge_two : ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1` as a field, so bolting a
genuine 2-rank-one hypothesis onto it would produce contradictory (hence vacuous) hypotheses.

`two_rank_one` says `G` has **no** Klein four subgroup, i.e. 2-rank `≤ 1`; equality holds because
`Q_even` forces an involution to exist (Cauchy).  The hypotheses are satisfiable: e.g.
`G = AGL(1, 3) ≅ S₃` acting on three points, with `Q` of order `2` and `D = 1`. -/
structure RankOneHypothesis (G Ω : Type*) [Group G] [MulAction G Ω] [Finite G] where
  /-- the base point of `Ω`; `H` is its stabilizer -/
  basept : Ω
  /-- (A1): the action is doubly transitive -/
  doubly_transitive : MulAction.IsMultiplyPretransitive G Ω 2
  /-- (A2): the action is faithful -/
  faithful : FaithfulSMul G Ω
  H : Subgroup G
  Q : Subgroup G
  D : Subgroup G
  H_def : H = MulAction.stabilizer G basept
  /-- the distinguished involution `t ∈ G - H` -/
  t : G
  t_sq : t ^ 2 = 1
  t_ne_one : t ≠ 1
  t_not_mem_H : t ∉ H
  D_def : D = H ⊓ H.map (MulAut.conj t).toMonoidHom
  Q_le_H : Q ≤ H
  Q_normal_in_H : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  Q_inf_D_eq_bot : Q ⊓ D = ⊥
  Q_mul_D_eq_H : (Q : Set G) * (D : Set G) = (H : Set G)
  Q_even : Even (Nat.card Q)
  D_odd : Odd (Nat.card D)
  /-- `G` has 2-rank one: it contains no elementary abelian subgroup of order `4`.
  This is the negation of Part II's hypothesis (A3). -/
  two_rank_one : ¬ ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1

/-- **Proposition 1, prerequisite (i)** (Huppert, *Endliche Gruppen* I, Kapitel III, Satz 8.2):
a group of 2-rank one has cyclic or generalized quaternion Sylow `2`-subgroups.

Bridge from `two_rank_one` to **Isaacs Thm 6.11**
(`isCyclic_or_two_quaternion_of_subgroups_card_prime_unique`): if a Sylow `2`-subgroup had two
distinct subgroups of order `2`, it would contain an elementary abelian subgroup of order `4`
(`IsPGroup.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne`), which
`two_rank_one` forbids. -/
theorem RankOneHypothesis.sylow_two_isCyclic_or_quaternion
    {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) (S : Sylow 2 G) :
    IsCyclic ↥(S : Subgroup G) ∨
      ∃ n : ℕ, Nonempty (↥(S : Subgroup G) ≃* QuaternionGroup n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUnique : ∀ K L : Subgroup ↥(S : Subgroup G),
      Nat.card K = 2 → Nat.card L = 2 → K = L := by
    intro K L hK hL
    by_contra hne
    obtain ⟨E, hE_elem, hE_card⟩ :=
      S.isPGroup'.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne
        hK hL hne
    refine hyp.two_rank_one ⟨E.map (S : Subgroup G).subtype, ?_, ?_⟩
    · rw [Nat.card_congr
        (Subgroup.equivMapOfInjective E _ (S : Subgroup G).subtype_injective).symm.toEquiv,
        hE_card]
      norm_num
    · rintro x ⟨y, hy, rfl⟩
      have hy2 : (⟨y, hy⟩ : ↥E) ^ 2 = 1 := hE_elem.pow_eq_one _
      have hyS : y ^ 2 = 1 := by simpa using congrArg Subtype.val hy2
      simpa using congrArg ((S : Subgroup G).subtype) hyS
  rcases OddOrder.Isaacs.Ch06.isCyclic_or_two_quaternion_of_subgroups_card_prime_unique
      S.isPGroup' hUnique with hcyc | ⟨_, hq⟩
  · exact Or.inl hcyc
  · exact Or.inr hq

/-- **Peterfalvi Appendix II, Proposition 1, conclusion**: the affine near-field model of `G`.

The book asserts an isomorphism `G ≅ 𝓛(F) ⋊ Σ = (F ⋊ F^*) ⋊ Σ` identifying `Q` with `F^*` and `D`
with `Σ`.  Internally this says: `F` sits in `G` as a normal subgroup complemented by `H`
(`G = F ⋊ H`), the conjugation action of `Q` on `F` is right multiplication by `F^*` under an
isomorphism `Q ≃* Fˣ`, and `D` acts faithfully on `F` by near-field automorphisms.  A "near-field
automorphism" is an additive equivalence that is also multiplicative — spelled out as `dAut` +
`dAut_mul` rather than through a bundled automorphism group.

The final two clauses of the proposition ("`H` has only one involution"; "if `u ≠ v` are
involutions of `G` then `|uv|` is the characteristic of `F`") are the last three fields; `char` is
the characteristic in the sense of `exists_prime_char`. -/
structure AffineNearFieldModel {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) (F : Type*) [NearField F] where
  /-- `(F, +)` embedded in `G`. -/
  emb : Multiplicative F →* G
  emb_injective : Function.Injective emb
  /-- `F ⊴ G`. -/
  range_normal : (MonoidHom.range emb).Normal
  /-- `G = F ⋊ H`. -/
  isComplement : Subgroup.IsComplement' (MonoidHom.range emb) hyp.H
  /-- `Q` is identified with `F^*`. -/
  qEquiv : ↥hyp.Q ≃* Fˣ
  /-- The identification `Q ≃* F^*` turns conjugation into right multiplication, i.e. it realizes
  `F ⋊ Q ≅ F ⋊ F^* = 𝓛(F)`.

  The `q⁻¹` on the right is forced and not cosmetic (issue 9406): in a *right* near-field the maps
  `x ↦ x·a` (`a ∈ F^*`) compose **anti**-homomorphically (`L_a ∘ L_b = L_{b·a}`), so the natural
  bijection `Q → F^*` sending `q` to the linear part of conjugation-by-`q` is an *anti*-isomorphism.
  A genuine group isomorphism `qEquiv : Q ≃* F^*` must therefore realize conjugation-by-`q` as right
  multiplication by `qEquiv q⁻¹` (equivalently `qEquiv q = q⁻¹ • e`, `mulEquivUnits`); writing
  `qEquiv q` here would force `Q` to be abelian and make the model unsatisfiable for the exceptional
  near-fields (`F^* ≅ SL(2, 3)`, quaternion Sylow `2`). -/
  qEquiv_conj : ∀ (q : ↥hyp.Q) (x : F),
    (q : G) * emb (Multiplicative.ofAdd x) * (q : G)⁻¹
      = emb (Multiplicative.ofAdd (x * ((qEquiv q⁻¹ : Fˣ) : F)))
  /-- `D` acts on `F` by additive bijections … -/
  dAut : ↥hyp.D → (F ≃+ F)
  /-- … which are multiplicative, i.e. near-field automorphisms … -/
  dAut_mul : ∀ (g : ↥hyp.D) (x y : F), dAut g (x * y) = dAut g x * dAut g y
  /-- … faithfully, so that `D` *is* a group `Σ` of automorphisms of `F` … -/
  dAut_injective : Function.Injective dAut
  /-- … and the action is the conjugation action inside `G`. -/
  dAut_conj : ∀ (g : ↥hyp.D) (x : F),
    (g : G) * emb (Multiplicative.ofAdd x) * (g : G)⁻¹ = emb (Multiplicative.ofAdd (dAut g x))
  /-- `H` has exactly one involution. -/
  unique_involution_in_H : ∃! u : ↥hyp.H, (u : G) ^ 2 = 1 ∧ (u : G) ≠ 1
  /-- The characteristic of the near-field `F`. -/
  char : ℕ
  char_prime : char.Prime
  char_spec : ∀ x : F, char • x = 0
  /-- If `u ≠ v` are involutions of `G` then `|uv|` is the characteristic of `F`. -/
  orderOf_mul_of_involutions : ∀ u v : G, u ^ 2 = 1 → u ≠ 1 → v ^ 2 = 1 → v ≠ 1 → u ≠ v →
    orderOf (u * v) = char
  /-- The product of two distinct involutions of `G` is a *translation*: both involutions
  invert the abelian regular normal subgroup, so their product centralizes it and hence
  lies in it.  (Peterfalvi App. C, Prop 1; used for `Z₁ ⊆ T` in Part II, Ch. II (14).) -/
  mul_involutions_mem_range : ∀ u v : G, u ^ 2 = 1 → u ≠ 1 → v ^ 2 = 1 → v ≠ 1 → u ≠ v →
    u * v ∈ MonoidHom.range emb

-- (`rankOne_affine_nearField` is stated and proved below, after its prerequisites
-- `oddCore_ne_bot` / `exists_regular_normal` / `brauerSuzuki` / `exists_conj_regular`.)

/-- **The odd core `O_{2'}(G)` is nontrivial** (first step of Peterfalvi App. C, Prop 1's proof,
given Brauer–Suzuki (ii)).  If `O_{2'}(G) = 1` then Brauer–Suzuki `O_{2'}(G) ⊔ C_G(t) = ⊤` collapses
to `C_G(t) = ⊤`, i.e. the involution `t` is central.  But then conjugation by `t` is the identity,
so `H^t = H` and `D = H ⊓ H^t = H`; hence `|H|` is odd (`D_odd`).  This contradicts `Q ≤ H` with
`|Q|` even (`Q_even`), which forces `|H|` even.

The Brauer–Suzuki conclusion is taken as a hypothesis `hbs`; it is discharged from
`RankOneHypothesis.sylow_two_isCyclic_or_quaternion` together with
`brauerSuzuki_of_isCyclic_sylowTwo` / `brauerSuzuki_of_quaternionSylow` (the residual `Q₈` case of
the latter being the sole research-adjacent gap). -/
theorem RankOneHypothesis.oddCore_ne_bot {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω)
    (hbs : OddOrder.Isaacs.Ch03.oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {hyp.t} = ⊤) :
    OddOrder.Isaacs.Ch03.oPiCore {p | p ≠ 2} G ≠ ⊥ := by
  intro hbot
  -- Trivial odd core collapses Brauer–Suzuki to `C_G(t) = ⊤`: `t` is central.
  rw [hbot, bot_sup_eq] at hbs
  have htc : ∀ g : G, hyp.t * g = g * hyp.t := by
    intro g
    have hmem : g ∈ Subgroup.centralizer {hyp.t} := by rw [hbs]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_iff.mp hmem hyp.t rfl
  -- Central `t` ⟹ conjugation by `t` is the identity ⟹ `H^t = H` ⟹ `D = H`.
  have hconj_id : (MulAut.conj hyp.t).toMonoidHom = MonoidHom.id G := by
    ext g
    change hyp.t * g * hyp.t⁻¹ = g
    rw [htc g, mul_assoc, mul_inv_cancel, mul_one]
  have hDH : hyp.D = hyp.H := by
    rw [hyp.D_def, hconj_id, Subgroup.map_id, inf_idem]
  -- `Q ≤ H` and `|Q|` even force `|H|` even, contradicting `|D| = |H|` odd.
  have hHeven : Even (Nat.card hyp.H) :=
    even_iff_two_dvd.mpr
      (dvd_trans hyp.Q_even.two_dvd (Subgroup.card_dvd_of_le hyp.Q_le_H))
  exact (Nat.not_even_iff_odd.mpr (hDH ▸ hyp.D_odd)) hHeven

/-- **The affine regular normal subgroup `F`** (Peterfalvi App. C, Prop 1, prerequisite (iii),
given Brauer–Suzuki (ii)).  From `O_{2'}(G) ≠ 1` (`oddCore_ne_bot`) and its solvability (odd order,
Feit–Thompson), Huppert II Satz 3.2
(`exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive`) yields an elementary abelian
`p`-subgroup `F ⊴ G` regular on `Ω`; regularity gives the complement `G = F ⋊ H`
(`isComplement'_stabilizer`).  This is the additive group underlying the near-field of Prop 1.

Takes the Brauer–Suzuki conclusion `hbs` as a hypothesis (discharged via the cyclic / generalized
quaternion split; the residual `Q₈` case of the latter is the sole research-adjacent gap). -/
theorem RankOneHypothesis.exists_regular_normal {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω)
    (hbs : OddOrder.Isaacs.Ch03.oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {hyp.t} = ⊤) :
    ∃ (p : ℕ) (F : Subgroup G), p.Prime ∧ F.Normal ∧ IsMulCommutative ↥F ∧
      (∀ x ∈ F, x ^ p = 1) ∧ MulAction.IsPretransitive ↥F Ω ∧
      Subgroup.IsComplement' F hyp.H ∧ Odd (Nat.card ↥F) := by
  have := hyp.faithful
  -- `O_{2'}(G)` is a nontrivial solvable normal subgroup (odd order → Feit–Thompson).
  have hNne : OddOrder.Isaacs.Ch03.oPiCore {p | p ≠ 2} G ≠ ⊥ := hyp.oddCore_ne_bot hbs
  have hNodd : Odd (Nat.card ↥(OddOrder.Isaacs.Ch03.oPiCore {p | p ≠ 2} G)) :=
    Nat.not_even_iff_odd.mp (mt Even.two_dvd (fun h2 =>
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {p | p ≠ 2}) 2
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, Nat.card_pos.ne'⟩) rfl))
  have hNsolv : Group.IsSolvable ↥(OddOrder.Isaacs.Ch03.oPiCore {p | p ≠ 2} G) := feitThompson hNodd
  obtain ⟨p, F, _hp, hFnormal, hFle, _hFne, hcomm, hexp, _hpgroup, htrans, hfree⟩ :=
    OddOrder.GroupTheory.exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive
      hyp.doubly_transitive hNne hNsolv
  -- `|F|` is odd since `F ≤ O_{2'}(G)` has odd order.
  have hFodd : Odd (Nat.card ↥F) :=
    Nat.not_even_iff_odd.mp fun he =>
      (Nat.not_even_iff_odd.mpr hNodd)
        (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp he).trans (Subgroup.card_dvd_of_le hFle)))
  refine ⟨p, F, _hp, hFnormal, hcomm, hexp, htrans, ?_, hFodd⟩
  -- `G = F ⋊ H`: `F` regular on `Ω`, `H = stabilizer basept`.
  rw [hyp.H_def]
  refine Subgroup.isComplement'_stabilizer hyp.basept (fun h hh => ?_) (fun g => ?_)
  · have hmem : (h : G) ∈ MulAction.stabilizer G hyp.basept ⊓ F :=
      ⟨MulAction.mem_stabilizer_iff.mpr hh, h.2⟩
    rw [hfree hyp.basept, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · obtain ⟨f, hf⟩ := htrans.exists_smul_eq (g • hyp.basept) hyp.basept
    exact ⟨f, hf⟩

section BrauerSuzukiAssembly

/-- **Brauer–Suzuki for the rank-one group** (Peterfalvi App. C, Prop 1, prerequisite (ii)):
`O_{2'}(G) ⊔ C_G(t) = ⊤` for the distinguished involution `t`.  The Sylow `2`-subgroup `T`
containing `t` is cyclic or generalized quaternion (`sylow_two_isCyclic_or_quaternion`), and
Brauer–Suzuki covers each case: `brauerSuzuki_of_isCyclic_sylowTwo` and
`brauerSuzuki_of_quaternionSylowTwo`.

The generalized quaternion branch used to be assembled here (splitting on `|T| = 4`, `8`, `≥ 16`
and transporting the presentation into a `QuaternionSylowSetup`); that argument uses nothing about
the rank-one hypothesis and now lives, in the general form, in
`OddOrder/GroupTheory/BrauerSuzukiGeneral.lean`. -/
theorem RankOneHypothesis.brauerSuzuki {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) :
    OddOrder.Isaacs.Ch03.oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {hyp.t} = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the Sylow `2`-subgroup `T` containing `t`
  have htP : IsPGroup 2 ↑(Subgroup.zpowers hyp.t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hyp.t_sq hyp.t_ne_one
  obtain ⟨T, hle⟩ := htP.exists_le_sylow
  have htT : hyp.t ∈ (T : Subgroup G) := hle (Subgroup.mem_zpowers hyp.t)
  rcases hyp.sylow_two_isCyclic_or_quaternion T with hcyc | ⟨m, he⟩
  · exact OddOrder.GroupTheory.brauerSuzuki_of_isCyclic_sylowTwo T hcyc hyp.t hyp.t_sq
      hyp.t_ne_one
  · exact OddOrder.GroupTheory.brauerSuzuki_of_quaternionSylowTwo T he htT
      (orderOf_eq_prime hyp.t_sq hyp.t_ne_one)

end BrauerSuzukiAssembly

open MulAction SubMulAction in
/-- **`Q` acts regularly on `Ω ∖ {basept}`** (the permutation-action heart of Peterfalvi App. C,
Prop 1's transport — *not* a research gap, elementary from the hypotheses).

The key is that `D = H ⊓ H^t` is the **two-point stabilizer** `G_{ω, ω'}` where `ω' := t • basept`:
`H^t = G_{t·ω}` (`stabilizer_smul_eq_stabilizer_map_conj`), so `D = G_ω ⊓ G_{ω'}`.  Since
`H = G_ω` is transitive on `Ω ∖ {ω}` (double transitivity) and `H = Q·D` with `D` fixing `ω'`, the
even part `Q` is **regular**: `q ↦ q • ω'` is a bijection onto `Ω ∖ {ω}` (transitive since every
target is `q·d • ω' = q • ω'`; free since `stab_Q(ω') = Q ⊓ D = ⊥`).

Under `F ≅ Ω` (`F` regular) this transports to `Q` acting regularly on `F^#` by conjugation, the
`reg` datum of the near-field `SharplyTransitiveData`. -/
theorem RankOneHypothesis.q_regular_on_complement {G Ω : Type*} [Group G] [MulAction G Ω]
    [Finite G] (hyp : RankOneHypothesis G Ω) (ω'' : Ω) (hω'' : ω'' ≠ hyp.basept) :
    ∃! q : ↥hyp.Q, (q : G) • (hyp.t • hyp.basept) = ω'' := by
  classical
  have h2 := hyp.doubly_transitive
  have hpre : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  set ω' := hyp.t • hyp.basept with hω'_def
  have hω'_ne : ω' ≠ hyp.basept := fun h =>
    hyp.t_not_mem_H (hyp.H_def ▸ mem_stabilizer_iff.mpr h)
  -- `D = G_basept ⊓ G_{ω'}` (two-point stabilizer).
  have hD_eq : hyp.D = stabilizer G hyp.basept ⊓ stabilizer G ω' := by
    rw [hyp.D_def, hyp.H_def, ← stabilizer_smul_eq_stabilizer_map_conj]
  -- `H = G_basept` is transitive on `Ω ∖ {basept}`.
  have h1 : IsPretransitive (stabilizer G hyp.basept) (ofStabilizer G hyp.basept) :=
    is_one_pretransitive_iff.mp
      ((SubMulAction.ofStabilizer.isMultiplyPretransitive (n := 1) (a := hyp.basept)).mp h2)
  have hH_trans : ∀ a b : Ω, a ≠ hyp.basept → b ≠ hyp.basept →
      ∃ h : G, h ∈ hyp.H ∧ h • a = b := by
    intro a b ha hb
    obtain ⟨h, hh⟩ := h1.exists_smul_eq
      (⟨a, (mem_ofStabilizer_iff G hyp.basept).mpr ha⟩ : ofStabilizer G hyp.basept)
      ⟨b, (mem_ofStabilizer_iff G hyp.basept).mpr hb⟩
    refine ⟨(h : G), by rw [hyp.H_def]; exact h.2, ?_⟩
    have hval := congrArg Subtype.val hh
    rwa [SubMulAction.val_smul_of_tower] at hval
  -- Existence: `h • ω' = ω''` for some `h = q·d ∈ H`, and `d • ω' = ω'`.
  obtain ⟨h, hhH, hh⟩ := hH_trans ω' ω'' hω'_ne hω''
  have hmem : h ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by rw [hyp.Q_mul_D_eq_H]; exact hhH
  obtain ⟨q, hqQ, d, hdD, hqd⟩ := Set.mem_mul.mp hmem
  have hdω' : (d : G) • ω' = ω' := by
    have hdD' : d ∈ hyp.D := SetLike.mem_coe.mp hdD
    rw [hD_eq] at hdD'
    exact mem_stabilizer_iff.mp hdD'.2
  have hqω' : (q : G) • ω' = ω'' := by rw [← hh, ← hqd, mul_smul, hdω']
  refine ⟨⟨q, SetLike.mem_coe.mp hqQ⟩, hqω', ?_⟩
  rintro ⟨q₂, hq₂Q⟩ hq₂
  -- `q₂⁻¹ q ∈ Q ⊓ D = ⊥`, hence `q = q₂`.
  have hmemQ : q₂⁻¹ * q ∈ hyp.Q := hyp.Q.mul_mem (hyp.Q.inv_mem hq₂Q) (SetLike.mem_coe.mp hqQ)
  have hmemStab_base : q₂⁻¹ * q ∈ stabilizer G hyp.basept := by
    rw [← hyp.H_def]; exact hyp.Q_le_H hmemQ
  have hmemStab_ω' : q₂⁻¹ * q ∈ stabilizer G ω' := by
    rw [mem_stabilizer_iff, mul_smul, hqω', ← hq₂, ← mul_smul, inv_mul_cancel, one_smul]
  have hmemD : q₂⁻¹ * q ∈ hyp.D := by
    rw [hD_eq]; exact Subgroup.mem_inf.mpr ⟨hmemStab_base, hmemStab_ω'⟩
  have hbot : q₂⁻¹ * q ∈ (⊥ : Subgroup G) := by
    rw [← hyp.Q_inf_D_eq_bot]; exact Subgroup.mem_inf.mpr ⟨hmemQ, hmemD⟩
  exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot))

open MulAction in
/-- **`Q` acts regularly on `F ∖ {1}` by conjugation** (Peterfalvi App. C, Prop 1's transport: the
near-field `reg` datum).  Transporting `q_regular_on_complement` across the regular action `F ≅ Ω`
(`f ↦ f • basept`): conjugation `q · e · q⁻¹` of the `F`-element `e` corresponds to the permutation
`q • ω'` since `(q e q⁻¹) • basept = q • (e • basept) = q • ω'` (as `q ∈ Q ≤ H` fixes `basept`).

Produces the multiplicative identity `e` (the `F`-element with `e • basept = t • basept = ω'`) and,
for every `f ∈ F ∖ {1}`, the unique `q ∈ Q` with `q e q⁻¹ = f`. -/
theorem RankOneHypothesis.exists_conj_regular {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) {Fsub : Subgroup G} [hFN : Fsub.Normal]
    (htrans : IsPretransitive ↥Fsub Ω) (hdisj : Disjoint Fsub hyp.H) :
    ∃ e : G, e ∈ Fsub ∧ e • hyp.basept = hyp.t • hyp.basept ∧
      ∀ f : G, f ∈ Fsub → f ≠ 1 → ∃! q : ↥hyp.Q, (q : G) * e * (q : G)⁻¹ = f := by
  classical
  -- `F` acts freely at `basept` (disjoint from `H = stabilizer basept`).
  have hfree : ∀ a b : G, a ∈ Fsub → b ∈ Fsub → a • hyp.basept = b • hyp.basept → a = b := by
    intro a b haF hbF hab
    have hmem : b⁻¹ * a ∈ Fsub ⊓ hyp.H :=
      ⟨Fsub.mul_mem (Fsub.inv_mem hbF) haF, hyp.H_def ▸ mem_stabilizer_iff.mpr (by
        rw [mul_smul, hab, ← mul_smul, inv_mul_cancel, one_smul])⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  -- pick `e ∈ F` with `e • basept = t • basept = ω'`.
  obtain ⟨e', he'⟩ := htrans.exists_smul_eq hyp.basept (hyp.t • hyp.basept)
  have he'G : (e' : G) • hyp.basept = hyp.t • hyp.basept := he'
  refine ⟨(e' : G), e'.2, he'G, fun f hfF hf1 => ?_⟩
  -- `((q e q⁻¹) • basept) = q • ω'`.
  have hconj : ∀ q : ↥hyp.Q, ((q : G) * (e' : G) * (q : G)⁻¹) • hyp.basept
      = (q : G) • (hyp.t • hyp.basept) := by
    intro q
    have hqfix : (q : G)⁻¹ • hyp.basept = hyp.basept :=
      mem_stabilizer_iff.mp (hyp.H_def ▸ hyp.Q_le_H (hyp.Q.inv_mem q.2))
    rw [mul_smul, mul_smul, hqfix, he'G]
  -- `q e q⁻¹ = f  ↔  q • ω' = f • basept`.
  have hφ : f • hyp.basept ≠ hyp.basept :=
    fun h => hf1 (hfree f 1 hfF Fsub.one_mem (by simpa using h))
  obtain ⟨q0, hq0, huniq⟩ := hyp.q_regular_on_complement (f • hyp.basept) hφ
  have hequiv : ∀ q : ↥hyp.Q,
      ((q : G) * (e' : G) * (q : G)⁻¹ = f) ↔ ((q : G) • (hyp.t • hyp.basept) = f • hyp.basept) := by
    intro q
    constructor
    · intro h; rw [← hconj q, h]
    · intro h
      exact hfree _ f (hFN.conj_mem _ e'.2 _) hfF (by rw [hconj q, h])
  exact ⟨q0, (hequiv q0).mpr hq0, fun q hq => huniq q ((hequiv q).mp hq)⟩

open OddOrder.GroupTheory
open scoped IsMulCommutative

/-- **The involution data of the affine near-field model** (Peterfalvi App. C, Prop 1, last three
clauses): `H` has a unique involution and, for distinct involutions `u ≠ v` of `G`, the order of
`u v` equals the exponent `p` of the regular normal subgroup `F` (the characteristic of the
near-field).

**Proved** (axiom-clean) via the fixed-point analysis of involutions in the doubly transitive
action: every involution of `G` fixes a point (odd degree `|Ω| = |F|`) and at most one (two-point
stabilizers are odd, being conjugate to `D`), so after conjugating into `H` it acts freely on
`F ∖ {1}`; a fixed-point-free order-`2` automorphism of the abelian `F` inverts it.  Hence all
involutions invert `F`, `C_G(F) = F`, so two involutions of `H` coincide (their product centralizes
`F` and lies in `F ⊓ H = 1`) and the product of two distinct involutions lies in `F ∖ {1}`, of order
`p`.  Stated over the same regular-normal data `(p, Fsub)` that the model is built from. -/
theorem RankOneHypothesis.model_involution_data {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) {p : ℕ} {Fsub : Subgroup G} [Fsub.Normal]
    [IsMulCommutative ↥Fsub]
    (hp : p.Prime) (htrans : MulAction.IsPretransitive ↥Fsub Ω)
    (hcompl : Subgroup.IsComplement' Fsub hyp.H) (hexp : ∀ x ∈ Fsub, x ^ p = 1)
    (hFodd : Odd (Nat.card ↥Fsub)) :
    (∃! u : ↥hyp.H, (u : G) ^ 2 = 1 ∧ (u : G) ≠ 1) ∧
      (∀ u v : G, u ^ 2 = 1 → u ≠ 1 → v ^ 2 = 1 → v ≠ 1 → u ≠ v →
        u * v ∈ Fsub ∧ orderOf (u * v) = p) := by
  classical
  have := hyp.faithful
  have h2t := hyp.doubly_transitive
  have hpre : MulAction.IsPretransitive G Ω := MulAction.isPretransitive_of_is_two_pretransitive
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint Fsub hyp.H := hcompl.disjoint
  -- `Fsub` acts freely at `basept`.
  have hfreeF : ∀ a b : G, a ∈ Fsub → b ∈ Fsub → a • hyp.basept = b • hyp.basept → a = b := by
    intro a b haF hbF hab
    have hmem : b⁻¹ * a ∈ Fsub ⊓ hyp.H :=
      ⟨Fsub.mul_mem (Fsub.inv_mem hbF) haF, hyp.H_def ▸ MulAction.mem_stabilizer_iff.mpr (by
        rw [mul_smul, hab, ← mul_smul, inv_mul_cancel, one_smul])⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  -- `f ↦ f • basept` is a bijection `Fsub ≃ Ω`, so `Ω` is finite of odd cardinality.
  have hbij : Function.Bijective (fun f : ↥Fsub => (f : G) • hyp.basept) := by
    refine ⟨fun a b hab => Subtype.ext (hfreeF a b a.2 b.2 hab), fun ω => ?_⟩
    obtain ⟨f, hf⟩ := htrans.exists_smul_eq hyp.basept ω
    exact ⟨f, hf⟩
  have : Finite Ω := Finite.of_surjective _ hbij.surjective
  have hΩodd : Odd (Nat.card Ω) := by
    rw [← Nat.card_eq_of_bijective _ hbij]; exact hFodd
  -- An element of `H` centralizing `Fsub` is trivial (fixes all of `Ω`).
  have hHCF_triv : ∀ h : G, h ∈ hyp.H → h ∈ Subgroup.centralizer (Fsub : Set G) → h = 1 := by
    intro h hhH hhC
    refine eq_of_smul_eq_smul (α := Ω) fun ω => ?_
    obtain ⟨f, hf⟩ := htrans.exists_smul_eq hyp.basept ω
    have hfG : (f : G) • hyp.basept = ω := hf
    have hbase : h • hyp.basept = hyp.basept :=
      MulAction.mem_stabilizer_iff.mp (hyp.H_def ▸ hhH)
    have hcomm : (f : G) * h = h * (f : G) :=
      Subgroup.mem_centralizer_iff.mp hhC (f : G) (SetLike.coe_mem f)
    rw [one_smul, ← hfG, ← mul_smul, ← hcomm, mul_smul, hbase]
  -- `C_G(Fsub) ≤ Fsub` (using `G = Fsub ⋊ H`).
  have hCF_le : Subgroup.centralizer (Fsub : Set G) ≤ Fsub := by
    intro g hg
    obtain ⟨⟨f, h⟩, hfh⟩ := hcompl.surjective g
    have hfhG : (f : G) * (h : G) = g := hfh
    have hf_mem : (f : G) ∈ Subgroup.centralizer (Fsub : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun s hs => by
        have hc := congrArg (fun z : ↥Fsub => (z : G)) (mul_comm (⟨s, hs⟩ : ↥Fsub) f)
        push_cast at hc
        exact hc
    have hh_mem : (h : G) ∈ Subgroup.centralizer (Fsub : Set G) := by
      have hheq : (h : G) = (f : G)⁻¹ * g := by rw [← hfhG]; group
      rw [hheq]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hf_mem) hg
    have hh1 : (h : G) = 1 := hHCF_triv (h : G) h.2 hh_mem
    have hgf : g = (f : G) := by rw [← hfhG, hh1, mul_one]
    rw [hgf]; exact f.2
  -- The two-point stabilizer `G_basept ⊓ G_ω` (for `ω ≠ basept`) is odd: it is conjugate to
  -- `D = G_basept ⊓ G_{t·basept}` inside `H` (which is transitive on `Ω ∖ {basept}`).
  have hHtrans : ∀ a b : Ω, a ≠ hyp.basept → b ≠ hyp.basept → ∃ h : G, h ∈ hyp.H ∧ h • a = b := by
    intro a b ha hb
    have h1 : MulAction.IsPretransitive (MulAction.stabilizer G hyp.basept)
        (SubMulAction.ofStabilizer G hyp.basept) :=
      MulAction.is_one_pretransitive_iff.mp
        ((SubMulAction.ofStabilizer.isMultiplyPretransitive (n := 1)
          (a := hyp.basept)).mp hyp.doubly_transitive)
    obtain ⟨h, hh⟩ := h1.exists_smul_eq
      (⟨a, (SubMulAction.mem_ofStabilizer_iff G hyp.basept).mpr ha⟩ :
        SubMulAction.ofStabilizer G hyp.basept)
      ⟨b, (SubMulAction.mem_ofStabilizer_iff G hyp.basept).mpr hb⟩
    refine ⟨(h : G), by rw [hyp.H_def]; exact h.2, ?_⟩
    have hval := congrArg Subtype.val hh
    rwa [SubMulAction.val_smul_of_tower] at hval
  have h2pt_odd : ∀ ω : Ω, ω ≠ hyp.basept →
      Odd (Nat.card ↥(MulAction.stabilizer G hyp.basept ⊓ MulAction.stabilizer G ω)) := by
    intro ω hω
    set ω' := hyp.t • hyp.basept with hω'_def
    have hω'_ne : ω' ≠ hyp.basept := fun h =>
      hyp.t_not_mem_H (hyp.H_def ▸ MulAction.mem_stabilizer_iff.mpr h)
    obtain ⟨h, hhH, hhω⟩ := hHtrans ω' ω hω'_ne hω
    have hhbase : h • hyp.basept = hyp.basept :=
      MulAction.mem_stabilizer_iff.mp (hyp.H_def ▸ hhH)
    have hD_eq : hyp.D = MulAction.stabilizer G hyp.basept ⊓ MulAction.stabilizer G ω' := by
      rw [hyp.D_def, hyp.H_def, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    -- `G_basept ⊓ G_ω = h (G_basept ⊓ G_ω') h⁻¹ = h · D · h⁻¹`.
    have hconj_eq : MulAction.stabilizer G hyp.basept ⊓ MulAction.stabilizer G ω
        = (hyp.D).map (MulAut.conj h).toMonoidHom := by
      rw [hD_eq, Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective]
      congr 1
      · rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hhbase]
      · rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hhω]
    rw [hconj_eq,
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).symm.toEquiv]
    exact hyp.D_odd
  have hnormal_conj : ∀ (a b : G), b ∈ Fsub → a * b * a⁻¹ ∈ Fsub :=
    fun a b hb => (‹Fsub.Normal›).conj_mem b hb a
  -- An involution in `H` inverts `Fsub`: it acts fixed-point-freely on `Fsub ∖ {1}` (else it would
  -- lie in an odd two-point stabilizer), and a fixed-point-free order-`2` automorphism of an
  -- abelian
  -- group inverts it.
  have hinv_fix : ∀ u : G, u ∈ hyp.H → u ^ 2 = 1 → u ≠ 1 →
      ∀ f : G, f ∈ Fsub → u * f * u⁻¹ = f⁻¹ := by
    intro u huH hu2 hu1 f hf
    have hub : u • hyp.basept = hyp.basept := MulAction.mem_stabilizer_iff.mp (hyp.H_def ▸ huH)
    -- fixed-point-freeness on `Fsub ∖ {1}`.
    have hfpf : ∀ g : G, g ∈ Fsub → u * g * u⁻¹ = g → g = 1 := by
      intro g hg hσg
      by_contra hg1
      have hgb_ne : (g : G) • hyp.basept ≠ hyp.basept := fun h =>
        hg1 (hfreeF g 1 hg Fsub.one_mem (by simpa using h))
      have hug : u * g = g * u := mul_inv_eq_iff_eq_mul.mp hσg
      have hu_fix_gb : u • ((g : G) • hyp.basept) = (g : G) • hyp.basept := by
        rw [← mul_smul, hug, mul_smul, hub]
      have huK : u ∈ MulAction.stabilizer G hyp.basept ⊓
          MulAction.stabilizer G ((g : G) • hyp.basept) :=
        ⟨MulAction.mem_stabilizer_iff.mpr hub, MulAction.mem_stabilizer_iff.mpr hu_fix_gb⟩
      have hodd := h2pt_odd ((g : G) • hyp.basept) hgb_ne
      set K := MulAction.stabilizer G hyp.basept ⊓ MulAction.stabilizer G ((g : G) • hyp.basept)
      have hu2K : (⟨u, huK⟩ : ↥K) ^ 2 = 1 := by
        apply Subtype.ext; push_cast; exact hu2
      have hord1 : orderOf (⟨u, huK⟩ : ↥K) ∣ 1 := by
        have h2d : orderOf (⟨u, huK⟩ : ↥K) ∣ 2 := orderOf_dvd_of_pow_eq_one hu2K
        have hcd : orderOf (⟨u, huK⟩ : ↥K) ∣ Nat.card ↥K := orderOf_dvd_natCard _
        have hdg := Nat.dvd_gcd h2d hcd
        rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)] at hdg
      exact hu1 (congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord1)))
    -- `σ(f) · f` is `σ`-fixed (abelian + `σ² = 1`), hence trivial.
    have hσf_mem : u * f * u⁻¹ ∈ Fsub := hnormal_conj u f hf
    have hcommF : (u * f * u⁻¹) * f = f * (u * f * u⁻¹) := by
      have hc := congrArg (fun z : ↥Fsub => (z : G))
        (mul_comm (⟨u * f * u⁻¹, hσf_mem⟩ : ↥Fsub) (⟨f, hf⟩ : ↥Fsub))
      push_cast at hc; exact hc
    have huu : u * u = 1 := by have h := hu2; rwa [pow_two] at h
    have hkey : u * ((u * f * u⁻¹) * f) * u⁻¹ = (u * f * u⁻¹) * f := by
      have hfix_mid : u * (u * f * u⁻¹) * u⁻¹ = f := by
        have : u * (u * f * u⁻¹) * u⁻¹ = (u * u) * f * (u⁻¹ * u⁻¹) := by group
        rw [this, huu, one_mul,
          show u⁻¹ * u⁻¹ = 1 from by rw [← mul_inv_rev, huu, inv_one], mul_one]
      calc u * ((u * f * u⁻¹) * f) * u⁻¹
          = (u * (u * f * u⁻¹) * u⁻¹) * (u * f * u⁻¹) := by group
        _ = f * (u * f * u⁻¹) := by rw [hfix_mid]
        _ = (u * f * u⁻¹) * f := hcommF.symm
    have hzero := hfpf ((u * f * u⁻¹) * f) (Fsub.mul_mem hσf_mem hf) hkey
    -- `u f u⁻¹ · f = 1` ⟹ `u f u⁻¹ = f⁻¹`.
    exact eq_inv_of_mul_eq_one_left (by rw [← hzero])
  -- Every involution of `G` has a fixed point on `Ω` (odd degree).
  have hfix_exists : ∀ u : G, u ^ 2 = 1 → u ≠ 1 → ∃ ω : Ω, u • ω = ω := by
    intro u hu2 hu1
    have hP2 : IsPGroup 2 ↥(Subgroup.zpowers u) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1, pow_one]
    have hmod := hP2.card_modEq_card_fixedPoints Ω
    have hfix_ne : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers u) Ω) ≠ 0 := by
      intro h0
      rw [h0] at hmod
      exact (Nat.not_even_iff_odd.mpr hΩodd)
        (even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hmod))
    obtain ⟨⟨ω, hω⟩⟩ := (Nat.card_ne_zero.mp hfix_ne).1
    exact ⟨ω, hω ⟨u, Subgroup.mem_zpowers u⟩⟩
  -- Every involution inverts `Fsub` (conjugate a fixed point to `basept`, apply `hinv_fix`).
  have hinv_all : ∀ u : G, u ^ 2 = 1 → u ≠ 1 → ∀ f : G, f ∈ Fsub → u * f * u⁻¹ = f⁻¹ := by
    intro u hu2 hu1 f hf
    obtain ⟨ω₀, hω₀⟩ := hfix_exists u hu2 hu1
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq hyp.basept ω₀
    set u0 := g⁻¹ * u * g with hu0_def
    have hu0H : u0 ∈ hyp.H := by
      rw [hyp.H_def, MulAction.mem_stabilizer_iff, hu0_def, mul_smul, mul_smul, hg, hω₀,
        inv_smul_eq_iff]
      exact hg.symm
    have hu02 : u0 ^ 2 = 1 := by
      rw [hu0_def, pow_two, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g from by group,
        ← pow_two, hu2]; group
    have hu01 : u0 ≠ 1 := by
      intro h
      exact hu1 (by
        rw [show u = g * u0 * g⁻¹ from by rw [hu0_def]; group, h, mul_one, mul_inv_cancel])
    have hgfg : g⁻¹ * f * g ∈ Fsub := by
      have := hnormal_conj g⁻¹ f hf; rwa [inv_inv] at this
    have hinv0 := hinv_fix u0 hu0H hu02 hu01 (g⁻¹ * f * g) hgfg
    rw [show u = g * u0 * g⁻¹ from by rw [hu0_def]; group]
    calc (g * u0 * g⁻¹) * f * (g * u0 * g⁻¹)⁻¹
        = g * (u0 * (g⁻¹ * f * g) * u0⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * f * g)⁻¹ * g⁻¹ := by rw [hinv0]
      _ = f⁻¹ := by group
  refine ⟨?_, ?_⟩
  · -- `H` has a unique involution: it exists (`|H|` even, Cauchy) and any two involutions of `H`
    -- both invert `Fsub`, so their product centralizes `Fsub`, lies in `C_G(Fsub) ⊓ H = 1`.
    have hHeven : 2 ∣ Nat.card ↥hyp.H :=
      dvd_trans hyp.Q_even.two_dvd (Subgroup.card_dvd_of_le hyp.Q_le_H)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥hyp.H) 2 hHeven
    have hx2 : (x : G) ^ 2 = 1 := by
      have hxpow : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      have hc := congrArg (fun z : ↥hyp.H => (z : G)) hxpow
      push_cast at hc; exact hc
    have hxne1 : x ≠ 1 := by intro h; rw [h, orderOf_one] at hx; omega
    have hx1 : (x : G) ≠ 1 := fun h => hxne1 (by ext; simpa using h)
    refine ⟨x, ⟨hx2, hx1⟩, ?_⟩
    rintro y ⟨hy2, hy1⟩
    have hxinv := hinv_fix (x : G) x.2 hx2 hx1
    have hyinv := hinv_fix (y : G) y.2 hy2 hy1
    have hyy : (y : G)⁻¹ = (y : G) := mul_eq_one_iff_inv_eq.mp (by rw [← pow_two]; exact hy2)
    have hcent : ((y : G)⁻¹ * (x : G)) ∈ Subgroup.centralizer (Fsub : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hconj : ((y : G)⁻¹ * (x : G)) * s * ((y : G)⁻¹ * (x : G))⁻¹ = s := by
        rw [hyy]
        calc (y : G) * (x : G) * s * ((y : G) * (x : G))⁻¹
            = (y : G) * ((x : G) * s * (x : G)⁻¹) * (y : G)⁻¹ := by group
          _ = (y : G) * s⁻¹ * (y : G)⁻¹ := by rw [hxinv s hs]
          _ = ((y : G) * s * (y : G)⁻¹)⁻¹ := by group
          _ = s := by rw [hyinv s hs, inv_inv]
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    have hmem : (y : G)⁻¹ * (x : G) ∈ Fsub ⊓ hyp.H :=
      ⟨hCF_le hcent, hyp.H.mul_mem (hyp.H.inv_mem y.2) x.2⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem)
  · -- For distinct involutions `u ≠ v`: both invert `Fsub`, so `u v` centralizes `Fsub`, lies in
    -- `C_G(Fsub) ≤ Fsub` and is `≠ 1`; being in the exponent-`p` group `Fsub`, `|u v| = p`.
    intro u v hu2 hu1 hv2 hv1 huv
    have huinv := hinv_all u hu2 hu1
    have hvinv := hinv_all v hv2 hv1
    have hcent : (u * v) ∈ Subgroup.centralizer (Fsub : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hconj : (u * v) * s * (u * v)⁻¹ = s := by
        calc (u * v) * s * (u * v)⁻¹ = u * (v * s * v⁻¹) * u⁻¹ := by group
          _ = u * s⁻¹ * u⁻¹ := by rw [hvinv s hs]
          _ = (u * s * u⁻¹)⁻¹ := by group
          _ = s := by rw [huinv s hs, inv_inv]
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    have huvF : u * v ∈ Fsub := hCF_le hcent
    have huv1 : u * v ≠ 1 := by
      intro h
      apply huv
      have h1 : u⁻¹ = v := mul_eq_one_iff_inv_eq.mp h
      have h2 : u⁻¹ = u := mul_eq_one_iff_inv_eq.mp (by rw [← pow_two]; exact hu2)
      rw [← h1, h2]
    refine ⟨huvF, ?_⟩
    have hdvd : orderOf (u * v) ∣ p := orderOf_dvd_of_pow_eq_one (hexp _ huvF)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) huv1
    · exact hp'

/-- **Peterfalvi Appendix II, Proposition 1** (p. 137).  If `G` satisfies (A1) and (A2) and has
2-rank `1`, then `G` is the affine group of a finite near-field: there is a near-field `F` and a
group `Σ` of automorphisms of `F` with `G ≅ 𝓛(F) ⋊ Σ = (F ⋊ F^*) ⋊ Σ`, identifying `Q` with `F^*`
and `D` with `Σ`.  Moreover `H` has a unique involution and, for distinct involutions `u, v ∈ G`,
`|uv|` equals the characteristic of `F`.

The near-field carrier is `F = Additive ↥Fsub`, where `Fsub` is the elementary abelian regular
normal subgroup of `G` (`exists_regular_normal`, via Brauer–Suzuki (ii)); its near-field structure
is transported from the sharply transitive conjugation action of `Q` on `F ∖ {1}`
(`exists_conj_regular` + `SharplyTransitiveData.nearField`).  The identifications are the actual
data: `emb` embeds `(F, +) = Fsub` into `G`; `qEquiv = mulEquivUnits` realizes `Q ≃* Fˣ`; the
conjugation-to-right-multiplication compatibility is `mul_mulEquivUnits_inv`; `D` acts by near-field
automorphisms via conjugation (using that `D` normalizes `Q` (`Q_normal_in_H`) and fixes `e`).

The three involution clauses are `model_involution_data`; the sole remaining gap is the residual
`Q₈` case of Brauer–Suzuki (inside `brauerSuzuki`), off the Feit–Thompson critical path. -/
theorem rankOne_affine_nearField.{u} {G : Type u} {Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) :
    ∃ (F : Type u) (_ : NearField F), Nonempty (AffineNearFieldModel hyp F) := by
  classical
  have := hyp.faithful
  -- Brauer–Suzuki (ii) discharges the odd-core hypothesis (`Q₈` case sorried inside).
  have hbs := hyp.brauerSuzuki
  -- Regular normal elementary abelian `F ⊴ G` with `G = F ⋊ H`.
  obtain ⟨p, Fsub, hp, hFnormal, hcomm, hexp, htrans, hcompl, hFodd⟩ :=
    hyp.exists_regular_normal hbs
  have : Fsub.Normal := hFnormal
  have : IsMulCommutative ↥Fsub := hcomm
  have hdisj : Disjoint Fsub hyp.H := hcompl.disjoint
  -- Conjugation-regular datum: identity `e` and the regular `Q`-action on `F ∖ {1}`.
  obtain ⟨e, heF, he_smul, hreg⟩ := hyp.exists_conj_regular htrans hdisj
  -- Conjugation actions of `Q` and `D` on the additive group `A = Additive ↥Fsub`.
  let actQ : DistribMulAction ↥hyp.Q (Additive ↥Fsub) := conjAdditiveAction Fsub hyp.Q
  let actD : DistribMulAction ↥hyp.D (Additive ↥Fsub) := conjAdditiveAction Fsub hyp.D
  set eA : Additive ↥Fsub := Additive.ofMul ⟨e, heF⟩ with heA_def
  -- `.toMul`-then-embed is injective on `A`.
  have htoMul_inj : ∀ a b : Additive ↥Fsub,
      ((Additive.toMul a : ↥Fsub) : G) = ((Additive.toMul b : ↥Fsub) : G) → a = b := by
    intro a b h
    have h2 : (Additive.toMul a : ↥Fsub) = Additive.toMul b := Subtype.ext h
    rw [← ofMul_toMul a, ← ofMul_toMul b, h2]
  -- `eA ≠ 0`, because `e • basept = t • basept ≠ basept`.
  have heA_ne : eA ≠ 0 := by
    intro h
    apply hyp.t_not_mem_H
    rw [hyp.H_def, MulAction.mem_stabilizer_iff, ← he_smul]
    have he1 : (⟨e, heF⟩ : ↥Fsub) = 1 := by
      have h' := congrArg Additive.toMul h
      simpa [heA_def] using h'
    rw [show e = ((⟨e, heF⟩ : ↥Fsub) : G) from rfl, he1, Subgroup.coe_one, one_smul]
  -- bridge: `q • eA = y  ↔  (q) e (q)⁻¹ = (toMul y)` (conjugation is the smul, definitionally).
  have hEq : ∀ (q : ↥hyp.Q) (y : Additive ↥Fsub),
      (q • eA = y) ↔ ((q : G) * e * (q : G)⁻¹ = ((Additive.toMul y : ↥Fsub) : G)) := by
    intro q y
    constructor
    · intro h
      have hc := conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.Q) q eA
      rw [h] at hc; exact hc.symm
    · intro h
      apply htoMul_inj
      rw [conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.Q) q eA]; exact h
  -- The sharply transitive datum: `Q` acts regularly on `A ∖ {0}` (via `hreg`).
  let data : SharplyTransitiveData ↥hyp.Q (Additive ↥Fsub) :=
    { e := eA
      e_ne_zero := heA_ne
      reg := by
        intro y hy
        have hf1 : ((Additive.toMul y : ↥Fsub) : G) ≠ 1 := by
          intro h
          apply hy
          have h2 : (Additive.toMul y : ↥Fsub) = 1 := Subtype.ext h
          rw [← ofMul_toMul y, h2]; rfl
        obtain ⟨q, hq, huniq⟩ := hreg _ (Additive.toMul y).2 hf1
        exact ⟨q, (hEq q y).mpr hq, fun q' hq' => huniq q' ((hEq q' y).mp hq')⟩ }
  let hNF : NearField (Additive ↥Fsub) := data.nearField
  -- The embedding `Multiplicative (Additive ↥Fsub) →* G` (= `Fsub ↪ G` under type tags).
  let emb : Multiplicative (Additive ↥Fsub) →* G :=
    { toFun := fun x => ((Additive.toMul (Multiplicative.toAdd x) : ↥Fsub) : G)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hemb_apply : ∀ z : Additive ↥Fsub,
      emb (Multiplicative.ofAdd z) = ((Additive.toMul z : ↥Fsub) : G) := fun _ => rfl
  have hrange : MonoidHom.range emb = Fsub := by
    ext g
    constructor
    · rintro ⟨z, rfl⟩; exact SetLike.coe_mem _
    · intro hg; exact ⟨Multiplicative.ofAdd (Additive.ofMul ⟨g, hg⟩), rfl⟩
  -- `D ≤ H`, and `D` fixes both `basept` and `ω' = t • basept` (two-point stabilizer).
  have hD_le_H : hyp.D ≤ hyp.H := by rw [hyp.D_def]; exact inf_le_left
  have hD_eq : hyp.D = MulAction.stabilizer G hyp.basept ⊓
      MulAction.stabilizer G (hyp.t • hyp.basept) := by
    rw [hyp.D_def, hyp.H_def, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hDfix_base : ∀ g : ↥hyp.D, (g : G) • hyp.basept = hyp.basept := by
    intro g
    have hg : (g : G) ∈ hyp.H := hD_le_H g.2
    rw [hyp.H_def] at hg
    exact MulAction.mem_stabilizer_iff.mp hg
  have hDfix_ω' : ∀ g : ↥hyp.D, (g : G) • (hyp.t • hyp.basept) = hyp.t • hyp.basept := by
    intro g
    have hmem : (↑g : G) ∈ MulAction.stabilizer G hyp.basept ⊓
        MulAction.stabilizer G (hyp.t • hyp.basept) := by rw [← hD_eq]; exact g.2
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hmem).2
  -- `Fsub` acts freely at `basept` (disjoint from `H = stabilizer basept`).
  have hfreeF : ∀ a b : G, a ∈ Fsub → b ∈ Fsub → a • hyp.basept = b • hyp.basept → a = b := by
    intro a b haF hbF hab
    have hmem : b⁻¹ * a ∈ Fsub ⊓ hyp.H :=
      ⟨Fsub.mul_mem (Fsub.inv_mem hbF) haF, hyp.H_def ▸ MulAction.mem_stabilizer_iff.mpr (by
        rw [mul_smul, hab, ← mul_smul, inv_mul_cancel, one_smul])⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  -- `e` is `D`-fixed: `(g) e (g)⁻¹ = e` for `g ∈ D` (the multiplicative identity is the `D`-fixed
  -- point of `F ∖ {1}`).
  have heDfix : ∀ g : ↥hyp.D, (g : G) * e * (g : G)⁻¹ = e := by
    intro g
    refine hfreeF _ _ (hFnormal.conj_mem e heF (g : G)) heF ?_
    have hginv : (g : G)⁻¹ • hyp.basept = hyp.basept := by
      rw [inv_smul_eq_iff]; exact (hDfix_base g).symm
    calc ((g : G) * e * (g : G)⁻¹) • hyp.basept
        = (g : G) • (e • ((g : G)⁻¹ • hyp.basept)) := by rw [mul_smul, mul_smul]
      _ = (g : G) • (e • hyp.basept) := by rw [hginv]
      _ = (g : G) • (hyp.t • hyp.basept) := by rw [he_smul]
      _ = hyp.t • hyp.basept := hDfix_ω' g
      _ = e • hyp.basept := he_smul.symm
  refine ⟨Additive ↥Fsub, hNF, ⟨?_⟩⟩
  refine
    { emb := emb
      emb_injective := by
        intro a b h
        have h1 : (Additive.toMul (Multiplicative.toAdd a) : ↥Fsub)
            = Additive.toMul (Multiplicative.toAdd b) := Subtype.ext h
        have := congrArg (fun f : ↥Fsub => Multiplicative.ofAdd (Additive.ofMul f)) h1
        simpa using this
      range_normal := by rw [hrange]; exact hFnormal
      isComplement := by rw [hrange]; exact hcompl
      qEquiv := data.mulEquivUnits
      qEquiv_conj := ?_
      dAut := fun g => DistribMulAction.toAddEquiv (Additive ↥Fsub) g
      dAut_mul := ?_
      dAut_injective := ?_
      dAut_conj := ?_
      unique_involution_in_H := (hyp.model_involution_data hp htrans hcompl hexp hFodd).1
      char := p
      char_prime := hp
      char_spec := ?_
      orderOf_mul_of_involutions := fun u v hu2 hu1 hv2 hv1 huv =>
        ((hyp.model_involution_data hp htrans hcompl hexp hFodd).2 u v hu2 hu1 hv2 hv1 huv).2
      mul_involutions_mem_range := fun u v hu2 hu1 hv2 hv1 huv => by
        rw [hrange]
        exact ((hyp.model_involution_data hp htrans hcompl hexp hFodd).2
          u v hu2 hu1 hv2 hv1 huv).1 }
  · -- qEquiv_conj: conjugation by `q` = right mult by `qEquiv q⁻¹` (`mul_mulEquivUnits_inv`).
    intro q x
    simp only [hemb_apply]
    change (q : G) * ((Additive.toMul x : ↥Fsub) : G) * (q : G)⁻¹
      = ((Additive.toMul (data.mul x
          ((data.mulEquivUnits q⁻¹ : (Additive ↥Fsub)ˣ) : Additive ↥Fsub)) : ↥Fsub) : G)
    rw [data.mul_mulEquivUnits_inv q x, conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.Q) q x]
  · -- dAut_mul: `D` acts by near-field automorphisms.  Uses `Q_normal_in_H` (so `data.coord`
    -- transports by conjugation) and that `e` is `D`-fixed (`heDfix`).
    intro g x y
    change (g : ↥hyp.D) • data.mul x y
      = data.mul ((g : ↥hyp.D) • x) ((g : ↥hyp.D) • y)
    by_cases hy : y = 0
    · subst hy; rw [data.mul_zero, smul_zero, data.mul_zero]
    · have hgy : (g : ↥hyp.D) • y ≠ 0 := fun h => hy (by rw [← inv_smul_smul g y, h, smul_zero])
      have hmemQ : (g : G) * (data.coord y : G) * (g : G)⁻¹ ∈ hyp.Q :=
        hyp.Q_normal_in_H (g : G) (hD_le_H g.2) (data.coord y : G) (data.coord y).2
      have hgeInv : (g : G)⁻¹ * e * (g : G) = e := by
        have h := heDfix g
        have h2 : (g : G)⁻¹ * ((g : G) * e * (g : G)⁻¹) * (g : G) = (g : G)⁻¹ * e * (g : G) := by
          rw [h]
        rw [← h2]; group
      have hy2 : ((Additive.toMul y : ↥Fsub) : G)
          = (data.coord y : G) * e * (data.coord y : G)⁻¹ := by
        have h := congrArg (fun z : Additive ↥Fsub => ((Additive.toMul z : ↥Fsub) : G))
          (data.coord_smul_e hy)
        rw [conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.Q)] at h
        exact h.symm
      have hcoordD : data.coord ((g : ↥hyp.D) • y)
          = ⟨(g : G) * (data.coord y : G) * (g : G)⁻¹, hmemQ⟩ := by
        refine (data.coord_unique hgy ?_).symm
        apply htoMul_inj
        rw [conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.Q)
              ⟨(g : G) * (data.coord y : G) * (g : G)⁻¹, hmemQ⟩ eA,
            conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.D) g y, hy2]
        change ((g : G) * (data.coord y : G) * (g : G)⁻¹) * e
            * ((g : G) * (data.coord y : G) * (g : G)⁻¹)⁻¹
          = (g : G) * ((data.coord y : G) * e * (data.coord y : G)⁻¹) * (g : G)⁻¹
        calc ((g : G) * (data.coord y : G) * (g : G)⁻¹) * e
              * ((g : G) * (data.coord y : G) * (g : G)⁻¹)⁻¹
            = (g : G) * (data.coord y : G) * ((g : G)⁻¹ * e * (g : G))
                * ((data.coord y : G)⁻¹ * (g : G)⁻¹) := by group
          _ = (g : G) * (data.coord y : G) * e * ((data.coord y : G)⁻¹ * (g : G)⁻¹) := by
                rw [hgeInv]
          _ = (g : G) * ((data.coord y : G) * e * (data.coord y : G)⁻¹) * (g : G)⁻¹ := by group
      rw [data.mul_def hy, data.mul_def hgy, hcoordD]
      apply htoMul_inj
      rw [conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.D) g (data.coord y • x),
        conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.Q)
          ⟨(g : G) * (data.coord y : G) * (g : G)⁻¹, hmemQ⟩ ((g : ↥hyp.D) • x),
        conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.Q) (data.coord y) x,
        conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.D) g x]
      change (g : G) * ((data.coord y : G) * ((Additive.toMul x : ↥Fsub) : G)
            * (data.coord y : G)⁻¹) * (g : G)⁻¹
        = ((g : G) * (data.coord y : G) * (g : G)⁻¹)
            * ((g : G) * ((Additive.toMul x : ↥Fsub) : G) * (g : G)⁻¹)
            * ((g : G) * (data.coord y : G) * (g : G)⁻¹)⁻¹
      group
  · -- dAut_injective: `dAut g = dAut g'` ⟹ `g, g'` conjugate `Fsub` identically ⟹ agree on `Ω`.
    intro g g' h
    apply Subtype.ext
    refine eq_of_smul_eq_smul (α := Ω) fun ω => ?_
    obtain ⟨f, hf⟩ := htrans.exists_smul_eq hyp.basept ω
    have hconj : (g : G) * (f : G) * (g : G)⁻¹ = (g' : G) * (f : G) * (g' : G)⁻¹ := by
      have hfun : (g : ↥hyp.D) • Additive.ofMul f = (g' : ↥hyp.D) • Additive.ofMul f :=
        DFunLike.congr_fun h (Additive.ofMul f)
      have h2 := congrArg (fun z : Additive ↥Fsub => ((Additive.toMul z : ↥Fsub) : G)) hfun
      rw [conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.D) g (Additive.ofMul f),
        conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.D) g' (Additive.ofMul f),
        toMul_ofMul] at h2
      exact h2
    have hfG : (f : G) • hyp.basept = ω := hf
    have key : ∀ d : ↥hyp.D, (d : G) • ω = ((d : G) * (f : G) * (d : G)⁻¹) • hyp.basept := by
      intro d
      rw [← hfG, ← mul_smul]
      conv_rhs => rw [← hDfix_base d, ← mul_smul]
      congr 1
      group
    rw [key g, key g', hconj]
  · -- dAut_conj: the `D`-action on `F` is conjugation inside `G` (definitionally).
    intro g x
    simp only [hemb_apply]
    change (g : G) * ((Additive.toMul x : ↥Fsub) : G) * (g : G)⁻¹
      = ((Additive.toMul ((g : ↥hyp.D) • x) : ↥Fsub) : G)
    rw [conjAdditiveAction_val_toMul (F := Fsub) (Q := hyp.D) g x]
  · -- char_spec: `p • x = 0`, i.e. `(toMul x) ^ p = 1` (exponent of the elementary abelian `Fsub`).
    intro x
    apply htoMul_inj
    rw [toMul_nsmul, Subgroup.coe_pow]
    exact hexp _ (Additive.toMul x).2

end PropositionOne

end OddOrder.Peterfalvi.Appendices.NearFields
