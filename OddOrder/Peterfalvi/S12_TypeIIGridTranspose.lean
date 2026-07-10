/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_TypeIIColumnPin
import OddOrder.FeitThompsonSetup

/-!
# Peterfalvi (8.8)/(10.7): the σ-agreement bridge for the type-P pair grid transpose

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §8 (8.8)
and §10 (10.7); Coq mirror `PFsection10.v` (`Frob_der1_type2`, the pair-witness route).

A type-P pair `(M, S)` shares the cyclic TI-structure `W = W₁ × W₂` with the roles of `W₁`
and `W₂` swapped ((8.8): `S ∩ M = W`).  Consequently the `M`-side and `S`-side (3.1) setups
(`TICyclicHypothesis`) have the *same* underlying TI-set `V = W ∖ (W₁ ∪ W₂)` and the same
`W`, and by the uniqueness of the Dade map (Peterfalvi (2.5), `S04.IsDadeMap.unique`) their
(3.2) Dade isometries agree.  This file proves that agreement in an entirely cast-free way,
as the bridge for identifying the `S`-side σ-grid (`certainTypeOmegaSigma`) with the
`M`-side grid (`alignedOmegaSigmaGrid`) up to the index swap — the "grid transpose" of the
(10.7) pair-witness route (issue 9079, part 1).

## Main statements

* `dadeMap_unique_of_forall_H_eq_bot`: two Dade maps for two (possibly different) TI-special
  (2.2) hypotheses on the same `(A, L)` coincide — cross-`Hypothesis` form of
  `S04.IsDadeMap.unique` (the `H` fields are all `⊥`, and every other field is a proof, so
  the two hypotheses are equal).
* `ticyclic_toDadeMap_eq_of_V_eq` (**core**): for `hyp₁ hyp₂ : TICyclicHypothesis G` with
  `hyp₁.V = hyp₂.V`, the full Dade maps agree on supported class functions with equal
  `V`-values.  Stated pointwise (two arguments `α₁, α₂` agreeing on `V`), which avoids all
  type transport: the TI-specialized (2.5) map is determined by `V` and `α|_V` alone.
* `ticyclicSupportedOnVCongr`: the transport `CF(W,V)(hyp₁) → CF(W,V)(hyp₂)` along
  `hyp₁.V = hyp₂.V`, `hyp₁.W = hyp₂.W`, implemented by value-restriction
  (`ClassFunction.compHom` along `Subgroup.inclusion`), not by `Eq.rec` — so applications
  reduce definitionally (`ticyclicSupportedOnVCongr_coe_apply` is `rfl`).
* `ticyclic_sigma_eq_of_V_eq` / `ticyclic_sigma_congr_eq`: the (3.2) `σ`'s of the two setups
  agree **on `V`-supported class functions** (through `sigma_eq_tau`).
* `ticyclic_Vdiff_eq_of_swap` / `ticyclic_V_eq_of_swap`: `V = W ∖ (W₁ ∪ W₂)` is invariant
  under the pair's role swap `W₁ ↔ W₂` (issue 9079 item (ii), the `V`-sharing input).
* `section16_partner_typePData_W2_eq` / `section16_pair_tic_V_eq` /
  `section16_pair_sigma_eq`: the (8.8) canonical-pair packaging — an `mp.T`-side `TypePData`
  whose `W₁` is the dual factor `mp.Kstar` has `W₂ = mp.K` (the (8.4.b) centralizer law) and
  shares `W` and `V` with the reconciled `mp.S`-side `tp.Sdata`, so the two
  `typePData_toTICyclicHypothesis` bridges have equal Dade maps and σ's on `CF(W, V)`.

## Design note

On non-`V`-supported class functions (e.g. the grid characters `ω_{ij}` themselves) the two
`σ`'s are *not* identified by this file: `σ` is built from a choice of the (3.5) family
`chiFam`, and only its restriction to `CF(W, V)` is pinned by the Dade map (via
`sigma_eq_tau`).  Identifying the full grids requires the (3.5)-determination / coefficient
rigidity step ((3.7)-style), which is part 2 of the transpose (issue 9079).

For the canonical pair, only the `S`-side `TypePData` is canonically reconciled to the pair
factors (`tp.Sdata` with `Sdata_W1_eq`; the `W₁`-prescribing producer
`exists_typePData_W1_eq_of_isTypeP2` is gated on type `P₂`, which `Section16MaximalPair`
pins only for `S` via `S_typeP2`).  The pair lemmas therefore take the `T`-side datum as a
hypothesis `(dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)` — the exact shape that
producer emits — and derive everything else; see issue 9079 for the sourcing gap record.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

section GenericBridge

variable [Fintype G]

/- (2.5) uniqueness across two TI-special hypotheses on the same `(A, L)` -/

/-- Two Peterfalvi (2.2) hypotheses on the same `(A, L)` whose `H`-fields are all trivial are
**equal**: `H` is the only data field of `S04.Hypothesis`, every other field being a proof.
This is what makes the Dade hypothesis of a TI-setup canonical — e.g. the `M`-side and
`S`-side `toDadeHypothesis` of a type-P pair coincide once `V` and `W` do. -/
theorem dadeHypothesis_eq_of_forall_H_eq_bot {A : Set G} {L : Subgroup G}
    {hyp hyp' : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (hH : ∀ a, hyp.H a = ⊥) (hH' : ∀ a, hyp'.H a = ⊥) : hyp = hyp' := by
  obtain ⟨s₁, l₁, n₁, H₁, c₁, ce₁, cd₁, hn₁, cc₁⟩ := hyp
  obtain ⟨s₂, l₂, n₂, H₂, c₂, ce₂, cd₂, hn₂, cc₂⟩ := hyp'
  have hHeq : H₁ = H₂ := funext fun a => (hH a).trans (hH' a).symm
  subst hHeq
  rfl

/-- **Peterfalvi (2.5), cross-hypothesis uniqueness** (TI-special case): candidate Dade maps
for two — possibly differently packaged — hypotheses on the same `(A, L)`, both with all
`H(a) = 1`, agree.  Reduces to `S04.IsDadeMap.unique` through
`dadeHypothesis_eq_of_forall_H_eq_bot`. -/
theorem dadeMap_unique_of_forall_H_eq_bot {k : Type*} [CommRing k]
    {A : Set G} {L : Subgroup G}
    {hyp hyp' : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    {τ₁ τ₂ : OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L}
    (h₁ : OddOrder.Peterfalvi.S04.IsDadeMap hyp τ₁)
    (h₂ : OddOrder.Peterfalvi.S04.IsDadeMap hyp' τ₂)
    (hH : ∀ a, hyp.H a = ⊥) (hH' : ∀ a, hyp'.H a = ⊥) : τ₁ = τ₂ := by
  rw [← dadeHypothesis_eq_of_forall_H_eq_bot hH hH'] at h₂
  exact h₁.unique h₂

/- Transport of `CF(W, V)` along `V`- and `W`-equalities -/

/-- Transport `CF(W, V)` along equalities `hyp₁.V = hyp₂.V`, `hyp₁.W = hyp₂.W` of the
underlying TI data, by **value restriction** (`ClassFunction.compHom` along
`Subgroup.inclusion hW.ge`) rather than by `Eq.rec` — so evaluating the transported function
is definitional (`ticyclicSupportedOnVCongr_coe_apply` is `rfl`) and no `HEq`/motive issues
ever arise downstream. -/
def ticyclicSupportedOnVCongr {k : Type*} [CommRing k]
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV k hyp₁) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV k hyp₂ :=
  ⟨ClassFunction.compHom (Subgroup.inclusion hW.ge) (α : ClassFunction ↥hyp₁.W k), by
    rw [ClassFunction.mem_supportedSubmodule]
    intro w hw
    rw [ClassFunction.mem_support, ClassFunction.compHom_apply] at hw
    have hmem := ClassFunction.mem_supportedSubmodule.mp α.2
      (ClassFunction.mem_support.mpr hw)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, ← hV]
    simpa using hmem⟩

@[simp] theorem ticyclicSupportedOnVCongr_coe_apply {k : Type*} [CommRing k]
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV k hyp₁) (w : ↥hyp₂.W) :
    (ticyclicSupportedOnVCongr hyp₁ hyp₂ hV hW α : ClassFunction ↥hyp₂.W k) w
      = (α : ClassFunction ↥hyp₁.W k) ⟨(w : G), hW.ge w.2⟩ :=
  rfl

/- The role swap `W₁ ↔ W₂` fixes the TI-set `V = W ∖ (W₁ ∪ W₂)` (issue 9079 item (ii)) -/

/-- **Peterfalvi (8.8), swap-invariance of the exceptional set**: `Vdiff = W ∖ (W₁ ∪ W₂)`
only sees the *unordered* pair `{W₁, W₂}`, so two TI-cyclic setups with the same `W` and the
roles of `W₁`/`W₂` exchanged (the (8.8) pair situation, `S ∩ M = W = W₁ × W₂` with swapped
factors) have the same `Vdiff` — just `Set.union_comm`. -/
theorem ticyclic_Vdiff_eq_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1) :
    hyp₁.Vdiff = hyp₂.Vdiff := by
  simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.Vdiff]
  rw [hW, hW12, hW21, Set.union_comm (hyp₂.W2 : Set G) (hyp₂.W1 : Set G)]

/-- **Peterfalvi (8.8), the pair shares its TI-set**: two TI-cyclic setups in the `Vdiff`
shape (`hVeq₁`, `hVeq₂`) with the same `W` and swapped `W₁`/`W₂` have equal `V`.  This is
the `hV` input of the σ-agreement bridge (`ticyclic_toDadeMap_eq_of_V_eq`,
`ticyclic_sigma_eq_of_V_eq`) in the (10.7) grid-transpose situation. -/
theorem ticyclic_V_eq_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1) :
    hyp₁.V = hyp₂.V :=
  hVeq₁.trans ((ticyclic_Vdiff_eq_of_swap hyp₁ hyp₂ hW hW12 hW21).trans hVeq₂.symm)

variable [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (2.5)/(3.2), independence of the packaging**: any two `FullDadeApplication`s
of one TI-cyclic hypothesis have the same Dade map (`S04.IsDadeMap.unique` at the canonical
`toDadeHypothesis`).  The `σ` of (3.2) is pinned by this only on `CF(W, V)` (see the design
note in the module docstring). -/
theorem ticyclic_toDadeMap_apply_eq (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app₁ app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp) :
    app₁.tau.toDadeMap α = app₂.tau.toDadeMap α :=
  congrFun (OddOrder.Peterfalvi.S04.IsDadeMap.unique
    app₁.tau.toDadeIsometryData.isDadeMap app₂.tau.toDadeIsometryData.isDadeMap) α

/- The σ-agreement bridge: same TI-set `V` ⟹ same Dade map, pointwise form -/

/-- **The σ-agreement bridge, core form (Peterfalvi (2.5) uniqueness for (8.8) pairs)**: if
two TI-cyclic setups share the TI-set (`hyp₁.V = hyp₂.V`), their full Dade maps agree on
supported class functions with equal values on `V`.

Stated pointwise — `α₁ ∈ CF(W₁ᵗᵒᵗ, V)`, `α₂ ∈ CF(W₂ᵗᵒᵗ, V)` with
`α₁(v) = α₂(v)` for `v ∈ V` — so that **no type transport** between the two supported
spaces is needed; the two sides even keep possibly different ambient `W`'s.  Honest content:
the TI-specialized Dade map is `α(a)` on conjugates of `a ∈ V` and `0` elsewhere, so it
depends only on `V` and `α|_V`. -/
theorem ticyclic_toDadeMap_eq_of_V_eq
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    (hV : hyp₁.V = hyp₂.V)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (α₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp₁)
    (α₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp₂)
    (hα : ∀ (v : G) (hv₁ : v ∈ hyp₁.V) (hv₂ : v ∈ hyp₂.V),
      (α₁ : ClassFunction ↥hyp₁.W ℂ) ⟨v, hyp₁.V_subset_W hv₁⟩
        = (α₂ : ClassFunction ↥hyp₂.W ℂ) ⟨v, hyp₂.V_subset_W hv₂⟩) :
    app₁.tau.toDadeMap α₁ = app₂.tau.toDadeMap α₂ := by
  ext g
  by_cases hg : g ∈ Group.conjugatesOfSet hyp₁.V
  · -- both sides are class functions; evaluate at the common `V`-representative
    obtain ⟨v, hv, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    rw [← (app₁.tau.toDadeMap α₁ : ClassFunction G ℂ).of_isConj hconj,
      ← (app₂.tau.toDadeMap α₂ : ClassFunction G ℂ).of_isConj hconj,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.full_map_eq_of_mem_V app₁ α₁ hv,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.full_map_eq_of_mem_V app₂ α₂ (hV ▸ hv)]
    exact hα v hv (hV ▸ hv)
  · -- off the (common) conjugates of `V` both Dade images vanish
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.full_map_eq_zero_of_not_mem_conjugatesOfSet_V
        app₁ α₁ hg,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.full_map_eq_zero_of_not_mem_conjugatesOfSet_V
        app₂ α₂ (hV ▸ hg)]

/-- The σ-agreement bridge in **transported form**: with both `V` and `W` shared, the second
Dade map applied to the transported class function returns the first.  Instance of
`ticyclic_toDadeMap_eq_of_V_eq` — the value-restriction transport agrees with `α` on `V` by
definitional proof irrelevance. -/
theorem ticyclic_toDadeMap_congr_eq
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp₁) :
    app₁.tau.toDadeMap α
      = app₂.tau.toDadeMap (ticyclicSupportedOnVCongr hyp₁ hyp₂ hV hW α) :=
  ticyclic_toDadeMap_eq_of_V_eq hyp₁ hyp₂ hV app₁ app₂ α
    (ticyclicSupportedOnVCongr hyp₁ hyp₂ hV hW α) (fun _ _ _ => rfl)

/- σ-agreement on `CF(W, V)` (through `sigma_eq_tau`) -/

/-- **Peterfalvi (3.2) σ-agreement on `CF(W, V)`, pointwise form**: two TI-cyclic setups
sharing the TI-set `V` have `σ`'s agreeing on supported class functions with equal
`V`-values — `σ = τ` on `CF(W, V)` (`sigma_eq_tau`) plus the Dade-map bridge
`ticyclic_toDadeMap_eq_of_V_eq`.  This is the σ-identification input of the (10.7) grid
transpose; on the *non-supported* grid characters themselves the identification needs the
(3.5)-determination step instead (see the module docstring). -/
theorem ticyclic_sigma_eq_of_V_eq
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hV : hyp₁.V = hyp₂.V)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (α₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp₁)
    (α₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp₂)
    (hα : ∀ (v : G) (hv₁ : v ∈ hyp₁.V) (hv₂ : v ∈ hyp₂.V),
      (α₁ : ClassFunction ↥hyp₁.W ℂ) ⟨v, hyp₁.V_subset_W hv₁⟩
        = (α₂ : ClassFunction ↥hyp₂.W ℂ) ⟨v, hyp₂.V_subset_W hv₂⟩) :
    hyp₁.sigma hVeq₁ app₁ (α₁ : ClassFunction ↥hyp₁.W ℂ)
      = hyp₂.sigma hVeq₂ app₂ (α₂ : ClassFunction ↥hyp₂.W ℂ) := by
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_eq_tau hyp₁ hVeq₁ app₁ α₁,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_eq_tau hyp₂ hVeq₂ app₂ α₂]
  exact ticyclic_toDadeMap_eq_of_V_eq hyp₁ hyp₂ hV app₁ app₂ α₁ α₂ hα

/-- **Peterfalvi (3.2) σ-agreement on `CF(W, V)`, transported form**: with both `V` and `W`
shared, `σ₂` applied to the transported supported class function returns `σ₁`'s value. -/
theorem ticyclic_sigma_congr_eq
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp₁) :
    hyp₁.sigma hVeq₁ app₁ (α : ClassFunction ↥hyp₁.W ℂ)
      = hyp₂.sigma hVeq₂ app₂
          ((ticyclicSupportedOnVCongr hyp₁ hyp₂ hV hW α) : ClassFunction ↥hyp₂.W ℂ) :=
  ticyclic_sigma_eq_of_V_eq hyp₁ hyp₂ hVeq₁ hVeq₂ hV app₁ app₂ α
    (ticyclicSupportedOnVCongr hyp₁ hyp₂ hV hW α) (fun _ _ _ => rfl)

end GenericBridge

/-! ## The (8.8) canonical-pair packaging (issue 9079 item (ii))

Instances of the generic bridge for the two `typePData_toTICyclicHypothesis` setups of the
canonical maximal pair `(mp.S, mp.T)`: the `S`-side datum is the reconciled `tp.Sdata`
(`Sdata_W1_eq : Sdata.W1 = tp.W1 = mp.K`), the `T`-side datum is any `TypePData mp.T` whose
`W₁` is the dual factor `mp.Kstar` (the shape `exists_typePData_W1_eq_of_isTypeP2` emits;
for `mp.T` its production is the remaining sourcing gap — see the module docstring and
issue 9079).  Its `W₂ = mp.K` is then *forced* by the (8.4.b) centralizer law, so the two
setups share `W = K ⊔ K*` and (by swap-invariance) the TI-set `V`. -/

section PairPackaging

open OddOrder.GroupTheory

/- projections of the §10 → §5 bridge (definitional; named for `rw`-chains) -/

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_W [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).W = data.W := rfl

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_W1 [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).W1 = data.W1 := rfl

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_W2 [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).W2 = data.W2 := rfl

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_V [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).V = typePV M data := rfl

open scoped FiniteInduce in
/-- The §10 → §5 bridge is in the `Vdiff` shape: `V = typePV = W ∖ (W₁ ∪ W₂)` definitionally.
This is the `hVeq` input of the (3.2) σ-machinery (`sigma`, `chiFam`), supplied as `rfl`
throughout the §10/§12 grid files. -/
theorem typePData_toTICyclicHypothesis_V_eq_Vdiff [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).V
      = (typePData_toTICyclicHypothesis data hodd).Vdiff := rfl

/-- **The (8.4.b) centralizer law pins the partner's dual factor**: a `TypePData` on the
canonical partner `mp.T` whose cyclic factor `W₁` is the pair's dual κ-Hall `mp.Kstar`
automatically has `W₂ = mp.K`.  Both are the `T'`-centralizer of any `x ∈ K*#`: `data.W₂`
by the `centralizer_W1` field, `mp.K` by BG Theorem A(5)
(`typeP_derivedInG_inf_centralizer_kappaElement_eq` with the pairing `mp.K_eq`). -/
theorem section16_partner_typePData_W2_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    dataT.W2 = mp.K := by
  -- a nonidentity element of the dual κ-Hall `K* ≠ ⊥`
  have hKstarne : mp.Kstar ≠ ⊥ := fun hbot =>
    OddOrder.BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
      (Subgroup.card_eq_one.mpr hbot)
  haveI := (Subgroup.nontrivial_iff_ne_bot mp.Kstar).mpr hKstarne
  obtain ⟨⟨x, hxK⟩, hxne⟩ := exists_ne (1 : ↥mp.Kstar)
  have hxne' : x ≠ 1 := fun h => hxne (Subtype.ext h)
  have hcen := dataT.centralizer_W1 x (hTW1.symm ▸ hxK) hxne'
  have hkstar := OddOrder.BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq hG
    mp.T_maximal mp.T_typeP mp.Kstar_le_T mp.Kstar_hall mp.K_eq x hxK hxne'
  exact hcen.symm.trans hkstar

/-- A `W₁`-reconciled partner `TypePData` has the pair's full cyclic factor:
`dataT.W = K ⊔ K*` (from `W = W₁ ⊔ W₂`, `W₁ = K*`, `W₂ = K`, and commutativity of `⊔`). -/
theorem section16_partner_typePData_W_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    dataT.W = mp.K ⊔ mp.Kstar := by
  rw [dataT.W_eq, hTW1, section16_partner_typePData_W2_eq hG dataT hTW1, sup_comm]

open scoped FiniteInduce in
/-- **The canonical pair shares its TI-set `V`** (Peterfalvi (8.8) for the §10 → §5
bridges): the `S`-side reconciled datum `tp.Sdata` and a `W₁`-reconciled `T`-side datum
give `TICyclicHypothesis`s with the *same* `V = W ∖ (K ∪ K*)` — the `W`-blocks agree up to
the role swap `W₁ ↔ W₂` (`S`-side `(K, K*)`, `T`-side `(K*, K)`), and `V` is
swap-invariant (`ticyclic_V_eq_of_swap`). -/
theorem section16_pair_tic_V_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) (hodd : Odd (Nat.card G))
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    (typePData_toTICyclicHypothesis tp.Sdata hodd).V
      = (typePData_toTICyclicHypothesis dataT hodd).V := by
  have hSW1 : tp.Sdata.W1 = mp.K :=
    tp.Sdata_W1_eq.trans (tp.W1_eq_K_and_W2_eq_Kstar hG).1
  have hSW2 : tp.Sdata.W2 = mp.Kstar :=
    tp.Sdata_W2_eq.trans (tp.W1_eq_K_and_W2_eq_Kstar hG).2
  have hTW2 : dataT.W2 = mp.K := section16_partner_typePData_W2_eq hG dataT hTW1
  refine ticyclic_V_eq_of_swap _ _ rfl rfl ?_ ?_ ?_
  · rw [typePData_toTICyclicHypothesis_W, typePData_toTICyclicHypothesis_W, tp.Sdata.W_eq,
      hSW1, hSW2, section16_partner_typePData_W_eq hG dataT hTW1]
  · rw [typePData_toTICyclicHypothesis_W1, typePData_toTICyclicHypothesis_W2, hSW1, hTW2]
  · rw [typePData_toTICyclicHypothesis_W2, typePData_toTICyclicHypothesis_W1, hSW2, hTW1]

open scoped FiniteInduce in
/-- **The canonical pair's Dade maps agree on `CF(W, V)`** (Peterfalvi (2.5) uniqueness for
the (8.8) pair): the `S`-side and `T`-side §10 → §5 bridges share `V`, so their full Dade
maps agree on supported class functions with equal `V`-values
(`ticyclic_toDadeMap_eq_of_V_eq` at `section16_pair_tic_V_eq`). -/
theorem section16_pair_toDadeMap_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) (hodd : Odd (Nat.card G))
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)
    (appS : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis tp.Sdata hodd))
    (appT : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis dataT hodd))
    (αS : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ
      (typePData_toTICyclicHypothesis tp.Sdata hodd))
    (αT : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ
      (typePData_toTICyclicHypothesis dataT hodd))
    (hα : ∀ (v : G) (hv₁ : v ∈ (typePData_toTICyclicHypothesis tp.Sdata hodd).V)
        (hv₂ : v ∈ (typePData_toTICyclicHypothesis dataT hodd).V),
      (αS : ClassFunction ↥(typePData_toTICyclicHypothesis tp.Sdata hodd).W ℂ)
          ⟨v, (typePData_toTICyclicHypothesis tp.Sdata hodd).V_subset_W hv₁⟩
        = (αT : ClassFunction ↥(typePData_toTICyclicHypothesis dataT hodd).W ℂ)
          ⟨v, (typePData_toTICyclicHypothesis dataT hodd).V_subset_W hv₂⟩) :
    appS.tau.toDadeMap αS = appT.tau.toDadeMap αT :=
  ticyclic_toDadeMap_eq_of_V_eq _ _ (section16_pair_tic_V_eq hG tp hodd dataT hTW1)
    appS appT αS αT hα

open scoped FiniteInduce in
/-- **The canonical pair's σ's agree on `CF(W, V)`** (issue 9079 item (ii), the pair
instance of the σ-agreement bridge): for the reconciled `S`-side `tp.Sdata` and a
`W₁`-reconciled `T`-side `TypePData`, the (3.2) isometries of the two
`typePData_toTICyclicHypothesis` setups take equal values on `V`-supported class functions
that agree on the shared `V`.  Combined with the (3.5) grid description
(`exists_alignedOmegaSigmaGrid_chiFam_family`) this is the cast-free entry point for the
`S`-grid = `M`-grid transpose of the (10.7) pair-witness route. -/
theorem section16_pair_sigma_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) (hodd : Odd (Nat.card G))
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)
    (appS : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis tp.Sdata hodd))
    (appT : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis dataT hodd))
    (αS : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ
      (typePData_toTICyclicHypothesis tp.Sdata hodd))
    (αT : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ
      (typePData_toTICyclicHypothesis dataT hodd))
    (hα : ∀ (v : G) (hv₁ : v ∈ (typePData_toTICyclicHypothesis tp.Sdata hodd).V)
        (hv₂ : v ∈ (typePData_toTICyclicHypothesis dataT hodd).V),
      (αS : ClassFunction ↥(typePData_toTICyclicHypothesis tp.Sdata hodd).W ℂ)
          ⟨v, (typePData_toTICyclicHypothesis tp.Sdata hodd).V_subset_W hv₁⟩
        = (αT : ClassFunction ↥(typePData_toTICyclicHypothesis dataT hodd).W ℂ)
          ⟨v, (typePData_toTICyclicHypothesis dataT hodd).V_subset_W hv₂⟩) :
    (typePData_toTICyclicHypothesis tp.Sdata hodd).sigma rfl appS
        (αS : ClassFunction ↥(typePData_toTICyclicHypothesis tp.Sdata hodd).W ℂ)
      = (typePData_toTICyclicHypothesis dataT hodd).sigma rfl appT
        (αT : ClassFunction ↥(typePData_toTICyclicHypothesis dataT hodd).W ℂ) :=
  ticyclic_sigma_eq_of_V_eq _ _ rfl rfl (section16_pair_tic_V_eq hG tp hodd dataT hTW1)
    appS appT αS αT hα

end PairPackaging

end OddOrder.Peterfalvi.S12
