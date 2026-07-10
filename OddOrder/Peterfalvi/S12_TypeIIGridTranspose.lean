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
* `exists_section16_partner_typePData`: the `T`-side **producer** — a `TypePData mp.T` with
  `W₁ = mp.Kstar` (hence `W₂ = mp.K`) exists, by Schur–Zassenhaus conjugation of the datum
  of `typePData_of_isTypeNonI` (no `IsTypeP2 mp.T` needed).  This discharges the hypothesis
  pair `(dataT, hTW1)` of the packaging lemmas above.
* `conj_eq_S_or_conj_eq_T_of_isTypeII` / `exists_conj_eq_S_of_isTypeII`: the (10.7)
  **reduction glue** — every type-II maximal subgroup is conjugate to `mp.S`, or to `mp.T`
  with the certificate `IsTypeII mp.T` (Peterfalvi (13.2.a) does not exclude a type-II
  partner; the strong form takes `¬ IsTypeII mp.T` as a hypothesis, mirroring Coq's
  contextual `notMtype2`).

* `ticyclic_eq_sigma_omega_of_eqOn_V`: the **(3.5)-determination** (Coq `eq_in_cycTIiso`) —
  a norm-one virtual character agreeing with the linear character `ω` on `V` *is* `ω^σ`.
  The grid vectors are pinned by their `V`-restrictions.
* `ticyclic_sigma_omega_eq_of_V_eq` / `section16_pair_sigma_omega_eq`: the **per-index
  σ-grid identification** (Coq `cycTIisoC`) — two setups sharing `V` and `W` (in
  particular the two sides of the canonical pair) have `σ₁(ω(ξ)) = σ₂(ω(ξ'))` with `ξ'`
  the value-restriction of `ξ` along the `W`-identification.  This is the grid transpose
  itself; what remains of issue 9079 part 2 is its translation into the named grids
  (`certainTypeOmegaSigma` ↔ `alignedOmegaSigmaGrid`) and the row-sum pin transfer
  (item 4).

## Design note

On non-`V`-supported class functions, `σ` is built from a choice of the (3.5) family
`chiFam`, and its restriction to `CF(W, V)` is pinned by the Dade map (`sigma_eq_tau`);
the σ-image of a single grid character `ω` is nevertheless pinned by its `V`-restriction
alone (`ticyclic_eq_sigma_omega_of_eqOn_V`, the (3.7)/(3.8)-counting uniqueness).

For the canonical pair, only the `S`-side `TypePData` is canonically reconciled to the pair
factors (`tp.Sdata` with `Sdata_W1_eq`; the `W₁`-prescribing producer
`exists_typePData_W1_eq_of_isTypeP2` is gated on type `P₂`, which `Section16MaximalPair`
pins only for `S` via `S_typeP2`).  The pair lemmas take the `T`-side datum as a hypothesis
pair `(dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)`, and
`exists_section16_partner_typePData` supplies it `P₂`-free — by Schur–Zassenhaus conjugacy
of complements of `T'`, transported through the whole-datum `TypePData.conj`.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory
open scoped IsMulCommutative

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

/- The (3.5)-determination: a ±irreducible agreeing with `ω` on `V` *is* `ω^σ` -/

/-- Integrality of the inner product on `ZIrr` (both slots): `⟨φ, η⟩ ∈ ℤ` for virtual
characters `φ, η`.  Right-slot span induction over `Irr(G)` on top of the single-irreducible
case `mem_ZIrr_inner_int`. -/
theorem inner_intCast_of_mem_ZIrr {φ η : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hη : η ∈ ZIrr G) :
    ∃ m : ℤ, ClassFunction.inner φ η = (m : ℂ) := by
  rw [ZIrr_eq_span] at hη
  induction hη using Submodule.span_induction with
  | mem x hx => exact mem_ZIrr_inner_int (⟨x, hx⟩ : IrreducibleCharacter G) hφ
  | zero =>
      refine ⟨0, ?_⟩
      rw [show (0 : ClassFunction G ℂ) = (0 : ℂ) • 0 from (zero_smul ℂ _).symm,
        OddOrder.RepresentationTheory.inner_smul_right]
      simp
  | add x y _ _ ihx ihy =>
      obtain ⟨mx, hmx⟩ := ihx
      obtain ⟨my, hmy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ClassFunction.inner_add_right, hmx, hmy]
      push_cast; ring
  | smul a x _ ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨a * m, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ a x, OddOrder.RepresentationTheory.inner_smul_right,
        hm, star_intCast]
      push_cast; ring

omit [Invertible (Nat.card G : ℂ)] in
/-- The TI-set `V = W ∖ (W₁ ∪ W₂)` of a (3.1) setup is nonempty: both cyclic factors are
nontrivial, so the internal product `W = W₁ × W₂` has an element with both components
nontrivial (`supportInVdiffEquiv`). -/
theorem ticyclic_V_nonempty (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hVeq : hyp.V = hyp.Vdiff) : hyp.V.Nonempty := by
  have hne1 : hyp.W1.subgroupOf hyp.W ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hyp.W1_nontrivial (hd.eq_bot_of_le hyp.W1_le_W)
  have hne2 : hyp.W2.subgroupOf hyp.W ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hyp.W2_nontrivial (hd.eq_bot_of_le hyp.W2_le_W)
  haveI := (Subgroup.nontrivial_iff_ne_bot _).mpr hne1
  haveI := (Subgroup.nontrivial_iff_ne_bot _).mpr hne2
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(hyp.W1.subgroupOf hyp.W))
  obtain ⟨b, hb⟩ := exists_ne (1 : ↥(hyp.W2.subgroupOf hyp.W))
  refine ⟨(((hyp.supportInVdiffEquiv.symm (⟨a, ha⟩, ⟨b, hb⟩)).1 : ↥hyp.W) : G), ?_⟩
  rw [hVeq]
  exact OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp
    (hyp.supportInVdiffEquiv.symm (⟨a, ha⟩, ⟨b, hb⟩)).2

/-- **The (3.5)-determination of the σ-grid** (Coq `eq_in_cycTIiso`, `PFsection3.v:1750`):
a norm-one virtual character of `G` that agrees on `V` with the linear character
`ω = ω(ξ)` of `W` **is** `ω^σ`.  This is the uniqueness underlying the per-index
identification of the two σ-grids of an (8.8) pair (Coq `cycTIisoC`): the grid vectors are
pinned by their `V`-restrictions alone.

Proof (mirroring Coq): let `η = ω^σ` and `ψ = η − φ`; `ψ` vanishes on `V` (both agree with
`ω` there — (3.2.c) `sigma_apply_irreducibleCharacter_of_mem_V` for `η`).  The integer
`c = ⟨φ, η⟩` satisfies `‖η ∓ φ‖² = 2 ∓ 2c ≥ 0`, so `c ∈ {−1, 0, 1}`:
`c = 1` forces `ψ = 0` (positive definiteness); `c = 0` gives `‖ψ‖² = 2`, so all
σ-coefficients of the `V`-vanishing `ψ` vanish (`sigmaCoeff_eq_zero_of_vanishOnV`, the
(3.7)/(3.8) counting) — contradicting `⟨ψ, η⟩ = 1`; `c = −1` forces `φ = −η`, making
`ω` vanish on the nonempty `V` — impossible for a unit-valued linear character. -/
theorem ticyclic_eq_sigma_omega_of_eqOn_V
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp)
    (ξ : hyp.W →* ℂˣ) {φ : ClassFunction G ℂ}
    (hφZ : φ ∈ ZIrr G) (hφ1 : ClassFunction.inner φ φ = 1)
    (hφV : ∀ (v : G) (hv : v ∈ hyp.V),
      φ v = (hyp.omega ξ : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩) :
    φ = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) := by
  classical
  set η := hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) with hηdef
  -- `η` is the (3.5) family member at the index of `ξ`: `ZIrr`, norm one
  have hηchi : η = hyp.chiFam hVeq app (hyp.omegaProdEquiv.symm ξ) :=
    hyp.sigma_omega hVeq app ξ
  have hηZ : η ∈ ZIrr G := by
    rw [hηchi]; exact (hyp.chiFam_spec hVeq app).2.1 _
  have hη1 : ClassFunction.inner η η = 1 := by
    rw [hηchi, (hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  -- `η` agrees with `ω` on `V` ((3.2.c)), so `ψ = η − φ` vanishes on `V`
  have hηV : ∀ (v : G) (hv : v ∈ hyp.V),
      η v = (hyp.omega ξ : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ := fun v hv =>
    hyp.sigma_apply_irreducibleCharacter_of_mem_V hVeq app (hyp.omega ξ) hv
  have hψV : ∀ v ∈ hyp.V, (η - φ) v = 0 := fun v hv => by
    rw [ClassFunction.sub_apply, hηV v hv, hφV v hv, sub_self]
  -- the integer inner product `c = ⟨φ, η⟩`
  obtain ⟨c, hc⟩ := inner_intCast_of_mem_ZIrr hφZ hηZ
  have hcstar : ClassFunction.inner η φ = (c : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc, star_intCast]
  -- `‖η − φ‖² = 2 − 2c` and `‖φ + η‖² = 2 + 2c`
  have hsub : ClassFunction.inner (η - φ) (η - φ) = ((2 - 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hη1, hφ1, hc, hcstar]
    push_cast; ring
  have hadd : ClassFunction.inner (φ + η) (φ + η) = ((2 + 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hη1, hφ1, hc, hcstar]
    push_cast; ring
  -- positivity bounds: `−1 ≤ c ≤ 1`
  have hle : c ≤ 1 := by
    have h0 := inner_self_re_nonneg (η - φ)
    rw [hsub, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 - 2 * c := by exact_mod_cast h0
    omega
  have hge : -1 ≤ c := by
    have h0 := inner_self_re_nonneg (φ + η)
    rw [hadd, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 + 2 * c := by exact_mod_cast h0
    omega
  interval_cases c
  · -- `c = −1`: `φ = −η`, so `ω` vanishes on the nonempty `V` — impossible
    exfalso
    have hzero : φ + η = 0 := by
      refine eq_zero_of_inner_self_re_eq_zero ?_
      rw [hadd]
      norm_num
    obtain ⟨v, hv⟩ := ticyclic_V_nonempty hyp hVeq
    have hφv : φ v = -(η v) := by
      have h := congrArg (fun f : ClassFunction G ℂ => f v) hzero
      simp only [ClassFunction.add_apply, ClassFunction.zero_apply] at h
      exact eq_neg_of_add_eq_zero_left h
    have homega : (hyp.omega ξ : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ = 0 := by
      have h1 := hφV v hv
      have h2 := hηV v hv
      rw [hφv, h2] at h1
      -- `−ω(v) = ω(v)` forces `ω(v) = 0`
      linear_combination -h1 / 2
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply] at homega
    exact Units.ne_zero _ homega
  · -- `c = 0`: `‖ψ‖² = 2` and `ψ|_V = 0`, so all σ-coefficients vanish — but `⟨ψ, η⟩ = 1`
    exfalso
    have hψZ : η - φ ∈ ZIrr G := Submodule.sub_mem _ hηZ hφZ
    have hψ2 : ClassFunction.inner (η - φ) (η - φ) = 2 := by rw [hsub]; norm_num
    have hall := hyp.sigmaCoeff_eq_zero_of_vanishOnV hVeq app hψZ hψ2 hψV
    have hcoeff : hyp.sigmaCoeff hVeq app (η - φ) (hyp.omegaProdEquiv.symm ξ)
        = ClassFunction.inner (η - φ) (hyp.chiFam hVeq app (hyp.omegaProdEquiv.symm ξ)) := rfl
    have h1 : ClassFunction.inner (η - φ) η = 0 := by
      have h := hall (hyp.omegaProdEquiv.symm ξ)
      rw [hcoeff, ← hηchi] at h
      exact h
    rw [ClassFunction.inner_sub_left, hη1, hc] at h1
    norm_num at h1
  · -- `c = 1`: `‖ψ‖² = 0`, so `φ = η`
    have hzero : η - φ = 0 := by
      refine eq_zero_of_inner_self_re_eq_zero ?_
      rw [hsub]
      norm_num
    exact (sub_eq_zero.mp hzero).symm

/-- **The per-index σ-grid identification** (Coq `cycTIisoC`, `PFsection3.v:1849`): two
TI-cyclic setups sharing the TI-set `V` and the ambient `W` have the *same* σ-image on each
grid character — `σ₁(ω(ξ)) = σ₂(ω(ξ'))`, where `ξ'` is `ξ` read along the `W`-identification
(value restriction along `Subgroup.inclusion`, no cast).

The grid characters are not `V`-supported, so this does **not** follow from the Dade-map
agreement (`ticyclic_sigma_eq_of_V_eq`); it is the (3.5)-determination
(`ticyclic_eq_sigma_omega_of_eqOn_V`) instead: `σ₁(ω(ξ))` is a norm-one virtual character
(σ is an isometry into `ZIrr`) agreeing with `ω(ξ')` on the shared `V` ((3.2.c) on the
`hyp₁` side — `ξ` and `ξ'` take the same values), so it *is* `σ₂(ω(ξ'))`. -/
theorem ticyclic_sigma_omega_eq_of_V_eq
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (ξ : hyp₁.W →* ℂˣ) :
    hyp₁.sigma hVeq₁ app₁ (hyp₁.omega ξ : ClassFunction hyp₁.W ℂ)
      = hyp₂.sigma hVeq₂ app₂
          (hyp₂.omega (ξ.comp (Subgroup.inclusion hW.ge)) : ClassFunction hyp₂.W ℂ) := by
  refine ticyclic_eq_sigma_omega_of_eqOn_V hyp₂ hVeq₂ app₂
    (ξ.comp (Subgroup.inclusion hW.ge))
    (hyp₁.sigma_mem_ZIrr hVeq₁ app₁
      (IsIrreducibleCharacter.mem_ZIrr (hyp₁.omega ξ).2)) ?_ ?_
  · rw [hyp₁.sigma_inner hVeq₁ app₁, irreducibleCharacter_inner_eq_ite, if_pos rfl]
  · intro v hv₂
    have hv₁ : v ∈ hyp₁.V := hV ▸ hv₂
    rw [hyp₁.sigma_apply_irreducibleCharacter_of_mem_V hVeq₁ app₁ (hyp₁.omega ξ) hv₁,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply]
    rfl

/-! ### The column → row transpose of σ-grid sums (issue 9079 item 4, generic core)

A pair situation swaps the roles of `W₁` and `W₂`.  Under the identifications
`hyp₁.W = hyp₂.W`, `hyp₁.W1 = hyp₂.W2`, `hyp₁.W2 = hyp₂.W1`, a *column* of the `hyp₁`-grid
(the (5.8) shape `∑_p χ_{(p, kcol)}`, `kcol` fixed) is a *row* of the `hyp₂`-grid: each
grid vector transposes by the per-index identification (`ticyclic_sigma_omega_eq_of_V_eq`),
and the index translation is the two-level `subgroupOf`-transport of the character pair
(`ω`-factors swap along the `W`-decomposition, `ticyclic_wFstSnd_inclusion_of_swap`). -/

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Value-level transport of `subgroupOf`-members along inclusions of both the ambient and
the subgroup: `⟨⟨v, _⟩, _⟩ ↦ ⟨⟨v, _⟩, _⟩` (membership proofs re-derived, no `Eq.rec`).
Upstream-hoist candidate (`OddOrder/Mathlib/Subgroup.lean`). -/
def subgroupOfTransport {W W' H H' : Subgroup G} (hW : W' ≤ W) (hH : H' ≤ H) :
    ↥(H'.subgroupOf W') →* ↥(H.subgroupOf W) :=
  MonoidHom.codRestrict ((Subgroup.inclusion hW).comp (H'.subgroupOf W').subtype)
    (H.subgroupOf W) fun x => by
      rw [Subgroup.mem_subgroupOf, MonoidHom.comp_apply, Subgroup.coe_inclusion]
      exact hH (Subgroup.mem_subgroupOf.mp x.2)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
@[simp] theorem subgroupOfTransport_coe {W W' H H' : Subgroup G} (hW : W' ≤ W) (hH : H' ≤ H)
    (x : ↥(H'.subgroupOf W')) :
    ((subgroupOfTransport hW hH x : ↥W) : G) = ((x : ↥W') : G) := rfl

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Precomposition with the two-level transport is a bijection of character groups: the
transports in the two directions compose to the identity by proof irrelevance (the
underlying element never moves). -/
def subgroupOfTransportCharEquiv {W W' H H' : Subgroup G}
    (hW : W' ≤ W) (hW' : W ≤ W') (hH : H' ≤ H) (hH' : H ≤ H') :
    (↥(H.subgroupOf W) →* ℂˣ) ≃ (↥(H'.subgroupOf W') →* ℂˣ) where
  toFun χ := χ.comp (subgroupOfTransport hW hH)
  invFun χ := χ.comp (subgroupOfTransport hW' hH')
  left_inv _ := MonoidHom.ext fun _ => rfl
  right_inv _ := MonoidHom.ext fun _ => rfl

omit [Invertible (Nat.card G : ℂ)] in
/-- **The `W = W₁ × W₂` decomposition transposes along a role swap**: reading a
`hyp₂.W`-element in `hyp₁` (same `W`, factors swapped), its `hyp₁`-`W₁`-component is its
`hyp₂`-`W₂`-component and vice versa — the internal-product decomposition is unique, and
the two factorizations differ only by the (abelian) reordering. -/
theorem ticyclic_wFstSnd_inclusion_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1)
    (w : ↥hyp₂.W) :
    hyp₁.wFst (Subgroup.inclusion hW.ge w)
        = subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w)
      ∧ hyp₁.wSnd (Subgroup.inclusion hW.ge w)
        = subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w) := by
  have hcomm : hyp₂.wProj2 w * hyp₂.wProj1 w = w := by
    haveI := hyp₂.isMulCommutative_W
    rw [mul_comm]
    exact hyp₂.wProj1_mul_wProj2 w
  have hsymm : hyp₁.wProdEquiv.symm (Subgroup.inclusion hW.ge w)
      = (subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w),
         subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w)) := by
    apply hyp₁.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp₁.wProdEquiv_apply]
    apply Subtype.ext
    calc ((Subgroup.inclusion hW.ge w : ↥hyp₁.W) : G)
        = ((w : ↥hyp₂.W) : G) := by rw [Subgroup.coe_inclusion]
      _ = ((hyp₂.wProj2 w * hyp₂.wProj1 w : ↥hyp₂.W) : G) := by rw [hcomm]
      _ = ((subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w) : ↥hyp₁.W) : G)
            * ((subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w) : ↥hyp₁.W) : G) := by
          rw [Subgroup.coe_mul, subgroupOfTransport_coe, subgroupOfTransport_coe]
          rfl
      _ = (((subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w) : ↥hyp₁.W)
            * (subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w) : ↥hyp₁.W) : ↥hyp₁.W) : G) := by
          rw [Subgroup.coe_mul]
  exact ⟨by rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.wFst_apply, hsymm],
    by rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.wSnd_apply, hsymm]⟩

omit [Invertible (Nat.card G : ℂ)] in
/-- **The grid characters transpose along a role swap** (the index translation of the
(8.8) grid transpose): reading the `hyp₁`-grid character `ω_{(p, kcol)}` on `hyp₂.W`
(same `W`), it is the `hyp₂`-grid character at the transported *swapped* pair —
the `W₁`-factor `p` becomes the `W₂`-factor and the `W₂`-factor `kcol` the `W₁`-factor. -/
theorem ticyclic_omegaProdChar_comp_inclusion_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1)
    (p : (hyp₁.W1.subgroupOf hyp₁.W) →* ℂˣ) (kcol : (hyp₁.W2.subgroupOf hyp₁.W) →* ℂˣ) :
    (hyp₁.omegaProdChar p kcol).comp (Subgroup.inclusion hW.ge)
      = hyp₂.omegaProdChar (kcol.comp (subgroupOfTransport hW.ge hW21.ge))
          (p.comp (subgroupOfTransport hW.ge hW12.ge)) := by
  ext w
  obtain ⟨h1, h2⟩ := ticyclic_wFstSnd_inclusion_of_swap hyp₁ hyp₂ hW hW12 hW21 w
  simp only [MonoidHom.comp_apply, OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar,
    MonoidHom.mul_apply]
  rw [h1, h2, mul_comm]

open scoped Classical in
/-- **The (5.8) column sum is a row sum of the transposed grid** (issue 9079 item 4, the
generic core of the `S`-grid = `M`-grid transpose): for two TI-cyclic setups sharing `V`
and `W` with the `W₁`/`W₂` roles swapped, the full `hyp₁`-grid column at `kcol` equals the
full `hyp₂`-grid row at the transported index `kcol'`.  Every grid vector transposes by the
(3.5)-determination (`ticyclic_sigma_omega_eq_of_V_eq` at the index translation
`ticyclic_omegaProdChar_comp_inclusion_of_swap`), and the summation reindexes along the
character-group bijection `p ↦ p ∘ transport`.

This is what turns the `S`-side (5.8) column pin (`typeII_nu_tau2_dichotomy`) into the
`M`-side row-sum form `ν^{τ₂} = ±∑_j ω_{r'j}^σ` that the (10.7) cross-isometry package
(`TypeIICrossIsometryData.nu_tau2_eq`) consumes. -/
theorem ticyclic_chiFam_columnSum_transpose
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    [Fintype ((hyp₁.W1.subgroupOf hyp₁.W) →* ℂˣ)]
    [Fintype ((hyp₂.W2.subgroupOf hyp₂.W) →* ℂˣ)]
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (kcol : (hyp₁.W2.subgroupOf hyp₁.W) →* ℂˣ) :
    ∑ p : (hyp₁.W1.subgroupOf hyp₁.W) →* ℂˣ, hyp₁.chiFam hVeq₁ app₁ (p, kcol)
      = ∑ q : (hyp₂.W2.subgroupOf hyp₂.W) →* ℂˣ,
          hyp₂.chiFam hVeq₂ app₂ (kcol.comp (subgroupOfTransport hW.ge hW21.ge), q) := by
  refine Fintype.sum_equiv
    (subgroupOfTransportCharEquiv hW.ge hW.le hW12.ge hW12.le) _ _ fun p => ?_
  -- the `hyp₁`-grid vector at `(p, kcol)` is `σ₁(ω(ξ))` at `ξ = ω_{(p, kcol)}`
  have h1 : hyp₁.chiFam hVeq₁ app₁ (p, kcol)
      = hyp₁.sigma hVeq₁ app₁
          (hyp₁.omega (hyp₁.omegaProdChar p kcol) : ClassFunction hyp₁.W ℂ) := by
    rw [hyp₁.sigma_omega hVeq₁ app₁, hyp₁.omegaProdEquiv_symm_omegaProdChar]
  -- transpose per index, then read the transported character as a `hyp₂`-grid pair
  have h2 := ticyclic_sigma_omega_eq_of_V_eq hyp₁ hyp₂ hVeq₁ hVeq₂ hV hW app₁ app₂
    (hyp₁.omegaProdChar p kcol)
  have h3 := ticyclic_omegaProdChar_comp_inclusion_of_swap hyp₁ hyp₂ hW hW12 hW21 p kcol
  have h4 : hyp₂.sigma hVeq₂ app₂
      (hyp₂.omega (hyp₂.omegaProdChar (kcol.comp (subgroupOfTransport hW.ge hW21.ge))
          (p.comp (subgroupOfTransport hW.ge hW12.ge))) : ClassFunction hyp₂.W ℂ)
      = hyp₂.chiFam hVeq₂ app₂ (kcol.comp (subgroupOfTransport hW.ge hW21.ge),
          p.comp (subgroupOfTransport hW.ge hW12.ge)) := by
    rw [hyp₂.sigma_omega hVeq₂ app₂, hyp₂.omegaProdEquiv_symm_omegaProdChar]
  rw [h1, h2, h3, h4]
  rfl

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
open scoped Pointwise

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

open scoped FiniteInduce in
/-- **The `S`-side (10.7) σ-machinery runs on the §10 → §5 bridge**: the `ticVdiff` of the
type-II Hypothesis (4.6) instance (`typeIIHypothesis46`, the setup of the (5.8) dichotomy
`typeII_nu_tau2_dichotomy`) **is** `typePData_toTICyclicHypothesis data hodd` — the `tic`
field of `typeIIHypothesis46` is that bridge, `ticVdiff` re-reads its `W`-block with the
`Vdiff`-shaped TI-set, and the bridge's own `V` is `Vdiff`-shaped definitionally.  All data
fields agree by `rfl` and every other field is a proof, so the two are definitionally equal
(structure eta + proof irrelevance).  This connects the `S`-side dichotomy to the pair
lemmas above without any reconciliation. -/
theorem ticVdiff_typeIIHypothesis46_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)
      = typePData_toTICyclicHypothesis data hodd := rfl

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

/-- **The `W₁`-reconciled partner `TypePData` exists** (the `T`-side producer, closing the
sourcing gap of the pair packaging; issue 9079).  `T` is type non-I, so it carries *some*
type-`P` datum (`typePData_of_isTypeNonI`); its cyclic factor `W₁` and the pair's dual
κ-Hall `K*` both complement `T' = [T,T]` in `T` (`M_complement`,
`typeP_derivedInG_isComplement_kappaHall`), so they are `T`-conjugate by Schur–Zassenhaus
(`IsComplement'.exists_conj_of_coprime`; `(|T'|, [T:T']) = 1` from the κ-Hall complement).
Conjugating the whole datum (`TypePData.conj`, conjugation by an element of `T` fixes `T`)
realigns `W₁` to `K*`; the dual factor `W₂ = K` then comes for free
(`section16_partner_typePData_W2_eq`).

No `IsTypeP2 mp.T` is needed — contrast `exists_typePData_W1_eq_of_isTypeP2`, whose
`(κ∪σ)'`-Hall complement `U` requires the `P₂`-only `M_F`-internal decomposition; here the
datum's own complement `U` is merely transported, never rebuilt. -/
theorem exists_section16_partner_typePData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    ∃ dataT : TypePData mp.T, dataT.W1 = mp.Kstar ∧ dataT.W2 = mp.K := by
  classical
  -- an arbitrary type-`P` datum on `T` (from `T_nonI`)
  obtain ⟨data₀⟩ := typePData_of_isTypeNonI mp.T_nonI
  haveI : IsCyclic ↥mp.Kstar := mp.isCyclic_Kstar
  -- `K*` complements `T'` in `T` (the κ-Hall complement, ungated for type `P`)
  have hKcompl := OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG
    mp.T_maximal mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
  -- `T'.subgroupOf T` is normal (it is the commutator subgroup of `↥T`)
  have hT'sub : (derivedInG mp.T).subgroupOf mp.T = commutator ↥mp.T :=
    Subgroup.comap_map_eq_self_of_injective mp.T.subtype_injective _
  haveI : ((derivedInG mp.T).subgroupOf mp.T).Normal := by rw [hT'sub]; infer_instance
  -- `(|T'|, [T : T']) = 1`: the κ-Hall complement has coprime order
  have hN : Nat.Coprime (Nat.card ↥((derivedInG mp.T).subgroupOf mp.T))
      ((derivedInG mp.T).subgroupOf mp.T).index := by
    rw [hKcompl.symm.index_eq_card]
    exact OddOrder.BG.Ch4.S14.coprime_card_derived_kappaHall_of_isComplement'
      mp.Kstar_hall hKcompl
  haveI hTsolv : IsSolvable ↥mp.T := hG.solvable_of_mem_maximalSubgroups mp.T_maximal
  have hSolv : IsSolvable ↥((derivedInG mp.T).subgroupOf mp.T) ∨
      IsSolvable (↥mp.T ⧸ (derivedInG mp.T).subgroupOf mp.T) :=
    Or.inl (solvable_of_solvable_injective
      (Subgroup.subtype_injective ((derivedInG mp.T).subgroupOf mp.T)))
  -- Schur–Zassenhaus: the two complements `data₀.W1`, `K*` of `T'` are `T`-conjugate
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hN hSolv
    data₀.M_complement hKcompl
  -- lift the `↥T`-level conjugacy to a `G`-level pointwise-`smul` equation
  set g : G := (n : G) with hgdef
  have hcomp : mp.T.subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj g).toMonoidHom.comp mp.T.subtype := by
    ext k
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hgdef, Subgroup.coe_mul, Subgroup.coe_inv]
  have hW1map : data₀.W1.map (MulAut.conj g).toMonoidHom = mp.Kstar := by
    have key := congrArg (Subgroup.map mp.T.subtype) hn
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le data₀.W1_le,
      Subgroup.map_subgroupOf_eq_of_le mp.Kstar_le_T] at key
    exact key
  have hW1smul : (MulAut.conj g) • data₀.W1 = mp.Kstar := by
    rw [pointwise_mulAut_smul_eq_map]; exact hW1map
  -- conjugation by `g ∈ T` fixes `T`; transport the whole datum and cast back
  have hgT : (MulAut.conj g) • mp.T = mp.T := Subgroup.conj_smul_eq_self_of_mem n.2
  have hcastW1 : ∀ {S : Subgroup G} (h : S = mp.T) (d : TypePData S), (h ▸ d).W1 = d.W1 := by
    intro S h d; subst h; rfl
  have hTW1 : (hgT ▸ data₀.conj (MulAut.conj g)).W1 = mp.Kstar := by
    rw [hcastW1 hgT,
      show (data₀.conj (MulAut.conj g)).W1 = (MulAut.conj g) • data₀.W1 from rfl, hW1smul]
  exact ⟨hgT ▸ data₀.conj (MulAut.conj g), hTW1,
    section16_partner_typePData_W2_eq hG _ hTW1⟩

open scoped FiniteInduce in
/-- **The canonical pair shares its ambient `W`** (Peterfalvi (8.8), `S ∩ T = W`): the
`S`-side reconciled datum and a `W₁`-reconciled `T`-side datum give `TICyclicHypothesis`s
with the same `W = K ⊔ K*` — the `S`-side by `Sdata_W1_eq`/`Sdata_W2_eq` and the pair
reconciliation, the `T`-side by `section16_partner_typePData_W_eq`.  This is the `hW` input
of the per-index σ-grid identification (`ticyclic_sigma_omega_eq_of_V_eq`). -/
theorem section16_pair_tic_W_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) (hodd : Odd (Nat.card G))
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    (typePData_toTICyclicHypothesis tp.Sdata hodd).W
      = (typePData_toTICyclicHypothesis dataT hodd).W := by
  have hSW1 : tp.Sdata.W1 = mp.K :=
    tp.Sdata_W1_eq.trans (tp.W1_eq_K_and_W2_eq_Kstar hG).1
  have hSW2 : tp.Sdata.W2 = mp.Kstar :=
    tp.Sdata_W2_eq.trans (tp.W1_eq_K_and_W2_eq_Kstar hG).2
  rw [typePData_toTICyclicHypothesis_W, typePData_toTICyclicHypothesis_W, tp.Sdata.W_eq,
    hSW1, hSW2, section16_partner_typePData_W_eq hG dataT hTW1]

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
  refine ticyclic_V_eq_of_swap _ _ rfl rfl
    (section16_pair_tic_W_eq hG tp hodd dataT hTW1) ?_ ?_
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

open scoped FiniteInduce in
/-- **The per-index identification of the canonical pair's σ-grids** (Coq `cycTIisoC` at
the (8.8) pair, `PFsection10.v:632` `etaC`; issue 9079 part 2): for each linear character
`ξ` of the shared `W`, the `S`-side σ-image of the grid character `ω(ξ)` **is** the
`T`-side σ-image of `ω(ξ')`, where `ξ'` reads `ξ` along the `W`-identification
(`section16_pair_tic_W_eq`).  Unlike the `CF(W, V)`-agreement (`section16_pair_sigma_eq`)
this pins the grid vectors themselves — the (3.5)-determination
(`ticyclic_eq_sigma_omega_of_eqOn_V`) applied over the shared TI-set
(`section16_pair_tic_V_eq`).  This is the index-by-index translation between the two
σ-grids of the (10.7) pair-witness route. -/
theorem section16_pair_sigma_omega_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) (hodd : Odd (Nat.card G))
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)
    (appS : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis tp.Sdata hodd))
    (appT : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis dataT hodd))
    (ξ : (typePData_toTICyclicHypothesis tp.Sdata hodd).W →* ℂˣ) :
    (typePData_toTICyclicHypothesis tp.Sdata hodd).sigma rfl appS
        ((typePData_toTICyclicHypothesis tp.Sdata hodd).omega ξ
          : ClassFunction (typePData_toTICyclicHypothesis tp.Sdata hodd).W ℂ)
      = (typePData_toTICyclicHypothesis dataT hodd).sigma rfl appT
          ((typePData_toTICyclicHypothesis dataT hodd).omega
              (ξ.comp (Subgroup.inclusion
                (section16_pair_tic_W_eq hG tp hodd dataT hTW1).ge))
            : ClassFunction (typePData_toTICyclicHypothesis dataT hodd).W ℂ) :=
  ticyclic_sigma_omega_eq_of_V_eq _ _ rfl rfl
    (section16_pair_tic_V_eq hG tp hodd dataT hTW1)
    (section16_pair_tic_W_eq hG tp hodd dataT hTW1) appS appT ξ

/- The type-II → canonical-partner reduction (Coq `Frob_der1_type2` head, issue 9079 item 3) -/

/-- The type-II-designated member of the canonical pair is indeed of type II:
`mp.S_typeP2` (Peterfalvi (13.2.a)) through the BG type dictionary
(`isTypeII_of_isTypeP2`, Proposition 16.1). -/
theorem section16_S_isTypeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    IsTypeII mp.S :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG mp.S_maximal mp.S_typeP2

/-- **Peterfalvi (10.7) reduction, covering step** (Coq `Frob_der1_type2` head,
`PFsection10.v:552-556`): every type-II maximal subgroup `L` is conjugate to a member of
the canonical pair — to `mp.S`, or to `mp.T` with `mp.T` itself then of type II (types are
conjugation-invariant, `isTypeII_pointwise_smul`).  The type-I branch of the (8.8) covering
`theorem88_caseB` is killed by type exclusivity (`not_isTypeI_of_isTypeNonI`).

The `T`-branch is **not refutable from the pair data alone**: Peterfalvi (13.2.a) is
one-directional ("if `q < p` then `S` is of type II"), so the larger-κ member `mp.T` may
also be of type II; the Coq proof kills its corresponding branch only under the §10
contextual hypothesis `notMtype2` (the ambient pair member there is assumed not of type 2).
Consumers either use the returned `IsTypeII mp.T` certificate symmetrically (the pair
machinery of this file is `S`/`T`-symmetric through `exists_section16_partner_typePData`)
or discharge it with `exists_conj_eq_S_of_isTypeII` below. -/
theorem conj_eq_S_or_conj_eq_T_of_isTypeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)
    {L : Subgroup G} (hL : L ∈ maximalSubgroups G) (hLII : IsTypeII L) :
    (∃ g : G, MulAut.conj g • L = mp.S) ∨
      ((∃ g : G, MulAut.conj g • L = mp.T) ∧ IsTypeII mp.T) := by
  rcases mp.theorem88_caseB L hL with hI | hS | hT
  · exact absurd hI (OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hL (Or.inl hLII))
  · exact Or.inl hS
  · refine Or.inr ⟨hT, ?_⟩
    obtain ⟨g, hg⟩ := hT
    exact hg ▸ isTypeII_pointwise_smul (MulAut.conj g) hLII

/-- **Peterfalvi (10.7) reduction, strong form**: if the partner `mp.T` is moreover not of
type II, every type-II maximal subgroup is conjugate to `mp.S` — the exact Lean form of the
Coq branch kill (`FTtypeJ` + `notMtype2`). -/
theorem exists_conj_eq_S_of_isTypeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)
    (hT : ¬ IsTypeII mp.T)
    {L : Subgroup G} (hL : L ∈ maximalSubgroups G) (hLII : IsTypeII L) :
    ∃ g : G, MulAut.conj g • L = mp.S := by
  rcases conj_eq_S_or_conj_eq_T_of_isTypeII hG mp hL hLII with hS | ⟨-, hTII⟩
  · exact hS
  · exact absurd hTII hT

end PairPackaging

end OddOrder.Peterfalvi.S12
