/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeSupport
import OddOrder.Peterfalvi.S06_CertainTypeStructure

/-!
# Peterfalvi (4.8): equal-degree certain-type differences are σ-isometric

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§4, pp. 23-24, statement (4.8).

Under Hypothesis (4.6), fix a row index `i` (`0 ≤ i < w₁`) and two nontrivial columns
`j, k` (`0 < j, k < w₂`).  If the two certain-type characters have equal degree,
`μ_{ij}(1) = μ_{ik}(1)`, then:

* `Supp(μ_{ij} − μ_{ik}) ⊆ A₀`;
* the column signs agree, `δ_j = δ_k`;
* the Dade image is `(μ_{ij} − μ_{ik})^τ = δ_j·(ω_{ij}^σ − ω_{ik}^σ)`.

This file develops the proof in stages (Peterfalvi's eight-step argument).

Landed so far:
* **step (1)** `certainType_sign_eq_of_degree_eq`: the sign equality `δ_j = δ_k`, from the degree
  congruence (4.3.d) and `w₁ > 2`;
* **step (2)** `certainType_apply_eq_of_mem_W1`: `μ_{ij} − μ_{ik}` vanishes on `W₁`;
* **conclusion (1)** `certainType_diff_supp_subset_A0`: `Supp(μ_{ij} − μ_{ik}) ⊆ A₀`;
* the `σ_G` foundation — `ticVdiff` (the `G`-side `V = W − (W₁ ∪ W₂)` TI-cyclic, on which `σ` runs),
  the L↔G bridge (`ticWEquivSdiffW`, `omegaProdCharTic`), `certainTypeOmegaSigma` (`ω_{ij}^σ`) and
  the `τ`-side `certainTypeDiffSupported` / `tau_toDadeMap_apply_of_mem`;
* **step (4)** `certainType_diff_dade_apply_eq_of_mem_V`: the two sides agree on `V`.

Remaining (steps 5-8, the `(3.8)` trichotomy endgame): `ψ := (μ_{ij} − μ_{ik})^τ −
δ_j(ω_{ij}^σ − ω_{ik}^σ)` vanishes on `V` (step 4), has `NC(ψ) ≤ 4 < 2w₁`, so the trichotomy
`sigmaCoeff_trichotomy` applies; cases (b)/(c) are excluded and case (a) forces `ψ = 0`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md` ("session 33").
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- The (3.1)-for-`G` TI-cyclic hypothesis on the **smaller** TI set `V = W − (W₁ ∪ W₂)`, the one
the §5 `σ`-machinery ((3.2)-(3.9)) runs on (the `ω_{ij}`-basis lives in `CF(W, V)`, vanishing on
`W₁` and `W₂`).  The ambient `h.tic` carries `V = W − W₂` for the Dade isometry `τ`; this shrinks
the TI set, which stays TI since `W − (W₁ ∪ W₂) ⊆ W − W₂` and `IsTISubset` is antitone in the set
(`tic.V_ti.subset`).  This is the `G`-side analogue of the `(L, W)`-side `toTICyclicHypothesis`, and
is what makes `σ_G` (its `sigma`) well-typed: `ticVdiff.V = ticVdiff.Vdiff` by `rfl`. -/
noncomputable def ticVdiff (h : Hypothesis46 A L) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis G where
  W := h.tic.W
  W1 := h.tic.W1
  W2 := h.tic.W2
  W1_le_W := h.tic.W1_le_W
  W2_le_W := h.tic.W2_le_W
  W1_nontrivial := h.tic.W1_nontrivial
  W2_nontrivial := h.tic.W2_nontrivial
  W_sup := h.tic.W_sup
  W_disjoint := h.tic.W_disjoint
  W_card_coprime := h.tic.W_card_coprime
  W_card_odd := h.tic.W_card_odd
  W_cyclic := h.tic.W_cyclic
  V := (↑h.tic.W : Set G) \ ((↑h.tic.W1 : Set G) ∪ (↑h.tic.W2 : Set G))
  V_subset_sharp := fun v hv => by
    rw [OddOrder.Peterfalvi.S04.mem_sharp]
    exact ⟨Set.mem_univ v, fun heq => hv.2 (Or.inl (by rw [heq]; exact Subgroup.one_mem h.tic.W1))⟩
  V_subset_W := fun _ hv => hv.1
  W_normalizes_V := by
    intro w v hv
    haveI := h.tic.isMulCommutative_W
    have h1 : (⟨v, hv.1⟩ : ↥h.tic.W) * w = w * ⟨v, hv.1⟩ := mul_comm _ _
    have h2 : (w : G) * v = v * (w : G) := (Subtype.ext_iff.mp h1).symm
    have h3 : (w : G) * v * (w : G)⁻¹ = v := by rw [h2]; exact mul_inv_cancel_right v w
    rw [h3]; exact hv
  V_ti := h.tic.V_ti.subset (by
    rw [h.tic_V]; exact fun _ hv => ⟨hv.1, fun h2 => hv.2 (Or.inr h2)⟩)

/-- The canonical Dade application driving `σ_G`: the §4 Dade package on `ticVdiff`'s TI set
`V = W − (W₁ ∪ W₂)`, whose local subgroups are all trivial (`H(a) = ⊥`), so `HConjInvariant` holds
for free.  Mirror of the `(L, W)`-side `toTICyclicFullDadeApplication`. -/
noncomputable def ticVdiffFullDadeApplication (h : Hypothesis46 A L)
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)] :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (ticVdiff h) :=
  ⟨(ticVdiff h).toDadeHypothesis.fullDadeIsometryData
    (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩

/-- `tic.W = (W₁ ⊔ W₂).map (L ↪ G)`: the ambient (3.1)-for-`G` group is the `G`-image of the
certain-type `W = W₁ ⊔ W₂ ≤ L`.  (Named so the bridge `ticWEquivSdiffW` and its coherence share one
proof term.) -/
theorem tic_W_eq_map (h : Hypothesis46 A L) :
    h.tic.W = (h.W1 ⊔ h.W2).map L.subtype := by
  rw [← h.tic.W_sup, h.tic_W1, h.tic_W2, ← Subgroup.map_sup]

/-- The bridge isomorphism `tic.W ≃* sdiff.W` — both are `W₁ ⊔ W₂`, one as a subgroup of `G`, the
other of `L`, identified by the corestriction of `L ↪ G`.  Transports the `sdiff`-side `(L, W)`
characters (`omegaProdChar`, `chiColumn`) to the `tic`-side `(G, W)` for the `G`-side `σ`. -/
noncomputable def ticWEquivSdiffW (h : Hypothesis46 A L) :
    h.tic.W ≃* h.sdiffTICyclicHypothesis.W :=
  (MulEquiv.subgroupCongr (tic_W_eq_map h)).trans
    (Subgroup.equivMapOfInjective (h.W1 ⊔ h.W2) L.subtype L.subtype_injective).symm

/-- Carrier coherence for the bridge: the underlying `G`-element of `g : tic.W` equals the image of
its `sdiff.W` partner under `L ↪ G`. -/
theorem coe_ticWEquivSdiffW (h : Hypothesis46 A L) (g : h.tic.W) :
    ((ticWEquivSdiffW h g : ↥L) : G) = (g : G) := by
  -- `equivMapOfInjective` undoes the `.symm` in the bridge, landing back on the `subgroupCongr` cast
  have key : (Subgroup.equivMapOfInjective (h.W1 ⊔ h.W2) L.subtype L.subtype_injective)
      (ticWEquivSdiffW h g) = MulEquiv.subgroupCongr (tic_W_eq_map h) g :=
    (Subgroup.equivMapOfInjective (h.W1 ⊔ h.W2) L.subtype L.subtype_injective).apply_symm_apply _
  simpa [Subgroup.coe_equivMapOfInjective_apply, MulEquiv.subgroupCongr_apply] using
    congrArg (fun x : ((h.W1 ⊔ h.W2).map L.subtype) => (x : G)) key

/-- The `tic`-side (`G`) linear character `ω_{ij}` of `W = W₁ ⊔ W₂`, transported from the
`sdiff`-side `omegaProdChar (w1CharEquiv i) χ₂` along the bridge `ticWEquivSdiffW`.  Its `σ_G`-image
`h.tic.sigma rfl (ticFullDadeApplication h) (h.tic.omega …)` is the `ω_{ij}^σ ∈ CF(G)` of (4.8)
conclusion (3). -/
noncomputable def omegaProdCharTic (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    h.tic.W →* ℂˣ :=
  (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂).comp (ticWEquivSdiffW h)

/-- The transported `tic`-side character evaluates as the `sdiff`-side `chiColumn` at the bridge
partner: `ω_{ij}^{tic}(g) = ω_{ij}(e g) = chiColumn χ₂ i (e g)` (`e = ticWEquivSdiffW`). -/
theorem omegaProdCharTic_apply (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) (g : h.tic.W) :
    ((omegaProdCharTic h χ₂ i g : ℂˣ) : ℂ)
      = (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) (ticWEquivSdiffW h g) := by
  rw [omegaProdCharTic, MonoidHom.comp_apply, Hypothesis.chiColumn,
    h.sdiffTICyclicHypothesis.omega_apply]
  rfl

/-- The `G`-side `σ`-image `ω_{ij}^σ ∈ CF(G)` of the certain-type column character `ω_{ij}`, built
from the `ticVdiff` σ-machinery applied to the transported `tic`-side character `omegaProdCharTic`.
This is the right-hand side ingredient of (4.8) conclusion (3). -/
noncomputable def certainTypeOmegaSigma (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) : ClassFunction G ℂ :=
  (ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h)
    ((ticVdiff h).omega (omegaProdCharTic h χ₂ i))

/-- The `σ_G`-image on `V = W − (W₁ ∪ W₂)`: `ω_{ij}^σ(v) = ω_{ij}(v) = chiColumn χ₂ i (e v)`
(`sigma_apply_of_mem_V` (3.2.c) + `omega_apply` + `omegaProdCharTic_apply`). -/
theorem certainTypeOmegaSigma_apply_of_mem_V (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {v : G} (hv : v ∈ (ticVdiff h).V) :
    certainTypeOmegaSigma h χ₂ i v
      = (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          (ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩) := by
  rw [certainTypeOmegaSigma, (ticVdiff h).sigma_apply_of_mem_V rfl _ _ hv,
    (ticVdiff h).omega_apply]
  exact omegaProdCharTic_apply h χ₂ i _

/-- The `σ_G`-image `ω_{ij}^σ` is the `χ`-family member at the index `omegaProdEquiv.symm` of the
transported character: `ω_{ij}^σ = χ_{P_{ij}}` (`sigma_omega`).  This identifies the two `δ`-term
positions `P_{ij}, P_{ik}` in the `σ`-coefficient grid of (4.8). -/
theorem certainTypeOmegaSigma_eq_chiFam (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    certainTypeOmegaSigma h χ₂ i = (ticVdiff h).chiFam rfl (ticVdiffFullDadeApplication h)
      ((ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i)) :=
  (ticVdiff h).sigma_omega rfl (ticVdiffFullDadeApplication h) (omegaProdCharTic h χ₂ i)

/-- **Peterfalvi (4.8), step (1)** (the sign equality `δ_j = δ_k`).  Fix a row `i` and two
columns `χ₂, χ₂'`.  If the certain-type characters `μ_{ij}` and `μ_{ik}` have equal degree at
`1`, then the two column signs coincide.

By the degree congruence (4.3.d), `μ_{ij}(1) ≡ δ_j` and `μ_{ik}(1) ≡ δ_k` modulo `w₁`, so the
equal-degree hypothesis forces `w₁ ∣ (δ_j − δ_k)`.  Since `δ_j, δ_k ∈ {±1}` and `w₁ ≥ 3`
(`W₁ ≠ 1` of odd order), the only multiple of `w₁` in `[-2, 2]` is `0`. -/
theorem certainType_sign_eq_of_degree_eq (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    (h.columnFamily χ₂).sign = (h.columnFamily χ₂').sign := by
  obtain ⟨a, ha⟩ := h.certainType_degree_modEq χ₂ i
  obtain ⟨b, hb⟩ := h.certainType_degree_modEq χ₂' i
  have hw3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1
  -- `δ_j + w₁·a = δ_k + w₁·b` in `ℤ`, transported from the `ℂ`-valued degree identity.
  have hZ : (h.columnFamily χ₂).sign + (Nat.card h.W1 : ℤ) * a
          = (h.columnFamily χ₂').sign + (Nat.card h.W1 : ℤ) * b := by
    have hC : ((h.columnFamily χ₂).sign : ℂ) + (Nat.card h.W1 : ℂ) * (a : ℂ)
            = ((h.columnFamily χ₂').sign : ℂ) + (Nat.card h.W1 : ℂ) * (b : ℂ) := by
      rw [← ha, ← hb]; exact hdeg
    exact_mod_cast hC
  -- Case split on the two signs.  Diagonal cases are reflexive; off-diagonal cases give
  -- `w₁ ∣ 2`, contradicting `w₁ ≥ 3`.
  rcases (h.columnFamily χ₂).sign_eq with hd | hd <;>
    rcases (h.columnFamily χ₂').sign_eq with hd' | hd' <;>
    rw [hd, hd'] at hZ ⊢ <;>
    first
    | rfl
    | (exfalso
       have hdvd : (Nat.card h.W1 : ℤ) ∣ 2 := ⟨b - a, by linear_combination hZ⟩
       have hle := Int.le_of_dvd (by norm_num) hdvd
       omega)
    | (exfalso
       have hdvd : (Nat.card h.W1 : ℤ) ∣ 2 := ⟨a - b, by linear_combination -hZ⟩
       have hle := Int.le_of_dvd (by norm_num) hdvd
       omega)

/-- On `W₁`, the column character `ω_{ij} = chiColumn χ₂ i` is independent of the column `χ₂`:
the `W₂`-projection `wSnd` is trivial on `W₁` (`wSnd_eq_one_of_mem_W1`), so
`ω_{ij}(w) = (w1CharEquiv i)(wFst w)` for every column `χ₂`.  (Generalizes `chiColumn_one_apply`
— the `χ₂ = 1` column for all `w` — to every column, with the point restricted to `W₁`.) -/
theorem chiColumn_apply_of_mem_W1 (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {w : ↥h.sdiffTICyclicHypothesis.W}
    (hw : w ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W) :
    (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) w
      = ((h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w) : ℂ) := by
  have hχ : χ₂ (h.sdiffTICyclicHypothesis.wSnd w) = 1 := by
    rw [h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hw]; exact map_one χ₂
  have h1 : h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂ w
      = (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
        * χ₂ (h.sdiffTICyclicHypothesis.wSnd w) := rfl
  rw [Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply, h1, hχ, mul_one]

/-- **Peterfalvi (4.8), step (2)** (agreement on `W₁`).  Two equal-degree certain-type characters
`μ_{ij}, μ_{ik}` (same row `i`, columns `χ₂, χ₂'`) agree on all of `W₁`, so `μ_{ij} − μ_{ik}`
vanishes there.

On `W₁^# ⊆ W − W₂` the (4.3.c) value identity gives `μ_{ij}(w) = δ_j·ω_{ij}(w)` and
`μ_{ik}(w) = δ_k·ω_{ik}(w)`; `δ_j = δ_k` (step (1), `certainType_sign_eq_of_degree_eq`) and the
column-independence of `ω` on `W₁` (`chiColumn_apply_of_mem_W1`) make these equal.  At `1` it is
the equal-degree hypothesis. -/
theorem certainType_apply_eq_of_mem_W1 (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    {w : ↥L} (hw : w ∈ h.W1) :
    ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) w
      = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) w := by
  by_cases hw1 : w = 1
  · rw [hw1]; exact hdeg
  · -- `w ∈ W₁^# ⊆ sdiff.V = W − W₂`
    have hwV : w ∈ h.sdiffTICyclicHypothesis.V := by
      have hVdef : h.sdiffTICyclicHypothesis.V
          = ((h.W1 ⊔ h.W2 : Subgroup ↥L) : Set ↥L) \ (h.W2 : Set ↥L) := rfl
      rw [hVdef]
      refine ⟨(le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) hw, fun hw2 => hw1 ?_⟩
      exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hw, hw2⟩))
    -- the point `⟨w, _⟩` lies in `W₁` inside `sdiff.W`
    have hwsub : (⟨w, h.sdiffTICyclicHypothesis.V_subset_W hwV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr hw
    rw [h.certainType_apply_eq_of_mem_V χ₂ i hwV, h.certainType_apply_eq_of_mem_V χ₂' i hwV,
      certainType_sign_eq_of_degree_eq h χ₂ χ₂' i hdeg,
      chiColumn_apply_of_mem_W1 h χ₂ i hwsub, chiColumn_apply_of_mem_W1 h χ₂' i hwsub]

/-- **Peterfalvi (4.8), conclusion (1)** (`Supp(μ_{ij} − μ_{ik}) ⊆ A₀`).  For nontrivial columns
`χ₂, χ₂' ≠ 1` and equal degree `μ_{ij}(1) = μ_{ik}(1)`, every point where `μ_{ij} − μ_{ik}` is
nonzero maps (via `L ↪ G`) into `A₀ = A ∪ V^L`.

Proof by cases on `z`:
* `z = 1`: the value is `μ_{ij}(1) − μ_{ik}(1) = 0` (equal degree), so this case is vacuous.
* `z ∈ K` (`z ≠ 1`): `μ_{ij}` and `μ_{ik}` restrict to `K` as `χ_j, χ_k` (`restrict_certainType_eq`,
  `coe_chiRestrict`), and (4.7) (`chiRestrict_apply_eq_zero_of_not_mem_union`) makes both vanish
  unless `L.subtype z ∈ A ∪ {1}`; with `z ≠ 1` this puts `L.subtype z ∈ A`.
* `z ∈ L − K`: by (2.1) (`mem_compl_conj_into_W`) `z` is `L`-conjugate to `x·y` with `x ∈ W₁^#`,
  `y ∈ W₂`; then `x·y ∈ W − W₂`, so its image lies in `tic.V = ↑W \ ↑W₂` (`tic_V`), and
  `L.subtype z` is an `L`-conjugate of it, i.e. lies in `V^L`. -/
theorem certainType_diff_supp_subset_A0 (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    {z : ↥L}
    (hz : (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
          - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ)) z ≠ 0) :
    L.subtype z ∈ (A ∪ {g : G | ∃ l : G, l ∈ L ∧ ∃ v ∈ h.tic.V, g = l * v * l⁻¹} : Set G) := by
  rw [ClassFunction.sub_apply, sub_ne_zero] at hz
  by_cases hz1 : z = 1
  · exact absurd (by rw [hz1]; exact hdeg) hz
  · by_cases hzK : z ∈ h.K
    · -- `z ∈ K`, `z ≠ 1`: land in `A`.
      left
      by_contra hzA
      have hsub1 : L.subtype z ≠ 1 := fun he => hz1 (L.subtype_injective (by simpa using he))
      have hnm : L.subtype z ∉ A ∪ ({1} : Set G) := by
        rintro (h' | h'); exacts [hzA h', hsub1 h']
      have hcoe : ∀ (ξ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
          ξ ≠ 1 → ((h.columnFamily ξ).mu i : ClassFunction ↥L ℂ) z = 0 := by
        intro ξ hξ
        have key := chiRestrict_apply_eq_zero_of_not_mem_union h hξ (g := ⟨z, hzK⟩) hnm
        rwa [h.coe_chiRestrict, ← h.restrict_certainType_eq ξ i, ClassFunction.restrict_apply] at key
      exact hz ((hcoe χ₂ hχ₂).trans (hcoe χ₂' hχ₂').symm)
    · -- `z ∈ L − K`: land in `V^L`.
      right
      obtain ⟨c, x, hxW1, hx1, y, hyW2, hcxy⟩ :=
        (h.toCertainTypeHypothesis.toHypothesis).mem_compl_conj_into_W hzK
      have hz_eq : z = c * (x * y) * c⁻¹ := by rw [← hcxy]; group
      -- `tic.W = (W₁ ⊔ W₂).map L.subtype`.
      have htW : h.tic.W = (h.W1 ⊔ h.W2).map L.subtype := by
        rw [← h.tic.W_sup, h.tic_W1, h.tic_W2, ← Subgroup.map_sup]
      have hxyW : x * y ∈ (h.W1 ⊔ h.W2 : Subgroup ↥L) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hxW1) (Subgroup.mem_sup_right hyW2)
      have hvV : L.subtype (x * y) ∈ h.tic.V := by
        rw [h.tic_V]
        refine ⟨?_, ?_⟩
        · show L.subtype (x * y) ∈ h.tic.W
          rw [htW]; exact Subgroup.mem_map.mpr ⟨x * y, hxyW, rfl⟩
        · show L.subtype (x * y) ∉ h.tic.W2
          rw [h.tic_W2]
          rintro hmem
          obtain ⟨w, hwW2, hweq⟩ := Subgroup.mem_map.mp hmem
          have hwxy : w = x * y := L.subtype_injective hweq
          have hxyW2 : x * y ∈ h.W2 := hwxy ▸ hwW2
          have hxW2 : x ∈ h.W2 := by
            have hx_eq : x = (x * y) * y⁻¹ := by group
            rw [hx_eq]; exact Subgroup.mul_mem _ hxyW2 (Subgroup.inv_mem _ hyW2)
          have hxbot : x ∈ h.W1 ⊓ h.W2 := ⟨hxW1, hxW2⟩
          rw [disjoint_iff.mp h.W_disjoint, Subgroup.mem_bot] at hxbot
          exact hx1 hxbot
      exact ⟨L.subtype c, c.2, L.subtype (x * y), hvV, by rw [hz_eq]; simp [map_mul, map_inv]⟩

/-- `μ_{ij} − μ_{ik}` as an element of Peterfalvi's `CF(L, A₀)` (`SupportedClassFunctions` on
`A₀ = A ∪ V^L`), the domain element fed to the certain-type Dade isometry `τ`.  The support
condition is exactly conclusion (1) `certainType_diff_supp_subset_A0`. -/
noncomputable def certainTypeDiffSupported (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (A ∪ {g : G | ∃ l : G, l ∈ L ∧ ∃ v ∈ h.tic.V, g = l * v * l⁻¹}) L :=
  ⟨((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ), by
    rw [ClassFunction.mem_supportedSubmodule]
    intro z hz
    rw [ClassFunction.mem_support] at hz
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    exact certainType_diff_supp_subset_A0 h hχ₂ hχ₂' i hdeg hz⟩

/-- The certain-type Dade isometry `τ` (= `h.tau`) preserves values on its support `A₀`:
`τ(α)(a) = α(a)` for every `a ∈ A₀`.  Since `a = a · 1` and `1 ∈ H(a)`, the point `a` lies in its
own `H`-coset, so the general `map_eq_of_mem_hCoset` applies even though the certain-type `dade0`
need not have trivial local subgroups. -/
theorem tau_toDadeMap_apply_of_mem (h : Hypothesis46 A L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (A ∪ {g : G | ∃ l : G, l ∈ L ∧ ∃ v ∈ h.tic.V, g = l * v * l⁻¹}) L)
    {a : G} (ha : a ∈ (A ∪ {g : G | ∃ l : G, l ∈ L ∧ ∃ v ∈ h.tic.V, g = l * v * l⁻¹} : Set G)) :
    h.tau.toDadeMap α a = (α : ClassFunction ↥L ℂ) ⟨a, h.dade0.mem_L ha⟩ :=
  h.tau.toDadeIsometryData.isDadeMap.map_eq_of_mem_hCoset α ⟨a, ha⟩
    ⟨1, one_mem _, (mul_one _).symm⟩

/-- **Peterfalvi (4.8), step (4)** (the two sides agree on `V`).  For `v ∈ V = W − (W₁ ∪ W₂)`,
`(μ_{ij} − μ_{ik})^τ(v) = δ_j·(ω_{ij}^σ(v) − ω_{ik}^σ(v))`.

On `V` both maps are value-preserving: `τ` preserves values on `A₀ ⊇ V^L`
(`tau_toDadeMap_apply_of_mem`) and `σ_G` on `V` (`certainTypeOmegaSigma_apply_of_mem_V`).  Writing
`w = e v` for the `sdiff.W` partner of `v` (`ticWEquivSdiffW`), the (4.3.c) value identity gives
`μ_{ij}(w) = δ_j·ω_{ij}(w)`, `μ_{ik}(w) = δ_k·ω_{ik}(w)`, and `δ_j = δ_k` (step (1)) makes the two
sides coincide. -/
theorem certainType_diff_dade_apply_eq_of_mem_V (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    {v : G} (hv : v ∈ (ticVdiff h).V) :
    h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg) v
      = ((h.columnFamily χ₂).sign : ℂ)
        * (certainTypeOmegaSigma h χ₂ i v - certainTypeOmegaSigma h χ₂' i v) := by
  -- `v ∈ tic.V` (the larger TI set), hence `v ∈ A₀`
  have hv_ticV : v ∈ h.tic.V := by
    rw [h.tic_V]; exact ⟨hv.1, fun h2 => hv.2 (Or.inr h2)⟩
  have hvA0 : v ∈ (A ∪ {g : G | ∃ l : G, l ∈ L ∧ ∃ u ∈ h.tic.V, g = l * u * l⁻¹} : Set G) :=
    Or.inr ⟨1, Subgroup.one_mem L, v, hv_ticV, by group⟩
  -- the `sdiff.W` partner `w = e v`, with `(w : L) = ⟨v, _⟩` and `(w : L) ∈ sdiff.V`
  set w : h.sdiffTICyclicHypothesis.W := ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩ with hw
  have hwG : ((w : ↥L) : G) = v := coe_ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩
  have hwL : (w : ↥L) = ⟨v, h.dade0.mem_L hvA0⟩ := Subtype.ext hwG
  have hwsdiffV : (w : ↥L) ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨w.2, fun hW2 => ?_⟩
    have hvW2 : v ∈ h.tic.W2 := by
      rw [h.tic_W2]; exact ⟨(w : ↥L), hW2, hwG⟩
    exact hv.2 (Or.inr hvW2)
  -- the point `⟨(w:L), _⟩ : sdiff.W` is `w` itself
  have hwpt : (⟨(w : ↥L), h.sdiffTICyclicHypothesis.V_subset_W hwsdiffV⟩ :
      h.sdiffTICyclicHypothesis.W) = w := Subtype.ext rfl
  rw [tau_toDadeMap_apply_of_mem h _ hvA0]
  show (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ)) ⟨v, h.dade0.mem_L hvA0⟩ = _
  rw [ClassFunction.sub_apply, ← hwL,
    h.certainType_apply_eq_of_mem_V χ₂ i hwsdiffV,
    h.certainType_apply_eq_of_mem_V χ₂' i hwsdiffV, hwpt,
    certainTypeOmegaSigma_apply_of_mem_V h χ₂ i hv,
    certainTypeOmegaSigma_apply_of_mem_V h χ₂' i hv,
    certainType_sign_eq_of_degree_eq h χ₂ χ₂' i hdeg]
  ring

/-- **Peterfalvi (4.8), step (5) input** (`‖φ‖² = 2`).  For distinct columns `χ₂ ≠ χ₂'`, the Dade
image `φ = (μ_{ij} − μ_{ik})^τ` is a virtual character of squared norm `2`: `τ` is an isometry
(`h.tau.inner_eq`), `μ_{ij}, μ_{ik}` are distinct irreducibles (`columnFamily_mu_ne`, (4.1)), so
`⟨φ, φ⟩ = ⟨μ_{ij} − μ_{ik}, μ_{ij} − μ_{ik}⟩ = 1 + 1 = 2`. -/
theorem certainType_diff_dade_inner_self (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    ClassFunction.inner (h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg))
        (h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg)) = 2 := by
  rw [h.tau.inner_eq]
  show ClassFunction.inner
      (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
        - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ))
      (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
        - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ)) = 2
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    irreducibleCharacter_inner_eq_ite, irreducibleCharacter_inner_eq_ite,
    irreducibleCharacter_inner_eq_ite, irreducibleCharacter_inner_eq_ite, if_pos rfl, if_pos rfl,
    if_neg (h.columnFamily_mu_ne hχ i i), if_neg (h.columnFamily_mu_ne hχ i i).symm]
  ring

/-- **Peterfalvi (4.8), step (6) input** (`NC(φ) ≤ 2`).  The Dade image `φ = (μ_{ij} − μ_{ik})^τ`,
of squared norm `2`, has at most two nonzero `σ`-image coefficients.  By `mem_ZIrr_inner_self_eq_sum_sq`
+ `exists_pair_of_sum_sq_eq_two` it is `ε_α·α + ε_β·β` for two distinct irreducibles `α, β`; each of
`α, β` has `≤ 1` nonzero inner product against the orthonormal `χ`-family
(`ncard_inner_chiFam_ne_zero_le_one`), and `Supp(φ-coeffs) ⊆ S_α ∪ S_β`. -/
theorem sigmaNC_dade_le_two (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    (ticVdiff h).sigmaNC rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg)) ≤ 2 := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) := Fintype.ofFinite _
  haveI hfprod : Fintype (((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
    ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ)) := inferInstance
  haveI : Finite (((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
    ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ)) := Finite.of_fintype _
  set φ := h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg) with hφdef
  have hφZ : φ ∈ ZIrr G := h.tau.maps_virtualCharacter _
    ((ZIrr (↥L)).sub_mem ((h.columnFamily χ₂).mu i).mem_ZIrr
      ((h.columnFamily χ₂').mu i).mem_ZIrr)
  have hφ2 : ClassFunction.inner φ φ = 2 := certainType_diff_dade_inner_self h hχ hχ₂ hχ₂' i hdeg
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφZ
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hφ2
  obtain ⟨α, β, hαβ, hs, -, -⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hαZ : α ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨α, hαm⟩ : IrreducibleCharacter G)
  have hβZ : β ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨β, hβm⟩ : IrreducibleCharacter G)
  have hα1 : ClassFunction.inner α α = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ⟨α, hαm⟩
    rwa [if_pos rfl] at this
  have hβ1 : ClassFunction.inner β β = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ⟨β, hβm⟩
    rwa [if_pos rfl] at this
  have hφαβ : φ = (c α : ℂ) • α + (c β : ℂ) • β := by
    rw [hrepr, hs, Finset.sum_pair hαβ]
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaNC]
  refine le_trans (Set.ncard_le_ncard (t :=
    {pq | ClassFunction.inner α ((ticVdiff h).chiFam rfl (ticVdiffFullDadeApplication h) pq) ≠ 0} ∪
    {pq | ClassFunction.inner β ((ticVdiff h).chiFam rfl (ticVdiffFullDadeApplication h) pq) ≠ 0})
    ?_ (Set.finite_univ.subset (Set.subset_univ _))) (le_trans (Set.ncard_union_le _ _) ?_)
  · intro pq hpq
    simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff, Set.mem_setOf_eq] at hpq
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    exact hpq (by rw [hφαβ, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, hcon.1, hcon.2, mul_zero, mul_zero, add_zero])
  · exact add_le_add
      ((ticVdiff h).ncard_inner_chiFam_ne_zero_le_one rfl (ticVdiffFullDadeApplication h) hαZ hα1)
      ((ticVdiff h).ncard_inner_chiFam_ne_zero_le_one rfl (ticVdiffFullDadeApplication h) hβZ hβ1)

/-- **Peterfalvi (4.8), step (7) input** (the `σ`-coefficients of `φ` lie in `{0, ±1}`).  Writing
`φ = ε_α·α + ε_β·β` (norm-2 ⟹ two constituents) and `χ_{pq} = ε·ν` (norm-1 classifier), the
coefficient `⟨φ, χ_{pq}⟩` is `ε_α·ε` if `ν = α`, `ε_β·ε` if `ν = β`, and `0` otherwise (`α ≠ β`).
This `|·| ≤ 1` bound (beyond `NC ≤ 2`) is what excludes the `w₂ = 3` row case in the trichotomy
endgame, where a coefficient would otherwise be `±2`. -/
theorem sigmaCoeff_dade_eq_zero_or_one (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    (pq : ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
        ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ)) :
    (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg)) pq = 0 ∨
      (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg)) pq = 1 ∨
      (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg)) pq = -1 := by
  classical
  haveI : Finite G := Finite.of_fintype G
  set φ := h.tau.toDadeMap (certainTypeDiffSupported h hχ₂ hχ₂' i hdeg) with hφdef
  have hφZ : φ ∈ ZIrr G := h.tau.maps_virtualCharacter _
    ((ZIrr (↥L)).sub_mem ((h.columnFamily χ₂).mu i).mem_ZIrr
      ((h.columnFamily χ₂').mu i).mem_ZIrr)
  have hφ2 : ClassFunction.inner φ φ = 2 := certainType_diff_dade_inner_self h hχ hχ₂ hχ₂' i hdeg
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφZ
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hφ2
  obtain ⟨α, β, hαβ, hs, hcα, hcβ⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  obtain ⟨ε, ν, hε, hν⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one
    (((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.1 pq)
    (by rw [((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1, if_pos rfl])
  -- the two irreducible inner products (type ascription absorbs the `CF ↔ IrreducibleCharacter` coe)
  have hαν : ClassFunction.inner α (ν : ClassFunction G ℂ)
      = if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ν
  have hβν : ClassFunction.inner β (ν : ClassFunction G ℂ)
      = if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ν
  have hf : (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h) φ pq
      = (c α : ℂ) * ((ε : ℂ) * (if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0))
        + (c β : ℂ) * ((ε : ℂ) * (if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0)) := by
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff, hrepr, hs, Finset.sum_pair hαβ, hν,
      ← Int.cast_smul_eq_zsmul ℂ ε, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast, hαν, hβν]
  rw [hf]
  by_cases hαe : (⟨α, hαm⟩ : IrreducibleCharacter G) = ν
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · exact absurd (Subtype.ext_iff.mp (hαe.trans hβe.symm)) hαβ
    · rw [if_pos hαe, if_neg hβe]
      simp only [mul_one, mul_zero, add_zero]
      rcases hcα with hcα | hcα <;> rcases hε with hε | hε <;> rw [hcα, hε] <;> norm_num
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · rw [if_neg hαe, if_pos hβe]
      simp only [mul_one, mul_zero, add_zero, zero_add]
      rcases hcβ with hcβ | hcβ <;> rcases hε with hε | hε <;> rw [hcβ, hε] <;> norm_num
    · rw [if_neg hαe, if_neg hβe]; left; ring

open scoped Classical in
/-- The `σ`-coefficient grid of `ψ = φ − δ_j·(ω_{ij}^σ − ω_{ik}^σ)`.  As `ω_{ij}^σ = χ_{P_{ij}}`
(`certainTypeOmegaSigma_eq_chiFam`) and the `χ`-family is orthonormal, the `δ`-part contributes
`∓δ_j` exactly at the two grid positions `P_{ij}, P_{ik}`:
`a(pq) = ⟨φ, χ_{pq}⟩ − δ_j·([P_{ij} = pq] − [P_{ik} = pq])`. -/
theorem sigmaCoeff_psi_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) (φ : ClassFunction G ℂ)
    (pq : ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
        ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ)) :
    (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (φ - (h.columnFamily χ₂).sign •
          (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i)) pq
      = (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h) φ pq
        - ((h.columnFamily χ₂).sign : ℂ)
          * ((if (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i) = pq then (1 : ℂ) else 0)
            - (if (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂' i) = pq
                then (1 : ℂ) else 0)) := by
  simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff]
  rw [certainTypeOmegaSigma_eq_chiFam, certainTypeOmegaSigma_eq_chiFam,
    ClassFunction.inner_sub_left, ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign,
    ClassFunction.inner_smul_left, ClassFunction.inner_sub_left,
    ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1,
    ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1]

/-- For distinct columns `χ₂ ≠ χ₂'`, the transported `tic`-side characters are distinct:
`omegaProdCharTic` is injective in the column.  (Precompose-cancel the bridge iso `e`, then
`omegaProdChar_inj`.) -/
theorem omegaProdCharTic_ne (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂') (i : Fin (Nat.card h.W1)) :
    omegaProdCharTic h χ₂ i ≠ omegaProdCharTic h χ₂' i := by
  intro heq
  refine hχ (h.sdiffTICyclicHypothesis.omegaProdChar_inj (χ₁ := h.w1CharEquiv i)
    (χ₁' := h.w1CharEquiv i) (MonoidHom.ext fun w => ?_)).2
  obtain ⟨w', rfl⟩ := (ticWEquivSdiffW h).surjective w
  exact DFunLike.congr_fun heq w'

/-- The two `σ`-image grid indices are distinct: `P_{ij} ≠ P_{ik}` for `χ₂ ≠ χ₂'`
(`omegaProdEquiv.symm` is injective and `omegaProdCharTic` is column-injective). -/
theorem omegaProdEquiv_symm_omegaProdCharTic_ne (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂') (i : Fin (Nat.card h.W1)) :
    (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i)
      ≠ (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂' i) :=
  fun heq => omegaProdCharTic_ne h hχ i ((ticVdiff h).omegaProdEquiv.symm.injective heq)

end OddOrder.Peterfalvi.S06
