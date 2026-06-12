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

This file develops the proof in stages (Peterfalvi's eight-step argument).  The present
commit lands **step (1)**: the sign equality `δ_j = δ_k`, an independent consequence of the
degree congruence (4.3.d) and `w₁ > 2`.

## Step (1): `δ_j = δ_k`

By (4.3.d) (`certainType_degree_modEq`) there are integers `a, b` with
`μ_{ij}(1) = δ_j + a·w₁` and `μ_{ik}(1) = δ_k + b·w₁`.  The equal-degree hypothesis gives
`δ_j − δ_k = (b − a)·w₁`, so `w₁ ∣ (δ_j − δ_k)`.  As `δ_j, δ_k ∈ {±1}` we have
`|δ_j − δ_k| ≤ 2 < 3 ≤ w₁` (`three_le_card_W1`: `W₁ ≠ 1` is of odd order), forcing
`δ_j − δ_k = 0`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md` ("session 30").
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- The canonical (3.1)-for-`G` Dade application of (4.6.b): the §4 Dade package on the ambient
TI set `V = W − W₂ ⊆ G` of `h.tic`, whose local subgroups are all trivial (`H(a) = ⊥`), so
`HConjInvariant` holds for free.  This `app` drives the §5 `σ`-machinery (`σ_G`) on `(G, W)`, the
`G`-side isometry `ω_{ij}^σ ∈ CF(G)` used in (4.8) conclusion (3).  (Mirror of the `(L, W)`-side
`toTICyclicFullDadeApplication`, the same `HConjInvariant.of_forall_H_eq_bot` recipe.) -/
noncomputable def ticFullDadeApplication (h : Hypothesis46 A L)
    [Fintype h.tic.W] [Invertible (Nat.card h.tic.W : ℂ)] :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication h.tic :=
  ⟨h.tic.toDadeHypothesis.fullDadeIsometryData
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

end OddOrder.Peterfalvi.S06
