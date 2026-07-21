/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyReductions

/-!
# Peterfalvi Appendix IV: Feit–Sibley — reduction (1) chief-factor induction support (pp. 146–147)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 146–147.  Supply for assembling the reduction (1) induction of
the Theorem (campaign issue 1054) from the one-step lemma
`ssetOf_coherent_step` of `FeitSibleyReductions`:

* `Subgroup.Normal` converters turning the elementwise `H`- (resp. `Q`-)
  invariance the induction carries into the relativised instance hypotheses the
  step lemma consumes;
* the central lift `Z = centralLift Q₃ _` of `Z(Q₁⧸Q₃)` ("`Z/Q₃ = Z(Q₁/Q₃)`",
  p. 146), defined elementwise, with its lattice position and `H`-invariance;
* minimal `H`-invariant subgroups over a given one (the chief-factor choice
  "`Q₂/Q₃` a chief factor of `H`");
* the per-prime divisibility `p ∣ |K⧸R|` for `R ≤ [K,K]` in a finite nilpotent
  `K` (via the normal `p`-complement), feeding the "`Z(Q₁/Q₃)` is not a
  `q`-group" step.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-! ## `Subgroup.Normal` converters for the relativised instance hypotheses -/

/-- Elementwise `H`-invariance of `R ≤ G` gives the `(R.subgroupOf H).Normal`
instance consumed by the counting side of `ssetOf_coherent_step`. -/
theorem subgroupOf_H_normal_of_conj_mem {R : Subgroup G}
    (hR : ∀ h ∈ hyp.H, ∀ x ∈ R, h * x * h⁻¹ ∈ R) :
    (R.subgroupOf hyp.H).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using hR g g.2 n hn

/-- Elementwise `Q`-invariance of `R ≤ G` gives the doubly relativised
`Normal` instance consumed by the (1.2) side of `ssetOf_coherent_step`. -/
theorem subgroupOf_Q_normal_of_conj_mem {R : Subgroup G}
    (hR : ∀ q ∈ hyp.Q, ∀ x ∈ R, q * x * q⁻¹ ∈ R) :
    ((R.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  simpa using hR g (Subgroup.mem_subgroupOf.mp g.2) n hn

/-- Elementwise `W`-invariance gives `(R.subgroupOf W).Normal` (the generic
form of `subgroupOf_H_normal_of_conj_mem`, used at `W = Q₁` for the quotient
`Q₁⧸Q₃`). -/
theorem subgroupOf_normal_of_conj_mem {R W : Subgroup G}
    (hR : ∀ w ∈ W, ∀ x ∈ R, w * x * w⁻¹ ∈ R) : (R.subgroupOf W).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using hR g g.2 n hn

/-! ## The central lift `Z` of `Z(Q₁⧸Q₃)` (p. 146) -/

/-- **The central lift `Z ≤ Q₁` of `Z(Q₁⧸Q₃)`** for a `Q₁`-invariant `Q₃`: the
elements of `Q₁` whose commutators with all of `Q₁` land in `Q₃`.  This is the
subgroup called `Z` in reduction (1) ("`Z/Q₃ = Z(Q₁/Q₃)`", p. 146), defined
elementwise so that the chief-factor data of `ssetOf_coherent_step`
(`hcentralZ`, invariances) reads off directly. -/
def centralLift (Q₃ : Subgroup G)
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃) : Subgroup G where
  carrier := {z | z ∈ hyp.Q1 ∧ ∀ y ∈ hyp.Q1, ⁅z, y⁆ ∈ Q₃}
  one_mem' := ⟨hyp.Q1.one_mem, fun y _ => by
    have h1 : ⁅(1 : G), y⁆ = 1 := by rw [commutatorElement_def]; group
    rw [h1]
    exact Q₃.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haQ1, ha⟩ ⟨hbQ1, hb⟩
    refine ⟨hyp.Q1.mul_mem haQ1 hbQ1, fun y hy => ?_⟩
    have hkey : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hkey]
    exact Q₃.mul_mem (hinv a haQ1 _ (hb y hy)) (ha y hy)
  inv_mem' := by
    rintro a ⟨haQ1, ha⟩
    refine ⟨hyp.Q1.inv_mem haQ1, fun y hy => ?_⟩
    have hkey : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * (a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hkey]
    exact hinv a⁻¹ (hyp.Q1.inv_mem haQ1) _ (Q₃.inv_mem (ha y hy))

theorem mem_centralLift {Q₃ : Subgroup G}
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃) {z : G} :
    z ∈ hyp.centralLift Q₃ hinv ↔ z ∈ hyp.Q1 ∧ ∀ y ∈ hyp.Q1, ⁅z, y⁆ ∈ Q₃ :=
  Iff.rfl

theorem centralLift_le_Q1 {Q₃ : Subgroup G}
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃) :
    hyp.centralLift Q₃ hinv ≤ hyp.Q1 := fun _ hz => hz.1

/-- `Q₃ ≤ Z`: the base sits inside its central lift (conjugates of members of
`Q₃` by `Q₁` stay in `Q₃`). -/
theorem le_centralLift {Q₃ : Subgroup G}
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃) (hQ₃Q1 : Q₃ ≤ hyp.Q1) :
    Q₃ ≤ hyp.centralLift Q₃ hinv := by
  intro x hx
  refine ⟨hQ₃Q1 hx, fun y hy => ?_⟩
  have hkey : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hkey]
  exact Q₃.mul_mem hx (hinv y hy x⁻¹ (Q₃.inv_mem hx))

/-- **`Z` is `H`-invariant**: conjugation by `h ∈ H` preserves `Q₁`
(`Q1_normal_in_H`) and `Q₃`, and transports the central-commutator condition. -/
theorem centralLift_conj_mem_of_mem_H [Finite G] {Q₃ : Subgroup G}
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃)
    (hQ₃H : ∀ h ∈ hyp.H, ∀ x ∈ Q₃, h * x * h⁻¹ ∈ Q₃)
    {h : G} (hh : h ∈ hyp.H) {z : G} (hz : z ∈ hyp.centralLift Q₃ hinv) :
    h * z * h⁻¹ ∈ hyp.centralLift Q₃ hinv := by
  obtain ⟨hzQ1, hzc⟩ := hz
  refine ⟨hyp.Q1_normal_in_H hh hzQ1, fun y hy => ?_⟩
  have hy' : h⁻¹ * y * (h⁻¹)⁻¹ ∈ hyp.Q1 :=
    hyp.Q1_normal_in_H (hyp.H.inv_mem hh) hy
  have hkey : ⁅h * z * h⁻¹, y⁆ = h * ⁅z, h⁻¹ * y * (h⁻¹)⁻¹⁆ * h⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hkey]
  exact hQ₃H h hh _ (hzc _ hy')

/-! ## Minimal `H`-invariant subgroups (the chief-factor choice) -/

/-- **A minimal `H`-invariant subgroup strictly over `Q₃` inside `W`** exists
(finite subgroup lattice): the choice "`Q₂ ⊴ H` with `Q₂/Q₃` a chief factor of
`H`" of reduction (1).  Minimality is phrased for the consumers: any
`H`-invariant `Q₂'` with `Q₃ < Q₂' ≤ Q₂` equals `Q₂`. -/
theorem exists_minimal_conjInvariant_between [Finite G] {Q₃ W : Subgroup G}
    (hlt : Q₃ < W)
    (hWinv : ∀ h ∈ hyp.H, ∀ x ∈ W, h * x * h⁻¹ ∈ W) :
    ∃ Q₂ : Subgroup G, Q₃ < Q₂ ∧ Q₂ ≤ W ∧
      (∀ h ∈ hyp.H, ∀ x ∈ Q₂, h * x * h⁻¹ ∈ Q₂) ∧
      ∀ Q₂' : Subgroup G, Q₃ < Q₂' → Q₂' ≤ Q₂ →
        (∀ h ∈ hyp.H, ∀ x ∈ Q₂', h * x * h⁻¹ ∈ Q₂') → Q₂' = Q₂ := by
  classical
  set S : Set (Subgroup G) :=
    {K | Q₃ < K ∧ K ≤ W ∧ ∀ h ∈ hyp.H, ∀ x ∈ K, h * x * h⁻¹ ∈ K} with hS_def
  obtain ⟨Q₂, hQ₂S, hmin⟩ :=
    (Set.toFinite S).exists_minimal ⟨W, hlt, le_rfl, hWinv⟩
  obtain ⟨hQ₂gt, hQ₂le, hQ₂inv⟩ := hQ₂S
  refine ⟨Q₂, hQ₂gt, hQ₂le, hQ₂inv, fun Q₂' hgt hle hinv' => ?_⟩
  exact le_antisymm hle (hmin ⟨hgt, hle.trans hQ₂le, hinv'⟩ hle)

/-- **The chief factor sits in the centre** (p. 146: "Since `Q₁` is nilpotent,
`(Q₂/Q₃) ∩ Z(Q₁/Q₃) ≠ 1`", and minimality forces `Q₂/Q₃ ⊆ Z(Q₁/Q₃)`): a
minimal `H`-invariant `Q₂` strictly over `Q₃` inside the nilpotent `Q₁` lies
in the central lift `Z`.  The intersection `Q₂ ⊓ Z` is `H`-invariant, contains
`Q₃`, and is strictly bigger by
`exists_mem_center_of_normal_ne_bot_of_isNilpotent` applied to the image of
`Q₂` in `Q₁⧸Q₃`; minimality then gives `Q₂ ⊓ Z = Q₂`. -/
theorem minimal_le_centralLift [Finite G] (hnil : Group.IsNilpotent ↥hyp.Q1)
    {Q₂ Q₃ : Subgroup G} (hQ₃Q₂ : Q₃ < Q₂) (hQ₂Q1 : Q₂ ≤ hyp.Q1)
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃)
    (hQ₂H : ∀ h ∈ hyp.H, ∀ x ∈ Q₂, h * x * h⁻¹ ∈ Q₂)
    (hQ₃H : ∀ h ∈ hyp.H, ∀ x ∈ Q₃, h * x * h⁻¹ ∈ Q₃)
    (hmin : ∀ Q₂' : Subgroup G, Q₃ < Q₂' → Q₂' ≤ Q₂ →
        (∀ h ∈ hyp.H, ∀ x ∈ Q₂', h * x * h⁻¹ ∈ Q₂') → Q₂' = Q₂) :
    Q₂ ≤ hyp.centralLift Q₃ hinv := by
  classical
  haveI := hnil
  haveI : (Q₃.subgroupOf hyp.Q1).Normal := subgroupOf_normal_of_conj_mem hinv
  haveI : (Q₂.subgroupOf hyp.Q1).Normal :=
    subgroupOf_normal_of_conj_mem fun q hq x hx => hQ₂H q (hyp.Q1_le_H hq) x hx
  -- the image of `Q₂` in `Q₁⧸Q₃` is a nontrivial normal subgroup
  set π := QuotientGroup.mk' (Q₃.subgroupOf hyp.Q1) with hπ_def
  set Qbar : Subgroup (↥hyp.Q1 ⧸ Q₃.subgroupOf hyp.Q1) :=
    (Q₂.subgroupOf hyp.Q1).map π with hQbar_def
  haveI : Qbar.Normal :=
    Subgroup.Normal.map ‹(Q₂.subgroupOf hyp.Q1).Normal› π
      (QuotientGroup.mk'_surjective _)
  have hQbar_ne : Qbar ≠ ⊥ := by
    obtain ⟨x, hxQ₂, hxQ₃⟩ := SetLike.exists_of_lt hQ₃Q₂
    intro hbot
    have hxmem : π (⟨x, hQ₂Q1 hxQ₂⟩ : ↥hyp.Q1) ∈ Qbar :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxQ₂)
    rw [hbot, Subgroup.mem_bot, hπ_def, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hxmem
    exact hxQ₃ (Subgroup.mem_subgroupOf.mp hxmem)
  -- a nonidentity central element of the image
  obtain ⟨xbar, hxbarQ, hxbarC, hxbar1⟩ :=
    OddOrder.Isaacs.Ch04.exists_mem_center_of_normal_ne_bot_of_isNilpotent hQbar_ne
  obtain ⟨w, hwQ, hwπ⟩ := hxbarQ
  -- its lift lands in `Q₂ ⊓ Z` but not in `Q₃`
  have hwZ : (w : G) ∈ hyp.centralLift Q₃ hinv := by
    refine ⟨w.2, fun y hy => ?_⟩
    have hcomm : π ⁅w, (⟨y, hy⟩ : ↥hyp.Q1)⁆ = 1 := by
      rw [map_commutatorElement, hwπ]
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hxbarC _).symm
    rw [hπ_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hcomm
    simpa [commutatorElement_def] using hcomm
  have hwQ₂ : (w : G) ∈ Q₂ := Subgroup.mem_subgroupOf.mp hwQ
  have hwQ₃ : (w : G) ∉ Q₃ := by
    intro hmem
    apply hxbar1
    rw [← hwπ, hπ_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hmem
  -- minimality: `Q₂ ⊓ Z = Q₂`
  have hZH : ∀ h ∈ hyp.H, ∀ x ∈ hyp.centralLift Q₃ hinv,
      h * x * h⁻¹ ∈ hyp.centralLift Q₃ hinv := fun h hh x hx =>
    hyp.centralLift_conj_mem_of_mem_H hinv hQ₃H hh hx
  have hlt' : Q₃ < Q₂ ⊓ hyp.centralLift Q₃ hinv := by
    rw [lt_iff_le_and_ne]
    constructor
    · exact le_inf hQ₃Q₂.le (hyp.le_centralLift hinv (hQ₃Q₂.le.trans hQ₂Q1))
    · intro heq
      exact hwQ₃ (heq ▸ (⟨hwQ₂, hwZ⟩ : (w : G) ∈ Q₂ ⊓ hyp.centralLift Q₃ hinv))
  have heq := hmin (Q₂ ⊓ hyp.centralLift Q₃ hinv) hlt' inf_le_left
    (fun h hh x hx => ⟨hQ₂H h hh x hx.1, hZH h hh x hx.2⟩)
  rw [← heq]
  exact inf_le_right

end Hypothesis

/-! ## Per-prime divisibility below the derived subgroup -/

namespace Hypothesis

/-- **`p ∣ |K⧸R|` for `R ≤ [K,K]` in a finite nilpotent `K` with `p ∣ |K|`**:
otherwise the Sylow `p`-subgroup would land in `R ≤ [K,K]`, making
`[K,K]·N_p = K` against `commutator_sup_normal_pcomplement_ne_top`.  This
feeds "`Z(Q₁/Q₃)` is divisible by both primes" in the reduction (1)
chief-factor step. -/
theorem prime_dvd_card_quotient_of_le_commutator {K : Type*} [Group K] [Finite K]
    [Group.IsNilpotent K] {p : ℕ} [hp : Fact p.Prime] (hpK : p ∣ Nat.card K)
    {R : Subgroup K} [R.Normal] (hR : R ≤ commutator K) :
    p ∣ Nat.card (K ⧸ R) := by
  classical
  by_contra hnd
  obtain ⟨N, hNnormal, hNC⟩ :=
    OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent (H := K) (p := p)
  haveI := hNnormal
  set P : Sylow p K := default with hP_def
  have hC := hNC P
  -- the image of `P` in `K⧸R` is a `p`-group of order dividing the
  -- `p`-prime `|K⧸R|`, hence trivial
  have himg : IsPGroup p ↥((P : Subgroup K).map (QuotientGroup.mk' R)) :=
    P.isPGroup'.map _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp himg
  have hn0 : n = 0 := by
    by_contra h0
    apply hnd
    have hpdvd : p ∣ Nat.card ↥((P : Subgroup K).map (QuotientGroup.mk' R)) := by
      rw [hn]
      exact dvd_pow_self p h0
    exact hpdvd.trans (Subgroup.card_subgroup_dvd_card _)
  have hPle : (P : Subgroup K) ≤ R := by
    have hbot : (P : Subgroup K).map (QuotientGroup.mk' R) = ⊥ := by
      rw [← Subgroup.card_eq_one, hn, hn0, pow_zero]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  apply commutator_sup_normal_pcomplement_ne_top hpK hC
  rw [eq_top_iff, ← hC.sup_eq_top]
  exact sup_le le_sup_right ((hPle.trans hR).trans le_sup_left)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
