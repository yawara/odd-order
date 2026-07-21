/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyReductions
import OddOrder.Isaacs.Ch09_MoreSubnormality.NilpotentResidual

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

/-! ## `S ⊴ H`, `⁅Q₁,Q₁⁆ ⊴ H`, and conjugation-closure of joins -/

/-- **`π'`-element characterisation of `S`** (mirror of
`mem_Q1_of_mem_Q_of_coprime_orderOf`): an element of `Q = S × Q₁` whose order
is coprime to `|Q₁|` lies in `S`. -/
theorem mem_S_of_mem_Q_of_coprime_orderOf [Finite G] {w : G} (hw : w ∈ hyp.Q)
    (hcop : Nat.Coprime (orderOf w) (Nat.card ↥hyp.Q1)) : w ∈ hyp.S := by
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hw
  obtain ⟨s, hs, y, hy, hsy⟩ := Set.mem_mul.mp hw
  rw [SetLike.mem_coe] at hs hy
  have hcomm : Commute s y := hyp.S_commutes_Q1 s hs y hy
  have hos_dvd : orderOf s ∣ Nat.card ↥hyp.S := hyp.S.orderOf_dvd_natCard hs
  have hoy_dvd : orderOf y ∣ Nat.card ↥hyp.Q1 := hyp.Q1.orderOf_dvd_natCard hy
  have hcop_orders : Nat.Coprime (orderOf s) (orderOf y) :=
    (hyp.coprime_S_Q1.coprime_dvd_left hos_dvd).coprime_dvd_right hoy_dvd
  have how : orderOf w = orderOf s * orderOf y := by
    rw [← hsy]
    exact hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders
  have hoy_dvd_w : orderOf y ∣ orderOf w := by
    rw [how]
    exact dvd_mul_left _ _
  have hcs : Nat.Coprime (orderOf y) (Nat.card ↥hyp.Q1) :=
    hcop.coprime_dvd_left hoy_dvd_w
  have hone : orderOf y ∣ 1 := by
    have hg : Nat.gcd (orderOf y) (Nat.card ↥hyp.Q1) = 1 := hcs
    exact hg ▸ Nat.dvd_gcd dvd_rfl hoy_dvd
  have hyone : y = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  rw [← hsy, hyone, mul_one]
  exact hs

/-- **`S ⊴ H`** (elementwise; mirror of `Q1_normal_in_H`): conjugates stay in
`Q` with unchanged order coprime to `|Q₁|`. -/
theorem S_normal_in_H [Finite G] {h : G} (hh : h ∈ hyp.H) {x : G}
    (hx : x ∈ hyp.S) : h * x * h⁻¹ ∈ hyp.S := by
  have hconjQ : h * x * h⁻¹ ∈ hyp.Q :=
    hyp.Q_normal_in_H h hh x (hyp.S_le_Q hx)
  have hox : orderOf x ∣ Nat.card ↥hyp.S := hyp.S.orderOf_dvd_natCard hx
  have hoconj : orderOf (h * x * h⁻¹) = orderOf x := by
    have h1 := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
    simpa [MulAut.conj_apply] using h1
  refine hyp.mem_S_of_mem_Q_of_coprime_orderOf hconjQ ?_
  rw [hoconj]
  exact hyp.coprime_S_Q1.coprime_dvd_left hox

/-- Conjugation by `h ∈ H` fixes `Q₁` as a set (both inclusions of
`Q1_normal_in_H`). -/
theorem Q1_map_conj_eq [Finite G] {h : G} (hh : h ∈ hyp.H) :
    hyp.Q1.map (MulAut.conj h).toMonoidHom = hyp.Q1 := by
  apply le_antisymm
  · rintro _ ⟨x, hxQ1, rfl⟩
    exact hyp.Q1_normal_in_H hh hxQ1
  · intro x hxQ1
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    · have h1 := hyp.Q1_normal_in_H (hyp.H.inv_mem hh) hxQ1
      simpa using h1
    · simp [MulAut.conj]
      group

/-- **`⁅Q₁,Q₁⁆ ⊴ H`** (elementwise; mirror of `Qder_conj_mem_of_mem_H`):
`H`-conjugation fixes `Q₁`, hence its commutator subgroup. -/
theorem Q1der_conj_mem_of_mem_H [Finite G] {h : G} (hh : h ∈ hyp.H) {x : G}
    (hx : x ∈ ⁅hyp.Q1, hyp.Q1⁆) : h * x * h⁻¹ ∈ ⁅hyp.Q1, hyp.Q1⁆ := by
  have hmap : (⁅hyp.Q1, hyp.Q1⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom
      = ⁅hyp.Q1, hyp.Q1⁆ := by
    rw [Subgroup.map_commutator, hyp.Q1_map_conj_eq hh]
  rw [← hmap]
  exact ⟨x, hx, rfl⟩

/-- **`Sder ⊴ H`** (elementwise): `H`-conjugation fixes `S` (`S_normal_in_H`),
hence `[S,S]`. -/
theorem Sder_conj_mem_of_mem_H [Finite G] {h : G} (hh : h ∈ hyp.H) {x : G}
    (hx : x ∈ hyp.Sder) : h * x * h⁻¹ ∈ hyp.Sder := by
  have hSmap : hyp.S.map (MulAut.conj h).toMonoidHom = hyp.S := by
    apply le_antisymm
    · rintro _ ⟨y, hyS, rfl⟩
      exact hyp.S_normal_in_H hh hyS
    · intro y hyS
      refine ⟨h⁻¹ * y * h, ?_, ?_⟩
      · have h1 := hyp.S_normal_in_H (hyp.H.inv_mem hh) hyS
        simpa using h1
      · simp [MulAut.conj]
        group
  have hmap : hyp.Sder.map (MulAut.conj h).toMonoidHom = hyp.Sder := by
    change (⁅hyp.S, hyp.S⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom = ⁅hyp.S, hyp.S⁆
    rw [Subgroup.map_commutator, hSmap]
  rw [← hmap]
  exact ⟨x, hx, rfl⟩

/-- Conjugation-closure passes to joins: if conjugation by `h` keeps `A` in
`A` and `B` in `B`, it keeps `A ⊔ B` in `A ⊔ B` (via
`map (conj h) (A ⊔ B) = map (conj h) A ⊔ map (conj h) B`). -/
theorem conj_mem_sup {A B : Subgroup G} {h : G}
    (hA : ∀ x ∈ A, h * x * h⁻¹ ∈ A) (hB : ∀ x ∈ B, h * x * h⁻¹ ∈ B)
    {x : G} (hx : x ∈ A ⊔ B) : h * x * h⁻¹ ∈ A ⊔ B := by
  have hle : (A ⊔ B).map (MulAut.conj h).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_sup_left (hA y hy)
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_sup_right (hB y hy)
  exact hle ⟨x, hx, rfl⟩

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

/-! ## Per-prime divisibility below the derived subgroup -/

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

/-- **The centre of a finite nilpotent group contains a nonidentity element of
`p`-power order for every prime `p ∣ |K|`**: the (normal) Sylow `p`-subgroup is
nontrivial and meets the centre
(`exists_mem_center_of_normal_ne_bot_of_isNilpotent`). -/
theorem exists_center_pow_prime_eq_one_of_dvd {K : Type*} [Group K] [Finite K]
    [Group.IsNilpotent K] {p : ℕ} [hp : Fact p.Prime] (hpK : p ∣ Nat.card K) :
    ∃ x : K, x ∈ Subgroup.center K ∧ x ≠ 1 ∧ ∃ k, x ^ p ^ k = 1 := by
  classical
  set P : Sylow p K := default with hP_def
  have hPne : (P : Subgroup K) ≠ ⊥ := by
    intro hbot
    have hcard := P.card_eq_multiplicity
    rw [hbot, Subgroup.card_bot] at hcard
    rcases (Nat.pow_eq_one.mp hcard.symm) with h1 | h0
    · exact hp.out.one_lt.ne' h1
    · exact (hp.out.factorization_pos_of_dvd Nat.card_pos.ne' hpK).ne' h0
  obtain ⟨x, hxP, hxC, hx1⟩ :=
    OddOrder.Isaacs.Ch04.exists_mem_center_of_normal_ne_bot_of_isNilpotent hPne
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  refine ⟨x, hxC, hx1, k, ?_⟩
  simpa using congrArg Subtype.val hk

/-! ## The `p`-primary lift and the properness `Z ⊄ Q₂` (p. 146) -/

/-- **The commutator subgroup of `↥Q₁` maps onto `⁅Q₁, Q₁⁆`** under the
inclusion. -/
theorem map_subtype_commutator :
    Subgroup.map hyp.Q1.subtype (commutator ↥hyp.Q1) = ⁅hyp.Q1, hyp.Q1⁆ := by
  change Subgroup.map hyp.Q1.subtype ⁅(⊤ : Subgroup ↥hyp.Q1), ⊤⁆ = ⁅hyp.Q1, hyp.Q1⁆
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- A subgroup below `⁅Q₁, Q₁⁆` relativises below `commutator ↥Q₁`. -/
theorem subgroupOf_le_commutator {R : Subgroup G} (hR : R ≤ ⁅hyp.Q1, hyp.Q1⁆) :
    R.subgroupOf hyp.Q1 ≤ commutator ↥hyp.Q1 := by
  intro x hx
  have hmem : (x : G) ∈ Subgroup.map hyp.Q1.subtype (commutator ↥hyp.Q1) := by
    rw [hyp.map_subtype_commutator]
    exact hR (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨y, hy, hyx⟩ := hmem
  rwa [show y = x from Subtype.ext hyx] at hy

/-- **The `p`-primary part of the central lift**: elements of
`Z = centralLift Q₃ _` with a `p`-power power in `Q₃` — the lift of the
`p`-primary component of `Z(Q₁⧸Q₃)`.  Closure under multiplication works
modulo `Q₃` (members of `Z` commute mod `Q₃`). -/
def primaryLift (Q₃ : Subgroup G)
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃) (p : ℕ) : Subgroup G where
  carrier := {z | z ∈ hyp.centralLift Q₃ hinv ∧ ∃ k, z ^ p ^ k ∈ Q₃}
  one_mem' := ⟨(hyp.centralLift Q₃ hinv).one_mem, 0, by simp [Q₃.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨haZ, ka, hka⟩ ⟨hbZ, kb, hkb⟩
    refine ⟨(hyp.centralLift Q₃ hinv).mul_mem haZ hbZ, ka + kb, ?_⟩
    -- pass to `Q₁⧸Q₃`, where the two factors commute and are torsion
    haveI : (Q₃.subgroupOf hyp.Q1).Normal := subgroupOf_normal_of_conj_mem hinv
    set π := QuotientGroup.mk' (Q₃.subgroupOf hyp.Q1) with hπ_def
    have hmk : ∀ (w : ↥hyp.Q1) (n : ℕ), (w : G) ^ n ∈ Q₃ → (π w) ^ n = 1 := by
      intro w n hw
      rw [← map_pow, hπ_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      simpa using hw
    have hcomm : Commute (π ⟨a, haZ.1⟩) (π ⟨b, hbZ.1⟩) := by
      have h1 : π ⁅(⟨a, haZ.1⟩ : ↥hyp.Q1), (⟨b, hbZ.1⟩ : ↥hyp.Q1)⁆ = 1 := by
        rw [hπ_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf]
        simpa [commutatorElement_def] using haZ.2 b hbZ.1
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hab : (π ⟨a, haZ.1⟩ * π ⟨b, hbZ.1⟩) ^ p ^ (ka + kb) = 1 := by
      rw [hcomm.mul_pow, pow_add]
      rw [pow_mul, hmk _ _ hka, one_pow, one_mul, mul_comm (p ^ ka) (p ^ kb),
        pow_mul, hmk _ _ hkb, one_pow]
    have := hab
    rw [← map_mul, ← map_pow, hπ_def, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  inv_mem' := by
    rintro a ⟨haZ, k, hk⟩
    refine ⟨(hyp.centralLift Q₃ hinv).inv_mem haZ, k, ?_⟩
    rw [inv_pow]
    exact Q₃.inv_mem hk

theorem primaryLift_le_centralLift {Q₃ : Subgroup G}
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃) (p : ℕ) :
    hyp.primaryLift Q₃ hinv p ≤ hyp.centralLift Q₃ hinv := fun _ hz => hz.1

theorem le_primaryLift {Q₃ : Subgroup G}
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃) (hQ₃Q1 : Q₃ ≤ hyp.Q1)
    (p : ℕ) : Q₃ ≤ hyp.primaryLift Q₃ hinv p := fun x hx =>
  ⟨hyp.le_centralLift hinv hQ₃Q1 hx, 0, by simpa using hx⟩

/-- **The `p`-primary lift is `H`-invariant** (centrality transports by
`centralLift_conj_mem_of_mem_H`; the torsion condition by `conj_pow`). -/
theorem primaryLift_conj_mem_of_mem_H [Finite G] {Q₃ : Subgroup G}
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃)
    (hQ₃H : ∀ h ∈ hyp.H, ∀ x ∈ Q₃, h * x * h⁻¹ ∈ Q₃) {p : ℕ}
    {h : G} (hh : h ∈ hyp.H) {z : G} (hz : z ∈ hyp.primaryLift Q₃ hinv p) :
    h * z * h⁻¹ ∈ hyp.primaryLift Q₃ hinv p := by
  obtain ⟨hzZ, k, hk⟩ := hz
  refine ⟨hyp.centralLift_conj_mem_of_mem_H hinv hQ₃H hh hzZ, k, ?_⟩
  rw [conj_pow]
  exact hQ₃H h hh _ hk

/-- **`Z ⊄ Q₂` for the chief factor** (p. 146, "since `|Q₁|` is divisible by
two primes, `Q₂ ⊊ Z`"): if `Z ≤ Q₂`, then by minimality the `p`-primary lift
`T` — `H`-invariant, strictly over `Q₃` by a central `p`-element of `Q₁⧸Q₃`
(`exists_center_pow_prime_eq_one_of_dvd`), and inside `Q₂ ⊇ Z ⊇ T` — equals
`Q₂`; but then the central `r`-element of `Q₁⧸Q₃` lies in `T`, forcing its
`r`-power order to be a `p`-power, i.e. trivial. -/
theorem not_centralLift_le_minimal [Finite G] (hnil : Group.IsNilpotent ↥hyp.Q1)
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpd : p ∣ Nat.card ↥hyp.Q1) (hrd : r ∣ Nat.card ↥hyp.Q1)
    {Q₂ Q₃ : Subgroup G} (hQ₃Q₂ : Q₃ < Q₂) (hQ₂der : Q₂ ≤ ⁅hyp.Q1, hyp.Q1⁆)
    (hinv : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃, q * x * q⁻¹ ∈ Q₃)
    (hQ₃H : ∀ h ∈ hyp.H, ∀ x ∈ Q₃, h * x * h⁻¹ ∈ Q₃)
    (hmin : ∀ Q₂' : Subgroup G, Q₃ < Q₂' → Q₂' ≤ Q₂ →
        (∀ h ∈ hyp.H, ∀ x ∈ Q₂', h * x * h⁻¹ ∈ Q₂') → Q₂' = Q₂) :
    ¬ hyp.centralLift Q₃ hinv ≤ Q₂ := by
  classical
  intro hZle
  haveI := hnil
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : (Q₃.subgroupOf hyp.Q1).Normal := subgroupOf_normal_of_conj_mem hinv
  have hQ₃der : Q₃ ≤ ⁅hyp.Q1, hyp.Q1⁆ := hQ₃Q₂.le.trans hQ₂der
  -- central elements of `p`- resp. `r`-power order in `Q₁⧸Q₃`
  obtain ⟨xp, hxpC, hxp1, kp, hkp⟩ := exists_center_pow_prime_eq_one_of_dvd
    (K := ↥hyp.Q1 ⧸ Q₃.subgroupOf hyp.Q1)
    (prime_dvd_card_quotient_of_le_commutator hpd (hyp.subgroupOf_le_commutator hQ₃der))
  obtain ⟨xr, hxrC, hxr1, kr, hkr⟩ := exists_center_pow_prime_eq_one_of_dvd
    (K := ↥hyp.Q1 ⧸ Q₃.subgroupOf hyp.Q1)
    (prime_dvd_card_quotient_of_le_commutator hrd (hyp.subgroupOf_le_commutator hQ₃der))
  obtain ⟨wp, hwp⟩ := QuotientGroup.mk'_surjective (Q₃.subgroupOf hyp.Q1) xp
  obtain ⟨wr, hwr⟩ := QuotientGroup.mk'_surjective (Q₃.subgroupOf hyp.Q1) xr
  -- lifts of central elements land in the central lift
  have hlift : ∀ w : ↥hyp.Q1,
      QuotientGroup.mk' (Q₃.subgroupOf hyp.Q1) w
        ∈ Subgroup.center (↥hyp.Q1 ⧸ Q₃.subgroupOf hyp.Q1) →
      (w : G) ∈ hyp.centralLift Q₃ hinv := by
    intro w hwC
    refine ⟨w.2, fun y hy => ?_⟩
    have hcomm : QuotientGroup.mk' (Q₃.subgroupOf hyp.Q1)
        ⁅w, (⟨y, hy⟩ : ↥hyp.Q1)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hwC _).symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hcomm
    simpa [commutatorElement_def] using hcomm
  have hwpZ : (wp : G) ∈ hyp.centralLift Q₃ hinv := hlift wp (by rw [hwp]; exact hxpC)
  have hwrZ : (wr : G) ∈ hyp.centralLift Q₃ hinv := hlift wr (by rw [hwr]; exact hxrC)
  -- the `p`-primary lift is a strict `H`-invariant enlargement of `Q₃` in `Q₂`
  have hwpT : (wp : G) ∈ hyp.primaryLift Q₃ hinv p := by
    refine ⟨hwpZ, kp, ?_⟩
    have h1 : QuotientGroup.mk' (Q₃.subgroupOf hyp.Q1) (wp ^ p ^ kp) = 1 := by
      rw [map_pow, hwp, hkp]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hwpQ₃ : (wp : G) ∉ Q₃ := by
    intro hmem
    apply hxp1
    rw [← hwp, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hmem
  have hTlt : Q₃ < hyp.primaryLift Q₃ hinv p := by
    refine lt_of_le_of_ne (hyp.le_primaryLift hinv (hQ₃Q₂.le.trans
      (hQ₂der.trans hyp.Q1der_le_Q1)) p) fun heq => ?_
    exact hwpQ₃ (by rw [heq]; exact hwpT)
  have hTeq := hmin _ hTlt
    ((hyp.primaryLift_le_centralLift hinv p).trans hZle)
    (fun h hh x hx => hyp.primaryLift_conj_mem_of_mem_H hinv hQ₃H hh hx)
  -- the `r`-element then acquires a trivialising `p`-power order
  have hwrT : (wr : G) ∈ hyp.primaryLift Q₃ hinv p := by
    rw [hTeq]
    exact hZle hwrZ
  obtain ⟨-, k, hk⟩ := hwrT
  have hxrp : xr ^ p ^ k = 1 := by
    rw [← hwr, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  have h1 : orderOf xr ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxrp
  have h2 : orderOf xr ∣ r ^ kr := orderOf_dvd_of_pow_eq_one hkr
  have hcop : Nat.Coprime (p ^ k) (r ^ kr) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hr).mpr hpr)
  have hone : orderOf xr = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
  exact hxr1 (orderOf_eq_one_iff.mp hone)

/-! ## The reduction (1) induction (p. 146) -/

section InductionAssembly

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

/-- **The reduction (1) chief-factor induction** (p. 146): for every
`H`-invariant `Q₃ ≤ [Q₁,Q₁]`, the family `𝒮(S'Q₃)` is coherent — by downward
strong induction from the base `Q₃ = [Q₁,Q₁]` (the Remark, via
`Q' = S'·[Q₁,Q₁]`), descending along minimal `H`-invariant steps
(`exists_minimal_conjInvariant_between`) through the one-step lemma
`ssetOf_coherent_step` with the chief data supplied by
`minimal_le_centralLift` / `not_centralLift_le_minimal` /
`d_add_one_sq_le_card_quot_of_two_primes`. -/
theorem ssetOf_sup_sder_coherent_of_conjInvariant
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    (hnil : Group.IsNilpotent ↥hyp.Q1)
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpd : p ∣ Nat.card ↥hyp.Q1) (hrd : r ∣ Nat.card ↥hyp.Q1)
    (Q₃ : Subgroup G) (hQ₃le : Q₃ ≤ ⁅hyp.Q1, hyp.Q1⁆)
    (hQ₃H : ∀ h ∈ hyp.H, ∀ x ∈ Q₃, h * x * h⁻¹ ∈ Q₃) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsetOf (hyp.Sder ⊔ Q₃)) hyp.A) := by
  classical
  haveI := hnil
  -- `[Q₁,Q₁] < Q₁` (nontrivial nilpotent), hence `S·Q' < Q` for the anchor
  haveI : Nontrivial ↥hyp.Q1 := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hpd)
  have hder_ne : ⁅hyp.Q1, hyp.Q1⁆ ≠ hyp.Q1 := by
    intro heq
    apply (IsSolvable.commutator_lt_top_of_nontrivial ↥hyp.Q1).ne
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ Subgroup.map hyp.Q1.subtype (commutator ↥hyp.Q1) := by
      rw [hyp.map_subtype_commutator, heq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hlt : hyp.S ⊔ hyp.Qder < hyp.Q := by
    rw [hyp.Qder_eq_sup_Sder_commutator, ← sup_assoc, sup_eq_left.mpr hyp.Sder_le_S,
      lt_iff_le_and_ne]
    refine ⟨sup_le hyp.S_le_Q (hyp.Q1der_le_Q1.trans hyp.Q1_le_Q), fun heq => ?_⟩
    have h1 : hyp.Q1 ⊓ (hyp.S ⊔ ⁅hyp.Q1, hyp.Q1⁆) = ⁅hyp.Q1, hyp.Q1⁆ :=
      hyp.Q1_inf_sup_eq le_rfl hyp.Q1der_le_Q1
    rw [heq, inf_eq_left.mpr hyp.Q1_le_Q] at h1
    exact hder_ne h1.symm
  -- the base of the induction: the Remark at `Q' = S'·[Q₁,Q₁]`
  have hbase : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsetOf (hyp.Sder ⊔ ⁅hyp.Q1, hyp.Q1⁆)) hyp.A) := by
    rw [← hyp.Qder_eq_sup_Sder_commutator]
    exact hyp.ssetOf_Qder_coherent hd hQ1odd (hyp.ssetOf_Qder_nonempty hlt)
  -- strong induction on the cardinality gap below `[Q₁,Q₁]`
  have hmain : ∀ n (Q₃' : Subgroup G), Q₃' ≤ ⁅hyp.Q1, hyp.Q1⁆ →
      (∀ h ∈ hyp.H, ∀ x ∈ Q₃', h * x * h⁻¹ ∈ Q₃') →
      Nat.card ↥(⁅hyp.Q1, hyp.Q1⁆ : Subgroup G) - Nat.card ↥Q₃' ≤ n →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
        (hyp.SsetOf (hyp.Sder ⊔ Q₃')) hyp.A) := by
    intro n
    induction n with
    | zero =>
      intro Q₃' hle hinvH hcard
      have hcard_le : Nat.card ↥(⁅hyp.Q1, hyp.Q1⁆ : Subgroup G) ≤ Nat.card ↥Q₃' := by
        have hpos : 0 < Nat.card ↥Q₃' := Nat.card_pos
        omega
      rw [OddOrder.Isaacs.Ch09.eq_of_le_of_card_le hle hcard_le]
      exact hbase
    | succ n ih =>
      intro Q₃' hle hinvH hcard
      by_cases heq : Q₃' = ⁅hyp.Q1, hyp.Q1⁆
      · rw [heq]
        exact hbase
      -- choose the chief step `Q₂/Q₃'` and apply the one-step lemma
      have hQ₃lt : Q₃' < ⁅hyp.Q1, hyp.Q1⁆ := lt_of_le_of_ne hle heq
      obtain ⟨Q₂, hQ₃Q₂, hQ₂le, hQ₂H, hmin⟩ :=
        hyp.exists_minimal_conjInvariant_between hQ₃lt
          (fun h hh x hx => hyp.Q1der_conj_mem_of_mem_H hh hx)
      have hinvQ1 : ∀ q ∈ hyp.Q1, ∀ x ∈ Q₃', q * x * q⁻¹ ∈ Q₃' :=
        fun q hq x hx => hinvH q (hyp.Q1_le_H hq) x hx
      -- the induction hypothesis applies at the strictly larger `Q₂`
      have hcard₂ : Nat.card ↥(⁅hyp.Q1, hyp.Q1⁆ : Subgroup G) - Nat.card ↥Q₂ ≤ n := by
        have h1 : Nat.card ↥Q₃' < Nat.card ↥Q₂ := by
          rcases lt_or_ge (Nat.card ↥Q₃') (Nat.card ↥Q₂) with h | h
          · exact h
          · exact absurd (OddOrder.Isaacs.Ch09.eq_of_le_of_card_le hQ₃Q₂.le h) hQ₃Q₂.ne
        have h2 : Nat.card ↥Q₂ ≤ Nat.card ↥(⁅hyp.Q1, hyp.Q1⁆ : Subgroup G) :=
          Subgroup.card_le_of_le hQ₂le
        omega
      have hcoh₂ := ih Q₂ hQ₂le hQ₂H hcard₂
      -- chief-factor data for the step lemma
      have hQ₂Z : Q₂ ≤ hyp.centralLift Q₃' hinvQ1 :=
        hyp.minimal_le_centralLift hnil hQ₃Q₂ (hQ₂le.trans hyp.Q1der_le_Q1)
          hinvQ1 hQ₂H hinvH hmin
      have hZQ₂ : ¬ hyp.centralLift Q₃' hinvQ1 ≤ Q₂ :=
        hyp.not_centralLift_le_minimal hnil hp hr hpr hpd hrd hQ₃Q₂ hQ₂le
          hinvQ1 hinvH hmin
      -- the relativised `Normal` instances
      haveI : ((hyp.Sder ⊔ Q₂).subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx =>
          conj_mem_sup (fun y hy => hyp.Sder_conj_mem_of_mem_H hh hy)
            (fun y hy => hQ₂H h hh y hy) hx
      haveI : ((hyp.Sder ⊔ Q₃').subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx =>
          conj_mem_sup (fun y hy => hyp.Sder_conj_mem_of_mem_H hh hy)
            (fun y hy => hinvH h hh y hy) hx
      haveI : (hyp.Q1.subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx => hyp.Q1_normal_in_H hh hx
      haveI : (((hyp.Sder ⊔ Q₃').subgroupOf hyp.H).subgroupOf
          (hyp.Q.subgroupOf hyp.H)).Normal :=
        hyp.subgroupOf_Q_normal_of_conj_mem fun q hq x hx =>
          conj_mem_sup (fun y hy => hyp.Sder_conj_mem_of_mem_H (hyp.Q_le_H hq) hy)
            (fun y hy => hinvH q (hyp.Q_le_H hq) y hy) hx
      haveI : ((hyp.S ⊔ hyp.centralLift Q₃' hinvQ1).subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx =>
          conj_mem_sup (fun y hy => hyp.S_normal_in_H hh hy)
            (fun y hy => hyp.centralLift_conj_mem_of_mem_H hinvQ1 hinvH hh hy) hx
      -- the one-step lemma closes the induction step
      exact hyp.ssetOf_coherent_step hd hQ1odd hlt hQ₂le hQ₃Q₂.le
        (hyp.centralLift_le_Q1 hinvQ1) hQ₂Z hZQ₂
        (fun z hz y hy => hz.2 y hy)
        (fun δ hδ z hz => hQ₂H δ (hyp.D_le_H hδ) z hz)
        (fun δ hδ z hz =>
          hyp.centralLift_conj_mem_of_mem_H hinvQ1 hinvH (hyp.D_le_H hδ) hz)
        (hyp.d_add_one_sq_le_card_quot_of_two_primes hnil hp hr hpr hpd hrd hQ₂le
          (fun δ hδ z hz => hQ₂H δ (hyp.D_le_H hδ) z hz))
        hcoh₂
  exact hmain _ Q₃ hQ₃le hQ₃H le_rfl

/-- **Reduction (1)** (p. 146): if `|Q₁|` is divisible by two distinct primes
(and `Q₁` is nilpotent — supplied by Thompson's theorem at the final assembly),
then `𝒮(S')` is coherent.  The chief-factor induction at `Q₃ = ⊥`. -/
theorem ssetOf_sder_coherent_of_two_primes
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    (hnil : Group.IsNilpotent ↥hyp.Q1)
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpd : p ∣ Nat.card ↥hyp.Q1) (hrd : r ∣ Nat.card ↥hyp.Q1) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsetOf hyp.Sder) hyp.A) := by
  have h := hyp.ssetOf_sup_sder_coherent_of_conjInvariant hd hQ1odd hnil hp hr hpr
    hpd hrd ⊥ bot_le (fun h _ x hx => by
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx]
      group)
  rwa [sup_bot_eq] at h

end InductionAssembly

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
