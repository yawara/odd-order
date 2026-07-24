/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_CollectionFormula
import OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.HallCollection
import OddOrder.GroupTheory.HallPetresco
import OddOrder.GroupTheory.RegularPGroup
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.BG.AppE_RegularOperator

/-!
# BG Appendix E: Further Results of Feit and Thompson

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 157--164.

Appendix E records Philip Hall's commutator collection formula (E.1), its
regular-`p`-group consequences (E.2), the 1991 Feit--Thompson results on a
regular operator action on a `p`-group (E.3, E.4), and a maximal-subgroup
application (E.5).

This file carries `(E.3)`--`(E.5)`.  Its two neighbours are
`OddOrder/BG/AppE_CollectionFormula.lean` (upstream: `(E.1)`, `(E.2)`) and
`OddOrder/BG/AppE_RegularOperator.lean` (downstream: the `(E.9)`--`(E.12)` eigenvalue
count).  Both splits were forced by the repo's 2000-line limit (issue 0134); the module
name here never changed, so consumers were unaffected.

## Honesty status

Every statement below is a genuine group-theoretic assertion: there are no
opaque `Prop` fields and no self-carried `_holds` proofs anywhere in this file.
This file is now **sorry-free**; the deep results whose proofs need machinery
staged in later leaves (E.3(b)–(d), E.4, E.5) are proved downstream, with
pointer comments here at their book positions.  Per-result status:

| Result | Status |
|---|---|
| E.1 general (`hallCollection`) | **proved** (Mann; `GroupTheory/HallPetresco.lean`) |
| E.1 class `≤ 3` (`hallCollection_of_class_le_three`) | **proved, sorry-free** (all `n`) |
| E.1 class `≤ 2` (`hallCollection_of_class_le_two`) | **proved** (subsumed by the above) |
| E.1 general framework | `OddOrder/GroupTheory/HallCollection.lean`, **sorry-free** |
| E.2 Step 1 (`GroupTheory.pow_mul_pow_eq_pow_of_commutator_exponent`) | **proved** (general) |
| E.2(a) (`omega_pow_eq_one_of_lowerCentralSeries_eq_bot`) | **proved** (`IsPGroup` dropped) |
| E.2(a) class `≤ 2` | already in repo: `GroupTheory.Omega.pow_eq_one_of_class_le_two` |
| E.2(b) (`pow_mul_of_commutator_le_omega`) | **proved** from E.2(a) + Step 1 |
| E.2(b) class `≤ 2` (`pow_mul_of_class_le_two`) | **proved, sorry-free** |
| E.3(a) (`card_A_dvd_half_p_sub_one`) | **proved, sorry-free** |
| E.3(b) `C_R(R₀) = R₀ × R₁` structure | **proved** (abelian, order `p·|R₁|`, rank `≤ 2`) |
| E.3(b) Step 2, `R₀ ⊄ S'` (`not_le_derivedInG`) | **proved, sorry-free**, both branches |
| E.3(b) Step 2, `S` narrow / `\|Ω₁(Z(S))\| = p` / `\|S:T\| = p` | **proved, sorry-free** |
| E.3(b) Step 2, (E.4)--(E.7) | **proved, sorry-free** (chain, `\|T\| = pⁿ`, `\|S/S'\| = p²`) |
| E.3(b) second + third clause | **proved** from Step 2 + first clause |
| E.3(c) (`card_omega_le`) | **proved** — in `AppE_RegularOperator.lean` (Step 2's count) |
| E.3(d) (`B_fixes_R₀_of_fixes_frattini`) | **proved** — `AppE_SemidirectFrattini.lean` (Step 4) |
| E.3(b) first clause | **proved** — in `AppE_ExponentP.lean` (Step 3) |
| E.4 (corrected, `+hdc`) | **proved** — in `AppE_PropE4.lean` (printed form is false) |
| E.5 (`maximalSubgroups_isTypeI_or_isTypeII`) | **proved** — in `AppE_E5Counting.lean` |
-/

namespace OddOrder.BG.AppE

section RegularOperator

open OddOrder.GroupTheory
open scoped commutatorElement Pointwise
open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch04
variable {R B : Type*} [Group R] [Group B]
variable {p q : ℕ}

/-- A finite `p`-group of order at most `p³` has nilpotency class `≤ 2`, i.e. `G' ≤ Z(G)`.

This is what BG's elided *"examination of the `p`-groups of order at most `p³`"* actually
needs; the classification of those groups is not required. -/
private theorem commutator_le_center_of_card_le_prime_cube {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hcard : Nat.card G ≤ p ^ 3) :
    _root_.commutator G ≤ Subgroup.center G := by
  haveI : Group.IsNilpotent G := hG.isNilpotent
  have hcl : Group.nilpotencyClass G ≤ 2 :=
    OddOrder.BG.Ch1.S04.nilpotencyClass_le_of_card_le_pow hG (by norm_num)
      (by simpa using hcard)
  have hlcs : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hcl
  have hce := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hlcs
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro h
  exact Subgroup.mem_centralizer_iff.mp (hce hg) h (Subgroup.mem_top h)

/-- In a finite `p`-group a *proper* subgroup has index divisible by `p`, so `K < H` gives
`p · |K| ≤ |H|`.  Used twice below, for the two ends of BG's (E.6) chain step. -/
private theorem prime_mul_card_le_card_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : IsPGroup p G) {K H : Subgroup G} (hlt : K < H) :
    p * Nat.card ↥K ≤ Nat.card ↥H := by
  have hidx_ne : (K.subgroupOf H).index ≠ 1 := fun h1 =>
    hlt.ne (le_antisymm hlt.le
      (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1)))
  have hdvd : (K.subgroupOf H).index ∣ Nat.card ↥H := Subgroup.index_dvd_card _
  obtain ⟨k, hk⟩ := (hG.to_subgroup H).exists_card_eq
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have hple : p ≤ (K.subgroupOf H).index := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact absurd (by simpa using hj) hidx_ne
    · rw [hj]
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hjpos
  have hmul : Nat.card ↥K * (K.subgroupOf H).index = Nat.card ↥H := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlt.le).toEquiv]
    exact Subgroup.card_mul_index _
  calc p * Nat.card ↥K = Nat.card ↥K * p := mul_comm _ _
    _ ≤ Nat.card ↥K * (K.subgroupOf H).index := Nat.mul_le_mul_left _ hple
    _ = Nat.card ↥H := hmul

/-- **BG Theorem E.3(b), Step 2, (E.6)**: one chain step has index exactly `p` —
`|H| = p · |⁅R₀, H⁆|` for a nontrivial normal `H ≤ T`.

Two bounds meet.  `≤`: the counting step `card_le_card_commutator_mul_prime`.  `≥`:
`⁅R₀, H⁆ = ⁅H, R₀⁆ < H` because `S` is nilpotent and `H` is normal and nontrivial
(`Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient`), and a *proper* subgroup of a
`p`-group has index divisible by `p`.

This is the inductive step of BG's series `T = H₀ ⊃ H₁ ⊃ ⋯ ⊃ Hₙ = 1`, whose factors BG
records as `|Hᵢ₋₁ : Hᵢ| = p`. -/
theorem RegularOperatorSetup.card_eq_prime_mul_card_commutator [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {H : Subgroup ↥S} [H.Normal]
    (hHne : H ≠ ⊥)
    (hHT : H ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    Nat.card ↥H = p * Nat.card ↥⁅hyp.R₀.subgroupOf S, H⁆ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : Group.IsNilpotent ↥S := (hyp.R_pGroup.to_subgroup S).isNilpotent
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'def
  set K : Subgroup ↥S := ⁅R₀', H⁆ with hKdef
  -- `⁅R₀, H⁆ = ⁅H, R₀⁆ < H` by nilpotency.
  have hlt : K < H := by
    rw [hKdef, Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient hHne
  have hge : p * Nat.card ↥K ≤ Nat.card ↥H :=
    prime_mul_card_le_card_of_lt (hyp.R_pGroup.to_subgroup S) hlt
  have hle : Nat.card ↥H ≤ Nat.card ↥K * p :=
    hyp.card_le_card_commutator_mul_prime hR₀S hexp hS hHT
  rw [mul_comm p] at hge ⊢
  exact le_antisymm hle hge

/-- **BG Theorem E.3(b), Step 2, (E.6)**: `⁅R₀, H⁆ = ⁅S, H⁆` for nontrivial normal `H ≤ T`.

BG *asserts* the identification `Hᵢ = [R, Hᵢ₋₁] = [R₀, Hᵢ₋₁]`.  It is a **consequence** of
the counting, not an input to it: `⁅R₀,H⁆ ≤ ⁅S,H⁆` is monotonicity, and conversely `⁅S,H⁆`
is a proper subgroup of the `p`-group `H` (nilpotency), so
`|⁅S,H⁆| ≤ |H|/p = |⁅R₀,H⁆|` by `card_eq_prime_mul_card_commutator`.

The identification is what makes BG's chain *characteristic*: `⁅S, ·⁆` preserves normality
in `S`, whereas `⁅R₀, ·⁆` need not, `R₀` being non-normal in `S`.  So the chain should be
**defined** by the `⁅S, ·⁆` form and only then recognised as the `⁅R₀, ·⁆` form. -/
theorem RegularOperatorSetup.commutator_R₀_eq_commutator_top [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {H : Subgroup ↥S} [H.Normal]
    (hHne : H ≠ ⊥)
    (hHT : H ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    ⁅hyp.R₀.subgroupOf S, H⁆ = ⁅(⊤ : Subgroup ↥S), H⁆ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : Group.IsNilpotent ↥S := (hyp.R_pGroup.to_subgroup S).isNilpotent
  have hmono : ⁅hyp.R₀.subgroupOf S, H⁆ ≤ ⁅(⊤ : Subgroup ↥S), H⁆ :=
    Subgroup.commutator_mono le_top le_rfl
  refine Subgroup.eq_of_le_of_card_ge hmono ?_
  -- `⁅S,H⁆ = ⁅H,S⁆ < H`, so `p · |⁅S,H⁆| ≤ |H| = p · |⁅R₀,H⁆|`.
  have hlt : ⁅(⊤ : Subgroup ↥S), H⁆ < H := by
    rw [Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient hHne
  have hge : p * Nat.card ↥⁅(⊤ : Subgroup ↥S), H⁆ ≤ Nat.card ↥H :=
    prime_mul_card_le_card_of_lt (hyp.R_pGroup.to_subgroup S) hlt
  rw [hyp.card_eq_prime_mul_card_commutator hR₀S hexp hS hHne hHT] at hge
  exact Nat.le_of_mul_le_mul_left hge hyp.p_prime.pos

/-- **BG Theorem E.3(b), Step 2, (E.5)**: `S = R₀T`.

BG records `T char S`, `|S : T| = p` and `R₀ ∩ T = 1`, then writes `S = R₀T`.  The last step
is a cardinality count: `T` is normal (indeed `T char S` is already an instance in the repo,
`GroupTheory.centralizer_omega1UpperCentralTwo_characteristic`), so `|R₀T| = |R₀| · |T| =
p · |T| = |S|`.

Note `hexp` is not needed: narrowness alone drives Theorem 5.3(d). -/
theorem RegularOperatorSetup.sup_centralizer_eq_top [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    hyp.R₀.subgroupOf S ⊔
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) = ⊤ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'def
  set T : Subgroup ↥S :=
    Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hTdef
  obtain ⟨-, -, hR₀T, -⟩ := OddOrder.BG.Ch1.S05.narrow_centralizer_decomp
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS (hyp.isNarrow_of_three_le_pRank hR₀S hS)
    R₀' (hyp.card_R₀_subgroupOf hR₀S) (hyp.pRank_centralizer_subgroupOf_le_two hR₀S)
  -- `|R₀ T| = |R₀| · |T| = p · |T|`
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card R₀' T
  rw [hR₀T, Subgroup.card_bot, mul_one, hyp.card_R₀_subgroupOf hR₀S] at hprod
  have hcong : Nat.card ↥(R₀' ⊔ T) = Nat.card ↥((R₀' : Set ↥S) * (T : Set ↥S)) :=
    Nat.card_congr (Equiv.setCongr (Subgroup.mul_normal R₀' T))
  -- `|S| = |T| · [S : T] = |T| · p`
  have hSc : Nat.card ↥T * T.index = Nat.card ↥S := T.card_mul_index
  rw [(hyp.card_omega1Center_and_index_centralizer hR₀S hS).2] at hSc
  refine Subgroup.eq_of_le_of_card_ge le_top ?_
  rw [Subgroup.card_top, hcong, hprod, ← hSc, mul_comm]

/-! ### (E.6): BG's descending series

BG's chain `T = H₀ ⊃ H₁ ⊃ ⋯ ⊃ Hₙ = 1` with `Hᵢ = [R, Hᵢ₋₁]` is the repo's
`Isaacs.Ch04.iterCommutator T ⊤` (iterated *right* commutator with the whole group), so no
new definition is introduced.  BG's other description `Hᵢ = [R₀, Hᵢ₋₁]` is recovered from
`commutator_R₀_eq_commutator_top`. -/

/-- Every term of `iterCommutator T ⊤` is normal when `T` is. -/
private theorem normal_iterCommutator {G : Type*} [Group G] {T : Subgroup G} [T.Normal] :
    ∀ n, (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n).Normal
  | 0 => ‹T.Normal›
  | n + 1 => by
      haveI := normal_iterCommutator (T := T) n
      exact Subgroup.commutator_normal _ _

/-- `iterCommutator T ⊤` descends: `⁅H, ⊤⁆ ≤ H` for normal `H`. -/
theorem iterCommutator_antitone {G : Type*} [Group G] {T : Subgroup G} [T.Normal] :
    ∀ n, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (n + 1) ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n := fun n => by
  haveI := normal_iterCommutator (T := T) n
  exact Subgroup.commutator_le_left _ _

/-- `iterCommutator T ⊤ n ≤ T` for every `n`.

Public because `AppE_RegularOperator` needs it to feed `commutator_R₀_eq_commutator_top`
(cross-file `private` is against repo convention). -/
theorem iterCommutator_le_start {G : Type*} [Group G] {T : Subgroup G} [T.Normal] :
    ∀ n, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n ≤ T
  | 0 => le_rfl
  | n + 1 => (iterCommutator_antitone n).trans (iterCommutator_le_start n)

/-- Every term of `iterCommutator T ⊤` is characteristic when `T` is.

This is the point of BG defining the chain by `[R, Hᵢ₋₁]` rather than `[R₀, Hᵢ₋₁]`
(`commutator_R₀_eq_commutator_top` shows they coincide): `⁅·, ⊤⁆` preserves
characteristicity, and characteristic subgroups are automatically `A`-invariant, which is
what (E.9) onwards needs. -/
instance characteristic_iterCommutator {G : Type*} [Group G] (T : Subgroup G)
    [T.Characteristic] (n : ℕ) :
    (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n).Characteristic := by
  induction n with
  | zero => exact ‹T.Characteristic›
  | succ n ih =>
      haveI := ih
      change (⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n,
        (⊤ : Subgroup G)⁆).Characteristic
      infer_instance

/-- **BG's sequence from (E.9)**: `w₀ = w` and `wᵢ = ⁅wᵢ₋₁, v⁆`.

The element-level counterpart of `Isaacs.Ch04.iterCommutator` (which iterates on
*subgroups*); BG walks the chain `T = H₀ ⊃ H₁ ⊃ ⋯` with this sequence, taking `v ∈ R₀^#`
and `w ∈ H₀ − H₁`. -/
def commutatorIterate {G : Type*} [Group G] (w v : G) : ℕ → G
  | 0 => w
  | n + 1 => ⁅commutatorIterate w v n, v⁆

@[simp]
theorem commutatorIterate_zero {G : Type*} [Group G] (w v : G) :
    commutatorIterate w v 0 = w := rfl

@[simp]
theorem commutatorIterate_succ {G : Type*} [Group G] (w v : G) (n : ℕ) :
    commutatorIterate w v (n + 1) = ⁅commutatorIterate w v n, v⁆ := rfl

/-- **BG (E.9)**: `wᵢ` walks down the chain — `wᵢ ∈ Hᵢ`.

Immediate induction: `wᵢ = ⁅wᵢ₋₁, v⁆ ∈ ⁅Hᵢ₋₁, S⁆ = Hᵢ`.  Note only `w ∈ T` is needed; the
element `v` is unconstrained, since the chain brackets against all of `S`. -/
theorem commutatorIterate_mem_chain {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {w v : G} (hw : w ∈ T) :
    ∀ n, commutatorIterate w v n ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n
  | 0 => hw
  | n + 1 =>
      Subgroup.commutator_mem_commutator (commutatorIterate_mem_chain hw n) (Subgroup.mem_top v)

/-- **BG Theorem E.3(b), Step 2, (E.12) setup**: `H̄ᵢ ≤ Z(S̄)` in `S̄ = S/Hᵢ₊₁`.

BG: *"Let `S̄ = S/Hᵢ₊₁` and apply the bar convention.  Then `|H̄ᵢ| = p` and `H̄ᵢ ≤ Z(S̄)`."*

Immediate from the chain's own definition: `Hᵢ₊₁ = ⁅Hᵢ, S⁆`, so every commutator of an
element of `Hᵢ` with anything dies in the quotient.  This centrality is precisely what makes
Lemma 4.2(a) — and hence `commutatorElement_pow_pow_of_central` — applicable there. -/
theorem chain_map_le_center {G : Type*} [Group G] (T : Subgroup G) [T.Characteristic]
    (i : ℕ) :
    (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1)))
      ≤ Subgroup.center
        (G ⧸ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have hmem : (y * x)⁻¹ * (x * y) ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) := by
    have hrw : (y * x)⁻¹ * (x * y) = ⁅x⁻¹, y⁻¹⁆ := by group
    rw [hrw, OddOrder.Isaacs.Ch04.iterCommutator_succ]
    exact Subgroup.commutator_mem_commutator
      ((OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i).inv_mem hx)
      (Subgroup.mem_top _)
  rw [← map_mul, ← map_mul]
  exact QuotientGroup.eq.mpr hmem

/-- **BG Theorem E.3(b), Step 2, (E.9)**: the chain is `A`-invariant.

BG says the series is `A`-invariant without further comment; the reason is that each term is
characteristic in `S`, and `S` itself is `A`-invariant by hypothesis, so
`Isaacs.Ch03.IsAInvariant.of_characteristic` applies to the restricted action on `↥S`. -/
theorem RegularOperatorSetup.isAInvariant_iterCommutator
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) (i : ℕ) :
    IsAInvariant hSinv.restrict
      (OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i) := by
  haveI := characteristic_iterCommutator
    (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) i
  exact IsAInvariant.of_characteristic _

/-- **BG Theorem E.3(b), Step 2, (E.6)**: every factor of the chain has order `p`.

For BG's series `Hᵢ = iterCommutator T ⊤ i`, as long as `Hᵢ ≠ 1` we have
`|Hᵢ| = p · |Hᵢ₊₁|` — BG's `|Hᵢ₋₁ : Hᵢ| = p`.

The two descriptions of the chain meet here: the *definition* uses `⁅Hᵢ, S⁆`, which keeps
each term normal in `S`, while the *counting* (`card_eq_prime_mul_card_commutator`) is about
`⁅R₀, Hᵢ⁆`; `commutator_R₀_eq_commutator_top` identifies them. -/
theorem RegularOperatorSetup.card_iterCommutator_eq [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {T : Subgroup ↥S} [T.Normal]
    (hT : T ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥) :
    Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) =
      p * Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1)) := by
  haveI := normal_iterCommutator (T := T) i
  have hHT : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≤
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) :=
    (iterCommutator_le_start i).trans hT
  have hstep := hyp.card_eq_prime_mul_card_commutator hR₀S hexp hS hne hHT
  rw [hyp.commutator_R₀_eq_commutator_top hR₀S hexp hS hne hHT] at hstep
  rw [hstep, OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]

/-- **BG Theorem E.3(b), Step 2, (E.6)**: `|T| = pⁱ · |Hᵢ|` for as long as `Hᵢ ≠ 1`.

Iterating `card_iterCommutator_eq`.  Since `iterCommutator T ⊤` reaches `⊥`
(`Isaacs.Ch04.iterCommutator_eq_bot_of_isNilpotent_ambient`), at the last nontrivial index
this reads `|T| = pⁿ` — BG's "Thus `|T| = pⁿ`". -/
theorem RegularOperatorSetup.card_start_eq_pow_mul [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {T : Subgroup ↥S} [T.Normal]
    (hT : T ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    ∀ i : ℕ, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥ →
      Nat.card ↥T =
        p ^ i * Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)
  | 0, _ => by simp [OddOrder.Isaacs.Ch04.iterCommutator_zero]
  | i + 1, hne => by
      have hprev : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥ := by
        intro h
        exact hne (le_bot_iff.mp ((iterCommutator_antitone i).trans (le_of_eq h)))
      rw [hyp.card_start_eq_pow_mul hR₀S hexp hS hT i hprev,
        hyp.card_iterCommutator_eq hR₀S hexp hS hT hprev, pow_succ]
      ring

/-- **BG Theorem E.3(b), Step 2, (E.7)**: `H₁ = S'` and `|S / S'| = p²`.

BG: *"Since `|H₀/H₁| = p` and `H₁ = [R₀,H₀] = [R₀,T] ≤ R₀T = S`, we have `|S/H₁| = p²` and
`S₂ = [S,S] ⊆ H₁ = [R₀,T] ⊆ S₂`."*

`|S : H₁| = p²` because `|S : T| = p` (E.5) and `|T : H₁| = p` (E.6).  Then `S/H₁` has order
`p²`, hence is abelian, giving `S' ≤ H₁`; and `H₁ = ⁅T, S⁆ ≤ ⁅S, S⁆ = S'` directly.  So the
two coincide and `|S/S'| = p²`.

With `S = Ω₁(R)` this is exactly E.3(b)'s third clause. -/
theorem RegularOperatorSetup.commutator_eq_and_card_quotient [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1
      = _root_.commutator ↥S ∧
    Nat.card (↥S ⧸ _root_.commutator ↥S) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S :=
    Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hTdef
  set H₁ : Subgroup ↥S := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) 1 with hH₁def
  haveI : H₁.Normal := normal_iterCommutator (T := T) 1
  have hTindex : T.index = p := (hyp.card_omega1Center_and_index_centralizer hR₀S hS).2
  have hScard : Nat.card ↥T * p = Nat.card ↥S := by
    rw [← hTindex]; exact T.card_mul_index
  -- `p³ ≤ |S|` from `r(S) ≥ 3`, so `T ≠ ⊥`.
  have hp3 : p ^ 3 ≤ Nat.card ↥S := by
    obtain ⟨A, hA, hAlog⟩ :=
      exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥S) (by norm_num) hS
    calc p ^ 3 ≤ p ^ Nat.log p (Nat.card ↥A) :=
          Nat.pow_le_pow_right hyp.p_prime.pos hAlog
      _ ≤ Nat.card ↥A := Nat.pow_log_le_self p (Nat.card_pos (α := ↥A)).ne'
      _ ≤ Nat.card ↥S :=
        Nat.card_le_card_of_injective (fun x : ↥A => (x : ↥S)) Subtype.val_injective
  have hTne : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) 0 ≠ ⊥ := by
    intro h
    rw [OddOrder.Isaacs.Ch04.iterCommutator_zero] at h
    rw [h, Subgroup.card_bot, one_mul] at hScard
    rw [← hScard] at hp3
    have hlt : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hyp.p_prime.one_lt (by norm_num)
    omega
  -- `|S| = p² · |H₁|`, so `[S : H₁] = p²`.
  have hstep := hyp.card_iterCommutator_eq hR₀S hexp hS (le_refl T) hTne
  rw [OddOrder.Isaacs.Ch04.iterCommutator_zero, ← hH₁def] at hstep
  have hH₁index : H₁.index = p ^ 2 := by
    have hmul : Nat.card ↥H₁ * H₁.index = Nat.card ↥S := H₁.card_mul_index
    have hSp2 : Nat.card ↥S = Nat.card ↥H₁ * p ^ 2 := by rw [← hScard, hstep]; ring
    rw [hSp2] at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥H₁)) hmul
  -- `S/H₁` has order `p²`, hence is abelian, so `S' ≤ H₁`; and `H₁ = ⁅T,S⁆ ≤ S'`.
  have hquot : Nat.card (↥S ⧸ H₁) = p ^ 2 := hH₁index
  haveI : IsMulCommutative (↥S ⧸ H₁) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hquot
  have hSle : _root_.commutator ↥S ≤ H₁ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hone : (QuotientGroup.mk' H₁) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact ‹IsMulCommutative (↥S ⧸ H₁)›.is_comm.comm _ _
    exact (QuotientGroup.eq_one_iff _).mp hone
  have hH₁le : H₁ ≤ _root_.commutator ↥S := by
    rw [hH₁def, OddOrder.Isaacs.Ch04.iterCommutator_succ,
      OddOrder.Isaacs.Ch04.iterCommutator_zero, commutator_def]
    exact Subgroup.commutator_mono le_top le_rfl
  have heq : H₁ = _root_.commutator ↥S := le_antisymm hH₁le hSle
  exact ⟨heq, by rw [← heq]; exact hquot⟩

/-- **BG Theorem E.3(b), Step 2, the elided small case for (E.7)**: `|S/S'| = p²` when
`|S| ≤ p³`.

This is where BG's *"an examination of the `p`-groups of order at most `p³`"* is genuinely
needed — unlike the clause `R₀ ⊄ S'`, which `S' ≤ Z(S)` alone already settles
(`not_le_derivedInG_of_derived_central`).  It is also the first point at which BG's
hypothesis that `S` contains `R₀` **properly** does any work.

* `S` abelian: exponent `p` makes it elementary abelian, and `R₀ ≤ S` puts `S` inside
  `C_R(R₀)`, of `p`-rank `≤ 2`; so `|S| ≤ p²`, while `R₀ < S` forces `|S| ≥ p²`.  Then
  `S' = 1` and `|S/S'| = |S| = p²`.
* `S` nonabelian: then `|S| = p³`; `S/Z(S)` is non-cyclic, so `|Z(S)| = p`, and `cl(S) ≤ 2`
  with `S' ≠ 1` gives `S' = Z(S)` of order `p`, whence `|S/S'| = p³/p = p²`. -/
theorem RegularOperatorSetup.card_quotient_commutator_of_card_le_prime_cube [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ < S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hcard : Nat.card ↥S ≤ p ^ 3) :
    Nat.card (↥S ⧸ _root_.commutator ↥S) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hSpg : IsPGroup p ↥S := hyp.R_pGroup.to_subgroup S
  -- `R₀ < S` gives `p² ≤ |S|`.
  have hR₀lt : hyp.R₀.subgroupOf S < (⊤ : Subgroup ↥S) :=
    lt_of_le_of_ne le_top fun h => absurd (Subgroup.subgroupOf_eq_top.mp h) hR₀S.not_ge
  have hp2 : p ^ 2 ≤ Nat.card ↥S := by
    have := prime_mul_card_le_card_of_lt hSpg hR₀lt
    rw [hyp.card_R₀_subgroupOf hR₀S.le, Subgroup.card_top] at this
    calc p ^ 2 = p * p := sq p
      _ ≤ Nat.card ↥S := this
  by_cases habel : IsMulCommutative ↥S
  · -- `S` elementary abelian of rank `≤ 2`, so `|S| = p²` and `S' = 1`.
    have hSC : S ≤ Subgroup.centralizer (hyp.R₀ : Set R) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg (fun z : ↥S => (z : R))
        (habel.is_comm.comm (⟨g, hR₀S.le hg⟩ : ↥S) ⟨x, hx⟩)
    have hEA : IsElementaryAbelian p ↥S := ⟨fun x y => habel.is_comm.comm x y, hexp⟩
    have hrank : pRank ↥S p ≤ 2 :=
      (pRank_le_of_injective (f := Subgroup.inclusion hSC)
        (Subgroup.inclusion_injective hSC)).trans hyp.pRank_centralizer_R₀_le_two
    have hle : Nat.card ↥S ≤ p ^ 2 := by
      obtain ⟨k, hk⟩ := hSpg.exists_card_eq
      have hlog := hEA.log_card_le_pRank
      rw [hk, Nat.log_pow hyp.p_prime.one_lt] at hlog
      rw [hk]
      exact Nat.pow_le_pow_right hyp.p_prime.pos (hlog.trans hrank)
    haveI := habel
    have hcomm : _root_.commutator ↥S = ⊥ := commutator_eq_bot ↥S
    rw [hcomm]
    change (⊥ : Subgroup ↥S).index = p ^ 2
    rw [Subgroup.index_bot]
    omega
  · -- `S` nonabelian: `|S| = p³`, `|Z(S)| = p`, `S' = Z(S)`.
    have hcentre := commutator_le_center_of_card_le_prime_cube hSpg hcard
    have hcommne : _root_.commutator ↥S ≠ ⊥ := by
      intro h
      refine habel (IsMulCommutative.of_comm fun a b => ?_)
      have hmem : ⁅a, b⁆ ∈ (⊥ : Subgroup ↥S) := h ▸ Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hmem)
    -- `|Z(S)| ≤ p`: otherwise `|S : Z(S)| ≤ p`, so `S/Z(S)` is cyclic and `S` abelian.
    have hZle : Nat.card ↥(Subgroup.center ↥S) ≤ p := by
      by_contra hgt
      push Not at hgt
      obtain ⟨j, hj⟩ := (hSpg.to_subgroup (Subgroup.center ↥S)).exists_card_eq
      have hZp2 : p ^ 2 ≤ Nat.card ↥(Subgroup.center ↥S) := by
        rw [hj]
        refine Nat.pow_le_pow_right hyp.p_prime.pos ?_
        by_contra hj2
        push Not at hj2
        rw [hj] at hgt
        have hjle : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hyp.p_prime.pos (by omega)
        rw [pow_one] at hjle
        omega
      have hidx : (Subgroup.center ↥S).index * Nat.card ↥(Subgroup.center ↥S) =
          Nat.card ↥S := (Subgroup.center ↥S).index_mul_card
      have hidxle : (Subgroup.center ↥S).index ≤ p := by
        nlinarith [hidx, hcard, hZp2, hyp.p_prime.pos, sq_nonneg p]
      haveI : IsCyclic (↥S ⧸ Subgroup.center ↥S) := by
        refine isCyclic_of_card_dvd_prime (p := p) ?_
        obtain ⟨m, hm⟩ := (hSpg.to_quotient (Subgroup.center ↥S)).exists_card_eq
        have hqidx : Nat.card (↥S ⧸ Subgroup.center ↥S) = (Subgroup.center ↥S).index := rfl
        have hm1 : m ≤ 1 := by
          by_contra hm2
          push Not at hm2
          have : p ^ 2 ≤ Nat.card (↥S ⧸ Subgroup.center ↥S) := by
            rw [hm]; exact Nat.pow_le_pow_right hyp.p_prime.pos hm2
          rw [hqidx] at this
          nlinarith [hidxle, hyp.p_prime.one_lt]
        rw [hm]
        interval_cases m
        · exact one_dvd p
        · rw [pow_one]
      exact habel (isMulCommutative_of_isCyclic_quotient_center_self ↥S)
    -- `S' ≤ Z(S)` with `S' ≠ 1` and `|Z(S)| ≤ p` forces `|S'| = |Z(S)| = p`.
    have hScomm : Nat.card ↥(_root_.commutator ↥S) = p := by
      obtain ⟨j, hj⟩ := (hSpg.to_subgroup (_root_.commutator ↥S)).exists_card_eq
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | h
        · exact absurd (Subgroup.card_eq_one.mp (by simpa using hj)) hcommne
        · exact h
      have hlecent : Nat.card ↥(_root_.commutator ↥S) ≤ p :=
        le_trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hcentre)) hZle
      have hge : p ≤ Nat.card ↥(_root_.commutator ↥S) := by
        rw [hj]
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ j := Nat.pow_le_pow_right hyp.p_prime.pos hjpos
      omega
    -- `|S| = p³`, so the quotient has order `p²`.
    have hScube : Nat.card ↥S = p ^ 3 := by
      obtain ⟨k, hk⟩ := hSpg.exists_card_eq
      rcases Nat.lt_or_ge k 3 with hk2 | hk3
      · exfalso
        have hup : Nat.card ↥S ≤ p ^ 2 := by
          rw [hk]; exact Nat.pow_le_pow_right hyp.p_prime.pos (by omega)
        exact habel (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p)
          (le_antisymm hup hp2))
      · have hk3' : k = 3 := by
          by_contra h
          have h4 : 4 ≤ k := by omega
          rw [hk] at hcard
          have : p ^ 4 ≤ p ^ k := Nat.pow_le_pow_right hyp.p_prime.pos h4
          have hlt : p ^ 3 < p ^ 4 :=
            Nat.pow_lt_pow_right hyp.p_prime.one_lt (by norm_num)
          omega
        rw [hk, hk3']
    change (_root_.commutator ↥S).index = p ^ 2
    have hmul : Nat.card ↥(_root_.commutator ↥S) * (_root_.commutator ↥S).index =
        Nat.card ↥S := (_root_.commutator ↥S).card_mul_index
    rw [hScomm, hScube] at hmul
    refine Nat.eq_of_mul_eq_mul_left hyp.p_prime.pos ?_
    rw [hmul]; ring

/-- **BG Theorem E.3(b), Step 2, the elided small case**: if `S' ≤ Z(S)` then `R₀ ⊄ S'`.

BG dispatches `|S| ≤ p³` by *"an examination of the `p`-groups of order at most `p³`"*.  No
examination is needed for the clause `R₀ ⊄ S'`: all that matters is that such an `S` has
nilpotency class `≤ 2`, i.e. `S' ≤ Z(S)`.  For if `R₀ ≤ S'`, then `S` centralizes `S'` hence
centralizes `R₀`, so `S ≤ C_R(R₀)`, which is **abelian**
(`isMulCommutative_centralizer_R₀`); then `S' = 1`, forcing `R₀ = 1` and contradicting
`|R₀| = p`.

Note this needs no `R₀ ≤ S` hypothesis: `R₀ ≤ S'` already puts `R₀` inside `S`. -/
theorem RegularOperatorSetup.not_le_derivedInG_of_derived_central [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hcent : S ≤ Subgroup.centralizer (derivedInG S : Set R)) :
    ¬ hyp.R₀ ≤ derivedInG S := by
  intro hle
  have hSC : S ≤ Subgroup.centralizer (hyp.R₀ : Set R) :=
    hcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle))
  haveI : IsMulCommutative ↥S := IsMulCommutative.of_comm fun x y => by
    have hxy := hyp.isMulCommutative_centralizer_R₀.is_comm.comm
      (⟨(x : R), hSC x.2⟩ : ↥(Subgroup.centralizer (hyp.R₀ : Set R)))
      ⟨(y : R), hSC y.2⟩
    exact Subtype.ext
      (congrArg (fun z : ↥(Subgroup.centralizer (hyp.R₀ : Set R)) => (z : R)) hxy)
  have hbot : derivedInG S = ⊥ := by
    rw [derivedInG, commutator_eq_bot, Subgroup.map_bot]
  rw [hbot, le_bot_iff] at hle
  have hc := hyp.R₀_card
  rw [hle, Subgroup.card_bot] at hc
  exact hyp.p_prime.one_lt.ne hc

/-- `|S| ≤ p³` forces `S' ≤ Z(S)`, the hypothesis of
`not_le_derivedInG_of_derived_central`.

`Ch1.S04.nilpotencyClass_le_of_card_le_pow` gives `cl(S) ≤ 2`, i.e. `γ₃(S) = ⁅S', S⁆ = 1`;
that is exactly `S' ≤ Z(S)`, which transported to the ambient group reads
`S ≤ C_R(S')`. -/
theorem RegularOperatorSetup.derived_central_of_card_le_prime_cube [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hcard : Nat.card ↥S ≤ p ^ 3) :
    S ≤ Subgroup.centralizer (derivedInG S : Set R) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hcentre := commutator_le_center_of_card_le_prime_cube
    (hyp.R_pGroup.to_subgroup S) hcard
  -- transport to the ambient group
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at *
  intro g hg
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
  have hcomm := congrArg (fun z : ↥S => (z : R))
    (Subgroup.mem_center_iff.mp (hcentre hg') ⟨x, hx⟩)
  simpa using hcomm.symm

/-- **BG Theorem E.3(b), Step 2, first conclusion of (E.13) — unconditionally**: for *any*
subgroup `S ≤ R` of exponent `p` containing `R₀`, `R₀ ⊄ S'`.

This is Step 2's `R₀ ⊄ S'` with both of BG's branches discharged: `|S| ≤ p³` by
`not_le_derivedInG_of_derived_central` (BG's elided *"examination of the `p`-groups of order
at most `p³`"*) and `|S| > p³` by the narrow route
(`not_le_derivedInG_of_three_le_pRank`), the two meeting at
`three_le_pRank_of_prime_cube_lt_card`.

⚠ BG additionally assumes `S` is `A`-invariant and `R₀ < S` *properly*; neither is used for
this clause. -/
theorem RegularOperatorSetup.not_le_derivedInG [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) :
    ¬ hyp.R₀ ≤ derivedInG S := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rcases le_or_gt (Nat.card ↥S) (p ^ 3) with hle | hgt
  · exact hyp.not_le_derivedInG_of_derived_central
      (hyp.derived_central_of_card_le_prime_cube hle)
  · exact hyp.not_le_derivedInG_of_three_le_pRank hR₀S
      (three_le_pRank_of_prime_cube_lt_card (hyp.R_pGroup.to_subgroup S) hexp hgt)

/-- `R₀ ≤ Ω₁(R)`: every element of `R₀` has order dividing `|R₀| = p`. -/
theorem RegularOperatorSetup.R₀_le_omega [Finite R]
    (hyp : RegularOperatorSetup R B p q) : hyp.R₀ ≤ Omega R p 1 := by
  intro x hx
  refine Omega.mem_of_pow_eq_one ?_
  have h := pow_card_eq_one' (G := ↥hyp.R₀) (x := ⟨x, hx⟩)
  rw [hyp.R₀_card] at h
  simpa using congrArg (fun z : ↥hyp.R₀ => (z : R)) h

/-- **The engine behind BG (E.9)**: an automorphism `φ` of a group of prime order `p` is a
power map, `φ x = xʳ`; and if `φ^q = 1` then `r^q ≡ 1 (mod p)`.

BG applies this twice — first to `R₀` itself (the opening of (E.9)), then to each section
`Hᵢ/Hᵢ₊₁` of the chain, which (E.6) shows also has order `p`.  Stated abstractly so both
uses go through the same lemma, and with an **integer** exponent, as BG does. -/
theorem exists_zpow_eq_of_card_eq_prime {C : Type*} [Group C] {p q : ℕ} (hp : p.Prime)
    (hC : Nat.card C = p) (φ : MulAut C) (hφ : φ ^ q = 1) :
    ∃ r : ℤ, (∀ x : C, φ x = x ^ r) ∧ ((r : ZMod p) ^ q = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; exact hp.pos.ne')
  haveI : IsCyclic C := isCyclic_of_prime_card hC
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨k, hk⟩ := hg (φ g)
  have hord : orderOf g = p := by
    have htop : Subgroup.zpowers g = ⊤ := by ext x; simpa using hg x
    have hc := Nat.card_zpowers g
    rw [htop, Subgroup.card_top, hC] at hc
    exact hc.symm
  refine ⟨k, fun x => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hg x
    rw [← hm, map_zpow, ← hk, ← zpow_mul, ← zpow_mul, mul_comm]
  · have hiter : ∀ n : ℕ, (φ ^ n) g = g ^ (k ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hstep : (φ ^ (n + 1)) g = (φ ^ n) (φ g) := by rw [pow_succ]; rfl
        rw [hstep, ← hk, map_zpow, ih, ← zpow_mul, ← pow_succ]
    have hgq : g ^ (k ^ q) = g := by rw [← hiter q, hφ]; rfl
    have hz : g ^ (k ^ q - 1) = 1 := by rw [zpow_sub, hgq, zpow_one, mul_inv_cancel]
    have hdvd : (p : ℤ) ∣ k ^ q - 1 := by
      rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr hz
    have hzero : ((k ^ q - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at hzero
    exact sub_eq_zero.mp hzero

/-- **BG Theorem E.3(b), Step 2, (E.9), opening sentence**: *"Then `vᵃ = vʳ` for some integer
`r` such that `r^q ≡ 1 (mod p)`."*

`A` fixes `R₀`, which has prime order `p`, and `a^q = 1` because `|A| = q`; so
`exists_zpow_eq_of_card_eq_prime` applies to the induced automorphism. -/
theorem RegularOperatorSetup.exists_zpow_eq_act_of_mem_A [Finite R]
    (hyp : RegularOperatorSetup R B p q) {a : B} (ha : a ∈ hyp.A) :
    ∃ r : ℤ, (∀ v ∈ hyp.R₀, hyp.act a v = v ^ r) ∧ ((r : ZMod p) ^ q = 1) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set ψ : ↥hyp.A →* MulAut ↥hyp.R₀ :=
    OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hyp.isAInvariant_R₀ with hψ
  have haq : (⟨a, ha⟩ : ↥hyp.A) ^ q = 1 := by
    have h := pow_card_eq_one' (G := ↥hyp.A) (x := ⟨a, ha⟩)
    rwa [hyp.A_card] at h
  obtain ⟨r, hr, hrq⟩ := exists_zpow_eq_of_card_eq_prime hyp.p_prime hyp.R₀_card
    (ψ ⟨a, ha⟩) (by rw [← map_pow, haq, map_one])
  refine ⟨r, fun v hv => ?_, hrq⟩
  have h2 := congrArg (fun z : ↥hyp.R₀ => (z : R)) (hr ⟨v, hv⟩)
  simpa [hψ, OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val] using h2

/-- **BG Theorem E.3(b), Step 2, (E.11)**: `r ≢ 1 (mod p)` for `a ∈ A^#`.

If `a` acted on `R₀` as the *identity* power map it would fix `R₀ ≠ 1` pointwise, and `A`
acts regularly — `C_R(α) = 1` for `α ∈ A^#`.  This is the first point in Step 2 where the
setup's regularity hypothesis does any work. -/
theorem RegularOperatorSetup.zpow_exponent_ne_one [Finite R]
    (hyp : RegularOperatorSetup R B p q) {a : B} (ha : a ∈ hyp.A) (hane : a ≠ 1)
    {r : ℤ} (hr : ∀ v ∈ hyp.R₀, hyp.act a v = v ^ r) :
    (r : ZMod p) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  intro h1
  -- `p ∣ r - 1`, so the `r`-th power map is the identity on `R₀`.
  have hdvd : (p : ℤ) ∣ r - 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
    push_cast
    rw [h1, sub_self]
  obtain ⟨c, hc⟩ := hdvd
  have hfix : ∀ v ∈ hyp.R₀, hyp.act a v = v := by
    intro v hv
    have hvp : v ^ p = 1 := by
      have h := pow_card_eq_one' (G := ↥hyp.R₀) (x := ⟨v, hv⟩)
      rw [hyp.R₀_card] at h
      simpa using congrArg (fun z : ↥hyp.R₀ => (z : R)) h
    have hsub : v ^ (r - 1) = 1 := by
      rw [hc, zpow_mul, zpow_natCast, hvp, one_zpow]
    calc hyp.act a v = v ^ r := hr v hv
      _ = v ^ ((r - 1) + 1) := by congr 1; ring
      _ = v ^ (r - 1) * v ^ (1 : ℤ) := zpow_add v _ _
      _ = v := by rw [hsub, zpow_one, one_mul]
  -- regularity then kills `R₀`
  have hbot : hyp.R₀ = ⊥ := by
    refine le_bot_iff.mp fun v hv => ?_
    exact Subgroup.mem_bot.mpr (hyp.A_regular a ha hane v (hfix v hv))
  have hc' := hyp.R₀_card
  rw [hbot, Subgroup.card_bot] at hc'
  exact hyp.p_prime.one_lt.ne hc'

/-- **BG Theorem E.3(b), Step 2, (E.8)**: `Hᵢ = S_{i+1}` — BG's chain out of `T` *is* the
lower central series of `S`, from its second term on.

BG derives this "similarly, by induction" after (E.7).  The induction is immediate once
(E.7) has identified `H₁ = S'`: both `Hᵢ₊₁ = ⁅Hᵢ, S⁆` and `γᵢ₊₁(S) = ⁅γᵢ(S), S⁆` are the
*same* recursion, so they agree forever after agreeing once.

(Indices: BG writes `S = S₁ ⊃ S₂ ⊃ ⋯`, so BG's `S_{i+1}` is mathlib's
`lowerCentralSeries ⊤ i`.) -/
theorem RegularOperatorSetup.iterCommutator_eq_lowerCentralSeries [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    ∀ i : ℕ, OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1)
      = Subgroup.lowerCentralSeries (⊤ : Subgroup ↥S) (i + 1)
  | 0 => by
      rw [Subgroup.top_lowerCentralSeries_one]
      exact (hyp.commutator_eq_and_card_quotient hR₀S hexp hS).1
  | i + 1 => by
      rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.lowerCentralSeries_succ,
        hyp.iterCommutator_eq_lowerCentralSeries hR₀S hexp hS i]

/-- **BG Theorem E.3(b), Step 2, (E.9)**: the chain section `Hᵢ/Hᵢ₊₁` has order `p`.

The `(E.6)` factor bound `|Hᵢ| = p·|Hᵢ₊₁|` restated as the index of `Hᵢ₊₁` *inside* `Hᵢ`,
which is the form `IsAInvariant.quotientMulAutHom` and
`exists_zpow_eq_of_card_eq_prime` consume. -/
theorem RegularOperatorSetup.index_subgroupOf_chain [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥) :
    ((OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
        (⊤ : Subgroup ↥S) (i + 1)).subgroupOf
      (OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
        (⊤ : Subgroup ↥S) i)).index = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  set Hi := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i with hHi
  set Hj := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1) with hHj
  have hle : Hj ≤ Hi := iterCommutator_antitone i
  have hmul := (Hj.subgroupOf Hi).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    hyp.card_iterCommutator_eq hR₀S hexp hS (le_refl T) hne] at hmul
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Hj)) ?_
  rw [hmul, mul_comm]

/-- **BG Theorem E.3(b), Step 2, (E.9)**: `Hᵢ₊₁` is `A`-invariant *inside* `Hᵢ`.

Both chain terms are `A`-invariant in `S` (`isAInvariant_iterCommutator`); this transports
that to the restricted action on `↥Hᵢ`, which is what lets the action descend to the
section `Hᵢ/Hᵢ₊₁` via `Isaacs.Ch03.IsAInvariant.quotientMulAutHom`. -/
theorem RegularOperatorSetup.isAInvariant_subgroupOf_chain
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) (i : ℕ) :
    IsAInvariant (hyp.isAInvariant_iterCommutator hSinv i).restrict
      ((OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
          (⊤ : Subgroup ↥S) (i + 1)).subgroupOf
        (OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
          (⊤ : Subgroup ↥S) i)) := by
  rw [isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact (hyp.isAInvariant_iterCommutator hSinv (i + 1)).smul_mem a hx

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem E.3(b), Step 2, (E.9)**: the eigenvalue `rᵢ` on the chain section.

BG: *"by (E.6), for `i = 0,…,n−1`, `wᵢᵃ ≡ wᵢ^{rᵢ} (mod Hᵢ₊₁)` for some integers `rᵢ` such
that `rᵢ^q ≡ 1 (mod p)`."*

Everything needed is now in place: the section `Hᵢ/Hᵢ₊₁` has order `p`
(`index_subgroupOf_chain`) and carries the induced `A`-action
(`isAInvariant_subgroupOf_chain` fed to `quotientMulAutHom`), so
`exists_zpow_eq_of_card_eq_prime` produces the power map and the congruence.  BG's
"`≡ mod Hᵢ₊₁`" is exactly this statement read in the quotient. -/
theorem RegularOperatorSetup.exists_zpow_eq_on_chain_section [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥)
    {a : B} (ha : a ∈ hyp.A) :
    ∃ r : ℤ,
      (∀ x, (quotientMulAutHom (hyp.isAInvariant_subgroupOf_chain hSinv i)) ⟨a, ha⟩ x = x ^ r) ∧
      ((r : ZMod p) ^ q = 1) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have haq : (⟨a, ha⟩ : ↥hyp.A) ^ q = 1 := by
    have h := pow_card_eq_one' (G := ↥hyp.A) (x := ⟨a, ha⟩)
    rwa [hyp.A_card] at h
  refine exists_zpow_eq_of_card_eq_prime hyp.p_prime ?_ _ ?_
  · exact hyp.index_subgroupOf_chain hR₀S hexp hS hne
  · rw [← map_pow, haq, map_one]

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **BG Theorem E.3(b), Step 2, (E.10)**: `A` does **not** centralize a nontrivial chain
section.

BG: *"if `rᵢ ≡ 1 (mod p)` for some `i`, then `A` centralizes `Hᵢ/Hᵢ₊₁` by Proposition
1.5(d) … contrary to the regular action of `A` on `R`."*

Stated as the induced automorphism being `≠ 1`, which is the content; the congruence form
`rᵢ ≢ 1` follows by combining with `exists_zpow_eq_on_chain_section`.

If `a` acted trivially on `Hᵢ/Hᵢ₊₁`, then Proposition 1.5(d) in its **element** form
(`Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal`) lifts a coset representative
`g ∉ Hᵢ₊₁` to an `⟨a⟩`-fixed `c` in the same coset; `c ∉ Hᵢ₊₁` so `c ≠ 1`, and `a` fixes it
— contradicting `C_R(α) = 1` for `α ∈ A^#`.

⚠ The coprime lemma is applied with the acting group `⟨a⟩`, **not** all of `A`: the
hypothesis is about one specific `a`. -/
theorem RegularOperatorSetup.quotient_action_ne_one [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) {i : ℕ}
    (hlt : OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1) <
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i)
    {a : B} (ha : a ∈ hyp.A) (hane : a ≠ 1) :
    (quotientMulAutHom (hyp.isAInvariant_subgroupOf_chain hSinv i)) ⟨a, ha⟩ ≠ 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  set Hi := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i with hHi
  set Hj := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1) with hHj
  set N : Subgroup ↥Hi := Hj.subgroupOf Hi with hN
  set φ : ↥hyp.A →* MulAut ↥Hi := (hyp.isAInvariant_iterCommutator hSinv i).restrict with hφ
  set hNinv := hyp.isAInvariant_subgroupOf_chain hSinv i with hNinvdef
  intro htriv
  -- a representative `g ∈ Hᵢ` outside `Hᵢ₊₁`
  obtain ⟨g0, hg0Hi, hg0Hj⟩ : ∃ x, x ∈ Hi ∧ x ∉ Hj := by
    by_contra hcon
    push Not at hcon
    exact hlt.ne (le_antisymm hlt.le fun x hx => hcon x hx)
  set g : ↥Hi := ⟨g0, hg0Hi⟩ with hg
  have hgN : g ∉ N := by rw [hN, Subgroup.mem_subgroupOf]; exact hg0Hj
  -- every element of `⟨a⟩` acts trivially on the section
  set Z : Subgroup ↥hyp.A := Subgroup.zpowers (⟨a, ha⟩ : ↥hyp.A) with hZ
  have hZtriv : ∀ b : ↥Z, quotientMulAutHom hNinv (b : ↥hyp.A) = 1 := by
    rintro ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [map_zpow, htriv, one_zpow]
  have hgfix : ∀ b : ↥Z, ∃ n ∈ N, (φ.comp Z.subtype) b g = g * n := by
    intro b
    refine ⟨g⁻¹ * (φ (b : ↥hyp.A)) g, ?_, (mul_inv_cancel_left _ _).symm⟩
    have h1 : quotientMulAutHom hNinv (b : ↥hyp.A) (QuotientGroup.mk' N g) =
        QuotientGroup.mk' N ((φ (b : ↥hyp.A)) g) := quotientMulAutHom_apply_mk' hNinv _ _
    rw [hZtriv b, MulAut.one_apply] at h1
    exact (QuotientGroup.eq (s := N)).mp h1
  -- Prop 1.5(d), element form
  haveI hNpg : IsPGroup p ↥N :=
    ((hyp.R_pGroup.to_subgroup S).to_subgroup Hi).to_subgroup N
  haveI : Group.IsNilpotent ↥N := hNpg.isNilpotent
  haveI : IsSolvable ↥N := inferInstance
  haveI : Finite ↥hyp.A :=
    Nat.finite_of_card_ne_zero (by rw [hyp.A_card]; exact hyp.q_prime.pos.ne')
  have hCop : Nat.Coprime (Nat.card ↥Z) (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := hNpg.exists_card_eq
    have hZle : Nat.card ↥Z ∣ Nat.card ↥hyp.A := Subgroup.card_subgroup_dvd_card Z
    rw [hyp.A_card] at hZle
    rw [hk]
    exact Nat.Coprime.pow_right _
      (Nat.Coprime.coprime_dvd_left hZle
        ((Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm hyp.p_ne_q)))
  have hNinv' : IsAInvariant (φ.comp Z.subtype) N := fun b => hNinv (Z.subtype b)
  obtain ⟨c, hcfix, n, hnN, hcn⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      (φ := φ.comp Z.subtype) hCop (Or.inr ‹IsSolvable ↥N›) hNinv' hgfix
  -- `c` is `a`-fixed and nontrivial: contradiction with regularity
  have hcN : c ∉ N := by
    rw [hcn]
    intro hmem
    exact hgN (by simpa using N.mul_mem hmem (N.inv_mem hnN))
  have hcne : (c : ↥S) ≠ 1 := by
    intro h
    have hc1 : c = 1 := Subtype.ext h
    exact hcN (hc1 ▸ N.one_mem)
  have hafix := hcfix ⟨(⟨a, ha⟩ : ↥hyp.A), Subgroup.mem_zpowers _⟩
  have hact : hyp.act a ((c : ↥S) : R) = ((c : ↥S) : R) :=
    congrArg (fun z : ↥S => (z : R)) (congrArg (fun z : ↥Hi => (z : ↥S)) hafix)
  have hone : ((c : ↥S) : R) = 1 := hyp.A_regular a ha hane _ hact
  exact hcne (Subtype.ext hone)

/-- **BG Theorem E.3(b), Step 2, (E.7) — unconditionally**: `|S/S'| = p²` for every
exponent-`p` subgroup `S` properly containing `R₀`.

Both of BG's branches joined at `three_le_pRank_of_prime_cube_lt_card`, exactly as for
`not_le_derivedInG`. -/
theorem RegularOperatorSetup.card_quotient_commutator [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ < S)
    (hexp : ∀ x : ↥S, x ^ p = 1) :
    Nat.card (↥S ⧸ _root_.commutator ↥S) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rcases le_or_gt (Nat.card ↥S) (p ^ 3) with hle | hgt
  · exact hyp.card_quotient_commutator_of_card_le_prime_cube hR₀S hexp hle
  · exact (hyp.commutator_eq_and_card_quotient hR₀S.le hexp
      (three_le_pRank_of_prime_cube_lt_card (hyp.R_pGroup.to_subgroup S) hexp hgt)).2

/-- **`R₁` contains an element of order `p` outside `R₀`**.

`R₁ ≠ 1` is a `p`-group, so Cauchy applies; disjointness from `R₀` is a setup field.

This is where the setup's cyclic factor `R₁` finally earns its keep: every earlier step of
Step 2 went through without it, but E.3(b)'s third clause is *false* for `S = R₀` (then
`|S/S'| = p`), so properness has to come from somewhere.  Step 3's seed
`Ω₁(C_R(R₀))` needs the same witness. -/
theorem RegularOperatorSetup.exists_mem_R₁_pow_eq_one [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    ∃ z ∈ hyp.R₁, z ∉ hyp.R₀ ∧ z ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  obtain ⟨k, hk⟩ := (hyp.R_pGroup.to_subgroup hyp.R₁).exists_card_eq
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hyp.R₁_ne_bot
    · exact h
  have hdvd : p ∣ Nat.card ↥hyp.R₁ := by
    rw [hk]; exact dvd_pow_self p hkpos.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥hyp.R₁) p hdvd
  have hzp : ((z : R)) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg (fun w : ↥hyp.R₁ => (w : R)) this
  refine ⟨(z : R), z.2, fun hzR₀ => ?_, hzp⟩
  have hzbot : (z : R) ∈ (⊥ : Subgroup R) :=
    (disjoint_iff.mp hyp.R₀_disjoint_R₁) ▸ Subgroup.mem_inf.mpr ⟨hzR₀, z.2⟩
  have hz1 : z = 1 := Subtype.ext (Subgroup.mem_bot.mp hzbot)
  rw [hz1, orderOf_one] at hz
  exact hyp.p_prime.one_lt.ne hz

/-- `R₀ < Ω₁(R)` **properly** — the witness of `exists_mem_R₁_pow_eq_one` lies in `Ω₁(R)`. -/
theorem RegularOperatorSetup.R₀_lt_omega [Finite R]
    (hyp : RegularOperatorSetup R B p q) : hyp.R₀ < Omega R p 1 := by
  refine lt_of_le_of_ne hyp.R₀_le_omega fun heq => ?_
  obtain ⟨z, _, hzR₀, hzp⟩ := hyp.exists_mem_R₁_pow_eq_one
  refine hzR₀ ?_
  rw [heq]
  exact Omega.mem_of_pow_eq_one (by simpa using hzp)

/- **BG Theorem E.3(b)**, all three clauses, are **proved** one leaf downstream, in
`OddOrder/BG/AppE_ExponentP.lean`: `omega_pow_eq_one` (first clause) is BG's Step 3, and the
other two are Step 2 applied to `S = Ω₁(R)` on top of it.  They have to live there — Step 3
is what that leaf carries. -/

/- **BG Theorem E.3(c)** (`|Ω₁(R)| ≤ p^q`) is **proved**, but lives one leaf downstream, as
`RegularOperatorSetup.card_omega_le` in `OddOrder/BG/AppE_RegularOperator.lean`.  It has to:
its proof is BG's `(E.9)`--`(E.12)` eigenvalue count, and that machinery is what the
downstream leaf carries. -/

/- **BG Theorem E.3(d)** (`B` fixes `R₀Φ(Ω₁(R))` ⇒ `B` fixes `R₀`) is **proved** two leaves
downstream, as `RegularOperatorSetup.B_fixes_R₀_of_fixes_frattini` in
`OddOrder/BG/AppE_SemidirectFrattini.lean`.  It has to live there: BG's Step 4 consumes the
class/coset count of `AppE_ExponentP.lean` (itself built on Step 2's `(E.15)`), and then
Glauberman's fixed-point lemma and Isaacs Thm 3.27. -/

/- **BG Proposition E.4** (`C_S(Z₂(S))` abelian of index `p`) is **proved** downstream, as
`RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p` in
`OddOrder/BG/AppE_PropE4.lean` — **with one corrective hypothesis added**.  As printed the
proposition is *false*: its display `(E.23)` silently uses the 2-step centralizer
relations `⁅Hₐ, T⁆ ≤ Hₐ₊₂` (non-exceptionality), which the printed hypotheses do not
force; the Lazard group of the exceptional filiform `Q₆` is a machine-checked
counterexample (`printed_propE4_false` in `OddOrder/BG/AppE_FiliformRefutation.lean`).
The corrected statement adds exactly that assumption as `hdc`.  It has to live
downstream: its proof consumes the `(E.28)` engine of `AppE_EigenvalueCombinatorics.lean`,
the corrected `(E.23)` supply of `AppE_BetaSupply.lean`, and the eigenvalue pieces of
`AppE_AbelianCentralizer.lean`.  Master note:
`notes/bg/appE_e4_counterexample_2026_07_21.md` (issues 3021/9402). -/

end RegularOperator

/-! ## E.5: the maximal-subgroup application -/

section MaximalApplication

open OddOrder.BG.Ch3.S12 OddOrder.BG.Ch4.S14

variable {G : Type*} [Group G]

/- **BG Corollary E.5** (`maximalSubgroups_isTypeI_or_isTypeII`) is **proved** one leaf
downstream, in `OddOrder/BG/AppE_E5Counting.lean` — with the corrected E.4's `hdc`
hypothesis added to the (ii) branch of its alternative (as printed that branch is
irreparable: `printed_propE4_false`).  It has to live there: the `(ii) ∧ hdc ⟹ (i)`
half consumes the staged `(E.29)`–`(E.32)` material of `AppE_CorollaryE5.lean` plus
Theorem E.3 / the corrected Proposition E.4, and the closing `(E.33)`/`(E.34)` counting
consumes the §14 machinery (Lemma 14.5(c), Theorem 14.7 duality, the `Ẑ` TI-count). -/

end MaximalApplication

end OddOrder.BG.AppE
