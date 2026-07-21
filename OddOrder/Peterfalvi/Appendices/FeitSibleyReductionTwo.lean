/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyInduction

/-!
# Peterfalvi Appendix IV: Feit–Sibley — reduction (2) machinery (pp. 146–147)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 146–147.  Machinery for reduction (2) of the Theorem (campaign
issue 1054): "if `𝒮(S')` is coherent then `𝒮` is coherent", the `S`-side mirror
of reduction (1).  This file provides the index bridges and the closing
arithmetic:

* `card_quot_sup_Q1_eq_d_mul`: `|H⧸A'Q₁| = d·|S⧸A'|` for `A' ≤ S` — the
  `S`-side counting keeps the factor `|S⧸S₁|` that reduction (1) dropped;
* `card_quot_S_mul_sub_one_le_of_card_quot_sub_le`: the (2)-shaped counting
  extraction `|S⧸S₁|·(|Q₁|−1) ≤ 2da`;
* `index_subgroupOf_sup_prod_eq`: `[Q : A'B'] = |S⧸A'|·|Q₁⧸B'|` for `A' ≤ S`,
  `B' ≤ Q₁`, in the doubly relativised form consumed by
  `exists_deg_sq_le_of_mem_SsetOf` at `D₀ = Z·Z(Q₁)`;
* `false_of_reduction_two_bounds`: the closing arithmetic
  `|S⧸S₁|·|Z(Q₁)|·(|Q₁|−2) < 4d²` versus `≥ 2(4d²−1)`.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-! ## The `S`-side index bridge `|H⧸A'Q₁| = d·|S⧸A'|` -/

/-- `Q₁ ⊓ A' = ⊥` for `A' ≤ S` (the direct-product disjointness). -/
theorem Q1_inf_eq_bot_of_le_S {A' : Subgroup G} (hA' : A' ≤ hyp.S) :
    hyp.Q1 ⊓ A' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ hyp.S ⊓ hyp.Q1 := ⟨hA' hx.2, hx.1⟩
  rwa [hyp.S_inf_Q1_eq_bot] at hmem

/-- `|Q₁⧸⊥| = |Q₁|`. -/
theorem card_quot_bot_subgroupOf_Q1 :
    Nat.card (↥hyp.Q1 ⧸ (⊥ : Subgroup G).subgroupOf hyp.Q1) = Nat.card ↥hyp.Q1 := by
  rw [Subgroup.bot_subgroupOf, ← Subgroup.index_eq_card, Subgroup.index_bot]

/-- **`[Q-in : S-in] = |Q₁|`** — the complementary index of the direct factor
`S` in `Q`, relativised to `H`. -/
theorem relIndex_S_subgroupOf_Q_eq [Finite G]
    [(hyp.S.subgroupOf hyp.H).Normal] :
    (hyp.S.subgroupOf hyp.H).relIndex (hyp.Q.subgroupOf hyp.H)
      = Nat.card ↥hyp.Q1 := by
  classical
  have hinfS : hyp.Q1 ⊓ hyp.S = ⊥ := hyp.Q1_inf_eq_bot_of_le_S le_rfl
  have hS := hyp.card_quot_eq_card_quot_Q1_mul (R := hyp.S) hinfS
  rw [hyp.card_quot_bot_subgroupOf_Q1] at hS
  have hsupSQ : (hyp.S.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)
      = hyp.Q.subgroupOf hyp.H := by
    rw [← Subgroup.subgroupOf_sup hyp.S_le_H (hyp.Q1_le_Q.trans hyp.Q_le_H),
      hyp.sup_S_Q1_eq_Q]
  rw [hsupSQ] at hS
  have hSle : hyp.S.subgroupOf hyp.H ≤ hyp.Q.subgroupOf hyp.H := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hyp.S_le_Q hx
  have ht : (hyp.S.subgroupOf hyp.H).relIndex (hyp.Q.subgroupOf hyp.H)
      * (hyp.Q.subgroupOf hyp.H).index = (hyp.S.subgroupOf hyp.H).index :=
    Subgroup.relIndex_mul_index hSle
  rw [Subgroup.index_eq_card (hyp.S.subgroupOf hyp.H), hS,
    Subgroup.index_eq_card (hyp.Q.subgroupOf hyp.H)] at ht
  have hd : Nat.card (↥hyp.H ⧸ hyp.Q.subgroupOf hyp.H) = hyp.d := by
    rw [← Subgroup.index_eq_card, hyp.index_Q_subgroupOf_eq_d]
  rw [hd] at ht
  exact Nat.eq_of_mul_eq_mul_right hyp.d_pos ht

/-- **`|H⧸A'Q₁| = d·|S⧸A'|`** for `A' ≤ S` (p. 146): the reduction (2)
counting keeps the `|S⧸S₁|` factor.  Two factorisations of `|H⧸A'|` —
`|Q₁|·|H⧸A'Q₁|` (the `Q₁`-side tower) and `|S⧸A'|·|Q₁|·d` (the relIndex tower
through `S` and `Q`) — cancel against `|Q₁|`. -/
theorem card_quot_sup_Q1_eq_d_mul [Finite G] {A' : Subgroup G} (hA' : A' ≤ hyp.S)
    [(A'.subgroupOf hyp.H).Normal] :
    Nat.card (↥hyp.H ⧸ ((A'.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)))
      = hyp.d * Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) := by
  classical
  haveI : (hyp.S.subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx => hyp.S_normal_in_H hh hx
  -- (i) `|H⧸A'| = |Q₁| · |H⧸A'Q₁|`
  have hi := hyp.card_quot_eq_card_quot_Q1_mul (R := A')
    (hyp.Q1_inf_eq_bot_of_le_S hA')
  rw [hyp.card_quot_bot_subgroupOf_Q1] at hi
  -- (ii) `|H⧸A'| = |S⧸A'| · |Q₁| · d` via the relIndex tower `A' ≤ S ≤ Q ≤ H`
  have hAle : A'.subgroupOf hyp.H ≤ hyp.S.subgroupOf hyp.H := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hA' hx
  have hSle : hyp.S.subgroupOf hyp.H ≤ hyp.Q.subgroupOf hyp.H := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hyp.S_le_Q hx
  have hAS : (A'.subgroupOf hyp.H).relIndex (hyp.S.subgroupOf hyp.H)
      = Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) := by
    rw [Subgroup.relIndex_subgroupOf hyp.S_le_H]
    exact Subgroup.index_eq_card _
  have hii : (A'.subgroupOf hyp.H).index
      = Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) * Nat.card ↥hyp.Q1 * hyp.d := by
    have h1 : (A'.subgroupOf hyp.H).relIndex (hyp.S.subgroupOf hyp.H)
        * (hyp.S.subgroupOf hyp.H).relIndex (hyp.Q.subgroupOf hyp.H)
        = (A'.subgroupOf hyp.H).relIndex (hyp.Q.subgroupOf hyp.H) :=
      Subgroup.relIndex_mul_relIndex _ _ _ hAle hSle
    have h2 : (A'.subgroupOf hyp.H).relIndex (hyp.Q.subgroupOf hyp.H)
        * (hyp.Q.subgroupOf hyp.H).index = (A'.subgroupOf hyp.H).index :=
      Subgroup.relIndex_mul_index (hAle.trans hSle)
    rw [← h2, ← h1, hAS, hyp.relIndex_S_subgroupOf_Q_eq, hyp.index_Q_subgroupOf_eq_d]
  rw [Subgroup.index_eq_card] at hii
  rw [hii] at hi
  -- cancel `|Q₁|`
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card ↥hyp.Q1 from Nat.card_pos)
  rw [← hi]
  ring

/-- **The (2)-shaped counting extraction** (p. 146,
"`d|S/S₁|(|Q₁|−1) = ∑_{𝒮(S₁)} χ(1)² ≤ 2dψ(1)`"): from the counting bound
`|H⧸S₁| − |H⧸S₁Q₁| ≤ d²·c`, keep the full factor: `|S⧸S₁|·(|Q₁|−1) ≤ d·c`. -/
theorem card_quot_S_mul_sub_one_le_of_card_quot_sub_le [Finite G]
    {A' : Subgroup G} (hA' : A' ≤ hyp.S) [(A'.subgroupOf hyp.H).Normal] {c : ℝ}
    (hcount : (Nat.card (↥hyp.H ⧸ A'.subgroupOf hyp.H) : ℝ)
        - (Nat.card (↥hyp.H ⧸ ((A'.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) : ℝ)
      ≤ (hyp.d : ℝ) ^ 2 * c) :
    (Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) : ℝ) * ((Nat.card ↥hyp.Q1 : ℝ) - 1)
      ≤ (hyp.d : ℝ) * c := by
  classical
  have hi := hyp.card_quot_eq_card_quot_Q1_mul (R := A')
    (hyp.Q1_inf_eq_bot_of_le_S hA')
  rw [hyp.card_quot_bot_subgroupOf_Q1] at hi
  have hbridge := hyp.card_quot_sup_Q1_eq_d_mul hA'
  rw [hi, hbridge] at hcount
  set m : ℕ := Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) with hm_def
  set q₁ : ℕ := Nat.card ↥hyp.Q1 with hq₁_def
  have hkey : (hyp.d : ℝ) * ((m : ℝ) * ((q₁ : ℝ) - 1)) ≤ (hyp.d : ℝ) * ((hyp.d : ℝ) * c) := by
    push_cast at hcount
    nlinarith [hcount]
  have hd_pos : (0 : ℝ) < (hyp.d : ℝ) := by exact_mod_cast hyp.d_pos
  exact le_of_mul_le_mul_left hkey hd_pos

/-! ## The product index `[Q : A'B'] = |S⧸A'|·|Q₁⧸B'|` -/

/-- **The (2)-side index conversion**: `[Q : A'B'] = |S⧸A'|·|Q₁⧸B'|` for
`A' ≤ S`, `B' ≤ Q₁`, in the doubly relativised form output by
`exists_deg_sq_le_of_mem_SsetOf` at `D₀ = A' ⊔ B'` (in reduction (2):
`D₀ = Z·Z(Q₁)`, giving `a² ≤ |S/Z|·|Q₁/Z(Q₁)|`).  RelIndex tower
`(A'⊔B')-in ≤ (A'⊔Q₁)-in ≤ Q-in` with the second-isomorphism step
`[A'Q₁ : A'B'] = [Q₁ : B']` and the bridge `[Q : A'Q₁] = |S⧸A'|`. -/
theorem index_subgroupOf_sup_prod_eq [Finite G] {A' B' : Subgroup G}
    (hA' : A' ≤ hyp.S) (hB' : B' ≤ hyp.Q1)
    [(A'.subgroupOf hyp.H).Normal] [((A' ⊔ B').subgroupOf hyp.H).Normal] :
    (((A' ⊔ B').subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).index
      = Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S)
        * Nat.card (↥hyp.Q1 ⧸ B'.subgroupOf hyp.Q1) := by
  classical
  have hABH : A' ⊔ B' ≤ hyp.H :=
    sup_le (hA'.trans hyp.S_le_H) (hB'.trans hyp.Q1_le_H)
  have hAQ1H : A' ⊔ hyp.Q1 ≤ hyp.H :=
    sup_le (hA'.trans hyp.S_le_H) hyp.Q1_le_H
  -- the two relIndex factors along `(A'⊔B')-in ≤ (A'⊔Q₁)-in ≤ Q-in`
  have hle₁ : (A' ⊔ B').subgroupOf hyp.H ≤ (A' ⊔ hyp.Q1).subgroupOf hyp.H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact sup_le le_sup_left (hB'.trans le_sup_right) hx
  have hle₂ : (A' ⊔ hyp.Q1).subgroupOf hyp.H ≤ hyp.Q.subgroupOf hyp.H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact sup_le (hA'.trans hyp.S_le_Q) hyp.Q1_le_Q hx
  -- second isomorphism: `[(A'⊔Q₁)-in : (A'⊔B')-in] = [Q₁ : B']`
  have hsup : ((A' ⊔ B').subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)
      = (A' ⊔ hyp.Q1).subgroupOf hyp.H := by
    rw [← Subgroup.subgroupOf_sup hABH (hyp.Q1_le_Q.trans hyp.Q_le_H)]
    congr 1
    rw [sup_assoc, sup_eq_right.mpr hB']
  have hinf : ((A' ⊔ B').subgroupOf hyp.H) ⊓ (hyp.Q1.subgroupOf hyp.H)
      = B'.subgroupOf hyp.H := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨h1, h2⟩
      have : (y : G) ∈ hyp.Q1 ⊓ (A' ⊔ B') := ⟨h2, h1⟩
      rwa [hyp.Q1_inf_sup_eq hA' hB'] at this
    · intro h
      exact ⟨Subgroup.mem_sup_right h, hB' h⟩
  have hstep : ((A' ⊔ B').subgroupOf hyp.H).relIndex ((A' ⊔ hyp.Q1).subgroupOf hyp.H)
      = Nat.card (↥hyp.Q1 ⧸ B'.subgroupOf hyp.Q1) := by
    rw [← hsup, Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hinf,
      Subgroup.relIndex_subgroupOf (hyp.Q1_le_Q.trans hyp.Q_le_H)]
    exact Subgroup.index_eq_card _
  -- bridge: `[Q-in : (A'⊔Q₁)-in] = |S⧸A'|`
  have hbridge : ((A' ⊔ hyp.Q1).subgroupOf hyp.H).relIndex (hyp.Q.subgroupOf hyp.H)
      = Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) := by
    have hsup' : (A' ⊔ hyp.Q1).subgroupOf hyp.H
        = (A'.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H) :=
      (Subgroup.subgroupOf_sup (hA'.trans hyp.S_le_H)
        (hyp.Q1_le_Q.trans hyp.Q_le_H)).symm ▸ rfl
    have ht : ((A' ⊔ hyp.Q1).subgroupOf hyp.H).relIndex (hyp.Q.subgroupOf hyp.H)
        * (hyp.Q.subgroupOf hyp.H).index
        = ((A' ⊔ hyp.Q1).subgroupOf hyp.H).index :=
      Subgroup.relIndex_mul_index hle₂
    rw [hyp.index_Q_subgroupOf_eq_d, Subgroup.index_eq_card] at ht
    have hcard : Nat.card (↥hyp.H ⧸ (A' ⊔ hyp.Q1).subgroupOf hyp.H)
        = hyp.d * Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) := by
      rw [Subgroup.subgroupOf_sup (hA'.trans hyp.S_le_H)
        (hyp.Q1_le_Q.trans hyp.Q_le_H)]
      exact hyp.card_quot_sup_Q1_eq_d_mul hA'
    rw [hcard] at ht
    exact Nat.eq_of_mul_eq_mul_right hyp.d_pos (by rw [ht]; ring)
  -- assemble via relIndex multiplicativity
  have hmul := Subgroup.relIndex_mul_relIndex
    ((A' ⊔ B').subgroupOf hyp.H) ((A' ⊔ hyp.Q1).subgroupOf hyp.H)
    (hyp.Q.subgroupOf hyp.H) hle₁ hle₂
  rw [hstep, hbridge] at hmul
  exact hmul.symm.trans (mul_comm _ _)

/-! ## The centre lift `Z(Q₁)` and its `2d+1` bound (p. 147) -/

/-- **The lift of the centre `Z(Q₁)`** to a subgroup of `G`: `centralLiftIn`
at `Q₃ = ⊥`. -/
def centerLiftQ1 : Subgroup G :=
  hyp.centralLiftIn hyp.Q1 ⊥ fun _ _ x hx => by
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx]
    group

theorem centerLiftQ1_le : hyp.centerLiftQ1 ≤ hyp.Q1 :=
  hyp.centralLiftIn_le hyp.Q1 _

theorem commutator_eq_one_of_mem_centerLiftQ1 {b : G} (hb : b ∈ hyp.centerLiftQ1)
    {y : G} (hy : y ∈ hyp.Q1) : ⁅b, y⁆ = 1 :=
  Subgroup.mem_bot.mp (hb.2 y hy)

theorem centerLiftQ1_conj_mem_of_mem_H [Finite G] {h : G} (hh : h ∈ hyp.H)
    {z : G} (hz : z ∈ hyp.centerLiftQ1) : h * z * h⁻¹ ∈ hyp.centerLiftQ1 :=
  hyp.centralLiftIn_conj_mem_of_mem_H hyp.Q1 _
    (fun _ _ x hx => by
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx]
      group)
    (fun _ hh' x hx => hyp.Q1_normal_in_H hh' hx) hh hz

/-- **`Z(Q₁) ≠ 1`**: `Q₁` is nontrivial (the trivial group would be a
`2`-group, against `Q1_not_two_group`), so its centre is nontrivial by
nilpotency (`Group.IsNilpotent.center_ne_bot`). -/
theorem centerLiftQ1_ne_bot [Finite G] (hnil : Group.IsNilpotent ↥hyp.Q1) :
    hyp.centerLiftQ1 ≠ ⊥ := by
  haveI := hnil
  haveI : Nontrivial ↥hyp.Q1 := by
    by_contra hcon
    apply hyp.Q1_not_two_group
    haveI : Subsingleton ↥hyp.Q1 := not_nontrivial_iff_subsingleton.mp hcon
    exact fun g => ⟨0, by rw [pow_zero, pow_one]; exact Subsingleton.elim g 1⟩
  have hcne := Group.IsNilpotent.center_ne_bot (G := ↥hyp.Q1)
  obtain ⟨x, hxC, hxb⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hcne)
  intro hbot
  have hmem : (x : G) ∈ hyp.centerLiftQ1 := by
    refine ⟨x.2, fun y hy => ?_⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hc := Subgroup.mem_center_iff.mp hxC ⟨y, hy⟩
    exact congrArg Subtype.val hc.symm
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hxb (by rw [show x = 1 from Subtype.ext hmem]; exact Subgroup.one_mem ⊥)

/-- **`|Z(Q₁)| ≥ 2d+1`** (p. 147, "`d` odd + f.p.f. ⟹ `|Z(Q₁)| ≥ 2d+1`"):
the centre lift is a nontrivial `D`-invariant odd-order subgroup of `Q₁`,
so `two_mul_d_add_one_le_card_of_le_Q1` applies. -/
theorem two_mul_d_add_one_le_card_centerLiftQ1 [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1)) (hnil : Group.IsNilpotent ↥hyp.Q1) :
    2 * hyp.d + 1 ≤ Nat.card ↥hyp.centerLiftQ1 := by
  refine hyp.two_mul_d_add_one_le_card_of_le_Q1 hd hyp.centerLiftQ1_le
    (fun δ hδ z hz => hyp.centerLiftQ1_conj_mem_of_mem_H (hyp.D_le_H hδ) hz)
    (hyp.centerLiftQ1_ne_bot hnil) ?_
  rcases Nat.even_or_odd (Nat.card ↥hyp.centerLiftQ1) with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := he.two_dvd.trans (Subgroup.card_dvd_of_le hyp.centerLiftQ1_le)
    exact (Nat.not_even_iff_odd.mpr hQ1odd) ⟨k, by omega⟩
  · exact ho

/-! ## The central-pair commutator split (p. 147) -/

/-- **The central-pair split**: `⁅x, q⁆ ∈ S₂` for `x ∈ A'·B'` and `q ∈ Q`,
where `A' ≤ S` commutes into `S₂` against `S` and `B' ≤ Q₁` is central in
`Q₁`.  In reduction (2) this is `A' = Z` (the lift of `Z(S/S₂)`) and
`B' = Z(Q₁)`, showing `Z·Z(Q₁)` maps into the centre of `Q⧸S₂` — the
`hcentral` input of `exists_deg_sq_le_of_mem_SsetOf` via
`map_mk_le_center_of_commutator_mem`.  Mirror of
`commutator_mem_sup_Sder_of_central` with the two factors' roles swapped. -/
theorem commutator_mem_of_central_pair {S₂ A' B' : Subgroup G}
    (hA'S : A' ≤ hyp.S) (hB'Q1 : B' ≤ hyp.Q1)
    (hA'c : ∀ a ∈ A', ∀ s ∈ hyp.S, ⁅a, s⁆ ∈ S₂)
    (hB'c : ∀ b ∈ B', ∀ y ∈ hyp.Q1, ⁅b, y⁆ = 1)
    {x q : G} (hx : x ∈ A' ⊔ B') (hq : q ∈ hyp.Q) :
    ⁅x, q⁆ ∈ S₂ := by
  -- decompose `x = a·b` along `A' ⊔ B' = A'·B'`
  have hnorm : A' ≤ Subgroup.normalizer (B' : Set G) :=
    hyp.le_normalizer_of_le_S_of_le_Q1 hA'S hB'Q1
  have hxmul : x ∈ (A' : Set G) * (B' : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A' B' hnorm]
    exact hx
  obtain ⟨a, ha, b, hb, hxeq⟩ := hxmul
  -- decompose `q = s₁·y₁` along `Q = S·Q₁`
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hq
  obtain ⟨s₁, hs₁, y₁, hy₁, hqeq⟩ := hq
  -- the commutator splits into the `S`- and `Q₁`-commutators
  have hc1 : Commute b s₁ := (hyp.S_commutes_Q1 s₁ hs₁ b (hB'Q1 hb)).symm
  have hc2 : Commute a⁻¹ y₁⁻¹ :=
    hyp.S_commutes_Q1 a⁻¹ (hyp.S.inv_mem (hA'S ha)) y₁⁻¹ (hyp.Q1.inv_mem hy₁)
  have hw : b * y₁ * (b⁻¹ * y₁⁻¹) ∈ hyp.Q1 :=
    hyp.Q1.mul_mem (hyp.Q1.mul_mem (hB'Q1 hb) hy₁)
      (hyp.Q1.mul_mem (hyp.Q1.inv_mem (hB'Q1 hb)) (hyp.Q1.inv_mem hy₁))
  have hc3 : (a⁻¹ * s₁⁻¹) * (b * y₁ * (b⁻¹ * y₁⁻¹))
      = (b * y₁ * (b⁻¹ * y₁⁻¹)) * (a⁻¹ * s₁⁻¹) :=
    hyp.S_commutes_Q1 _ (hyp.S.mul_mem (hyp.S.inv_mem (hA'S ha))
      (hyp.S.inv_mem hs₁)) _ hw
  have hkey : ⁅x, q⁆ = ⁅a, s₁⁆ * ⁅b, y₁⁆ := by
    calc ⁅x, q⁆
        = (a * b) * (s₁ * y₁) * ((b⁻¹ * a⁻¹) * (y₁⁻¹ * s₁⁻¹)) := by
          rw [← hxeq, ← hqeq, commutatorElement_def]; group
      _ = (a * s₁) * (b * y₁) * ((b⁻¹ * y₁⁻¹) * (a⁻¹ * s₁⁻¹)) := by
          rw [hc1.mul_mul_mul_comm, hc2.mul_mul_mul_comm]
      _ = (a * s₁) * ((b * y₁ * (b⁻¹ * y₁⁻¹)) * (a⁻¹ * s₁⁻¹)) := by group
      _ = (a * s₁) * ((a⁻¹ * s₁⁻¹) * (b * y₁ * (b⁻¹ * y₁⁻¹))) := by rw [hc3]
      _ = ⁅a, s₁⁆ * ⁅b, y₁⁆ := by
          rw [commutatorElement_def, commutatorElement_def]; group
  rw [hkey, hB'c b hb y₁ hy₁, mul_one]
  exact hA'c a ha s₁ hs₁

/-! ## The reduction (2) closing arithmetic -/

/-- **The reduction (2) final arithmetic** (p. 147): the counting bound
`m(q₁−1) ≤ 2da`, the degree bound `a² ≤ m·qz`, the tower `q₁ = qz·zc`, the
`d`-odd fixed-point-free bound `zc ≥ 2d+1` on the centre, and `m ≥ 2`
(`S₁ ≤ [S,S] ⊊ S`) are jointly contradictory:
`m·zc·(q₁−2) < 4d²` while `m·zc·(q₁−2) ≥ 2(2d+1)(2d−1) = 8d²−2 ≥ 4d²`. -/
theorem false_of_reduction_two_bounds {d a m q₁ qz zc : ℕ}
    (hd : 1 ≤ d) (hqz : 0 < qz)
    (h1 : (m : ℝ) * ((q₁ : ℝ) - 1) ≤ (d : ℝ) * (2 * a))
    (h2 : a ^ 2 ≤ m * qz)
    (h3 : q₁ = qz * zc)
    (h4 : 2 * d + 1 ≤ zc)
    (h5 : 2 ≤ m) : False := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2R : (a : ℝ) ^ 2 ≤ (m : ℝ) * (qz : ℝ) := by exact_mod_cast h2
  have h3R : (q₁ : ℝ) = (qz : ℝ) * (zc : ℝ) := by exact_mod_cast h3
  have h4R : 2 * (d : ℝ) + 1 ≤ (zc : ℝ) := by exact_mod_cast h4
  have h5R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h5
  have hqzR : (1 : ℝ) ≤ (qz : ℝ) := by exact_mod_cast hqz
  have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  -- `zc ≤ q₁` and `q₁ ≥ 3`
  have hzc0 : (0 : ℝ) ≤ (zc : ℝ) := Nat.cast_nonneg zc
  have hzcq₁ : (zc : ℝ) ≤ (q₁ : ℝ) := by
    rw [h3R]
    have hmul := mul_le_mul_of_nonneg_right hqzR hzc0
    linarith
  have hq₁3 : (3 : ℝ) ≤ (q₁ : ℝ) := by linarith
  -- `m²(q₁−1)² ≤ 4d²·m·qz` ⟹ `m·zc·(q₁−1)² ≤ 4d²·q₁`
  have k1 : (m : ℝ) ^ 2 * ((q₁ : ℝ) - 1) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * ((m : ℝ) * (qz : ℝ)) := by
    nlinarith [mul_le_mul h1 h1 (by nlinarith) (by positivity)]
  have k2 : (m : ℝ) * ((q₁ : ℝ) - 1) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (qz : ℝ) := by
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have := k1
    nlinarith [this, hm0]
  have k3 : (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) - 1) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (q₁ : ℝ) := by
    have hzc0 : (0 : ℝ) < (zc : ℝ) := by linarith
    calc (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) - 1) ^ 2
        = (zc : ℝ) * ((m : ℝ) * ((q₁ : ℝ) - 1) ^ 2) := by ring
      _ ≤ (zc : ℝ) * (4 * (d : ℝ) ^ 2 * (qz : ℝ)) :=
          mul_le_mul_of_nonneg_left k2 hzc0.le
      _ = 4 * (d : ℝ) ^ 2 * ((qz : ℝ) * (zc : ℝ)) := by ring
      _ = 4 * (d : ℝ) ^ 2 * (q₁ : ℝ) := by rw [← h3R]
  -- strict drop to `m·zc·(q₁−2) < 4d²`
  have k4 : (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) - 2) < 4 * (d : ℝ) ^ 2 := by
    have hmzc0 : (0 : ℝ) < (m : ℝ) * (zc : ℝ) := by nlinarith
    have hq₁0 : (0 : ℝ) < (q₁ : ℝ) := by linarith
    have hstrict : (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) * ((q₁ : ℝ) - 2))
        < (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) - 1) ^ 2 := by
      apply mul_lt_mul_of_pos_left _ hmzc0
      nlinarith
    have k5 : (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) - 2) * (q₁ : ℝ)
        < 4 * (d : ℝ) ^ 2 * (q₁ : ℝ) := by
      nlinarith [hstrict, k3]
    exact lt_of_mul_lt_mul_right k5 hq₁0.le
  -- lower bound `m·zc·(q₁−2) ≥ 2(2d+1)(2d−1) ≥ 4d²`
  have k6 : 2 * ((2 * (d : ℝ) + 1) * (2 * (d : ℝ) - 1))
      ≤ (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) - 2) := by
    have hgap : 2 * (d : ℝ) - 1 ≤ (q₁ : ℝ) - 2 := by linarith
    have hpos1 : (0 : ℝ) ≤ 2 * (d : ℝ) - 1 := by linarith
    have s1 : (2 * (d : ℝ) + 1) * (2 * (d : ℝ) - 1) ≤ (zc : ℝ) * ((q₁ : ℝ) - 2) :=
      mul_le_mul h4R hgap hpos1 hzc0
    have s2 : 2 * ((2 * (d : ℝ) + 1) * (2 * (d : ℝ) - 1))
        ≤ (m : ℝ) * ((zc : ℝ) * ((q₁ : ℝ) - 2)) :=
      mul_le_mul h5R s1 (mul_nonneg (by linarith) hpos1) (by linarith)
    calc 2 * ((2 * (d : ℝ) + 1) * (2 * (d : ℝ) - 1))
        ≤ (m : ℝ) * ((zc : ℝ) * ((q₁ : ℝ) - 2)) := s2
      _ = (m : ℝ) * (zc : ℝ) * ((q₁ : ℝ) - 2) := by ring
  nlinarith [k4, k6]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
