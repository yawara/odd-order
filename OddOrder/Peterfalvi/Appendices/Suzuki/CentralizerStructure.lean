/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.InvertedProduct
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-!
# Peterfalvi Part II, Ch. I §1: Proposition 5 (`V = C_D(s)`, `W = C_D(H∩I)`)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §1, p. 101.

Proposition 5: `V = C_D(s)` and `W = C_D(H ∩ I)`, where `s` is the
distinguished involution (Prop 4(b)).

The inclusion `V ⊆ C_D(s)` follows from the uniqueness of the distinguished
pair `(s, r)` (conjugating the structure equation by `v ∈ V` gives another
valid pair `(sᵛ, rᵛ)`, hence `sᵛ = s`).  Equality then follows by counting:
`|D:V| = |K|` (the Lemma (a) applied to `(D, t)`), `|K| = |H∩I|` (Prop 3), and
`|H∩I| = |sᴰ| = |D:C_D(s)|` (orbit–stabilizer for `D` acting on `s` by
conjugation, `sᴰ = H∩I`).
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

open scoped Pointwise

/-! ## `V ⊆ C_D(s)` (p. 101) -/

/-- **Peterfalvi Part II, Ch. I Prop 5** (p. 101), first inclusion —
`V ⊆ C_D(s)`.  For `v ∈ V = C_D(t)`, conjugating the structure equation
`tst = r⁻¹tr` by `v` yields `t sᵛ t = (rᵛ)⁻¹ t rᵛ`; the pair `(sᵛ, rᵛ)`
satisfies the defining conditions, so by uniqueness `sᵛ = s`, i.e. `v`
centralizes `s`. -/
theorem V_le_centralizer_distinguishedInvolution :
    hyp.V ≤ hyp.D ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} := by
  intro v hv
  have hvD : v ∈ hyp.D := hyp.V_le_D hv
  have hvH : v ∈ hyp.H := hyp.D_le_H hvD
  have hvt : Commute v hyp.t := hyp.commute_t_of_mem_V hv
  have hv't : v⁻¹ * hyp.t = hyp.t * v⁻¹ := hvt.inv_left.eq
  have hvtv : v⁻¹ * hyp.t * v = hyp.t := by
    rw [mul_assoc, ← hvt.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  set s := hyp.distinguishedInvolution with hs
  set r := hyp.structureConjugator with hr
  have hsH : s ∈ hyp.H := hyp.distinguishedInvolution_mem_H
  have hs2 : s ^ 2 = 1 := hyp.distinguishedInvolution_sq
  have hs1 : s ≠ 1 := hyp.distinguishedInvolution_ne_one
  have hrQ : r ∈ hyp.Q := hyp.structureConjugator_mem_Q
  have hstr : hyp.t * s * hyp.t = r⁻¹ * hyp.t * r := hyp.structure_equation
  -- conjugated structure equation
  have hconj : hyp.t * (v⁻¹ * s * v) * hyp.t
      = (v⁻¹ * r * v)⁻¹ * hyp.t * (v⁻¹ * r * v) := by
    calc hyp.t * (v⁻¹ * s * v) * hyp.t
        = (hyp.t * v⁻¹) * s * (v * hyp.t) := by group
      _ = (v⁻¹ * hyp.t) * s * (hyp.t * v) := by rw [← hv't, hvt.eq]
      _ = v⁻¹ * (hyp.t * s * hyp.t) * v := by group
      _ = v⁻¹ * (r⁻¹ * hyp.t * r) * v := by rw [hstr]
      _ = (v⁻¹ * r⁻¹ * v) * (v⁻¹ * hyp.t * v) * (v⁻¹ * r * v) := by group
      _ = (v⁻¹ * r⁻¹ * v) * hyp.t * (v⁻¹ * r * v) := by rw [hvtv]
      _ = (v⁻¹ * r * v)⁻¹ * hyp.t * (v⁻¹ * r * v) := by
          have hinv : (v⁻¹ * r * v)⁻¹ = v⁻¹ * r⁻¹ * v := by
            rw [mul_inv_rev, mul_inv_rev, inv_inv]; group
          rw [hinv]
  -- (sᵛ, rᵛ) is a valid pair, so sᵛ = s
  have hsv2 : (v⁻¹ * s * v) ^ 2 = 1 := by
    rw [sq]
    calc (v⁻¹ * s * v) * (v⁻¹ * s * v) = v⁻¹ * (s * s) * v := by group
      _ = 1 := by rw [← sq, hs2]; group
  have hsvne : v⁻¹ * s * v ≠ 1 := by
    intro h
    apply hs1
    have h2 : v * (v⁻¹ * s * v) * v⁻¹ = v * 1 * v⁻¹ := by rw [h]
    rw [show v * (v⁻¹ * s * v) * v⁻¹ = s from by group,
      show v * 1 * v⁻¹ = 1 from by group] at h2
    exact h2
  have hrvQ : v⁻¹ * r * v ∈ hyp.Q := by
    have := hyp.Q_normal_in_H v⁻¹ (inv_mem hvH) r hrQ
    rwa [inv_inv] at this
  obtain ⟨hsv, -⟩ := hyp.eq_distinguishedPair_of_structure
    (mul_mem (mul_mem (inv_mem hvH) hsH) hvH) hsv2 hsvne hrvQ hconj
  -- hsv : v⁻¹ * s * v = s  ⟹  Commute v s
  have hcomm : v * s = s * v := by
    have h2 : v * (v⁻¹ * s * v) = v * s := by rw [hsv]
    rw [show v * (v⁻¹ * s * v) = s * v from by group] at h2
    exact h2.symm
  exact Subgroup.mem_inf.mpr ⟨hvD, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩

/-! ## `V = C_D(s)` (p. 101) -/

/-- `sᴰ = H ∩ I`: the `D`-conjugacy class of the distinguished involution is
exactly the set of involutions of `H` (Prop 2(a)/Prop 3). -/
theorem orbit_distinguishedInvolution_eq
    (act : MulAction (↥hyp.D) G)
    (hsmul : ∀ d : ↥hyp.D, d • hyp.distinguishedInvolution =
      (↑d : G) * hyp.distinguishedInvolution * (↑d : G)⁻¹) :
    MulAction.orbit (↥hyp.D) hyp.distinguishedInvolution =
      {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
  set s := hyp.distinguishedInvolution with hs
  have hsH : s ∈ hyp.H := hyp.distinguishedInvolution_mem_H
  have hs2 : s ^ 2 = 1 := hyp.distinguishedInvolution_sq
  have hs1 : s ≠ 1 := hyp.distinguishedInvolution_ne_one
  ext w
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨d, rfl⟩
    have hdH : (↑d : G) ∈ hyp.H := hyp.D_le_H d.2
    rw [hsmul d]
    refine ⟨?_, ?_, ?_⟩
    · rw [sq]
      calc (↑d * s * (↑d)⁻¹) * (↑d * s * (↑d)⁻¹) = ↑d * (s * s) * (↑d)⁻¹ := by group
        _ = 1 := by rw [← sq, hs2]; group
    · intro h
      apply hs1
      have h2 : (↑d : G)⁻¹ * (↑d * s * (↑d)⁻¹) * ↑d = (↑d : G)⁻¹ * 1 * ↑d := by rw [h]
      rw [show (↑d : G)⁻¹ * (↑d * s * (↑d)⁻¹) * ↑d = s from by group,
        show (↑d : G)⁻¹ * 1 * ↑d = 1 from by group] at h2
      exact h2
    · exact mul_mem (mul_mem hdH hsH) (inv_mem hdH)
  · rintro ⟨hw2, hw1, hwH⟩
    have himg := hyp.image_conj_KSet_eq_involutions_H hsH hs2 hs1
    have hw : w ∈ (fun k : G => k⁻¹ * s * k) '' hyp.KSet := by
      rw [himg]; exact ⟨hw2, hw1, hwH⟩
    obtain ⟨k, hkK, hkw⟩ := hw
    refine ⟨⟨k⁻¹, hyp.D.inv_mem hkK.1⟩, ?_⟩
    rw [hsmul]
    change (k⁻¹ : G) * s * (k⁻¹)⁻¹ = w
    rw [inv_inv]; exact hkw

/-- **Peterfalvi Part II, Ch. I Prop 5** (p. 101) — `V = C_D(s)`.  Combining
`V ⊆ C_D(s)` with `|D| = |V||K|` (Lemma (a)), `|K| = |H∩I|` (Prop 3) and
`|D| = |H∩I|·|C_D(s)|` (orbit–stabilizer, `sᴰ = H∩I`). -/
theorem V_eq_centralizer_distinguishedInvolution :
    hyp.V = hyp.D ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} := by
  classical
  set s := hyp.distinguishedInvolution with hs
  have hsH : s ∈ hyp.H := hyp.distinguishedInvolution_mem_H
  have hs2 : s ^ 2 = 1 := hyp.distinguishedInvolution_sq
  -- the D-conjugation action
  letI act : MulAction (↥hyp.D) G :=
    MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp hyp.D.subtype)
  have hsmul : ∀ d : ↥hyp.D, d • s = (↑d : G) * s * (↑d : G)⁻¹ :=
    fun d => ConjAct.toConjAct_smul _ _
  -- (I) Lemma (a): |D| = |V| * |K|
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  have hnorm : ∀ x ∈ hyp.D, hyp.t * x * hyp.t ∈ hyp.D := by
    intro x hx
    have := hyp.t_conj_mem_D hx
    rwa [hyp.t_inv_eq] at this
  have hLemma : Nat.card ↥hyp.D = Nat.card ↥hyp.V * hyp.KSet.ncard :=
    card_eq_card_centralizer_mul_ncard_invertedBy (X := hyp.D) (t := hyp.t)
      htt hyp.D_odd hnorm
  -- (II) |K| = |H∩I|
  have hKHI : hyp.KSet.ncard = {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard :=
    hyp.ncard_KSet_eq
  -- stabilizer = C_D(s), so |stab| = |C_D(s)|
  have hstab_eq : MulAction.stabilizer (↥hyp.D) s =
      (Subgroup.centralizer {s}).subgroupOf hyp.D := by
    ext d
    rw [MulAction.mem_stabilizer_iff, hsmul d, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hstabcard : Nat.card (MulAction.stabilizer (↥hyp.D) s) =
      Nat.card ↥(hyp.D ⊓ Subgroup.centralizer {s}) := by
    rw [hstab_eq, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  -- (III) orbit = H∩I, so |orbit| = |H∩I|
  have horbit_card : Nat.card (MulAction.orbit (↥hyp.D) s) =
      {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard := by
    rw [hyp.orbit_distinguishedInvolution_eq act hsmul, Nat.card_coe_set_eq]
  -- orbit–stabilizer: |D| = |orbit| * |stab|
  have horbit_index : Nat.card (MulAction.orbit (↥hyp.D) s) =
      (MulAction.stabilizer (↥hyp.D) s).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥hyp.D) s)
  have hcount : Nat.card ↥hyp.D =
      {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard *
        Nat.card ↥(hyp.D ⊓ Subgroup.centralizer {s}) := by
    rw [← horbit_card, ← hstabcard, horbit_index,
      (MulAction.stabilizer (↥hyp.D) s).index_mul_card]
  -- combine: |V| = |C_D(s)|
  have hHIpos : 0 < {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard := by
    apply Set.ncard_pos (Set.toFinite _) |>.mpr
    exact ⟨s, hs2, hyp.distinguishedInvolution_ne_one, hsH⟩
  have hVcard : Nat.card ↥hyp.V = Nat.card ↥(hyp.D ⊓ Subgroup.centralizer {s}) := by
    have h1 : Nat.card ↥hyp.V * {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard
        = Nat.card ↥(hyp.D ⊓ Subgroup.centralizer {s}) *
          {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard := by
      rw [mul_comm (Nat.card ↥(hyp.D ⊓ _)), ← hcount, hLemma, hKHI]
    exact Nat.eq_of_mul_eq_mul_right hHIpos h1
  -- V ⊆ C_D(s) and equal card ⟹ equal
  have hle := hyp.V_le_centralizer_distinguishedInvolution
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hle) ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact le_of_eq hVcard.symm

/-! ## `W = C_D(H ∩ I)` (p. 101) -/

/-- `V` normalizes `K`: for `v ∈ V = C_D(t)` and `k ∈ K`, `vkv⁻¹ ∈ K`
(since `t` centralizes `v`, so `t(vkv⁻¹)t = v k⁻¹ v⁻¹ = (vkv⁻¹)⁻¹`). -/
lemma conj_mem_KSet_of_mem_V {v k : G} (hv : v ∈ hyp.V) (hk : k ∈ hyp.KSet) :
    v * k * v⁻¹ ∈ hyp.KSet := by
  have hvD : v ∈ hyp.D := hyp.V_le_D hv
  have hvt : Commute v hyp.t := hyp.commute_t_of_mem_V hv
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  refine ⟨hyp.D.mul_mem (hyp.D.mul_mem hvD hk.1) (hyp.D.inv_mem hvD), ?_⟩
  have htvt : hyp.t * v * hyp.t = v := by
    calc hyp.t * v * hyp.t = hyp.t * (v * hyp.t) := by rw [mul_assoc]
      _ = hyp.t * (hyp.t * v) := by rw [hvt.eq]
      _ = (hyp.t * hyp.t) * v := by rw [mul_assoc]
      _ = v := by rw [htt, one_mul]
  have htv't : hyp.t * v⁻¹ * hyp.t = v⁻¹ := by
    calc hyp.t * v⁻¹ * hyp.t = hyp.t * (v⁻¹ * hyp.t) := by rw [mul_assoc]
      _ = hyp.t * (hyp.t * v⁻¹) := by rw [hvt.inv_left.eq]
      _ = (hyp.t * hyp.t) * v⁻¹ := by rw [mul_assoc]
      _ = v⁻¹ := by rw [htt, one_mul]
  have hdecomp : hyp.t * (v * k * v⁻¹) * hyp.t
      = (hyp.t * v * hyp.t) * (hyp.t * k * hyp.t) * (hyp.t * v⁻¹ * hyp.t) := by
    have h : (hyp.t * v * hyp.t) * (hyp.t * k * hyp.t) * (hyp.t * v⁻¹ * hyp.t)
        = hyp.t * v * (hyp.t * hyp.t) * k * (hyp.t * hyp.t) * v⁻¹ * hyp.t := by group
    rw [h, htt]; group
  rw [hdecomp, htvt, hk.2, htv't, mul_inv_rev, mul_inv_rev, inv_inv]
  group

/-- **Peterfalvi Part II, Ch. I Prop 5** (p. 101), second clause —
`W = C_D(H ∩ I)`.  `W = C_V(K) = C_D(s) ∩ C_D(K)` (as `V = C_D(s)`), which is
exactly the elements of `D` centralizing `H ∩ I = sᴷ`: the `⊆` direction is a
product computation, and `⊇` uses that an element centralizing `H∩I` lies in
`V = C_D(s)`, hence normalizes `K` and — by injectivity of `k ↦ s^k` (Prop 3)
— centralizes `K`. -/
theorem W_eq_centralizer_involutions_H :
    hyp.W = hyp.D ⊓ Subgroup.centralizer {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
  classical
  set s := hyp.distinguishedInvolution with hs
  have hsH : s ∈ hyp.H := hyp.distinguishedInvolution_mem_H
  have hs2 : s ^ 2 = 1 := hyp.distinguishedInvolution_sq
  have hs1 : s ≠ 1 := hyp.distinguishedInvolution_ne_one
  have hsHI : s ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := ⟨hs2, hs1, hsH⟩
  have hVeq : hyp.V = hyp.D ⊓ Subgroup.centralizer {s} :=
    hyp.V_eq_centralizer_distinguishedInvolution
  have hsurj := hyp.image_conj_KSet_eq_involutions_H hsH hs2 hs1
  have hinj := hyp.injOn_conj_KSet hsH hs2 hs1
  -- `w ∈ V` unfolds to `w ∈ D` and `Commute w s`
  have hV_commute : ∀ {w : G}, w ∈ hyp.V → Commute w s := fun {w} hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hVeq ▸ hw)).2
  ext w
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hw
    obtain ⟨hwV, hwKc⟩ := Subgroup.mem_inf.mp hw
    have hwK := Subgroup.mem_centralizer_iff.mp hwKc
    have hcws : Commute w s := hV_commute hwV
    refine ⟨hyp.V_le_D hwV, ?_⟩
    intro x hx
    rw [← hsurj] at hx
    obtain ⟨k, hkK, hkx⟩ := hx
    rw [← hkx]
    have hck : Commute w k := (hwK k hkK).symm
    have hc : Commute w (k⁻¹ * s * k) :=
      ((hck.inv_right).mul_right hcws).mul_right hck
    exact hc.symm.eq
  · intro hw
    obtain ⟨hwD, hwHI⟩ := hw
    have hcws : Commute w s := (hwHI s hsHI).symm
    have hwV : w ∈ hyp.V := by
      rw [hVeq]
      exact Subgroup.mem_inf.mpr ⟨hwD, Subgroup.mem_centralizer_singleton_iff.mpr hcws⟩
    refine Subgroup.mem_inf.mpr ⟨hwV, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro k hkK
    -- `k' = wkw⁻¹ ∈ K` and `s^{k'} = s^k`, so injectivity gives `wkw⁻¹ = k`
    have hk'K : w * k * w⁻¹ ∈ hyp.KSet := hyp.conj_mem_KSet_of_mem_V hwV hkK
    have hwsw : w⁻¹ * s * w = s := by
      rw [hcws.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
    have hskmem : k⁻¹ * s * k ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
      rw [← hsurj]; exact ⟨k, hkK, rfl⟩
    have hcomm_sk : (k⁻¹ * s * k) * w = w * (k⁻¹ * s * k) := hwHI _ hskmem
    have hs_eq : (w * k * w⁻¹)⁻¹ * s * (w * k * w⁻¹) = k⁻¹ * s * k := by
      calc (w * k * w⁻¹)⁻¹ * s * (w * k * w⁻¹)
          = w * k⁻¹ * (w⁻¹ * s * w) * k * w⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, inv_inv]; group
        _ = w * k⁻¹ * s * k * w⁻¹ := by rw [hwsw]
        _ = w * (k⁻¹ * s * k) * w⁻¹ := by group
        _ = k⁻¹ * s * k := by rw [← hcomm_sk]; group
    have hk'k : w * k * w⁻¹ = k := hinj hk'K hkK hs_eq
    have hwk : w * k = k * w := by
      calc w * k = w * k * (w⁻¹ * w) := by rw [inv_mul_cancel, mul_one]
        _ = (w * k * w⁻¹) * w := by group
        _ = k * w := by rw [hk'k]
    exact hwk.symm

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
