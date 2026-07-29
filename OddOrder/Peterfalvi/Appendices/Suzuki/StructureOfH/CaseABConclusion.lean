/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.CaseBStructure
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionNonSimple
import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreePSL

/-!
# Cases (a) and (b) of Ch. III §1 give the conclusion of Theorem A

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §3, p. 119:

> Assume that case (a) or (b) of the proposition in §1 holds.  Then
> `G₀ = (SK) ∪ (SKtS)` is a subgroup of `G` (§2 and Chapter I, §3, Lemma 4).
> Also, `G = H ∪ (HtS) = ⟨G₀, V⟩` and `V` normalizes `S`, `K` and `t` whence
> `G₀ ⊴ G` and `|G/G₀| = |V|`.  The conclusion of Theorem A now follows from
> Chapter I, §3, Proposition 2.

So cases (a) and (b) are disposed of and §3 may assume (C2): `S` of type B,
`st` of order `3`, `W ≠ 1`.

Both cases enter through the *same* carrier `(SK) ∪ (SKtS)`
(`Hypothesis.orderFiveCarrier`) — case (b) by the Proposition of §2
(`typeASubgroup`) and case (a), where `S = Q₀`, by Ch. I §3 Lemma 4
(`orderThreeGeneratedSubgroup`) — so the argument is stated once, for an
arbitrary subgroup with that carrier.

## Main results

* `Hypothesis.orderFiveCarrier_sup_V_eq_top` — `G = ⟨G₀, V⟩`.
* `Hypothesis.normal_of_orderFiveCarrier` — `G₀ ⊴ G`.
* `Hypothesis.eq_one_of_mem_V_of_mem_orderFiveCarrier` — `G₀ ∩ V = 1`.
* `Hypothesis.theoremAConclusion_of_orderFiveCarrier_subgroup` — the
  conclusion of Theorem A.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

lemma mem_orderFiveCarrier_of_mem_Q {q : G} (hq : q ∈ hyp.Q) :
    q ∈ hyp.orderFiveCarrier :=
  Or.inl ⟨q, hq, 1, hyp.K.one_mem, (mul_one q).symm⟩

lemma mem_orderFiveCarrier_of_mem_K {k : G} (hk : k ∈ hyp.K) :
    k ∈ hyp.orderFiveCarrier :=
  Or.inl ⟨1, hyp.Q.one_mem, k, hk, (one_mul k).symm⟩

lemma t_mem_orderFiveCarrier : hyp.t ∈ hyp.orderFiveCarrier :=
  Or.inr ⟨1, hyp.Q.one_mem, 1, hyp.K.one_mem, 1, hyp.Q.one_mem, by group⟩

/-- **`V` normalizes `(SK) ∪ (SKtS)`** (Peterfalvi Part II, Ch. III §3,
p. 119): `V ≤ D` normalizes `S` and `K`, and centralizes `t`. -/
lemma conj_mem_orderFiveCarrier_of_mem_V {v : G} (hv : v ∈ hyp.V) {g : G}
    (hg : g ∈ hyp.orderFiveCarrier) : v * g * v⁻¹ ∈ hyp.orderFiveCarrier := by
  have hvD : v ∈ hyp.D := hyp.V_le_D hv
  have hvH : v ∈ hyp.H := hyp.D_le_H hvD
  have hvt : v * hyp.t * v⁻¹ = hyp.t := by
    rw [hyp.commute_t_of_mem_V hv]; group
  rcases hg with ⟨q, hq, k, hk, rfl⟩ | ⟨q, hq, k, hk, q', hq', rfl⟩
  · exact Or.inl ⟨v * q * v⁻¹, hyp.Q_normal_in_H v hvH q hq, v * k * v⁻¹,
      hyp.conj_mem_K_of_mem_D hvD hk, by group⟩
  · refine Or.inr ⟨v * q * v⁻¹, hyp.Q_normal_in_H v hvH q hq, v * k * v⁻¹,
      hyp.conj_mem_K_of_mem_D hvD hk, v * q' * v⁻¹,
      hyp.Q_normal_in_H v hvH q' hq', ?_⟩
    calc v * (q * k * hyp.t * q') * v⁻¹
        = (v * q * v⁻¹) * (v * k * v⁻¹) * (v * hyp.t * v⁻¹) * (v * q' * v⁻¹) := by
          group
      _ = v * q * v⁻¹ * (v * k * v⁻¹) * hyp.t * (v * q' * v⁻¹) := by rw [hvt]

section Carrier

variable {G₀ : Subgroup G} (hG₀ : (G₀ : Set G) = hyp.orderFiveCarrier)

include hG₀

lemma mem_carrier_iff (x : G) : x ∈ G₀ ↔ x ∈ hyp.orderFiveCarrier := by
  rw [← SetLike.mem_coe, hG₀]

lemma Q_le_of_orderFiveCarrier : hyp.Q ≤ G₀ := fun _ hq =>
  (hyp.mem_carrier_iff hG₀ _).mpr (hyp.mem_orderFiveCarrier_of_mem_Q hq)

lemma K_le_of_orderFiveCarrier : hyp.K ≤ G₀ := fun _ hk =>
  (hyp.mem_carrier_iff hG₀ _).mpr (hyp.mem_orderFiveCarrier_of_mem_K hk)

lemma t_mem_of_orderFiveCarrier : hyp.t ∈ G₀ :=
  (hyp.mem_carrier_iff hG₀ _).mpr hyp.t_mem_orderFiveCarrier

/-- `H ≤ ⟨G₀, V⟩`: `H = Q·D` and `D = V ⊔ K`. -/
lemma H_le_orderFiveCarrier_sup_V : hyp.H ≤ G₀ ⊔ hyp.V := by
  intro x hx
  have hxQD : x ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
    rw [hyp.Q_mul_D_eq_H]; exact hx
  obtain ⟨q, hq, d, hd, rfl⟩ := hxQD
  have hdVK : d ∈ hyp.V ⊔ hyp.K := by rw [hyp.V_sup_K_eq_D]; exact hd
  refine (G₀ ⊔ hyp.V).mul_mem ?_ ?_
  · exact (le_sup_left : G₀ ≤ G₀ ⊔ hyp.V) (hyp.Q_le_of_orderFiveCarrier hG₀ hq)
  · exact sup_le (le_sup_right : hyp.V ≤ G₀ ⊔ hyp.V)
      ((hyp.K_le_of_orderFiveCarrier hG₀).trans le_sup_left) hdVK

/-- **`G = ⟨G₀, V⟩`** (Peterfalvi Part II, Ch. III §3, p. 119): `G = H ∪ HtS`
and `H ≤ ⟨G₀, V⟩`, while `t` and `S` lie in `G₀`. -/
theorem orderFiveCarrier_sup_V_eq_top : G₀ ⊔ hyp.V = ⊤ := by
  rw [eq_top_iff]
  intro g _
  by_cases hg : g ∈ hyp.H
  · exact hyp.H_le_orderFiveCarrier_sup_V hG₀ hg
  · obtain ⟨x, hx, y, hy, rfl⟩ := hyp.exists_canonicalForm hg
    refine (G₀ ⊔ hyp.V).mul_mem ((G₀ ⊔ hyp.V).mul_mem
      (hyp.H_le_orderFiveCarrier_sup_V hG₀ hx) ?_) ?_
    · exact (le_sup_left : G₀ ≤ G₀ ⊔ hyp.V) (hyp.t_mem_of_orderFiveCarrier hG₀)
    · exact (le_sup_left : G₀ ≤ G₀ ⊔ hyp.V) (hyp.Q_le_of_orderFiveCarrier hG₀ hy)

/-- **`G₀ ⊴ G`** (Peterfalvi Part II, Ch. III §3, p. 119): the normalizer
contains `G₀` and `V`, hence `⟨G₀, V⟩ = G`. -/
theorem normal_of_orderFiveCarrier : G₀.Normal := by
  refine Subgroup.normalizer_eq_top_iff.mp ?_
  rw [eq_top_iff, ← hyp.orderFiveCarrier_sup_V_eq_top hG₀]
  refine sup_le Subgroup.le_normalizer fun v hv => ?_
  have hconj : ∀ w ∈ hyp.V, ∀ n : G, n ∈ G₀ → w * n * w⁻¹ ∈ G₀ :=
    fun w hw n hn => (hyp.mem_carrier_iff hG₀ _).mpr
      (hyp.conj_mem_orderFiveCarrier_of_mem_V hw ((hyp.mem_carrier_iff hG₀ n).mp hn))
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨hconj v hv n, fun h => ?_⟩
  have hback := hconj v⁻¹ (hyp.V.inv_mem hv) _ h
  have heq : v⁻¹ * (v * n * v⁻¹) * (v⁻¹)⁻¹ = n := by group
  rwa [heq] at hback

/-- **`G₀ ∩ V = 1`** (Peterfalvi Part II, Ch. III §3, p. 119, the source of
`|G/G₀| = |V|`).  The big cell misses `H ⊇ V` because `t ∉ H`, and on the
small cell `S ∩ D = 1` and `K ∩ V = 1`. -/
theorem eq_one_of_mem_V_of_mem_orderFiveCarrier {v : G} (hv : v ∈ hyp.V)
    (hvG : v ∈ G₀) : v = 1 := by
  have hvD : v ∈ hyp.D := hyp.V_le_D hv
  rcases (hyp.mem_carrier_iff hG₀ v).mp hvG with
    ⟨q, hq, k, hk, rfl⟩ | ⟨q, hq, k, hk, q', hq', rfl⟩
  · have hkD : k ∈ hyp.D := hyp.K_le_D hk
    have hqD : q ∈ hyp.D := by
      have hrw : q = (q * k) * k⁻¹ := by group
      rw [hrw]
      exact hyp.D.mul_mem hvD (hyp.D.inv_mem hkD)
    have hqbot : q ∈ hyp.Q ⊓ hyp.D := ⟨hq, hqD⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hqbot
    have hkV : k ∈ hyp.K ⊓ hyp.V := ⟨hk, by rwa [hqbot, one_mul] at hv⟩
    rw [hyp.K_inf_V_eq_bot, Subgroup.mem_bot] at hkV
    rw [hqbot, hkV, one_mul]
  · exfalso
    refine hyp.t_not_mem_H ?_
    have hvH : q * k * hyp.t * q' ∈ hyp.H := hyp.D_le_H hvD
    have hqH : q ∈ hyp.H := hyp.Q_le_H hq
    have hkH : k ∈ hyp.H := hyp.D_le_H (hyp.K_le_D hk)
    have hq'H : q' ∈ hyp.H := hyp.Q_le_H hq'
    have hrw : hyp.t = (q * k)⁻¹ * (q * k * hyp.t * q') * q'⁻¹ := by group
    rw [hrw]
    exact hyp.H.mul_mem (hyp.H.mul_mem (hyp.H.inv_mem (hyp.H.mul_mem hqH hkH)) hvH)
      (hyp.H.inv_mem hq'H)

/-- **The conclusion of Theorem A in cases (a) and (b)** (Peterfalvi Part II,
Ch. III §3, p. 119).

`G₀ = (SK) ∪ (SKtS)` is normal in `G` with `G₀ ∩ V = 1`, so `V ≠ 1` makes it a
proper non-trivial normal subgroup; `G` is therefore not simple and Ch. I §3
Proposition 2 applies. -/
theorem theoremAConclusion_of_orderFiveCarrier_subgroup (hV : hyp.V ≠ ⊥)
    (ind : TheoremAInductionBelow G Ω) : Nonempty (TheoremAConclusion G Ω) := by
  have hnorm := hyp.normal_of_orderFiveCarrier hG₀
  haveI := hnorm
  have hne : G₀ ≠ ⊤ := by
    intro htop
    refine hV (eq_bot_iff.mpr fun v hv => Subgroup.mem_bot.mpr ?_)
    exact hyp.eq_one_of_mem_V_of_mem_orderFiveCarrier hG₀ hv (htop ▸ Subgroup.mem_top v)
  have hbot : G₀ ≠ ⊥ := by
    intro hb
    refine hyp.distinguishedInvolution_ne_one ?_
    have := hyp.Q_le_of_orderFiveCarrier hG₀ hyp.distinguishedInvolution_mem_Q
    rwa [hb, Subgroup.mem_bot] at this
  refine hyp.theoremAConclusion_of_not_simple (fun hsimple => ?_) ind
  rcases hsimple.eq_bot_or_eq_top_of_normal G₀ hnorm with h | h
  · exact hbot h
  · exact hne h

end Carrier

/-! ## The two cases -/

/-- **Case (b)** of the Proposition of §1: the subgroup is the one built in §2
(`typeASubgroup`). -/
theorem theoremAConclusion_of_caseB
    (hA : Suzuki2Groups.IsTypeA.{u, 0} ↥hyp.Q)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5)
    (hV : hyp.V ≠ ⊥) (ind : TheoremAInductionBelow G Ω) :
    Nonempty (TheoremAConclusion G Ω) :=
  hyp.theoremAConclusion_of_orderFiveCarrier_subgroup
    (hyp.coe_typeASubgroup hA hQcard h5) hV ind

/-- In case (a) of the Proposition of §1 — where `S = Q₀` — the subgroup
`⟨Q₀, K, t⟩` of Ch. I §3 Lemma 4 has carrier `(SK) ∪ (SKtS)`. -/
theorem coe_orderThreeGeneratedSubgroup_eq_orderFiveCarrier
    (h3 : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hQ : hyp.Q = hyp.Q0) :
    (hyp.orderThreeGeneratedSubgroup : Set G) = hyp.orderFiveCarrier := by
  rw [hyp.coe_orderThreeGeneratedSubgroup_eq_Q0K_union_Q0KtQ0 h3, ← hQ]
  ext g
  simp only [orderFiveCarrier, Set.mem_union, Set.mem_mul, Set.mem_singleton_iff,
    Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro (⟨q, hq, k, hk, rfl⟩ |
      ⟨-, ⟨-, ⟨q, hq, k, hk, rfl⟩, -, rfl, rfl⟩, q', hq', rfl⟩)
    · exact Or.inl ⟨q, hq, k, hk, rfl⟩
    · exact Or.inr ⟨q, hq, k, hk, q', hq', rfl⟩
  · rintro (⟨q, hq, k, hk, rfl⟩ | ⟨q, hq, k, hk, q', hq', rfl⟩)
    · exact Or.inl ⟨q, hq, k, hk, rfl⟩
    · exact Or.inr ⟨_, ⟨_, ⟨q, hq, k, hk, rfl⟩, _, rfl, rfl⟩, q', hq', rfl⟩

/-- **Case (a)** of the Proposition of §1: `S = Q₀`, `st` of order `3`, and the
subgroup is `⟨Q₀, K, t⟩` (Ch. I §3 Lemma 4). -/
theorem theoremAConclusion_of_caseA
    (hQ : hyp.Q = hyp.Q0)
    (h3 : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hV : hyp.V ≠ ⊥) (ind : TheoremAInductionBelow G Ω) :
    Nonempty (TheoremAConclusion G Ω) :=
  hyp.theoremAConclusion_of_orderFiveCarrier_subgroup
    (hyp.coe_orderThreeGeneratedSubgroup_eq_orderFiveCarrier h3 hQ) hV ind

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
