/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure
import OddOrder.Peterfalvi.Appendices.Huppert
import OddOrder.FeitThompson

/-!
# Peterfalvi Part II, Ch. I §2, Proposition 2: `K` is a cyclic normal subgroup of `D`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §2, p. 103.

`D̄ = D/W` acts faithfully on `Q₀` (the kernel of the conjugation action is
`C_D(H∩I) = W` by §1 Prop 5) and transitively on `Q₀^# = H∩I` (§1 Prop 3), so
**Appendix I, Proposition 1** (`Huppert.fitting_cyclic_fixedPointFree`; `D̄`
is solvable by the Feit–Thompson theorem) applies: `Ā = F(D̄)` is cyclic,
fixed-point-free on `Q₀`, and `D̄/Ā` is abelian.

The element `t` acts on `D̄` as an involutive automorphism `τ` (it normalizes
`D` and centralizes `W ≤ V = C_D(t)` pointwise).  Writing
`J̄ = {x̄ ∈ D̄ | τ(x̄) = x̄⁻¹}` for the `τ`-inverted elements, the proof of
Proposition 2 runs:

* `C_D̄(τ) = V̄`: a coset `dW` with `τ(dW) = dW` has `w = d⁻¹(tdt) ∈ W` with
  `w² = 1`, so `w = 1` and `d ∈ V` — every `τ`-fixed coset consists of `V`-
  elements (no coprime-action machinery is needed since `t` centralizes `W`).
* `C_Ā(τ) = 1`: a `τ`-fixed element of `Ā` lies in `V̄`, and `V ≤ C_D(s)`
  (§1 Prop 5) fixes the point `s ∈ Q₀^#`, so fixed-point-freeness kills it.
* `Ā ⊆ J̄`: the Lemma (a) in endomorphism form
  (`map_eq_inv_of_forall_fixed_eq_one`) applied to `τ` on `Ā`.
* `J̄ = K̄` (image of `K`): a coset inverted by `τ` contains an element of
  `K` (an explicit `W`-correction using that representatives commute with
  the error term `w = d(tdt) ∈ W`).
* `J̄ ⊆ Ā`: with `B̄` the preimage in `D̄` of the `τ`-inverted subgroup of the
  abelian quotient `D̄/Ā`, one has `C_B̄(τ) = 1`, so `τ` inverts `B̄`, making
  `B̄` an abelian normal subgroup of `D̄`; hence `J̄ ⊆ B̄ ≤ F(D̄) = Ā`
  (Fitting's theorem, `nilpotent_normal_le_fitting`).
* Hence `Ā = K̄` is cyclic of order `|K|` (the projection `K → K̄` is
  injective), and a generator lifts to `k ∈ K` with `K = ⟨k⟩`; normality of
  `⟨K⟩` in `D` is §1 Lemma (b).
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)
open OddOrder.Isaacs.Ch06 (actionFixedBy)

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The conjugation action of `D` on `Q₀` and its kernel `W` -/

/-- `D` normalizes `Q₀` (conjugation preserves `H` and squares). -/
lemma conj_mem_Q0_of_mem_D {d x : G} (hd : d ∈ hyp.D) (hx : x ∈ hyp.Q0) :
    d * x * d⁻¹ ∈ hyp.Q0 := by
  obtain ⟨hx2, hxH⟩ := hx
  have hdH : d ∈ hyp.H := hyp.D_le_H hd
  refine ⟨?_, mul_mem (mul_mem hdH hxH) (inv_mem hdH)⟩
  calc (d * x * d⁻¹) ^ 2 = d * x ^ 2 * d⁻¹ := conj_pow
    _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]

/-- The conjugation action `D →* Aut(Q₀)`, `d ↦ (x ↦ dxd⁻¹)`. -/
def conjQ0 : ↥hyp.D →* MulAut ↥hyp.Q0 where
  toFun d :=
    { toFun := fun x => ⟨(d : G) * x * (d : G)⁻¹, hyp.conj_mem_Q0_of_mem_D d.2 x.2⟩
      invFun := fun x => ⟨(d : G)⁻¹ * x * (d : G), by
        simpa using hyp.conj_mem_Q0_of_mem_D (inv_mem d.2) x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        change (d : G) * (↑x * ↑y) * (d : G)⁻¹ =
          ((d : G) * ↑x * (d : G)⁻¹) * ((d : G) * ↑y * (d : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : ↥hyp.D) : G) * (x : G) * ((1 : ↥hyp.D) : G)⁻¹ = (x : G)
    rw [Subgroup.coe_one, one_mul, inv_one, mul_one]
  map_mul' d e := by
    ext x
    change ((d : G) * (e : G)) * ↑x * ((d : G) * (e : G))⁻¹ =
      (d : G) * ((e : G) * ↑x * (e : G)⁻¹) * (d : G)⁻¹
    group

@[simp] lemma conjQ0_apply_coe (d : ↥hyp.D) (x : ↥hyp.Q0) :
    ((hyp.conjQ0 d x : ↥hyp.Q0) : G) = (d : G) * x * (d : G)⁻¹ := rfl

/-- The kernel of the conjugation action of `D` on `Q₀` is `W = C_D(H ∩ I)`
(§1 Prop 5). -/
lemma ker_conjQ0 : hyp.conjQ0.ker = hyp.W.subgroupOf hyp.D := by
  ext d
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    hyp.W_eq_centralizer_involutions_H]
  constructor
  · intro h1
    refine ⟨d.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hxQ0 : x ∈ hyp.Q0 := ⟨hx.1, hx.2.2⟩
    have h1x : hyp.conjQ0 d ⟨x, hxQ0⟩ = ⟨x, hxQ0⟩ := by rw [h1]; rfl
    have h2 : (d : G) * x * (d : G)⁻¹ = x := congrArg Subtype.val h1x
    calc x * (d : G) = ((d : G) * x * (d : G)⁻¹) * (d : G) := by rw [h2]
      _ = (d : G) * x := by group
  · rintro ⟨-, hcent⟩
    ext x
    change (d : G) * (x : G) * (d : G)⁻¹ = (x : G)
    rcases eq_or_ne (x : G) 1 with h1 | h1
    · rw [h1, mul_one, mul_inv_cancel]
    · have hx : (x : G) ∈ {y : G | y ^ 2 = 1 ∧ y ≠ 1 ∧ y ∈ hyp.H} :=
        ⟨x.2.1, h1, x.2.2⟩
      have := (Subgroup.mem_centralizer_iff.mp hcent) _ hx
      calc (d : G) * (x : G) * (d : G)⁻¹ = ((x : G) * (d : G)) * (d : G)⁻¹ := by
            rw [← this]
        _ = (x : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-! ## The quotient `D̄ = D/W` and Appendix I, Proposition 1 -/

instance : (hyp.W.subgroupOf hyp.D).Normal := by
  rw [← hyp.ker_conjQ0]
  infer_instance

/-- `D̄ = D/W`, the group the book calls `D̄` on p. 103. -/
abbrev Dbar := ↥hyp.D ⧸ hyp.W.subgroupOf hyp.D

/-- The induced faithful action `D̄ →* Aut(Q₀)`. -/
def conjQ0bar : hyp.Dbar →* MulAut ↥hyp.Q0 :=
  QuotientGroup.lift _ hyp.conjQ0 (fun x hx => by
    rw [← hyp.ker_conjQ0] at hx
    exact hx)

@[simp] lemma conjQ0bar_mk (d : ↥hyp.D) :
    hyp.conjQ0bar (QuotientGroup.mk d) = hyp.conjQ0 d := rfl

lemma injective_conjQ0bar : Function.Injective hyp.conjQ0bar := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, conjQ0bar_mk] at hx
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, ← hyp.ker_conjQ0]
  exact hx

/-- `D̄` (hence `D`) is transitive on `Q₀^#` (§1 Prop 3: `s^K = H ∩ I`). -/
lemma conjQ0bar_transitive (a b : ↥hyp.Q0) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ g : hyp.Dbar, hyp.conjQ0bar g a = b := by
  have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hb' : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
  have himg := hyp.image_conj_KSet_eq_involutions_H (s := (a : G)) a.2.2 a.2.1 ha'
  have hbmem : (b : G) ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} :=
    ⟨b.2.1, hb', b.2.2⟩
  rw [← himg] at hbmem
  obtain ⟨k, hkK, hk⟩ := hbmem
  refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hkK.1⟩, ?_⟩
  rw [conjQ0bar_mk]
  refine Subtype.ext ?_
  change k⁻¹ * (a : G) * k⁻¹⁻¹ = (b : G)
  rw [inv_inv]
  exact hk

lemma odd_card_Dbar : Odd (Nat.card hyp.Dbar) := by
  have hdvd : Nat.card hyp.Dbar ∣ Nat.card ↥hyp.D := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (s := hyp.W.subgroupOf hyp.D)]
    exact Dvd.intro _ rfl
  rcases Nat.even_or_odd (Nat.card hyp.Dbar) with he | ho
  · exact absurd hyp.D_odd
      (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_trans he.two_dvd hdvd)))
  · exact ho

instance : IsSolvable hyp.Dbar :=
  OddOrder.feitThompson hyp.odd_card_Dbar

instance : Nontrivial ↥hyp.Q0 := by
  refine ⟨1, ⟨hyp.distinguishedInvolution,
    hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩, ?_⟩
  intro h
  exact hyp.distinguishedInvolution_ne_one (congrArg Subtype.val h).symm

lemma isElementaryAbelian_Q0 :
    OddOrder.GroupTheory.IsElementaryAbelian 2 ↥hyp.Q0 := by
  constructor
  · intro x y
    exact Subtype.ext (hyp.commute_of_mem_Q0 x.2 y.2)
  · intro x
    exact Subtype.ext (by simpa using x.2.1)

/-- **Appendix I, Proposition 1** applied to `D̄` acting on `Q₀` (p. 103):
`Ā = F(D̄)` is cyclic, acts fixed-point-freely on `Q₀`, and `D̄/Ā` is
abelian. -/
theorem fitting_Dbar_cyclic_fpf_abelian :
    IsCyclic ↥(fitting hyp.Dbar) ∧
      (∀ x ∈ fitting hyp.Dbar, x ≠ 1 →
        actionFixedBy hyp.conjQ0bar x = ⊥) ∧
      commutator hyp.Dbar ≤ fitting hyp.Dbar :=
  Huppert.fitting_cyclic_fixedPointFree Nat.prime_two hyp.odd_card_Dbar
    hyp.isElementaryAbelian_Q0 hyp.conjQ0bar hyp.injective_conjQ0bar
    hyp.conjQ0bar_transitive

/-! ## The involutive automorphism `τ` of `D̄` induced by `t`

`t` normalizes `D` and centralizes `W ≤ V = C_D(t)` pointwise, so conjugation
by `t` induces an involutive automorphism `τ` of `D̄ = D/W`.  The book writes
this action exponentially (`ā ↦ āᵗ`). -/

lemma t_mul_t : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq

/-- `t` normalizes `D` (p. 100), in the form using `t⁻¹ = t`. -/
lemma t_conj_mem_D' {x : G} (hx : x ∈ hyp.D) : hyp.t * x * hyp.t ∈ hyp.D := by
  have := hyp.t_conj_mem_D hx
  rwa [hyp.t_inv_eq] at this

/-- Conjugation by `t` as an endomorphism of `D`. -/
def tauD : ↥hyp.D →* ↥hyp.D where
  toFun d := ⟨hyp.t * (d : G) * hyp.t, hyp.t_conj_mem_D' d.2⟩
  map_one' := Subtype.ext (by
    change hyp.t * ((1 : ↥hyp.D) : G) * hyp.t = ((1 : ↥hyp.D) : G)
    rw [Subgroup.coe_one, mul_one]
    exact hyp.t_mul_t)
  map_mul' d e := Subtype.ext (by
    change hyp.t * ((d : G) * (e : G)) * hyp.t =
      (hyp.t * (d : G) * hyp.t) * (hyp.t * (e : G) * hyp.t)
    calc hyp.t * ((d : G) * (e : G)) * hyp.t
        = hyp.t * (d : G) * (hyp.t * hyp.t) * (e : G) * hyp.t := by
          rw [hyp.t_mul_t]; group
      _ = (hyp.t * (d : G) * hyp.t) * (hyp.t * (e : G) * hyp.t) := by group)

@[simp] lemma tauD_apply_coe (d : ↥hyp.D) :
    ((hyp.tauD d : ↥hyp.D) : G) = hyp.t * (d : G) * hyp.t := rfl

lemma tauD_involutive (d : ↥hyp.D) : hyp.tauD (hyp.tauD d) = d := by
  refine Subtype.ext ?_
  change hyp.t * (hyp.t * (d : G) * hyp.t) * hyp.t = (d : G)
  calc hyp.t * (hyp.t * (d : G) * hyp.t) * hyp.t
      = (hyp.t * hyp.t) * (d : G) * (hyp.t * hyp.t) := by group
    _ = (d : G) := by rw [hyp.t_mul_t, one_mul, mul_one]

/-- `τ` fixes `W` pointwise: `W ≤ V = C_D(t)`. -/
lemma tauD_apply_of_mem_W {d : ↥hyp.D} (hd : (d : G) ∈ hyp.W) : hyp.tauD d = d := by
  refine Subtype.ext ?_
  change hyp.t * (d : G) * hyp.t = (d : G)
  have hc : Commute (d : G) hyp.t := hyp.commute_t_of_mem_V (hyp.W_le_V hd)
  rw [← hc.eq, mul_assoc, hyp.t_mul_t, mul_one]

lemma tauD_mem_W_subgroupOf {d : ↥hyp.D} (hd : d ∈ hyp.W.subgroupOf hyp.D) :
    hyp.tauD d ∈ hyp.W.subgroupOf hyp.D := by
  rw [Subgroup.mem_subgroupOf] at hd ⊢
  rw [hyp.tauD_apply_of_mem_W hd]
  exact hd

/-- The endomorphism of `D̄ = D/W` induced by `tauD`. -/
def tauHom : hyp.Dbar →* hyp.Dbar :=
  QuotientGroup.map _ _ hyp.tauD fun _ hd => hyp.tauD_mem_W_subgroupOf hd

@[simp] lemma tauHom_mk (d : ↥hyp.D) :
    hyp.tauHom (QuotientGroup.mk d) = QuotientGroup.mk (hyp.tauD d) := rfl

lemma tauHom_involutive (x : hyp.Dbar) : hyp.tauHom (hyp.tauHom x) = x := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
  rw [hyp.tauHom_mk, hyp.tauHom_mk, hyp.tauD_involutive]

/-- **`τ`** — the involutive automorphism of `D̄` induced by conjugation by
`t` (p. 103, written `ā ↦ āᵗ`). -/
def tau : MulAut hyp.Dbar where
  toFun := hyp.tauHom
  invFun := hyp.tauHom
  left_inv := hyp.tauHom_involutive
  right_inv := hyp.tauHom_involutive
  map_mul' := map_mul hyp.tauHom

@[simp] lemma tau_apply (x : hyp.Dbar) : hyp.tau x = hyp.tauHom x := rfl

lemma tau_involutive (x : hyp.Dbar) : hyp.tau (hyp.tau x) = x :=
  hyp.tauHom_involutive x

/-! ## `C_D̄(τ) = V̄`: the `τ`-fixed cosets are exactly the `V`-cosets (p. 103)

A coset `d̄ = dW` is fixed by `τ` iff `w = (tdt)⁻¹d ∈ W`; but `w` commutes with `t`
(as `W ≤ V = C_D(t)`), which forces `w² = 1`, and `D` has odd order, so `w = 1` and
`t d t = d`, i.e. `d ∈ V`.  No coprime-action machinery is needed. -/

/-- The coset element `w = ((tdt)⁻¹d : ↥D)` has `G`-value `t d⁻¹ t d`. -/
private lemma tauD_inv_mul_coe (d : ↥hyp.D) :
    (((hyp.tauD d)⁻¹ * d : ↥hyp.D) : G) = hyp.t * (d : G)⁻¹ * hyp.t * (d : G) := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hyp.tauD_apply_coe]
  simp only [mul_inv_rev, hyp.t_inv_eq]
  group

/-- If `a² = 1` then `(a b⁻¹ a b)(b⁻¹ a b a) = 1` — the algebraic core of `w² = 1`
for the `τ`-fixed-coset argument. -/
private lemma sq_inverted_eq_one {H : Type*} [Group H] {a b : H} (ha : a * a = 1) :
    (a * b⁻¹ * a * b) * (b⁻¹ * a * b * a) = 1 := by
  have h1 : (a * b⁻¹ * a * b) * (b⁻¹ * a * b * a) = a * b⁻¹ * (a * a) * b * a := by group
  rw [h1, ha, mul_one]
  have h2 : a * b⁻¹ * b * a = a * a := by group
  rw [h2, ha]

/-- **Peterfalvi Part II, Ch. I §2** (p. 103): `C_D̄(τ) = V̄`.  A coset `d̄` is fixed
by `τ` iff its representative lies in `V = C_D(t)`. -/
lemma tau_mk_eq_iff_mem_V (d : ↥hyp.D) :
    hyp.tau (QuotientGroup.mk d) = QuotientGroup.mk d ↔ (d : G) ∈ hyp.V := by
  rw [hyp.tau_apply, hyp.tauHom_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · -- `w = (tdt)⁻¹d ∈ W ⟹ d ∈ V`.
    intro hwW
    set w : G := (((hyp.tauD d)⁻¹ * d : ↥hyp.D) : G) with hwdef
    have hwcoe : w = hyp.t * (d : G)⁻¹ * hyp.t * (d : G) := hyp.tauD_inv_mul_coe d
    have hcomm : Commute w hyp.t := hyp.commute_t_of_mem_V (hyp.W_le_V hwW)
    -- `t w t = w`, giving the second form `w = d⁻¹ t d t`.
    have htwt : hyp.t * w * hyp.t = w := by
      rw [hcomm.symm.eq, mul_assoc, hyp.t_mul_t, mul_one]
    have hw2 : w = (d : G)⁻¹ * hyp.t * (d : G) * hyp.t := by
      have hcalc : hyp.t * w * hyp.t = (d : G)⁻¹ * hyp.t * (d : G) * hyp.t := by
        rw [hwcoe]
        rw [show hyp.t * (hyp.t * (d : G)⁻¹ * hyp.t * (d : G)) * hyp.t
              = hyp.t * hyp.t * ((d : G)⁻¹ * hyp.t * (d : G) * hyp.t) by
            simp only [mul_assoc], hyp.t_mul_t, one_mul]
      rw [← hcalc, htwt]
    -- `w² = 1` from the two forms; `D` odd ⟹ `w = 1`.
    have hsq : w ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hwcoe]
      nth_rewrite 1 [hw2]
      exact sq_inverted_eq_one hyp.t_mul_t
    have hw1 : w = 1 :=
      eq_one_of_sq_eq_one_of_odd_card hyp.D_odd (hyp.V_le_D (hyp.W_le_V hwW)) hsq
    -- `w = 1 ⟹ t d t = d ⟹ d ∈ V`.
    have hwe : hyp.t * (d : G)⁻¹ * hyp.t * (d : G) = 1 := hwcoe ▸ hw1
    have htdt : hyp.t * (d : G) * hyp.t = (d : G) := by
      have hh : hyp.t * (d : G)⁻¹ * hyp.t = (d : G)⁻¹ := eq_inv_of_mul_eq_one_left hwe
      have hinv := congrArg (·⁻¹) hh
      simpa [mul_inv_rev, hyp.t_inv_eq, mul_assoc] using hinv
    have hc : hyp.t * (d : G) = (d : G) * hyp.t := by
      have hcong := congrArg (· * hyp.t) htdt
      rwa [mul_assoc, hyp.t_mul_t, mul_one] at hcong
    exact Subgroup.mem_inf.mpr
      ⟨d.2, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩
  · -- `d ∈ V ⟹ tauD d = d`, so the coset element is `1 ∈ W`.
    intro hdV
    have hcomm : Commute (d : G) hyp.t := hyp.commute_t_of_mem_V hdV
    have htdt : hyp.t * (d : G) * hyp.t = (d : G) := by
      rw [← hcomm.eq, mul_assoc, hyp.t_mul_t, mul_one]
    have htauD : hyp.tauD d = d := Subtype.ext (by rw [hyp.tauD_apply_coe, htdt])
    rw [htauD, inv_mul_cancel]
    simpa using hyp.W.one_mem

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
