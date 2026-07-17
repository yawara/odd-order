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
* `J̄ ⊆ Ā`: with `B̄` the preimage in `D̄` of the `τ`-inverted subgroup of the
  abelian quotient `D̄/Ā`, one has `C_B̄(τ) = 1`, so `τ` inverts `B̄`, making
  `B̄` an abelian normal subgroup of `D̄`; hence `J̄ ⊆ B̄ ≤ F(D̄) = Ā`
  (Fitting's theorem, `nilpotent_normal_le_fitting`).
* `A` is the full preimage of `Ā`.  Then `K ⊆ A` because `Ā = J̄`, while
  `A ∩ V = W` because the `τ`-fixed locus in `Ā` is trivial.
* Applying §1 Lemma (a) to `A` gives `A = KW`; comparison with the quotient-
  preimage cardinal formula gives `|Ā| = |K|`.
* A generator of cyclic `Ā` lifts through `A = KW` to some `k ∈ K`.  The order
  equality forces `K = ⟨k⟩`; the genuine subgroup with carrier `K` is normal
  in `D` by §1 Lemma (b).
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)
open OddOrder.Isaacs.Ch06 (actionFixedBy)
open scoped IsMulCommutative Pointwise

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

/-! ## `C_Ā(τ) = 1` (p. 103) -/

/-- **Peterfalvi Part II, Ch. I §2** (p. 103): a `τ`-fixed element of `Ā = F(D̄)` is
trivial.  Such an element lies in `V̄` (`tau_mk_eq_iff_mem_V`), whose elements fix the
distinguished point `s ∈ Q₀^#` (`V ⊆ C_D(s)`, §1 Prop 5); but `Ā` acts fixed-point-
freely on `Q₀` (Appendix I, Proposition 1), so it must be `1`. -/
lemma tau_fixed_fitting_eq_one {x : hyp.Dbar} (hxF : x ∈ fitting hyp.Dbar)
    (hxτ : hyp.tau x = x) : x = 1 := by
  by_contra hx1
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
  -- `v ∈ V`, hence `v` centralizes the distinguished involution `s`.
  have hvV : (v : G) ∈ hyp.V := (hyp.tau_mk_eq_iff_mem_V v).mp hxτ
  have hvs : (v : G) ∈ Subgroup.centralizer {hyp.distinguishedInvolution} := by
    rw [hyp.V_eq_centralizer_distinguishedInvolution] at hvV
    exact (Subgroup.mem_inf.mp hvV).2
  have hcomm : Commute (v : G) hyp.distinguishedInvolution :=
    Subgroup.mem_centralizer_singleton_iff.mp hvs
  have hsQ : hyp.distinguishedInvolution ∈ hyp.Q0 :=
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
  -- `x = mk v` fixes the nonidentity point `s ∈ Q₀`.
  have hfix : hyp.conjQ0bar (QuotientGroup.mk v) ⟨hyp.distinguishedInvolution, hsQ⟩ =
      ⟨hyp.distinguishedInvolution, hsQ⟩ := by
    rw [hyp.conjQ0bar_mk]
    refine Subtype.ext ?_
    rw [hyp.conjQ0_apply_coe, hcomm.eq]
    group
  -- fixed-point-freeness of `Ā` (Appendix I Prop 1) gives a contradiction.
  have hfpf := hyp.fitting_Dbar_cyclic_fpf_abelian.2.1 (QuotientGroup.mk v) hxF hx1
  have hmem : (⟨hyp.distinguishedInvolution, hsQ⟩ : ↥hyp.Q0) ∈
      actionFixedBy hyp.conjQ0bar (QuotientGroup.mk v) := hfix
  rw [hfpf, Subgroup.mem_bot] at hmem
  exact hyp.distinguishedInvolution_ne_one (by simpa using congrArg Subtype.val hmem)

/-! ## `Ā ⊆ J`: `τ` inverts every element of `Ā` (p. 103) -/

/-- **Peterfalvi Part II, Ch. I §2** (p. 103): `Ā = F(D̄) ⊆ J`, i.e. `τ` inverts every
element of the Fitting subgroup.  `Ā` is characteristic, so `τ` restricts to an
involutive endomorphism of `Ā` fixing only `1` (`tau_fixed_fitting_eq_one`); `Ā` has
odd order, so the §1 Lemma (a) in endomorphism form
(`map_eq_inv_of_forall_fixed_eq_one`) shows `τ` inverts every element. -/
lemma fitting_subset_inverted {y : hyp.Dbar} (hy : y ∈ fitting hyp.Dbar) :
    hyp.tau y = y⁻¹ := by
  -- `τ` maps `Ā` into `Ā` (characteristic).
  have hmapeq : (fitting hyp.Dbar).map (hyp.tau : hyp.Dbar ≃* hyp.Dbar).toMonoidHom =
      fitting hyp.Dbar :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) hyp.tau
  have hmem : ∀ z ∈ fitting hyp.Dbar, hyp.tau z ∈ fitting hyp.Dbar := fun z hz => by
    rw [← hmapeq]; exact Subgroup.mem_map_of_mem _ hz
  -- the restricted endomorphism `σ = τ|_Ā`.
  let σ : ↥(fitting hyp.Dbar) →* ↥(fitting hyp.Dbar) :=
    { toFun := fun a => ⟨hyp.tau a, hmem a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by push_cast; rw [map_mul]) }
  have hσ2 : ∀ a, σ (σ a) = a := fun a => Subtype.ext (hyp.tau_involutive a)
  have hfix : ∀ a, σ a = a → a = 1 := fun a ha =>
    Subtype.ext (hyp.tau_fixed_fitting_eq_one a.2 (congrArg Subtype.val ha))
  -- odd order of `Ā`.
  have hodd : Odd (Nat.card ↥(fitting hyp.Dbar)) := by
    rcases Nat.even_or_odd (Nat.card ↥(fitting hyp.Dbar)) with he | ho
    · exact absurd hyp.odd_card_Dbar (Nat.not_odd_iff_even.mpr
        (even_iff_two_dvd.mpr (dvd_trans he.two_dvd (Subgroup.card_subgroup_dvd_card _))))
    · exact ho
  -- §1 Lemma (a), endomorphism form.
  exact congrArg Subtype.val (map_eq_inv_of_forall_fixed_eq_one hodd σ hσ2 hfix ⟨y, hy⟩)

/-! ## `J ⊆ Ā`: every `τ`-inverted element lies in `F(D̄)` (p. 103) -/

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103): if `τ` inverts
`x ∈ D̄`, then `x ∈ Ā = F(D̄)`.

In the abelian quotient `D̄/Ā`, the inverted elements form a subgroup; its full
preimage `B` is normal in `D̄`.  A `τ`-fixed element of `B` maps to an involution
in the odd-order quotient, hence lies in `Ā`, where `tau_fixed_fitting_eq_one`
kills it.  Thus §1 Lemma (a) makes `τ` inversion on `B`, so `B` is abelian and
Fitting maximality gives `B ≤ Ā`. -/
lemma inverted_mem_fitting {x : hyp.Dbar} (hx : hyp.tau x = x⁻¹) :
    x ∈ fitting hyp.Dbar := by
  let F : Subgroup hyp.Dbar := fitting hyp.Dbar
  have hFmap : F.map (hyp.tau : hyp.Dbar ≃* hyp.Dbar).toMonoidHom = F :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) hyp.tau
  have htauF : ∀ z ∈ F, hyp.tau z ∈ F := fun z hz => by
    rw [← hFmap]
    exact Subgroup.mem_map_of_mem _ hz
  let Q := hyp.Dbar ⧸ F
  letI : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hyp.fitting_Dbar_cyclic_fpf_abelian.2.2
  letI : CommGroup Q := inferInstance
  let tauQ : Q →* Q :=
    QuotientGroup.map F F hyp.tau.toMonoidHom (fun z hz => htauF z hz)
  have tauQ_mk (z : hyp.Dbar) :
      tauQ (QuotientGroup.mk' F z) = QuotientGroup.mk' F (hyp.tau z) := rfl
  have htauQ2 (q : Q) : tauQ (tauQ q) = q := by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective F q
    rw [tauQ_mk, tauQ_mk, hyp.tau_involutive]
  let Jq : Subgroup Q := MonoidHom.eqLocus tauQ invMonoidHom
  let B : Subgroup hyp.Dbar := Jq.comap (QuotientGroup.mk' F)
  haveI hJqN : Jq.Normal := Subgroup.normal_of_isMulCommutative Jq
  haveI hBN : B.Normal := hJqN.comap (QuotientGroup.mk' F)
  have hmemB_iff (z : hyp.Dbar) :
      z ∈ B ↔ tauQ (QuotientGroup.mk' F z) = (QuotientGroup.mk' F z)⁻¹ := Iff.rfl
  have hxB : x ∈ B := by
    rw [hmemB_iff, tauQ_mk]
    simpa using congrArg (QuotientGroup.mk' F) hx
  have htauB : ∀ z ∈ B, hyp.tau z ∈ B := by
    intro z hz
    rw [hmemB_iff, tauQ_mk]
    have hzq : tauQ (QuotientGroup.mk' F z) = (QuotientGroup.mk' F z)⁻¹ :=
      (hmemB_iff z).mp hz
    rw [hyp.tau_involutive, ← tauQ_mk]
    have hi := congrArg Inv.inv hzq
    simpa using hi.symm
  have hoddQ : Odd (Nat.card Q) := by
    have hdvd : Nat.card Q ∣ Nat.card hyp.Dbar := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (s := F)]
      exact Dvd.intro _ rfl
    rcases Nat.even_or_odd (Nat.card Q) with he | ho
    · exact absurd hyp.odd_card_Dbar
        (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_trans he.two_dvd hdvd)))
    · exact ho
  have hoddB : Odd (Nat.card ↥B) := by
    rcases Nat.even_or_odd (Nat.card ↥B) with he | ho
    · exact absurd hyp.odd_card_Dbar
        (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr
          (dvd_trans he.two_dvd (Subgroup.card_subgroup_dvd_card B))))
    · exact ho
  let sigma : ↥B →* ↥B :=
    { toFun := fun z => ⟨hyp.tau z, htauB z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by push_cast; rw [map_mul]) }
  have hsigma2 : ∀ z, sigma (sigma z) = z := fun z =>
    Subtype.ext (hyp.tau_involutive z)
  have hfix : ∀ z, sigma z = z → z = 1 := by
    intro z hz
    have hzfix : hyp.tau (z : hyp.Dbar) = z := congrArg Subtype.val hz
    have hzJ : tauQ (QuotientGroup.mk' F z) = (QuotientGroup.mk' F z)⁻¹ :=
      (hmemB_iff z).mp z.2
    have hqfix : tauQ (QuotientGroup.mk' F z) = QuotientGroup.mk' F z := by
      rw [tauQ_mk, hzfix]
    have hqinv : (QuotientGroup.mk' F z) = (QuotientGroup.mk' F z)⁻¹ :=
      hqfix.symm.trans hzJ
    have hq2 : (QuotientGroup.mk' F z) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hqinv]
      rw [inv_mul_cancel]
    have hoddTop : Odd (Nat.card ↥(⊤ : Subgroup Q)) := by simpa using hoddQ
    have hq1 : QuotientGroup.mk' F z = 1 :=
      eq_one_of_sq_eq_one_of_odd_card hoddTop (Subgroup.mem_top _) hq2
    have hzF : (z : hyp.Dbar) ∈ F :=
      (QuotientGroup.eq_one_iff (N := F) (z : hyp.Dbar)).mp hq1
    exact Subtype.ext (hyp.tau_fixed_fitting_eq_one hzF hzfix)
  have hinvB : ∀ z ∈ B, hyp.tau z = z⁻¹ := by
    intro z hz
    exact congrArg Subtype.val
      (map_eq_inv_of_forall_fixed_eq_one hoddB sigma hsigma2 hfix ⟨z, hz⟩)
  haveI hBcomm : IsMulCommutative ↥B := isMulCommutative_iff.mpr fun a b => by
    apply Subtype.ext
    have hab := hinvB ((a : hyp.Dbar) * b) (B.mul_mem a.2 b.2)
    rw [map_mul, hinvB a a.2, hinvB b b.2, mul_inv_rev] at hab
    have hab' := congrArg Inv.inv hab
    simpa [mul_inv_rev] using hab'.symm
  letI : CommGroup ↥B := inferInstance
  haveI : Group.IsNilpotent ↥B := inferInstance
  exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting hxB

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103):
`Ā = J̄`; membership in `F(D̄)` is equivalent to being inverted by `τ`. -/
lemma mem_fitting_iff_tau_eq_inv {x : hyp.Dbar} :
    x ∈ fitting hyp.Dbar ↔ hyp.tau x = x⁻¹ :=
  ⟨hyp.fitting_subset_inverted, hyp.inverted_mem_fitting⟩

/-! ## The preimage `A` and the identities `K ⊆ A`, `A ∩ V = W` (p. 103) -/

/-- The subgroup of `D` called `A` in Proposition 2: the full preimage of
`Ā = F(D̄)` under `D → D̄ = D/W`. -/
def fittingPreimage : Subgroup ↥hyp.D :=
  (fitting hyp.Dbar).comap (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D))

/-- Membership in the Fitting preimage `A`. -/
lemma mem_fittingPreimage_iff (d : ↥hyp.D) :
    d ∈ hyp.fittingPreimage ↔ QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d ∈
      fitting hyp.Dbar := Iff.rfl

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103): `K ⊆ A`.
Every element of `K` maps to the inverted locus `J̄ = Ā`. -/
lemma mem_fittingPreimage_of_mem_KSet {k : G} (hk : k ∈ hyp.KSet) :
    (⟨k, hk.1⟩ : ↥hyp.D) ∈ hyp.fittingPreimage := by
  let kD : ↥hyp.D := ⟨k, hyp.mem_D_of_mem_KSet hk⟩
  change kD ∈ hyp.fittingPreimage
  rw [hyp.mem_fittingPreimage_iff, hyp.mem_fitting_iff_tau_eq_inv]
  have htauD : hyp.tauD kD = kD⁻¹ :=
    Subtype.ext (hyp.t_conj_eq_inv_of_mem_KSet hk)
  calc
    hyp.tau (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kD) =
        QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) (hyp.tauD kD) :=
      hyp.tauHom_mk kD
    _ = QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kD⁻¹ := congrArg _ htauD
    _ = (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kD)⁻¹ := map_inv _ _

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103): `A ∩ V = W`.
The image of `A ∩ V` is both `τ`-fixed and in `F(D̄)`, hence trivial. -/
lemma fittingPreimage_inf_V :
    hyp.fittingPreimage ⊓ hyp.V.subgroupOf hyp.D = hyp.W.subgroupOf hyp.D := by
  ext d
  constructor
  · rintro ⟨hdA, hdV⟩
    change (d : G) ∈ hyp.V at hdV
    change (d : G) ∈ hyp.W
    have hfixed : hyp.tau (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d) =
        QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d :=
      (hyp.tau_mk_eq_iff_mem_V d).2 hdV
    have hdF : QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d ∈ fitting hyp.Dbar :=
      (hyp.mem_fittingPreimage_iff d).1 hdA
    exact (QuotientGroup.eq_one_iff (N := hyp.W.subgroupOf hyp.D) d).mp
      (hyp.tau_fixed_fitting_eq_one hdF hfixed)
  · intro hdW
    change (d : G) ∈ hyp.W at hdW
    refine ⟨?_, ?_⟩
    · change QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d ∈ fitting hyp.Dbar
      have hq1 : QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d = 1 :=
        (QuotientGroup.eq_one_iff (N := hyp.W.subgroupOf hyp.D) d).2 hdW
      rw [hq1]
      exact (fitting hyp.Dbar).one_mem
    · change (d : G) ∈ hyp.V
      exact hyp.W_le_V hdW

/-! ## The decomposition A = KW and the order identity |Ā| = |K| (p. 103) -/

/-- The book's subgroup A, now regarded as a subgroup of the ambient group G.
Its subtype model above is convenient for the quotient map; this image model is
the one to which the involution decomposition from §1 applies. -/
def fittingPreimageInG : Subgroup G :=
  hyp.fittingPreimage.map hyp.D.subtype

lemma fittingPreimageInG_le_D : hyp.fittingPreimageInG ≤ hyp.D :=
  Subgroup.map_subtype_le hyp.fittingPreimage

lemma W_le_fittingPreimageInG : hyp.W ≤ hyp.fittingPreimageInG := by
  intro w hw
  change w ∈ hyp.fittingPreimage.map hyp.D.subtype
  rw [Subgroup.mem_map]
  let wD : ↥hyp.D := ⟨w, hyp.V_le_D (hyp.W_le_V hw)⟩
  refine ⟨wD, ?_, rfl⟩
  have hwsub : wD ∈ hyp.W.subgroupOf hyp.D := hw
  rw [← hyp.fittingPreimage_inf_V] at hwsub
  exact hwsub.1

lemma KSet_subset_fittingPreimageInG : hyp.KSet ⊆ hyp.fittingPreimageInG := by
  intro k hk
  change k ∈ hyp.fittingPreimage.map hyp.D.subtype
  rw [Subgroup.mem_map]
  exact ⟨⟨k, hyp.mem_D_of_mem_KSet hk⟩,
    hyp.mem_fittingPreimage_of_mem_KSet hk, rfl⟩

/-- Conjugation by t preserves A. -/
lemma t_conj_mem_fittingPreimageInG {x : G} (hx : x ∈ hyp.fittingPreimageInG) :
    hyp.t * x * hyp.t ∈ hyp.fittingPreimageInG := by
  change x ∈ hyp.fittingPreimage.map hyp.D.subtype at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨d, hdA, rfl⟩ := hx
  change hyp.t * (d : G) * hyp.t ∈ hyp.fittingPreimage.map hyp.D.subtype
  rw [Subgroup.mem_map]
  refine ⟨hyp.tauD d, ?_, rfl⟩
  change QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) (hyp.tauD d) ∈ fitting hyp.Dbar
  change hyp.tau (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d) ∈ fitting hyp.Dbar
  have hmapeq : (fitting hyp.Dbar).map
      (hyp.tau : hyp.Dbar ≃* hyp.Dbar).toMonoidHom = fitting hyp.Dbar :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) hyp.tau
  rw [← hmapeq]
  exact Subgroup.mem_map_of_mem _ hdA

lemma odd_card_fittingPreimageInG : Odd (Nat.card hyp.fittingPreimageInG) := by
  have hcard : Nat.card hyp.fittingPreimageInG = Nat.card hyp.fittingPreimage := by
    exact Subgroup.card_map_of_injective hyp.D.subtype_injective
  rw [hcard]
  exact hyp.D_odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.fittingPreimage)

/-- Inside the ambient group, the fixed part of A under conjugation by t
is precisely W. -/
lemma fittingPreimageInG_inf_centralizer_t :
    hyp.fittingPreimageInG ⊓ Subgroup.centralizer ({hyp.t} : Set G) = hyp.W := by
  apply le_antisymm
  · intro x hx
    have hxA : x ∈ hyp.fittingPreimageInG := hx.1
    have hxcent : x ∈ Subgroup.centralizer ({hyp.t} : Set G) := hx.2
    have hxD : x ∈ hyp.D := hyp.fittingPreimageInG_le_D hxA
    change x ∈ hyp.fittingPreimage.map hyp.D.subtype at hxA
    rw [Subgroup.mem_map] at hxA
    obtain ⟨d, hdA, hdval⟩ := hxA
    have hd_eq : d = ⟨x, hxD⟩ := Subtype.ext hdval
    subst d
    have hxV : x ∈ hyp.V := ⟨hxD, hxcent⟩
    have hxAV : (⟨x, hxD⟩ : ↥hyp.D) ∈
        hyp.fittingPreimage ⊓ hyp.V.subgroupOf hyp.D := ⟨hdA, hxV⟩
    rw [hyp.fittingPreimage_inf_V] at hxAV
    exact hxAV
  · intro w hw
    exact ⟨hyp.W_le_fittingPreimageInG hw, (hyp.W_le_V hw).2⟩

/-- The elements of A inverted by t are exactly the book's set K. -/
lemma invertedBy_fittingPreimageInG :
    invertedBy hyp.fittingPreimageInG hyp.t = hyp.KSet := by
  ext x
  change (x ∈ hyp.fittingPreimageInG ∧ hyp.t * x * hyp.t = x⁻¹) ↔
    (x ∈ hyp.D ∧ hyp.t * x * hyp.t = x⁻¹)
  constructor
  · rintro ⟨hxA, hxi⟩
    exact ⟨hyp.fittingPreimageInG_le_D hxA, hxi⟩
  · rintro hk
    exact ⟨hyp.KSet_subset_fittingPreimageInG hk, hk.2⟩

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103): A = KW.
Here multiplication is pointwise set multiplication; §1 Lemma (a) first gives
A = WK, and W ≤ C_G(K) permits the displayed order. -/
theorem fittingPreimageInG_eq_KSet_mul_W :
    (hyp.fittingPreimageInG : Set G) = hyp.KSet * (hyp.W : Set G) := by
  have hAWK : (hyp.fittingPreimageInG : Set G) =
      (hyp.W : Set G) * hyp.KSet := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨⟨w, hw⟩, ⟨k, hk⟩⟩, heq⟩ :=
        (invertedProdEquiv (X := hyp.fittingPreimageInG) (t := hyp.t)
          hyp.t_mul_t hyp.odd_card_fittingPreimageInG
          (fun _ hxA => hyp.t_conj_mem_fittingPreimageInG hxA)).surjective ⟨x, hx⟩
      rw [Set.mem_mul]
      refine ⟨w, ?_, k, ?_, congrArg Subtype.val heq⟩
      · change w ∈ hyp.W
        rw [← hyp.fittingPreimageInG_inf_centralizer_t]
        exact hw
      · rw [← hyp.invertedBy_fittingPreimageInG]
        exact hk
    · intro hx
      rw [Set.mem_mul] at hx
      obtain ⟨w, hw, k, hk, rfl⟩ := hx
      exact hyp.fittingPreimageInG.mul_mem
        (hyp.W_le_fittingPreimageInG hw) (hyp.KSet_subset_fittingPreimageInG hk)
  rw [hAWK]
  ext x
  constructor
  · intro hx
    rw [Set.mem_mul] at hx ⊢
    obtain ⟨w, hw, k, hk, rfl⟩ := hx
    refine ⟨k, hk, w, hw, ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hw.2 k hk
  · intro hx
    rw [Set.mem_mul] at hx ⊢
    obtain ⟨k, hk, w, hw, rfl⟩ := hx
    refine ⟨w, hw, k, hk, ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hw.2 k hk).symm

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103):
|Ā| = |K|, where Ā = F(D̄) and |K| denotes the cardinality of the
inverted set. -/
theorem card_fitting_Dbar_eq_ncard_KSet :
    Nat.card (fitting hyp.Dbar) = hyp.KSet.ncard := by
  have hcardA : Nat.card hyp.fittingPreimageInG =
      Nat.card hyp.W * hyp.KSet.ncard := by
    have h := card_eq_card_centralizer_mul_ncard_invertedBy
      (X := hyp.fittingPreimageInG) (t := hyp.t) hyp.t_mul_t
      hyp.odd_card_fittingPreimageInG
      (fun _ hxA => hyp.t_conj_mem_fittingPreimageInG hxA)
    rwa [hyp.fittingPreimageInG_inf_centralizer_t,
      hyp.invertedBy_fittingPreimageInG] at h
  have hcardApre : Nat.card hyp.fittingPreimageInG =
      Nat.card hyp.fittingPreimage :=
    Subgroup.card_map_of_injective hyp.D.subtype_injective
  have hcardWsub : Nat.card ↥(hyp.W.subgroupOf hyp.D) = Nat.card ↥hyp.W :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (hyp.W_le_V.trans hyp.V_le_D)).toEquiv
  have hcardPre : Nat.card hyp.fittingPreimage =
      Nat.card (fitting hyp.Dbar) * Nat.card hyp.W := by
    calc
      Nat.card hyp.fittingPreimage =
          Nat.card (fitting hyp.Dbar) *
            Nat.card (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D)).ker :=
        Subgroup.card_comap_eq_card_mul_card_ker
          (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D))
          (QuotientGroup.mk'_surjective _) (fitting hyp.Dbar)
      _ = Nat.card (fitting hyp.Dbar) * Nat.card hyp.W := by
        rw [QuotientGroup.ker_mk', hcardWsub]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥hyp.W))
  calc
    Nat.card hyp.W * Nat.card (fitting hyp.Dbar) =
        Nat.card (fitting hyp.Dbar) * Nat.card hyp.W := Nat.mul_comm _ _
    _ = Nat.card hyp.fittingPreimage := hcardPre.symm
    _ = Nat.card hyp.fittingPreimageInG := hcardApre.symm
    _ = Nat.card hyp.W * hyp.KSet.ncard := hcardA

/-! ## The cyclic normal subgroup K (p. 103) -/

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103):
there is an element k ∈ K whose powers are exactly K.

Lift a generator of the cyclic group F(D̄) to A = KW, discard its W-factor,
and compare orders using |F(D̄)| = |K|. -/
theorem exists_KSet_generator :
    ∃ k : G, k ∈ hyp.KSet ∧ (Subgroup.zpowers k : Set G) = hyp.KSet := by
  let F := fitting hyp.Dbar
  haveI : IsCyclic ↥F := hyp.fitting_Dbar_cyclic_fpf_abelian.1
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥F)
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective
    (N := hyp.W.subgroupOf hyp.D) (a : hyp.Dbar)
  have hdA : d ∈ hyp.fittingPreimage := by
    rw [hyp.mem_fittingPreimage_iff, hd]
    exact a.2
  have hdAG : (d : G) ∈ hyp.fittingPreimageInG := by
    change (d : G) ∈ hyp.fittingPreimage.map hyp.D.subtype
    rw [Subgroup.mem_map]
    exact ⟨d, hdA, rfl⟩
  have hdAG' : (d : G) ∈ hyp.KSet * (hyp.W : Set G) :=
    (Set.ext_iff.mp hyp.fittingPreimageInG_eq_KSet_mul_W (d : G)).mp hdAG
  rw [Set.mem_mul] at hdAG'
  obtain ⟨k, hk, w, hw, hkw⟩ := hdAG'
  let kd : ↥hyp.D := ⟨k, hyp.mem_D_of_mem_KSet hk⟩
  let wd : ↥hyp.D := ⟨w, hyp.V_le_D (hyp.W_le_V hw)⟩
  have hkdwd : kd * wd = d := Subtype.ext hkw
  have hkmk : QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kd = (a : hyp.Dbar) := by
    rw [← hd, ← hkdwd, map_mul]
    have hwdW : wd ∈ hyp.W.subgroupOf hyp.D := hw
    have hwdq : QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) wd = 1 :=
      (QuotientGroup.eq_one_iff wd).mpr hwdW
    rw [hwdq, mul_one]
  let kG : G := kd
  refine ⟨kG, hk, ?_⟩
  have horder_a : orderOf a = Nat.card ↥F :=
    orderOf_eq_card_of_forall_mem_zpowers ha
  have horder_dvd : orderOf (a : hyp.Dbar) ∣ orderOf kG := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D)) kd
    rw [hkmk] at h
    simpa [kG] using h
  have hzp_card : (Subgroup.zpowers kG : Set G).ncard = orderOf kG := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zpowers]
  have hcard_le : hyp.KSet.ncard ≤ (Subgroup.zpowers kG : Set G).ncard := by
    rw [hzp_card, ← hyp.card_fitting_Dbar_eq_ncard_KSet, ← horder_a]
    simpa using Nat.le_of_dvd (orderOf_pos kG) horder_dvd
  apply Set.eq_of_subset_of_ncard_le _ hcard_le
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact hyp.zpow_mem_KSet hk n

/-- The book's K, constructed as a genuine subgroup. The carrier equality
below proves that taking the closure adds no elements. -/
def K : Subgroup G := Subgroup.closure hyp.KSet

lemma K_le_D : hyp.K ≤ hyp.D :=
  (Subgroup.closure_le _).mpr (fun _ hk => hyp.mem_D_of_mem_KSet hk)

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103):
K is normal in D, by §1 Lemma (b). -/
instance K_normal : (hyp.K.subgroupOf hyp.D).Normal := by
  simpa only [K, KSet, invertedBy] using
    (closure_invertedBy_subgroupOf_normal hyp.t_mul_t hyp.D_odd
      (fun x hx => hyp.t_conj_mem_D' hx))

/-- The closure construction of K has exactly the original inverted set as
its carrier. -/
@[simp] lemma coe_K : (hyp.K : Set G) = hyp.KSet := by
  obtain ⟨k, -, hk⟩ := hyp.exists_KSet_generator
  change (Subgroup.closure hyp.KSet : Set G) = hyp.KSet
  rw [← hk, Subgroup.closure_eq]

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2** (p. 103):
K is cyclic. -/
instance K_isCyclic : IsCyclic ↥hyp.K := by
  obtain ⟨k, -, hk⟩ := hyp.exists_KSet_generator
  have hK : hyp.K = Subgroup.zpowers k := by
    rw [K, ← hk, Subgroup.closure_eq]
  rw [hK]
  infer_instance

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
