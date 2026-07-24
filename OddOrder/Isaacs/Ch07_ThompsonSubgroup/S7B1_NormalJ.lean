/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7A2_NormalPThm75
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B1_NormalJ_Setup

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7B part 1: normal-J (Thm 7.6) Steps 1-6 (pp. 209-214)
-/


namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Step 6 main: `K := C_G(V)` is a `p`-group (mmd L3879-3884)

This is the heart of Step 6: for every prime `q ≠ p`, the action of any
Sylow `q`-subgroup `Q` of `K` on `Z(U) = Z(O_p(G))` (by conjugation) is
forced to be trivial via Cor 4.35 (`Q` fixes every element of order `p`
in `Z(U)`, namely all of `V`), so `Q ⊆ C_G(Z(U)) ⊆ C_G(Z(P)) = P`.  Then
`Q ⊆ P ∩ K`, but `Q` is a `q`-group and `P` is a `p`-group with `q ≠ p`,
forcing `Q = ⊥`.  Since all primes `q ≠ p` give trivial Sylow `q`-subgroups
of `K`, `K` is a `p`-group. -/

/-- The conjugation action of `Q ≤ K = C_G(V)` on `V = Ω₁ Z(U)` is trivial:
every element of `V` is fixed by every element of `Q`.  Pure unpacking of
`conj_fixes_omega1ZCenterOpCore_of_le_centralizer` into the action form needed
to apply Cor 4.35. -/
private theorem conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G}
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))
    (z : ↥(zCenterOpCoreSubgroup G p)) (hz_p : z ^ p = 1) (q : ↥Q) :
    (conjActionOnZCenterOpCoreSubgroup Q q) z = z := by
  -- (z : G) ∈ V := Ω₁ Z(U) since z ∈ Z(U) and z^p = 1.
  have hz_V : (z : G) ∈ omega1ZCenterOpCore G p := by
    rw [mem_omega1ZCenterOpCore]
    refine ⟨z.2, ?_⟩
    -- z^p = 1 in subtype ↥(Z(U)) ⇒ (z : G)^p = 1.
    have hzp_coe := congr_arg (fun x : ↥(zCenterOpCoreSubgroup G p) => (x : G)) hz_p
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hzp_coe
    exact hzp_coe
  -- Q ⊆ C_G(V), so (q : G) * (z : G) * (q : G)⁻¹ = (z : G).
  have hconj : (q : G) * (z : G) * (q : G)⁻¹ = (z : G) :=
    conj_fixes_omega1ZCenterOpCore_of_le_centralizer hQ_le_K q hz_V
  apply Subtype.ext
  -- (conjActionOnZCenterOpCoreSubgroup Q q) z = MulAut.conjNormal (q : G) z
  unfold conjActionOnZCenterOpCoreSubgroup
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  exact hconj

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
the centralizer of `Z(U)` in `G`.

Apply Cor 4.35 (`cor_4_35_for_zCenterOpCoreSubgroup`) with the conjugation action
of `Q` on `Z(U)`: `Q` is a `p'`-group, and `Q` fixes every order-`p` element of
`Z(U)` (these are the elements of `V = Ω₁ Z(U)`, and `Q ⊆ K = C_G(V)`).  This
yields `actionCommutator = ⊥`, i.e., `Q` acts trivially on `Z(U)`. -/
private theorem q_subgroup_in_K_le_centralizer_zCenter
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- (1) Q is a p'-group: q ≠ p prime + |Q| = q^k ⇒ p ∤ |Q|.
  have hQp' : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ_q
    rw [hk]
    intro hpdvd
    have hp_prime : p.Prime := Fact.out
    have hq_dvd_p : p ∣ q := hp_prime.dvd_of_dvd_pow hpdvd
    -- p ∣ q with p, q prime ⇒ p = q
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hq_dvd_p
    exact hqp this.symm
  -- (2) Apply Cor 4.35: the conjugation action of Q on Z(U) has actionCommutator = ⊥.
  have h_ac_bot :
      OddOrder.Isaacs.Ch04.actionCommutator (conjActionOnZCenterOpCoreSubgroup Q)
        = ⊥ :=
    cor_4_35_for_zCenterOpCoreSubgroup (conjActionOnZCenterOpCoreSubgroup Q) hQp'
      (fun z hz_p s => conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer hQ_le_K z hz_p s)
  -- (3) Translate "actionCommutator = ⊥" into "Q acts trivially":
  --     for all (qq : Q), (z : Z(U)), MulAut.conjNormal qq z = z.
  have h_trivial :
      ∀ qq : Q, ∀ z : ↥(zCenterOpCoreSubgroup G p),
        (conjActionOnZCenterOpCoreSubgroup Q qq) z = z :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp h_ac_bot
  -- (4) Convert to: Q ⊆ C_G(Z(U)) inside G.
  intro qq hqq_Q
  rw [Subgroup.mem_centralizer_iff]
  rintro z hz
  -- z ∈ Z(U) as Subgroup G ⇒ z is in zCenterOpCoreSubgroup, lifted from a z' in subtype.
  -- Apply h_trivial at (⟨qq, hqq_Q⟩ : ↥Q) and (⟨z, hz⟩ : ↥(Z(U))).
  have hcommute := h_trivial ⟨qq, hqq_Q⟩ ⟨z, hz⟩
  -- hcommute: (conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ = ⟨z, hz⟩
  -- Unfold: MulAut.conjNormal (qq) ⟨z, hz⟩ = ⟨z, hz⟩, i.e., qq * z * qq⁻¹ = z.
  have hcommute_coe : ((conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ : G)
      = (⟨z, hz⟩ : ↥(zCenterOpCoreSubgroup G p)) := by
    rw [hcommute]
  unfold conjActionOnZCenterOpCoreSubgroup at hcommute_coe
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply] at hcommute_coe
  -- hcommute_coe : qq * z * qq⁻¹ = z. Rearrange to z * qq = qq * z.
  calc z * qq = (qq * z * qq⁻¹) * qq := by rw [hcommute_coe]
    _ = qq * z := by group

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
`P`, under hypothesis (v) `P = C_G(Z(P))` and `O_{p'}(G) = ⊥`.

Combines `q_subgroup_in_K_le_centralizer_zCenter` (yielding `Q ⊆ C_G(Z(U))`) with
the chain `Z(P) ⊆ Z(U)` (`center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot`)
+ contravariant `centralizer_le` + hypothesis (v) `C_G(Z(P)) = P`. -/
private theorem q_subgroup_in_K_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ (P : Subgroup G) := by
  -- Q ⊆ C_G(Z(U)).
  have hQ_cZU : Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) :=
    q_subgroup_in_K_le_centralizer_zCenter hq_prime hqp hQ_q hQ_le_K
  -- Z(P) ⊆ Z(U), so C_G(Z(U)) ⊆ C_G(Z(P)) = P.
  have hZP_le_ZU :
      ((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype : Subgroup G) ≤
        zCenterOpCoreSubgroup G p :=
    center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot hOp' P
  have hC_ZU_le_C_ZP :
      Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) ≤
        Subgroup.centralizer
          (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G) :=
    Subgroup.centralizer_le hZP_le_ZU
  rw [h_centralizer_center] at hC_ZU_le_C_ZP
  exact hQ_cZU.trans hC_ZU_le_C_ZP

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is trivial,
under the Thm 7.6 hypotheses (iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`.

From `q_subgroup_in_K_le_sylow` we get `Q ⊆ P`.  Then `Q` is a `q`-group inside a
`p`-group `P` with `q ≠ p`, forcing `Q = ⊥` by coprimality of cardinalities. -/
private theorem q_subgroup_in_K_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q = ⊥ := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hQ_le_P : Q ≤ (P : Subgroup G) :=
    q_subgroup_in_K_le_sylow hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- Q is a q-group and Q ≤ P which is a p-group; coprime ⇒ |Q| = 1.
  have hP_p : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hQ_p : IsPGroup p Q := hP_p.to_le hQ_le_P
  obtain ⟨a, hQa⟩ := IsPGroup.iff_card.mp hQ_q
  obtain ⟨b, hQb⟩ := IsPGroup.iff_card.mp hQ_p
  have hp_prime : p.Prime := Fact.out
  have hQ_card : Nat.card Q = 1 := by
    have h_eq : q ^ a = p ^ b := hQa.symm.trans hQb
    by_contra h_ne
    have ha_pos : 1 ≤ a := by
      rcases a with _ | a'
      · -- a = 0 ⇒ |Q| = q^0 = 1, contradicting h_ne.
        exfalso
        apply h_ne
        rw [hQa, pow_zero]
      · exact Nat.le_add_left 1 a'
    have hq_dvd_qa : q ∣ q ^ a := dvd_pow_self q (Nat.one_le_iff_ne_zero.mp ha_pos)
    rw [h_eq] at hq_dvd_qa
    have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_qa
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp hq_dvd_p
    exact hqp this
  exact Subgroup.eq_bot_of_card_eq Q hQ_card

/-- **Isaacs Thm 7.6 Step 6 main** (mmd L3879-3884): under hypotheses
(iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`, `K := C_G(V)` is a `p`-group.

Proof: for every `g ∈ K`, the order `orderOf g` has only `p` as a prime divisor.
Indeed, if some prime `q ≠ p` divided `orderOf g = n`, then `g^(n/q) ∈ K` would
generate a `q`-subgroup of order `q`, which is forced to be trivial by
`q_subgroup_in_K_eq_bot`, contradicting `orderOf (g^(n/q)) = q > 1`.

Hence `orderOf g` is a power of `p` for every `g ∈ K`, so `K` is a `p`-group. -/
theorem centralizer_omega1ZCenterOpCore_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) := by
  -- Use IsPGroup.iff_orderOf: K is a p-group iff every g ∈ K has order a power of p.
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg_K⟩
  set K : Subgroup G := Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) with hK_def
  -- Step (1): orderOf ⟨g, hg_K⟩ in K = orderOf g in G.
  set n : ℕ := orderOf g with hn_def
  have h_ord_eq : orderOf (⟨g, hg_K⟩ : ↥K) = n := Subgroup.orderOf_mk g hg_K
  rw [h_ord_eq]
  -- Reduce to: n is a power of p. Argue by contradiction.
  by_contra hno_pk
  push Not at hno_pk
  have hn_pos : 0 < n := orderOf_pos g
  have hp_prime : p.Prime := Fact.out
  -- ∃ q prime, q ≠ p, q ∣ n.
  have h_exists_q : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ n := by
    by_contra h_all
    push Not at h_all
    suffices ∀ q ∈ n.primeFactorsList, q = p by
      have : ∃ k, n = p ^ k := by
        refine ⟨n.primeFactorsList.length, ?_⟩
        rw [← List.prod_replicate, ← List.eq_replicate_of_mem this,
          Nat.prod_primeFactorsList hn_pos.ne']
      obtain ⟨k, hk⟩ := this
      exact hno_pk _ hk
    intro q hq
    obtain ⟨hq_prime, hq_dvd⟩ := (Nat.mem_primeFactorsList hn_pos.ne').mp hq
    by_contra hqp
    exact h_all q hq_prime hqp hq_dvd
  obtain ⟨q, hq_prime, hqp, hq_dvd_n⟩ := h_exists_q
  -- Set h := g^(n/q). It has order q.
  set h_elem : G := g ^ (n / q) with h_elem_def
  have hh_K : h_elem ∈ K := K.pow_mem hg_K _
  have hgq_pow_q : h_elem ^ q = 1 := by
    rw [h_elem_def, ← pow_mul, Nat.div_mul_cancel hq_dvd_n, pow_orderOf_eq_one]
  -- h ≠ 1 because n/q < n and orderOf g = n.
  have hh_ne_one : h_elem ≠ 1 := by
    intro h_eq
    have h_div : n ∣ (n / q) := by
      rw [hn_def]; exact orderOf_dvd_of_pow_eq_one h_eq
    have hq_two : 2 ≤ q := hq_prime.two_le
    have hnq_lt : n / q < n := Nat.div_lt_self hn_pos hq_two
    have hnq_pos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn_pos hq_dvd_n) hq_prime.pos
    have : n ≤ n / q := Nat.le_of_dvd hnq_pos h_div
    omega
  -- orderOf h = q.
  have hh_ord : orderOf h_elem = q := by
    have h_ord_dvd : orderOf h_elem ∣ q := orderOf_dvd_of_pow_eq_one hgq_pow_q
    rcases (Nat.dvd_prime hq_prime).mp h_ord_dvd with h1 | hqeq
    · exact absurd (orderOf_eq_one_iff.mp h1) hh_ne_one
    · exact hqeq
  -- Q := Subgroup.zpowers h is a q-group of K.
  have hQ_q : IsPGroup q (Subgroup.zpowers h_elem) := by
    haveI : Fact q.Prime := ⟨hq_prime⟩
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, hh_ord, pow_one]
  have hQ_le_K : (Subgroup.zpowers h_elem) ≤ K := by
    rw [Subgroup.zpowers_le]; exact hh_K
  -- Apply q_subgroup_in_K_eq_bot: ⟨h⟩ = ⊥.
  have hQ_bot : Subgroup.zpowers h_elem = ⊥ :=
    q_subgroup_in_K_eq_bot hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- But h ∈ ⟨h⟩ = ⊥ ⇒ h = 1, contradicting hh_ne_one.
  have : h_elem ∈ Subgroup.zpowers h_elem := Subgroup.mem_zpowers _
  rw [hQ_bot, Subgroup.mem_bot] at this
  exact hh_ne_one this

/-- **Isaacs Thm 7.6 Step 6 faithfulness** (mmd L3884): `K̄ = ⊥` in `Ḡ` given
`K ≤ U`.  This is the final Step 6 conclusion: the Ḡ-action on V is faithful
because its kernel `K̄ = (K.map mk')` is trivial. -/
theorem centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hK_le_U : Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) ≤
        OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  -- Goal: K ≤ oPiCore {p} G
  intro x hx
  have hx_U : x ∈ OddOrder.Isaacs.Ch01.opCore p G := hK_le_U hx
  rwa [show OddOrder.Isaacs.Ch01.opCore p G =
        OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G from
      (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm] at hx_U

/-! ### Step 7 counting argument: `|V : V ∩ A| ≤ p` (mmd L3886-3892)

The book's Step 7 derives a counting bound on `V := Ω₁ Z(O_p(G))`:

> Write `D = U ∩ A` and `E = V ∩ A`.  Then `|V:E| = |V:V∩D| = |VD:D|`.  Now
> `D` is elementary abelian in `U`, and `V` is a central elementary abelian
> subgroup of `U`, so `VD` is elementary abelian.  By `A ∈ E(P)`, `|VD| ≤ |A|`,
> hence `|VD:D| ≤ |A:D| = |Ā| = p`.

We package this combinatorial step as `omega1ZCenterOpCore_relIndex_inter_A_le`,
isolating from the broader Goldschmidt argument the part that only needs
elementary-abelian structure, `V ≤ centralizer U`, and the maximality of
`A ∈ maxElemAbelianIn P p`.

The hypothesis `|A : A ⊓ U| ≤ p` is supplied externally (it is the Step 5
conclusion `|Ā| = p`). -/

/-- **Subgroup `V ⊔ D` is contained in its own centralizer** when `V`
centralizes `D`, `V` is commutative, and `D` is commutative.

This packages `V ⊔ D ≤ centralizer (V ⊔ D)`, i.e., `V ⊔ D` is abelian. -/
private theorem sup_le_centralizer_self_of_centralizing
    {G : Type*} [Group G] {V D : Subgroup G}
    (hV_comm : ∀ x y : ↥V, x * y = y * x)
    (hD_comm : ∀ x y : ↥D, x * y = y * x)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G) ≤ Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
  -- Strategy: show V ∪ D ⊆ centralizer (V ⊔ D), then by closure of centralizer.
  -- centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- V ⊔ D = closure (V ∪ D), giving the conclusion.
  have h_VuD_in_cent : (V : Set G) ∪ (D : Set G) ⊆
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
    -- Show each element of V ∪ D commutes with every element of V ⊔ D.
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    -- x ∈ V ⊔ D ⟺ x ∈ closure (V ∪ D). Use closure_induction.
    have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
      rwa [← Subgroup.sup_eq_closure]
    clear hx
    -- w ∈ V ∪ D, x ∈ closure (V ∪ D). Goal: x * w = w * x.
    induction hx_clos using Subgroup.closure_induction with
    | mem y hy =>
      -- Both w and y are in V ∪ D, show they commute.
      rcases hw with hw_V | hw_D
      · rcases hy with hy_V | hy_D
        · have := hV_comm ⟨y, hy_V⟩ ⟨w, hw_V⟩
          exact congr_arg Subtype.val this
        · -- w ∈ V, y ∈ D: hVD says V centralizes D.
          have h_w_cent := hVD hw_V
          rw [Subgroup.mem_centralizer_iff] at h_w_cent
          exact h_w_cent y hy_D
      · rcases hy with hy_V | hy_D
        · -- w ∈ D, y ∈ V: hVD says V centralizes D.
          have h_y_cent := hVD hy_V
          rw [Subgroup.mem_centralizer_iff] at h_y_cent
          exact (h_y_cent w hw_D).symm
        · have := hD_comm ⟨y, hy_D⟩ ⟨w, hw_D⟩
          exact congr_arg Subtype.val this
    | one => rw [one_mul, mul_one]
    | mul a b _ _ ha hb =>
      calc (a * b) * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [ha]
        _ = w * (a * b) := by group
    | inv a _ ha =>
      have hcomm : a * w = w * a := ha
      calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [hcomm]
        _ = w * a⁻¹ := by group
  -- Now centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- The result follows because V ⊔ D = closure (V ∪ D).
  intro x hx
  -- Convert hx to closure form, apply h_VuD_in_cent + closure_le.
  have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
    rwa [← Subgroup.sup_eq_closure]
  exact (Subgroup.closure_le _).mpr h_VuD_in_cent hx_clos

/-- **VD is elementary abelian**: if `V` centralizes `D`, both `V` and `D` are
elementary abelian `p`-groups, and `V` is normal in `G`, then `V ⊔ D` is also
elementary abelian.

Proof: by `mul_normal`, every element of `V ⊔ D` is `v * d` for some `v ∈ V`,
`d ∈ D`.  Commutativity in `V ⊔ D` and exponent `p` both follow from `V` and
`D` commuting pointwise. -/
private theorem sup_isElementaryAbelian_of_centralizing
    {G : Type*} [Group G] {p : ℕ} {V D : Subgroup G} [V.Normal]
    (hV : V.IsElementaryAbelian p) (hD : D.IsElementaryAbelian p)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G).IsElementaryAbelian p := by
  have h_VD_comm : (V ⊔ D : Subgroup G) ≤
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) :=
    sup_le_centralizer_self_of_centralizing hV.1 hD.1 hVD
  -- Element decomposition: every element of V ⊔ D is v*d for v ∈ V, d ∈ D.
  have h_decomp : ∀ x ∈ (V ⊔ D : Subgroup G), ∃ v ∈ V, ∃ d ∈ D, (v * d : G) = x := by
    intro x hx
    have h_mul : (↑(V ⊔ D) : Set G) = V * D := Subgroup.normal_mul V D
    have hx_set : x ∈ (↑(V ⊔ D) : Set G) := hx
    rw [h_mul] at hx_set
    obtain ⟨v, hv, d, hd, hvd⟩ := hx_set
    exact ⟨v, hv, d, hd, hvd⟩
  refine ⟨?_, ?_⟩
  · -- Commutativity in V ⊔ D.
    intro x y
    apply Subtype.ext
    have hxy_cent := h_VD_comm x.2
    rw [Subgroup.mem_centralizer_iff] at hxy_cent
    have : (y : G) * x = x * y := hxy_cent y y.2
    exact this.symm
  · -- Exponent p.  In V ⊔ D, every element w has w^p = 1.
    intro w
    apply Subtype.ext
    change (w.val : G) ^ p = 1
    -- w = v * d for some v ∈ V, d ∈ D.
    obtain ⟨v, hv_V, d, hd_D, hvd_eq⟩ := h_decomp w.val w.2
    rw [← hvd_eq]
    -- (v * d)^p = v^p * d^p (since v and d commute), and v^p = 1, d^p = 1.
    have hv_d_comm : v * d = d * v := by
      have hv_cent := hVD hv_V
      rw [Subgroup.mem_centralizer_iff] at hv_cent
      exact (hv_cent d hd_D).symm
    have hCom : Commute v d := hv_d_comm
    have : (v * d) ^ p = v ^ p * d ^ p := Commute.mul_pow hCom p
    rw [this]
    have hv_p : v ^ p = 1 := by
      have := hV.2 ⟨v, hv_V⟩
      exact congr_arg Subtype.val this
    have hd_p : d ^ p = 1 := by
      have := hD.2 ⟨d, hd_D⟩
      exact congr_arg Subtype.val this
    rw [hv_p, hd_p, mul_one]

/-- **Isaacs Thm 7.6 Step 7** (mmd L3886-3892): `|V : V ∩ A| ≤ p` for any
`A ∈ maxElemAbelianIn P p`, assuming `|A : A ∩ U| ≤ p` (Step 5).

`A.relIndex V` is `|V : V ⊓ A|` in book notation
(`(A.subgroupOf V).index = |V/(A ⊓ V)|`).  Similarly,
`(A ⊓ U).relIndex A = |A : A ⊓ U|` is the Step-5 bound.

The book's argument:
1. Set `D = U ∩ A` and `E = V ∩ A`.  Observe `V ⊆ U` (so `V ∩ A = V ∩ D`).
2. `D` is elementary abelian (sub of `A`).
3. `V` is elementary abelian and central in `U`, so `V ⊆ centralizer D`.
4. `VD := V ⊔ D` is elementary abelian (`sup_isElementaryAbelian_of_centralizing`).
5. `VD ≤ P` (since `V ≤ U ≤ P` and `D ≤ A ≤ P`).
6. By maximality `A ∈ E(P)`, `|VD| ≤ |A|`, so `|VD : D| ≤ |A : D|`.
7. By second isomorphism (V normal, V centralizes D), `|V : V ∩ D| = |VD : D|`.
8. Combine: `|V : V ∩ A| = |V : V ∩ D| = |VD : D| ≤ |A : D| ≤ p`. -/
theorem omega1ZCenterOpCore_relIndex_inter_A_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hA : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p G).relIndex A ≤ p) :
    A.relIndex (omega1ZCenterOpCore G p) ≤ p := by
  classical
  set V : Subgroup G := omega1ZCenterOpCore G p with hV_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set D : Subgroup G := A ⊓ U with hD_def
  -- Basic facts.
  have hV_le_U : V ≤ U := omega1ZCenterOpCore_le_opCore
  have hA_P : A ≤ (P : Subgroup G) := hA.1
  have hU_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  have hA_el : A.IsElementaryAbelian p := hA.2.1
  have hD_el : D.IsElementaryAbelian p :=
    inf_isElementaryAbelian_of_isElementaryAbelian hA_el U
  have hV_el : V.IsElementaryAbelian p := omega1ZCenterOpCore_isElementaryAbelian
  have hV_cent_U : V ≤ Subgroup.centralizer (U : Set G) :=
    omega1ZCenterOpCore_centralizes_opCore
  have hD_le_U : D ≤ U := inf_le_right
  have hD_le_A : D ≤ A := inf_le_left
  have hV_cent_D : V ≤ Subgroup.centralizer (D : Set G) :=
    hV_cent_U.trans (Subgroup.centralizer_le hD_le_U)
  -- V ⊔ D is elementary abelian.
  haveI : V.Normal := omega1ZCenterOpCore_normal
  have hVD_el : (V ⊔ D : Subgroup G).IsElementaryAbelian p :=
    sup_isElementaryAbelian_of_centralizing hV_el hD_el hV_cent_D
  -- V ⊔ D ≤ P.
  have hVD_le_P : (V ⊔ D : Subgroup G) ≤ (P : Subgroup G) := by
    rw [sup_le_iff]
    exact ⟨hV_le_U.trans hU_P, hD_le_A.trans hA_P⟩
  -- Maximality of A: |V ⊔ D| ≤ |A|.
  have hVD_card_le_A : Nat.card (V ⊔ D : Subgroup G) ≤ Nat.card A :=
    hA.2.2 (V ⊔ D) hVD_le_P hVD_el
  -- A.relIndex V = |V : V ∩ A| (book notation).  Rewrite via V ⊓ A = V ⊓ D.
  -- V ⊓ A = V ⊓ U ⊓ A = V ⊓ (U ⊓ A) = V ⊓ (A ⊓ U) = V ⊓ D since V ≤ U.
  have hVA_eq_VD : V ⊓ A = V ⊓ D := by
    have h_VU : V ⊓ U = V := inf_eq_left.mpr hV_le_U
    rw [hD_def, inf_comm A U, ← inf_assoc, h_VU]
  have hAV_eq : A.relIndex V = D.relIndex V := by
    -- A.relIndex V = (A ⊓ V).relIndex V via inf_relIndex_right.
    -- Same for D. Use V ⊓ A = V ⊓ D, i.e., A ⊓ V = D ⊓ V (by inf_comm).
    have h1 : A.relIndex V = (A ⊓ V).relIndex V := (Subgroup.inf_relIndex_right A V).symm
    have h2 : D.relIndex V = (D ⊓ V).relIndex V := (Subgroup.inf_relIndex_right D V).symm
    have h_inf_comm : A ⊓ V = D ⊓ V := by
      rw [inf_comm A V, inf_comm D V]; exact hVA_eq_VD
    rw [h1, h2, h_inf_comm]
  rw [hAV_eq]
  -- Second isomorphism: V / (D ⊓ V) ≅ (V ⊔ D) / D, requiring V ≤ normalizer D.
  -- V centralizes D, so V ≤ centralizer D ≤ normalizer D.
  have hV_norm_D : V ≤ Subgroup.normalizer D := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hv_cent : v ∈ Subgroup.centralizer (D : Set G) := hV_cent_D hv
    have hv_inv_cent : v⁻¹ ∈ Subgroup.centralizer (D : Set G) := Subgroup.inv_mem _ hv_cent
    constructor
    · intro hy
      have hyv : y * v = v * y := Subgroup.mem_centralizer_iff.mp hv_cent y hy
      have heq : v * y * v⁻¹ = y := by
        calc v * y * v⁻¹ = (y * v) * v⁻¹ := by rw [hyv]
          _ = y := by group
      rw [heq]
      exact hy
    · intro hyc
      have hcomm := Subgroup.mem_centralizer_iff.mp hv_inv_cent (v * y * v⁻¹) hyc
      have heq : y = v⁻¹ * (v * y * v⁻¹) * v := by group
      have hpush : v⁻¹ * (v * y * v⁻¹) * v = v * y * v⁻¹ := by
        calc v⁻¹ * (v * y * v⁻¹) * v
            = (v * y * v⁻¹) * v⁻¹ * v := by rw [← hcomm]
          _ = v * y * v⁻¹ := by group
      rw [heq, hpush]
      exact hyc
  set VD : Subgroup G := V ⊔ D with hVD_def
  have hD_le_VD : D ≤ VD := hVD_def ▸ le_sup_right
  -- Apply second iso: |V/(D ⊓ V).subgroupOf V| = |VD/D.subgroupOf VD|.
  letI hD_normal_in_V : (D.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hV_norm_D
  letI hD_normal_in_VD : (D.subgroupOf VD).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hV_norm_D
  have h_card_quot_V : Nat.card (V ⧸ D.subgroupOf V) =
      Nat.card (VD ⧸ D.subgroupOf VD) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient V D hV_norm_D).toEquiv
  have h_card_eq : D.relIndex V = D.relIndex VD := by
    unfold Subgroup.relIndex Subgroup.index
    exact h_card_quot_V
  rw [h_card_eq]
  -- Lagrange: |VD| = D.relIndex VD * |D|, |A| = U.relIndex A * |D|.
  have hD_card_pos : 0 < Nat.card D := Nat.card_pos
  have h_lag_VD : Nat.card VD = D.relIndex VD * Nat.card D := by
    have h_index_mul_card : (D.subgroupOf VD).index *
        Nat.card (D.subgroupOf VD) = Nat.card VD :=
      Subgroup.index_mul_card _
    have hD_card_eq : Nat.card (D.subgroupOf VD) = Nat.card D := by
      have h_map_eq : ((D.subgroupOf VD : Subgroup VD).map VD.subtype : Subgroup G) = D :=
        Subgroup.map_subgroupOf_eq_of_le hD_le_VD
      have h_card : Nat.card (D.subgroupOf VD) =
          Nat.card ((D.subgroupOf VD : Subgroup VD).map VD.subtype) :=
        (Subgroup.card_map_of_injective VD.subtype_injective).symm
      rw [h_card, h_map_eq]
    rw [show D.relIndex VD = (D.subgroupOf VD).index from rfl,
        ← h_index_mul_card, hD_card_eq]
  have h_lag_A : Nat.card A = U.relIndex A * Nat.card D := by
    have h_index_mul_card : (U.subgroupOf A).index *
        Nat.card (U.subgroupOf A) = Nat.card A :=
      Subgroup.index_mul_card _
    have hU_subgrpOf_card : Nat.card (U.subgroupOf A) = Nat.card D := by
      -- (U.subgroupOf A).map A.subtype = U ⊓ A = A ⊓ U = D.
      have h_map_eq : ((U.subgroupOf A : Subgroup A).map A.subtype : Subgroup G) = U ⊓ A :=
        Subgroup.subgroupOf_map_subtype U A
      have h_card : Nat.card (U.subgroupOf A) =
          Nat.card ((U.subgroupOf A : Subgroup A).map A.subtype) :=
        (Subgroup.card_map_of_injective A.subtype_injective).symm
      rw [h_card, h_map_eq, inf_comm, ← hD_def]
    rw [show U.relIndex A = (U.subgroupOf A).index from rfl,
        ← h_index_mul_card, hU_subgrpOf_card]
  -- D.relIndex VD * |D| = |VD| ≤ |A| = U.relIndex A * |D|.
  have hVD_card_le_A' : Nat.card VD ≤ Nat.card A := hVD_card_le_A
  have hmul_le : D.relIndex VD * Nat.card D ≤ U.relIndex A * Nat.card D := by
    rw [← h_lag_VD, ← h_lag_A]
    exact hVD_card_le_A'
  exact (Nat.le_of_mul_le_mul_right hmul_le hD_card_pos).trans hA_D_relIndex

/-! ### Step 7-8: closing reductions (mmd L3884-3896)

Once Step 5-6 produce the triviality of the `A`-action on `V = Z(L)`, the book:

* (Step 7) Combines `[A, V] = 1` with hypothesis (v) `P = C_G(Z(P))` and the
  maximality of `A ∈ E(P)` to force `A ⊆ L`, contradicting `A ⊄ L`.
* (Step 8) From Step 2's conclusion `J(P) ≤ L`, applies Thm 7.2
  (`thompsonJ_eq_of_le_of_le`) to get `J(L) = J(P)`, then uses that `J(L)` is
  characteristic in `L` and `L` is characteristic in `G` to conclude
  `J(P) ⊴ G`.

The Step 7 contradiction itself is a delicate counting argument over `E(P)`
combined with the action analysis; we defer it.  Step 8 only needs the Thm 7.2
bridge, which we record here. -/

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893): if `J(P) ≤ L` and `L ≤ P` then
`J(L) = J(P)`, the consequence of Thm 7.2 needed in the closing step. -/
private theorem thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
  Subgroup.thompsonJ_eq_of_le_of_le h_le (OddOrder.Isaacs.Ch01.opCore_le P)

/-- **Conjugating `maxElemAbelianIn L p` by `g ∈ G`** when `L` is `G`-normal.

If `L ⊴ G` and `E ∈ maxElemAbelianIn L p`, then for any `g : G`, the conjugate
`g E g⁻¹` is again in `maxElemAbelianIn L p`.  Pure normality + the fact that
conjugation is an isomorphism (preserves cardinality and elementary-abelian
property). -/
private theorem maxElemAbelianIn_conj_mem
    {G : Type*} [Group G] {L E : Subgroup G} [hL : L.Normal] {p : ℕ}
    (hE : E ∈ Subgroup.maxElemAbelianIn L p) (g : G) :
    E.map (MulAut.conj g).toMonoidHom ∈ Subgroup.maxElemAbelianIn L p := by
  refine ⟨?_, ?_, ?_⟩
  · -- E.map (conj g) ≤ L
    rintro _ ⟨e, he_E, rfl⟩
    have he_L : e ∈ L := hE.1 he_E
    change g * e * g⁻¹ ∈ L
    exact hL.conj_mem _ he_L g
  · -- E.map (conj g) is elementary abelian
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩ ⟨_, ⟨b, hb_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹)
      have habcomm : a * b = b * a := by
        have h := hE.2.1.comm ⟨a, ha_E⟩ ⟨b, hb_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) * (g * b * g⁻¹)
          = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [habcomm]
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) ^ p = 1
      have ha_p : a ^ p = 1 := by
        have h := hE.2.1.pow_eq_one ⟨a, ha_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) ^ p
          = g * a ^ p * g⁻¹ := by
            rw [conj_pow]
        _ = g * 1 * g⁻¹ := by rw [ha_p]
        _ = 1 := by group
  · -- E.map (conj g) is of maximum cardinality
    intro F hF_L hF_el
    have hF_conj_card : Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) =
        Nat.card F :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    have hE_conj_card : Nat.card (E.map (MulAut.conj g).toMonoidHom : Subgroup G) =
        Nat.card E :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    rw [hE_conj_card]
    have hF_inv : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ L := by
      rintro _ ⟨e, he_F, rfl⟩
      have he_L : e ∈ L := hF_L he_F
      change g⁻¹ * e * g⁻¹⁻¹ ∈ L
      exact hL.conj_mem _ he_L g⁻¹
    have hF_inv_el : (F.map (MulAut.conj g⁻¹).toMonoidHom).IsElementaryAbelian p := by
      refine ⟨?_, ?_⟩
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩ ⟨_, ⟨b, hb_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹) =
          (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹)
        have habcomm : a * b = b * a := by
          have h := hF_el.comm ⟨a, ha_F⟩ ⟨b, hb_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹)
            = g⁻¹ * (a * b) * g⁻¹⁻¹ := by group
          _ = g⁻¹ * (b * a) * g⁻¹⁻¹ := by rw [habcomm]
          _ = (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹) := by group
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) ^ p = 1
        have ha_p : a ^ p = 1 := by
          have h := hF_el.pow_eq_one ⟨a, ha_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) ^ p
            = g⁻¹ * a ^ p * g⁻¹⁻¹ := by rw [conj_pow]
          _ = g⁻¹ * 1 * g⁻¹⁻¹ := by rw [ha_p]
          _ = 1 := by group
    have := hE.2.2 (F.map (MulAut.conj g⁻¹).toMonoidHom) hF_inv hF_inv_el
    rw [hF_conj_card] at this
    exact this

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893-3896): under the running hypotheses, the
**conditional conclusion** of Step 2 (`J(P) ≤ L`) yields normality of `J(P)` in `G`.

Strategy: from `J(P) ≤ L = O_p(G)` and the Step 2 / Thm 7.2 bridge, `J(L) = J(P)`.
Then `g ∈ G`, `E ∈ E(L)` ⇒ `g E g⁻¹ ∈ E(L)` (`maxElemAbelianIn_conj_mem`), so the
iSup defining `J(L)` is `G`-stable. -/
theorem normal_thompsonJ_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by
  -- Replace J(P) by J(L) using Thm 7.2.
  have hJLP : Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
    thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore P h_le
  rw [← hJLP]
  -- It suffices to show: ∀ g ∈ G, (J(L)).map (conj g) ≤ J(L).
  refine ⟨?_⟩
  intro n hn g
  -- Reduce to: g * J(L) * g⁻¹ ≤ J(L).
  -- We show `(J(L)).map (MulAut.conj g).toMonoidHom ≤ J(L)`.
  have h_map_le :
      (Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom ≤
      Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p := by
    rw [show Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p
          = ⨆ E ∈ Subgroup.maxElemAbelianIn
            (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p, E from rfl,
        Subgroup.map_iSup]
    refine iSup_le fun E => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hE_mem => ?_
    -- E.map (conj g) ∈ maxElemAbelianIn L p, so E.map (conj g) ≤ J(L).
    have h_conj_mem :=
      maxElemAbelianIn_conj_mem (L := OddOrder.Isaacs.Ch01.opCore p G) hE_mem g
    exact Subgroup.le_thompsonJ_of_mem_maxElemAbelianIn h_conj_mem
  have : g * n * g⁻¹ ∈ (Subgroup.thompsonJ
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom := by
    refine ⟨n, hn, ?_⟩
    change g * n * g⁻¹ = g * n * g⁻¹
    rfl
  exact h_map_le this

/-! ### Step 7: contradiction giving `J(P) ≤ L` (mmd L3884-3892)

The book's Step 7 combines:

* The Step 5-6 conclusion: `A` acts trivially on `V := Z(O_p(G))`, i.e.,
  `[A, V] = 1` (`A` and `V` commute pointwise).
* The Step 1 conclusion: `Z(P) ≤ Z(L)` (Z(P) sits inside Z(L) since
  Z(P) commutes with all of L).
* The hypothesis (v): `P = C_G(Z(P))`.
* The maximality of `A ∈ E(P)`.

The combined counting argument forces `A ⊆ L`, contradicting the choice of
`A ⊄ L`.  This is the most delicate part of the Goldschmidt-style proof; the
Step 7 conclusion is **landed as the proved theorem**
`omega1ZCenterOpCore_relIndex_inter_A_le`, consumed by Step 8's wrap-up in
`S7B2_NormalJ_PComplement`.  (Historical tracking issue 0036 is closed.) -/


end OddOrder.Isaacs.Ch07
