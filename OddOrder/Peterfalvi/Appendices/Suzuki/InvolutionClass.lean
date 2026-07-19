/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.Basic

/-!
# Peterfalvi Part II, Ch. I §1: the involution class (Props 2–3)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §1, pp. 100–101.

Propositions 2 and 3 of Ch. I §1, building on the hypotheses (A1)–(A3) and
Proposition 1 from `Suzuki.Basic`:

* Prop 2 (a): for `s ∈ H ∩ I` and `u ∈ I - (H ∩ I)`, `su` has odd order;
* Prop 2 (b): `I` is a single conjugacy class of `G`;
* Prop 2 (c): for an involution `s ∈ Q`, `u ↦ s^u` permutes `I - (H ∩ I)`;
* Prop 2 (d): `#{u ∈ I | H^u = H^t} = |H ∩ I|`;
* Prop 3: `|K| = |H ∩ I|`, and `s^K = H ∩ I` for `s ∈ H ∩ I`.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Chapter I §1, Proposition 2 (pp. 100–101) -/

/-- Every element of `H` of order dividing `2` lies in `Q` (as `H/Q ≅ D`
has odd order).  In particular `H ∩ I = Q ∩ I`. -/
lemma mem_Q_of_sq_eq_one_of_mem_H {s : G} (hsH : s ∈ hyp.H) (hs2 : s ^ 2 = 1) :
    s ∈ hyp.Q := by
  haveI hnorm : (hyp.Q.subgroupOf hyp.H).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact hyp.Q_normal_in_H h h.2 n hn
  -- `|H ⧸ Q| = |D|` is odd
  have hcard_sub : Nat.card (hyp.Q.subgroupOf hyp.H) = Nat.card hyp.Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q_le_H).toEquiv
  have hidx : (hyp.Q.subgroupOf hyp.H).index = Nat.card hyp.D := by
    have h1 := (hyp.Q.subgroupOf hyp.H).card_mul_index
    rw [hcard_sub, hyp.card_H_eq] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  -- the image of `s` in `H ⧸ Q` has order dividing both `2` and the odd `|D|`
  set s' : hyp.H := ⟨s, hsH⟩ with hs'
  have hs'2 : s' ^ 2 = 1 := Subtype.ext (by push_cast; exact hs2)
  have hdvd2 : orderOf ((QuotientGroup.mk' (hyp.Q.subgroupOf hyp.H)) s') ∣ 2 :=
    (orderOf_map_dvd _ s').trans (orderOf_dvd_of_pow_eq_one hs'2)
  have hdvdD : orderOf ((QuotientGroup.mk' (hyp.Q.subgroupOf hyp.H)) s') ∣
      Nat.card hyp.D := by
    rw [← hidx, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h1 : orderOf ((QuotientGroup.mk' (hyp.Q.subgroupOf hyp.H)) s') = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hyp.D_odd) hdvd2 hdvdD
  have hker : s' ∈ (QuotientGroup.mk' (hyp.Q.subgroupOf hyp.H)).ker := by
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
    exact h1
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hker
  exact hker

/-- **Peterfalvi Part II, Ch. I Prop 2 (a)** (p. 100) — if `s ∈ H ∩ I` and
`u ∈ I - (H ∩ I)`, then `su` has odd order.  (If the order were even, the
involution `w ∈ ⟨su⟩` would be centralized by both `s` and `u`; by Prop 1(b)
first `w ∈ H` — hence `w ∈ Q` — and then `u ∈ H`, a contradiction.) -/
lemma odd_orderOf_mul_involution {s u : G} (hsH : s ∈ hyp.H) (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) (hu2 : u ^ 2 = 1) (huH : u ∉ hyp.H) :
    Odd (orderOf (s * u)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hss : s * s = 1 := by rw [← sq]; exact hs2
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hn_pos : 0 < orderOf (s * u) := orderOf_pos _
  obtain ⟨m, hm⟩ := hodd
  -- the involution `w = (su)^m` of `⟨su⟩`
  set w : G := (s * u) ^ m with hw
  have hw2 : w ^ 2 = 1 := by
    rw [hw, ← pow_mul, mul_two, ← hm, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hwinv : w⁻¹ = w :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hw2)
  -- `s` and `u` invert `su`, hence centralize `w`
  have hconj_s : s * (s * u) * s⁻¹ = (s * u)⁻¹ := by
    rw [hsinv, mul_inv_rev, huinv, hsinv]
    calc s * (s * u) * s = s * s * (u * s) := by group
      _ = u * s := by rw [hss, one_mul]
  have hconj_u : u * (s * u) * u⁻¹ = (s * u)⁻¹ := by
    rw [huinv, mul_inv_rev, huinv, hsinv]
    calc u * (s * u) * u = (u * s) * (u * u) := by group
      _ = u * s := by rw [huu, mul_one]
  have hs_w : s * w * s⁻¹ = w := by
    rw [hw, ← conj_pow, hconj_s, inv_pow, ← hw, hwinv]
  have hu_w : u * w * u⁻¹ = w := by
    rw [hw, ← conj_pow, hconj_u, inv_pow, ← hw, hwinv]
  have hcomm_ws : w * s = s * w := by
    have h2 := congrArg (fun z : G => z * s) hs_w
    simpa [mul_assoc, hsinv, hss] using h2.symm
  have hcomm_wu : w * u = u * w := by
    have h2 := congrArg (fun z : G => z * u) hu_w
    simpa [mul_assoc, huinv, huu] using h2.symm
  -- `w ∈ C_G(s) ≤ H` (Prop 1(b)), hence `w ∈ Q`
  have hsQ : s ∈ hyp.Q := hyp.mem_Q_of_sq_eq_one_of_mem_H hsH hs2
  have hwH : w ∈ hyp.H :=
    hyp.centralizer_le_H_of_mem_Q hsQ hs1
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm_ws)
  have hwQ : w ∈ hyp.Q := hyp.mem_Q_of_sq_eq_one_of_mem_H hwH hw2
  -- then `u ∈ C_G(w) ≤ H`, contradiction
  exact huH (hyp.centralizer_le_H_of_mem_Q hwQ hw1
    (Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [hcomm_wu])))

/-- `Q` contains an involution (`|Q|` is even; Cauchy). -/
lemma exists_involution_mem_Q :
    ∃ x : G, x ∈ hyp.Q ∧ x ^ 2 = 1 ∧ x ≠ 1 := by
  haveI : Fintype hyp.Q := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := hyp.Q) 2
    (by rw [← Nat.card_eq_fintype_card]; exact hyp.Q_even.two_dvd)
  have hord : orderOf (x : G) = 2 :=
    (orderOf_injective hyp.Q.subtype hyp.Q.subtype_injective x).trans hx
  refine ⟨x, x.2, by rw [← hord]; exact pow_orderOf_eq_one _, ?_⟩
  intro h1
  rw [h1, orderOf_one] at hord
  norm_num at hord

/-- An involution of `H` is conjugate to any involution outside `H`
(Prop 2(a) + the dihedral conjugation lemma). -/
lemma isConj_involution_of_mem_of_not_mem {s w : G} (hsH : s ∈ hyp.H)
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hw2 : w ^ 2 = 1) (hwH : w ∉ hyp.H) :
    IsConj s w := by
  obtain ⟨u, hu2, hconj⟩ := exists_involution_conj_of_odd_orderOf
    (by rw [← sq]; exact hs2) (by rw [← sq]; exact hw2)
    (hyp.odd_orderOf_mul_involution hsH hs2 hs1 hw2 hwH)
  rw [isConj_iff]
  exact ⟨u⁻¹, by rwa [inv_inv]⟩

include hyp in
/-- **Peterfalvi Part II, Ch. I Prop 2 (b)** (p. 100) — the involutions of
`G` form a single conjugacy class. -/
lemma isConj_of_involutions {u v : G} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1) : IsConj u v := by
  by_cases huH : u ∈ hyp.H <;> by_cases hvH : v ∈ hyp.H
  · -- both in `H`: both are conjugate to `t ∉ H`
    have h1 := hyp.isConj_involution_of_mem_of_not_mem huH hu2 hu1
      hyp.t_sq hyp.t_not_mem_H
    have h2 := hyp.isConj_involution_of_mem_of_not_mem hvH hv2 hv1
      hyp.t_sq hyp.t_not_mem_H
    exact h1.trans h2.symm
  · exact hyp.isConj_involution_of_mem_of_not_mem huH hu2 hu1 hv2 hvH
  · exact (hyp.isConj_involution_of_mem_of_not_mem hvH hv2 hv1 hu2 huH).symm
  · -- both outside `H`: both are conjugate to an involution of `Q ≤ H`
    obtain ⟨s₀, hs₀Q, hs₀2, hs₀1⟩ := hyp.exists_involution_mem_Q
    have h1 := hyp.isConj_involution_of_mem_of_not_mem
      (hyp.Q_le_H hs₀Q) hs₀2 hs₀1 hu2 huH
    have h2 := hyp.isConj_involution_of_mem_of_not_mem
      (hyp.Q_le_H hs₀Q) hs₀2 hs₀1 hv2 hvH
    exact h1.symm.trans h2

/-- **Peterfalvi Part II, Ch. I Prop 2 (c)** (p. 100) — for an involution
`s ∈ Q`, the map `u ↦ s^u = u⁻¹ s u` is a permutation of `I - (H ∩ I)`. -/
lemma bijOn_conj_of_involution_mem_Q {s : G} (hsQ : s ∈ hyp.Q)
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    Set.BijOn (fun u => u⁻¹ * s * u)
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H}
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H} := by
  classical
  have hsH := hyp.Q_le_H hsQ
  have hmaps : Set.MapsTo (fun u => u⁻¹ * s * u)
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H}
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H} := by
    rintro u ⟨hu2, hu1, huH⟩
    have hcsq : (u⁻¹ * s * u) ^ 2 = 1 := by
      rw [sq]
      calc u⁻¹ * s * u * (u⁻¹ * s * u) = u⁻¹ * (s * s) * u := by group
        _ = 1 := by rw [← sq, hs2, mul_one, inv_mul_cancel]
    have hcne : u⁻¹ * s * u ≠ 1 := by
      intro h
      apply hs1
      have h2 := congrArg (fun z : G => u * z * u⁻¹) h
      simpa [mul_assoc] using h2
    refine ⟨hcsq, hcne, ?_⟩
    -- `s^u ∈ H` would put an involution inside the odd-order `H^{u⁻¹} ∩ H`
    intro hmem
    have huinvH : u⁻¹ ∉ hyp.H := fun h => huH (by simpa using inv_mem h)
    have hKmem : u⁻¹ * s * u ∈
        hyp.H.map (MulAut.conj u⁻¹).toMonoidHom ⊓ hyp.H := by
      refine Subgroup.mem_inf.mpr ⟨?_, hmem⟩
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      have hred : (u⁻¹)⁻¹ * (u⁻¹ * s * u) * u⁻¹ = s := by group
      rw [hred]
      exact hsH
    exact hcne (eq_one_of_sq_eq_one_of_odd_card
      (hyp.odd_card_conj_inf huinvH) hKmem hcsq)
  have hsurj : Set.SurjOn (fun u => u⁻¹ * s * u)
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H}
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H} := by
    rintro v ⟨hv2, hv1, hvH⟩
    obtain ⟨u, hu2, hconj⟩ := exists_involution_conj_of_odd_orderOf
      (by rw [← sq]; exact hs2) (by rw [← sq]; exact hv2)
      (hyp.odd_orderOf_mul_involution hsH hs2 hs1 hv2 hvH)
    have huH : u ∉ hyp.H := by
      intro huH
      apply hvH
      rw [← hconj]
      exact mul_mem (mul_mem (inv_mem huH) hsH) huH
    have hu1 : u ≠ 1 := by
      intro h1
      rw [h1] at hconj
      simp only [inv_one, one_mul, mul_one] at hconj
      exact hvH (hconj ▸ hsH)
    exact ⟨u, ⟨by rw [sq]; exact hu2, hu1, huH⟩, hconj⟩
  exact ((Set.toFinite _).surjOn_iff_bijOn_of_mapsTo hmaps).mp hsurj

/-- `H^g = H` exactly for `g ∈ H` (restatement of `N_G(H) = H`, Prop 1(d)). -/
lemma map_conj_eq_self_iff_mem_H {g : G} :
    hyp.H.map (MulAut.conj g).toMonoidHom = hyp.H ↔ g ∈ hyp.H := by
  constructor
  · intro heq
    rw [← hyp.normalizer_H_eq_H, Subgroup.mem_set_normalizer_iff]
    intro n
    simp only [SetLike.mem_coe]
    constructor
    · intro hn
      rw [← heq]
      exact ⟨n, hn, rfl⟩
    · intro hn
      rw [← heq] at hn
      obtain ⟨m, hm, hme⟩ := hn
      have h2 : g * m * g⁻¹ = g * n * g⁻¹ := hme
      have hmn : m = n := mul_left_cancel (mul_right_cancel h2)
      rwa [← hmn]
  · intro hg
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact mul_mem (mul_mem hg hm) (inv_mem hg)
    · intro hx
      exact ⟨g⁻¹ * x * g, mul_mem (mul_mem (inv_mem hg) hx) hg, by
        change g * (g⁻¹ * x * g) * g⁻¹ = x
        group⟩

/-- `H^a = H^b ↔ b⁻¹a ∈ H` (from Prop 1(d)). -/
lemma map_conj_eq_map_conj_iff {a b : G} :
    hyp.H.map (MulAut.conj a).toMonoidHom =
      hyp.H.map (MulAut.conj b).toMonoidHom ↔ b⁻¹ * a ∈ hyp.H := by
  constructor
  · intro h
    have h2 := congrArg
      (fun K : Subgroup G => K.map (MulAut.conj b⁻¹).toMonoidHom) h
    simp only [map_conj_map_conj] at h2
    rw [inv_mul_cancel, map_conj_one] at h2
    exact (hyp.map_conj_eq_self_iff_mem_H).mp h2
  · intro h
    have h2 := congrArg
      (fun K : Subgroup G => K.map (MulAut.conj b).toMonoidHom)
      ((hyp.map_conj_eq_self_iff_mem_H).mpr h)
    simp only [map_conj_map_conj] at h2
    rwa [mul_inv_cancel_left] at h2

/-- For an involution `u`, `s^u = u⁻¹su` lands in `H^u`. -/
lemma conj_mem_map_conj_of_sq_eq_one {s u : G} (hsH : s ∈ hyp.H)
    (hu2 : u ^ 2 = 1) :
    u⁻¹ * s * u ∈ hyp.H.map (MulAut.conj u).toMonoidHom := by
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have heq : u⁻¹ * (u⁻¹ * s * u) * u = s := by
    rw [huinv]
    calc u * (u * s * u) * u = (u * u) * s * (u * u) := by group
      _ = s := by rw [huu, one_mul, mul_one]
  rw [heq]
  exact hsH

/-- **Peterfalvi Part II, Ch. I Prop 2 (d)** (p. 100) — the number of
involutions `u` with `H^u = H^t` equals `|H ∩ I|`.

Proof: for the involution `s ∈ Q` of Cauchy, the permutation `u ↦ s^u` of
`I - (H ∩ I)` (Prop 2(c)) maps `{u ∈ I | H^u = H^t}` bijectively onto
`H^t ∩ I` (as `s^u ∈ H^u`, and `s^u ∈ H^u ∩ H^t` forces `H^u = H^t` by the
oddness of Prop 1(a)), and `|H^t ∩ I| = |H ∩ I|`. -/
lemma ncard_involutions_map_conj_eq_card_involutions_H :
    {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
        hyp.H.map (MulAut.conj u).toMonoidHom =
          hyp.H.map (MulAut.conj hyp.t).toMonoidHom}.ncard =
      {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard := by
  classical
  obtain ⟨s, hsQ, hs2, hs1⟩ := hyp.exists_involution_mem_Q
  have hsH := hyp.Q_le_H hsQ
  have hbij := hyp.bijOn_conj_of_involution_mem_Q hsQ hs2 hs1
  -- `T ⊆ A` (an involution with `H^u = H^t` is outside `H`)
  have hTA : {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
      hyp.H.map (MulAut.conj u).toMonoidHom =
        hyp.H.map (MulAut.conj hyp.t).toMonoidHom} ⊆
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H} := by
    rintro u ⟨hu2, hu1, hueq⟩
    refine ⟨hu2, hu1, fun huH => ?_⟩
    exact hyp.t_not_mem_H ((hyp.map_conj_eq_self_iff_mem_H).mp
      (((hyp.map_conj_eq_self_iff_mem_H).mpr huH).symm.trans hueq).symm)
  -- `B ⊆ A` (an involution of `H^t` is outside `H`, by Prop 1(a))
  have hBA : {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
      u ∈ hyp.H.map (MulAut.conj hyp.t).toMonoidHom} ⊆
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H} := by
    rintro u ⟨hu2, hu1, huHt⟩
    refine ⟨hu2, hu1, fun huH => ?_⟩
    exact hu1 (eq_one_of_sq_eq_one_of_odd_card
      (hyp.odd_card_conj_inf hyp.t_not_mem_H)
      (Subgroup.mem_inf.mpr ⟨huHt, huH⟩) hu2)
  -- on `A`: `u ∈ T ↔ s^u ∈ B`
  have hkey : ∀ u ∈ {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∉ hyp.H},
      (u ∈ {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
          hyp.H.map (MulAut.conj u).toMonoidHom =
            hyp.H.map (MulAut.conj hyp.t).toMonoidHom} ↔
        u⁻¹ * s * u ∈ {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
          u ∈ hyp.H.map (MulAut.conj hyp.t).toMonoidHom}) := by
    rintro u huA
    obtain ⟨hu2, hu1, huH⟩ := huA
    constructor
    · rintro ⟨-, -, hueq⟩
      obtain ⟨hσ2, hσ1, -⟩ := hbij.mapsTo ⟨hu2, hu1, huH⟩
      refine ⟨hσ2, hσ1, ?_⟩
      rw [← hueq]
      exact hyp.conj_mem_map_conj_of_sq_eq_one hsH hu2
    · rintro ⟨hσ2, hσ1, hσHt⟩
      refine ⟨hu2, hu1, ?_⟩
      by_contra hne
      -- `H^u ≠ H^t`, so `|H^u ∩ H^t|` is odd, yet contains the involution `s^u`
      have htuH : hyp.t⁻¹ * u ∉ hyp.H :=
        fun h => hne ((hyp.map_conj_eq_map_conj_iff).mpr h)
      have hodd := hyp.odd_card_conj_inf htuH
      have hconj_eq : (hyp.H.map (MulAut.conj (hyp.t⁻¹ * u)).toMonoidHom ⊓
          hyp.H).map (MulAut.conj hyp.t).toMonoidHom =
          hyp.H.map (MulAut.conj u).toMonoidHom ⊓
            hyp.H.map (MulAut.conj hyp.t).toMonoidHom := by
        rw [Subgroup.map_inf _ _ _ (MulEquiv.injective (MulAut.conj hyp.t)),
          map_conj_map_conj, mul_inv_cancel_left]
      have hoddconj : Odd (Nat.card
          ↥(hyp.H.map (MulAut.conj u).toMonoidHom ⊓
            hyp.H.map (MulAut.conj hyp.t).toMonoidHom)) := by
        rw [← hconj_eq,
          ← Nat.card_congr (Subgroup.equivMapOfInjective _ _
            (MulEquiv.injective (MulAut.conj hyp.t))).toEquiv]
        exact hodd
      exact hσ1 (eq_one_of_sq_eq_one_of_odd_card hoddconj
        (Subgroup.mem_inf.mpr
          ⟨hyp.conj_mem_map_conj_of_sq_eq_one hsH hu2, hσHt⟩) hσ2)
  -- the permutation restricts to a bijection `T ≃ B`
  have himg : (fun u => u⁻¹ * s * u) ''
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
        hyp.H.map (MulAut.conj u).toMonoidHom =
          hyp.H.map (MulAut.conj hyp.t).toMonoidHom} =
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
        u ∈ hyp.H.map (MulAut.conj hyp.t).toMonoidHom} := by
    apply Set.Subset.antisymm
    · rintro - ⟨u, huT, rfl⟩
      exact (hkey u (hTA huT)).mp huT
    · intro b hb
      obtain ⟨u, huA, hub⟩ := hbij.surjOn (hBA hb)
      have hub' : u⁻¹ * s * u = b := hub
      refine ⟨u, (hkey u huA).mpr ?_, hub⟩
      rw [hub']
      exact hb
  -- `|H^t ∩ I| = |H ∩ I|` via conjugation by `t`
  have hBS : {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
      u ∈ hyp.H.map (MulAut.conj hyp.t).toMonoidHom} =
      (fun x : G => hyp.t * x * hyp.t⁻¹) ''
        {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
    ext b
    constructor
    · rintro ⟨hb2, hb1, hbHt⟩
      obtain ⟨m, hm, hme⟩ := hbHt
      have hme' : hyp.t * m * hyp.t⁻¹ = b := hme
      refine ⟨m, ⟨?_, ?_, hm⟩, hme'⟩
      · have h2 : (hyp.t * m * hyp.t⁻¹) ^ 2 = 1 := by rw [hme']; exact hb2
        rw [conj_pow] at h2
        have h3 := congrArg (fun z : G => hyp.t⁻¹ * z * hyp.t) h2
        simpa [mul_assoc] using h3
      · intro h1
        apply hb1
        rw [← hme', h1, mul_one, mul_inv_cancel]
    · rintro ⟨m, ⟨hm2, hm1, hmH⟩, rfl⟩
      refine ⟨?_, ?_, ⟨m, hmH, rfl⟩⟩
      · rw [conj_pow, hm2, mul_one, mul_inv_cancel]
      · intro h
        apply hm1
        have h2 := congrArg (fun z : G => hyp.t⁻¹ * z * hyp.t) h
        simpa [mul_assoc] using h2
  calc {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
        hyp.H.map (MulAut.conj u).toMonoidHom =
          hyp.H.map (MulAut.conj hyp.t).toMonoidHom}.ncard
      = ((fun u => u⁻¹ * s * u) ''
          {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
            hyp.H.map (MulAut.conj u).toMonoidHom =
              hyp.H.map (MulAut.conj hyp.t).toMonoidHom}).ncard :=
        (Set.InjOn.ncard_image (hbij.injOn.mono hTA)).symm
    _ = {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
          u ∈ hyp.H.map (MulAut.conj hyp.t).toMonoidHom}.ncard := by
        rw [himg]
    _ = {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard := by
        rw [hBS]
        exact Set.ncard_image_of_injective _ (fun a b h => by
          simpa [mul_assoc] using
            congrArg (fun z : G => hyp.t⁻¹ * z * hyp.t) h)

/-! ## Chapter I §1, Proposition 3 (p. 101) -/

/-- `k ↦ kt` maps `K` onto `{u ∈ I | H^u = H^t}` (the book's `Dt ∩ I`). -/
lemma image_mul_t_KSet :
    (fun k : G => k * hyp.t) '' hyp.KSet =
      {u : G | u ^ 2 = 1 ∧ u ≠ 1 ∧
        hyp.H.map (MulAut.conj u).toMonoidHom =
          hyp.H.map (MulAut.conj hyp.t).toMonoidHom} := by
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  ext u
  constructor
  · rintro ⟨k, ⟨hkD, hkinv⟩, rfl⟩
    have hkH : k ∈ hyp.H := hyp.D_le_H hkD
    refine ⟨?_, ?_, ?_⟩
    · rw [sq]
      calc k * hyp.t * (k * hyp.t) = k * (hyp.t * k * hyp.t) := by group
        _ = k * k⁻¹ := by rw [hkinv]
        _ = 1 := mul_inv_cancel k
    · intro h1
      apply hyp.t_not_mem_H
      have h2 : hyp.t = k⁻¹ := by
        have h3 := congrArg (fun z : G => k⁻¹ * z) h1
        simpa [mul_assoc] using h3
      rw [h2]
      exact inv_mem hkH
    · rw [hyp.map_conj_eq_map_conj_iff, hyp.t_inv_eq]
      have h2 : hyp.t * (k * hyp.t) = k⁻¹ := by
        rw [← mul_assoc]
        exact hkinv
      rw [h2]
      exact inv_mem hkH
  · rintro ⟨hu2, hu1, hueq⟩
    have huu : u * u = 1 := by rw [← sq]; exact hu2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have htuH : hyp.t⁻¹ * u ∈ hyp.H := (hyp.map_conj_eq_map_conj_iff).mp hueq
    refine ⟨u * hyp.t, ⟨?_, ?_⟩, ?_⟩
    · rw [hyp.mem_D_iff]
      constructor
      · have h2 : u * hyp.t = (hyp.t⁻¹ * u)⁻¹ := by
          rw [mul_inv_rev, inv_inv, huinv]
        rw [h2]
        exact inv_mem htuH
      · have h2 : hyp.t⁻¹ * (u * hyp.t) * hyp.t = hyp.t⁻¹ * u := by
          calc hyp.t⁻¹ * (u * hyp.t) * hyp.t
              = hyp.t⁻¹ * (u * (hyp.t * hyp.t)) := by group
            _ = hyp.t⁻¹ * u := by rw [htt, mul_one]
        rw [h2]
        exact htuH
    · calc hyp.t * (u * hyp.t) * hyp.t
          = hyp.t * (u * (hyp.t * hyp.t)) := by group
        _ = hyp.t * u := by rw [htt, mul_one]
        _ = (u * hyp.t)⁻¹ := by rw [mul_inv_rev, hyp.t_inv_eq, huinv]
    · calc u * hyp.t * hyp.t = u * (hyp.t * hyp.t) := by rw [mul_assoc]
        _ = u := by rw [htt, mul_one]

/-- **Peterfalvi Part II, Ch. I Prop 3** (p. 101), first clause —
`|K| = |H ∩ I|`. -/
lemma ncard_KSet_eq :
    hyp.KSet.ncard = {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard := by
  have hinj : Function.Injective (fun k : G => k * hyp.t) :=
    fun a b h => mul_right_cancel h
  calc hyp.KSet.ncard
      = ((fun k : G => k * hyp.t) '' hyp.KSet).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ = {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard := by
        rw [hyp.image_mul_t_KSet,
          hyp.ncard_involutions_map_conj_eq_card_involutions_H]

/-- `k ↦ kt` sends `K` into `I - (H ∩ I)`. -/
lemma mul_t_mem_of_mem_KSet {k : G} (hk : k ∈ hyp.KSet) :
    (k * hyp.t) ^ 2 = 1 ∧ k * hyp.t ≠ 1 ∧ k * hyp.t ∉ hyp.H := by
  obtain ⟨hkD, hkinv⟩ := hk
  have hkH : k ∈ hyp.H := hyp.D_le_H hkD
  refine ⟨?_, ?_, ?_⟩
  · rw [sq]
    calc k * hyp.t * (k * hyp.t) = k * (hyp.t * k * hyp.t) := by group
      _ = k * k⁻¹ := by rw [hkinv]
      _ = 1 := mul_inv_cancel k
  · intro h1
    apply hyp.t_not_mem_H
    have h2 : hyp.t = k⁻¹ := by
      have h3 := congrArg (fun z : G => k⁻¹ * z) h1
      simpa [mul_assoc] using h3
    rw [h2]
    exact inv_mem hkH
  · intro hktH
    apply hyp.t_not_mem_H
    have h2 : hyp.t = k⁻¹ * (k * hyp.t) := by group
    rw [h2]
    exact mul_mem (inv_mem hkH) hktH

/-- **Peterfalvi Part II, Ch. I Prop 3** (p. 101), injectivity clause — for
`s ∈ H ∩ I` the map `k ↦ s^k = k⁻¹ s k` is injective on `K`.  (From Prop 2(c)
applied to the involutions `kt`, whose conjugation permutes `I - (H∩I)`.) -/
lemma injOn_conj_KSet {s : G} (hsH : s ∈ hyp.H) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    Set.InjOn (fun k : G => k⁻¹ * s * k) hyp.KSet := by
  classical
  have hsQ := hyp.mem_Q_of_sq_eq_one_of_mem_H hsH hs2
  have hbij := hyp.bijOn_conj_of_involution_mem_Q hsQ hs2 hs1
  rintro k₁ hk₁ k₂ hk₂ heq
  have heq' : k₁⁻¹ * s * k₁ = k₂⁻¹ * s * k₂ := heq
  have hσeq : (k₁ * hyp.t)⁻¹ * s * (k₁ * hyp.t) =
      (k₂ * hyp.t)⁻¹ * s * (k₂ * hyp.t) := by
    have e1 : ∀ k : G, (k * hyp.t)⁻¹ * s * (k * hyp.t) =
        hyp.t⁻¹ * (k⁻¹ * s * k) * hyp.t := by
      intro k
      group
    rw [e1, e1, heq']
  have h2 := hbij.injOn (hyp.mul_t_mem_of_mem_KSet hk₁)
    (hyp.mul_t_mem_of_mem_KSet hk₂) hσeq
  exact mul_right_cancel h2

/-- **Peterfalvi Part II, Ch. I Prop 3** (p. 101), second clause — for
`s ∈ H ∩ I` the conjugates `s^K` exhaust `H ∩ I`. -/
lemma image_conj_KSet_eq_involutions_H {s : G} (hsH : s ∈ hyp.H)
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    (fun k : G => k⁻¹ * s * k) '' hyp.KSet =
      {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
  classical
  have hsub : (fun k : G => k⁻¹ * s * k) '' hyp.KSet ⊆
      {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
    rintro - ⟨k, ⟨hkD, -⟩, rfl⟩
    have hkH : k ∈ hyp.H := hyp.D_le_H hkD
    refine ⟨?_, ?_, ?_⟩
    · rw [sq]
      calc k⁻¹ * s * k * (k⁻¹ * s * k) = k⁻¹ * (s * s) * k := by group
        _ = 1 := by rw [← sq, hs2, mul_one, inv_mul_cancel]
    · intro h
      apply hs1
      have h2 := congrArg (fun z : G => k * z * k⁻¹) h
      simpa [mul_assoc] using h2
    · exact mul_mem (mul_mem (inv_mem hkH) hsH) hkH
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.InjOn.ncard_image (hyp.injOn_conj_KSet hsH hs2 hs1),
    ← hyp.ncard_KSet_eq]


end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
