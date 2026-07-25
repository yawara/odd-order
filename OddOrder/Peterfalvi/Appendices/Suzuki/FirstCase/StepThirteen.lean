/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTwelveTransfer

/-!
# Peterfalvi Part II, Ch. II, step (13): `C_G(Z₁)` is a `3`-group — preliminaries

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (13), p. 113.

The centralizer identities feeding the step (13) counting
`|C_G(Z₁)| = |C_G(Z₁) ∩ C_G(s)|·|J|`:

* `C_G(st) ∩ C_G(s) = C_G(t) ∩ C_G(s)` (elementary: `t = s⁻¹·(st)`);
* `C_G(t) ∩ C_G(s) = V` — an element commuting with `s` fixes the base point
  (the fixed points of `s ∈ Q` off the base point would violate the
  regularity of `Q` on `Ω − {basept}`), and commuting with `t` it then also
  fixes `t • basept`, so it lies in `D`; conversely `V = C_D(t) = C_D(s)`
  (Ch. I Prop 5).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp in
/-- Commuting with `s` and `st` is the same as commuting with `s` and `t`
(elementary: `t = s⁻¹·(st)`). -/
lemma centralizer_mul_t_inf_eq_centralizer_t_inf :
    Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution}
      = Subgroup.centralizer {hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hst, hs⟩
    refine ⟨?_, hs⟩
    have h1 : Commute x (hyp.distinguishedInvolution⁻¹
        * (hyp.distinguishedInvolution * hyp.t)) :=
      (Commute.inv_right hs).mul_right hst
    rwa [inv_mul_cancel_left] at h1
  · rintro ⟨ht, hs⟩
    exact ⟨(Commute.mul_right hs ht : _), hs⟩

include hyp in
/-- **Step (13) preliminary** (p. 113): `C_G(t) ∩ C_G(s) = V`.

`⊆`: an element `x` commuting with `s` maps the base point to an `s`-fixed
point; since `s` is an involution of `H` it lies in `Q`, which acts freely on
`Ω − {basept}`, so `x` fixes the base point.  Commuting with `t` as well, `x`
also fixes `t • basept`, hence `x ∈ D ⊓ C_G(t) = V`.  `⊇`: `V = C_D(t)` by
definition and `V = C_D(s)` by Ch. I Prop 5. -/
lemma centralizer_t_inf_centralizer_eq_V :
    Subgroup.centralizer {hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} = hyp.V := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxt0, hxs0⟩ := Subgroup.mem_inf.mp hx
    have hxt : Commute x hyp.t := Subgroup.mem_centralizer_singleton_iff.mp hxt0
    have hxs : Commute x hyp.distinguishedInvolution :=
      Subgroup.mem_centralizer_singleton_iff.mp hxs0
    have hsH := hyp.distinguishedInvolution_mem_H
    have hsQ : hyp.distinguishedInvolution ∈ hyp.Q :=
      hyp.mem_Q_of_sq_eq_one_of_mem_H hsH hyp.distinguishedInvolution_sq
    -- `x` fixes the base point
    have hxbase : x • hyp.basept = hyp.basept := by
      by_contra hne
      obtain ⟨q, hq⟩ := hyp.qRegularEquiv.surjective ⟨x • hyp.basept, hne⟩
      have hqval : (q : G) • (hyp.t • hyp.basept) = x • hyp.basept :=
        congrArg Subtype.val hq
      have hsfix : hyp.distinguishedInvolution • (x • hyp.basept)
          = x • hyp.basept := by
        rw [← mul_smul, ← hxs.eq, mul_smul, hyp.smul_basept_eq_of_mem_H hsH]
      have hsq : (hyp.distinguishedInvolution * (q : G))
          • (hyp.t • hyp.basept) = x • hyp.basept := by
        rw [mul_smul, hqval, hsfix]
      have he : hyp.qRegularEquiv
          ⟨hyp.distinguishedInvolution * (q : G), hyp.Q.mul_mem hsQ q.2⟩
          = hyp.qRegularEquiv q := by
        rw [hq]
        exact Subtype.ext hsq
      have hval : hyp.distinguishedInvolution * (q : G) = (q : G) :=
        congrArg Subtype.val (hyp.qRegularEquiv.injective he)
      apply hyp.distinguishedInvolution_ne_one
      have h1 : hyp.distinguishedInvolution * (q : G) = 1 * (q : G) := by
        rw [one_mul]
        exact hval
      exact mul_right_cancel h1
    -- `x` fixes `t • basept` as well, so `x ∈ D`
    have hxtb : x • (hyp.t • hyp.basept) = hyp.t • hyp.basept := by
      rw [← mul_smul, hxt.eq, mul_smul, hxbase]
    have hxD : x ∈ hyp.D := by
      rw [hyp.D_eq_stabilizer_inf]
      exact ⟨mem_stabilizer_iff.mpr hxbase, mem_stabilizer_iff.mpr hxtb⟩
    exact Subgroup.mem_inf.mpr ⟨hxD, hxt0⟩
  · intro v hv
    refine Subgroup.mem_inf.mpr ⟨hv.2, ?_⟩
    exact (hyp.V_le_centralizer_distinguishedInvolution hv).2

include hyp in
/-- The two identities combined: `C_G(st) ∩ C_G(s) = V` (p. 113). -/
lemma centralizer_mul_t_inf_centralizer_eq_V :
    Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} = hyp.V := by
  rw [hyp.centralizer_mul_t_inf_eq_centralizer_t_inf,
    hyp.centralizer_t_inf_centralizer_eq_V]

include hyp in
/-- `st` is strongly real (it is the product of the two involutions `s`
and `t`). -/
lemma isStronglyReal_distinguishedInvolution_mul_t :
    IsStronglyReal (hyp.distinguishedInvolution * hyp.t) :=
  ⟨hyp.distinguishedInvolution,
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_ne_one⟩,
    hyp.t, ⟨hyp.t_sq, hyp.t_ne_one⟩, rfl⟩

include hyp in
/-- `s` inverts `st` (`s·(st)·s = ts = (st)⁻¹`), hence normalizes its
centralizer. -/
lemma conj_mem_centralizer_mul_t (x : G)
    (hx : x ∈ Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t}) :
    hyp.distinguishedInvolution * x * hyp.distinguishedInvolution
      ∈ Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t} := by
  set s := hyp.distinguishedInvolution with hs_def
  set c : G := s * hyp.t with hc_def
  have hs2 : s * s = 1 := by rw [← sq]; exact hyp.distinguishedInvolution_sq
  have ht2 : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  -- `s c s = c⁻¹`
  have hinv : s * c * s = c⁻¹ := by
    have hL : s * c * s = hyp.t * s := by
      rw [hc_def]
      calc s * (s * hyp.t) * s = (s * s) * hyp.t * s := by group
        _ = hyp.t * s := by rw [hs2, one_mul]
    have hR : c⁻¹ = hyp.t * s := by
      rw [hc_def, mul_inv_rev, inv_eq_of_mul_eq_one_right ht2,
        inv_eq_of_mul_eq_one_right hs2]
    rw [hL, hR]
  have hsc : s * c = c⁻¹ * s := by
    calc s * c = s * c * (s * s) := by rw [hs2, mul_one]
      _ = (s * c * s) * s := by group
      _ = c⁻¹ * s := by rw [hinv]
  have hsc' : s * c⁻¹ = c * s := by
    have h1 : s * c⁻¹ * s = c := by
      have h2 := congrArg (fun y : G => y⁻¹) hinv
      simp only [mul_inv_rev, inv_inv] at h2
      rw [inv_eq_of_mul_eq_one_right hs2, ← mul_assoc] at h2
      exact h2
    calc s * c⁻¹ = s * c⁻¹ * (s * s) := by rw [hs2, mul_one]
      _ = (s * c⁻¹ * s) * s := by group
      _ = c * s := by rw [h1]
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have hxc : Commute x c := hx
  have hxci : x * c⁻¹ = c⁻¹ * x := hxc.inv_right.eq
  calc s * x * s * c = s * x * (s * c) := by group
    _ = s * x * (c⁻¹ * s) := by rw [hsc]
    _ = s * (x * c⁻¹) * s := by group
    _ = s * (c⁻¹ * x) * s := by rw [hxci]
    _ = (s * c⁻¹) * (x * s) := by group
    _ = (c * s) * (x * s) := by rw [hsc']
    _ = c * (s * x * s) := by group

include hyp in
/-- **Step (13), the counting identity** (p. 113):
`|C_G(st)| = |V| · |J|` where `J = {x ∈ C_G(st) | sxs = x⁻¹}`.

This is Ch. I §1, the Lemma (a), applied to the involution `s` acting on the
odd-order group `C_G(st)` (odd by Ch. I §3, Lemma 3, since `st` is strongly
real and not an involution), together with `C_G(st) ∩ C_G(s) = V`. -/
theorem card_centralizer_mul_t_eq
    (hst2 : (hyp.distinguishedInvolution * hyp.t) ^ 2 ≠ 1) :
    Nat.card ↥(Subgroup.centralizer
        ({hyp.distinguishedInvolution * hyp.t} : Set G))
      = Nat.card ↥hyp.V *
        (invertedBy (Subgroup.centralizer
          ({hyp.distinguishedInvolution * hyp.t} : Set G))
          hyp.distinguishedInvolution).ncard := by
  have hs2 : hyp.distinguishedInvolution * hyp.distinguishedInvolution = 1 := by
    rw [← sq]; exact hyp.distinguishedInvolution_sq
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer
      ({hyp.distinguishedInvolution * hyp.t} : Set G))) :=
    hyp.centralizer_natCard_odd_of_stronglyReal
      hyp.isStronglyReal_distinguishedInvolution_mul_t hst2
  have hkey := card_eq_card_centralizer_mul_ncard_invertedBy
    (X := Subgroup.centralizer ({hyp.distinguishedInvolution * hyp.t} : Set G))
    hs2 hodd hyp.conj_mem_centralizer_mul_t
  rwa [hyp.centralizer_mul_t_inf_centralizer_eq_V] at hkey

include hyp in
/-- **Step (13)** (p. 113): every prime `r` dividing `|J|` occurs as the order
of an element `u·t` with `u ∈ Q₀#`.

By the prime-divisor clause of Ch. I §1 (Cauchy inside `Z`) there is `x ∈ J`
of order `r`; as `s` inverts `x`, the element `x = s·(sx)` is a product of two
involutions, so Ch. I §3 Lemma 3 conjugates it into the normal form `u·t`
with `u ∈ Q₀#`. -/
theorem exists_mem_Q0_orderOf_mul_t_eq_of_dvd_ncard_invertedBy
    (hst2 : (hyp.distinguishedInvolution * hyp.t) ^ 2 ≠ 1)
    {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ (invertedBy (Subgroup.centralizer
      ({hyp.distinguishedInvolution * hyp.t} : Set G))
      hyp.distinguishedInvolution).ncard) :
    ∃ u : G, u ∈ hyp.Q0 ∧ u ≠ 1 ∧ orderOf (u * hyp.t) = r := by
  set s := hyp.distinguishedInvolution with hs_def
  have hs2 : s * s = 1 := by rw [← sq]; exact hyp.distinguishedInvolution_sq
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer ({s * hyp.t} : Set G))) :=
    hyp.centralizer_natCard_odd_of_stronglyReal
      hyp.isStronglyReal_distinguishedInvolution_mul_t hst2
  -- `r` is odd: it divides `|J|`, which divides the odd `|C_G(st)|`.
  have hrne2 : r ≠ 2 := by
    intro h2
    have hJdvd : (invertedBy (Subgroup.centralizer ({s * hyp.t} : Set G)) s).ncard
        ∣ Nat.card ↥(Subgroup.centralizer ({s * hyp.t} : Set G)) :=
      Dvd.intro_left _ (hyp.card_centralizer_mul_t_eq hst2).symm
    have h2dvd : (2 : ℕ) ∣ Nat.card ↥(Subgroup.centralizer ({s * hyp.t} : Set G)) :=
      (h2 ▸ hdvd).trans hJdvd
    rw [Nat.odd_iff] at hodd
    omega
  -- Cauchy inside `J`.
  obtain ⟨x, hxJ, hxord⟩ := exists_orderOf_eq_prime_of_dvd_ncard_invertedBy
    hs2 hodd hyp.conj_mem_centralizer_mul_t hr hdvd
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hxord] at hdvd2
    exact hrne2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd2)
  -- `x` is strongly real: `x = s · (sx)` with `(sx)² = 1`.
  have hv2 : (s * x) ^ 2 = 1 := by
    rw [sq]
    calc (s * x) * (s * x) = (s * x * s) * x := by group
      _ = x⁻¹ * x := by rw [hxJ.2]
      _ = 1 := inv_mul_cancel x
  have hv1 : s * x ≠ 1 := by
    intro h
    have hxs : x = s := by
      have h1 : s * (s * x) = s * 1 := by rw [h]
      rw [← mul_assoc, hs2, one_mul, mul_one] at h1
      exact h1
    rw [hxs] at hx2
    exact hx2 hyp.distinguishedInvolution_sq
  have hSR : IsStronglyReal x :=
    ⟨s, ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_ne_one⟩,
      s * x, ⟨hv2, hv1⟩, by rw [← mul_assoc, hs2, one_mul]⟩
  -- normal form (Ch. I §3, Lemma 3).
  obtain ⟨u, huQ0, hu1, hconj⟩ := hyp.exists_isConj_mul_t_of_stronglyReal hSR hx2
  refine ⟨u, huQ0, hu1, ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  rw [← hg, ← hxord]
  exact orderOf_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective x

include hyp in
/-- **Step (13)** (p. 113): if `st` has order three, every prime dividing
`|J|` divides `|⟨Q₀, K, t⟩| = |Q₀|·|K|·(|Q₀| + 1)`.

The `J`-side prime `r` is realised as the order of some `u·t` with
`u ∈ Q₀#`, and `u·t` lies in the Lemma-4 group.  (In the First Case this
reads `r ∣ 8·7·9 = 504 = |PSL(2,8)|`, so an odd `r` is `3` or `7`.) -/
theorem dvd_card_orderThree_of_dvd_ncard_invertedBy
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ (invertedBy (Subgroup.centralizer
      ({hyp.distinguishedInvolution * hyp.t} : Set G))
      hyp.distinguishedInvolution).ncard) :
    r ∣ Nat.card ↥hyp.Q0 * Nat.card ↥hyp.K * (Nat.card ↥hyp.Q0 + 1) := by
  have hst2 : (hyp.distinguishedInvolution * hyp.t) ^ 2 ≠ 1 := by
    intro h
    have h2 : orderOf (hyp.distinguishedInvolution * hyp.t) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one h
    rw [hst] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨u, huQ0, -, hord⟩ :=
    hyp.exists_mem_Q0_orderOf_mul_t_eq_of_dvd_ncard_invertedBy hst2 hr hdvd
  rw [← hyp.card_orderThreeGeneratedSubgroup hst, ← hord]
  have humem : u * hyp.t ∈ hyp.orderThreeGeneratedSubgroup :=
    mul_mem (hyp.orderThree_Q0_le huQ0) hyp.orderThree_t_mem
  have hdvd2 := orderOf_dvd_natCard
    (⟨u * hyp.t, humem⟩ : ↥hyp.orderThreeGeneratedSubgroup)
  have heq : orderOf (u * hyp.t)
      = orderOf (⟨u * hyp.t, humem⟩ : ↥hyp.orderThreeGeneratedSubgroup) :=
    orderOf_injective hyp.orderThreeGeneratedSubgroup.subtype
      (Subgroup.subtype_injective _) ⟨u * hyp.t, humem⟩
  rw [heq]
  exact hdvd2

include hyp in
/-- **Step (13), the `r = 7` obstruction** (p. 113): no strongly real
non-involution whose order is prime to `|K|` centralises `K`.

Such a `y` has odd centralizer order (Ch. I §3, Lemma 3), so `y` itself has
odd order and therefore lies in `D` (it cannot interchange the two fixed
points of a `1 ≠ k ∈ K`); being prime to `|K|` it then lies in `V = C_D(t)`
by the `D = K ⋊ V` factorisation.  But then the involution `t` centralises
`y`, making `|C_G(y)|` even — a contradiction.

This is the group-theoretic content of Peterfalvi's "`C_G(K) = C_D(K) = KW`,
so `x` cannot centralize a strongly real element of order 3". -/
theorem not_mem_centralizer_K_of_isStronglyReal {y : G}
    (hSR : IsStronglyReal y) (hy2 : y ^ 2 ≠ 1)
    (hcop : Nat.Coprime (orderOf y) (Nat.card ↥hyp.K))
    (hyK : y ∈ Subgroup.centralizer (hyp.K : Set G)) : False := by
  classical
  -- `|C_G(y)|` is odd, hence so is `orderOf y`.
  have hoddC : Odd (Nat.card ↥(Subgroup.centralizer ({y} : Set G))) :=
    hyp.centralizer_natCard_odd_of_stronglyReal hSR hy2
  have hymem : y ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hdvd : orderOf y ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
    have h1 := orderOf_dvd_natCard
      (⟨y, hymem⟩ : ↥(Subgroup.centralizer ({y} : Set G)))
    have heq : orderOf y
        = orderOf (⟨y, hymem⟩ : ↥(Subgroup.centralizer ({y} : Set G))) :=
      orderOf_injective (Subgroup.centralizer ({y} : Set G)).subtype
        (Subgroup.subtype_injective _) ⟨y, hymem⟩
    rw [heq]
    exact h1
  have hoddy : Odd (orderOf y) := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at hoddC
    exact (Nat.odd_mul.mp hoddC).1
  -- `y` centralises some `1 ≠ k ∈ K`, hence lies in `D`, hence in `V`.
  obtain ⟨k, hk, hk1⟩ := hyp.exists_ne_one_mem_KSet
  have hkK : k ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk
  have hyc : y ∈ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hyK k hkK).symm
  have hyD : y ∈ hyp.D :=
    hyp.mem_D_of_odd_orderOf_of_mem_centralizer_KSet hk hk1 hyc hoddy
  have hyV : y ∈ hyp.V :=
    hyp.mem_V_of_mem_centralizer_K_of_coprime hyD hyK hcop
  -- but then the involution `t` centralises `y`.
  have htC : hyp.t ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hyV.2).symm
  have heven := even_card_of_sq_eq_one_mem htC hyp.t_sq hyp.t_ne_one
  rw [Nat.odd_iff] at hoddC
  rw [Nat.even_iff] at heven
  omega

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
