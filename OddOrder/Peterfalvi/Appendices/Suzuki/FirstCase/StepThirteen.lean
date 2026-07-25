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

open scoped Pointwise

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
/-- An element of `J = {x ∈ C_G(st) | sxs = x⁻¹}` which is not an involution
is strongly real: `x = s·(sx)` with `(sx)² = (sxs)x = x⁻¹x = 1`. -/
lemma isStronglyReal_of_mem_invertedBy_centralizer {x : G}
    (hxJ : x ∈ invertedBy (Subgroup.centralizer
      ({hyp.distinguishedInvolution * hyp.t} : Set G))
      hyp.distinguishedInvolution)
    (hx2 : x ^ 2 ≠ 1) : IsStronglyReal x := by
  set s := hyp.distinguishedInvolution with hs_def
  have hs2 : s * s = 1 := by rw [← sq]; exact hyp.distinguishedInvolution_sq
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
  exact ⟨s, ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_ne_one⟩,
    s * x, ⟨hv2, hv1⟩, by rw [← mul_assoc, hs2, one_mul]⟩

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
  have hSR : IsStronglyReal x :=
    hyp.isStronglyReal_of_mem_invertedBy_centralizer hxJ hx2
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

include hyp in
/-- **Step (13), Sylow transport** (p. 113): if the prime `q = |K|` divides
neither `|Q₀|` nor `|Q₀| + 1`, then `K` is a Sylow `q`-subgroup of the Lemma-4
group `L`, so every element of order `q` in `L` is `L`-conjugate into `K`. -/
theorem exists_conj_mem_K_of_orderOf_eq
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    {q : ℕ} (hq : q.Prime) (hqK : Nat.card ↥hyp.K = q)
    (hqQ0 : ¬ q ∣ Nat.card ↥hyp.Q0 * (Nat.card ↥hyp.Q0 + 1))
    {w : G} (hwL : w ∈ hyp.orderThreeGeneratedSubgroup) (hwq : orderOf w = q) :
    ∃ g : G, g * w * g⁻¹ ∈ hyp.K ∧ g * w * g⁻¹ ≠ 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set L : Subgroup G := hyp.orderThreeGeneratedSubgroup with hL_def
  set m : ℕ := Nat.card ↥hyp.Q0 * (Nat.card ↥hyp.Q0 + 1) with hm_def
  have hcardL : Nat.card ↥L = q * m := by
    rw [hL_def, hyp.card_orderThreeGeneratedSubgroup hst, hqK, hm_def]
    ring
  -- any `q`-subgroup of `L` has order at most `q`
  have hSylowCard : ∀ S : Sylow q ↥L, Nat.card ↥(S : Subgroup ↥L) ∣ q := by
    intro S
    obtain ⟨a, ha⟩ := S.2.exists_card_eq
    have hdvd : Nat.card ↥(S : Subgroup ↥L) ∣ Nat.card ↥L :=
      Subgroup.card_subgroup_dvd_card _
    rw [ha, hcardL] at hdvd
    rcases Nat.lt_or_ge a 2 with hlt | hge
    · interval_cases a
      · rw [ha, pow_zero]; exact one_dvd q
      · rw [ha, pow_one]
    · exfalso
      have h2 : q ^ 2 ∣ q * m := dvd_trans (pow_dvd_pow q hge) hdvd
      obtain ⟨c, hc⟩ := h2
      have hqm : q ∣ m := by
        refine ⟨c, ?_⟩
        have hqpos : 0 < q := hq.pos
        have h3 : q * m = q * (q * c) := by rw [hc]; ring
        exact Nat.eq_of_mul_eq_mul_left hqpos h3
      exact hqQ0 hqm
  -- `K`, viewed in `L`, is a Sylow `q`-subgroup
  have hKL : hyp.K ≤ L := hyp.orderThree_K_le
  set Kl : Subgroup ↥L := hyp.K.subgroupOf L with hKl_def
  have hKlcard : Nat.card ↥Kl = q := by
    rw [hKl_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hqK]
  obtain ⟨SK, hKSK⟩ :=
    (IsPGroup.of_card (n := 1) (by rw [hKlcard, pow_one]) :
      IsPGroup q ↥Kl).exists_le_sylow
  have hSKeq : (SK : Subgroup ↥L) = Kl := by
    refine (Subgroup.eq_of_le_of_card_ge hKSK ?_).symm
    rw [hKlcard]
    exact Nat.le_of_dvd hq.pos (hSylowCard SK)
  -- likewise for the cyclic group generated by `w`
  set wl : ↥L := ⟨w, hwL⟩ with hwl_def
  have hwlord : orderOf wl = q := by
    rw [← hwq]
    exact (orderOf_injective L.subtype (Subgroup.subtype_injective _) wl).symm
  have hWcard : Nat.card ↥(Subgroup.zpowers wl) = q := by
    rw [Nat.card_zpowers, hwlord]
  obtain ⟨SW, hWSW⟩ :=
    (IsPGroup.of_card (n := 1) (by rw [hWcard, pow_one]) :
      IsPGroup q ↥(Subgroup.zpowers wl)).exists_le_sylow
  -- conjugate the two Sylow subgroups
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) SW SK
  have hwlSW : wl ∈ (SW : Subgroup ↥L) := hWSW (Subgroup.mem_zpowers wl)
  have hconj : (MulAut.conj g) wl ∈ (SK : Subgroup ↥L) := by
    have h1 : (MulAut.conj g) • wl ∈ (MulAut.conj g) • (SW : Subgroup ↥L) :=
      Subgroup.smul_mem_pointwise_smul wl (MulAut.conj g) _ hwlSW
    have h2 : ((g • SW : Sylow q ↥L) : Subgroup ↥L)
        = (MulAut.conj g) • (SW : Subgroup ↥L) := Sylow.coe_subgroup_smul
    rw [← h2, hg] at h1
    exact h1
  rw [hSKeq, hKl_def, Subgroup.mem_subgroupOf] at hconj
  refine ⟨(g : G), ?_, ?_⟩
  · have h3 : (((MulAut.conj g) wl : ↥L) : G) = (g : G) * w * (g : G)⁻¹ := rfl
    rwa [h3] at hconj
  · intro h4
    have h5 : w = 1 := by
      have h6 : (g : G)⁻¹ * ((g : G) * w * (g : G)⁻¹) * (g : G) = w := by group
      rw [h4] at h6
      simpa using h6.symm
    rw [h5, orderOf_one] at hwq
    exact hq.one_lt.ne' hwq.symm

include hyp in
/-- **Step (13), the exclusion of `r = |K|`** (p. 113): the prime `q = |K|`
does not divide `|J|`.

Otherwise `J` contains an element `x` of order `q`; being strongly real, `x` is
conjugate to some `u·t` (`u ∈ Q₀#`) inside the Lemma-4 group `L`, and there to a
generator `k` of `K` (Sylow).  Transporting `st` along the same conjugation
produces a strongly real element `y` of order 3 centralising `K`, which is
impossible. -/
theorem not_card_K_dvd_ncard_invertedBy
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    {q : ℕ} (hq : q.Prime) (hqK : Nat.card ↥hyp.K = q)
    (hqQ0 : ¬ q ∣ Nat.card ↥hyp.Q0 * (Nat.card ↥hyp.Q0 + 1)) (hq3 : q ≠ 3) :
    ¬ q ∣ (invertedBy (Subgroup.centralizer
      ({hyp.distinguishedInvolution * hyp.t} : Set G))
      hyp.distinguishedInvolution).ncard := by
  classical
  intro hdvd
  set s := hyp.distinguishedInvolution with hs_def
  have hs2 : s * s = 1 := by rw [← sq]; exact hyp.distinguishedInvolution_sq
  have hst2 : (s * hyp.t) ^ 2 ≠ 1 := by
    intro h
    have h2 : orderOf (s * hyp.t) ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hst] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer ({s * hyp.t} : Set G))) :=
    hyp.centralizer_natCard_odd_of_stronglyReal
      hyp.isStronglyReal_distinguishedInvolution_mul_t hst2
  -- `q = |K|` is odd, since `K ≤ D` and `|D|` is odd.
  have hqodd : Odd q := by
    rw [← hqK]
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hyp.K_le_D
    have hD := hyp.D_odd
    rw [hc] at hD
    exact (Nat.odd_mul.mp hD).1
  -- Cauchy inside `J` gives `x` of order `q`.
  obtain ⟨x, hxJ, hxord⟩ := exists_orderOf_eq_prime_of_dvd_ncard_invertedBy
    hs2 hodd hyp.conj_mem_centralizer_mul_t hq hdvd
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hxord] at h1
    have h2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1
    rw [h2] at hqodd
    exact (Nat.not_odd_iff_even.mpr (even_two)) hqodd
  have hSR := hyp.isStronglyReal_of_mem_invertedBy_centralizer hxJ hx2
  -- normal form and Sylow transport: `x` is conjugate to a generator of `K`.
  obtain ⟨u, huQ0, -, hconj⟩ := hyp.exists_isConj_mul_t_of_stronglyReal hSR hx2
  obtain ⟨c₁, hc₁⟩ := isConj_iff.mp hconj
  have hordut : orderOf (u * hyp.t) = q := by
    rw [← hc₁, ← hxord]
    exact orderOf_injective (MulAut.conj c₁).toMonoidHom
      (MulAut.conj c₁).injective x
  have humem : u * hyp.t ∈ hyp.orderThreeGeneratedSubgroup :=
    mul_mem (hyp.orderThree_Q0_le huQ0) hyp.orderThree_t_mem
  obtain ⟨g, hgK, hgne⟩ :=
    hyp.exists_conj_mem_K_of_orderOf_eq hst hq hqK hqQ0 humem hordut
  set c : G := g * c₁ with hc_def
  set k : G := g * (u * hyp.t) * g⁻¹ with hk_def
  have hcx : c * x * c⁻¹ = k := by
    rw [hc_def, hk_def, ← hc₁]
    group
  -- `K` is generated by `k`.
  have hKz : hyp.K = Subgroup.zpowers k := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgK) ?_).symm
    have hordk : orderOf k = q := by
      have h1 : orderOf k ∣ q := by
        rw [← hqK]
        have h2 := orderOf_dvd_natCard (⟨k, hgK⟩ : ↥hyp.K)
        have heq : orderOf k = orderOf (⟨k, hgK⟩ : ↥hyp.K) :=
          orderOf_injective hyp.K.subtype (Subgroup.subtype_injective _) ⟨k, hgK⟩
        rw [heq]
        exact h2
      rcases (Nat.dvd_prime hq).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hgne
      · exact h
    rw [Nat.card_zpowers, hordk, hqK]
  -- transport `st` along the same conjugation
  set y : G := c * (s * hyp.t) * c⁻¹ with hy_def
  have hyord : orderOf y = 3 := by
    rw [hy_def, ← hst]
    exact orderOf_injective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective (s * hyp.t)
  have hySR : IsStronglyReal y := by
    refine ⟨c * s * c⁻¹, ⟨?_, ?_⟩, c * hyp.t * c⁻¹, ⟨?_, ?_⟩, by rw [hy_def]; group⟩
    · have h := hyp.distinguishedInvolution_sq
      calc (c * s * c⁻¹) ^ 2 = (c * s * c⁻¹) * (c * s * c⁻¹) := pow_two _
        _ = c * (s * s) * c⁻¹ := by group
        _ = c * s ^ 2 * c⁻¹ := by rw [pow_two]
        _ = c * 1 * c⁻¹ := by rw [h]
        _ = 1 := by group
    · intro h
      apply hyp.distinguishedInvolution_ne_one
      have h1 : c⁻¹ * (c * s * c⁻¹) * c = s := by group
      rw [h] at h1
      simpa using h1.symm
    · calc (c * hyp.t * c⁻¹) ^ 2
          = (c * hyp.t * c⁻¹) * (c * hyp.t * c⁻¹) := pow_two _
        _ = c * (hyp.t * hyp.t) * c⁻¹ := by group
        _ = c * hyp.t ^ 2 * c⁻¹ := by rw [pow_two]
        _ = c * 1 * c⁻¹ := by rw [hyp.t_sq]
        _ = 1 := by group
    · intro h
      apply hyp.t_ne_one
      have h1 : c⁻¹ * (c * hyp.t * c⁻¹) * c = hyp.t := by group
      rw [h] at h1
      simpa using h1.symm
  have hy2 : y ^ 2 ≠ 1 := by
    intro h
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hyord] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    omega
  -- `y` centralises `k`, hence all of `K = ⟨k⟩`
  have hyk : y * k = k * y := by
    have hxst : x * (s * hyp.t) = (s * hyp.t) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxJ.1
    rw [hy_def, ← hcx]
    calc (c * (s * hyp.t) * c⁻¹) * (c * x * c⁻¹)
        = c * ((s * hyp.t) * x) * c⁻¹ := by group
      _ = c * (x * (s * hyp.t)) * c⁻¹ := by rw [hxst]
      _ = (c * x * c⁻¹) * (c * (s * hyp.t) * c⁻¹) := by group
  have hyK : y ∈ Subgroup.centralizer (hyp.K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hKz, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hh
    obtain ⟨n, rfl⟩ := hh
    exact (Commute.zpow_left (show Commute k y from hyk.symm) n).eq
  -- contradiction with the `r = 7` obstruction
  refine hyp.not_mem_centralizer_K_of_isStronglyReal hySR hy2 ?_ hyK
  rw [hyord, hqK]
  exact (Nat.coprime_primes (by norm_num) hq).mpr (fun h => hq3 h.symm)

include hyp in
/-- **Step (13), the `J`-side conclusion** (p. 113): in the First-Case numerics
(`|Q₀| = 8`, `|K| = 7`) the set `J` has `3`-power cardinality.

Every prime `r` dividing `|J|` divides `|L| = 8·7·9 = 504`, is odd (as `|J|`
divides the odd `|C_G(st)|`), and is not `7` by the previous theorem; so `r = 3`
and `|J|` is a power of `3`. -/
theorem exists_ncard_invertedBy_eq_three_pow
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hQ0 : Nat.card ↥hyp.Q0 = 8) (hK : Nat.card ↥hyp.K = 7) :
    ∃ n : ℕ, (invertedBy (Subgroup.centralizer
      ({hyp.distinguishedInvolution * hyp.t} : Set G))
      hyp.distinguishedInvolution).ncard = 3 ^ n := by
  classical
  set s := hyp.distinguishedInvolution with hs_def
  set N : ℕ := (invertedBy (Subgroup.centralizer ({s * hyp.t} : Set G)) s).ncard
    with hN_def
  have hst2 : (s * hyp.t) ^ 2 ≠ 1 := by
    intro h
    have h2 : orderOf (s * hyp.t) ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hst] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  -- `|J|` divides the odd `|C_G(st)|`
  have hoddC : Odd (Nat.card ↥(Subgroup.centralizer ({s * hyp.t} : Set G))) :=
    hyp.centralizer_natCard_odd_of_stronglyReal
      hyp.isStronglyReal_distinguishedInvolution_mul_t hst2
  have hNdvd : N ∣ Nat.card ↥(Subgroup.centralizer ({s * hyp.t} : Set G)) :=
    Dvd.intro_left _ (hyp.card_centralizer_mul_t_eq hst2).symm
  have hNodd : Odd N := by
    obtain ⟨c, hc⟩ := hNdvd
    rw [hc] at hoddC
    exact (Nat.odd_mul.mp hoddC).1
  have hNne : N ≠ 0 := by
    intro h
    rw [h, Nat.odd_iff] at hNodd
    omega
  -- every prime divisor of `N` equals `3`
  refine ⟨N.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hNne ?_⟩
  intro r hr hrdvd
  have hrL : r ∣ Nat.card ↥hyp.Q0 * Nat.card ↥hyp.K * (Nat.card ↥hyp.Q0 + 1) :=
    hyp.dvd_card_orderThree_of_dvd_ncard_invertedBy hst hr hrdvd
  rw [hQ0, hK] at hrL
  have hr2 : r ≠ 2 := by
    intro h
    rw [h] at hrdvd
    rw [Nat.odd_iff] at hNodd
    omega
  have hr7 : r ≠ 7 := by
    intro h
    refine hyp.not_card_K_dvd_ncard_invertedBy hst (by norm_num) hK ?_
      (by norm_num) (h ▸ hrdvd)
    rw [hQ0]
    norm_num
  -- `r ∣ 8·7·9` with `r ∉ {2, 7}` forces `r = 3`
  rcases (Nat.Prime.dvd_mul hr).mp hrL with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hr.dvd_of_dvd_pow (n := 3) (by rw [show (2 : ℕ) ^ 3 = 8 from rfl]; exact h')))
        hr2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h') hr7
  · exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp
      (hr.dvd_of_dvd_pow (n := 2) (by rw [show (3 : ℕ) ^ 2 = 9 from rfl]; exact h))

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
