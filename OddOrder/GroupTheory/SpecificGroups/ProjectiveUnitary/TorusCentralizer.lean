/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupStructure
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.StandardGenerators
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupSuzukiType

/-!
# The determinant-one torus does not act faithfully on `Ω₁(S₀)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, Proposition, p. 117:

> But, if `G₀ = PSU(3, ℓ)`, `S₀` is a Sylow `2`-subgroup of `G₀` and
> `N_{G₀}(S₀) = S₀ ⋊ D₀`, then, **as can be checked**, `C_{D₀}(Ω₁(S₀)) ≠ 1`.

Peterfalvi does not carry out the check.  In the coordinates of this
development it is a computation in `𝔽_{ℓ²}^×`:

* `Ω₁(S₀)` is `{u : RootGroup n | u.fst = 0}`, and the torus acts on the second
  coordinate through the norm `N(c) = c · c* = c^{ℓ+1}` (`scalePoint_snd`);
* the determinant-one torus `D₀` is the image of `t ↦ t^{2ℓ − 1}`
  (`PSUTorusParameter`);
* for `c = t^{2ℓ−1}` the norm is `t^{(2ℓ−1)(ℓ+1)}`, which is `1` as soon as `t`
  has order dividing `ℓ + 1`;
* an element of order exactly `ℓ + 1` gives `c ≠ 1`, because
  `2ℓ − 1 = 2(ℓ + 1) − 3` makes `(ℓ + 1) ∣ (2ℓ − 1)` equivalent to
  `(ℓ + 1) ∣ 3`, i.e. to `ℓ ≤ 2`.

This is exactly the point where `PSU(3, ℓ)` differs from `Sz(ℓ)`: the Suzuki
torus acts *regularly* on the involutions of its root group
(`standardRootTorus_actsRegularlyOnInvolutions`), so its centralizer there is
trivial, while the unitary torus has the norm-one subgroup of order `ℓ + 1` in
its kernel.

## Main results

* `exists_ne_one_mem_psuTorus_torusWeight_eq_one` — a non-trivial parameter of
  the determinant-one torus with trivial norm.
* `scalePoint_eq_of_torusWeight_eq_one` — *every* norm-one parameter fixes
  `Ω₁(S₀)` pointwise.
* `torusWeight_eq_one_of_commute_weylElement`,
  `commute_rootHom_of_commute_weylElement` — a determinant-one torus element
  commuting with the Weyl element has norm one, hence centralizes every
  involution of the standard root group.  This is the structure fact
  Peterfalvi Part II, Ch. IV §4 step (2) (p. 133) quotes for `V ∩ U`.
* `exists_ne_one_mem_psuTorus_scalePoint_eq_of_sq_eq_one` — the same in the
  form Peterfalvi uses: a non-trivial `c ∈ D₀` fixing every element of
  `Ω₁(S₀)`.
* `exists_ne_one_odd_centralizing_involutions_standardRoot` — the statement
  transported into `standardPermGroup n`: a non-trivial element of odd order
  commuting with every involution of the standard root group.
* `exists_ne_one_odd_centralizing_involutions_of_sylowTwo` — the same for an
  arbitrary Sylow `2`-subgroup, by Sylow conjugacy.  This is the form the
  Ch. III §1 Proposition consumes, because there the Sylow `2`-subgroup is the
  image of `C_Q(P)` and is not the standard one on the nose.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

open scoped Pointwise

/-- The order of the multiplicative group of the quadratic field. -/
theorem natCard_units_field (n : ℕ) (hn : 0 < n) :
    Nat.card (Field n)ˣ = 2 ^ (2 * n) - 1 := by
  classical
  haveI : Fintype (Field n) := Fintype.ofFinite (Field n)
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    natCard_field n hn]

/-- **`C_{D₀}(Ω₁(S₀)) ≠ 1`, in torus coordinates** (Peterfalvi Part II, Ch. III
§1, p. 117): the determinant-one torus contains a non-trivial parameter of norm
one.

`(Field n)ˣ` is cyclic of order `ℓ² − 1 = (ℓ − 1)(ℓ + 1)` with `ℓ = 2ⁿ`, so it
has an element `t` of order exactly `ℓ + 1`.  Then `c = t^{2ℓ−1}` lies in the
determinant-one torus and `c^{ℓ+1} = (t^{ℓ+1})^{2ℓ−1} = 1`, while `c ≠ 1`
because `(ℓ + 1) ∤ (2ℓ − 1)` for `ℓ ≥ 4`. -/
theorem exists_ne_one_mem_psuTorus_torusWeight_eq_one (n : ℕ) (hn : 1 < n) :
    ∃ c : GeneralTorusParameter n, c ∈ PSUTorusParameter n ∧ c ≠ 1 ∧
      torusWeight c = 1 := by
  classical
  have hn0 : 0 < n := Nat.zero_lt_one.trans hn
  set l : ℕ := 2 ^ n with hl
  have hl4 : 4 ≤ l := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  -- the unit group is cyclic of order `l² − 1`
  have hcard : Nat.card (Field n)ˣ = l ^ 2 - 1 := by
    rw [natCard_units_field n hn0, hl, ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Field n)ˣ)
  have hgord : orderOf g = l ^ 2 - 1 := by
    rw [← hcard, orderOf_eq_card_of_forall_mem_zpowers hg]
  obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have hkpos : 0 < k := by omega
  have hsub : l - 1 = k := by omega
  have hsq : l ^ 2 - 1 = k * (k + 2) := by
    have h1 : l ^ 2 = k * (k + 2) + 1 := by rw [hk]; ring
    omega
  have hdvd : (l - 1) ∣ l ^ 2 - 1 := ⟨k + 2, by rw [hsub, hsq]⟩
  set t : (Field n)ˣ := g ^ (l - 1) with ht
  have htord : orderOf t = l + 1 := by
    rw [ht, orderOf_pow_of_dvd (by omega) (hgord ▸ hdvd), hgord, hsub, hsq,
      Nat.mul_div_cancel_left _ hkpos]
    omega
  refine ⟨t ^ (2 * l - 1), ⟨t, rfl⟩, ?_, ?_⟩
  · -- `c ≠ 1` because `(l + 1) ∤ (2l − 1)`
    intro hc
    have hdvd' : orderOf t ∣ 2 * l - 1 := orderOf_dvd_of_pow_eq_one hc
    rw [htord] at hdvd'
    obtain ⟨j, hj⟩ := hdvd'
    have hj2 : j < 2 := by
      by_contra hge2
      push Not at hge2
      have hmul : (l + 1) * 2 ≤ (l + 1) * j := Nat.mul_le_mul_left _ hge2
      omega
    interval_cases j <;> omega
  · -- the norm is `t ^ ((2l − 1)(l + 1)) = 1`
    have htone : t ^ (l + 1) = 1 := by
      rw [← htord]; exact pow_orderOf_eq_one t
    have hone : (t ^ (2 * l - 1)) ^ (l + 1) = (1 : (Field n)ˣ) := by
      rw [← pow_mul, mul_comm, pow_mul, htone, one_pow]
    have hval : ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) ^ (l + 1) = 1 := by
      have hv := congrArg (Units.val (α := Field n)) hone
      simpa using hv
    rw [torusWeight, star_eq_conjugation, conjugation_apply n hn0]
    calc ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) *
        ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) ^ l
        = ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) ^ (l + 1) := by ring
      _ = 1 := hval

/-- Every torus parameter has odd order: the unit group of `𝔽_{ℓ²}` has order
`ℓ² − 1` with `ℓ` a power of two. -/
theorem odd_orderOf_psuTorusParameter (n : ℕ) (hn : 0 < n)
    (c : PSUTorusParameter n) : Odd (orderOf c) := by
  have hdvd : orderOf c ∣ Nat.card (GeneralTorusParameter n) := by
    refine dvd_trans (orderOf_dvd_natCard c) ?_
    exact Subgroup.card_subgroup_dvd_card _
  rw [natCard_units_field n hn] at hdvd
  have hodd : Odd (2 ^ (2 * n) - 1) := by
    have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have h2 : 2 ∣ 2 ^ (2 * n) :=
      dvd_pow_self 2 (by positivity)
    rcases h2 with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  exact hodd.of_dvd_nat hdvd

/-- **A determinant-one torus parameter commuting with the Weyl element has norm one.**

Weyl conjugation sends the parameter `c` to `(c*)⁻¹`
(`weylElement_mul_psuTorusHom_mul_weylElement`, `coe_weylParameterHom`), so it fixes `c`
exactly when `c c* = 1`, i.e. when `torusWeight c = 1`.

Together with `scalePoint_eq_of_torusWeight_eq_one` this is the `PSU(3, ℓ)` content of
Peterfalvi Part II, Ch. IV §4 step (2)'s "`(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`"
(p. 133): `V = C_D(t)` is the norm-one torus, which acts trivially on `Ω₁(S₀)`. -/
theorem torusWeight_eq_one_of_commute_weylElement {n : ℕ} (c : PSUTorusParameter n)
    (hc : Commute (weylElement n) (psuTorusHom n c)) :
    torusWeight (c : GeneralTorusParameter n) = 1 := by
  have hw2 : weylElement n * weylElement n = 1 := by
    have h := weylElement_sq_eq_one n
    rwa [sq] at h
  have h1 : psuTorusHom n (Unital.psuWeylParameterHom n c) = psuTorusHom n c := by
    rw [← weylElement_mul_psuTorusHom_mul_weylElement]
    calc weylElement n * psuTorusHom n c * weylElement n
        = (psuTorusHom n c * weylElement n) * weylElement n := by rw [hc.eq]
      _ = psuTorusHom n c * (weylElement n * weylElement n) := by group
      _ = psuTorusHom n c := by rw [hw2, mul_one]
  have h2 : Unital.psuWeylParameterHom n c = c := psuTorusHom_injective n h1
  have h3 : weylParameterHom n (c : GeneralTorusParameter n)
      = (c : GeneralTorusParameter n) := by
    rw [← Unital.coe_psuWeylParameterHom, h2]
  have hstar : (star ((c : GeneralTorusParameter n) : Field n))⁻¹
      = ((c : GeneralTorusParameter n) : Field n) := by
    rw [← coe_weylParameterHom]
    exact congrArg Units.val h3
  have hne : star ((c : GeneralTorusParameter n) : Field n) ≠ 0 :=
    (star_ne_zero (R := Field n)).2 (Units.ne_zero _)
  calc torusWeight (c : GeneralTorusParameter n)
      = ((c : GeneralTorusParameter n) : Field n) *
          star ((c : GeneralTorusParameter n) : Field n) := rfl
    _ = (star ((c : GeneralTorusParameter n) : Field n))⁻¹ *
          star ((c : GeneralTorusParameter n) : Field n) := by rw [hstar]
    _ = 1 := inv_mul_cancel₀ hne

/-- **A norm-one torus parameter fixes `Ω₁(S₀)` pointwise.**

`Ω₁(S₀)` is the centre line `{u | u.fst = 0}` (`sq_eq_one_iff_fst_eq_zero`), on
which the torus acts through the norm `N(c) = c^{ℓ+1}` (`scalePoint_snd`).  This
is the `PSU(3, ℓ)` structure fact behind Peterfalvi Part II, Ch. III §1's
`C_{D₀}(Ω₁(S₀)) ≠ 1` and Ch. IV §4 step (2)'s "`(V ∩ U)/(P ∩ U)` centralizes
`C_{Q₀}(P)`" (p. 133). -/
theorem scalePoint_eq_of_torusWeight_eq_one {n : ℕ} {c : GeneralTorusParameter n}
    (hw : torusWeight c = 1) {u : RootGroup n} (hu : u ^ 2 = 1) :
    scalePoint c u = u := by
  have hfst : u.fst = 0 := (RootGroup.sq_eq_one_iff_fst_eq_zero u).mp hu
  ext
  · rw [scalePoint_fst, hfst, mul_zero]
  · rw [scalePoint_snd, hw, one_mul]

/-- **`C_{D₀}(Ω₁(S₀)) ≠ 1`** (Peterfalvi Part II, Ch. III §1, Proposition,
p. 117, the step stated "as can be checked") — the norm-one parameter of
`exists_ne_one_mem_psuTorus_torusWeight_eq_one`, read through
`scalePoint_eq_of_torusWeight_eq_one`. -/
theorem exists_ne_one_mem_psuTorus_scalePoint_eq_of_sq_eq_one (n : ℕ) (hn : 1 < n) :
    ∃ c : GeneralTorusParameter n, c ∈ PSUTorusParameter n ∧ c ≠ 1 ∧
      ∀ u : RootGroup n, u ^ 2 = 1 → scalePoint c u = u := by
  obtain ⟨c, hmem, hne, hw⟩ := exists_ne_one_mem_psuTorus_torusWeight_eq_one n hn
  exact ⟨c, hmem, hne, fun _u hu => scalePoint_eq_of_torusWeight_eq_one hw hu⟩

/-- **Every determinant-one torus element commuting with the Weyl element centralizes the
involutions of the standard root group.**

This is the `PSU(3, ℓ)` structure fact Peterfalvi Part II, Ch. IV §4 step (2) (p. 133)
quotes as "by the structure of `PSU(3, ℓ)`, `(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`":
`V = C_D(t)` is the norm-one torus (`torusWeight_eq_one_of_commute_weylElement`), which
acts trivially on `Ω₁(S₀)` (`scalePoint_eq_of_torusWeight_eq_one`).

Unlike `exists_ne_one_odd_centralizing_involutions_standardRoot`, which produces one such
element, this quantifies over all of them — which is what step (2) needs. -/
theorem commute_rootHom_of_commute_weylElement {n : ℕ} (c : PSUTorusParameter n)
    (hc : Commute (weylElement n) (psuTorusHom n c))
    {u : RootGroup n} (hu : u ^ 2 = 1) :
    Commute (psuTorusHom n c) (rootHom n u) := by
  have hw := torusWeight_eq_one_of_commute_weylElement c hc
  have hconj := psuTorusHom_mul_rootHom_mul_inv c u
  rw [psuTorusScaleHom_apply, scalePoint_eq_of_torusWeight_eq_one hw hu] at hconj
  have heq : psuTorusHom n c * rootHom n u = rootHom n u * psuTorusHom n c :=
    calc psuTorusHom n c * rootHom n u
        = (psuTorusHom n c * rootHom n u * (psuTorusHom n c)⁻¹) * psuTorusHom n c := by
          group
      _ = rootHom n u * psuTorusHom n c := by rw [hconj]
  exact heq

/-! ## The same statement inside `standardPermGroup n` -/

/-- **`C_{D₀}(Ω₁(S₀)) ≠ 1`, for the standard Sylow `2`-subgroup**
(Peterfalvi Part II, Ch. III §1, Proposition, p. 117).

The determinant-one torus element of `exists_ne_one_mem_psuTorus_torusWeight_eq_one`,
read inside `standardPermGroup n`: it is non-trivial, of odd order, and it
commutes with every involution of the standard root group — which is a Sylow
`2`-subgroup (`standardRootSylow`). -/
theorem exists_ne_one_odd_centralizing_involutions_standardRoot
    (n : ℕ) (hn : 1 < n) :
    ∃ g : standardPermGroup n, g ≠ 1 ∧ Odd (orderOf g) ∧
      ∀ u ∈ standardRootSubgroup n, u ^ 2 = 1 → g * u = u * g := by
  obtain ⟨c, hmem, hne, hfix⟩ :=
    exists_ne_one_mem_psuTorus_scalePoint_eq_of_sq_eq_one n hn
  set d : PSUTorusParameter n := ⟨c, hmem⟩ with hd
  refine ⟨psuTorusHom n d, ?_, ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val
      (psuTorusHom_injective n (h.trans (map_one (psuTorusHom n)).symm)))
  · rw [orderOf_injective (psuTorusHom n) (psuTorusHom_injective n) d]
    exact odd_orderOf_psuTorusParameter n (Nat.zero_lt_one.trans hn) d
  · rintro _ ⟨v, rfl⟩ hsq
    have hv : v ^ 2 = 1 :=
      rootHom_injective n (by rw [map_pow, hsq, map_one])
    have hconj := psuTorusHom_mul_rootHom_mul_inv d v
    rw [psuTorusScaleHom_apply, hfix v hv] at hconj
    calc psuTorusHom n d * rootHom n v
        = (psuTorusHom n d * rootHom n v * (psuTorusHom n d)⁻¹) *
            psuTorusHom n d := by group
      _ = rootHom n v * psuTorusHom n d := by rw [hconj]

/-- **`C_{D₀}(Ω₁(S₀)) ≠ 1`, for an arbitrary Sylow `2`-subgroup**
(Peterfalvi Part II, Ch. III §1, Proposition, p. 117).

Sylow's theorem transports
`exists_ne_one_odd_centralizing_involutions_standardRoot` to any Sylow
`2`-subgroup `S`: the element that centralizes `Ω₁(S₀)` for the standard `S₀`
is conjugated along with `S₀`. -/
theorem exists_ne_one_odd_centralizing_involutions_of_sylowTwo
    (n : ℕ) (hn : 1 < n) (S : Sylow 2 (standardPermGroup n)) :
    ∃ g : standardPermGroup n, g ≠ 1 ∧ Odd (orderOf g) ∧
      ∀ u ∈ (S : Subgroup (standardPermGroup n)), u ^ 2 = 1 → g * u = u * g := by
  classical
  obtain ⟨g₀, hg₀ne, hg₀odd, hg₀fix⟩ :=
    exists_ne_one_odd_centralizing_involutions_standardRoot n hn
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (standardPermGroup n)
    (standardRootSylow n (Nat.zero_lt_one.trans hn)) S
  refine ⟨h * g₀ * h⁻¹, ?_, ?_, ?_⟩
  · intro hcon
    exact hg₀ne (by
      have := congrArg (fun x => h⁻¹ * x * h) hcon
      simpa [mul_assoc] using this)
  · have heq : orderOf (h * g₀ * h⁻¹) = orderOf g₀ := by
      simpa [MulAut.conj_apply] using
        orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective g₀
    rwa [heq]
  · intro u hu hsq
    -- `h⁻¹ u h` is an involution of the standard root subgroup
    have hmem : h⁻¹ * u * h ∈ standardRootSubgroup n := by
      have hSu : u ∈ (S : Set (standardPermGroup n)) := hu
      rw [← hh, Sylow.coe_smul] at hSu
      obtain ⟨x, hx, hxu⟩ := hSu
      have hxval : h * x * h⁻¹ = u := hxu
      have : h⁻¹ * u * h = x := by rw [← hxval]; group
      rw [this]
      exact hx
    have hsq' : (h⁻¹ * u * h) ^ 2 = 1 := by
      have hcp : (h⁻¹ * u * h) ^ 2 = h⁻¹ * u ^ 2 * (h⁻¹)⁻¹ :=
        conj_pow (a := h⁻¹) (b := u) (i := 2)
      rw [hcp, hsq, mul_one, inv_inv, inv_mul_cancel]
    have hc := hg₀fix _ hmem hsq'
    calc (h * g₀ * h⁻¹) * u
        = h * (g₀ * (h⁻¹ * u * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * u * h) * g₀) * h⁻¹ := by rw [hc]
      _ = u * (h * g₀ * h⁻¹) := by group

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
