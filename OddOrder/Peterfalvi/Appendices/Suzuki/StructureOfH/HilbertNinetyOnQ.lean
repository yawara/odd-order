/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.FieldRealizationK
import OddOrder.GroupTheory.SemilinearOrbitFixedPoint

/-!
# `C_{S/Q₀}(P) ≠ 1` from Hilbert 90

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §1, Proposition, p. 117:

> But `[K, P] ⋊ P` is a Frobenius group acting on `S/Q₀` and `[K, P]` acts
> without fixed points on `S/Q₀`, so `C_{S/Q₀}(P) ≠ 1`.

The Frobenius property asserted there needs `|P|` prime to `|K|`, which
Chapter III does not supply — and which genuinely fails in some of its
configurations (see `WielandtOnQ.lean` for that route, valid when
`p ∤ q₀ − 1`).  The conclusion is nevertheless correct, for a different reason:
`K` is cyclic and acts fixed-point-freely on a `K`-invariant subgroup `N/Q₀` of
order `q`, hence turns it into a line over a field with `q` elements
(Appendix I, Proposition 2), and `P` acts on that line semilinearly with a
non-trivial twist.  **Hilbert's Theorem 90** then produces the fixed vector,
with no coprimality whatsoever.

The non-triviality of the twist is exactly `W = C_V(K) = 1`: an element of `V`
centralizing `K` lies in `W`.

Running the same argument on a `K`-*orbit* rather than on a `K`-submodule
removes the need for an invariant `N` altogether: the book's count of the
`K`-subgroups of `S` of order `q²` (which in type B goes through the projective
line over `𝔽_q`) is replaced by the elementary observation that `P`, of order
prime to `q + 1`, must fix one of the `q + 1` `K`-orbits on `S/Q₀`.

## Main results

* `Hypothesis.exists_mem_inf_centralizer_not_mem_Q0` — for a `K`- and
  `X`-invariant `N` with `Q₀ ≤ N ≤ Q` of order `q²`, some element of
  `C_Q(X)` lies outside `Q₀`.
* `Hypothesis.exists_mem_inf_centralizer_not_mem_Q0_of_orbit` — the same
  conclusion with no invariant `N`, assuming only `|Q| = q³` and `p ∤ q + 1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise
open OddOrder.GroupTheory OddOrder.Isaacs.Ch03

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **The `PSL(2, ℓ)` branch's `C_{S/Q₀}(P) ≠ 1`, without any coprimality**
(Peterfalvi Part II, Ch. III §1, p. 117, in the corrected form).

`N/Q₀` has order `q`, `K` acts on it fixed-point-freely (`hKfree`) and has order
`q − 1`, so the action is transitive on the non-identity elements and in
particular irreducible.  Appendix I, Proposition 2 therefore makes `N/Q₀` a line
over a field of order `q` on which `K` acts by scalars, and a generator `x` of
`X` acts semilinearly.  Its twist is non-trivial because `x` does not centralize
`K` (`W = 1`), so Hilbert 90
(`Huppert.exists_ne_one_fixed_of_prime_pow_eq_one`) gives a non-trivial fixed
point of `x` in `N/Q₀`; a coprime lift (Isaacs Cor 3.28) turns it into an
element of `C_Q(X)` outside `Q₀`. -/
theorem exists_mem_inf_centralizer_not_mem_Q0
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    (hKfree : ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q,
      k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0)
    (hQ2 : IsPGroup 2 ↥hyp.Q) (hQ0two : 2 ≤ Nat.card ↥hyp.Q0)
    (hW : hyp.W = ⊥) {X : Subgroup G} (hXV : X ≤ hyp.V)
    {p : ℕ} (hp : p.Prime) (hXcard : Nat.card ↥X = p)
    {N : Subgroup G} (hQ0N : hyp.Q0 ≤ N) (hNQ : N ≤ hyp.Q)
    (hNcard : Nat.card ↥N = Nat.card ↥hyp.Q0 ^ 2)
    (hNK : ∀ k ∈ hyp.K, ∀ y ∈ N, k * y * k⁻¹ ∈ N)
    (hNX : ∀ g ∈ X, ∀ y ∈ N, g * y * g⁻¹ ∈ N) :
    ∃ y ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G), y ∉ hyp.Q0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q with hMdef
  set π : ↥hyp.Q →* M := QuotientGroup.mk' (Subgroup.center ↥hyp.Q) with hπ
  -- the center of `Q` is `Q₀`
  have hmemZ : ∀ (y : G) (hy : y ∈ hyp.Q),
      (⟨y, hy⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q ↔ y ∈ hyp.Q0 := by
    intro y hy
    rw [hZQ0]
    exact Subgroup.mem_subgroupOf
  have hπone : ∀ (y : G) (hy : y ∈ hyp.Q), π ⟨y, hy⟩ = 1 ↔ y ∈ hyp.Q0 := by
    intro y hy
    rw [hπ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hmemZ y hy
  -- the operator group `A = K ⊔ X`
  have hXH : X ≤ hyp.H := hXV.trans (hyp.V_le_D.trans hyp.D_le_H)
  have hKH : hyp.K ≤ hyp.H := hyp.K_le_D.trans hyp.D_le_H
  set A : Subgroup G := hyp.K ⊔ X with hAdef
  have hKA : hyp.K ≤ A := le_sup_left
  have hXA : X ≤ A := le_sup_right
  have hAH : A ≤ hyp.H := sup_le hKH hXH
  have hNinv : ∀ a ∈ A, ∀ y ∈ N, a * y * a⁻¹ ∈ N := conj_mem_sup hNK hNX
  -- the image `U` of `N` in the central quotient
  set U : Subgroup M := (N.subgroupOf hyp.Q).map π with hUdef
  have hUinv : IsAInvariant (hyp.conjQuotientBy hAH) U :=
    aInvariant_map_of_conj_mem hAH hNinv
  have hUmem : ∀ u : M, u ∈ U → ∃ (y : G) (hy : y ∈ hyp.Q), y ∈ N ∧ π ⟨y, hy⟩ = u := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨(v : G), v.2, Subgroup.mem_subgroupOf.mp hv, rfl⟩
  -- the action of `A` on the central quotient, evaluated
  have hact : ∀ (a : ↥A) (y : G) (hy : y ∈ hyp.Q),
      (hyp.conjQuotientBy hAH) a (π ⟨y, hy⟩)
        = π ⟨(a : G) * y * (a : G)⁻¹, hyp.Q_normal_in_H (a : G) (hAH a.2) y hy⟩ := by
    intro a y hy
    rw [conjQuotientBy, IsAInvariant.quotientMulAutHom_apply_mk']
    rfl
  -- `|U| = |Q₀|`
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hUlift : hyp.liftCentralQuotient U = N := by
    have hCle : Subgroup.center ↥hyp.Q ≤ N.subgroupOf hyp.Q := by
      intro v hv
      exact Subgroup.mem_subgroupOf.mpr (hQ0N ((hmemZ (v : G) v.2).mp hv))
    have hcomap : (U.comap π) = N.subgroupOf hyp.Q := by
      rw [hUdef, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hCle]
    rw [liftCentralQuotient, hcomap, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNQ]
  have hUcard : Nat.card ↥U = Nat.card ↥hyp.Q0 := by
    have h1 := card_liftCentralQuotient (hyp := hyp) U
    rw [hUlift, hNcard, hZcard, sq] at h1
    have hpos : 0 < Nat.card ↥hyp.Q0 := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1.symm
  -- `K` acts freely on `U ∖ {1}`
  have hUfree : ∀ (k : G) (hk : k ∈ hyp.K), k ≠ 1 → ∀ u ∈ U,
      (hyp.conjQuotientBy hAH) ⟨k, hKA hk⟩ u = u → u = 1 := by
    intro k hk hk1 u hu hfix
    obtain ⟨y, hy, -, rfl⟩ := hUmem u hu
    rw [hact ⟨k, hKA hk⟩ y hy, hπ, QuotientGroup.mk'_eq_mk'] at hfix
    obtain ⟨z, hzZ, hz⟩ := hfix
    have hzc : ∀ w : ↥hyp.Q, w * z⁻¹ = z⁻¹ * w := by
      intro w
      have := (Subgroup.mem_center_iff.mp hzZ) w
      exact (inv_mul_eq_iff_eq_mul.mpr (by rw [← mul_assoc, ← this, mul_assoc,
        mul_inv_cancel, mul_one])).symm
    set a : ↥hyp.Q := ⟨k * y * k⁻¹, hyp.Q_normal_in_H k (hKH hk) y hy⟩ with hadef
    have hab : a * (⟨y, hy⟩ : ↥hyp.Q)⁻¹ = z⁻¹ := by
      rw [← hz, mul_inv_rev, ← mul_assoc, hzc a, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : k * y * k⁻¹ * y⁻¹ ∈ hyp.Q :=
      hyp.Q.mul_mem (hyp.Q_normal_in_H k (hKH hk) y hy) (hyp.Q.inv_mem hy)
    have hval : (⟨k * y * k⁻¹ * y⁻¹, hmem⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q := by
      have : (⟨k * y * k⁻¹ * y⁻¹, hmem⟩ : ↥hyp.Q) = a * (⟨y, hy⟩ : ↥hyp.Q)⁻¹ := rfl
      rw [this, hab]
      exact Subgroup.inv_mem _ hzZ
    exact (hπone y hy).mpr (hKfree k hk hk1 y hy ((hmemZ _ hmem).mp hval))
  -- `U` is a non-trivial elementary abelian `2`-group
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hUcard
    omega
  haveI hUnontriv : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
  have hUEA : IsElementaryAbelian 2 ↥U := hQEA.to_subgroup U
  letI : CommGroup ↥U := { (inferInstance : Group ↥U) with mul_comm := hUEA.comm }
  -- the restricted actions
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
  set ψ₀ : ↥A →* MulAut ↥U := hUinv.restrict with hψ₀
  set ψ : ↥hyp.K →* MulAut ↥U := ψ₀.comp (Subgroup.inclusion hKA) with hψ
  have hψval : ∀ (k : ↥hyp.K) (u : ↥U),
      ((ψ k u : ↥U) : M) = (hyp.conjQuotientBy hAH) ⟨(k : G), hKA k.2⟩ (u : M) := by
    intro k u; rfl
  -- freeness in subtype form
  have hfree' : ∀ (k : ↥hyp.K) (u : ↥U), u ≠ 1 → ψ k u = u → k = 1 := by
    intro k u hu hfix
    by_contra hkne
    refine hu (Subtype.ext ?_)
    refine hUfree (k : G) k.2 (fun h => hkne (Subtype.ext h)) (u : M) u.2 ?_
    rw [← hψval k u, hfix]
  -- the conjugating element `x` and its automorphism `g`
  haveI : Nontrivial ↥X := by
    refine (Subgroup.nontrivial_iff_ne_bot X).mpr fun hbot => ?_
    rw [hbot, Subgroup.card_bot] at hXcard
    exact hp.one_lt.ne hXcard
  obtain ⟨x₀, hx₀⟩ := exists_ne (1 : ↥X)
  obtain ⟨x, hxX⟩ := x₀
  have hxne : x ≠ 1 := fun h => hx₀ (Subtype.ext h)
  have hordx : orderOf (⟨x, hxX⟩ : ↥X) = p := by
    have hdvd : orderOf (⟨x, hxX⟩ : ↥X) ∣ p := hXcard ▸ orderOf_dvd_natCard _
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hx₀
    · exact h
  have hxp : x ^ p = 1 := by
    have h := pow_orderOf_eq_one (⟨x, hxX⟩ : ↥X)
    rw [hordx] at h
    exact congrArg (Subtype.val (p := fun z => z ∈ X)) h
  set xA : ↥A := ⟨x, hXA hxX⟩ with hxAdef
  set g : MulAut ↥U := ψ₀ xA with hgdef
  have hxAp : xA ^ p = 1 := by
    apply Subtype.ext
    simpa using hxp
  have hgp : g ^ p = 1 := by rw [hgdef, ← map_pow, hxAp, map_one]
  -- conjugation by `x` on `K`
  have hxD : x ∈ hyp.D := hyp.V_le_D (hXV hxX)
  have hcK : ∀ k ∈ hyp.K, x * k * x⁻¹ ∈ hyp.K := fun k hk => hyp.conj_mem_K_of_mem_D hxD hk
  have hcK' : ∀ k ∈ hyp.K, x⁻¹ * k * x ∈ hyp.K := by
    intro k hk
    have h := hyp.conj_mem_K_of_mem_D (hyp.D.inv_mem hxD) hk
    rwa [show x⁻¹ * k * x⁻¹⁻¹ = x⁻¹ * k * x from by group] at h
  set c : ↥hyp.K ≃* ↥hyp.K :=
    { toFun := fun k => ⟨x * (k : G) * x⁻¹, hcK _ k.2⟩
      invFun := fun k => ⟨x⁻¹ * (k : G) * x, hcK' _ k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k l => Subtype.ext (by push_cast; group) } with hcdef
  have hcval : ∀ k : ↥hyp.K, ((c k : ↥hyp.K) : G) = x * (k : G) * x⁻¹ := fun _ => rfl
  have hcψ : ∀ t : ↥hyp.K, ψ (c t) = g * ψ t * g⁻¹ := by
    intro t
    have h1 : (Subgroup.inclusion hKA) (c t) = xA * (Subgroup.inclusion hKA t) * xA⁻¹ :=
      Subtype.ext rfl
    calc ψ (c t) = ψ₀ (xA * (Subgroup.inclusion hKA t) * xA⁻¹) := by
          rw [hψ, MonoidHom.comp_apply, h1]
      _ = g * ψ t * g⁻¹ := by
          rw [map_mul, map_mul, map_inv, hgdef, hψ, MonoidHom.comp_apply]
  -- the twist is non-trivial: `x` does not centralize `K` since `W = 1`
  obtain ⟨k₀, hk₀K, hk₀ne⟩ : ∃ k ∈ hyp.K, x * k * x⁻¹ ≠ k := by
    by_contra hcon
    push Not at hcon
    have hxW : x ∈ hyp.W := by
      refine ⟨hXV hxX, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have hkK : k ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk
      have h := hcon k hkK
      calc k * x = (x * k * x⁻¹) * x := by rw [h]
        _ = x * k := by group
    rw [hW, Subgroup.mem_bot] at hxW
    exact hxne hxW
  have ht₀ : ψ (c ⟨k₀, hk₀K⟩) ≠ ψ (⟨k₀, hk₀K⟩ : ↥hyp.K) := by
    intro heq
    have h1 : ψ ((c ⟨k₀, hk₀K⟩) * (⟨k₀, hk₀K⟩ : ↥hyp.K)⁻¹) = 1 := by
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    obtain ⟨u, hu⟩ := exists_ne (1 : ↥U)
    have h2 : (c ⟨k₀, hk₀K⟩) * (⟨k₀, hk₀K⟩ : ↥hyp.K)⁻¹ = 1 := by
      refine hfree' _ u hu ?_
      rw [h1]; rfl
    have h3 : c ⟨k₀, hk₀K⟩ = (⟨k₀, hk₀K⟩ : ↥hyp.K) := mul_inv_eq_one.mp h2
    have h4 := hcval ⟨k₀, hk₀K⟩
    rw [h3] at h4
    exact hk₀ne h4.symm
  -- irreducibility of the `K`-action on `U`
  have hirr : ∀ B : Subgroup ↥U, IsAInvariant ψ B → B = ⊥ ∨ B = ⊤ := by
    intro B hB
    by_cases hBbot : B = ⊥
    · exact Or.inl hBbot
    right
    obtain ⟨b, hbB, hb1⟩ : ∃ b : ↥U, b ∈ B ∧ b ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hBbot (le_bot_iff.mp fun y hy => Subgroup.mem_bot.mpr (hcon y hy))
    have hbne : ∀ k : ↥hyp.K, ψ k b ≠ 1 := by
      intro k h
      exact hb1 (by simpa using congrArg (ψ k)⁻¹ h)
    set f : Option ↥hyp.K → ↥B := fun o =>
      o.rec (⟨1, B.one_mem⟩) (fun k => ⟨ψ k b, hB.smul_mem k hbB⟩) with hfdef
    have hfinj : Function.Injective f := by
      rintro (_ | k) (_ | l) h
      · rfl
      · exact absurd (congrArg (Subtype.val (p := fun z => z ∈ B)) h).symm (hbne l)
      · exact absurd (congrArg (Subtype.val (p := fun z => z ∈ B)) h) (hbne k)
      · have hval : ψ k b = ψ l b := congrArg (Subtype.val (p := fun z => z ∈ B)) h
        have hfix : ψ (l⁻¹ * k) b = b := by
          rw [map_mul, map_inv]
          change (ψ l)⁻¹ ((ψ k) b) = b
          rw [hval]
          simp
        have := hfree' _ b hb1 hfix
        exact congrArg some (by
          have h2 : l⁻¹ * k = 1 := this
          exact (inv_mul_eq_one.mp h2).symm)
    have hcard : Nat.card ↥hyp.K + 1 ≤ Nat.card ↥B := by
      have := Nat.card_le_card_of_injective f hfinj
      rwa [Finite.card_option] at this
    have hKcard : Nat.card ↥hyp.K = Nat.card ↥hyp.Q0 - 1 := hyp.card_K_eq_card_Q0_sub_one
    have hBle : Nat.card ↥B ≤ Nat.card ↥U := Subgroup.card_le_card_group B
    refine Subgroup.eq_top_of_card_eq B ?_
    rw [hUcard] at hBle ⊢
    omega
  -- Hilbert 90
  obtain ⟨e, hene, hefix⟩ :=
    Huppert.exists_ne_one_fixed_of_prime_pow_eq_one hUEA ψ hirr hcψ ht₀ hp hgp
  -- transport the fixed point back to `Q`
  obtain ⟨y, hyQ, -, hyπ⟩ := hUmem (e : M) e.2
  have heM : (e : M) ≠ 1 := fun h => hene (Subtype.ext h)
  have hyQ0 : y ∉ hyp.Q0 := by
    rw [← hπone y hyQ]
    intro h
    exact heM (by rw [← hyπ, h])
  -- every element of `X` fixes `(e : M)`
  have hstab : ∀ (a : G) (ha : a ∈ X),
      (hyp.conjQuotientBy hAH) ⟨a, hXA ha⟩ (e : M) = (e : M) := by
    intro a ha
    have hzp : Subgroup.zpowers (⟨x, hxX⟩ : ↥X) = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [Nat.card_zpowers, hordx, hXcard]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨x, hxX⟩ : ↥X) ^ n = ⟨a, ha⟩ := by
      have : (⟨a, ha⟩ : ↥X) ∈ Subgroup.zpowers (⟨x, hxX⟩ : ↥X) := by rw [hzp]; trivial
      exact this
    have hxa : a = x ^ n := by
      have := congrArg (Subtype.val (p := fun z => z ∈ X)) hn
      push_cast at this
      exact this.symm
    have hAeq : (⟨a, hXA ha⟩ : ↥A) = xA ^ n := Subtype.ext (by push_cast [hxa]; rfl)
    have hfixg : (hyp.conjQuotientBy hAH) xA (e : M) = (e : M) := by
      have := congrArg (Subtype.val (p := fun z => z ∈ U)) hefix
      rw [hgdef] at this
      exact this
    have hmemstab : (hyp.conjQuotientBy hAH) xA ∈
        MulAction.stabilizer (MulAut M) (e : M) := hfixg
    have := Subgroup.zpow_mem (MulAction.stabilizer (MulAut M) (e : M)) hmemstab n
    rw [hAeq, map_zpow]
    exact this
  -- coprime lifting (Isaacs Cor 3.28)
  have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥hyp.Q) := by
    obtain ⟨j, hj⟩ := hQ2.exists_card_eq
    rw [hj]
    refine Nat.Coprime.pow_right j ?_
    have hdvd : Nat.card ↥X ∣ Nat.card ↥hyp.D :=
      Subgroup.card_dvd_of_le (hXV.trans hyp.V_le_D)
    have hodd : Odd (Nat.card ↥X) := hyp.D_odd.of_dvd_nat hdvd
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.mp hodd)).symm
  have hsolv : IsSolvable ↥hyp.Q := by
    haveI := hQ2.isNilpotent
    infer_instance
  have hZinv : IsAInvariant (hyp.conjQBy hXH) (Subgroup.center ↥hyp.Q) :=
    IsAInvariant.of_characteristic (hyp.conjQBy hXH)
  have hgfix : ∀ a : ↥X, ∃ n ∈ Subgroup.center ↥hyp.Q,
      (hyp.conjQBy hXH) a (⟨y, hyQ⟩ : ↥hyp.Q) = (⟨y, hyQ⟩ : ↥hyp.Q) * n := by
    intro a
    have hconj : (a : G) * y * (a : G)⁻¹ ∈ hyp.Q :=
      hyp.Q_normal_in_H (a : G) (hXH a.2) y hyQ
    have h1 : π ⟨(a : G) * y * (a : G)⁻¹, hconj⟩ = π ⟨y, hyQ⟩ := by
      rw [← hact ⟨(a : G), hXA a.2⟩ y hyQ, hyπ, hstab (a : G) a.2, ← hyπ]
    rw [hπ, QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have hval : (hyp.conjQBy hXH a) (⟨y, hyQ⟩ : ↥hyp.Q)
        = (⟨(a : G) * y * (a : G)⁻¹, hconj⟩ : ↥hyp.Q) := rfl
    refine ⟨z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
    have key : ∀ b b' : ↥hyp.Q, b * z = b' → b = b' * z⁻¹ := by
      intro b b' h
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hval]
    exact key _ _ hzeq
  obtain ⟨w, hwfix, z, hzZ, hwz⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := hyp.conjQBy hXH)
      hcop (Or.inr hsolv) hZinv hgfix
  refine ⟨(w : G), ⟨w.2, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have h := hwfix ⟨a, ha⟩
    have hval : ((hyp.conjQBy hXH ⟨a, ha⟩ w : ↥hyp.Q) : G) = a * (w : G) * a⁻¹ := rfl
    have h2 : a * (w : G) * a⁻¹ = (w : G) := by rw [← hval, h]
    calc a * (w : G) = (a * (w : G) * a⁻¹) * a := by group
      _ = (w : G) * a := by rw [h2]
  · intro hmem
    have hz1 : π z = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hzZ
    have hwπ : π w = π ⟨y, hyQ⟩ := by
      rw [hwz, map_mul, hz1, mul_one]
    have h1 : π w = 1 := (hπone (w : G) w.2).mpr hmem
    rw [hwπ, hyπ] at h1
    exact heM h1

/-- **`C_{S/Q₀}(P) ≠ 1` with no invariant subgroup as input** (Peterfalvi
Part II, Ch. III §1, p. 117, case (3), in the corrected form).

`K` acts freely on `S/Q₀ = Q ⧸ Z(Q)` off the identity, so its orbits there have
length `|K| = q − 1` and there are `(q² − 1) / (q − 1) = q + 1` of them.  A
group `P` of prime order `p ∤ q + 1` therefore fixes one of them setwise, and on
that orbit — a `K`-torsor — Hilbert 90 produces a fixed point of `P`
(`exists_ne_one_fixed_of_free_orbit_semilinear`), the field data coming from the
action of `K` on `Q₀` (`exists_field_realization_K`).  A coprime lift (Isaacs
Cor 3.28) turns it into an element of `C_Q(P)` outside `Q₀`.

Unlike `exists_mem_inf_centralizer_not_mem_Q0` this needs no `K`-invariant
subgroup of order `q²`, so it bypasses the book's count of those subgroups —
the one step of case (3) whose type-B half is not proved in the text. -/
theorem exists_mem_inf_centralizer_not_mem_Q0_of_orbit
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hKfree : ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q,
      k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0)
    (hQ2 : IsPGroup 2 ↥hyp.Q) (hQ0two : 2 ≤ Nat.card ↥hyp.Q0)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (hW : hyp.W = ⊥) {X : Subgroup G} (hXV : X ≤ hyp.V)
    {p : ℕ} (hp : p.Prime) (hXcard : Nat.card ↥X = p)
    (hnd : ¬ p ∣ Nat.card ↥hyp.Q0 + 1) :
    ∃ y ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G), y ∉ hyp.Q0 := by
  classical
  set M := ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q with hMdef
  set π : ↥hyp.Q →* M := QuotientGroup.mk' (Subgroup.center ↥hyp.Q) with hπ
  -- the center of `Q` is `Q₀`
  have hmemZ : ∀ (y : G) (hy : y ∈ hyp.Q),
      (⟨y, hy⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q ↔ y ∈ hyp.Q0 := by
    intro y hy
    rw [hZQ0]
    exact Subgroup.mem_subgroupOf
  have hπone : ∀ (y : G) (hy : y ∈ hyp.Q), π ⟨y, hy⟩ = 1 ↔ y ∈ hyp.Q0 := by
    intro y hy
    rw [hπ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hmemZ y hy
  -- the operator group `A = K ⊔ X`
  have hXH : X ≤ hyp.H := hXV.trans (hyp.V_le_D.trans hyp.D_le_H)
  have hKH : hyp.K ≤ hyp.H := hyp.K_le_D.trans hyp.D_le_H
  set A : Subgroup G := hyp.K ⊔ X with hAdef
  have hKA : hyp.K ≤ A := le_sup_left
  have hXA : X ≤ A := le_sup_right
  have hAH : A ≤ hyp.H := sup_le hKH hXH
  have hact : ∀ (a : ↥A) (y : G) (hy : y ∈ hyp.Q),
      (hyp.conjQuotientBy hAH) a (π ⟨y, hy⟩)
        = π ⟨(a : G) * y * (a : G)⁻¹, hyp.Q_normal_in_H (a : G) (hAH a.2) y hy⟩ := by
    intro a y hy
    rw [conjQuotientBy, IsAInvariant.quotientMulAutHom_apply_mk']
    rfl
  -- `|Z(Q)| = |Q₀|`, hence `|M| = |Q₀|²`
  have hQ0pos : 0 < Nat.card ↥hyp.Q0 := by omega
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hMcard : Nat.card M = Nat.card ↥hyp.Q0 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥hyp.Q)
    rw [hZcard, hcardQ] at h
    refine Nat.eq_of_mul_eq_mul_right hQ0pos ?_
    rw [← h]; ring
  -- the restricted action of `K` on the central quotient
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
  set ψ : ↥hyp.K →* MulAut M :=
    (hyp.conjQuotientBy hAH).comp (Subgroup.inclusion hKA) with hψ
  have hψval : ∀ (k : ↥hyp.K) (u : M),
      ψ k u = (hyp.conjQuotientBy hAH) ⟨(k : G), hKA k.2⟩ u := fun _ _ => rfl
  -- `K` acts freely off the identity
  have hfree : ∀ (k : ↥hyp.K) (u : M), u ≠ 1 → ψ k u = u → k = 1 := by
    intro k u hu hfix
    by_contra hkne
    obtain ⟨⟨y, hyQ⟩, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥hyp.Q) u
    have hk1 : (k : G) ≠ 1 := fun h => hkne (Subtype.ext h)
    rw [hψval k, hact ⟨(k : G), hKA k.2⟩ y hyQ, hπ, QuotientGroup.mk'_eq_mk'] at hfix
    obtain ⟨z, hzZ, hz⟩ := hfix
    have hzc : ∀ w : ↥hyp.Q, w * z⁻¹ = z⁻¹ * w := by
      intro w
      have := (Subgroup.mem_center_iff.mp hzZ) w
      exact (inv_mul_eq_iff_eq_mul.mpr (by rw [← mul_assoc, ← this, mul_assoc,
        mul_inv_cancel, mul_one])).symm
    set a : ↥hyp.Q := ⟨(k : G) * y * (k : G)⁻¹,
      hyp.Q_normal_in_H (k : G) (hKH k.2) y hyQ⟩ with hadef
    have hab : a * (⟨y, hyQ⟩ : ↥hyp.Q)⁻¹ = z⁻¹ := by
      rw [← hz, mul_inv_rev, ← mul_assoc, hzc a, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : (k : G) * y * (k : G)⁻¹ * y⁻¹ ∈ hyp.Q :=
      hyp.Q.mul_mem (hyp.Q_normal_in_H (k : G) (hKH k.2) y hyQ) (hyp.Q.inv_mem hyQ)
    have hval : (⟨(k : G) * y * (k : G)⁻¹ * y⁻¹, hmem⟩ : ↥hyp.Q)
        ∈ Subgroup.center ↥hyp.Q := by
      have heq : (⟨(k : G) * y * (k : G)⁻¹ * y⁻¹, hmem⟩ : ↥hyp.Q)
          = a * (⟨y, hyQ⟩ : ↥hyp.Q)⁻¹ := rfl
      rw [heq, hab]
      exact Subgroup.inv_mem _ hzZ
    exact hu ((hπone y hyQ).mpr (hKfree (k : G) k.2 hk1 y hyQ ((hmemZ _ hmem).mp hval)))
  -- the conjugating element `x` and its automorphism `g`
  haveI : Nontrivial ↥X := by
    refine (Subgroup.nontrivial_iff_ne_bot X).mpr fun hbot => ?_
    rw [hbot, Subgroup.card_bot] at hXcard
    exact hp.one_lt.ne hXcard
  obtain ⟨x₀, hx₀⟩ := exists_ne (1 : ↥X)
  obtain ⟨x, hxX⟩ := x₀
  have hxne : x ≠ 1 := fun h => hx₀ (Subtype.ext h)
  have hordx : orderOf (⟨x, hxX⟩ : ↥X) = p := by
    have hdvd : orderOf (⟨x, hxX⟩ : ↥X) ∣ p := hXcard ▸ orderOf_dvd_natCard _
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hx₀
    · exact h
  have hxp : x ^ p = 1 := by
    have h := pow_orderOf_eq_one (⟨x, hxX⟩ : ↥X)
    rw [hordx] at h
    exact congrArg (Subtype.val (p := fun z => z ∈ X)) h
  set xA : ↥A := ⟨x, hXA hxX⟩ with hxAdef
  set g : MulAut M := (hyp.conjQuotientBy hAH) xA with hgdef
  have hxAp : xA ^ p = 1 := by
    apply Subtype.ext
    simpa using hxp
  have hgp : g ^ p = 1 := by rw [hgdef, ← map_pow, hxAp, map_one]
  -- conjugation by `x` on `K`
  have hxD : x ∈ hyp.D := hyp.V_le_D (hXV hxX)
  have hcK : ∀ k ∈ hyp.K, x * k * x⁻¹ ∈ hyp.K := fun k hk => hyp.conj_mem_K_of_mem_D hxD hk
  have hcK' : ∀ k ∈ hyp.K, x⁻¹ * k * x ∈ hyp.K := by
    intro k hk
    have h := hyp.conj_mem_K_of_mem_D (hyp.D.inv_mem hxD) hk
    rwa [show x⁻¹ * k * x⁻¹⁻¹ = x⁻¹ * k * x from by group] at h
  set c : ↥hyp.K ≃* ↥hyp.K :=
    { toFun := fun k => ⟨x * (k : G) * x⁻¹, hcK _ k.2⟩
      invFun := fun k => ⟨x⁻¹ * (k : G) * x, hcK' _ k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k l => Subtype.ext (by push_cast; group) } with hcdef
  have hcval : ∀ k : ↥hyp.K, ((c k : ↥hyp.K) : G) = x * (k : G) * x⁻¹ := fun _ => rfl
  have hcψ : ∀ t : ↥hyp.K, ψ (c t) = g * ψ t * g⁻¹ := by
    intro t
    have h1 : (Subgroup.inclusion hKA) (c t) = xA * (Subgroup.inclusion hKA t) * xA⁻¹ :=
      Subtype.ext rfl
    calc ψ (c t) = (hyp.conjQuotientBy hAH)
          (xA * (Subgroup.inclusion hKA t) * xA⁻¹) := by
          rw [hψ, MonoidHom.comp_apply, h1]
      _ = g * ψ t * g⁻¹ := by
          rw [map_mul, map_mul, map_inv, hgdef, hψ, MonoidHom.comp_apply]
  -- `K ≠ 1`, since `W = C_V(K) = 1` and `x ≠ 1`
  haveI : Nontrivial ↥hyp.K := by
    refine (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot => hxne ?_
    have hxW : x ∈ hyp.W := by
      refine ⟨hXV hxX, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have hkK : k ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk
      rw [hbot, Subgroup.mem_bot] at hkK
      rw [hkK, one_mul, mul_one]
    rw [hW, Subgroup.mem_bot] at hxW
    exact hxW
  -- the field realization of `K` coming from `Q₀`
  obtain ⟨F, instF, instFin, μ, σ, hσne, -, hμσ⟩ :=
    hyp.exists_field_realization_K hW (hXV hxX) hxne c hcval
  letI : Field F := instF
  letI : Finite F := instFin
  -- there are `q + 1` non-trivial `K`-orbits on `M`, and `p ∤ q + 1`
  have hnd' : ¬ p ∣ (Nat.card M - 1) / Nat.card ↥hyp.K := by
    have hfact : Nat.card ↥hyp.Q0 ^ 2 - 1
        = (Nat.card ↥hyp.Q0 - 1) * (Nat.card ↥hyp.Q0 + 1) := by
      obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥hyp.Q0 = d + 1 :=
        ⟨Nat.card ↥hyp.Q0 - 1, by omega⟩
      rw [hd, show d + 1 - 1 = d by omega,
        show (d + 1) ^ 2 = d * (d + 2) + 1 by ring, show d * (d + 2) + 1 - 1
          = d * (d + 2) by omega, show d + 1 + 1 = d + 2 from rfl]
    rw [hMcard, hyp.card_K_eq_card_Q0_sub_one, hfact,
      Nat.mul_div_cancel_left _ (by omega : 0 < Nat.card ↥hyp.Q0 - 1)]
    exact hnd
  obtain ⟨u, hune, hufix⟩ :=
    OddOrder.GroupTheory.exists_ne_one_fixed_of_free_orbit_semilinear ψ hfree hcψ hp
      hgp μ hμσ hσne hnd'
  -- transport the fixed point back to `Q`
  obtain ⟨⟨y, hyQ⟩, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥hyp.Q) u
  have hyQ0 : y ∉ hyp.Q0 := fun h => hune ((hπone y hyQ).mpr h)
  -- every element of `X` fixes the class of `y`
  have hstab : ∀ (a : G) (ha : a ∈ X),
      (hyp.conjQuotientBy hAH) ⟨a, hXA ha⟩ (π ⟨y, hyQ⟩) = π ⟨y, hyQ⟩ := by
    intro a ha
    have hzp : Subgroup.zpowers (⟨x, hxX⟩ : ↥X) = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [Nat.card_zpowers, hordx, hXcard]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨x, hxX⟩ : ↥X) ^ n = ⟨a, ha⟩ := by
      have : (⟨a, ha⟩ : ↥X) ∈ Subgroup.zpowers (⟨x, hxX⟩ : ↥X) := by rw [hzp]; trivial
      exact this
    have hxa : a = x ^ n := by
      have := congrArg (Subtype.val (p := fun z => z ∈ X)) hn
      push_cast at this
      exact this.symm
    have hAeq : (⟨a, hXA ha⟩ : ↥A) = xA ^ n := Subtype.ext (by push_cast [hxa]; rfl)
    have hmemstab : (hyp.conjQuotientBy hAH) xA ∈
        MulAction.stabilizer (MulAut M) (π ⟨y, hyQ⟩) := hufix
    have := Subgroup.zpow_mem (MulAction.stabilizer (MulAut M) (π ⟨y, hyQ⟩)) hmemstab n
    rw [hAeq, map_zpow]
    exact this
  -- coprime lifting (Isaacs Cor 3.28)
  have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥hyp.Q) := by
    obtain ⟨j, hj⟩ := hQ2.exists_card_eq
    rw [hj]
    refine Nat.Coprime.pow_right j ?_
    have hdvd : Nat.card ↥X ∣ Nat.card ↥hyp.D :=
      Subgroup.card_dvd_of_le (hXV.trans hyp.V_le_D)
    have hodd : Odd (Nat.card ↥X) := hyp.D_odd.of_dvd_nat hdvd
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.mp hodd)).symm
  have hsolv : IsSolvable ↥hyp.Q := by
    haveI := hQ2.isNilpotent
    infer_instance
  have hZinv : IsAInvariant (hyp.conjQBy hXH) (Subgroup.center ↥hyp.Q) :=
    IsAInvariant.of_characteristic (hyp.conjQBy hXH)
  have hgfix : ∀ a : ↥X, ∃ n ∈ Subgroup.center ↥hyp.Q,
      (hyp.conjQBy hXH) a (⟨y, hyQ⟩ : ↥hyp.Q) = (⟨y, hyQ⟩ : ↥hyp.Q) * n := by
    intro a
    have hconj : (a : G) * y * (a : G)⁻¹ ∈ hyp.Q :=
      hyp.Q_normal_in_H (a : G) (hXH a.2) y hyQ
    have h1 : π ⟨(a : G) * y * (a : G)⁻¹, hconj⟩ = π ⟨y, hyQ⟩ := by
      rw [← hact ⟨(a : G), hXA a.2⟩ y hyQ, hstab (a : G) a.2]
    rw [hπ, QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have hval : (hyp.conjQBy hXH a) (⟨y, hyQ⟩ : ↥hyp.Q)
        = (⟨(a : G) * y * (a : G)⁻¹, hconj⟩ : ↥hyp.Q) := rfl
    refine ⟨z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
    have key : ∀ b b' : ↥hyp.Q, b * z = b' → b = b' * z⁻¹ := by
      intro b b' h
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hval]
    exact key _ _ hzeq
  obtain ⟨w, hwfix, z, hzZ, hwz⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := hyp.conjQBy hXH)
      hcop (Or.inr hsolv) hZinv hgfix
  refine ⟨(w : G), ⟨w.2, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have h := hwfix ⟨a, ha⟩
    have hval : ((hyp.conjQBy hXH ⟨a, ha⟩ w : ↥hyp.Q) : G) = a * (w : G) * a⁻¹ := rfl
    have h2 : a * (w : G) * a⁻¹ = (w : G) := by rw [← hval, h]
    calc a * (w : G) = (a * (w : G) * a⁻¹) * a := by group
      _ = (w : G) * a := by rw [h2]
  · intro hmem
    have hz1 : π z = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hzZ
    have hwπ : π w = π ⟨y, hyQ⟩ := by
      rw [hwz, map_mul, hz1, mul_one]
    exact hune (by rw [← hwπ]; exact (hπone (w : G) w.2).mpr hmem)

/-- **`Z(Q) = Q₀` when `|Q| = q³`** (Peterfalvi Part II, Ch. III §1, p. 117):
Higman's clause (d) says every central element of a Suzuki `2`-group of order
`q³` with a regular `q − 1` operator group squares to `1`, and `Q₀` collects
exactly the squares-to-one elements of `Q`. -/
theorem center_eq_Q0_subgroupOf_of_card_cube
    (hQsuz : Suzuki2Group.IsSuzuki2Group ↥hyp.Q) {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3) :
    Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q := by
  have hKcyc : IsCyclic ↥hyp.actualKActor := hyp.actualKActor_isCyclic
  have hreg := hyp.actualKActor_actsRegularlyOnInvolutions
  have hKKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
    have h1 : Nat.card ↥hyp.actualKActor = Nat.card ↥hyp.K :=
      Nat.card_congr (MonoidHom.ofInjective hyp.conjQByK_injective).toEquiv.symm
    rw [h1, hyp.card_K_eq_card_Q0_sub_one, hQ0card]
  have hcard : Nat.card ↥hyp.Q = (2 ^ m) ^ 3 := by rw [hcardQ, hQ0card]
  obtain ⟨-, hZsq, -⟩ :=
    OddOrder.Higman.Suzuki2Groups.center_payload_of_card_eq_cube hQsuz hKcyc hreg hm
      hKKcard hcard
  exact hyp.center_Q_eq_Q0_subgroupOf_of_sq_eq_one hZsq

/-- **`K` acts freely on `Q ⧸ Q₀`** (Peterfalvi Part II, Ch. I §2,
Proposition 1(a) plus a coprime action argument).

A nonidentity `k ∈ K` fixes only `1` in `Q` (`conjQByK_fixed_eq_one`), and
`|K| = |Q₀| − 1` is coprime to `|Q₀| = |Z(Q)|`, so the induced action on the
central quotient is again fixed-point-free. -/
theorem kfree_mod_Q0_of_center_eq
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q) :
    ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q, k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0 := by
  intro k hk hk1 y hy hcomm
  have hmemZ : ∀ (z : G) (hz : z ∈ hyp.Q),
      (⟨z, hz⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q ↔ z ∈ hyp.Q0 := by
    intro z hz
    rw [hZQ0]
    exact Subgroup.mem_subgroupOf
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hZinv : IsAInvariant hyp.conjQByK (Subgroup.center ↥hyp.Q) :=
    IsAInvariant.of_characteristic hyp.conjQByK
  have hcop : Nat.Coprime (Nat.card ↥hyp.K) (Nat.card ↥(Subgroup.center ↥hyp.Q)) :=
    Suzuki2Groups.card_coprime_of_card_eq_sub_one _
      (by rw [hyp.card_K_eq_card_Q0_sub_one, hZcard])
  have hfixed : ∀ k' : ↥hyp.K, k' ≠ 1 → ∀ z : ↥hyp.Q,
      hyp.conjQByK k' z = z → z ∈ Subgroup.center ↥hyp.Q := by
    intro k' hk' z hz
    rw [hyp.conjQByK_fixed_eq_one hk' hz]
    exact Subgroup.one_mem _
  have hq := Suzuki2Groups.quotient_fixedPointFree_of_fixedPoints_le
    hyp.conjQByK (Subgroup.center ↥hyp.Q) hZinv hcop hfixed
  -- the commutator is a central element of `Q`
  have hcQ : k * y * k⁻¹ * y⁻¹ ∈ hyp.Q :=
    hyp.Q.mul_mem (hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D hk)) y hy)
      (hyp.Q.inv_mem hy)
  have hcZ : (⟨k * y * k⁻¹ * y⁻¹, hcQ⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q :=
    (hmemZ _ hcQ).mpr hcomm
  have hcy : y * (k * y * k⁻¹ * y⁻¹) = (k * y * k⁻¹ * y⁻¹) * y := by
    have h := Subgroup.mem_center_iff.mp hcZ ⟨y, hy⟩
    exact congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) h
  have hval : k * y * k⁻¹ * (k * y * k⁻¹ * y⁻¹)⁻¹ = y := by
    have h1 : (k * y * k⁻¹ * y⁻¹) * y = k * y * k⁻¹ := by group
    calc k * y * k⁻¹ * (k * y * k⁻¹ * y⁻¹)⁻¹
        = ((k * y * k⁻¹ * y⁻¹) * y) * (k * y * k⁻¹ * y⁻¹)⁻¹ := by rw [h1]
      _ = (y * (k * y * k⁻¹ * y⁻¹)) * (k * y * k⁻¹ * y⁻¹)⁻¹ := by rw [hcy]
      _ = y := by group
  have hfix : IsAInvariant.quotientMulAutHom hZinv ⟨k, hk⟩
      (QuotientGroup.mk' (Subgroup.center ↥hyp.Q) ⟨y, hy⟩)
      = QuotientGroup.mk' (Subgroup.center ↥hyp.Q) ⟨y, hy⟩ := by
    rw [IsAInvariant.quotientMulAutHom_apply_mk', QuotientGroup.mk'_eq_mk']
    exact ⟨(⟨k * y * k⁻¹ * y⁻¹, hcQ⟩ : ↥hyp.Q)⁻¹, Subgroup.inv_mem _ hcZ,
      Subtype.ext hval⟩
  have hone := hq ⟨k, hk⟩ (fun h => hk1 (congrArg (Subtype.val
    (p := fun z => z ∈ hyp.K)) h)) _ hfix
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hone
  exact (hmemZ y hy).mp hone

/-- **`C_Q(P) ⊄ Q₀` in case (3)** (Peterfalvi Part II, Ch. III §1, p. 117),
packaged for the `PSL(2, ℓ)` branch: the hypotheses are exactly those of
case (3), plus `p ∤ q + 1`.

This is `exists_mem_inf_centralizer_not_mem_Q0_of_orbit` with `Z(Q) = Q₀`
(`center_eq_Q0_subgroupOf_of_card_cube`) and the freeness of `K` on `Q ⧸ Q₀`
(`kfree_mod_Q0_of_center_eq`) supplied from the Suzuki structure of `Q`. -/
theorem exists_mem_inf_centralizer_not_mem_Q0_of_card_cube
    (hQsuz : Suzuki2Group.IsSuzuki2Group ↥hyp.Q) {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (hW : hyp.W = ⊥) {X : Subgroup G} (hXV : X ≤ hyp.V)
    {p : ℕ} (hp : p.Prime) (hXcard : Nat.card ↥X = p)
    (hnd : ¬ p ∣ Nat.card ↥hyp.Q0 + 1) :
    ∃ y ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G), y ∉ hyp.Q0 := by
  have hZQ0 := hyp.center_eq_Q0_subgroupOf_of_card_cube hQsuz hm hQ0card hcardQ
  obtain ⟨hQ2, -, -, -⟩ := id hQsuz
  exact hyp.exists_mem_inf_centralizer_not_mem_Q0_of_orbit hZQ0
    (hyp.kfree_mod_Q0_of_center_eq hZQ0) hQ2 hyp.two_le_card_Q0 hcardQ hW hXV hp
    hXcard hnd

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
