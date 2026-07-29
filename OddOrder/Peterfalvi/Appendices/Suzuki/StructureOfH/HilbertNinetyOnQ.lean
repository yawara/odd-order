/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.TwoKSubgroups
import OddOrder.Peterfalvi.Appendices.SemilinearField

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

## Main results

* `Hypothesis.exists_mem_inf_centralizer_not_mem_Q0` — for a `K`- and
  `X`-invariant `N` with `Q₀ ≤ N ≤ Q` of order `q²`, some element of
  `C_Q(X)` lies outside `Q₀`.
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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
