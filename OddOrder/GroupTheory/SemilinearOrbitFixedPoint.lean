/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SemilinearFixedPoint
import OddOrder.GroupTheory.FreeActionOrbitCount
import Mathlib.GroupTheory.PGroup

/-!
# A fixed point on a free orbit, from Hilbert 90

Let a finite abelian group `K` act *freely* on a finite group `M` (freely off the
identity), and let `g` be an automorphism of `M` of prime order `p` normalizing
that action through `α : K ≃* K`.  Suppose moreover that `K` carries a *field*
realization `μ : K ≃* Fˣ` for which `α` becomes a non-trivial field automorphism
`σ` of `F`.  If `p` does not divide the number `(|M| − 1) / |K|` of non-trivial
`K`-orbits, then `g` has a non-trivial fixed point on `M`.

The two ingredients:

* **Orbit counting.**  `g` permutes the `K`-orbits and fixes `{1}`; if it fixed no
  other orbit, all remaining orbits would fall into `⟨g⟩`-cycles of length `p`,
  forcing `p ∣ (|M| − 1) / |K|`.  So some `ω₀ ≠ 1` has `g ω₀` in its own
  `K`-orbit.
* **Hilbert 90.**  On that orbit `K` acts simply transitively, so `g ω₀ = c₀ • ω₀`
  for a unique `c₀ ∈ K`, and `g ^ p = 1` says exactly that `μ c₀` has norm `1` for
  `F / F^σ`.  `OddOrder.RingAut.exists_ne_zero_mul_pow_eq` then solves
  `σ(a) · μ c₀ = a`, and `μ⁻¹ a • ω₀` is the fixed point.

This replaces the (unavailable) Frobenius argument of Peterfalvi Part II,
Ch. III §1, p. 117 — see `Peterfalvi/Appendices/Suzuki/StructureOfH/WNeBot.lean`.

## Main results

* `OddOrder.GroupTheory.exists_mem_orbit_of_not_dvd_orbitCount` — some non-trivial
  `K`-orbit is `g`-invariant.
* `OddOrder.GroupTheory.exists_ne_one_fixed_of_free_orbit_semilinear` — the fixed
  point.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

open MulAction

section OrbitCount

variable {M : Type*} [Group M] [Finite M] {K : Type*} [Group K] [Finite K]
  (ψ : K →* MulAut M)

/-- **Some non-trivial `K`-orbit is `g`-invariant.**

`g` permutes the `K`-orbits (it normalizes the `K`-action through `α`) and fixes
the singleton orbit `{1}`.  Since `g ^ p = 1`, the orbit space is a `⟨g⟩`-set for
a group of `p`-power order, so its cardinality is congruent mod `p` to the number
of `g`-fixed orbits.  There are `1 + (|M| − 1) / |K|` orbits in all
(`card_orbits_eq_of_free_off_unique_fixed`), so if `{1}` were the only fixed one
we would get `p ∣ (|M| − 1) / |K|`. -/
theorem exists_mem_orbit_of_not_dvd_orbitCount [Nontrivial K]
    (hfree : ∀ (k : K) (u : M), u ≠ 1 → ψ k u = u → k = 1)
    {g : MulAut M} {α : K ≃* K} (hα : ∀ k, ψ (α k) = g * ψ k * g⁻¹)
    {p : ℕ} (hp : p.Prime) (hgp : g ^ p = 1)
    (hnd : ¬ p ∣ (Nat.card M - 1) / Nat.card K) :
    ∃ (ω₀ : M) (c₀ : K), ω₀ ≠ 1 ∧ g ω₀ = ψ c₀ ω₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction K M := MulAction.compHom M ψ
  have hsmul : ∀ (k : K) (u : M), k • u = ψ k u := fun _ _ => rfl
  -- the identity is the unique fixed point, and `K` acts freely off it
  have hone : (1 : M) ∈ fixedPoints K M := fun k => by rw [hsmul]; exact map_one (ψ k)
  have huniq : ∀ u : M, u ∈ fixedPoints K M → u = 1 := by
    intro u hu
    by_contra hne
    obtain ⟨k, hk⟩ := exists_ne (1 : K)
    exact hk (hfree k u hne (by rw [← hsmul]; exact hu k))
  have hstab : ∀ u : M, u ≠ 1 → stabilizer K u = ⊥ := by
    intro u hu
    refine le_bot_iff.mp fun k hk => Subgroup.mem_bot.mpr (hfree k u hu ?_)
    rw [← hsmul]; exact hk
  have hfree' : ∀ u : M, u ∉ fixedPoints K M → Nat.card (orbit K u) = Nat.card K := by
    intro u hu
    have hne : u ≠ 1 := fun h => hu (h ▸ hone)
    rw [Nat.card_congr (orbitEquivQuotientStabilizer K u), hstab u hne]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  have hcount : Nat.card (orbitRel.Quotient K M) = 1 + (Nat.card M - 1) / Nat.card K :=
    FreeActionOrbitCount.card_orbits_eq_of_free_off_unique_fixed 1 hone huniq hfree'
  -- `g` descends to a permutation of the orbit space
  have hαinv : ∀ k : K, ψ (α.symm k) = g⁻¹ * ψ k * g := by
    intro k
    have h := hα (α.symm k)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    group
  have hwd : ∀ a b : M, a ∈ orbit K b → g a ∈ orbit K (g b) := by
    rintro a b ⟨k, rfl⟩
    refine ⟨α k, ?_⟩
    have := hα k
    simp only [hsmul]
    rw [show ψ (α k) (g b) = (g * ψ k * g⁻¹) (g b) by rw [this]]
    simp
  have hwd' : ∀ a b : M, a ∈ orbit K b → g⁻¹ a ∈ orbit K (g⁻¹ b) := by
    rintro a b ⟨k, rfl⟩
    refine ⟨α.symm k, ?_⟩
    simp only [hsmul]
    rw [show ψ (α.symm k) (g⁻¹ b) = (g⁻¹ * ψ k * g) (g⁻¹ b) by rw [hαinv k]]
    simp
  set Y := orbitRel.Quotient K M with hY
  set Φ : Equiv.Perm Y :=
    { toFun := Quotient.map' (fun u => g u) hwd
      invFun := Quotient.map' (fun u => g⁻¹ u) hwd'
      left_inv := by
        rintro ⟨u⟩
        change Quotient.map' _ hwd' (Quotient.map' _ hwd (Quotient.mk'' u)) = Quotient.mk'' u
        simp only [Quotient.map'_mk'']
        congr 1
        simp
      right_inv := by
        rintro ⟨u⟩
        change Quotient.map' _ hwd (Quotient.map' _ hwd' (Quotient.mk'' u)) = Quotient.mk'' u
        simp only [Quotient.map'_mk'']
        congr 1
        simp } with hΦ
  have hΦmk : ∀ u : M, Φ (Quotient.mk'' u) = Quotient.mk'' (g u) := fun _ => rfl
  have hΦpow : ∀ (n : ℕ) (u : M), (Φ ^ n) (Quotient.mk'' u) = Quotient.mk'' ((g ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ, Equiv.Perm.mul_apply, hΦmk, ih]
      congr 1
  have hΦp : Φ ^ p = 1 := by
    ext y
    obtain ⟨u, rfl⟩ := Quotient.mk''_surjective y
    rw [hΦpow, hgp]
    rfl
  -- the orbit space as a `⟨Φ⟩`-set
  set Γ : Subgroup (Equiv.Perm Y) := Subgroup.zpowers Φ with hΓ
  haveI : Finite Y := Finite.of_surjective (Quotient.mk'' : M → Y) Quotient.mk''_surjective
  have hΓp : IsPGroup p Γ := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    apply Subtype.ext
    have hval : ((x ^ p ^ 1 : ↥Γ) : Equiv.Perm Y) = (x : Equiv.Perm Y) ^ p ^ 1 := by
      push_cast; rfl
    rw [hval, ← hn, pow_one, ← zpow_natCast (Φ ^ n) p, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hΦp, one_zpow]
    rfl
  letI : MulAction Γ Y := MulAction.compHom Y Γ.subtype
  have hmod : Nat.card Y ≡ Nat.card (fixedPoints Γ Y) [MOD p] :=
    hΓp.card_modEq_card_fixedPoints Y
  -- if `⟦1⟧` were the only fixed orbit, `p ∣ (|M| − 1) / |K|`
  by_cases hex : ∃ (ω₀ : M) (c₀ : K), ω₀ ≠ 1 ∧ g ω₀ = ψ c₀ ω₀
  · exact hex
  exfalso
  push Not at hex
  have hΦone : Φ (Quotient.mk'' (1 : M)) = Quotient.mk'' (1 : M) := by
    rw [hΦmk]
    congr 1
    exact map_one g
  have hfixone : (Quotient.mk'' (1 : M) : Y) ∈ fixedPoints Γ Y := by
    rintro ⟨γ, hγ⟩
    have hΦstab : Φ ∈ MulAction.stabilizer (Equiv.Perm Y) (Quotient.mk'' (1 : M) : Y) :=
      hΦone
    exact (Subgroup.zpowers_le.mpr hΦstab) hγ
  have hfixuniq : ∀ y : Y, y ∈ fixedPoints Γ Y → y = Quotient.mk'' (1 : M) := by
    intro y hy
    obtain ⟨u, rfl⟩ := Quotient.mk''_surjective y
    have hΦfix : Φ (Quotient.mk'' u) = Quotient.mk'' u := by
      have := hy ⟨Φ, Subgroup.mem_zpowers Φ⟩
      exact this
    rw [hΦmk] at hΦfix
    have hmem : g u ∈ orbit K u := Quotient.eq''.mp hΦfix
    obtain ⟨c₀, hc₀⟩ := hmem
    by_cases hu1 : u = 1
    · rw [hu1]
    · exact absurd (hc₀.symm.trans (hsmul c₀ u)) (hex u c₀ hu1)
  have hfixcard : Nat.card (fixedPoints Γ Y) = 1 := by
    refine Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => Subtype.ext ((hfixuniq a a.2).trans (hfixuniq b b.2).symm)⟩,
        ⟨(⟨_, hfixone⟩ : ↥(fixedPoints Γ Y))⟩⟩
  rw [hfixcard, hcount] at hmod
  refine hnd ?_
  have hdvd : p ∣ (1 + (Nat.card M - 1) / Nat.card K) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).mp hmod.symm
  simpa using hdvd

end OrbitCount

section Torsor

variable {M : Type*} [Group M] [Finite M] {K : Type*} [CommGroup K] [Finite K]

/-- **Hilbert 90 on a free orbit.**

`K` acts freely on `M`, `g` normalizes the action through `α` and has `g ^ p = 1`,
and `μ : K ≃* Fˣ` realizes `α` as a non-trivial field automorphism `σ`.  If `p`
does not divide the number of non-trivial `K`-orbits, then `g` fixes a
non-trivial element of `M`.

`exists_mem_orbit_of_not_dvd_orbitCount` supplies an orbit `K · ω₀` that `g`
preserves, say `g ω₀ = ψ c₀ ω₀`; iterating, `g ^ p = 1` forces
`∏_{i < p} α^i c₀ = 1`, i.e. the norm of `c := μ c₀` is `1`.  Multiplication by
`c` composed with `σ` is then a `σ`-semilinear additive automorphism of the line
`F` of order dividing `p`, so `exists_ne_zero_fixed_of_semilinear` gives
`x ≠ 0` with `c · σ x = x`; then `μ⁻¹ x · ω₀` is fixed by `g`. -/
theorem exists_ne_one_fixed_of_free_orbit_semilinear [Nontrivial K]
    (ψ : K →* MulAut M)
    (hfree : ∀ (k : K) (u : M), u ≠ 1 → ψ k u = u → k = 1)
    {g : MulAut M} {α : K ≃* K} (hα : ∀ k, ψ (α k) = g * ψ k * g⁻¹)
    {p : ℕ} (hp : p.Prime) (hgp : g ^ p = 1)
    {F : Type*} [Field F] [Finite F] (μ : K ≃* Fˣ) {σ : RingAut F}
    (hμσ : ∀ k : K, ((μ (α k) : Fˣ) : F) = σ ((μ k : Fˣ) : F)) (hσne : σ ≠ 1)
    (hnd : ¬ p ∣ (Nat.card M - 1) / Nat.card K) :
    ∃ u : M, u ≠ 1 ∧ g u = u := by
  classical
  obtain ⟨ω₀, c₀, hω₀, hgω₀⟩ :=
    exists_mem_orbit_of_not_dvd_orbitCount ψ hfree hα hp hgp hnd
  set c : F := ((μ c₀ : Fˣ) : F) with hcdef
  have hcne : c ≠ 0 := (μ c₀).ne_zero
  -- conjugating the action through `g`
  have hstep : ∀ (P : K) (u : M), g (ψ P u) = ψ (α P) (g u) := by
    intro P u
    rw [hα P]
    change g (ψ P u) = g (ψ P (g⁻¹ (g u)))
    rw [MulAut.inv_apply_self]
  -- `μ` intertwines the iterates of `α` and of `σ`
  have hμσpow : ∀ (n : ℕ) (k : K),
      ((μ ((α ^ n) k) : Fˣ) : F) = (σ ^ n) ((μ k : Fˣ) : F) := by
    intro n
    induction n with
    | zero => intro k; rfl
    | succ n ih =>
      intro k
      rw [pow_succ, MulAut.mul_apply, ih, hμσ, pow_succ]
      rfl
  -- `σ ^ p = 1`, because `g ^ p = 1` and the action is faithful
  have hαpow : ∀ (n : ℕ) (k : K), ψ ((α ^ n) k) = g ^ n * ψ k * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ]
      group
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun k hk => ?_
    exact hfree k ω₀ hω₀ (by rw [hk]; rfl)
  have hσp : σ ^ p = 1 := by
    ext x
    by_cases hx : x = 0
    · rw [hx]; simp
    · set k : K := μ.symm (Units.mk0 x hx) with hk
      have hμk : ((μ k : Fˣ) : F) = x := by
        rw [hk, MulEquiv.apply_symm_apply]
        rfl
      have hαp : (α ^ p) k = k := by
        refine hψinj ?_
        rw [hαpow, hgp]
        group
      have h1 := hμσpow p k
      rw [hαp, hμk] at h1
      exact h1.symm
  -- the norm of `c` is `1`
  have hgpow : ∀ n : ℕ, (g ^ n) ω₀ = ψ (∏ i ∈ Finset.range n, (α ^ i) c₀) ω₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hprod : α (∏ i ∈ Finset.range n, (α ^ i) c₀) * c₀
          = ∏ i ∈ Finset.range (n + 1), (α ^ i) c₀ := by
        rw [Finset.prod_range_succ' (fun i => (α ^ i) c₀) n, map_prod]
        have h1 : ∀ i ∈ Finset.range n, α ((α ^ i) c₀) = (α ^ (i + 1)) c₀ :=
          fun i _ => by rw [← MulAut.mul_apply, ← pow_succ']
        rw [Finset.prod_congr rfl h1, pow_zero]
        rfl
      rw [pow_succ', MulAut.mul_apply, ih, hstep, hgω₀, ← MulAut.mul_apply, ← map_mul,
        hprod]
  have hnorm₀ : ∏ i ∈ Finset.range p, (α ^ i) c₀ = 1 := by
    refine hfree _ ω₀ hω₀ ?_
    rw [← hgpow p, hgp]
    rfl
  have hnorm : ∏ i ∈ Finset.range p, (σ ^ i) c = 1 := by
    calc ∏ i ∈ Finset.range p, (σ ^ i) c
        = ∏ i ∈ Finset.range p, ((μ ((α ^ i) c₀) : Fˣ) : F) :=
          Finset.prod_congr rfl fun i _ => (hμσpow i c₀).symm
      _ = ((∏ i ∈ Finset.range p, μ ((α ^ i) c₀) : Fˣ) : F) :=
          (map_prod (Units.coeHom F) _ _).symm
      _ = 1 := by rw [← map_prod μ, hnorm₀, map_one]; rfl
  -- the semilinear automorphism `x ↦ c * σ x` of the line `F`
  set T : F ≃+ F :=
    { toFun := fun x => c * σ x
      invFun := fun x => σ.symm (c⁻¹ * x)
      left_inv := fun x => by
        change σ.symm (c⁻¹ * (c * σ x)) = x
        rw [inv_mul_cancel_left₀ hcne, RingEquiv.symm_apply_apply]
      right_inv := fun x => by
        change c * σ (σ.symm (c⁻¹ * x)) = x
        rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ hcne]
      map_add' := fun x y => by
        show c * σ (x + y) = c * σ x + c * σ y
        rw [map_add, mul_add] } with hTdef
  have hTapp : ∀ x : F, T x = c * σ x := fun _ => rfl
  have hTiter : ∀ (n : ℕ) (x : F),
      (T : F → F)^[n] x = (∏ i ∈ Finset.range n, (σ ^ i) c) * (σ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, hTapp, map_mul, map_prod,
        Finset.prod_range_succ', pow_succ']
      have hshift : ∀ i ∈ Finset.range n, σ ((σ ^ i) c) = (σ ^ (i + 1)) c := by
        intro i _
        rw [pow_succ']
        rfl
      rw [Finset.prod_congr rfl hshift, pow_zero]
      change _ = ((∏ i ∈ Finset.range n, (σ ^ (i + 1)) c) * c) * σ ((σ ^ n) x)
      ring
  have hTp : ∀ x : F, (T : F → F)^[p] x = x := by
    intro x
    rw [hTiter, hnorm, hσp]
    simp
  obtain ⟨x, hxne, hxfix⟩ :=
    OddOrder.exists_ne_zero_fixed_of_semilinear (e₀ := (1 : F)) one_ne_zero
      (fun y => ⟨y, by simp⟩) T σ (fun a y => by
        change c * σ (a • y) = σ a • (c * σ y)
        rw [smul_eq_mul, smul_eq_mul, map_mul]
        ring) hp hTp hσne
  -- transport the solution back
  have hfix' : c * σ x = x := by rw [← hTapp]; exact hxfix
  set k : K := μ.symm (Units.mk0 x hxne) with hk
  have hμk : ((μ k : Fˣ) : F) = x := by
    rw [hk, MulEquiv.apply_symm_apply]
    rfl
  have hkey : α k * c₀ = k := by
    refine μ.injective (Units.ext ?_)
    rw [map_mul, Units.val_mul, hμσ k, hμk, ← hcdef, mul_comm]
    exact hfix'
  refine ⟨ψ k ω₀, fun h => hω₀ ((ψ k).injective (by rw [h]; exact (map_one (ψ k)).symm)), ?_⟩
  rw [hstep, hgω₀, ← MulAut.mul_apply, ← map_mul, hkey]

end Torsor

end OddOrder.GroupTheory
