/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowDecomposition
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualKActor
import OddOrder.GroupTheory.MinimalInvariantNormal

/-!
# Peterfalvi Part II: minimal invariant subgroups of the odd part `Q₁`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (3), p. 109 (setup).

Step (3) of Chapter II opens with: "Let `M` be an elementary abelian
`r`-subgroup of `Q₁` normalized by `KP` such that `M ≠ 1` and `M` is
minimal with these properties."  This leaf supplies that `M` at the
Chapter I level (`exists_minimal_invariant_elab`): for any subgroup
`X ≤ H` and any prime `r ∣ |Q₁|` there is a nontrivial `X`-invariant
elementary abelian `r`-subgroup `M ≤ Q₁` whose only nontrivial
`X`-invariant subgroup is `M` itself — i.e. `M` is an irreducible
`𝔽_r[X]`-module.

Supporting facts proved here:

* `H_le_normalizer_Q` / `H_le_normalizer_Q1` — `H` normalizes `Q` and its
  odd part `Q₁` (`Q₁Subgroup` is characteristic in `Q`);
* `coprime_card_Q_K` — `(|Q|, |K|) = 1`: the conjugation action of `K` on
  `Q` is Frobenius (§2 Proposition 1(a)), and Frobenius actions force
  coprime orders.  Chapter II uses this as `r ∤ |K|` for primes `r ∣ |Q₁|`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory (IsElementaryAbelian)
open OddOrder.Isaacs.Ch03 (IsAInvariant)

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## `H` normalizes `Q` and `Q₁` -/

/-- `H` normalizes `Q`: the `Subgroup.normalizer` form of `Q_normal_in_H`. -/
theorem H_le_normalizer_Q : hyp.H ≤ Subgroup.normalizer (hyp.Q : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hyp.Q_normal_in_H h hh x hx
  · intro hx
    have h2 := hyp.Q_normal_in_H h⁻¹ (inv_mem hh) _ hx
    simpa [mul_assoc] using h2

/-- `H` normalizes the odd part `Q₁`: conjugation by `h ∈ H` is an
automorphism of `Q`, and `Q₁Subgroup` is characteristic in `Q`. -/
theorem conj_mem_Q1_of_mem_H {h : G} (hh : h ∈ hyp.H) {x : G}
    (hx : x ∈ hyp.Q1) : h * x * h⁻¹ ∈ hyp.Q1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  set ψ : MulAut ↥hyp.Q :=
    hyp.Q.normalizerMonoidHom ⟨h, hyp.H_le_normalizer_Q hh⟩ with hψ
  have hmem : ψ y ∈ hyp.Q1Subgroup.map ψ.toMonoidHom := ⟨y, hy, rfl⟩
  rw [Subgroup.characteristic_iff_map_eq.mp hyp.Q1Subgroup_characteristic ψ]
    at hmem
  exact ⟨ψ y, hmem, rfl⟩

/-- The `Subgroup.normalizer` form: `H ≤ N_G(Q₁)`. -/
theorem H_le_normalizer_Q1 :
    hyp.H ≤ Subgroup.normalizer (hyp.Q1 : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hyp.conj_mem_Q1_of_mem_H hh hx
  · intro hx
    have h2 := hyp.conj_mem_Q1_of_mem_H (inv_mem hh) hx
    simpa [mul_assoc] using h2

/-! ## `(|Q|, |K|) = 1` -/

open OddOrder.Isaacs.Ch06 in
/-- `(|Q|, |K|) = 1`: the conjugation action of `K` on `Q` is Frobenius by
§2 Proposition 1(a) (`conjQByK_fixed_eq_one`), and a Frobenius action forces
coprime orders (`IsFrobeniusAction.coprime_card`).  Chapter II step (3) uses
this as `r ∤ |K|` for prime divisors `r` of `|Q₁|`. -/
theorem coprime_card_Q_K :
    Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥hyp.K) := by
  classical
  letI : MulDistribMulAction ↥hyp.K ↥hyp.Q :=
    MulDistribMulAction.compHom _ hyp.conjQByK
  have hFrob : IsFrobeniusAction ↥hyp.K ↥hyp.Q := by
    intro a ha n hn hann
    exact hn (hyp.conjQByK_fixed_eq_one ha hann)
  haveI : Fintype ↥hyp.Q := Fintype.ofFinite _
  haveI : Fintype ↥hyp.K := Fintype.ofFinite _
  have h := hFrob.coprime_card
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-! ## The minimal invariant elementary abelian `r`-subgroup of `Q₁` -/

/-- **Peterfalvi Part II, Ch. II, (3), the minimal module `M`** (p. 109), at
the Chapter I level: for `X ≤ H` and a prime `r ∣ |Q₁|` there is a
nontrivial `X`-invariant elementary abelian `r`-subgroup `M ≤ Q₁` whose only
nontrivial `X`-invariant subgroup is `M` itself (so `M` is an irreducible
`𝔽_r[X]`-module).

Construction: the Sylow `r`-subgroup `R` of the nilpotent group `Q₁` is
normal, hence characteristic, hence `X`-invariant; a minimal nontrivial
`X`-invariant normal subgroup of `R` is elementary abelian
(`exists_aInvariant_normal_isElementaryAbelian`), and a minimal element of
the resulting nonempty family of candidates has the stated minimality. -/
theorem exists_minimal_invariant_elab {X : Subgroup G} (hX : X ≤ hyp.H)
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card ↥hyp.Q1) :
    ∃ M : Subgroup G, M ≤ hyp.Q1 ∧ M ≠ ⊥ ∧ IsElementaryAbelian r ↥M ∧
      (∀ g ∈ X, ∀ m ∈ M, g * m * g⁻¹ ∈ M) ∧
      ∀ B ≤ M, (∀ g ∈ X, ∀ m ∈ B, g * m * g⁻¹ ∈ B) → B ≠ ⊥ → B = M := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  -- The candidate family and a minimal element of it.
  set S : Set (Subgroup G) := {A | A ≤ hyp.Q1 ∧ A ≠ ⊥ ∧
    IsElementaryAbelian r ↥A ∧ ∀ g ∈ X, ∀ m ∈ A, g * m * g⁻¹ ∈ A} with hSdef
  have hS_ne : S.Nonempty := by
    -- `Q₁` is nilpotent: it is isomorphic to `Q₁Subgroup ≤ Q` and `Q` is
    -- nilpotent (§2 Proposition 1(b)).
    haveI : Group.IsNilpotent ↥hyp.Q1 := by
      letI := hyp.isNilpotent_Q
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.equivMapOfInjective hyp.Q1Subgroup hyp.Q.subtype
          hyp.Q.subtype_injective)
    -- The Sylow `r`-subgroup of `Q₁`: normal (nilpotency), characteristic,
    -- nontrivial (`r ∣ |Q₁|`).
    obtain ⟨R⟩ : Nonempty (Sylow r ↥hyp.Q1) := inferInstance
    haveI hRnorm : (R : Subgroup ↥hyp.Q1).Normal := inferInstance
    haveI : (R : Subgroup ↥hyp.Q1).Characteristic :=
      Sylow.characteristic_of_normal R hRnorm
    have hRne : (R : Subgroup ↥hyp.Q1) ≠ ⊥ := R.ne_bot_of_dvd_card hdvd
    -- The conjugation action of `X` on `Q₁` and its restriction to `R`.
    set φQ1 : ↥X →* MulAut ↥hyp.Q1 :=
      hyp.Q1.normalizerMonoidHom.comp
        (Subgroup.inclusion (hX.trans hyp.H_le_normalizer_Q1)) with hφQ1
    have hφQ1_val : ∀ (a : ↥X) (w : ↥hyp.Q1),
        ((φQ1 a w : ↥hyp.Q1) : G) = (a : G) * (w : G) * (a : G)⁻¹ :=
      fun _ _ => rfl
    have hRinv : IsAInvariant φQ1 (R : Subgroup ↥hyp.Q1) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φQ1
    set φR : ↥X →* MulAut ↥(R : Subgroup ↥hyp.Q1) := hRinv.restrict with hφR
    -- A minimal nontrivial `X`-invariant normal subgroup of the `r`-group
    -- `R` is elementary abelian of exponent `r`.
    haveI : Group.IsNilpotent ↥(R : Subgroup ↥hyp.Q1) :=
      IsPGroup.isNilpotent R.isPGroup'
    haveI : IsSolvable ↥(R : Subgroup ↥hyp.Q1) := inferInstance
    haveI : Nontrivial ↥(R : Subgroup ↥hyp.Q1) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hRne
    obtain ⟨N, q, hq, hN_ne, hN_normal, hN_inv, hN_elab⟩ :=
      OddOrder.GroupTheory.exists_aInvariant_normal_isElementaryAbelian
        (φ := φR)
    -- The exponent `q` is `r`: `N` is a nontrivial subgroup of the
    -- `r`-group `R`.
    have hq_eq : q = r := by
      haveI : Fact q.Prime := ⟨hq⟩
      haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne
      obtain ⟨x, hx1⟩ := exists_ne (1 : ↥N)
      have hxq : orderOf x = q := orderOf_eq_prime (hN_elab.pow_eq_one x) hx1
      have hxr : IsPGroup r ↥N := IsPGroup.to_subgroup R.isPGroup' N
      obtain ⟨k, hk⟩ := hxr x
      have hdvd_pow : q ∣ r ^ k := hxq ▸ orderOf_dvd_of_pow_eq_one hk
      exact (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow hdvd_pow)
    subst hq_eq
    -- Push `N` down to an ambient subgroup of `G`.
    refine ⟨(N.map (R : Subgroup ↥hyp.Q1).subtype).map hyp.Q1.subtype,
      Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
    · -- nontrivial
      intro hbot
      apply hN_ne
      have h1 : N.map (R : Subgroup ↥hyp.Q1).subtype = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _
          hyp.Q1.subtype_injective).mp hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _
        (R : Subgroup ↥hyp.Q1).subtype_injective).mp h1
    · -- elementary abelian
      have h1 : IsElementaryAbelian q ↥(N.map (R : Subgroup ↥hyp.Q1).subtype) :=
        OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
          (Subgroup.equivMapOfInjective N _
            (R : Subgroup ↥hyp.Q1).subtype_injective) hN_elab
      exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ hyp.Q1.subtype_injective) h1
    · -- `X`-invariance, unwound through the two `map`s
      rintro g hg m ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      have hmemN : φR ⟨g, hg⟩ z ∈ N := hN_inv.smul_mem ⟨g, hg⟩ hz
      refine ⟨(φR ⟨g, hg⟩ z : ↥(R : Subgroup ↥hyp.Q1)),
        ⟨φR ⟨g, hg⟩ z, hmemN, rfl⟩, ?_⟩
      rfl
  obtain ⟨M, hM_mem, hM_min⟩ := (Set.toFinite S).exists_minimal hS_ne
  obtain ⟨hMQ1, hMne, hMelab, hMinv⟩ := hM_mem
  refine ⟨M, hMQ1, hMne, hMelab, hMinv, ?_⟩
  intro B hBM hBinv hBne
  -- `B` inherits membership in the family, so minimality gives `B = M`.
  have hBelab : IsElementaryAbelian r ↥B :=
    OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hBM) (hMelab.to_subgroup _)
  have hB_mem : B ∈ S := ⟨hBM.trans hMQ1, hBne, hBelab, hBinv⟩
  exact le_antisymm hBM (hM_min hB_mem hBM)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
