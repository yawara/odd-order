/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Commutator.Basic
import OddOrder.BG.Ch1_Preliminary.S03b_Lemma33
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
import OddOrder.BG.Ch1_Preliminary.S03d_Thm34
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# BG §3: Theorem 3.5 (Frobenius action with one-dimensional fixed space)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §3, mmd `references/bg/local-analysis.mmd` L903-951.

**BG Theorem 3.5**: Let `G = KR` be a Frobenius group with solvable Frobenius kernel `K` and cyclic
Frobenius complement `R` of prime order.  Suppose `G` acts on a vector space `V` over a field `F`
with `char F ∤ |G|`.  If `C_V(R)` is **one-dimensional**, then `K' ⊆ C_K(V)`.

Sibling of Theorem 3.4 (`S03d_Thm34.lean`, complete); upstream of Theorem 3.6 (mmd L955) → §10.6.

## 証明の構造 (minimal counterexample / induction on `|G|`, mmd L907-951)

1. WLOG `F` algebraically closed (base change, BG (2.9)); `dim C_V(R) = 1` is preserved.
2. If `G` is not faithful on `V` (`C = C_G(V) ≠ 1`): either `K ⊆ C` (done) or, by Lemma 3.2,
   `C ⊂ K` and `G/C` is Frobenius; induction gives `(K/C)' ⊆ C/C`, i.e. `K' ⊆ C`.
3. Assume `G` faithful (`C_G(V) = 1`).
4. **(3.4)** every proper `R`-invariant subgroup `N < K` is abelian (`NR` satisfies the hypotheses,
   `|NR| < |G|`, induction gives `N' ⊆ C_N(V) ⊆ C_G(V) = 1`).
5. `K'` is abelian (proper characteristic `R`-invariant subgroup, by (3.4)).
6. **(3.5)** for `R`-invariant `N ⊆ K` and an `NR`-decomposition `U ⊕ W`, either `U ⊆ C_V(N)` or
   `W ⊆ C_V(N)` (Lemma 3.3 twice, using `dim C_V(R) = 1`).
7. Pick an irreducible `G`-submodule `U` with `K` nontrivial; Maschke gives a complement `W`; (3.5)
   gives `W ⊆ C_V(K')`.
8. It suffices to show `C_U(K') ≠ 0` (then `U ⊆ C_V(K')`, so `V = U ⊕ W ⊆ C_V(K')`, faithful ⟹
   `K' = 1`).
9. `C_U(K') ≠ 0` via Clifford's Theorem (Wedderburn components of `U` over `K`, `K'R`, `K'`) +
   Proposition 2.2: the cyclic `R` permutes components, the projection argument forces a
   one-dimensional `K`-module, and `K'` abelian over an algebraically closed field forces
   `dim U = 1`.

**状態 (scaffold, 2026-06-09)**: statement 確定のみ.  step 9 の Clifford/Wedderburn 分解
(一般体) が hard core (Thm 3.4 における Thm 2.5 に相当, `Clifford.lean` は ℂ 限定).  詳細プラン =
`notes/bg/s03_thm35.md`.
-/

namespace OddOrder.BG.Ch1.S03e

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open scoped commutatorElement

/-- **Sub-Frobenius constructor.**  If `G = K R` is a Frobenius group and `N ≤ K` is a nontrivial
`R`-invariant subgroup (`R ≤ N_G(N)`), then `N R = N ⊔ R` is again a Frobenius group with kernel `N`
and complement `R` (viewed inside the subtype `↥(N ⊔ R)`).  The conjugation condition transfers from
`K`'s since `N ⊆ K`; complementation and normality transfer as in the `HR` setup of Theorem 3.4.

Used in Theorem 3.5 to feed the induction hypothesis to the proper `R`-invariant subgroups (step
(3.4)) and to apply Lemma 3.3 to `NR`-submodules (step (3.5)). -/
theorem isFrobeniusGroup_subgroupOf_sup
    {G : Type*} [Group G] {K R N : Subgroup G}
    (hFrob : IsFrobeniusGroup G K R) (hNK : N ≤ K) (hNinv : R ≤ Subgroup.normalizer N)
    (hNne : N ≠ ⊥) :
    IsFrobeniusGroup ↥(N ⊔ R) (N.subgroupOf (N ⊔ R)) (R.subgroupOf (N ⊔ R)) where
  isNormal := Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hNinv)
  isComplement := by
    haveI : (N.subgroupOf (N ⊔ R)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hNinv)
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
      rw [Subgroup.mem_inf] at hx
      simp only [Subgroup.mem_subgroupOf] at hx
      have hmem : (x : G) ∈ N ⊓ R := ⟨hx.1, hx.2⟩
      have hdisjNR : Disjoint N R := hFrob.isComplement.disjoint.mono_left hNK
      rw [hdisjNR.eq_bot, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]; exact Subtype.ext (by simpa using hmem)
    · have hsup : (N.subgroupOf (N ⊔ R)) ⊔ (R.subgroupOf (N ⊔ R)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (N.subgroupOf (N ⊔ R)) (R.subgroupOf (N ⊔ R))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  ne_bot_kernel := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd =>
      hNne ((inf_of_le_left (le_sup_left : N ≤ N ⊔ R)).symm.trans (disjoint_iff.mp hd))
  ne_bot_complement := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd =>
      hFrob.ne_bot_complement ((inf_of_le_left (le_sup_right : R ≤ N ⊔ R)).symm.trans
        (disjoint_iff.mp hd))
  conj_frobenius := by
    intro a haR ha n hnN hn hconj
    rw [Subgroup.mem_subgroupOf] at haR hnN
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hnG : (n : G) ≠ 1 := fun h => hn (Subtype.ext h)
    have hconjG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := congrArg (Subtype.val) hconj
      simpa using this
    exact hFrob.conj_frobenius (a : G) haR haG (n : G) (hNK hnN) hnG hconjG

/-- **Frobenius normal dichotomy.**  In a Frobenius group `G = KR`, a normal subgroup `N` that does
not contain the kernel `K` is contained in `K`.  (With the trivial converse, every normal subgroup
of a Frobenius group is comparable to the kernel.)

Used in the non-faithful branch of Theorem 3.5 to show `C = C_G(V) ⊆ K` when `K ⊄ C`, so that the
Frobenius quotient `G/C` (with kernel `K/C`) is available for the induction (Lemma 3.2).

Proof: pick `c ∈ N \ K`.  By `centralizer_kernel_le`, `c` centralizes no nontrivial element of `K`
(else `c ∈ C_G(k) ≤ K`), so conjugation by `c` is a fixed-point-free automorphism of `K`.  Hence the
commutator map `k ↦ k · (c k c⁻¹)⁻¹` is surjective onto `K`
(`MonoidHom.FixedPointFree.commutatorMap_surjective`); each value `k c k⁻¹ c⁻¹` lies in `N`
(`c ∈ N ◁ G`), so `K ≤ N` — contradicting `¬ K ≤ N`. -/
theorem normal_le_kernel_of_not_kernel_le {G : Type*} [Group G] [Finite G]
    {K R N : Subgroup G} (hFrob : IsFrobeniusGroup G K R) [hNnorm : N.Normal]
    (hKN : ¬ K ≤ N) : N ≤ K := by
  haveI hKnorm : K.Normal := hFrob.isNormal
  intro c hcN
  by_contra hcK
  -- Conjugation by `c` is fixed-point-free on `K` (via `centralizer_kernel_le`).
  have hFPF : MonoidHom.FixedPointFree (OddOrder.RepresentationTheory.conjNormalMulAut K c) := by
    intro g hg
    by_contra hg1
    have hgcoe : c * (g : G) * c⁻¹ = (g : G) := by
      have := congrArg (Subtype.val) hg
      rwa [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe] at this
    have hcent : c ∈ Subgroup.centralizer ({(g : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgcoe)
    exact hcK (hFrob.centralizer_kernel_le (g : G) g.2
      (fun h => hg1 (Subtype.ext (by simpa using h))) hcent)
  -- The commutator map is surjective onto `K`; every value lies in `N`, so `K ≤ N`.
  refine absurd (fun x hxK => ?_) hKN
  obtain ⟨k', hk'⟩ := hFPF.commutatorMap_surjective ⟨x, hxK⟩
  have h : ((MonoidHom.commutatorMap (OddOrder.RepresentationTheory.conjNormalMulAut K c) k'
      : ↥K) : G) = x := by rw [hk']
  rw [MonoidHom.commutatorMap_apply, Subgroup.coe_div,
    OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe] at h
  -- `h : (k' : G) / (c * (k' : G) * c⁻¹) = x`
  have hval : x = (k' : G) * c * (k' : G)⁻¹ * c⁻¹ := by rw [← h, div_eq_mul_inv]; group
  rw [hval]
  exact N.mul_mem (hNnorm.conj_mem c hcN (k' : G)) (N.inv_mem hcN)

/-! ## Step (3.5): the dichotomy `U ⊆ C_V(N)` or `W ⊆ C_V(N)` (mmd L931-939) -/

section Dichotomy35

variable {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **Lemma 3.3 plumbing for (3.5).**  If `N ⊔ R` preserves a submodule `A`, `N ≤ K` is a
nontrivial `R`-invariant subgroup of the kernel of a Frobenius group `G = KR`, and `R` has no
nonzero fixed vector inside `A` (i.e. `C_A(R) = 0`), then `N` acts trivially on `A`.

This is the contrapositive of Wielandt's Lemma 3.3
(`OddOrder.BG.Ch1.S03b.kernel_acts_trivially_of_centralizer_eq_bot`) applied to the sub-Frobenius
group `NR = N ⊔ R` (constructed by `isFrobeniusGroup_subgroupOf_sup`) acting on the submodule
`A`. -/
theorem kernel_trivial_on_submodule_of_centralizer_eq_bot
    {K R N : Subgroup G} (hFrob : IsFrobeniusGroup G K R)
    (hNK : N ≤ K) (hNinv : R ≤ Subgroup.normalizer N) (hNne : N ≠ ⊥)
    (ρ : Representation F G V) (hchar : (Nat.card ↥N : F) ≠ 0)
    {A : Submodule F V} (hAinv : ∀ g ∈ N ⊔ R, ∀ a ∈ A, ρ g a ∈ A)
    (hCA : ∀ a ∈ A, (∀ r : ↥R, ρ (r : G) a = a) → a = 0) :
    ∀ n : ↥N, ∀ a ∈ A, ρ (n : G) a = a := by
  -- Restrict `ρ` to the subgroup `N ⊔ R` and to the invariant submodule `A`.
  set ρNR := ρ.comp (N ⊔ R).subtype with hρNR
  let σ : Subrepresentation ρNR :=
    { toSubmodule := A
      apply_mem_toSubmodule := fun g a ha => hAinv (g : G) g.2 a ha }
  -- The kernel `N.subgroupOf (N ⊔ R)` has the same order as `N`.
  have hcardN : Nat.card ↥(N.subgroupOf (N ⊔ R)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv
  have hchar' : (Nat.card ↥(N.subgroupOf (N ⊔ R)) : F) ≠ 0 := by rw [hcardN]; exact hchar
  -- `C_A(R') = 0` transported to the sub-Frobenius complement.
  have hCR' : ∀ v : ↥σ.toSubmodule,
      (∀ r : ↥(R.subgroupOf (N ⊔ R)), σ.toRepresentation (r : ↥(N ⊔ R)) v = v) → v = 0 := by
    intro v hv
    refine Submodule.coe_eq_zero.mp (hCA (v : V) v.2 (fun r => ?_))
    have hrmem : (r : G) ∈ N ⊔ R := Subgroup.mem_sup_right r.2
    have hr' : (⟨(r : G), hrmem⟩ : ↥(N ⊔ R)) ∈ R.subgroupOf (N ⊔ R) := by
      rw [Subgroup.mem_subgroupOf]; exact r.2
    have key := hv ⟨⟨(r : G), hrmem⟩, hr'⟩
    have := congrArg (Subtype.val) key
    simpa [σ, Subrepresentation.toRepresentation, ρNR] using this
  -- Lemma 3.3 (contrapositive) on the sub-Frobenius group.
  have hKtriv := OddOrder.BG.Ch1.S03b.kernel_acts_trivially_of_centralizer_eq_bot
    (isFrobeniusGroup_subgroupOf_sup hFrob hNK hNinv hNne) σ.toRepresentation hchar' hCR'
  intro n a ha
  have hnmem : (n : G) ∈ N ⊔ R := Subgroup.mem_sup_left n.2
  have hk : (⟨(n : G), hnmem⟩ : ↥(N ⊔ R)) ∈ N.subgroupOf (N ⊔ R) := by
    rw [Subgroup.mem_subgroupOf]; exact n.2
  set kk : ↥(N.subgroupOf (N ⊔ R)) := ⟨⟨(n : G), hnmem⟩, hk⟩ with hkk
  have h2 : σ.toRepresentation (kk : ↥(N ⊔ R)) ⟨a, ha⟩ = ⟨a, ha⟩ := by
    rw [hKtriv kk]; rfl
  have h3 := congrArg Subtype.val h2
  simpa [σ, Subrepresentation.toRepresentation, ρNR, kk] using h3

/-- **BG (3.5)** (mmd L931-939).  Let `G = KR` be a Frobenius group (`R` the complement), `ρ` a
representation on `V` with `dim C_V(R) = 1`.  If `N ≤ K` is a nontrivial `R`-invariant subgroup and
`A ⊕ B` is an `NR`-decomposition (`A`, `B` disjoint `NR`-invariant submodules), then `N` acts
trivially on `A` or on `B`.

Proof: `C_A(R)` and `C_B(R)` are disjoint subspaces of the one-dimensional `C_V(R)`, so one of them
is zero; the contrapositive of Lemma 3.3 (`kernel_trivial_on_submodule_of_centralizer_eq_bot`) then
makes `N` act trivially on the corresponding summand. -/
theorem dichotomy_3_5
    {K R N : Subgroup G} (hFrob : IsFrobeniusGroup G K R)
    (hNK : N ≤ K) (hNinv : R ≤ Subgroup.normalizer N) (hNne : N ≠ ⊥)
    (ρ : Representation F G V) (hchar : (Nat.card G : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1)
    {A B : Submodule F V}
    (hAinv : ∀ g ∈ N ⊔ R, ∀ a ∈ A, ρ g a ∈ A)
    (hBinv : ∀ g ∈ N ⊔ R, ∀ b ∈ B, ρ g b ∈ B)
    (hAB : Disjoint A B) :
    (∀ n : ↥N, ∀ a ∈ A, ρ (n : G) a = a) ∨ (∀ n : ↥N, ∀ b ∈ B, ρ (n : G) b = b) := by
  -- `|N| ≠ 0` in `F` (it divides `|G|`).
  have hcharN : (Nat.card ↥N : F) ≠ 0 := by
    obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card N
    intro h0; exact hchar (by rw [hm, Nat.cast_mul, h0, zero_mul])
  -- Membership in `C_X(R)` as fixed vectors; abbreviate the predicate.
  set inv := Representation.invariants (ρ.comp R.subtype) with hinv
  have hmem_inv : ∀ w : V, w ∈ inv ↔ ∀ r : ↥R, ρ (r : G) w = w := by
    intro w; rw [hinv, Representation.mem_invariants]; rfl
  -- Either `C_A(R) = 0` or `C_B(R) = 0`.
  by_cases hA0 : ∀ a ∈ A, (∀ r : ↥R, ρ (r : G) a = a) → a = 0
  · exact Or.inl (kernel_trivial_on_submodule_of_centralizer_eq_bot hFrob hNK hNinv hNne ρ
      hcharN hAinv hA0)
  · refine Or.inr (kernel_trivial_on_submodule_of_centralizer_eq_bot hFrob hNK hNinv hNne ρ
      hcharN hBinv (fun b hb hbfix => ?_))
    -- From `¬ (C_A(R) = 0)` get a nonzero `a ∈ A` fixed by `R`; show `C_B(R) = 0`.
    push_neg at hA0
    obtain ⟨a, haA, hafix, ha0⟩ := hA0
    -- `a ∈ inv`, `a ≠ 0`, and `inv` is one-dimensional, so `inv = span {a}`.
    have hainv : a ∈ inv := (hmem_inv a).mpr hafix
    have hspan : Submodule.span F {a} = inv := by
      refine Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hainv)) ?_
      rw [hCV1, finrank_span_singleton ha0]
    -- `b ∈ inv = span {a}`, so `b = c • a ∈ A`; with `b ∈ B` and `A ⊓ B = ⊥`, `b = 0`.
    have hbinv : b ∈ inv := (hmem_inv b).mpr hbfix
    rw [← hspan, Submodule.mem_span_singleton] at hbinv
    obtain ⟨c, hc⟩ := hbinv
    have hbA : b ∈ A := hc ▸ A.smul_mem c haA
    exact (Submodule.disjoint_def.mp hAB) b hbA hb

end Dichotomy35

/-- **BG Theorem 3.5, group-order strong-induction core** (algebraically closed `F`).

`Nat.card G = n` での強帰納法。結論 `∀ g ∈ ⁅K, K⁆, ρ g = 1` (= `K' ⊆ C_K(V)`)。
non-faithful 枝 (この induction backbone) は `C = ker ρ` で `G/C` に帰着 (Lemma 3.2)；
faithful 枝 ((3.4)/(3.5)/Clifford core) が hard core。詳細 = `notes/bg/s03_thm35.md`。 -/
private theorem thm35_aux : ∀ (n : ℕ)
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (K R : Subgroup G),
    IsFrobeniusGroup G K R → IsSolvable ↥K →
    (∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p) →
    (Nat.card G : F) ≠ 0 →
    Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1 →
    Nat.card G = n →
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro F _ _ G _ _ V _ _ _ ρ K R hFrob hKsolv hRp hchar hCV1 hn
    haveI hKnorm : K.Normal := hFrob.isNormal
    -- `⁅K, K⁆ ≤ K`.
    have hKK_le : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_right K K
    by_cases hfaithful : Function.Injective ρ
    · -- **faithful branch** (`C_G(V) = 1`): steps (3.4)/(3.5)/(Clifford core).  Hard core.
      sorry
    · -- **non-faithful branch**: `C = ker ρ ≠ ⊥`; reduce to `G/C` (Lemma 3.2).
      set C := MonoidHom.ker ρ with hCdef
      haveI hCnorm : C.Normal := MonoidHom.normal_ker _
      by_cases hKC : K ≤ C
      · -- `K ≤ C`: `⁅K, K⁆ ≤ K ≤ C = ker ρ`, so `ρ` kills `⁅K, K⁆`.
        intro g hg
        exact MonoidHom.mem_ker.mp (le_trans hKK_le hKC hg)
      · -- `¬ K ≤ C`: `C ⊆ K` (Frobenius normal ⊆ kernel) and `G/C` is Frobenius; apply IH.
        have hCK : C ≤ K := normal_le_kernel_of_not_kernel_le hFrob hKC
        -- `ρ` factors through `G/C` as `ρ̄ = ofQuotient ρ C`.
        haveI hIsTriv : Representation.IsTrivial (ρ.comp C.subtype) := by
          refine ⟨fun c => ?_⟩
          show ρ (c : G) = LinearMap.id
          rw [MonoidHom.mem_ker.mp c.2]; rfl
        set ρbar := Representation.ofQuotient ρ C with hρbar
        haveI : (K.map (QuotientGroup.mk' C)).Normal :=
          hKnorm.map (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
        haveI hKbarsolv : IsSolvable ↥(K.map (QuotientGroup.mk' C)) :=
          solvable_of_surjective (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' C) K)
        -- `|G| = |G/C| · |C|`, so `|G/C| < |G|` (since `C ≠ ⊥`).
        have hCne : C ≠ ⊥ := fun h => hfaithful ((MonoidHom.ker_eq_bot_iff ρ).mp h)
        have hGcard : Nat.card G = Nat.card (G ⧸ C) * Nat.card ↥C :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup C
        have hGCdvd : Nat.card (G ⧸ C) ∣ Nat.card G := ⟨_, hGcard⟩
        have hCgt : 1 < Nat.card ↥C :=
          Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot C).mpr hCne)
        have hlt : Nat.card (G ⧸ C) < n := by
          rw [← hn, hGcard]; exact (Nat.lt_mul_iff_one_lt_right Nat.card_pos).mpr hCgt
        have hcharQ : (Nat.card (G ⧸ C) : F) ≠ 0 := by
          obtain ⟨m, hm⟩ := hGCdvd; intro h0; apply hchar; rw [hm, Nat.cast_mul, h0, zero_mul]
        -- `G/C` is Frobenius with kernel `K̄`, complement `R̄`.
        have hFrobQ : IsFrobeniusGroup (G ⧸ C) (K.map (QuotientGroup.mk' C))
            (R.map (QuotientGroup.mk' C)) :=
          OddOrder.BG.Ch1.S03c.frobenius_quotient_of_normal_lt_kernel hFrob hCK hKC hKsolv
        -- `C ⊓ R = ⊥` (since `C ≤ K` and `K ⊓ R = ⊥`), so `|R̄| = |R|` is prime.
        have hCR : C ⊓ R = ⊥ := by
          rw [eq_bot_iff]
          exact le_trans (inf_le_inf_right R hCK) (le_of_eq hFrob.isComplement.disjoint.eq_bot)
        obtain ⟨p, hp, hpcard⟩ := hRp
        have hRp' : (Nat.card ↥R).Prime := hpcard ▸ hp
        have hRQcard : Nat.card ↥(R.map (QuotientGroup.mk' C)) = Nat.card ↥R := by
          rcases (Nat.dvd_prime hRp').mp (Subgroup.card_map_dvd R (QuotientGroup.mk' C)) with h1 | h
          · exfalso
            have hbot : R.map (QuotientGroup.mk' C) = ⊥ := Subgroup.card_eq_one.mp h1
            rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
            have hRbot : R = ⊥ := by
              rw [eq_bot_iff]; intro x hx
              have : x ∈ C ⊓ R := ⟨hbot hx, hx⟩
              rwa [hCR, Subgroup.mem_bot] at this
            exact hp.ne_one (hpcard ▸ Subgroup.card_eq_one.mpr hRbot)
          · exact h
        have hRpQ : ∃ q : ℕ, q.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' C)) = q :=
          ⟨p, hp, hRQcard.trans hpcard⟩
        -- `C_V(R̄) = C_V(R)` (same fixed subspace), so still one-dimensional.
        have heqinv : Representation.invariants (ρbar.comp (R.map (QuotientGroup.mk' C)).subtype)
            = Representation.invariants (ρ.comp R.subtype) := by
          ext v
          rw [Representation.mem_invariants, Representation.mem_invariants]
          constructor
          · intro hv r
            have hkey : ρbar ((r : G) : G ⧸ C) v = v :=
              hv ⟨QuotientGroup.mk' C (r : G), Subgroup.mem_map_of_mem _ r.2⟩
            rwa [hρbar, Representation.ofQuotient_coe_apply] at hkey
          · intro hv rbar
            obtain ⟨r', hr', hr'eq⟩ := rbar.2
            show ρbar (rbar : G ⧸ C) v = v
            rw [← hr'eq, hρbar, QuotientGroup.mk'_apply, Representation.ofQuotient_coe_apply]
            exact hv ⟨r', hr'⟩
        have hCV1Q : Module.finrank F
            (Representation.invariants (ρbar.comp (R.map (QuotientGroup.mk' C)).subtype)) = 1 := by
          rw [heqinv]; exact hCV1
        -- IH on `G/C`.
        have hIHconcl := IH (Nat.card (G ⧸ C)) hlt ρbar (K.map (QuotientGroup.mk' C))
          (R.map (QuotientGroup.mk' C)) hFrobQ hKbarsolv hRpQ hcharQ hCV1Q rfl
        -- pull `⁅K, K⁆` back: `mk g ∈ ⁅K̄, K̄⁆`, so `ρ̄ (mk g) = 1`, i.e. `ρ g = 1`.
        intro g hg
        have hgbar : (QuotientGroup.mk' C) g ∈
            ⁅K.map (QuotientGroup.mk' C), K.map (QuotientGroup.mk' C)⁆ := by
          rw [← Subgroup.map_commutator]; exact Subgroup.mem_map_of_mem _ hg
        have h1 := hIHconcl _ hgbar
        apply LinearMap.ext
        intro v
        have h2 : ρbar ((g : G) : G ⧸ C) v = (1 : Module.End F V) v :=
          congrFun (congrArg DFunLike.coe h1) v
        rwa [hρbar, Representation.ofQuotient_coe_apply] at h2

/-- **BG Theorem 3.5** (algebraically closed core).  `G = KR` a Frobenius group with solvable kernel
`K` and prime-order complement `R`, acting on `V/F` with `char F ∤ |G|` and `F` algebraically
closed.  If `dim C_V(R) = 1` then `K' ⊆ C_K(V)` (i.e. `ρ` kills every element of `⁅K, K⁆`).

Strong induction on `|G|` (`thm35_aux`); the hard core (step 9 of the faithful branch) is Clifford
theory over an algebraically closed field.  See `notes/bg/s03_thm35.md`. -/
theorem thm35_algClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (K R : Subgroup G)
    (hFrob : IsFrobeniusGroup G K R) (hKsolv : IsSolvable ↥K)
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p)
    (hchar : (Nat.card G : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1) :
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 :=
  thm35_aux (Nat.card G) ρ K R hFrob hKsolv hRp hchar hCV1 rfl

end OddOrder.BG.Ch1.S03e
