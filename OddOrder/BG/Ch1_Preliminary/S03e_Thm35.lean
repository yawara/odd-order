/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Eigenspace.Pi
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

/-! ## Step 9 foundations: the Clifford hard core (mmd L945-951) -/

section Step9

variable {F : Type*} [Field F] {G : Type*} [Group G]
variable {W : Type*} [AddCommGroup W] [Module F W]

/-- On a one-dimensional module every linear endomorphism is a scalar (a homothety), so the
endomorphisms `ρ g` pairwise commute and the representation kills commutators: `⁅K, K⁆ ⊆ C_W(K)`
for any subgroup `K`.

This is the punchline of step 9 of Theorem 3.5: once the reductions force `dim_F U = 1`, the
abelian group `K' = ⁅K, K⁆` acts trivially on `U`, so `C_U(K') = U ≠ 0`. -/
theorem trivial_on_commutator_of_finrank_eq_one
    (ρ : Representation F G W) (hdim : Module.finrank F W = 1) (K : Subgroup G) :
    ∀ g ∈ (⁅K, K⁆ : Subgroup G), ρ g = 1 := by
  -- Every `ρ a` is a scalar `algebraMap F (End) c`.
  have hsc : ∀ a : G, ∃ c : F, ρ a = algebraMap F (Module.End F W) c := fun a => by
    obtain ⟨c, hc⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ a)).exists
    exact ⟨c, by rw [hc]; exact (Algebra.algebraMap_eq_smul_one c).symm⟩
  -- Scalars commute, so all `ρ x` commute.
  have hcomm : ∀ x y : G, ρ x * ρ y = ρ y * ρ x := fun x y => by
    obtain ⟨cx, hx⟩ := hsc x; obtain ⟨cy, hy⟩ := hsc y
    rw [hx, hy, ← map_mul, ← map_mul, mul_comm cx cy]
  -- `⁅K, K⁆ ≤ ker ρ`, checking single commutators.
  suffices hle : (⁅K, K⁆ : Subgroup G) ≤ MonoidHom.ker ρ from fun g hg => hle hg
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
  calc ρ a * ρ b * ρ a⁻¹ * ρ b⁻¹
      = ρ a * (ρ b * ρ a⁻¹) * ρ b⁻¹ := by rw [mul_assoc (ρ a)]
    _ = ρ a * (ρ a⁻¹ * ρ b) * ρ b⁻¹ := by rw [hcomm b a⁻¹]
    _ = (ρ a * ρ a⁻¹) * (ρ b * ρ b⁻¹) := by simp only [mul_assoc]
    _ = ρ (a * a⁻¹) * ρ (b * b⁻¹) := by rw [← map_mul, ← map_mul]
    _ = 1 := by rw [mul_inv_cancel, mul_inv_cancel, map_one, mul_one]

/-- **The fixed space of a normal subgroup is `G`-invariant**, so for an irreducible `ρ` it is `⊥`
or `⊤`.  Hence if a normal subgroup `N ◁ G` has a nonzero fixed vector (`C_W(N) ≠ 0`), it acts
trivially on the whole irreducible module: `∀ g ∈ N, ρ g = 1`.

This is the step-8/9 reduction `C_U(K') ≠ 0 ⟹ K' ⊆ C_K(V)` (BG mmd L943): once `C_U(K')` is
shown nonzero, irreducibility upgrades it to all of `U`. -/
theorem trivial_of_invariants_comp_ne_bot
    (ρ : Representation F G W) [ρ.IsIrreducible] (N : Subgroup G) [hNnorm : N.Normal]
    (hne : Representation.invariants (ρ.comp N.subtype) ≠ ⊥) :
    ∀ g ∈ N, ρ g = 1 := by
  -- The fixed space `C_W(N)` carries a subrepresentation (it is `G`-invariant by normality of `N`).
  let Wρ : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp N.subtype)
      apply_mem_toSubmodule := fun g v hv => by
        rw [Representation.mem_invariants] at hv ⊢
        intro n
        have hn' : g⁻¹ * (n : G) * g ∈ N := by
          have := hNnorm.conj_mem (n : G) n.2 g⁻¹; simpa using this
        have hfix := hv ⟨g⁻¹ * (n : G) * g, hn'⟩
        show ρ (n : G) (ρ g v) = ρ g v
        have hfix' : ρ (g⁻¹ * (n : G) * g) v = v := hfix
        rw [← Module.End.mul_apply, ← map_mul,
          show (n : G) * g = g * (g⁻¹ * (n : G) * g) by group, map_mul, Module.End.mul_apply,
          hfix'] }
  -- Irreducibility: `Wρ` is `⊥` or `⊤`; nonzero rules out `⊥`, so `N` fixes everything.
  rcases IsSimpleOrder.eq_bot_or_eq_top Wρ with hbot | htop
  · exact absurd (congrArg Subrepresentation.toSubmodule hbot) hne
  · have htop' : Representation.invariants (ρ.comp N.subtype) = ⊤ :=
      congrArg Subrepresentation.toSubmodule htop
    intro g hg
    ext v
    have hv : v ∈ Representation.invariants (ρ.comp N.subtype) := htop' ▸ Submodule.mem_top
    rw [Representation.mem_invariants] at hv
    exact hv ⟨g, hg⟩

open OddOrder.RepresentationTheory in
/-- **Inner conjugates are trivial** (orbit-machinery entry point for step 9).  For `g ∈ H`, the
conjugate `M^g = M.map (conjSemilinearEnd ρ g)` of an `F[H]`-submodule `M` equals `M` itself: `ρ g`
preserves the `H`-submodule `M` (it is the action of the group element `single ⟨g,·⟩ 1`).

This supplies the `hconj` hypothesis of `restriction_isIrreducible` (BG Prop 2.2(a)) on the subgroup
elements; combined with `map_map_conjSemilinearEnd`, an isomorphism `M ≅ M^x` for a generator `x`
propagates to all of `G = ⟨H, x⟩`. -/
theorem map_conjSemilinearEnd_eq_self_of_mem (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] {g : G} (hg : g ∈ H)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) :
    M.map (conjSemilinearEnd (H := H) ρ g) = M := by
  -- For `h ∈ H`, `conjSemilinearEnd ρ h v = single ⟨h,·⟩ 1 • v`, which stays in the
  -- `F[H]`-submodule `M`.
  have hact : ∀ {h : G} (hh : h ∈ H) (v : (resRep ρ H).asModule),
      (conjSemilinearEnd (H := H) ρ h v)
        = MonoidAlgebra.single (⟨h, hh⟩ : ↥H) (1 : F) • v := by
    intro h hh v
    rw [conjSemilinearEnd_apply, Representation.single_smul, one_smul, resRep_apply]; rfl
  refine le_antisymm ?_ ?_
  · rintro w ⟨v, hv, rfl⟩
    rw [hact hg v]; exact M.smul_mem _ hv
  · intro w hw
    rw [mem_map_conjSemilinearEnd]
    refine ⟨conjSemilinearEnd (H := H) ρ g⁻¹ w, ?_, ?_⟩
    · rw [hact (H.inv_mem hg) w]; exact M.smul_mem _ hw
    · rw [conjSemilinearEnd_apply]
      show ρ g (ρ g⁻¹ w) = w
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

open OddOrder.RepresentationTheory in
/-- **`hconj` propagation (character route).**  Let `ρ` be irreducible on `W` over an algebraically
closed `F` with `char F ∤ |H|`, `H ◁ G`, `G = ⟨H, x⟩`, and `M` a simple `F[H]`-submodule of the
restriction.  If the conjugate `M^x` has the same character as `M`, then `M ≅ M^g` for **every**
`g ∈ G` — exactly the `hconj` input of `restriction_isIrreducible` (BG Prop 2.2(a)).

The set of `g` with `char(M^g) = char(M)` is the conjugation-stabilizer of `char(M)` (a subgroup of
`G`, via the `conjNormalMulAut` composition law).  It contains `H` (inner conjugates are trivial,
`map_conjSemilinearEnd_eq_self_of_mem`) and `x` (hypothesis), hence all of `G = ⟨H, x⟩`; then
`submodule_iso_of_character_eq` (Schur orthogonality) turns equal characters into isomorphisms. -/
theorem nonempty_linearEquiv_map_conjSemilinearEnd_forall
    [IsAlgClosed F] [FiniteDimensional F W] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] [Finite ↥H] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hx : ((Subrepresentation.ofSubmodule'
              (M.map (conjSemilinearEnd (H := H) ρ x))).toRepresentation).character
        = ((Subrepresentation.ofSubmodule' M).toRepresentation).character) :
    ∀ g : G, Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ g))) := by
  haveI : Invertible (Nat.card ↥H : F) := invertibleOfNonzero hHchar
  set χ := ((Subrepresentation.ofSubmodule' M).toRepresentation).character with hχ
  -- Conjugation composition law for `conjNormalMulAut`.
  have hcomp : ∀ (a b : G) (h : ↥H),
      conjNormalMulAut H (a * b) h = conjNormalMulAut H a (conjNormalMulAut H b h) := by
    intro a b h; apply Subtype.ext
    rw [conjNormalMulAut_apply_coe, conjNormalMulAut_apply_coe, conjNormalMulAut_apply_coe]; group
  have hone : ∀ h : ↥H, conjNormalMulAut H 1 h = h := by
    intro h; apply Subtype.ext; rw [conjNormalMulAut_apply_coe]; group
  -- The conjugation-stabilizer subgroup of `χ`.
  let S : Subgroup G :=
    { carrier := {g | ∀ h : ↥H, χ (conjNormalMulAut H g⁻¹ h) = χ h}
      one_mem' := by intro h; rw [inv_one, hone]
      mul_mem' := fun {a b} ha hb h => by
        rw [mul_inv_rev, hcomp, hb (conjNormalMulAut H a⁻¹ h)]; exact ha h
      inv_mem' := fun {a} ha h => by
        have hkey := ha (conjNormalMulAut H a h)
        rw [← hcomp, inv_mul_cancel, hone] at hkey
        rw [inv_inv]; exact hkey.symm }
  -- `H ≤ S`: inner conjugates are trivial (`M^h = M`), so `char(M^h) = χ`.
  have hHS : (H : Set G) ⊆ (S : Set G) := by
    intro h₀ hh₀ h
    have hMM : M.map (conjSemilinearEnd (H := H) ρ h₀) = M :=
      map_conjSemilinearEnd_eq_self_of_mem ρ hh₀ M
    have hc := character_subRep_conj ρ M h₀ h
    rw [hMM] at hc
    exact hc.symm
  -- `x ∈ S`: hypothesis.
  have hxS : x ∈ S := by
    intro h
    have hc := character_subRep_conj ρ M x h
    rw [hx] at hc
    exact hc.symm
  -- `S = ⊤`, so every `g` stabilises `χ`, giving `char(M^g) = χ` and hence `M ≅ M^g`.
  have htop : (⊤ : Subgroup G) ≤ S := by
    rw [← hgen]; exact Subgroup.closure_le S |>.mpr (Set.union_subset hHS (by simpa using hxS))
  intro g
  have hgS : ∀ h : ↥H, χ (conjNormalMulAut H g⁻¹ h) = χ h := htop (Subgroup.mem_top g)
  have hcharg : ((Subrepresentation.ofSubmodule'
      (M.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character = χ := by
    funext h; rw [character_subRep_conj]; exact hgS h
  exact submodule_iso_of_character_eq ρ M g hcharg

open OddOrder.RepresentationTheory in
/-- **ISO case: the restriction `Res^G_H ρ` is irreducible** (BG Prop 2.2(a) applied).  If `M` is a
simple `F[H]`-submodule of an irreducible `ρ` (alg-closed, `char F ∤ |H|`, `H ◁ G`, `G = ⟨H, x⟩`)
and the conjugate `M^x` has the same character as `M`, then `ρ` restricted to `H` is irreducible.

Composes the character-route `hconj` propagation
(`nonempty_linearEquiv_map_conjSemilinearEnd_forall`) with `restriction_isIrreducible`.  Used in
step 9 with `H = K` (over `G`) and `H = K'` (over `K'R`). -/
theorem resRep_isIrreducible_of_char_eq_generator
    [IsAlgClosed F] [FiniteDimensional F W] [Nontrivial W] (ρ : Representation F G W)
    [ρ.IsIrreducible] {H : Subgroup G} [H.Normal] [Finite ↥H] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) (hM : M ≠ ⊥)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hx : ((Subrepresentation.ofSubmodule'
              (M.map (conjSemilinearEnd (H := H) ρ x))).toRepresentation).character
        = ((Subrepresentation.ofSubmodule' M).toRepresentation).character) :
    (resRep ρ H).IsIrreducible := by
  haveI : NeZero (Nat.card ↥H : F) := ⟨hHchar⟩
  exact restriction_isIrreducible ρ x hgen M hM
    (nonempty_linearEquiv_map_conjSemilinearEnd_forall ρ hHchar M x hgen hx)

open OddOrder.RepresentationTheory in
/-- **Isomorphic constituents have equal characters** (reverse of `submodule_iso_of_character_eq`).
An `F[H]`-linear isomorphism `A ≃ₗ B` of constituents gives equal characters: compose with
`subRepAsModuleEquiv` to get an `F[H]`-linear iso of the subrepresentation `asModule`s, turn it into
a `Representation.Equiv` (`equivOfAsModuleEquiv`), and apply `Representation.char_iso`.

Used in the NONISO branch of step 9 to rule out `M ≅ M^{x^j}` from the character distinctness
`char(M^x) ≠ char(M)`. -/
theorem character_eq_of_nonempty_linearEquiv [FiniteDimensional F W] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal]
    {A B : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule}
    (e : ↥A ≃ₗ[MonoidAlgebra F ↥H] ↥B) :
    ((Subrepresentation.ofSubmodule' A).toRepresentation).character
      = ((Subrepresentation.ofSubmodule' B).toRepresentation).character :=
  Representation.char_iso (equivOfAsModuleEquiv
    ((subRepAsModuleEquiv (resRep ρ H) A).symm.trans
      (e.trans (subRepAsModuleEquiv (resRep ρ H) B))))

open OddOrder.RepresentationTheory in
/-- **`hconj` propagation, iso-phrased** (perf-safe variant of
`nonempty_linearEquiv_map_conjSemilinearEnd_forall`).  If the conjugate `M^x` for a generator `x`
(with `G = ⟨H, x⟩`) is `F[H]`-linearly isomorphic to `M`, then `M ≅ M^g` for **every** `g ∈ G`.

Converts the iso `M ≅ M^x` to the equal-character hypothesis once
(`character_eq_of_nonempty_linearEquiv`) and feeds it to the character-route propagation.  Phrasing
the hypothesis as a *module isomorphism* (rather than a character identity) keeps the downstream
NONISO arguments off the pathological nested-character `isDefEq` path. -/
theorem nonempty_linearEquiv_forall_of_iso_generator
    [IsAlgClosed F] [FiniteDimensional F W] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] [Finite ↥H] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hx : Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x)))) :
    ∀ g : G, Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ g))) := by
  obtain ⟨e⟩ := hx
  exact nonempty_linearEquiv_map_conjSemilinearEnd_forall ρ hHchar M x hgen
    (character_eq_of_nonempty_linearEquiv ρ e).symm

open OddOrder.RepresentationTheory in
/-- **Distinctness of conjugates** (NONISO branch of step 9, iso-phrased).  Let `R = ⟨x⟩` be of
prime order with `G = ⟨H, x⟩`.  If `M` is *not* isomorphic to its conjugate `M^x`, then `M` is not
isomorphic to `M^{x^j}` for any `j` with `x^j ≠ 1` (i.e. for `1 ≤ j < |R|`).

Proof: a non-identity power `x^j` again generates the prime-order `R`
(`zpowers_eq_of_prime_card`), so `G = ⟨H, x^j⟩`; an iso `M ≅ M^{x^j}` would propagate
(`nonempty_linearEquiv_forall_of_iso_generator`) to `M ≅ M^x`, contradicting the hypothesis. -/
theorem not_nonempty_linearEquiv_pow_of_not_generator
    [IsAlgClosed F] [FiniteDimensional F W] [Finite G] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    {R : Subgroup G} {x : G} (hxR : Subgroup.zpowers x = R) (hRp : (Nat.card ↥R).Prime)
    (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hniso : ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x))))
    {j : ℕ} (hxj : x ^ j ≠ 1) :
    ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ (x ^ j)))) := by
  intro hiso
  have hxR' : x ∈ R := hxR ▸ Subgroup.mem_zpowers x
  have hxjR : x ^ j ∈ R := R.pow_mem hxR' j
  have hgenj : Subgroup.zpowers (x ^ j) = R :=
    OddOrder.BG.Ch1.S03d.zpowers_eq_of_prime_card hRp hxjR hxj
  have hgenj' : Subgroup.closure ((H : Set G) ∪ {x ^ j}) = ⊤ := by
    have hle : Subgroup.zpowers (x ^ j) ≤ Subgroup.closure ((H : Set G) ∪ {x ^ j}) :=
      (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Or.inr rfl))
    have hxmem : x ∈ Subgroup.closure ((H : Set G) ∪ {x ^ j}) :=
      hle (by rw [hgenj, ← hxR]; exact Subgroup.mem_zpowers x)
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro s (hsH | hsx)
    · exact Subgroup.subset_closure (Or.inl hsH)
    · rw [Set.mem_singleton_iff] at hsx; rw [hsx]; exact hxmem
  exact hniso
    (nonempty_linearEquiv_forall_of_iso_generator ρ hHchar M (x ^ j) hgenj' hiso x)

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **(P) disjointness** (NONISO branch of step 9).  Let `R = ⟨x⟩` be of prime order `p` with
`G = ⟨H, x⟩`.  If `M` is a simple `F[H]`-constituent not isomorphic to its conjugate `M^x`, then `M`
meets the sum of the *other* conjugates `M^{x^i}` (`1 ≤ i < p`) trivially.

Proof: `M` is an atom, so `M ⊓ (⨆ …)` is `⊥` or `M`; if it were `M` then `M ≤ ⨆ M^{x^i}`, and a
simple submodule of a sum of simple modules is isomorphic to one of them
(`Submodule.linearEquiv_of_le_sSup`), i.e. `M ≅ M^{x^i}` for some `1 ≤ i < p` — contradicting the
distinctness `not_nonempty_linearEquiv_pow_of_not_generator`. -/
theorem inf_iSup_map_conjSemilinearEnd_eq_bot
    [IsAlgClosed F] [FiniteDimensional F W] [Finite G] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    {R : Subgroup G} {x : G} (hxR : Subgroup.zpowers x = R) (hRp : (Nat.card ↥R).Prime)
    (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hniso : ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x)))) :
    M ⊓ (⨆ i ∈ Set.Ioo 0 (Nat.card ↥R),
        M.map (conjSemilinearEnd (H := H) ρ (x ^ i))) = ⊥ := by
  set p := Nat.card ↥R with hp
  have hordx : orderOf x = p := by rw [hp, ← hxR, Nat.card_zpowers]
  set Sup := ⨆ i ∈ Set.Ioo 0 p, M.map (conjSemilinearEnd (H := H) ρ (x ^ i)) with hSup
  have hatom : IsAtom M := IsSimpleModule.isAtom
  rcases eq_or_lt_of_le (inf_le_left : M ⊓ Sup ≤ M) with heq | hlt
  · exfalso
    have hMle : M ≤ Sup := by rw [← heq]; exact inf_le_right
    set s : Set (Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) :=
      (fun i => M.map (conjSemilinearEnd (H := H) ρ (x ^ i))) '' Set.Ioo 0 p with hs
    have hssup : sSup s = Sup := by rw [hs, sSup_image]
    haveI hsimple : ∀ m : s, IsSimpleModule (MonoidAlgebra F ↥H)
        ↥(m : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) := by
      rintro ⟨_, i, _, rfl⟩
      exact isSimpleModule_map_conjSemilinearEnd ρ (x ^ i) M
    obtain ⟨S, hSs, ⟨e⟩⟩ := M.linearEquiv_of_le_sSup s (by rw [hssup]; exact hMle)
    obtain ⟨i, hiIoo, rfl⟩ := hSs
    have hxi1 : x ^ i ≠ 1 := by
      intro h
      have hdvd := orderOf_dvd_of_pow_eq_one h
      rw [hordx] at hdvd
      exact Nat.not_dvd_of_pos_of_lt hiIoo.1 hiIoo.2 hdvd
    exact not_nonempty_linearEquiv_pow_of_not_generator ρ hHchar M hxR hRp hgen hniso hxi1 ⟨e⟩
  · exact hatom.2 (M ⊓ Sup) hlt

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **(P) projection / dimension bound** (NONISO branch of step 9).  With the hypotheses of
`inf_iSup_map_conjSemilinearEnd_eq_bot` and `dim C_W(R) = 1`, a simple `F[H]`-constituent `M` not
isomorphic to `M^x` is **one-dimensional** over `F`.

Proof (the BG projection argument): the `F`-linear map `T : M → W`, `m ↦ ∑_{i<p} ρ(xⁱ) m`, lands in
`C_W(R)` (it is `x`-invariant since `xᵖ = 1`: `a · Φ = Φ` for `a = ρ x`, `Φ = ∑ aⁱ`, by the
geometric-sum identity `Φ·(a-1) = aᵖ-1 = 0`) and is injective (if `T m = 0` then
`m = -∑_{1≤i<p} ρ(xⁱ) m ∈ M ⊓ ⨆ M^{xⁱ} = ⊥`, the disjointness above).  Hence
`dim_F M ≤ dim_F C_W(R) = 1`, and `M ≠ 0`, so `dim_F M = 1`. -/
theorem finrank_eq_one_of_not_iso_generator
    [IsAlgClosed F] [FiniteDimensional F W] [Finite G] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    {R : Subgroup G} {x : G} (hxR : Subgroup.zpowers x = R) (hRp : (Nat.card ↥R).Prime)
    (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1)
    (hniso : ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x)))) :
    Module.finrank F ↥M = 1 := by
  set p := Nat.card ↥R with hp
  have hordx : orderOf x = p := by rw [hp, ← hxR, Nat.card_zpowers]
  have hxp : x ^ p = 1 := by rw [← hordx]; exact pow_orderOf_eq_one x
  set a : Module.End F W := ρ x with ha
  have hap : a ^ p = 1 := by rw [ha, ← map_pow, hxp, map_one]
  set Φ : Module.End F W := ∑ i ∈ Finset.range p, a ^ i with hΦ
  -- `a · Φ = Φ` (geometric sum, `aᵖ = 1`).
  have hΦfix : a * Φ = Φ := by
    have hcomm : a * Φ = Φ * a :=
      Commute.sum_right (Finset.range p) (fun i => a ^ i) a
        (fun i _ => (Commute.refl a).pow_right i)
    have hgs := geom_sum_mul a p
    rw [hap, sub_self, ← hΦ, mul_sub, mul_one, sub_eq_zero] at hgs
    rw [hcomm]; exact hgs
  -- disjointness from (P-disjoint).
  have hdisj := inf_iSup_map_conjSemilinearEnd_eq_bot ρ hHchar M hxR hRp hgen hniso
  set Sup := ⨆ i ∈ Set.Ioo 0 p, M.map (conjSemilinearEnd (H := H) ρ (x ^ i)) with hSup
  -- the projection `T`.
  let T : ↥M →ₗ[F] W := Φ ∘ₗ (M.subtype.restrictScalars F)
  have hTm : ∀ m : ↥M, T m = Φ (m : (resRep ρ H).asModule) := fun _ => rfl
  have hTsum : ∀ m : ↥M,
      T m = ∑ i ∈ Finset.range p, ρ (x ^ i) (m : (resRep ρ H).asModule) := by
    intro m
    rw [hTm, hΦ, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [ha, ← map_pow])
  -- `T` injective.
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker, hTsum] at hm
    have hp0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hRp.pos
    rw [← Finset.add_sum_erase _ _ hp0, pow_zero, map_one, Module.End.one_apply] at hm
    -- hm : (m : W) + ∑_{i ∈ erase 0} ρ(xⁱ) m = 0.
    have hmem : (m : (resRep ρ H).asModule) ∈ Sup := by
      have heq : (m : (resRep ρ H).asModule)
          = -(∑ i ∈ (Finset.range p).erase 0, ρ (x ^ i) (m : (resRep ρ H).asModule)) :=
        eq_neg_of_add_eq_zero_left hm
      rw [heq]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ (fun i hi => ?_))
      rw [Finset.mem_erase, Finset.mem_range] at hi
      have hiIoo : i ∈ Set.Ioo 0 p := ⟨Nat.pos_of_ne_zero hi.1, hi.2⟩
      have hsub : M.map (conjSemilinearEnd (H := H) ρ (x ^ i)) ≤ Sup :=
        le_iSup₂ (f := fun i (_ : i ∈ Set.Ioo 0 p) =>
          M.map (conjSemilinearEnd (H := H) ρ (x ^ i))) i hiIoo
      refine hsub ?_
      rw [mem_map_conjSemilinearEnd]
      exact ⟨(m : (resRep ρ H).asModule), m.2, rfl⟩
    have hbot : (m : (resRep ρ H).asModule) ∈ M ⊓ Sup := ⟨m.2, hmem⟩
    rw [hdisj, Submodule.mem_bot] at hbot
    rw [Submodule.mem_bot]
    exact Submodule.coe_eq_zero.mp hbot
  -- range `T` lands in `C_W(R)`.
  have hTinv : LinearMap.range T ≤ Representation.invariants (ρ.comp R.subtype) := by
    rw [SetLike.le_def]
    rintro v ⟨m, rfl⟩
    rw [Representation.mem_invariants]
    have hxfix : ρ x (T m) = T m := by
      have h := LinearMap.congr_fun hΦfix (m : (resRep ρ H).asModule)
      rwa [Module.End.mul_apply, ← hTm, ha] at h
    let Stab : Subgroup G :=
      { carrier := {g | ρ g (T m) = T m}
        one_mem' := by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply]
        mul_mem' := fun {b c} hb hc => by
          simp only [Set.mem_setOf_eq, map_mul] at *
          rw [Module.End.mul_apply, hc, hb]
        inv_mem' := fun {b} hb => by
          simp only [Set.mem_setOf_eq] at *
          have h1 : ρ b⁻¹ (ρ b (T m)) = T m := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
          rwa [hb] at h1 }
    have hRStab : R ≤ Stab := by rw [← hxR, Subgroup.zpowers_le]; exact hxfix
    intro r
    exact hRStab r.2
  -- dimension count.
  haveI : Nontrivial ↥M := IsSimpleModule.nontrivial (MonoidAlgebra F ↥H) ↥M
  haveI : Module.Finite F ↥M :=
    Module.Finite.of_injective (M.subtype.restrictScalars F) Subtype.val_injective
  have hle : Module.finrank F ↥M ≤ 1 := by
    rw [← hCV1]
    calc Module.finrank F ↥M
        = Module.finrank F ↥(LinearMap.range T) := (LinearEquiv.ofInjective T hTinj).finrank_eq
      _ ≤ Module.finrank F ↥(Representation.invariants (ρ.comp R.subtype)) :=
          Submodule.finrank_mono hTinv
  have hpos : 0 < Module.finrank F ↥M := Module.finrank_pos
  omega

end Step9

/-! ## Step 9, (O): weight spaces of an abelian normal subgroup and the orbit count (mmd L949-951)

For the `K'`-analysis of step 9.  When `K'` is abelian and `F` is algebraically closed, the simple
`F[K']`-constituents of `U` are one-dimensional, indexed by *characters* `χ : K' → F`.  Their weight
spaces `U_χ = {v | ∀ k', ρ k' v = χ k' • v}` are independent (distinct characters), `G` permutes
them by conjugation (`ρ g (U_χ) = U_{g·χ}`), and irreducibility over a subgroup forces that subgroup
to act transitively on the (finite) set of weights.  Running this for `K` (number of weights divides
`|K|`) and for `R = ⟨x⟩` (number divides `p`), with the two weights `χ` and `x·χ` distinct in the
NONISO case, forces the weight count to be `p`, hence `p ∣ |K|` — contradicting `gcd(p, |K|) = 1`. -/

section WeightSpace

variable {F : Type*} [Field F] {G : Type*} [Group G]
variable {W : Type*} [AddCommGroup W] [Module F W]

/-- The `χ`-**weight space** of `K'` acting via `ρ`: the simultaneous `χ k'`-eigenspace of every
`ρ k'` (`k' ∈ K'`).  For abelian `K'` over an algebraically closed field these are the
one-dimensional `F[K']`-isotypic pieces of `U`. -/
def weightSpace (ρ : Representation F G W) (K' : Subgroup G) (χ : ↥K' → F) : Submodule F W :=
  ⨅ k' : ↥K', Module.End.eigenspace (ρ (k' : G)) (χ k')

theorem mem_weightSpace {ρ : Representation F G W} {K' : Subgroup G} {χ : ↥K' → F} {v : W} :
    v ∈ weightSpace ρ K' χ ↔ ∀ k' : ↥K', ρ (k' : G) v = χ k' • v := by
  simp only [weightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- The conjugation action of `G` on characters of a normal subgroup `K'`:
`(g · χ) k' = χ (g⁻¹ k' g)`. -/
noncomputable def conjChar (K' : Subgroup G) [K'.Normal] (g : G) (χ : ↥K' → F) : ↥K' → F :=
  fun k' => χ (OddOrder.RepresentationTheory.conjNormalMulAut K' g⁻¹ k')

theorem conjChar_one (K' : Subgroup G) [K'.Normal] (χ : ↥K' → F) : conjChar K' 1 χ = χ := by
  funext k'
  simp only [conjChar, inv_one]
  congr 1
  apply Subtype.ext
  rw [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe]; group

theorem conjChar_mul (K' : Subgroup G) [K'.Normal] (g₁ g₂ : G) (χ : ↥K' → F) :
    conjChar K' (g₁ * g₂) χ = conjChar K' g₁ (conjChar K' g₂ χ) := by
  funext k'
  simp only [conjChar]
  congr 1
  apply Subtype.ext
  rw [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe,
    OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe,
    OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe]
  group

/-- **`G` permutes the weight spaces**: `ρ g` carries the `χ`-weight space onto the
`(g · χ)`-weight space.  This is the key conjugation identity — purely an eigenspace computation
(`ρ g` is `F`-linear), with no semilinearity, because `ρ k' (ρ g v) = ρ g (ρ (g⁻¹ k' g) v)`. -/
theorem map_weightSpace (ρ : Representation F G W) {K' : Subgroup G} [K'.Normal] (g : G)
    (χ : ↥K' → F) :
    (weightSpace ρ K' χ).map (ρ g) = weightSpace ρ K' (conjChar K' g χ) := by
  have hkey : ∀ (h : G) (v : W) (k' : ↥K'),
      ρ (k' : G) (ρ h v)
        = ρ h (ρ ((OddOrder.RepresentationTheory.conjNormalMulAut K' h⁻¹ k' : ↥K') : G) v) := by
    intro h v k'
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    rw [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe]; group
  ext w
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_weightSpace] at hv ⊢
    intro k'
    rw [hkey g v k', hv (OddOrder.RepresentationTheory.conjNormalMulAut K' g⁻¹ k'), map_smul]
    rfl
  · intro hw
    rw [mem_weightSpace] at hw
    refine ⟨ρ g⁻¹ w, ?_, ?_⟩
    · rw [mem_weightSpace]
      intro k'
      rw [hkey g⁻¹ w k']
      have hcc : conjChar K' g χ
          (OddOrder.RepresentationTheory.conjNormalMulAut K' (g⁻¹)⁻¹ k') = χ k' := by
        simp only [conjChar]
        rw [OddOrder.RepresentationTheory.conjNormalMulAut_conjNormalMulAut_inv]
      rw [hw (OddOrder.RepresentationTheory.conjNormalMulAut K' (g⁻¹)⁻¹ k'), hcc, map_smul]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- **Weight spaces are independent** (distinct characters ⟹ independent eigenspaces).  For a
commuting family `{ρ k' : k' ∈ K'}` the simultaneous maximal generalised eigenspaces are independent
(`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`); the weight spaces are contained in
them, so are independent too. -/
theorem iSupIndep_weightSpace (ρ : Representation F G W) {K' : Subgroup G}
    (hcomm : ∀ a b : ↥K', (a : G) * (b : G) = (b : G) * (a : G)) :
    iSupIndep (weightSpace ρ K') := by
  have hC : ∀ a b : ↥K', Commute (ρ (a : G)) (ρ (b : G)) := fun a b => by
    show ρ (a : G) * ρ (b : G) = ρ (b : G) * ρ (a : G)
    rw [← map_mul, ← map_mul, hcomm a b]
  refine (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun k' : ↥K' => ρ (k' : G))
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hC j i) φ)).mono ?_
  intro χ
  exact iInf_mono (fun _ => Module.End.eigenspace_le_maxGenEigenspace)

end WeightSpace


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


