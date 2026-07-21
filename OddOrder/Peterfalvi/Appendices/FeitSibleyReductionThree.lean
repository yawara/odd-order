/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyReductionTwo
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

/-!
# Peterfalvi Appendix IV: Feit–Sibley — reduction (3), `p`-power degrees (p. 146)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, p. 146.  The degree computation feeding step (3) of the Theorem
(campaign issue 1054): when `Q₁` is a `p`-group, every `χᵢ ∈ 𝒮(S')` has degree
`χᵢ(1) = d·p^{kᵢ}`.

Writing `χ = Ind_Q^H φ` (Lemma 2(a)), the kernel condition `S' ⊆ Ker χ` makes
`φ` constant on `S'`, so `φ` inflates through `Q/S'`, where the image of the
abelianised direct factor `S/S'` is **central**.  The central scalar rule
`φ(a·x) = ω(a)·φ(x)` (`|ω(a)| = 1`) folds the norm `⟨φ, φ⟩_Q = 1` over the
unique factorisation `Q = S·Q₁` into `⟨Res_{Q₁} φ, Res_{Q₁} φ⟩ = 1`, so
`Res_{Q₁} φ` is irreducible and `φ(1)` is a `p`-power ([Is] Cor. 3.12 for the
`p`-group `Q₁`); hence `χ(1) = d·φ(1) = d·p^k`.

The three norm-fold bricks are `hyp`-independent (stated over an abstract
finite group `K`) for later reuse:

* `exists_unit_mul_eq_of_le_center` — the central scalar rule for `Z ≤ Z(K)`;
* `exists_unit_mul_eq_of_forall_eq_one_of_map_le_center` — its mod-kernel form,
  through the inflation bijection `Irr(K⧸N) ≃ {χ | N ⊆ Ker χ}`;
* `isIrreducibleCharacter_restrict_of_isComplement'` — the norm-folding
  restriction theorem for a complement pair `A·B = K` with `A`-scalars.

The `hyp`-level assembly is `Hypothesis.exists_apply_one_eq_d_mul_pow`.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-! ## The central scalar rule (hyp-independent) -/

/-- **Central elements act on an irreducible character by unimodular scalars**
([Is] Lemma 2.27, product form).  For `χ ∈ Irr(K)` and `Z ≤ Z(K)` there is
`ω : K → ℂ` with `star (ω z) · ω z = 1` and `χ(z·x) = ω(z)·χ(x)` for every
`z ∈ Z`, `x ∈ K`.  By Schur's lemma a witnessing representation sends a central
`z` to a scalar `c` (`exists_central_scalar`); taking traces gives the product
rule, `z^{|K|} = 1` forces `c^{|K|} = 1`, so `‖c‖ = 1` and
`star c · c = c⁻¹·c = 1`.  This is the scalar decomposition behind the
Peterfalvi p. 146 step (3) norm folding. -/
theorem exists_unit_mul_eq_of_le_center {K : Type*} [Group K] [Finite K]
    {χ : ClassFunction K ℂ} (hχ : IsIrreducibleCharacter χ)
    {Z : Subgroup K} (hZ : Z ≤ Subgroup.center K) :
    ∃ ω : K → ℂ, (∀ z ∈ Z, star (ω z) * ω z = 1) ∧
      ∀ z ∈ Z, ∀ x : K, χ (z * x) = ω z * χ x := by
  obtain ⟨d0, hd0, hd0val⟩ := hχ.exists_apply_one_eq_pos_natCast
  have hχ1ne : χ 1 ≠ 0 := by
    rw [show χ 1 = (χ : K → ℂ) 1 from rfl, hd0val]
    exact Nat.cast_ne_zero.mpr hd0.ne'
  have key : ∀ z ∈ Z, star (χ z / χ 1) * (χ z / χ 1) = 1 ∧
      ∀ x : K, χ (z * x) = (χ z / χ 1) * χ x := by
    intro z hz
    obtain ⟨W, _, _, _, ρ, hirr, hchar⟩ := hχ
    haveI : Representation.IsIrreducible ρ := hirr
    haveI := nontrivial_of_isIrreducible ρ
    obtain ⟨c, hc⟩ := exists_central_scalar ρ (hZ hz)
    -- the product rule `χ(z·x) = c·χ(x)` by taking traces
    have hval : ∀ x : K, χ (z * x) = c * χ x := by
      intro x
      rw [show χ (z * x) = (χ : K → ℂ) (z * x) from rfl, congrFun hchar (z * x),
        show χ x = (χ : K → ℂ) x from rfl, congrFun hchar x]
      change LinearMap.trace ℂ W (ρ (z * x)) = c * LinearMap.trace ℂ W (ρ x)
      rw [map_mul, hc]
      have hcomp : (c • LinearMap.id : W →ₗ[ℂ] W) * ρ x = c • ρ x := by
        ext w
        simp [Module.End.mul_apply]
      rw [hcomp, map_smul, smul_eq_mul]
    -- the scalar is `χ(z)/χ(1)`
    have homega : χ z / χ 1 = c := by
      have h1 : χ z = c * χ 1 := by
        have h := hval 1
        rwa [mul_one] at h
      rw [h1, mul_div_assoc, div_self hχ1ne, mul_one]
    -- the scalar is a root of unity, hence unimodular
    have hcpow : c ^ Nat.card K = 1 := by
      have hρpow : ρ z ^ Nat.card K = 1 := by
        rw [← map_pow, pow_card_eq_one', map_one]
      rw [hc, ← Module.End.one_eq_id, smul_pow, one_pow] at hρpow
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      have happ := congrArg (fun f : Module.End ℂ W => f w) hρpow
      simp only [LinearMap.smul_apply, Module.End.one_apply] at happ
      have hkey : c ^ Nat.card K • w = (1 : ℂ) • w := by rw [happ, one_smul]
      exact smul_left_injective ℂ hw hkey
    have hnorm : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hcpow Nat.card_pos.ne'
    have hcne : c ≠ 0 := fun h0 => by rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
    have hstar : star c = c⁻¹ := by rw [RCLike.inv_eq_conj hnorm, starRingEnd_apply]
    refine ⟨?_, fun x => by rw [homega]; exact hval x⟩
    rw [homega, hstar]
    exact inv_mul_cancel₀ hcne
  exact ⟨fun z => χ z / χ 1, fun z hz => (key z hz).1, fun z hz x => (key z hz).2 x⟩

/-- **The central scalar rule modulo a kernel** (mod-`N` form of
`exists_unit_mul_eq_of_le_center`).  If `χ ∈ Irr(K)` is constant on a normal
subgroup `N` and the image of `Z` in `K⧸N` is central, then `χ(z·x) = ω(z)·χ(x)`
with `star (ω z) · ω z = 1` for `z ∈ Z`.  The constancy places `N` in the
character kernel, so `χ` is inflated from `K⧸N`
(`exists_inflate_eq_of_subset_characterKernel`, [Is] (2.22)); the scalar rule
for the central image pulls back along the quotient map. -/
theorem exists_unit_mul_eq_of_forall_eq_one_of_map_le_center {K : Type*} [Group K]
    [Finite K] {χ : ClassFunction K ℂ} (hχ : IsIrreducibleCharacter χ)
    (N : Subgroup K) [N.Normal] (hker : ∀ n ∈ N, χ n = χ 1) {Z : Subgroup K}
    (hZ : Z.map (QuotientGroup.mk' N) ≤ Subgroup.center (K ⧸ N)) :
    ∃ ω : K → ℂ, (∀ z ∈ Z, star (ω z) * ω z = 1) ∧
      ∀ z ∈ Z, ∀ x : K, χ (z * x) = ω z * χ x := by
  have hkerset : (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ := fun n hn => by
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
    exact hker n hn
  obtain ⟨χbar, hbar⟩ := exists_inflate_eq_of_subset_characterKernel N ⟨χ, hχ⟩ hkerset
  have hχeq : χ = ClassFunction.compHom (QuotientGroup.mk' N)
      (χbar : ClassFunction (K ⧸ N) ℂ) := by
    have h := congrArg (fun ξ : IrreducibleCharacter K => (ξ : ClassFunction K ℂ)) hbar
    simpa using h.symm
  obtain ⟨ωbar, hωunit, hωmul⟩ := exists_unit_mul_eq_of_le_center χbar.isIrreducible hZ
  refine ⟨fun x => ωbar (QuotientGroup.mk' N x), fun z hz => ?_, fun z hz x => ?_⟩
  · change star (ωbar (QuotientGroup.mk' N z)) * ωbar (QuotientGroup.mk' N z) = 1
    exact hωunit _ (Subgroup.mem_map_of_mem _ hz)
  · change χ (z * x) = ωbar (QuotientGroup.mk' N z) * χ x
    rw [hχeq, ClassFunction.compHom_apply, ClassFunction.compHom_apply, map_mul]
    exact hωmul _ (Subgroup.mem_map_of_mem _ hz) _

/-! ## The norm folding over a complement pair (hyp-independent) -/

/-- **Norm folding: an irreducible character scaled on a complement restricts
irreducibly** (Peterfalvi p. 146, step (3) core).  Let `A·B = K` be a complement
pair and `χ ∈ Irr(K)` with unimodular `A`-scalars: `χ(a·x) = ω(a)·χ(x)`,
`star (ω a) · ω a = 1` for `a ∈ A`.  Reindexing `⟨χ, χ⟩_K = 1` over the unique
factorisation `K ≃ A × B` folds each `|χ(a·b)|² = |χ(b)|²`, giving
`Σ_K |χ|² = |A| · Σ_B |χ|²`, i.e. `⟨Res_B χ, Res_B χ⟩ = 1` since
`|K| = |A|·|B|`; as `Res_B χ` is a virtual character (`restrict_mem_ZIrr`) of
positive degree, it is irreducible
(`isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos`). -/
theorem isIrreducibleCharacter_restrict_of_isComplement' {K : Type*} [Group K]
    [Finite K] {A B : Subgroup K} (hAB : Subgroup.IsComplement' A B)
    {χ : ClassFunction K ℂ} (hχ : IsIrreducibleCharacter χ) {ω : K → ℂ}
    (hω : ∀ a ∈ A, star (ω a) * ω a = 1)
    (hmul : ∀ a ∈ A, ∀ x : K, χ (a * x) = ω a * χ x) :
    IsIrreducibleCharacter (ClassFunction.restrict B χ) := by
  classical
  letI : Fintype K := Fintype.ofFinite _
  letI : Fintype ↥B := Fintype.ofFinite _
  letI : Fintype ↥(A : Set K) := Fintype.ofFinite _
  letI : Fintype ↥(B : Set K) := Fintype.ofFinite _
  letI : Invertible ((Nat.card K : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible ((Nat.card ↥B : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Nonempty ↥(A : Set K) := ⟨⟨1, A.one_mem⟩⟩
  set e := hAB.equiv with he_def
  have hcardA : Nat.card ↥(A : Set K) = Nat.card ↥A :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => SetLike.mem_coe)
  -- fold `Σ_K |χ|²` over the unique factorisation `K ≃ A × B`
  have hterm : ∀ (a : ↥(A : Set K)) (b : ↥(B : Set K)),
      χ (e.symm (a, b)) * star (χ (e.symm (a, b))) = χ (b : K) * star (χ (b : K)) := by
    intro a b
    have hab : e.symm (a, b) = (a : K) * (b : K) := rfl
    have haA : (a : K) ∈ A := a.2
    rw [hab, hmul _ haA, star_mul',
      show ω (a : K) * χ (b : K) * (star (ω (a : K)) * star (χ (b : K)))
          = star (ω (a : K)) * ω (a : K) * (χ (b : K) * star (χ (b : K))) from by ring,
      hω _ haA, one_mul]
  have hfold : ClassFunction.innerSum χ χ
      = (Nat.card ↥A : ℂ) * ClassFunction.innerSum
          (ClassFunction.restrict B χ) (ClassFunction.restrict B χ) :=
    calc ClassFunction.innerSum χ χ
        = ∑ x : ↥(A : Set K) × ↥(B : Set K), χ (e.symm x) * star (χ (e.symm x)) :=
          (Equiv.sum_comp e.symm fun g : K => χ g * star (χ g)).symm
      _ = ∑ a : ↥(A : Set K), ∑ b : ↥(B : Set K),
            χ (e.symm (a, b)) * star (χ (e.symm (a, b))) := Fintype.sum_prod_type _
      _ = ∑ _a : ↥(A : Set K), ∑ b : ↥(B : Set K), χ (b : K) * star (χ (b : K)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
      _ = (Nat.card ↥(A : Set K) : ℂ)
            * ∑ b : ↥(B : Set K), χ (b : K) * star (χ (b : K)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
      _ = (Nat.card ↥A : ℂ) * ClassFunction.innerSum
            (ClassFunction.restrict B χ) (ClassFunction.restrict B χ) := by
          rw [hcardA]
          congr 1
  -- `⟨Res_B χ, Res_B χ⟩ = 1` from `⟨χ, χ⟩ = 1` and `|K| = |A|·|B|`
  have hA0 : ((Nat.card ↥A : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hB0 : ((Nat.card ↥B : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hone : ClassFunction.inner (ClassFunction.restrict B χ)
      (ClassFunction.restrict B χ) = 1 := by
    have hK : ((Nat.card K : ℕ) : ℂ) = ClassFunction.innerSum χ χ := by
      rw [← ClassFunction.card_mul_inner χ χ, hχ.inner_self_eq_one, mul_one]
    have hB : ClassFunction.innerSum (ClassFunction.restrict B χ)
        (ClassFunction.restrict B χ)
        = ((Nat.card ↥B : ℕ) : ℂ) * ClassFunction.inner (ClassFunction.restrict B χ)
            (ClassFunction.restrict B χ) := (ClassFunction.card_mul_inner _ _).symm
    have hmain : ((Nat.card ↥A : ℕ) : ℂ) * ((Nat.card ↥B : ℕ) : ℂ)
        = ((Nat.card ↥A : ℕ) : ℂ) * (((Nat.card ↥B : ℕ) : ℂ)
            * ClassFunction.inner (ClassFunction.restrict B χ)
                (ClassFunction.restrict B χ)) := by
      rw [← hB, ← hfold, ← hK, ← Nat.cast_mul, hAB.card_mul]
    have h2 := mul_left_cancel₀ hA0 hmain
    nth_rewrite 1 [← mul_one ((Nat.card ↥B : ℕ) : ℂ)] at h2
    exact (mul_left_cancel₀ hB0 h2).symm
  -- positive degree, virtual character ⟹ irreducible
  have hmem : ClassFunction.restrict B χ ∈ ZIrr ↥B :=
    ClassFunction.restrict_mem_ZIrr B hχ.mem_ZIrr
  have hpos : ∃ d0 : ℕ, 0 < d0
      ∧ (ClassFunction.restrict B χ : ↥B → ℂ) 1 = (d0 : ℂ) := by
    obtain ⟨d0, hd0, hval⟩ := hχ.exists_apply_one_eq_pos_natCast
    exact ⟨d0, hd0, by simpa using hval⟩
  exact isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos hmem hone hpos

/-! ## The `hyp`-level assembly (Peterfalvi p. 146, step (3)) -/

namespace Hypothesis

variable (hyp : Hypothesis G)

/-- **`⁅S, Q⁆ ⊆ S'`**: `S` commutes with the direct factor `Q₁` and has
commutators in `S' = [S,S]` within `S`, so every commutator of `S` against
`Q = S·Q₁` lands in `S'`.  This is `commutator_mem_sup_Sder_of_central` at
`Z = Q₃ = ⊥`; it makes the image of `S` central in `Q⧸S'`. -/
theorem commutator_mem_Sder_of_mem_S {x q : G} (hx : x ∈ hyp.S) (hq : q ∈ hyp.Q) :
    ⁅x, q⁆ ∈ hyp.Sder := by
  have h := hyp.commutator_mem_sup_Sder_of_central (Q₃ := (⊥ : Subgroup G))
    (Z := (⊥ : Subgroup G)) bot_le
    (fun z hz y _ => by
      rw [Subgroup.mem_bot] at hz
      subst hz
      rw [Subgroup.mem_bot, commutatorElement_def]
      group)
    (x := x) (q := q) (by rw [sup_bot_eq]; exact hx) hq
  rwa [sup_bot_eq] at h

/-- **`S' ⊴ Q`, doubly relativised**: the `Normal` instance for
`(S'.subgroupOf H).subgroupOf (Q.subgroupOf H)` consumed by the inflation
through `Q⧸S'`, from `H`-invariance of `S'` (`Sder_conj_mem_of_mem_H`). -/
theorem Sder_subgroupOf_Q_normal [Finite G] :
    ((hyp.Sder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal :=
  hyp.subgroupOf_Q_normal_of_conj_mem fun _q hq _x hx =>
    hyp.Sder_conj_mem_of_mem_H (hyp.Q_le_H hq) hx

/-- **`Q = S·Q₁` as a complement pair, doubly relativised**: inside
`↥(Q.subgroupOf H)`, the images of `S` and `Q₁` are complements
(`S ∩ Q₁ = 1` and `S·Q₁ = Q`). -/
theorem isComplement'_S_Q1_subgroupOf :
    Subgroup.IsComplement'
      ((hyp.S.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))
      ((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro x hxS hxQ1
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hxS hxQ1
    have hmem : (((x : ↥(hyp.Q.subgroupOf hyp.H)) : ↥hyp.H) : G) ∈ hyp.S ⊓ hyp.Q1 :=
      ⟨hxS, hxQ1⟩
    rw [hyp.S_inf_Q1_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  · ext g
    simp only [Set.mem_univ, iff_true]
    have hgQ : ((g : ↥hyp.H) : G) ∈ hyp.Q := Subgroup.mem_subgroupOf.mp g.2
    rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hgQ
    obtain ⟨s, hs, y, hy, hsy⟩ := Set.mem_mul.mp hgQ
    rw [SetLike.mem_coe] at hs hy
    have hab : (⟨⟨s, hyp.S_le_H hs⟩, Subgroup.mem_subgroupOf.mpr (hyp.S_le_Q hs)⟩ :
          ↥(hyp.Q.subgroupOf hyp.H))
        * ⟨⟨y, hyp.Q1_le_H hy⟩, Subgroup.mem_subgroupOf.mpr (hyp.Q1_le_Q hy)⟩ = g :=
      Subtype.ext (Subtype.ext hsy)
    rw [← hab]
    exact Set.mul_mem_mul
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hs))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hy))

/-- The double relativisation of the `p`-group `Q₁` is a `p`-group (transport
along `↥((Q₁-in-H)-in-(Q-in-H)) ≃* ↥(Q₁-in-H) ≃* ↥Q₁`). -/
theorem isPGroup_Q1_subgroupOf_subgroupOf {p : ℕ} (hQ1p : IsPGroup p ↥hyp.Q1) :
    IsPGroup p ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) := by
  have hle : hyp.Q1.subgroupOf hyp.H ≤ hyp.Q.subgroupOf hyp.H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hyp.Q1_le_Q (Subgroup.mem_subgroupOf.mp hx))
  exact (hQ1p.of_equiv (Subgroup.subgroupOfEquivOfLe hyp.Q1_le_H).symm).of_equiv
    (Subgroup.subgroupOfEquivOfLe hle).symm

set_option linter.unusedFintypeInType false in
/-- **Members of `𝒮(S')` have degree `d·p^k` when `Q₁` is a `p`-group**
(Peterfalvi p. 146, step (3): "`χᵢ(1)` is of the form `d·p^{kᵢ}`").  Writing
`χ = Ind_Q^H φ` (Lemma 2(a)), `χ(1) = d·φ(1)` and `S' ⊆ Ker χ` makes `φ`
constant on `S'` (`forall_eq_one_of_leKer`); the image of `S` in `Q⧸S'` is
central (`commutator_mem_Sder_of_mem_S`), so the central scalar rule
(`exists_unit_mul_eq_of_forall_eq_one_of_map_le_center`) folds `⟨φ, φ⟩ = 1`
over `Q = S·Q₁` (`isIrreducibleCharacter_restrict_of_isComplement'`): the
restriction `Res_{Q₁} φ` is irreducible, so `φ(1)` is a `p`-power
([Is] Cor. 3.12, `exists_charValue_one_eq_prime_pow_of_isPGroup`). -/
theorem exists_apply_one_eq_d_mul_pow [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    {p : ℕ} (hp : p.Prime) (hQ1p : IsPGroup p ↥hyp.Q1)
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.SsetOf hyp.Sder) :
    ∃ k : ℕ, χ (1 : ↥hyp.H) = (hyp.d : ℂ) * ((p ^ k : ℕ) : ℂ) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  letI : Fintype ↥(hyp.Q.subgroupOf hyp.H) := Fintype.ofFinite _
  obtain ⟨hχS, hkerS'⟩ := hχ
  have hχS' := hχS
  rw [Sset_eq_induced_of_Q hyp] at hχS'
  obtain ⟨φ, ⟨hφirr, -⟩, rfl⟩ := hχS'
  have hindirr : IsIrreducibleCharacter
      (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ) := hχS.1
  -- `φ` is constant on `S'`, doubly relativised
  have hconst := hyp.forall_eq_one_of_leKer hyp.Sder hyp.Sder_le_Q hφirr hindirr hkerS'
  haveI : ((hyp.Sder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal :=
    hyp.Sder_subgroupOf_Q_normal
  -- the image of `S` in `Q⧸S'` is central
  have hcentral := hyp.map_mk_le_center_of_commutator_mem (R := hyp.Sder)
    (D₀ := hyp.S) fun x hx q hq => hyp.commutator_mem_Sder_of_mem_S hx hq
  -- the unimodular `S`-scalar rule for `φ`
  obtain ⟨ω, hωunit, hωmul⟩ := exists_unit_mul_eq_of_forall_eq_one_of_map_le_center
    hφirr ((hyp.Sder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))
    (fun n hn => hconst ⟨n, hn⟩) hcentral
  -- `Res_{Q₁} φ` is irreducible by norm folding over `Q = S·Q₁`
  have hres := isIrreducibleCharacter_restrict_of_isComplement'
    hyp.isComplement'_S_Q1_subgroupOf hφirr hωunit hωmul
  -- the degree of `Res_{Q₁} φ` is a `p`-power
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hres.exists_charValue_one_eq_prime_pow_of_isPGroup
    (hyp.isPGroup_Q1_subgroupOf_subgroupOf hQ1p)
  have hdeg := hk
  rw [ClassFunction.restrict_apply, OneMemClass.coe_one] at hdeg
  -- `χ(1) = [H:Q]·φ(1) = d·p^k`
  refine ⟨k, ?_⟩
  rw [ClassFunction.induce_apply_one, hyp.index_Q_subgroupOf_eq_d, hdeg]
  push_cast
  ring

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
