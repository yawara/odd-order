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

/-! ## The family `𝒳(R, Z)` (p. 147, step (3) setup)

Step (3) works with `𝒳 = 𝒮 − 𝒮(Z)` for a nontrivial `Z ⊴ H` with `Z ≤ Z(Q₁)`,
and its intersections `𝒳 ∩ 𝒮(R)` for the `S`-side induction (Part B).  We
parametrise both: `XsetOf R Z = {χ ∈ 𝒮(R) | Z ⊄ Ker χ}`.  For `Z ≤ Q₁`
membership in `𝒮` is automatic for an irreducible with `Z ⊄ Ker χ`
(`Z ≤ Q₁ ⊆ Ker χ` otherwise), so the degree-square counting reduces to the
two-kernel counting `sum_degreeSq_ker_subset_not_subset`. -/

/-- **`𝒳(R, Z) = {χ ∈ 𝒮(R) | Z ⊄ Ker χ}`** (p. 147: `𝒳 = 𝒮 − 𝒮(Z)`,
relativised by the kernel condition `R` for the Part B induction;
`𝒳 = XsetOf ⊥ Z`, `𝒳₁ = XsetOf Sder Z`). -/
def XsetOf (R Z : Subgroup G) : Set (ClassFunction ↥hyp.H ℂ) :=
  {χ | χ ∈ hyp.SsetOf R ∧ ¬ hyp.LeKer χ Z}

theorem XsetOf_subset_SsetOf (R Z : Subgroup G) : hyp.XsetOf R Z ⊆ hyp.SsetOf R :=
  fun _ h => h.1

theorem XsetOf_subset_Sset (R Z : Subgroup G) : hyp.XsetOf R Z ⊆ hyp.Sset :=
  fun _ h => h.1.1

theorem XsetOf_finite [Finite G] (R Z : Subgroup G) : (hyp.XsetOf R Z).Finite := by
  letI : Invertible ((Nat.card G : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible ((Nat.card ↥hyp.H : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible ((Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact hyp.Sset_finite.subset (hyp.XsetOf_subset_Sset R Z)

/-- **`𝒳(R, Z)` is closed under complex conjugation**: `𝒮(R)`-membership is
conjugation-closed (`conj_mem_SsetOf`), and the `LeKer` constancy on `Z`
transports through `star` in both directions. -/
theorem conj_mem_XsetOf [Finite G] {R Z : Subgroup G} {χ : ClassFunction ↥hyp.H ℂ}
    (hχ : χ ∈ hyp.XsetOf R Z) : χ.conj ∈ hyp.XsetOf R Z := by
  obtain ⟨hχS, hker⟩ := hχ
  refine ⟨hyp.conj_mem_SsetOf hχS, fun hcon => hker fun x hx => ?_⟩
  have h := hcon x hx
  rw [ClassFunction.conj_apply, ClassFunction.conj_apply] at h
  exact star_injective h

/-- **Membership in `𝒳(R, Z)` for irreducibles, `Z ≤ Q₁`**: the `𝒮`-membership
clause is automatic — `Q₁ ⊆ Ker χ` would force `Z ⊆ Ker χ`.  This is the
form consumed by the two-kernel counting. -/
theorem mem_XsetOf_iff_of_le_Q1 {R Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    {χ : ClassFunction ↥hyp.H ℂ} (hχirr : IsIrreducibleCharacter χ) :
    χ ∈ hyp.XsetOf R Z ↔ hyp.LeKer χ R ∧ ¬ hyp.LeKer χ Z := by
  constructor
  · rintro ⟨⟨-, hR⟩, hZ⟩
    exact ⟨hR, hZ⟩
  · rintro ⟨hR, hZ⟩
    exact ⟨⟨⟨hχirr, fun hQ1 => hZ fun x hx => hQ1 x (hZQ1 hx)⟩, hR⟩, hZ⟩

/-- **`|Q₁|` is odd when `Q₁` is a `p`-group**: `p = 2` is excluded by
`Q1_not_two_group`, so `p` is an odd prime and `|Q₁| = p^n` is odd.  Supplies
the `hQ1odd` hypothesis of the no-real-characters lemma (2(c)) in the
`p`-group context of steps (3)–(8). -/
theorem odd_card_Q1_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1) : Odd (Nat.card ↥hyp.Q1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ1p.exists_card_eq
  have hp2 : p ≠ 2 := fun h2 => hyp.Q1_not_two_group (by rwa [h2] at hQ1p)
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

open scoped Classical in
/-- **The `𝒳(R, Z)` degree-square sum** (p. 147, step (3) counting): for
`Z ≤ Q₁`, `∑_{χ ∈ 𝒳(R,Z)} χ(1)² = |H⧸R| − |H⧸(R·Z)|` (quotients inside `↥H`).
Membership is exactly "kernel contains `R` but not `Z`"
(`mem_XsetOf_iff_of_le_Q1` + `leKer_iff_subset_characterKernel`), so this is
`sum_degreeSq_ker_subset_not_subset` at `N = R`, `M = Z`. -/
theorem sum_degreeSq_XsetOf [Finite G] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {R Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    [(R.subgroupOf hyp.H).Normal]
    [((R.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter ↥hyp.H =>
        (χ : ClassFunction ↥hyp.H ℂ) ∈ hyp.XsetOf R Z),
        ((χ : ClassFunction ↥hyp.H ℂ) 1) ^ 2
      = (Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H) : ℂ)
        - (Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H))) : ℂ) := by
  classical
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  have hcongr : ∀ χb : IrreducibleCharacter ↥hyp.H,
      ((χb : ClassFunction ↥hyp.H ℂ) ∈ hyp.XsetOf R Z)
      ↔ (((R.subgroupOf hyp.H : Subgroup ↥hyp.H) : Set ↥hyp.H)
            ⊆ OddOrder.Peterfalvi.S03.characterKernel (χb : ClassFunction ↥hyp.H ℂ) ∧
          ¬ ((Z.subgroupOf hyp.H : Subgroup ↥hyp.H) : Set ↥hyp.H)
            ⊆ OddOrder.Peterfalvi.S03.characterKernel (χb : ClassFunction ↥hyp.H ℂ)) := by
    intro χb
    rw [hyp.mem_XsetOf_iff_of_le_Q1 hZQ1 χb.isIrreducible,
      hyp.leKer_iff_subset_characterKernel, hyp.leKer_iff_subset_characterKernel]
  rw [Finset.filter_congr (fun χb _ => by
    constructor
    · exact fun h => by simpa using (hcongr χb).mp (by simpa using h)
    · exact fun h => by simpa using (hcongr χb).mpr (by simpa using h))]
  exact sum_degreeSq_ker_subset_not_subset (R.subgroupOf hyp.H) (Z.subgroupOf hyp.H)

open scoped Classical in
/-- **`sum_degreeSq_XsetOf`, `toFinset` form** (the shape produced by the
counterexample extraction): bundling `x ↦ ⟨x, irr⟩` is a bijection onto the
filtered irreducible-character `Finset` of `sum_degreeSq_XsetOf`. -/
theorem sum_degreeSq_XsetOf_toFinset [Finite G]
    [Invertible (Nat.card ↥hyp.H : ℂ)] {R Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    [(R.subgroupOf hyp.H).Normal]
    [((R.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    (hfin : (hyp.XsetOf R Z).Finite) :
    ∑ x ∈ hfin.toFinset, (x (1 : ↥hyp.H)) ^ 2
      = (Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H) : ℂ)
        - (Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H))) : ℂ) := by
  classical
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  rw [← hyp.sum_degreeSq_XsetOf hZQ1]
  refine Finset.sum_bij'
    (fun x hx => (⟨x, ((hfin.mem_toFinset.mp hx).1.1.1 :)⟩ : IrreducibleCharacter ↥hyp.H))
    (fun χb hb => (χb : ClassFunction ↥hyp.H ℂ)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hfin.mem_toFinset.mp hx⟩
  · intro χb hb
    rw [Set.Finite.mem_toFinset]
    exact (Finset.mem_filter.mp hb).2
  · intro x hx
    rfl
  · intro χb hb
    rfl
  · intro x hx
    rfl

/-- **`|H⧸A'| = d·|S⧸A'|·|Q₁|`** for `A' ≤ S`: the `Q₁`-side tower
`|H⧸A'| = |Q₁|·|H⧸A'Q₁|` (`card_quot_eq_card_quot_Q1_mul` at `Q₁ ⊓ A' = ⊥`)
and `|H⧸A'Q₁| = d·|S⧸A'|` (`card_quot_sup_Q1_eq_d_mul`). -/
theorem card_quot_subgroupOf_eq_d_mul [Finite G] {A' : Subgroup G} (hA' : A' ≤ hyp.S)
    [(A'.subgroupOf hyp.H).Normal] :
    Nat.card (↥hyp.H ⧸ A'.subgroupOf hyp.H)
      = hyp.d * Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) * Nat.card ↥hyp.Q1 := by
  have hi := hyp.card_quot_eq_card_quot_Q1_mul (R := A') (hyp.Q1_inf_eq_bot_of_le_S hA')
  rw [hyp.card_quot_bot_subgroupOf_Q1, hyp.card_quot_sup_Q1_eq_d_mul hA'] at hi
  rw [hi]
  ring

/-- **`|H⧸A'Z| = d·|S⧸A'|·|Q₁⧸Z|`** for `A' ≤ S`, `Z ≤ Q₁` (the second
counting factor of step (3)): rewrite the `↥H`-level join as `(A'⊔Z)`-in
(`subgroupOf_sup`), apply the `Q₁`-side tower at `Q₁ ⊓ (A'⊔Z) = Z`
(`Q1_inf_sup_eq`), absorb `Z` into `Q₁` in the join with `Q₁`, and finish
with `card_quot_sup_Q1_eq_d_mul`. -/
theorem card_quot_sup_Z_subgroupOf_eq [Finite G] {A' Z : Subgroup G}
    (hA' : A' ≤ hyp.S) (hZQ1 : Z ≤ hyp.Q1)
    [(A'.subgroupOf hyp.H).Normal]
    [((A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal] :
    Nat.card (↥hyp.H ⧸ ((A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)))
      = hyp.d * Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S)
        * Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) := by
  have hsub : (A' ⊔ Z).subgroupOf hyp.H
      = (A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H) :=
    Subgroup.subgroupOf_sup (hA'.trans (hyp.S_le_Q.trans hyp.Q_le_H))
      (hZQ1.trans (hyp.Q1_le_Q.trans hyp.Q_le_H))
  haveI : ((A' ⊔ Z).subgroupOf hyp.H).Normal := hsub ▸
    ‹((A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal›
  have hi := hyp.card_quot_eq_card_quot_Q1_mul (R := A' ⊔ Z)
    (hyp.Q1_inf_sup_eq hA' hZQ1)
  have hjoin : ((A' ⊔ Z).subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)
      = (A'.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H) := by
    rw [hsub, sup_assoc]
    congr 1
    exact sup_eq_right.mpr fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hZQ1 (Subgroup.mem_subgroupOf.mp hx))
  rw [hjoin, hyp.card_quot_sup_Q1_eq_d_mul hA'] at hi
  rw [← hsub, hi]
  ring

/-- **`|Q₁| = |Q₁⧸Z|·|Z|`** for `Z ≤ Q₁` (the `Q₂ = ⊥` case of the internal
tower `card_quot_Q1_eq_mul`). -/
theorem card_Q1_eq_card_quot_mul {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) :
    Nat.card ↥hyp.Q1
      = Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) * Nat.card ↥Z := by
  have h := hyp.card_quot_Q1_eq_mul (Q₂ := ⊥) bot_le hZQ1
  rw [hyp.card_quot_bot_subgroupOf_Q1] at h
  rw [h]
  congr 1
  rw [Subgroup.bot_subgroupOf, ← Subgroup.index_eq_card, Subgroup.index_bot]

open scoped Classical in
/-- **The step (3) counting, factored form** (p. 147, `𝒳₁` at `A' = S'`):
`∑_{χ ∈ 𝒳(A',Z)} χ(1)² = d·|S⧸A'|·|Q₁⧸Z|·(|Z|−1)` for `A' ≤ S`, `Z ≤ Q₁` —
the two-kernel counting difference `|H⧸A'| − |H⧸A'Z|` with both terms
factored through the direct product `Q = S × Q₁`. -/
theorem sum_degreeSq_XsetOf_eq_mul [Finite G] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {A' Z : Subgroup G} (hA' : A' ≤ hyp.S) (hZQ1 : Z ≤ hyp.Q1)
    [(A'.subgroupOf hyp.H).Normal]
    [((A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    (hfin : (hyp.XsetOf A' Z).Finite) :
    ∑ x ∈ hfin.toFinset, (x (1 : ↥hyp.H)) ^ 2
      = (hyp.d : ℂ) * (Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) : ℂ)
        * (Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) : ℂ)
        * ((Nat.card ↥Z : ℂ) - 1) := by
  rw [hyp.sum_degreeSq_XsetOf_toFinset hZQ1 hfin,
    hyp.card_quot_subgroupOf_eq_d_mul hA',
    hyp.card_quot_sup_Z_subgroupOf_eq hA' hZQ1,
    hyp.card_Q1_eq_card_quot_mul hZQ1]
  push_cast
  ring

open scoped Classical in
/-- **`𝒳(A', Z)` is nonempty** for `A' ≤ S`, `⊥ ≠ Z ≤ Q₁` (p. 147): the
degree-square sum `d·|S⧸A'|·|Q₁⧸Z|·(|Z|−1)` is positive (`|Z| ≥ 2`), so the
family cannot be empty. -/
theorem XsetOf_nonempty [Finite G] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {A' Z : Subgroup G} (hA' : A' ≤ hyp.S) (hZQ1 : Z ≤ hyp.Q1) (hZne : Z ≠ ⊥)
    [(A'.subgroupOf hyp.H).Normal]
    [((A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal] :
    (hyp.XsetOf A' Z).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  have hsum := hyp.sum_degreeSq_XsetOf_eq_mul hA' hZQ1 (hyp.XsetOf_finite A' Z)
  rw [Set.Finite.toFinset_eq_empty.mpr hempty, Finset.sum_empty] at hsum
  have hd0 : ((hyp.d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
  have hS0 : ((Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hQ0 : ((Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hZ2 : 2 ≤ Nat.card ↥Z :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot Z).mpr hZne)
  have hZ0 : ((Nat.card ↥Z : ℕ) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h1 : Nat.card ↥Z = 1 := Nat.cast_eq_one.mp h
    omega
  exact hd0 (by
    rcases mul_eq_zero.mp hsum.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · exact absurd h'' hS0
      · exact absurd h' hQ0
    · exact absurd h hZ0)

end Hypothesis

/-! ## The (3.1) numeric core (p. 147)

Degrees in `𝒳₁` are `d·p^k` (`exists_apply_one_eq_d_mul_pow`); the chain
adjoins of Part A need, at a step of degree `d·p^k` with anchor `d·p^{k₀}`,
the strict bound `2·p^{k₀}·p^k < ∑_{S₁} p^{2k_x}` — the `hlt` of
`coherent_insert_pair_of_two_mul_lt_sum`.  It follows from `p^{2k}` dividing
the accumulated sum (Peterfalvi's (3.1) divisibility): `p^{2k} ≤ |Q₁⧸Z|`
([Is] 2.30) makes `p^{2k}` divide the counting total (`|Q₁⧸Z|` is a `p`-power
and `p ∤ d`), the unaccumulated members all have `k_x ≥ k`, and `p ≥ 3`,
`k₀ < k` close the arithmetic. -/

/-- A `p`-power bounded below by `p^i` is divisible by `p^i`. -/
theorem pow_dvd_of_exists_pow_of_le {p i n : ℕ} (hp : 1 < p)
    (hn : ∃ j, n = p ^ j) (hle : p ^ i ≤ n) : p ^ i ∣ n := by
  obtain ⟨j, rfl⟩ := hn
  exact Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp).mp hle)

/-- **The (3.1) numeric key** (p. 147): if `p ≥ 3`, `k₀ < k`, and `p^{2k}`
divides a positive sum `s`, then `2·p^{k₀}·p^k < s` — Peterfalvi's
`2χ₁(1)χᵢ(1) < pχ₁(1)χᵢ(1) ≤ χᵢ(1)² ≤ ∑_{j<i} χⱼ(1)²` with `d²` cancelled:
`2·p^{k₀+k} < p^{k₀+k+1} ≤ p^{2k} ≤ s`. -/
theorem two_mul_pow_lt_of_pow_dvd {p k₀ k s : ℕ} (hp : 3 ≤ p) (hk : k₀ < k)
    (hdvd : p ^ (2 * k) ∣ s) (hs : 0 < s) :
    2 * (p ^ k₀ : ℝ) * (p ^ k : ℝ) < (s : ℝ) := by
  have hppos : 0 < p := by omega
  have hX : 0 < p ^ k₀ * p ^ k := Nat.mul_pos (pow_pos hppos k₀) (pow_pos hppos k)
  have h1 : 2 * (p ^ k₀ * p ^ k) < p * (p ^ k₀ * p ^ k) :=
    (Nat.mul_lt_mul_right hX).mpr (by omega)
  have h2 : p * (p ^ k₀ * p ^ k) = p ^ (k₀ + k + 1) := by ring
  have h3 : p ^ (k₀ + k + 1) ≤ p ^ (2 * k) :=
    Nat.pow_le_pow_right hppos (by omega)
  have h4 : 2 * (p ^ k₀ * p ^ k) < s :=
    ((h1.trans_eq h2).trans_le h3).trans_le (Nat.le_of_dvd hs hdvd)
  calc 2 * (p ^ k₀ : ℝ) * (p ^ k : ℝ)
      = ((2 * (p ^ k₀ * p ^ k) : ℕ) : ℝ) := by push_cast; ring
    _ < (s : ℝ) := by exact_mod_cast h4

namespace Hypothesis

variable (hyp : Hypothesis G)

/-- **`|Q₁⧸Z|` is a `p`-power** for a `p`-group `Q₁` (Lagrange: the coset
count divides `|Q₁| = p^n`). -/
theorem exists_card_quot_Q1_eq_pow [Finite G] {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1) (Z : Subgroup G) :
    ∃ j, Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) = p ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ1p.exists_card_eq
  have hdvd : Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) ∣ p ^ n := by
    rw [← hn, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨m, hm⟩

/-- **`(p, d) = 1`** for a `p`-group `Q₁`: `p ∣ |Q₁| ∣ |Q|` (`Q₁` is
nontrivial) and `(|Q|, |D|) = 1`. -/
theorem coprime_d_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1) : Nat.Coprime p hyp.d := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ1p.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hn
    haveI := hyp.nontrivial_Q1
    have := Finite.one_lt_card (α := ↥hyp.Q1)
    omega
  have hpQ1 : p ∣ Nat.card ↥hyp.Q1 := hn ▸ dvd_pow_self p hn0
  have hQ1Q : Nat.card ↥hyp.Q1 ∣ Nat.card ↥hyp.Q :=
    Subgroup.card_dvd_of_le hyp.Q1_le_Q
  exact Nat.Coprime.coprime_dvd_left (hpQ1.trans hQ1Q) hyp.coprime_Q_D

open scoped Classical in
/-- **The step (3) counting in exponent units** (ℕ): with every member of
`𝒳(A',Z)` of degree `d·p^{k(x)}`,
`d·∑_x p^{2k(x)} = |S⧸A'|·|Q₁⧸Z|·(|Z|−1)` — the `T`-factorisation
`sum_degreeSq_XsetOf_eq_mul` with one `d` cancelled against the degrees. -/
theorem d_mul_sum_pow_eq [Finite G] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {A' Z : Subgroup G} (hA' : A' ≤ hyp.S) (hZQ1 : Z ≤ hyp.Q1)
    [(A'.subgroupOf hyp.H).Normal]
    [((A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    (hfin : (hyp.XsetOf A' Z).Finite) {p : ℕ}
    {k : ClassFunction ↥hyp.H ℂ → ℕ}
    (hk : ∀ x ∈ hyp.XsetOf A' Z,
      x (1 : ↥hyp.H) = (hyp.d : ℂ) * ((p ^ k x : ℕ) : ℂ)) :
    hyp.d * ∑ x ∈ hfin.toFinset, p ^ (2 * k x)
      = Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S)
        * Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) * (Nat.card ↥Z - 1) := by
  have hsum := hyp.sum_degreeSq_XsetOf_eq_mul hA' hZQ1 hfin
  have hL : ∑ x ∈ hfin.toFinset, (x (1 : ↥hyp.H)) ^ 2
      = ((hyp.d : ℕ) : ℂ) ^ 2 * ∑ x ∈ hfin.toFinset, ((p ^ (2 * k x) : ℕ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hk x (hfin.mem_toFinset.mp hx)]
    push_cast
    rw [pow_mul']
    ring
  rw [hL] at hsum
  have hdne : ((hyp.d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
  have hz1 : 1 ≤ Nat.card ↥Z := Nat.card_pos
  have h2 : ((hyp.d : ℕ) : ℂ) * ∑ x ∈ hfin.toFinset, ((p ^ (2 * k x) : ℕ) : ℂ)
      = (Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S) : ℂ)
        * (Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) : ℂ)
        * ((Nat.card ↥Z : ℂ) - 1) := by
    refine mul_left_cancel₀ hdne ?_
    linear_combination hsum
  have h3 : ((hyp.d * ∑ x ∈ hfin.toFinset, p ^ (2 * k x) : ℕ) : ℂ)
      = ((Nat.card (↥hyp.S ⧸ A'.subgroupOf hyp.S)
          * Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1)
          * (Nat.card ↥Z - 1) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hz1] at h2 ⊢
    linear_combination h2
  exact Nat.cast_injective h3

open scoped Classical in
/-- **The (3.1) divisibility of the exponent total** (p. 147): if the step
degree obeys `p^j ≤ |Q₁⧸Z|` (supplied by [Is] Cor. 2.30 at `j = 2k`), then
`p^j` divides `W = ∑_{𝒳(A',Z)} p^{2k(x)}`: `p^j ∣ |Q₁⧸Z| ∣ d·W`
(`d_mul_sum_pow_eq`) and `(p^j, d) = 1`. -/
theorem pow_dvd_sum_pow [Finite G] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {A' Z : Subgroup G} (hA' : A' ≤ hyp.S) (hZQ1 : Z ≤ hyp.Q1)
    [(A'.subgroupOf hyp.H).Normal]
    [((A'.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    (hfin : (hyp.XsetOf A' Z).Finite) {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1)
    {k : ClassFunction ↥hyp.H ℂ → ℕ}
    (hk : ∀ x ∈ hyp.XsetOf A' Z,
      x (1 : ↥hyp.H) = (hyp.d : ℂ) * ((p ^ k x : ℕ) : ℂ))
    {j : ℕ} (hle : p ^ j ≤ Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1)) :
    p ^ j ∣ ∑ x ∈ hfin.toFinset, p ^ (2 * k x) := by
  have hW := hyp.d_mul_sum_pow_eq hA' hZQ1 hfin hk
  have hdvd_n : p ^ j ∣ Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) :=
    pow_dvd_of_exists_pow_of_le hp.one_lt
      (hyp.exists_card_quot_Q1_eq_pow hp hQ1p Z) hle
  have hdvd_T : p ^ j ∣ hyp.d * ∑ x ∈ hfin.toFinset, p ^ (2 * k x) := by
    rw [hW]
    exact ((hdvd_n.mul_left _).mul_right _)
  exact ((hyp.coprime_d_of_isPGroup hp hQ1p).pow_left j).dvd_of_dvd_mul_left hdvd_T

/-! ## Part A: `𝒳₁ = 𝒳 ∩ 𝒮(S')` is coherent (p. 147)

The chain assembly: the equal-minimal-degree base `B` is coherent by
Lemma 1(b) (`coherent_of_constant_degree`, relativised to a subfamily of `𝒮`);
the conjugate-pair decomposition `exists_conjPair_pairUnion_eq` enumerates
`𝒳₁ ∖ B` min-degree-first; each pair is adjoined by the Lemma 1(a) wrapper
`coherent_insert_pair_of_two_mul_lt_sum`, whose degree inequality is the
(3.1) divisibility (`pow_dvd_sum_pow` + the [Is] 2.30 degree bound at
`D₀ = SZ`) closed by `two_mul_pow_lt_of_pow_dvd`. -/

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

/-- **Peterfalvi Lemma 1(b), subfamily form**: a finite, conjugation-closed,
equal-degree family `B ⊆ 𝒮` with at least two members is coherent.  The §7
(5.2) hypothesis for `B` restricts from the `𝒮`-level toolkit (every field is
per-member or monotone in the family), and `coherent_of_constant_degree`
concludes. -/
theorem coherent_of_subset_constant_degree (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {B : Set (ClassFunction ↥hyp.H ℂ)} (hBS : B ⊆ hyp.Sset) (hBfin : B.Finite)
    (hBconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate B) (hcard : 2 ≤ B.ncard)
    (hconst : ∀ a ∈ B, ∀ b ∈ B, a (1 : ↥hyp.H) = b (1 : ↥hyp.H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau B hyp.A) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  have hself : ∀ ⦃ζ : ClassFunction ↥hyp.H ℂ⦄, ζ ∈ hyp.Sset →
      ClassFunction.inner ζ ζ = 1 := by
    intro ζ hζ
    have h := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
      (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H) (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H)
    rw [if_pos rfl] at h
    simpa using h
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun _ _ hφ hψ => hyp.tau_inner_eq_of_supported_Sset
        ⟨Submodule.span_mono hBS hφ.1, hφ.2⟩ ⟨Submodule.span_mono hBS hψ.1, hψ.2⟩
      conjugate_closed := hBconj
      no_real_characters := (hasNoRealCharacters_Sset hyp hd hQ1odd).mono hBS
      pairwise_orthogonal := fun _ _ hχ hψ hne =>
        hyp.Sset_pairwiseOrthogonal (hBS hχ) (hBS hψ) hne
      difference_image := fun _ hχ => hyp.ssetDifferenceImage hd hQ1odd (hBS hχ)
      difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
        hyp.ssetDifferenceImages_orthogonal hd hQ1odd (hBS hφ) (hBS hχ) h1 h2 }
    hBfin hcard
    (fun ζ hζ => hself (hBS hζ))
    (fun a ha b hb => hyp.tau_mem_ZIrr (Submodule.sub_mem _
      (Submodule.subset_span (hBS ha)) (Submodule.subset_span (hBS hb))))
    (fun a ha b hb => by
      change a (1 : ↥hyp.H) = b (1 : ↥hyp.H)
      exact hconst a ha b hb)
    (fun a ha => by
      change a (1 : ↥hyp.H) ≠ 0
      obtain ⟨m, hmpos, hm⟩ := hyp.exists_apply_one_eq_d_mul (hBS ha)
      rw [hm]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hyp.d_pos.ne')
        (Nat.cast_ne_zero.mpr hmpos.ne'))
    hyp.one_notMem_A
    (fun a ha b hb => by
      have h := hyp.scaled_diff_support_subset_A_of_mem_Sset (hBS ha) (hBS hb)
        (n := 1) (m := 1) (by rw [Nat.cast_one, one_mul, one_mul]; exact hconst a ha b hb)
      simpa using h)

open scoped Classical in
/-- **Peterfalvi p. 147, step (3) Part A: `𝒳₁ = 𝒳 ∩ 𝒮(S')` is coherent**
(campaign issue 1054) for a nontrivial `Z ≤ Z(Q₁)` (`Q₁` a `p`-group, `d` odd,
`Z` `H`-invariant through the `Normal` instances).

Chain assembly: all degrees in `𝒳₁` are `d·p^k`
(`exists_apply_one_eq_d_mul_pow`); the equal-minimal-degree base `B` is
coherent by Lemma 1(b) (`coherent_of_subset_constant_degree`, `|B| ≥ 2` from a
conjugate pair); the min-degree-first conjugate-pair decomposition
(`exists_conjPair_pairUnion_eq`) feeds the `coherentPairChain` engine, each
step adjoined by `coherent_insert_pair_of_two_mul_lt_sum` whose degree
inequality `2·p^{k₀}·p^k < ∑_{S₁} p^{2k_x}` is Peterfalvi's (3.1): `p^{2k}`
divides both the counting total (`pow_dvd_sum_pow`, via the [Is] 2.30 bound
`p^{2k} ≤ |Q₁⧸Z|` at `D₀ = SZ`) and the unaccumulated remainder (min-degree
clause), hence the accumulated sum, and `p ≥ 3`, `k₀ < k` close the
arithmetic (`two_mul_pow_lt_of_pow_dvd`). -/
theorem xsetOf_sder_coherent (hd : Odd hyp.d) {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1)
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) (hZne : Z ≠ ⊥)
    (hZc : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ = 1)
    [(hyp.Sder.subgroupOf hyp.H).Normal]
    [((hyp.Sder.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    [((hyp.S ⊔ Z).subgroupOf hyp.H).Normal] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf hyp.Sder Z) hyp.A) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : ((hyp.Sder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal :=
    hyp.Sder_subgroupOf_Q_normal
  have hQ1odd := hyp.odd_card_Q1_of_isPGroup hp hQ1p
  have hp2 : p ≠ 2 := fun h2 => hyp.Q1_not_two_group (by rwa [h2] at hQ1p)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  -- the family `Y = 𝒳₁` and its basic structure
  have hYS : hyp.XsetOf hyp.Sder Z ⊆ hyp.Sset := hyp.XsetOf_subset_Sset _ _
  have hYSder : hyp.XsetOf hyp.Sder Z ⊆ hyp.SsetOf hyp.Sder :=
    hyp.XsetOf_subset_SsetOf _ _
  have hYfin : (hyp.XsetOf hyp.Sder Z).Finite := hyp.XsetOf_finite _ _
  have hYconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.XsetOf hyp.Sder Z) :=
    fun _ hx => hyp.conj_mem_XsetOf hx
  have hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.XsetOf hyp.Sder Z) :=
    (hasNoRealCharacters_Sset hyp hd hQ1odd).mono hYS
  have hYne : (hyp.XsetOf hyp.Sder Z).Nonempty :=
    hyp.XsetOf_nonempty hyp.Sder_le_S hZQ1 hZne
  -- the exponent function: `x(1) = d·p^{k x}` on `Y`
  have hdegY : ∀ x ∈ hyp.XsetOf hyp.Sder Z,
      ∃ kx : ℕ, x (1 : ↥hyp.H) = (hyp.d : ℂ) * ((p ^ kx : ℕ) : ℂ) :=
    fun x hx => hyp.exists_apply_one_eq_d_mul_pow hp hQ1p (hYSder hx)
  choose! k hk using hdegY
  have hdne : ((hyp.d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
  -- degree comparisons transfer to exponent comparisons
  have hre : ∀ x ∈ hyp.XsetOf hyp.Sder Z,
      (x (1 : ↥hyp.H)).re = (hyp.d : ℝ) * ((p ^ k x : ℕ) : ℝ) := by
    intro x hx
    rw [hk x hx, ← Nat.cast_mul, Complex.natCast_re]
    push_cast
    ring
  have hkmono : ∀ x ∈ hyp.XsetOf hyp.Sder Z, ∀ y ∈ hyp.XsetOf hyp.Sder Z,
      (x (1 : ↥hyp.H)).re ≤ (y (1 : ↥hyp.H)).re → k x ≤ k y := by
    intro x hx y hy hle
    rw [hre x hx, hre y hy] at hle
    have hd0 : (0 : ℝ) < (hyp.d : ℝ) := by exact_mod_cast hyp.d_pos
    have h1 : ((p ^ k x : ℕ) : ℝ) ≤ ((p ^ k y : ℕ) : ℝ) :=
      le_of_mul_le_mul_left hle hd0
    have h2 : p ^ k x ≤ p ^ k y := by exact_mod_cast h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hkinj : ∀ x ∈ hyp.XsetOf hyp.Sder Z, ∀ y ∈ hyp.XsetOf hyp.Sder Z,
      x (1 : ↥hyp.H) = y (1 : ↥hyp.H) → k x = k y := by
    intro x hx y hy heq
    have h1 := (hk x hx).symm.trans (heq.trans (hk y hy))
    have h2 : ((p ^ k x : ℕ) : ℂ) = ((p ^ k y : ℕ) : ℂ) := mul_left_cancel₀ hdne h1
    exact Nat.pow_right_injective hp.two_le (Nat.cast_injective h2)
  have hconjdeg : ∀ x ∈ hyp.XsetOf hyp.Sder Z,
      x.conj (1 : ↥hyp.H) = x (1 : ↥hyp.H) := by
    intro x hx
    rw [ClassFunction.conj_apply, hk x hx]
    simp
  -- the minimal-degree anchor `χ₀`
  obtain ⟨χ₀, hχ₀Y, hχ₀min⟩ := Set.exists_min_image (hyp.XsetOf hyp.Sder Z)
    (fun x => (x (1 : ↥hyp.H)).re) hYfin hYne
  have hk₀min : ∀ x ∈ hyp.XsetOf hyp.Sder Z, k χ₀ ≤ k x :=
    fun x hx => hkmono χ₀ hχ₀Y x hx (hχ₀min x hx)
  -- the equal-minimal-degree base `B`
  set B := {x ∈ hyp.XsetOf hyp.Sder Z | k x = k χ₀} with hBdef
  have hBY : B ⊆ hyp.XsetOf hyp.Sder Z := Set.sep_subset _ _
  have hBconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate B := by
    rintro x ⟨hxY, hxk⟩
    refine ⟨hYconj hxY, ?_⟩
    rw [← hxk]
    exact hkinj _ (hYconj hxY) _ hxY (hconjdeg x hxY)
  have hχ₀B : χ₀ ∈ B := ⟨hχ₀Y, rfl⟩
  have hB2 : 2 ≤ B.ncard := by
    have hχ₀cB : χ₀.conj ∈ B := hBconj hχ₀B
    have hne : χ₀ ≠ χ₀.conj := fun h => hnoreal hχ₀Y h.symm
    have hsub : ({χ₀, χ₀.conj} : Set (ClassFunction ↥hyp.H ℂ)) ⊆ B := by
      rintro x (rfl | rfl)
      · exact hχ₀B
      · exact hχ₀cB
    calc 2 = ({χ₀, χ₀.conj} : Set (ClassFunction ↥hyp.H ℂ)).ncard :=
          (Set.ncard_pair hne).symm
      _ ≤ B.ncard := Set.ncard_le_ncard hsub (hYfin.subset hBY)
  have hconstB : ∀ a ∈ B, ∀ b ∈ B, a (1 : ↥hyp.H) = b (1 : ↥hyp.H) := by
    rintro a ⟨haY, hak⟩ b ⟨hbY, hbk⟩
    rw [hk a haY, hk b hbY, hak, hbk]
  obtain ⟨h0⟩ := hyp.coherent_of_subset_constant_degree hd hQ1odd
    (hBY.trans hYS) (hYfin.subset hBY) hBconj hB2 hconstB
  -- the min-degree-first conjugate-pair decomposition of `Y` over `B`
  obtain ⟨N, pair, hcover, hfresh, hmin⟩ :=
    exists_conjPair_pairUnion_eq hBY hYfin hYconj hBconj hnoreal
  -- the accumulated sets stay inside `Y` and conjugation-closed
  have hacc_sub : ∀ i ≤ N,
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i
        ⊆ hyp.XsetOf hyp.Sder Z := by
    intro i hiN x hx
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hB | ⟨j, hji, hj⟩
    · exact hBY hB
    · obtain ⟨hpc, hp1Y', -, -⟩ := hfresh j (lt_of_lt_of_le hji hiN)
      rcases hj with h1 | h2
      · exact h1 ▸ hp1Y'
      · have h2' : x = (pair j).2 := h2
        rw [h2', hpc]
        exact hYconj hp1Y'
  have hacc_conj : ∀ i ≤ N,
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i) := by
    intro i hiN x hx
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hB | ⟨j, hji, hj⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hBconj hB))
    · obtain ⟨hpc, -, -, -⟩ := hfresh j (lt_of_lt_of_le hji hiN)
      refine OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, ?_⟩)
      rcases hj with h1 | h2
      · right
        change x.conj = (pair j).2
        rw [h1, hpc]
      · left
        have h2' : x = (pair j).2 := h2
        rw [h2', hpc, ClassFunction.conj_conj]
  -- the per-step adjoining
  have hstep : ∀ i, i < N →
      OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i) hyp.A →
      OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair (i + 1)) hyp.A := by
    intro i hiN hcoh_i
    obtain ⟨hpconj, hp1Y, hp1fresh, hp2fresh⟩ := hfresh i hiN
    have hacc_sub_i := hacc_sub i hiN.le
    have haccfin : (OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i).Finite :=
      hYfin.subset hacc_sub_i
    have hχ₀acc : χ₀ ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i :=
      OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hχ₀B)
    -- `k χ₀ < k χ` for the adjoined `χ = (pair i).1`
    have hklt : k χ₀ < k (pair i).1 := by
      rcases Nat.lt_or_ge (k χ₀) (k (pair i).1) with h | h
      · exact h
      · have hχB : (pair i).1 ∈ B := ⟨hp1Y, le_antisymm h (hk₀min _ hp1Y)⟩
        exact absurd (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hχB)) hp1fresh
    -- the (1.2) degree bound: `p^{2k} ≤ |Q₁⧸Z|` at `D₀ = SZ`
    have hle : p ^ (2 * k (pair i).1)
        ≤ Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) := by
      have hcomm : ∀ x ∈ hyp.S ⊔ Z, ∀ q ∈ hyp.Q, ⁅x, q⁆ ∈ hyp.Sder := by
        intro x hx q hq
        have h := hyp.commutator_mem_sup_Sder_of_central (Q₃ := (⊥ : Subgroup G)) hZQ1
          (fun z hz y hy => by rw [Subgroup.mem_bot]; exact hZc z hz y hy) hx hq
        rwa [sup_bot_eq] at h
      obtain ⟨a', ha'deg, ha'sq⟩ := hyp.exists_deg_sq_le_of_mem_SsetOf hyp.Sder
        (hyp.S ⊔ Z) (hyp.Sder_le_S.trans hyp.S_le_Q) (hyp.Sder_le_S.trans le_sup_left)
        (sup_le hyp.S_le_Q (hZQ1.trans hyp.Q1_le_Q))
        (hyp.map_mk_le_center_of_commutator_mem hcomm)
        (hYSder hp1Y)
      rw [hyp.index_subgroupOf_sup_S_eq hZQ1] at ha'sq
      have haa' : a' = p ^ k (pair i).1 := by
        have h1 := ha'deg.symm.trans (hk _ hp1Y)
        exact_mod_cast mul_left_cancel₀ hdne h1
      rw [haa'] at ha'sq
      rw [pow_mul']
      exact ha'sq
    -- the (3.1) divisibility of the accumulated sum
    have hsub_fin : haccfin.toFinset ⊆ hYfin.toFinset := fun x hx =>
      hYfin.mem_toFinset.mpr (hacc_sub_i (haccfin.mem_toFinset.mp hx))
    have hsplit := Finset.sum_sdiff (f := fun x => p ^ (2 * k x)) hsub_fin
    have hW : p ^ (2 * k (pair i).1) ∣ ∑ x ∈ hYfin.toFinset, p ^ (2 * k x) :=
      hyp.pow_dvd_sum_pow hyp.Sder_le_S hZQ1 hYfin hp hQ1p hk hle
    have hdvd_diff : p ^ (2 * k (pair i).1)
        ∣ ∑ x ∈ hYfin.toFinset \ haccfin.toFinset, p ^ (2 * k x) := by
      refine Finset.dvd_sum fun x hx => ?_
      obtain ⟨hxY, hxacc⟩ := Finset.mem_sdiff.mp hx
      have hxY' := hYfin.mem_toFinset.mp hxY
      have hxacc' : x ∉ OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i :=
        fun hc => hxacc (haccfin.mem_toFinset.mpr hc)
      have hkle : k (pair i).1 ≤ k x :=
        hkmono _ hp1Y x hxY' (hmin i hiN x hxY' hxacc')
      exact Nat.pow_dvd_pow p (by omega)
    have hdvd_s : p ^ (2 * k (pair i).1) ∣ ∑ x ∈ haccfin.toFinset, p ^ (2 * k x) := by
      rw [← hsplit] at hW
      exact (Nat.dvd_add_right hdvd_diff).mp hW
    have hspos : 0 < ∑ x ∈ haccfin.toFinset, p ^ (2 * k x) :=
      Finset.sum_pos' (fun x _ => Nat.zero_le _)
        ⟨χ₀, haccfin.mem_toFinset.mpr hχ₀acc, pow_pos (by omega) _⟩
    -- Peterfalvi's degree inequality, in the wrapper's real form
    have hltR := two_mul_pow_lt_of_pow_dvd hp3 hklt hdvd_s hspos
    have hsum_eq : ((∑ x ∈ haccfin.toFinset, p ^ (2 * k x) : ℕ) : ℝ)
        = ∑ x ∈ haccfin.toFinset, (((p ^ k x : ℕ) : ℝ)) ^ 2 := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pow_mul']
      push_cast
      ring
    have hltR' : 2 * ((p ^ k χ₀ : ℕ) : ℝ) * ((p ^ k (pair i).1 : ℕ) : ℝ)
        < ∑ x ∈ haccfin.toFinset, (((p ^ k x : ℕ) : ℝ)) ^ 2 := by
      rw [← hsum_eq]
      calc 2 * ((p ^ k χ₀ : ℕ) : ℝ) * ((p ^ k (pair i).1 : ℕ) : ℝ)
          = 2 * ((p : ℝ)) ^ k χ₀ * ((p : ℝ)) ^ k (pair i).1 := by push_cast; ring
        _ < _ := hltR
    -- adjoin the pair by the Lemma 1(a) wrapper
    have hres := hyp.coherent_insert_pair_of_two_mul_lt_sum hd hQ1odd
      (hacc_sub_i.trans hYS) haccfin (hacc_conj i hiN.le) ⟨hcoh_i⟩ hχ₀acc
      (m := fun x => p ^ k x)
      (fun x hx => hk x (hacc_sub_i hx))
      (pow_pos (by omega) _)
      (fun x hx => Nat.pow_dvd_pow p (hk₀min x (hacc_sub_i hx)))
      (hYS hp1Y) hp1fresh (hpconj ▸ hp2fresh)
      (a := p ^ k (pair i).1) (hk _ hp1Y)
      (Nat.pow_dvd_pow p (hk₀min _ hp1Y))
      hltR'
    rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair rfl hpconj]
    exact hres.some
  -- run the chain and rewrite the accumulator to `Y`
  have hall := OddOrder.Peterfalvi.S07.coherentPairChain (τ := hyp.tau) (A := hyp.A)
    B pair h0 N hstep
  exact ⟨hcover ▸ hall⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
