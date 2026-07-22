/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer

/-!
# Transfer over a transversal invariant under conjugation

For the transfer homomorphism `MonoidHom.transfer ϕ : G →* A` (with `ϕ : H →* A`,
`A` commutative, `H` of finite index), if some left transversal `S` of `H` in `G`
is **invariant under conjugation by an element `x ∈ H`** (`x⁻¹ * s * x ∈ S` for all
`s ∈ S`), then

`transfer ϕ x = ϕ ⟨x, _⟩ ^ H.index`.

Conjugation by `x` permutes the coset representatives, so `x • S = S · x` and every
factor of the transfer product `diff ϕ S (x • S)` equals `ϕ x`.

This is the mechanism behind Peterfalvi's transfer computation in the First Case of
Suzuki's theorem (Part II, Ch. II, step (9)): the representatives `1` and
`{t y : y ∈ Q}` of the (right) cosets of `H` are permuted by conjugation by
`x ∈ P` (which centralises `t` and normalises `Q`), giving `T(x) = x ^ (|Q| + 1)`.

It is genuinely different from `MonoidHom.transfer_eq_pow`, whose hypothesis (every
conjugate `g₀⁻¹ xᵏ g₀` that lands in `H` already equals `xᵏ`) *fails* in that
application: here only a *single* transversal need be closed under `x`-conjugation.
-/

namespace OddOrder.GroupTheory

open Subgroup Subgroup.leftTransversals MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]

/-- The pointwise inverse of a right transversal of `H` is a left transversal of `H`.
(If `G = H · T`, then `G = T⁻¹ · H` by inverting `h · t = g ↦ t⁻¹ · h⁻¹ = g⁻¹`.) -/
lemma isComplement_inv_of_isComplement {T : Set G}
    (hT : IsComplement (H : Set G) T) : IsComplement T⁻¹ (H : Set G) := by
  rw [isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  obtain ⟨t, ht, htu⟩ := isComplement_iff_existsUnique_mul_inv_mem.mp hT g⁻¹
  refine ⟨⟨(t : G)⁻¹, Set.inv_mem_inv.mpr t.2⟩, ?_, ?_⟩
  · change ((t : G)⁻¹)⁻¹ * g ∈ H
    simpa using inv_mem ht
  · rintro ⟨s, hs⟩ hmem
    have hsT : s⁻¹ ∈ T := Set.mem_inv.mp hs
    have hst : (⟨s⁻¹, hsT⟩ : ↥T) = t := by
      refine htu _ ?_
      change g⁻¹ * (s⁻¹)⁻¹ ∈ H
      simpa using inv_mem hmem
    exact Subtype.ext (by simpa using congrArg (fun u : ↥T => ((u : G)⁻¹)) hst)

/-- If `a ∈ S` (a left transversal of `H`) lies in the coset `↑a`, then `a` is the
chosen representative of that coset. -/
lemma leftQuotientEquiv_coe_eq_of_mem (S : H.LeftTransversal) {a : G}
    (ha : a ∈ (S : Set G)) :
    (S.2.leftQuotientEquiv (a : G ⧸ H) : G) = a := by
  obtain ⟨s0, _, huniq⟩ := (isComplement_iff_existsUnique_inv_mul_mem.mp S.2) a
  have e1 : S.2.leftQuotientEquiv (a : G ⧸ H) = s0 := by
    refine huniq _ ?_
    change (S.2.leftQuotientEquiv (a : G ⧸ H) : G)⁻¹ * a ∈ H
    rw [← QuotientGroup.eq]
    exact S.2.quotientGroupMk_leftQuotientEquiv (a : G ⧸ H)
  have e2 : (⟨a, ha⟩ : ↥(S : Set G)) = s0 := by
    refine huniq _ ?_
    change (a : G)⁻¹ * a ∈ H
    simp
  exact Subtype.ext_iff.mp (e1.trans e2.symm)

/-- **Transfer over a conjugation-invariant transversal.** If a left transversal `S`
of `H ≤ G` is invariant under conjugation by `x ∈ H`, then
`transfer ϕ x = ϕ ⟨x, hx⟩ ^ H.index`. -/
theorem transfer_eq_pow_of_conj_invariant_transversal [H.FiniteIndex]
    (ϕ : H →* A) (S : H.LeftTransversal) {x : G} (hx : x ∈ H)
    (hS : ∀ s ∈ (S : Set G), x⁻¹ * s * x ∈ (S : Set G)) :
    MonoidHom.transfer ϕ x = ϕ ⟨x, hx⟩ ^ H.index := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  -- The chosen representative of `x⁻¹ • q` is the `x`-conjugate of that of `q`.
  have hrep : ∀ q : G ⧸ H,
      (S.2.leftQuotientEquiv (x⁻¹ • q) : G)
        = x⁻¹ * (S.2.leftQuotientEquiv q : G) * x := by
    intro q
    set s : G := (S.2.leftQuotientEquiv q : G) with hs
    have hsS : s ∈ (S : Set G) := (S.2.leftQuotientEquiv q).2
    have hmem : x⁻¹ * s * x ∈ (S : Set G) := hS s hsS
    have hq : (s : G ⧸ H) = q := by
      rw [hs]; exact S.2.quotientGroupMk_leftQuotientEquiv q
    have hcoset : ((x⁻¹ * s * x : G) : G ⧸ H) = x⁻¹ • q := by
      rw [← hq, Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      have hcalc : (x⁻¹ * s * x)⁻¹ * (x⁻¹ * s) = x⁻¹ := by group
      rw [hcalc]; exact H.inv_mem hx
    rw [← hcoset, leftQuotientEquiv_coe_eq_of_mem S hmem]
  -- Every factor of the transfer product equals `x`.
  have hfactor : ∀ q : G ⧸ H,
      (S.2.leftQuotientEquiv q : G)⁻¹ * ((x • S).2.leftQuotientEquiv q : G) = x := by
    intro q
    rw [smul_apply_eq_smul_apply_inv_smul x S q, smul_eq_mul, hrep q]
    group
  rw [MonoidHom.transfer_def ϕ S]
  have hprod : Subgroup.leftTransversals.diff ϕ S (x • S) = ∏ _q : G ⧸ H, ϕ ⟨x, hx⟩ := by
    unfold Subgroup.leftTransversals.diff
    simp only
    exact Finset.prod_congr rfl (fun q _ => congrArg ϕ (Subtype.ext (hfactor q)))
  rw [hprod, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index_eq_card]

/-- **Transfer over a conjugation-invariant right transversal.** If a *right*
transversal `T` of `H ≤ G` (`IsComplement ↑H T`) is invariant under conjugation by
`x ∈ H`, then `transfer ϕ x = ϕ ⟨x, hx⟩ ^ H.index`.  (Its pointwise inverse `T⁻¹` is
the conjugation-invariant left transversal fed to
`transfer_eq_pow_of_conj_invariant_transversal`.) -/
theorem transfer_eq_pow_of_conj_invariant_rightTransversal [H.FiniteIndex]
    (ϕ : H →* A) {T : Set G} (hT : IsComplement (H : Set G) T) {x : G} (hx : x ∈ H)
    (hTconj : ∀ r ∈ T, x⁻¹ * r * x ∈ T) :
    MonoidHom.transfer ϕ x = ϕ ⟨x, hx⟩ ^ H.index := by
  refine transfer_eq_pow_of_conj_invariant_transversal ϕ
    ⟨T⁻¹, isComplement_inv_of_isComplement hT⟩ hx ?_
  intro s hs
  rw [Set.mem_inv] at hs ⊢
  have hinv : (x⁻¹ * s * x)⁻¹ = x⁻¹ * s⁻¹ * x := by group
  rw [hinv]
  exact hTconj s⁻¹ hs

end OddOrder.GroupTheory
