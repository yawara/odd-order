/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_HypothesisB

/-!
# BG Appendix C: basic facts about `H = P ⋊ U` and its prime-field line

Elementary `(p, q)`-level facts about the Frobenius group `H = P ⋊ U` of BG Appendix C and its
prime-field line `P₀`, used throughout the Lemma C.1--C.3 development.

These were previously stated only through the Peterfalvi Section 16 hypothesis (as
`fieldNormalizer*` lemmas); nothing in them depends on that configuration, so they belong here
with the rest of the `(p, q)`-level Appendix C material (issue 0151).
-/

namespace OddOrder.BG.AppC

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and the
norm-one complement meet trivially. -/
theorem normOneFrobeniusKernel_inf_complement_eq_bot (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneFrobeniusKernel p q ⊓ NormSet.normOneFrobeniusComplement p q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  rcases hx.1 with ⟨a, rfl⟩
  rcases hx.2 with ⟨u, hu⟩
  have ha : a = 1 := by
    have hleft := congrArg
      (fun g : NormSet.normOneFrobeniusGroup p q => g.left) hu
    simpa using hleft.symm
  subst a
  simp

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and
norm-one complement generate the whole group. -/
theorem normOneFrobeniusKernel_sup_complement_eq_top (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneFrobeniusKernel p q ⊔ NormSet.normOneFrobeniusComplement p q = ⊤ := by
  apply le_antisymm le_top
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact Subgroup.mul_mem_sup ⟨g.left, rfl⟩ ⟨g.right, rfl⟩

/-- Prime-line scalar elements lie in the concrete subgroup `P₀`. -/
theorem primeLineElement_mem (p q : ℕ) [Fact p.Prime]
    (c : ZMod p) :
    primeLineElement p q c ∈ primeLine p q := by
  dsimp [primeLineElement, primeLine, OddOrder.BG.AppC.primeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  have h1 : (1 : GaloisField p q) ∈
      Submodule.span (ZMod p)
        ({(1 : GaloisField p q)} :
          Set (GaloisField p q)) :=
    Submodule.subset_span (by simp)
  simpa [Algebra.smul_def] using
    (Submodule.smul_mem
      (Submodule.span (ZMod p)
        ({(1 : GaloisField p q)} :
          Set (GaloisField p q))) c h1)

/-- Prime-line scalar elements invert by negating the scalar. -/
theorem primeLineElement_neg (p q : ℕ) [Fact p.Prime]
    (c : ZMod p) :
    primeLineElement p q (-c) =
      (primeLineElement p q c)⁻¹ := by
  simp [primeLineElement]

/-- The distinguished generator lies in the concrete prime-field line `P₀`. -/
theorem primeLineGenerator_mem (p q : ℕ) [Fact p.Prime] :
    primeLineGenerator p q ∈ primeLine p q := by
  dsimp [primeLineGenerator, primeLine, OddOrder.BG.AppC.primeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  exact Submodule.subset_span (by simp)

/-- The distinguished generator of `P₀` is nontrivial. -/
theorem primeLineGenerator_ne_one (p q : ℕ) [Fact p.Prime] :
    primeLineGenerator p q ≠ 1 := by
  intro h
  have hfield : (1 : GaloisField p q) = 0 :=
    ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h)
  exact one_ne_zero hfield

/-- The distinguished generator of `P₀` has order dividing `p`. -/
theorem primeLineGenerator_pow_p (p q : ℕ) [Fact p.Prime] :
    (primeLineGenerator p q) ^ p = 1 := by
  haveI : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q)
      p]
    exact ZMod.charP p
  dsimp [primeLineGenerator]
  let inlHom :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup p q →*
        NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_nsmul]
  congr
  simp

/-- There is a nonidentity norm-one unit, provided `q > 1`. -/
theorem exists_normOneUnit_ne_one (p q : ℕ) [Fact p.Prime] (hq : 1 < q) :
    ∃ u : NormSet.normOneUnits p q, u ≠ 1 := by
  haveI : Nontrivial (NormSet.normOneUnits p q) :=
    Finite.one_lt_card_iff_nontrivial.mp (NormSet.normOneUnits_card_gt_one p q hq)
  exact exists_ne 1

/-- The concrete `p`-power Frobenius on the additive kernel of BG's model
`P ⋊ U`, written multiplicatively via `Multiplicative`. -/
noncomputable def additiveFrobeniusHom (p q : ℕ) [Fact p.Prime] :
    NormSet.additiveFieldGroup p q →* NormSet.additiveFieldGroup p q where
  toFun x := Multiplicative.ofAdd (x.toAdd ^ p)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [(Fact.out : Nat.Prime p).ne_zero]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact (OddOrder.BG.AppC.NormSet.add_pow_p
      p q x.toAdd y.toAdd).symm

/-- The concrete `p`-power Frobenius on the norm-one complement. -/
noncomputable def normOneUnitsFrobeniusHom (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneUnits p q →* NormSet.normOneUnits p q where
  toFun u := u ^ p
  map_one' := by simp
  map_mul' u v := by
    rw [mul_pow]

/-- The concrete `p`-power Frobenius of BG's semidirect product
`P ⋊ U`: it sends `(x,u)` to `(x^p,u^p)`. -/
noncomputable def frobeniusHom (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneFrobeniusGroup p q →* NormSet.normOneFrobeniusGroup p q :=
  SemidirectProduct.map
    (additiveFrobeniusHom p q)
    (normOneUnitsFrobeniusHom p q)
    (by
      intro u
      ext x
      apply Multiplicative.toAdd.injective
      change (((u : (GaloisField p q)ˣ) :
              GaloisField p q) * x) ^ p =
            (((u ^ p : NormSet.normOneUnits p q) :
                  (GaloisField p q)ˣ) :
                GaloisField p q) * x ^ p
      simpa [map_pow] using
        (mul_pow (((u : (GaloisField p q)ˣ) :
          GaloisField p q)) x p))

@[simp]
theorem frobeniusHom_inl (p q : ℕ) [Fact p.Prime]
    (x : NormSet.additiveFieldGroup p q) :
    frobeniusHom p q (SemidirectProduct.inl x) =
      SemidirectProduct.inl (Multiplicative.ofAdd (x.toAdd ^ p)) := by
  simp [frobeniusHom, additiveFrobeniusHom]

@[simp]
theorem frobeniusHom_inr (p q : ℕ) [Fact p.Prime]
    (u : NormSet.normOneUnits p q) :
    frobeniusHom p q
        (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) =
      SemidirectProduct.inr (u ^ p) := by
  simp [frobeniusHom, normOneUnitsFrobeniusHom]

end OddOrder.BG.AppC
