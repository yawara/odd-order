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

end OddOrder.BG.AppC
