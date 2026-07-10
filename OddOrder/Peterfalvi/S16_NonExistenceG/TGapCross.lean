import OddOrder.Peterfalvi.S16_NonExistenceG.TGapDelta
import OddOrder.Peterfalvi.S16_GridExpansion

/-!
# Peterfalvi (14.9): assembly of the S/T gap identity

This file isolates the linear-algebraic end of the identity
`⟨Γ, τ₁ζ⟩ = 1 + ⟨Δ, Γ⟩`, where
`Γ = τ_S β_S - 1_G + η₀₁` and `Δ = τ_T β_T - 1_G + τ₁ζ`.
Once the two genuine cross-side inputs
`⟨τ_T β_T, τ_S β_S⟩ = 0` and `⟨τ_T β_T, η₀₁⟩ = 0` are known,
the claimed equality follows formally.  The only subtlety is that the
class-function inner product is Hermitian; integrality makes it symmetric
on virtual characters.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]
open scoped BigOperators

/-- The inner product of two virtual characters is symmetric: its value is
an integer, hence fixed by complex conjugation. -/
theorem inner_eq_swap_of_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {φ ψ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hψ : ψ ∈ ZIrr G) :
    ClassFunction.inner φ ψ = ClassFunction.inner ψ φ := by
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφ hψ
  calc
    ClassFunction.inner φ ψ = (m : ℂ) := hm
    _ = star (m : ℂ) := by rw [star_intCast]
    _ = star (ClassFunction.inner φ ψ) := by rw [hm]
    _ = ClassFunction.inner ψ φ :=
      (OddOrder.RepresentationTheory.inner_conj_symm φ ψ).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)/(14.9), projection-to-row reduction.**

Let `b` be the T-side Dade image of `β_{T,0}`.  The output of the
`FTtype34_structure` projection calculation is that every `η_{0j}`
has the same inner product with `b` as with the zero-column sum
`∑ᵢ η_{i0}`.  Orthonormality of the η-grid then gives
`⟨b,η_{0j}⟩ = [j=0]`.

This theorem is the fully formal linear-algebraic passage from the deep
(11.9) projection statement to Coq's `o_eta0_betaT0`; the remaining
character-theoretic input is now exactly `hproj`. -/
theorem tSide_beta_inner_eta_of_zeroColumn_projection [Finite G]
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (b : ClassFunction G ℂ)
    (hproj : ∀ j : Fin base.p,
      ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
        ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j)
          (∑ i : Fin base.q,
            base.eta i ⟨0, base.p_prime.pos⟩))
    (j : Fin base.p) :
    ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j) =
      if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hsum : ClassFunction.inner
      (base.eta ⟨0, base.q_prime.pos⟩ j)
      (∑ i : Fin base.q, base.eta i ⟨0, base.p_prime.pos⟩) =
        if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    by_cases hj : j = ⟨0, base.p_prime.pos⟩
    · subst j
      rw [Finset.sum_eq_single_of_mem (⟨0, base.q_prime.pos⟩ : Fin base.q)
        (Finset.mem_univ _) (fun i _ hi => by
          rw [eta_orthonormal, if_neg]
          rintro ⟨h, -⟩
          exact hi h.symm)]
      rw [eta_orthonormal, if_pos ⟨rfl, rfl⟩]
      simp
    · simp only [if_neg hj]
      apply Finset.sum_eq_zero
      intro i _
      rw [eta_orthonormal, if_neg]
      exact fun h => hj h.2
  calc
    ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j) =
        star (ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b) :=
      OddOrder.RepresentationTheory.inner_conj_symm _ _
    _ = star (if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) := by rw [hproj j, hsum]
    _ = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by split <;> simp

/-- **Peterfalvi (14.9), S/T gap assembly.**

Expand `Γ = σβ - 1 + η` and `Δ = τβ - 1 + a`.  Cross-Dade
orthogonality and the T-side β–η row give `⟨τβ, Γ⟩ = -1`;
principal orthogonality of `Γ` kills the trivial term.  Integrality of
the remaining virtual-character pairings removes the Hermitian
conjugations and yields `⟨Γ,a⟩ = 1 + ⟨Δ,Γ⟩`. -/
theorem gap_cross_inner_identity [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {Γ Δ τβ σβ η a one : ClassFunction G ℂ}
    (hΓZ : Γ ∈ ZIrr G) (haZ : a ∈ ZIrr G) (honeZ : one ∈ ZIrr G)
    (hΓ : Γ = σβ - one + η)
    (hΔ : Δ = τβ - one + a)
    (hτβ_one : ClassFunction.inner τβ one = 1)
    (hτβ_σβ : ClassFunction.inner τβ σβ = 0)
    (hτβ_eta : ClassFunction.inner τβ η = 0)
    (hΓ_one : ClassFunction.inner Γ one = 0) :
    ClassFunction.inner Γ a = 1 + ClassFunction.inner Δ Γ := by
  have hτβΓ : ClassFunction.inner τβ Γ = -1 := by
    rw [hΓ, ClassFunction.inner_add_right, ClassFunction.inner_sub_right,
      hτβ_σβ, hτβ_one, hτβ_eta]
    norm_num
  have honeΓ : ClassFunction.inner one Γ = 0 := by
    rw [inner_eq_swap_of_mem_ZIrr honeZ hΓZ, hΓ_one]
  have haΓ : ClassFunction.inner a Γ = ClassFunction.inner Γ a :=
    inner_eq_swap_of_mem_ZIrr haZ hΓZ
  rw [hΔ, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    hτβΓ, honeΓ, haΓ]
  ring

end OddOrder.Peterfalvi.S16
