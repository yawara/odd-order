/-
# Peterfalvi §7 — discharging the `(7.7.a)`/`(7.8.c)` certificates of `S09`

`S09_NonexistenceCertain.lean` carries Peterfalvi's `(7.7.a)` (`Hypothesis76.chiRho_decomp`) and
`(7.8.c.i)` (`Hypothesis78.chiRho_eq_inner_beta`) as structural certificate fields: deriving them
needs the `CF(L,A)`-basis argument of Peterfalvi (7.7), whose foundation is the **spanning
identity** formalized here.

This file lives outside `S09` (which is concurrently edited for the `(7.11)` assembly) to avoid
conflicts; it imports the `S09` machinery and supplies standalone lemmas toward the certificate
discharge (issue 1013).
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

namespace OddOrder.Peterfalvi.S09.Cert

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L]

/-- **Peterfalvi (7.7.a), the spanning identity.**  For a *normal* subgroup `K ◁ L` and a class
function `ψ` on `L` supported inside `K` (vanishing off `K`),
`Ind_K^L Res_K^L ψ = [L : K] · ψ`.

This is the key step in Peterfalvi's proof that `CF(L, A)` (with `A = K^#`) is spanned by the
family `{Ind_K^L θ}`: since `ψ = (1/e) Ind_K^L Res_K^L ψ` lies in the span of the induced
characters, the basis argument of (7.7.a) applies.

Proof.  Pointwise.  For `y ∈ K`, normality makes every conjugate `x⁻¹ y x ∈ K`, so each induction
summand is `ψ(x⁻¹ y x) = ψ(y)` (class function); the `|L|` summands divided by `|K|` give
`[L:K]·ψ(y)`.  For `y ∉ K`, no conjugate lies in `K`, so the induction vanishes — as does `ψ(y)`. -/
theorem induce_restrict_eq_index_smul (K : Subgroup L) [hK : K.Normal]
    [Invertible (Nat.card ↥K : ℂ)] (ψ : ClassFunction L ℂ)
    (hψ : ∀ y : L, y ∉ K → ψ y = 0) :
    ClassFunction.induce K (ClassFunction.restrict K ψ) = (K.index : ℂ) • ψ := by
  classical
  ext y
  rw [ClassFunction.induce_apply, ClassFunction.smul_apply]
  by_cases hy : y ∈ K
  · -- Every induction summand equals `ψ y`.
    have hterm : ∀ x : L, ClassFunction.induceTerm K (ClassFunction.restrict K ψ) x y = ψ y := by
      intro x
      have hxy : x⁻¹ * y * x ∈ K := by simpa using hK.conj_mem y hy x⁻¹
      rw [ClassFunction.induceTerm_of_mem _ hxy, ClassFunction.restrict_apply]
      simpa using ψ.conj_eq y x⁻¹
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    have hcard : (Nat.card L : ℂ) = (K.index : ℂ) * (Nat.card ↥K : ℂ) := by
      rw [← Nat.cast_mul, K.index_mul_card]
    rw [hcard,
      show ⅟(Nat.card ↥K : ℂ) * ((K.index : ℂ) * (Nat.card ↥K : ℂ) * ψ y)
        = (K.index : ℂ) * (⅟(Nat.card ↥K : ℂ) * (Nat.card ↥K : ℂ)) * ψ y from by ring,
      invOf_mul_self, mul_one]
  · -- `y ∉ K`: every summand vanishes (no conjugate lands in `K`), and `ψ y = 0`.
    have hterm : ∀ x : L, ClassFunction.induceTerm K (ClassFunction.restrict K ψ) x y = 0 := by
      intro x
      apply ClassFunction.induceTerm_of_not_mem
      intro hmem
      apply hy
      have hconj := hK.conj_mem (x⁻¹ * y * x) hmem x
      have he : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rwa [he] at hconj
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const_zero, mul_zero,
      hψ y hy, mul_zero]

/-- **Peterfalvi (7.7.a), `CF(L,A)` is induced from `K`.**  A class function `ψ` on `L` supported
inside a normal subgroup `K` (i.e. `ψ ∈ CF(L, K^#)`) is the induction of a class function on `K`,
namely `ψ = Ind_K^L ((1/[L:K]) · Res_K^L ψ)`.  Immediate from the spanning identity
`induce_restrict_eq_index_smul` and linearity of induction (`induce_smul`).

This realizes the membership `CF(L,A) ⊆ Ind_K^L(CF(K)) = ⟨Ind_K^L θ⟩_ℂ` that underlies Peterfalvi's
basis argument: every `ψ ∈ CF(L,A)` lies in the `ℂ`-span of the family `T = {Ind_K^L θ}`. -/
theorem eq_induce_restrict_of_supported (K : Subgroup L) [K.Normal]
    [Invertible (Nat.card ↥K : ℂ)] (ψ : ClassFunction L ℂ)
    (hψ : ∀ y : L, y ∉ K → ψ y = 0) :
    ψ = ClassFunction.induce K ((K.index : ℂ)⁻¹ • ClassFunction.restrict K ψ) := by
  rw [ClassFunction.induce_smul, induce_restrict_eq_index_smul K ψ hψ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite), one_smul]

end OddOrder.Peterfalvi.S09.Cert
