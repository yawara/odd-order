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
open scoped Classical

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

/-- **Positive-definiteness of Peterfalvi's class-function inner product.**  Over `ℂ`,
`⟨η, η⟩ = 0` forces `η = 0`.  Indeed `⟨η, η⟩ = |G|⁻¹ Σ_g |η(g)|²`, a sum of non-negative reals, so
it vanishes only when every `η(g) = 0`.  This is the non-degeneracy used in Peterfalvi's (7.7.a)
basis argument: a class function in `CF(L,A)` orthogonal to a spanning set is zero. -/
theorem inner_self_eq_zero [Invertible (Nat.card L : ℂ)] {η : ClassFunction L ℂ}
    (h : ClassFunction.inner η η = 0) :
    η = 0 := by
  have hsum : ClassFunction.innerSum η η = 0 := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum] at h
    have := congrArg (fun z => (Nat.card L : ℂ) * z) h
    simpa [← mul_assoc, mul_invOf_self] using this
  have hreal : (∑ g : L, Complex.normSq (η g)) = 0 := by
    have hcast : (∑ g : L, η g * star (η g)) = ((∑ g : L, Complex.normSq (η g) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun g _ => Complex.mul_conj (η g)
    have : ((∑ g : L, Complex.normSq (η g) : ℝ) : ℂ) = 0 := by
      rw [← hcast]; exact hsum
    exact_mod_cast this
  have hzero : ∀ g : L, Complex.normSq (η g) = 0 :=
    fun g => (Finset.sum_eq_zero_iff_of_nonneg fun g _ => Complex.normSq_nonneg _).mp hreal g
      (Finset.mem_univ g)
  ext g
  simpa using Complex.normSq_eq_zero.mp (hzero g)

/-- **Peterfalvi (7.7.a), the uniqueness principle.**  If `η` lies in the `ℂ`-span of a set `S` of
class functions and is orthogonal to every member of `S`, then `η = 0`.  This is the
non-degeneracy of the inner product on a spanned subspace: the linear functional `⟨·, η⟩` vanishes
on `S`, hence on `span S ∋ η`, giving `⟨η, η⟩ = 0` and `η = 0` by `inner_self_eq_zero`.

In (7.7.a), `S = {ψ_i}` spans `CF(L,A)`, so a class function in `CF(L,A)` is determined by its inner
products against the `ψ_i` — the determination of `χ^ρ` on `A`. -/
theorem eq_zero_of_mem_span_orthogonal [Invertible (Nat.card L : ℂ)]
    {S : Set (ClassFunction L ℂ)} {η : ClassFunction L ℂ}
    (hη : η ∈ Submodule.span ℂ S) (horth : ∀ v ∈ S, ClassFunction.inner v η = 0) :
    η = 0 := by
  have key : ∀ φ ∈ Submodule.span ℂ S, ClassFunction.inner φ η = 0 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem v hv => exact horth v hv
    | zero => exact ClassFunction.inner_zero_left η
    | add x y _ _ ihx ihy => rw [ClassFunction.inner_add_left, ihx, ihy, add_zero]
    | smul c x _ ih => rw [ClassFunction.inner_smul_left, ih, mul_zero]
  exact inner_self_eq_zero (key η hη)

/-- **The supported projection** `η ↦ η · 𝟙_A` of a class function onto `CF(L, A)`.  When `A` is a
conjugation-invariant set, the pointwise product with the indicator of `A` is again a class
function (the indicator and `η` are both conjugation-invariant).  This is the projection used in
Peterfalvi's (7.7.a) basis argument to compare `χ^ρ` (already supported on `A`) with the candidate
linear combination `Σ c̄_i/‖ζ_i‖² ζ_i` (whose `A`-part is what (7.7.a) computes). -/
noncomputable def supportedProj (A : Set L) (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A)
    (η : ClassFunction L ℂ) : ClassFunction L ℂ :=
  ⟨fun x => if x ∈ A then η x else 0, fun g h => by
    by_cases hg : g ∈ A
    · simp only [if_pos hg, if_pos ((hA g h).mpr hg), η.conj_eq g h]
    · simp only [if_neg hg, if_neg (fun hc => hg ((hA g h).mp hc))]⟩

@[simp] theorem supportedProj_apply (A : Set L) (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A)
    (η : ClassFunction L ℂ) (x : L) :
    supportedProj A hA η x = if x ∈ A then η x else 0 := rfl

/-- The supported projection is supported on `A` (lies in `CF(L,A)`). -/
theorem supportedProj_mem_supported (A : Set L) (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A)
    (η : ClassFunction L ℂ) :
    supportedProj A hA η ∈ ClassFunction.supportedSubmodule A := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro x hx
  by_contra hxA
  apply hx
  show supportedProj A hA η x = 0
  simp only [supportedProj_apply, if_neg hxA]

/-- **The supported projection preserves inner products against `CF(L,A)`.**  For `ψ` supported on
`A`, `⟨ψ, η · 𝟙_A⟩ = ⟨ψ, η⟩`: off `A` the factor `ψ(x)` already vanishes, so multiplying `η` by the
indicator of `A` changes nothing. -/
theorem inner_supportedProj [Invertible (Nat.card L : ℂ)] (A : Set L)
    (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A) {ψ : ClassFunction L ℂ}
    (hψ : ψ ∈ ClassFunction.supportedSubmodule A) (η : ClassFunction L ℂ) :
    ClassFunction.inner ψ (supportedProj A hA η) = ClassFunction.inner ψ η := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum]
  congr 1
  simp only [ClassFunction.innerSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ A
  · rw [supportedProj_apply, if_pos hx]
  · have hψx : ψ x = 0 := by
      by_contra h0
      exact hx ((ClassFunction.mem_supportedSubmodule.mp hψ) (ClassFunction.mem_support.mpr h0))
    rw [hψx, zero_mul, zero_mul]

/-- **Peterfalvi (7.7.a), the determination step.**  If a set `S` of class functions spans `CF(L,A)`
(`hspan`) and consists of `A`-supported functions (`hS_supp`), then a class function `η` orthogonal
to every member of `S` vanishes on `A`.  Apply the uniqueness principle to the supported projection
`η · 𝟙_A ∈ CF(L,A) = span S`, which is orthogonal to `S` (`inner_supportedProj`), hence zero.

This is the heart of (7.7.a): `χ^ρ − Σ c̄_i/‖ζ_i‖² ζ_i` is orthogonal to the spanning `{ψ_i}` (the
inner products are the `c_i`), so it vanishes on `A` — pinning down `χ^ρ` there. -/
theorem eq_zero_on_A_of_inner_zero [Invertible (Nat.card L : ℂ)] (A : Set L)
    (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A) {S : Set (ClassFunction L ℂ)}
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ S)
    (hS_supp : ∀ v ∈ S, v ∈ ClassFunction.supportedSubmodule A)
    {η : ClassFunction L ℂ} (horth : ∀ v ∈ S, ClassFunction.inner v η = 0)
    {x : L} (hx : x ∈ A) :
    η x = 0 := by
  have hproj_zero : supportedProj A hA η = 0 :=
    eq_zero_of_mem_span_orthogonal (hspan (supportedProj_mem_supported A hA η))
      (fun v hv => by rw [inner_supportedProj A hA (hS_supp v hv) η]; exact horth v hv)
  have h0 : supportedProj A hA η x = 0 := by rw [hproj_zero]; rfl
  rwa [supportedProj_apply, if_pos hx] at h0

/-- **Peterfalvi (7.7.a), the Gram entry.**  For a pairwise-orthogonal family `ζ : Fin (n+1) → CF(L)`
and the difference vectors `ψ_j = ζ_j − d_j ζ_0` (`j ≥ 1`), the inner product `⟨ψ_j, ζ_i⟩` (`i ≥ 1`)
is the diagonal entry `‖ζ_j‖²` when `i = j` and `0` otherwise: the `ζ_0` term drops out (`0 ≠ i`) and
the `ζ_j`-term is the orthonormality indicator.  This is the Gram matrix that pins the coefficients
of the (7.7.a) decomposition. -/
theorem inner_psi_zeta [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    {i j : Fin (n + 1)} (hi : i ≠ 0) :
    ClassFunction.inner (ζ j - d j • ζ 0) (ζ i) =
      if i = j then ClassFunction.inner (ζ j) (ζ j) else 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    horth 0 i (Ne.symm hi), mul_zero, sub_zero]
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij, horth j i (fun h => hij h.symm)]

end OddOrder.Peterfalvi.S09.Cert
