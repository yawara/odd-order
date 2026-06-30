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
import OddOrder.Peterfalvi.S09_NonexistenceCertain

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

/-- **The induced characters span the image of induction** (Peterfalvi (7.7.a) spanning, image
half).  Every induced class function `Ind_K^L φ` lies in the `ℂ`-span of the induced *irreducible*
characters `{Ind_K^L θ : θ ∈ Irr K}`.  Expand `φ` in the irreducible basis of `CF(K)`
(`span_irreducibleCharacter_eq_top`) and push through the linearity of induction
(`induce_add`/`induce_smul`/`induce_zero`) by `Submodule.span_induction`. -/
theorem induce_mem_span_induce_irr (K : Subgroup L) [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (φ : ClassFunction ↥K ℂ) :
    ClassFunction.induce K φ ∈ Submodule.span ℂ
      (Set.range (fun θ : IrreducibleCharacter ↥K =>
        ClassFunction.induce K (θ : ClassFunction ↥K ℂ))) := by
  classical
  haveI : Finite ↥K := Finite.of_fintype _
  have hφ : φ ∈ Submodule.span ℂ
      (Set.range (fun θ : IrreducibleCharacter ↥K => (θ : ClassFunction ↥K ℂ))) := by
    rw [span_irreducibleCharacter_eq_top]; exact Submodule.mem_top
  induction hφ using Submodule.span_induction with
  | mem v hv => obtain ⟨θ, rfl⟩ := hv; exact Submodule.subset_span ⟨θ, rfl⟩
  | zero => rw [ClassFunction.induce_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [ClassFunction.induce_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih => rw [ClassFunction.induce_smul]; exact Submodule.smul_mem _ c ih

/-- **`CF(L,A)` lies in the span of the induced irreducibles** (Peterfalvi (7.7.a) spanning).  A
class function `ψ` supported inside the normal subgroup `K` lies in the `ℂ`-span of the family
`{Ind_K^L θ : θ ∈ Irr K}`: combine `eq_induce_restrict_of_supported` (`ψ = Ind_K^L(e⁻¹ Res ψ)`,
so `ψ ∈ Ind_K^L(CF K)`) with `induce_mem_span_induce_irr`.  This is the spanning input that, after
the degree-`0` reduction (`mem_span_psi_of_apply_one_zero`), supplies the `hspan` hypothesis of
`chiRho_decomp_proof`. -/
theorem supported_mem_span_induce_irr (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] (ψ : ClassFunction L ℂ)
    (hψ : ∀ y : L, y ∉ K → ψ y = 0) :
    ψ ∈ Submodule.span ℂ
      (Set.range (fun θ : IrreducibleCharacter ↥K =>
        ClassFunction.induce K (θ : ClassFunction ↥K ℂ))) := by
  rw [eq_induce_restrict_of_supported K ψ hψ]
  exact induce_mem_span_induce_irr K _

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

/-- **The inner product only sees the second factor on the support of the first.**  If `ψ` and `ψ'`
agree wherever `α` is nonzero, then `⟨α, ψ⟩ = ⟨α, ψ'⟩`.  Used in (7.8.a)/(7.8.c) where a class
function supported on `A` is paired against `(1_G)^ρ`, which equals `1_L` on `A`. -/
theorem inner_eq_of_eqOn_support [Invertible (Nat.card L : ℂ)] {α ψ ψ' : ClassFunction L ℂ}
    (h : ∀ g : L, α g ≠ 0 → ψ g = ψ' g) :
    ClassFunction.inner α ψ = ClassFunction.inner α ψ' := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum, ClassFunction.innerSum]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  by_cases hg : α g = 0
  · rw [hg, zero_mul, zero_mul]
  · rw [h g hg]

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

/-- **Peterfalvi (7.7.a), the Gram sum.**  For a pairwise-orthogonal family `ζ` and `j ≥ 1`, pairing
`ψ_j = ζ_j − d_j ζ_0` against any linear combination `Σ_{i ≥ 1} b_i ζ_i` picks out the diagonal:
`⟨ψ_j, Σ_{i≥1} b_i ζ_i⟩ = star(b_j) ‖ζ_j‖²`.  Immediate from the Gram entry `inner_psi_zeta` and
`Finset.sum_eq_single`.  In (7.7.a) the candidate is `Σ_{i≥1} (c̄_i/‖ζ_i‖²) ζ_i`, so this equals `c_j`
(after `star (c̄_j/‖ζ_j‖²)·‖ζ_j‖² = c_j`, using `‖ζ_j‖²` real). -/
theorem inner_psi_candidate [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (b : Fin (n + 1) → ℂ) {j : Fin (n + 1)} (hj : j ≠ 0) :
    ClassFunction.inner (ζ j - d j • ζ 0)
        (∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), b i • ζ i) =
      star (b j) * ClassFunction.inner (ζ j) (ζ j) := by
  rw [inner_sum_right, Finset.sum_eq_single j
    (fun i hi hij => by
      rw [ClassFunction.inner_smul_right, inner_psi_zeta ζ d horth (Finset.mem_Ioi.mp hi).ne',
        if_neg hij, mul_zero])
    (fun hj_notin => absurd (Finset.mem_Ioi.mpr (Fin.pos_of_ne_zero hj)) hj_notin)]
  rw [ClassFunction.inner_smul_right, inner_psi_zeta ζ d horth hj, if_pos rfl]

/-- **Peterfalvi (7.7.a), the candidate-coefficient identity.**  With the (7.7.a) coefficients
`b_i = star(c_i)/‖ζ_i‖²`, the pairing of `ψ_j` against the candidate `Σ_{i≥1} b_i ζ_i` recovers
`c_j` exactly: `star(b_j)·‖ζ_j‖² = (c_j/‖ζ_j‖²)·‖ζ_j‖² = c_j` (using `‖ζ_j‖²` real and nonzero).
This is the consistency that makes `Σ c̄_i/‖ζ_i‖² ζ_i` the decomposition of `χ^ρ`. -/
theorem inner_psi_candidate_eq [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (c : Fin (n + 1) → ℂ) (hnorm : ∀ i : Fin (n + 1), ClassFunction.inner (ζ i) (ζ i) ≠ 0)
    {j : Fin (n + 1)} (hj : j ≠ 0) :
    ClassFunction.inner (ζ j - d j • ζ 0)
        (∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
          (star (c i) / ClassFunction.inner (ζ i) (ζ i)) • ζ i) = c j := by
  rw [inner_psi_candidate ζ d horth (fun i => star (c i) / ClassFunction.inner (ζ i) (ζ i)) hj,
    div_eq_mul_inv, star_mul, star_star, star_inv₀,
    OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.star_inner_self,
    mul_right_comm, inv_mul_cancel₀ (hnorm j), one_mul]

open OddOrder.Peterfalvi.S09 in
/-- **Peterfalvi (7.7.a), the decomposition.**  Given the §7 `ρ`-machinery (`Hypothesis71`), a
pairwise-orthogonal family `ζ` of class functions with nonzero norms whose difference vectors
`ψ_i = ζ_i − d_i ζ_0` are `A`-supported and span `CF(L, A)`, the `ρ`-image of any `χ` decomposes on
`A` as `χ^ρ(x) = Σ_{i≥1} c̄_i/‖ζ_i‖² · ζ_i(x)`, where `c_i = ⟨ψ_i^τ, χ⟩`.

This **discharges the `Hypothesis76.chiRho_decomp` certificate** of Peterfalvi (7.7.a) (issue 1013):
the candidate `Σ c̄_i/‖ζ_i‖² ζ_i` and `χ^ρ` have the same inner products `c_j` against the spanning
`{ψ_j}` (`chiRho_adjoint` on one side, `inner_psi_candidate_eq` on the other), so their difference is
orthogonal to a spanning set of `CF(L,A)` and hence vanishes on `A` (`eq_zero_on_A_of_inner_zero`). -/
theorem chiRho_decomp_proof {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (hnorm : ∀ i : Fin (n + 1), ClassFunction.inner (ζ i) (ζ i) ≠ 0)
    (hAconj : ∀ g h : L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hspan : ClassFunction.supportedSubmodule (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ≤
      Submodule.span ℂ ((fun j => ζ j - d j • ζ 0) '' {j : Fin (n + 1) | j ≠ 0}))
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (ClassFunction.inner (H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩) χ) /
          ClassFunction.inner (ζ i) (ζ i)) * ζ i x := by
  set A' := OddOrder.Peterfalvi.S04.supportInSubgroup A L with hA'
  set c : Fin (n + 1) → ℂ :=
    fun i => ClassFunction.inner (H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩) χ with hc
  set cand : ClassFunction L ℂ :=
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
      (star (c i) / ClassFunction.inner (ζ i) (ζ i)) • ζ i with hcand
  -- `η = χ^ρ − cand` is orthogonal to every `ψ_j` and lies in `CF(L,A) = span {ψ_j}`, so it
  -- vanishes on `A`.
  have hηA : (H71.chiRhoCF χ - cand) x = 0 := by
    apply eq_zero_on_A_of_inner_zero A' hAconj hspan
    · rintro v ⟨j, _, rfl⟩
      rw [ClassFunction.mem_supportedSubmodule]
      exact psi_support j
    · rintro v ⟨j, hj, rfl⟩
      rw [ClassFunction.inner_sub_right,
        show ClassFunction.inner (ζ j - d j • ζ 0) (H71.chiRhoCF χ) = c j from
          (H71.chiRho_adjoint ⟨ζ j - d j • ζ 0, psi_support j⟩ χ).symm,
        inner_psi_candidate_eq ζ d horth c hnorm hj, sub_self]
    · rw [hA', OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hx
  -- conclude `χ^ρ x = cand x`, then evaluate the sum.
  have hval : H71.chiRho χ x = cand x := by
    have := hηA
    rw [ClassFunction.sub_apply, H71.chiRhoCF_apply] at this
    exact sub_eq_zero.mp this
  rw [hval, hcand, ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [ClassFunction.smul_apply]

/-- **Induced irreducible characters have nonzero norm.**  `‖Ind_K^L θ‖² ≠ 0`, since
`|K|·‖Ind θ‖² = |I_L(θ)| > 0` (`card_mul_inner_self_induce_eq_card_inertia`).  Supplies the
`hnorm` hypothesis of `chiRho_decomp_proof` for the family `ζ_i = Ind θ_i` of (7.6)/(7.7.a). -/
theorem induce_norm_ne_zero (K : Subgroup L) [K.Normal] [Fintype ↥K] [Invertible (Nat.card L : ℂ)]
    [Invertible (Nat.card ↥K : ℂ)] (θ : IrreducibleCharacter ↥K) :
    ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)) ≠ 0 := by
  intro h0
  have hkey := card_mul_inner_self_induce_eq_card_inertia (G := L) θ
  rw [h0, mul_zero] at hkey
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') hkey.symm

/-- **An induced irreducible character is nonzero at `1`.**  `Ind_K^L θ (1) = [L:K] · θ(1)`
(`induce_apply_one`), and both factors are nonzero: `[L:K] ≠ 0` (finite index) and `θ(1)` is the
positive natural number `dim θ` (`irreducibleCharacter_apply_one_eq_pos_natCast`).  This supplies
`ζ_0(1) ≠ 0` (`hz0`), hence the well-definedness of the degree ratios `d_i = ζ_i(1)/ζ_0(1)` and the
degree relation `ζ_i(1) = d_i ζ_0(1)` for the family `ζ_i = Ind_K^L θ_i`. -/
theorem induce_apply_one_ne_zero (K : Subgroup L) [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (θ : IrreducibleCharacter ↥K) :
    ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L) ≠ 0 := by
  rw [ClassFunction.induce_apply_one]
  obtain ⟨d, hd, hval⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  refine mul_ne_zero (Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite) ?_
  rw [hval]
  exact Nat.cast_ne_zero.mpr hd.ne'

/-- **The induced character is real at `1`.**  `Ind_K^L θ (1) = [L:K] · θ(1)` is the natural-number
cast `[L:K] · dim θ`, so it is fixed by complex conjugation.  Supplies `star d_i = d_i` for the
degree ratios `d_i = ζ_i(1)/ζ_0(1)` in the `(7.8.a)` `Gamma_orth_nu` computation. -/
theorem induce_apply_one_star (K : Subgroup L) [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (θ : IrreducibleCharacter ↥K) :
    star (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L))
      = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L) := by
  rw [ClassFunction.induce_apply_one]
  obtain ⟨d, _, hval⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  rw [hval, ← Nat.cast_mul]
  exact star_natCast _

/-- **The induced family is pairwise orthogonal** (Peterfalvi (7.6)/(7.7.a) hypothesis).  For a
family `θ : Fin (n+1) → Irr K` of pairwise non-conjugate irreducibles, the induced characters
`ζ_i = Ind_K^L θ_i` are pairwise orthogonal — the `horth` hypothesis of `chiRho_decomp_proof`.
Direct from `inner_induce_eq_zero_of_not_conj`. -/
theorem induce_family_orthogonal (K : Subgroup L) [K.Normal] [Fintype ↥K] [Invertible (Nat.card L : ℂ)]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hnc : ∀ a b : Fin (n + 1), a ≠ b →
      ∀ g : L, IrreducibleCharacter.conjBy g (θ a) ≠ θ b) :
    ∀ a b : Fin (n + 1), a ≠ b →
      ClassFunction.inner (ClassFunction.induce K (θ a : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (θ b : ClassFunction ↥K ℂ)) = 0 :=
  fun a b hab => inner_induce_eq_zero_of_not_conj (θ a) (θ b) (hnc a b hab)

/-- **An injective induced family is pairwise orthogonal** (Peterfalvi (7.6)/(7.7.a)).  When the
map `i ↦ Ind_K^L θ_i` is injective, the `θ_i` are pairwise non-conjugate (a conjugacy would force
equal inductions, `induce_eq_induce_iff_conj`), so `induce_family_orthogonal` applies.  This is the
form of `horth` actually supplied by the enumeration of the *distinct* induced characters. -/
theorem induce_family_orthogonal_of_injective (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective
      (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) :
    ∀ a b : Fin (n + 1), a ≠ b →
      ClassFunction.inner (ClassFunction.induce K (θ a : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (θ b : ClassFunction ↥K ℂ)) = 0 :=
  induce_family_orthogonal K θ fun a b hab g hg =>
    hab (hinj ((induce_eq_induce_iff_conj (θ a) (θ b)).mpr ⟨g, hg⟩))

/-- **The difference `ψ_i = ζ_i − d_i ζ_0` is supported on `K^#`** (Peterfalvi (7.6)/(7.7.a)
hypothesis).  With `ζ = Ind_K^L θ` and the degree relation `ζ_i(1) = d_i ζ_0(1)`, the difference
`Ind θ − d • Ind θ₀` vanishes off `K` (induction from the normal `K` is `K`-supported) and at `1`
(degree relation), so its support lies in `K^# = K \ {1}` — the `psi_support` hypothesis of
`chiRho_decomp_proof`. -/
theorem induce_diff_support {K : Subgroup L} [hK : K.Normal] [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] (θ θ₀ : IrreducibleCharacter ↥K) (d : ℂ)
    (hd : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L)
        = d * ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) (1 : L)) :
    (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
        - d • ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ)).support ⊆ (K : Set L) \ {1} := by
  have hvanish : ∀ φ : ClassFunction ↥K ℂ, ∀ x : L, x ∉ K → ClassFunction.induce K φ x = 0 := by
    intro φ x hxK
    have hconj : x ∉ ClassFunction.conjugatesInto K := by
      rw [ClassFunction.mem_conjugatesInto]
      rintro ⟨y, hy⟩
      have h := hK.conj_mem (y⁻¹ * x * y) hy y
      have he : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
      exact hxK (he ▸ h)
    rw [ClassFunction.induce_apply, ← ClassFunction.induceSum_apply,
      ClassFunction.induceSum_eq_zero_of_not_conjugatesInto φ hconj, mul_zero]
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, ClassFunction.smul_apply] at hx
  refine ⟨?_, ?_⟩
  · by_contra hxK
    exact hx (by rw [hvanish _ x hxK, hvanish _ x hxK, mul_zero, sub_zero])
  · intro hx1
    rw [Set.mem_singleton_iff] at hx1
    exact hx (by rw [hx1, hd, sub_self])

/-- **Peterfalvi (7.7.a), the degree-zero reduction.**  A class function in the span of the full
family `{ζ_i}` that vanishes at `1` lies in the span of the difference vectors `{ψ_i = ζ_i − d_i ζ_0}`
(`i ≠ 0`).  Writing `ψ = Σ a_i ζ_i`, the condition `ψ(1) = 0` gives `Σ a_i d_i = 0` (`ζ_i(1) = d_i ζ_0(1)`,
`ζ_0(1) ≠ 0`), and then `ψ = Σ_{i≠0} a_i ψ_i` since the `ζ_0`-coefficient `a_0 + Σ_{i≠0} a_i d_i =
Σ_i a_i d_i = 0`.  Combined with `CF(L,A) ⊆ span {ζ_i}` (`eq_induce_restrict_of_supported` + the family
covering all induced characters), this gives the `hspan` hypothesis of `chiRho_decomp_proof`. -/
theorem mem_span_psi_of_apply_one_zero {n : ℕ} (ζ : Fin (n + 1) → ClassFunction L ℂ)
    (d : Fin (n + 1) → ℂ) (hd : ∀ i : Fin (n + 1), ζ i (1 : L) = d i * ζ 0 (1 : L))
    (hz0 : ζ 0 (1 : L) ≠ 0) {ψ : ClassFunction L ℂ}
    (hψ : ψ ∈ Submodule.span ℂ (Set.range ζ)) (hψ1 : ψ (1 : L) = 0) :
    ψ ∈ Submodule.span ℂ ((fun i => ζ i - d i • ζ 0) '' {i : Fin (n + 1) | i ≠ 0}) := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hψ
  have hd0 : d 0 = 1 := (mul_right_cancel₀ hz0 (by rw [one_mul]; exact hd 0)).symm
  -- `Σ a_i d_i = 0` from `ψ(1) = 0`.
  have hsum0 : ∑ i, a i * d i = 0 := by
    have hv : ∑ i, a i * ζ i (1 : L) = 0 := by
      have h0 : (∑ i, a i • ζ i) (1 : L) = 0 := by rw [ha]; exact hψ1
      rw [ClassFunction.finset_sum_apply] at h0
      simpa only [ClassFunction.smul_apply] using h0
    have h1 : (∑ i, a i * d i) * ζ 0 (1 : L) = 0 := by
      rw [Finset.sum_mul, ← hv]
      exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
    exact (mul_eq_zero.mp h1).resolve_right hz0
  -- `Σ_{i≠0} a_i • (ζ_i − d_i ζ_0) = ψ`.
  have hcombo : (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), a i • (ζ i - d i • ζ 0)) = ψ := by
    have hexp : (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), a i • (ζ i - d i • ζ 0))
        = (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), a i • ζ i)
          - (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (a i * d i) • ζ 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_sub, smul_smul]
    rw [hexp, ← Finset.sum_smul,
      Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin (n + 1))),
      Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin (n + 1))),
      ha, hd0, mul_one, hsum0, zero_sub, neg_smul]
    abel
  rw [← hcombo]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨i, Finset.ne_of_mem_erase hi, rfl⟩

/-- **Peterfalvi (7.7.a), the spanning hypothesis from a covering induced family.**  Given a family
`ζ : Fin (n+1) → CF(L)` whose values *cover* every induced irreducible `Ind_K^L θ` (`hcover`) and
satisfy the degree relation `ζ_i(1) = d_i ζ_0(1)` with `ζ_0(1) ≠ 0`, any class function `ψ`
supported inside the normal subgroup `K` and vanishing at `1` lies in the span of the difference
vectors `{ψ_i = ζ_i − d_i ζ_0 : i ≠ 0}`.

This is the `hspan` hypothesis of `chiRho_decomp_proof`: `supported_mem_span_induce_irr` places `ψ`
in the span of the induced irreducibles, `hcover` + `Submodule.span_mono` transports this to the
span of `{ζ_i}`, and `mem_span_psi_of_apply_one_zero` performs the degree-`0` reduction. -/
theorem supported_mem_span_psi (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (hcover : ∀ θ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∈ Set.range ζ)
    (hdeg : ∀ i : Fin (n + 1), ζ i (1 : L) = d i * ζ 0 (1 : L)) (hz0 : ζ 0 (1 : L) ≠ 0)
    {ψ : ClassFunction L ℂ} (hsupp : ∀ y : L, y ∉ K → ψ y = 0) (hψ1 : ψ (1 : L) = 0) :
    ψ ∈ Submodule.span ℂ ((fun i => ζ i - d i • ζ 0) '' {i : Fin (n + 1) | i ≠ 0}) := by
  refine mem_span_psi_of_apply_one_zero ζ d hdeg hz0 ?_ hψ1
  refine Submodule.span_mono ?_ (supported_mem_span_induce_irr K ψ hsupp)
  rintro v ⟨θ, rfl⟩
  exact hcover θ

/-- **The distinct induced characters as data** (Peterfalvi (7.6) family).  Bundles the
representative family `θ : Fin (n+1) → Irr K` enumerating the *distinct* induced characters
`ζ_i = Ind_K^L θ_i`, together with the two facts `inj` (the members are distinct) and `cover`
(every induced irreducible occurs).  Packaged as data (not an `∃`) so it can be projected inside a
`Type`-valued construction such as `hypothesis76OfDade`. -/
structure DistinctInducedFamily (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] where
  /-- One less than the number of distinct induced characters. -/
  n : ℕ
  /-- A representative irreducible for each distinct induced character. -/
  θ : Fin (n + 1) → IrreducibleCharacter ↥K
  /-- The induced characters `ζ_i = Ind_K^L θ_i` are pairwise distinct. -/
  inj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
  /-- Every induced irreducible occurs among the `ζ_i`. -/
  cover : ∀ φ : IrreducibleCharacter ↥K,
    ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
      Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))

/-- **Construction of the distinct induced family.**  The members are the `Finset.equivFin` listing
of `Finset.univ.image (Ind_K^L ·)`, nonempty since the trivial character contributes; injectivity
is `equivFin.symm.injective` and covering is `Finset.mem_image`. -/
noncomputable def distinctInducedFamily (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] :
    DistinctInducedFamily K := by
  classical
  haveI : Finite ↥K := Finite.of_fintype _
  let V : Finset (ClassFunction L ℂ) :=
    Finset.univ.image (fun φ : IrreducibleCharacter ↥K =>
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ))
  have hVne : V.Nonempty :=
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (trivialIrreducibleCharacter ↥K))⟩
  have hn : V.card = (V.card - 1) + 1 := (Nat.succ_pred_eq_of_pos hVne.card_pos).symm
  let e : ↥V ≃ Fin ((V.card - 1) + 1) := V.equivFin.trans (finCongr hn)
  have hrep : ∀ i : Fin ((V.card - 1) + 1), ∃ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) = (e.symm i : ClassFunction L ℂ) := by
    intro i
    obtain ⟨φ, _, hφ⟩ := Finset.mem_image.mp (e.symm i).2
    exact ⟨φ, hφ⟩
  choose θ hθ using hrep
  exact
    { n := V.card - 1
      θ := θ
      inj := by
        intro i j hij
        have hval : (e.symm i : ClassFunction L ℂ) = (e.symm j : ClassFunction L ℂ) := by
          rw [← hθ i, ← hθ j]; exact hij
        exact e.symm.injective (Subtype.ext hval)
      cover := by
        intro φ
        have hmem : ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈ V :=
          Finset.mem_image_of_mem _ (Finset.mem_univ φ)
        refine ⟨e ⟨_, hmem⟩, ?_⟩
        show ClassFunction.induce K (θ (e ⟨_, hmem⟩) : ClassFunction ↥K ℂ) = _
        rw [hθ (e ⟨_, hmem⟩)]
        exact congrArg Subtype.val (Equiv.symm_apply_apply e ⟨_, hmem⟩) }

/-- **Existence form** of `distinctInducedFamily`, for `Prop`-level consumers. -/
theorem exists_distinct_induced_family (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] :
    ∃ (n : ℕ) (θ : Fin (n + 1) → IrreducibleCharacter ↥K),
      Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) ∧
      ∀ φ : IrreducibleCharacter ↥K,
        ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
          Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) :=
  let F := distinctInducedFamily K
  ⟨F.n, F.θ, F.inj, F.cover⟩

/-- **Reindexing the induced family preserves injectivity.**  For any permutation `σ`, the family
`i ↦ Ind_K^L θ_{σ i}` is injective when `i ↦ Ind_K^L θ_i` is.  Used to move the distinguished member
to index `0` (`σ = Equiv.swap 0 j`) before applying `chiRho_eq_inner_beta_induced` (which expects
the distinguished `ζ` at index `0`). -/
theorem induce_family_comp_perm_injective {K : Subgroup L} [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ} {θ : Fin (n + 1) → IrreducibleCharacter ↥K}
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Function.Injective (fun i => ClassFunction.induce K (θ (σ i) : ClassFunction ↥K ℂ)) :=
  hinj.comp σ.injective

/-- **Reindexing the induced family preserves covering.** -/
theorem induce_family_comp_perm_covering {K : Subgroup L} [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ} {θ : Fin (n + 1) → IrreducibleCharacter ↥K}
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (σ : Equiv.Perm (Fin (n + 1))) :
    ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ (σ i) : ClassFunction ↥K ℂ)) := by
  intro φ
  obtain ⟨i, hi⟩ := hcover φ
  exact ⟨σ.symm i, by simpa using hi⟩

/-- **Discharge of the (7.7.a) certificate for an induced family** (Peterfalvi (7.7.a)).  This is
the consolidation of `chiRho_decomp_proof` for the concrete family `ζ_i = Ind_K^L θ_i`: the
orthogonality (`horth`) and spanning (`hspan`) hypotheses of the basis argument are *derived* from
the induced-family data — injectivity `hinj` (distinct members) and covering `hcover` (every induced
irreducible is in the family) — via `induce_family_orthogonal_of_injective`, `induce_norm_ne_zero`,
and `supported_mem_span_psi`.  The only remaining inputs are the geometric facts that `A` (where
`χ^ρ` is read off) sits inside `K^#`: `hAK_off` (`A`-support lies in `K`), `hA_one` (`1 ∉ A`), and
the conjugation-invariance `hAconj`.

When `K = H.subgroupOf L` for the normal subgroup `H ⊴ L` of Peterfalvi's `Hypothesis76` and
`A = H \ {1}`, all of `hinj`/`hcover` come from `exists_distinct_induced_family`, `hdeg`/`psi_support`
from `induce_apply_one_ne_zero`/`induce_diff_support`, and `hAK_off`/`hA_one`/`hAconj` from
`Subgroup.mem_subgroupOf` + the normality of `H`.  Thus the `Hypothesis76.chiRho_decomp` certificate
is constructible from `(7.1)` data alone, with no certificate assumed. -/
theorem chiRho_decomp_induced {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (K : Subgroup ↥L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L)
        = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L))
    (hAconj : ∀ g h : ↥L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hAK_off : ∀ y : ↥L, y ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L → y ∈ K)
    (hA_one : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (χ : ClassFunction G ℂ) {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
            - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ) /
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) *
        ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) x := by
  refine chiRho_decomp_proof H71 (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) d
    psi_support (induce_family_orthogonal_of_injective K θ hinj)
    (fun i => induce_norm_ne_zero K (θ i)) hAconj ?_ χ hx
  intro ψ hψ
  refine supported_mem_span_psi K (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) d
    hcover hdeg (induce_apply_one_ne_zero K (θ 0)) ?_ ?_
  · intro y hyK
    by_contra hne
    exact hyK (hAK_off y (hψ (ClassFunction.mem_support.mpr hne)))
  · by_contra hne
    exact hA_one (hψ (ClassFunction.mem_support.mpr hne))

/-- **`H.subgroupOf L` is normal when `L` conjugation-normalizes `H`.**  If every `l ∈ L`
conjugates `H ≤ G` into itself (the `H_normal_in_L` field of `Hypothesis76`), then `H.subgroupOf L`
is a normal subgroup of `↥L`.  Direct check of the `conj_mem` field via `Subgroup.mem_subgroupOf`
and the coercion `↑(g·n·g⁻¹) = ↑g·↑n·↑g⁻¹`. -/
theorem subgroupOf_normal_of_conj {G : Type*} [Group G] {H L : Subgroup G}
    (hconj : ∀ (g : ↥L) {h : G}, h ∈ H → (g : G) * h * (g : G)⁻¹ ∈ H) :
    (H.subgroupOf L).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj g hn

/-! ### Geometric facts on the sharp support `supportInSubgroup (H \ {1}) L`

The support set `A = H \ {1}` (where `H ⊴ L`) translates, on the subgroup side
`K = H.subgroupOf L`, into the punctured subgroup `K \ {1}`.  These lemmas package the
`A ↔ K` dictionary used by `chiRho_decomp_induced` / `chiRho_eq_inner_beta_induced`
(membership, the excluded identity, and conjugation-invariance from normality of `H`). -/

section SharpSupport
variable {G : Type*} [Group G] {L : Subgroup G}

/-- Membership in the sharp support, phrased on `G`: `x ∈ supportInSubgroup (H \ {1}) L`
iff `(x : G) ∈ H` and `(x : G) ≠ 1`. -/
theorem mem_supportInSubgroup_sharp_iff (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) (x : ↥L) :
    x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔ ((x : G) ∈ H ∧ (x : G) ≠ 1) := by
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hAH]
  simp only [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]

/-- Membership in the sharp support, phrased on the subgroup side `K = H.subgroupOf L`:
`x ∈ supportInSubgroup (H \ {1}) L` iff `x ∈ H.subgroupOf L` and `x ≠ 1`. -/
theorem mem_supportInSubgroup_sharp_subgroupOf_iff (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) (x : ↥L) :
    x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔ (x ∈ H.subgroupOf L ∧ x ≠ 1) := by
  rw [mem_supportInSubgroup_sharp_iff H hAH x, Subgroup.mem_subgroupOf]
  exact and_congr_right fun _ => not_congr OneMemClass.coe_eq_one

/-- The sharp support is contained in `K = H.subgroupOf L`. -/
theorem supportInSubgroup_sharp_subset_subgroupOf (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) {x : ↥L}
    (hx : x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L) : x ∈ H.subgroupOf L :=
  ((mem_supportInSubgroup_sharp_subgroupOf_iff H hAH x).mp hx).1

/-- The identity is not in the sharp support. -/
theorem one_not_mem_supportInSubgroup_sharp (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) :
    (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L := fun hx =>
  ((mem_supportInSubgroup_sharp_subgroupOf_iff H hAH 1).mp hx).2 rfl

/-- The sharp support is invariant under `L`-conjugation (from normality of `H` in `L`). -/
theorem supportInSubgroup_sharp_conj_mem_iff (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1})
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H) (g h : ↥L) :
    h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  rw [mem_supportInSubgroup_sharp_subgroupOf_iff H hAH,
    mem_supportInSubgroup_sharp_subgroupOf_iff H hAH]
  refine and_congr ?_ ?_
  · constructor
    · intro hm
      have hc := hKnorm.conj_mem _ hm h⁻¹
      have heq : h⁻¹ * (h * g * h⁻¹) * (h⁻¹)⁻¹ = g := by group
      rwa [heq] at hc
    · intro hm; exact hKnorm.conj_mem _ hm h
  · rw [ne_eq, ne_eq, mul_inv_eq_one, mul_eq_left]

end SharpSupport

/-- **Construction of `Hypothesis76` from `(7.1)` data** (Peterfalvi (7.6)/(7.7.a)).  Given the
Dade-isometry data of `(7.1)` (`H71` together with `hτ : IsDadeIsometry H71.τ`) and a normal
subgroup `H ⊴ L` with `A = H \ {1}`, the entire `Hypothesis76` structure — *including* the
`(7.7.a)` certificate `chiRho_decomp` — is constructed with **no certificate assumed**.

The induced family `ζ_i = Ind_{H}^L θ_i` is the `exists_distinct_induced_family` enumeration of the
distinct induced characters, the degree ratios are `d_i = ζ_i(1)/ζ_0(1)`, and `chiRho_decomp` is
discharged by `chiRho_decomp_induced` (its `hinj`/`hcover` from the enumeration, the geometric
`A = H^#` inputs from `Subgroup.mem_subgroupOf` + normality of `H`).  This realizes the issue-1013
goal: `Hypothesis76` (hence the `(7.7.a)` content) is constructible from coherence/`(7.1)` data alone. -/
noncomputable def hypothesis76OfFamily
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))) :
    Hypothesis76 G A L := by
  classical
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  -- The induced family `ζ` and degree ratios `d`.
  set ζ : Fin (n + 1) → ClassFunction ↥L ℂ :=
    fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) with hζ
  set d : Fin (n + 1) → ℂ := fun i => ζ i (1 : ↥L) / ζ 0 (1 : ↥L) with hd
  have hz0 : ζ 0 (1 : ↥L) ≠ 0 := induce_apply_one_ne_zero _ (θ 0)
  have hdeg : ∀ i, ζ i (1 : ↥L) = d i * ζ 0 (1 : ↥L) := fun i => by
    rw [hd]; field_simp
  -- Support characterization: `x ∈ supportInSubgroup A L ↔ (x:G) ∈ H ∧ (x:G) ≠ 1`.
  have hAchar : ∀ x : ↥L, x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      ((x : G) ∈ H ∧ (x : G) ≠ 1) := fun x => by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hAH]
    simp only [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  -- `x ≠ 1` in `↥L` is equivalent to `(x:G) ≠ 1`.
  have hne_one : ∀ x : ↥L, (x : G) ≠ 1 ↔ x ≠ 1 := fun x => by
    rw [not_iff_not]
    constructor
    · intro h; exact Subtype.ext (by rw [h, Subgroup.coe_one])
    · intro h; rw [h, Subgroup.coe_one]
  -- `ζ_i` vanishes off `H`.
  have hvanish : ∀ (i : Fin (n + 1)) (x : ↥L), (x : G) ∉ H → ζ i x = 0 := fun i x hxH => by
    rw [hζ]
    exact ClassFunction.induce_eq_zero_of_not_mem_normal _ (by rwa [Subgroup.mem_subgroupOf])
  -- `ψ_i = ζ_i − d_i ζ_0` is supported on `A = H^#`.
  have hpsupp : ∀ i, (ζ i - d i • ζ 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L := fun i => by
    rw [hζ]
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_diff, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_singleton_iff] at hx
    rw [hAchar]
    exact ⟨hx.1, (hne_one x).mpr hx.2⟩
  -- Geometric inputs for `chiRho_decomp_induced`, phrased through `K = H.subgroupOf L`.
  have hAK_off : ∀ x : ↥L, x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L →
      x ∈ H.subgroupOf L := fun _ => supportInSubgroup_sharp_subset_subgroupOf H hAH
  have hA_one : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    one_not_mem_supportInSubgroup_sharp H hAH
  have hAconj : ∀ g h : ↥L,
      h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    fun g h => supportInSubgroup_sharp_conj_mem_iff H hAH hHnorm g h
  -- Assemble the structure; `chiRho_decomp` is discharged by `chiRho_decomp_induced`.
  exact
    { hyp71 := H71
      isDadeIsometry := hτ
      H := H
      H_le_L := hHL
      H_normal_in_L := hHnorm
      A_eq_H_sharp := hAH
      n := n
      zeta := ζ
      d := d
      zeta_eq_zero_of_not_mem_H := hvanish
      zeta_one_eq_d_mul := hdeg
      psi_support := hpsupp
      chiRho_decomp := by
        intro χ x hx
        exact chiRho_decomp_induced H71 (H.subgroupOf L) θ d hpsupp hinj hcover hdeg hAconj
          hAK_off hA_one χ hx }

/-- **Construction of `Hypothesis76` from `(7.1)` data** (Peterfalvi (7.6)/(7.7.a)).  The induced
family is the canonical `distinctInducedFamily` enumeration; this is `hypothesis76OfFamily`
specialised to that family.  See `hypothesis76OfFamily` for the construction details. -/
noncomputable def hypothesis76OfDade
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1}) :
    Hypothesis76 G A L := by
  classical
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  exact hypothesis76OfFamily H71 hτ H hHL hHnorm hAH (distinctInducedFamily (H.subgroupOf L)).θ
    (distinctInducedFamily (H.subgroupOf L)).inj (distinctInducedFamily (H.subgroupOf L)).cover

/-! ### (7.8.c) building blocks: the induced principal character on `A`

Peterfalvi's (7.8.c) collapse hinges on the fact that `ζ_1 = Ind_K^L 1_K` satisfies
`ζ_1(x) = ‖ζ_1‖² = [L:K]` for `x ∈ K`, so the single surviving `(7.7.a)` term
`(c̄_1/‖ζ_1‖²) ζ_1(x)` simplifies to `c̄_1 = star(β,χ)`. -/

/-- **Conjugation fixes the trivial class function.**  `(1_K)^g = 1_K` for any `g`, since the
trivial class function is constant `1`. -/
theorem conjBy_trivialClassFunction {K : Subgroup L} [K.Normal] (g : L) :
    ClassFunction.conjBy g (trivialClassFunction ↥K) = trivialClassFunction ↥K := by
  ext h
  simp only [ClassFunction.conjBy_apply, trivialClassFunction_apply]

/-- **The induced principal character is `[L:K]` on `K`** (Peterfalvi (7.8.c)).  For a normal
subgroup `K ◁ L` and `x ∈ K`, `(Ind_K^L 1_K)(x) = [L:K]`: every conjugate of `x` lies in `K`
(normality), so all `|L|` induction summands equal `1`, giving `|L|/|K| = [L:K]`. -/
theorem induce_trivialChar_apply_eq_index (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {x : L} (hx : x ∈ K) :
    ClassFunction.induce K (trivialClassFunction ↥K) x = (K.index : ℂ) := by
  rw [ClassFunction.induce_apply_of_mem_normal_of_const (le_refl K) (trivialClassFunction ↥K)
      (fun a' _ => trivialClassFunction_apply _) hx, mul_one,
    show (Nat.card L : ℂ) = (K.index : ℂ) * (Nat.card ↥K : ℂ) from by
      rw [← Nat.cast_mul, K.index_mul_card],
    show ⅟(Nat.card ↥K : ℂ) * ((K.index : ℂ) * (Nat.card ↥K : ℂ))
        = (K.index : ℂ) * (⅟(Nat.card ↥K : ℂ) * (Nat.card ↥K : ℂ)) from by ring,
    invOf_mul_self, mul_one]

/-- **The norm of the induced principal character is `[L:K]`** (Peterfalvi (7.8.c)).  For a normal
subgroup `K ◁ L`, `‖Ind_K^L 1_K‖² = [L:K]`: by `card_mul_inner_self_induce_eq_card_inertia`,
`|K| · ‖Ind 1_K‖² = |I_L(1_K)| = |L|` since the trivial character is `L`-invariant
(`inertia 1_K = ⊤`); dividing by `|K|` gives `[L:K]`. -/
theorem induce_trivialChar_normSq_eq_index (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] :
    ClassFunction.inner (ClassFunction.induce K (trivialClassFunction ↥K))
      (ClassFunction.induce K (trivialClassFunction ↥K)) = (K.index : ℂ) := by
  have hcoe : (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) = trivialClassFunction ↥K := rfl
  have htop : ClassFunction.inertia (trivialClassFunction ↥K) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [ClassFunction.mem_inertia]
    exact conjBy_trivialClassFunction g
  have hkey := card_mul_inner_self_induce_eq_card_inertia (G := L) (trivialIrreducibleCharacter ↥K)
  rw [hcoe, htop, Subgroup.card_top] at hkey
  have hcardK : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h2 : (Nat.card ↥K : ℂ) * (K.index : ℂ) = (Nat.card L : ℂ) := by
    rw [← Nat.cast_mul, mul_comm, K.index_mul_card]
  exact mul_left_cancel₀ hcardK (hkey.trans h2.symm)

/-- **A nonprincipal induced character is orthogonal to `1_L`** (Peterfalvi (7.8.a), the `(φ,1_L)=0`
step).  For `θ ∈ Irr K` with `θ ≠ 1_K`, `(Ind_K^L θ, 1_L)_L = 0`: by Frobenius reciprocity it is
`(θ, Res_K 1_L)_K = (θ, 1_K)_K`, which vanishes by orthonormality of distinct irreducibles.

This is the honest `(7.8.a)` ingredient that `(φ − d ζ, 1_L) = 0` (for the members `φ, ζ ∈ S`,
induced from nonprincipal characters) rests on; the rest of `(7.8.a)`'s `orth_one` additionally
needs the coherence facts `(φ−dζ)^τ = φ^ν − d ζ^ν` and `(ζ^ν, 1_G) = 0` about the extension `ν`. -/
theorem inner_induce_constOne_eq_zero (K : Subgroup L) [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    (θ : IrreducibleCharacter ↥K) (hθ : θ ≠ trivialIrreducibleCharacter ↥K) :
    ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
      (Hypothesis71.constOne L) = 0 := by
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    show ClassFunction.restrict K (Hypothesis71.constOne L)
        = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) from by
      ext h; rw [ClassFunction.restrict_apply]; rfl,
    irreducibleCharacter_inner_eq_ite, if_neg hθ]

/-- **The induced principal character has inner product `1` with `1_L`** (Peterfalvi (7.8.a)).
`⟨Ind_K^L 1_K, 1_L⟩ = ⟨1_K, 1_K⟩ = 1` by Frobenius reciprocity.  Supplies `⟨β, 1_G⟩ = ⟨Ind 1_K − ζ,
1_L⟩ = 1 − 0 = 1` in the `Gamma_orth_one` computation. -/
theorem inner_induce_trivialChar_constOne_eq_one (K : Subgroup L) [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] :
    ClassFunction.inner
        (ClassFunction.induce K (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ))
        (Hypothesis71.constOne L) = 1 := by
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    show ClassFunction.restrict K (Hypothesis71.constOne L)
        = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) from by
      ext h; rw [ClassFunction.restrict_apply]; rfl,
    irreducibleCharacter_inner_eq_ite, if_pos rfl]

/-- **The Dade image of a supported class function is orthogonal to `1_G` iff the source is to
`1_L`** (Peterfalvi (7.8.a), the `(2.7)`-for-`1_G` instance).  For `α ∈ CF(L,A)`,
`⟨α^τ, 1_G⟩_G = ⟨α, 1_L⟩_L`: by the adjoint formula `chiRho_adjoint` `⟨α^τ, 1_G⟩ = ⟨α, (1_G)^ρ⟩`,
and `(1_G)^ρ = 1` on `A` (`chiRho_constOne`) where `α` is supported (`inner_eq_of_eqOn_support`). -/
theorem inner_tau_supported_constOne {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L) :
    ClassFunction.inner (H71.τ α) (Hypothesis71.constOne G)
      = ClassFunction.inner (α : ClassFunction L ℂ) (Hypothesis71.constOne L) := by
  rw [H71.chiRho_adjoint]
  refine inner_eq_of_eqOn_support fun g hg => ?_
  have hgA : (g : G) ∈ A := by
    have h := (ClassFunction.mem_supportedSubmodule.mp α.2) (ClassFunction.mem_support.mpr hg)
    rwa [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at h
  rw [H71.chiRhoCF_apply, H71.chiRho_constOne, if_pos hgA, Hypothesis71.constOne_apply]

/-- **Peterfalvi (7.8.a), `S^ν ⊥ 1_G`** (the `orth_one` field of `BetaDecomp`), carrier-conditional
on the coherence of `ν`.  With the distinguished `ζ = Ind_K^L θ_0` at index `0`, the principal
`Ind_K^L 1_K` at `ind1H ≠ 0`, the coherence agreement `(ζ_i − d_i ζ_0)^τ = ζ_i^ν − d_i ζ_0^ν`
(`hagree`), and the single base fact `⟨ζ_0^ν, 1_G⟩ = 0` (`hzeta0nu`, the distinguished image is
nonprincipal), every `ζ_i^ν` (`i ≠ ind1H`) is orthogonal to `1_G`:

* `i = 0` is `hzeta0nu`;
* for `i ≠ 0, ind1H`, `⟨ζ_i^ν, 1_G⟩ = ⟨(ζ_i − d_i ζ_0)^τ, 1_G⟩ + d_i ⟨ζ_0^ν, 1_G⟩` (`hagree`), the
  first summand is `⟨ζ_i − d_i ζ_0, 1_L⟩ = 0` (`inner_tau_supported_constOne` +
  `inner_induce_constOne_eq_zero`, as `θ_i, θ_0 ≠ 1_K`), the second is `0` (`hzeta0nu`). -/
theorem betaDecomp_orth_one {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (K : Subgroup ↥L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
    (hzeta0nu : ClassFunction.inner (ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
      (Hypothesis71.constOne G) = 0) :
    ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
        (Hypothesis71.constOne G) = 0 := by
  have hne_triv : ∀ j : Fin (n + 1), j ≠ ind1H → θ j ≠ trivialIrreducibleCharacter ↥K := by
    intro j hj hcontra
    apply hj
    apply hinj
    show ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)
      = ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
    rw [hcontra, hzeta_ind1H]
  intro i hi
  by_cases hi0 : i = 0
  · rw [hi0]; exact hzeta0nu
  · have hrearrange : ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
        = H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
            - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
          + d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) := by
      rw [hagree i hi0 hi]; abel
    rw [hrearrange, ClassFunction.inner_add_left, ClassFunction.inner_smul_left, hzeta0nu,
      mul_zero, add_zero, inner_tau_supported_constOne]
    show ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) (Hypothesis71.constOne L) = 0
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      inner_induce_constOne_eq_zero K (θ i) (hne_triv i hi),
      inner_induce_constOne_eq_zero K (θ 0) (hne_triv 0 (Ne.symm hind1H)),
      mul_zero, sub_zero]

/-- **The family-difference inner product** (Peterfalvi (7.8.a), `a_φ` computation).  For pairwise
distinct family members, `⟨ζ_{ind1H} − ζ_0, ζ_i − d_i ζ_0⟩ = star(d_i) ‖ζ_0‖²` (`i ≠ 0, ind1H`,
`ind1H ≠ 0`): all cross terms vanish by orthogonality (`induce_family_orthogonal_of_injective`),
leaving the `d_i ζ_0`-against-`ζ_0` term.  Via `IsDadeIsometry.inner_eq` and the coherence agreement
this equals `⟨β, ζ_i^ν − d_i ζ_0^ν⟩`, the key step in the `(7.8.a)` decomposition. -/
theorem inner_family_diff (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (d : Fin (n + 1) → ℂ) {i ind1H : Fin (n + 1)}
    (hi0 : i ≠ 0) (hi_ind : i ≠ ind1H) (hind0 : ind1H ≠ 0) :
    ClassFunction.inner
        (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      = star (d i) * ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
          (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) := by
  have horth := induce_family_orthogonal_of_injective K θ hinj
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_right, ClassFunction.inner_smul_right,
    horth ind1H i (Ne.symm hi_ind), horth ind1H 0 hind0, horth 0 i (Ne.symm hi0)]
  ring

/-- **The inner product `⟨β, ζ_i^ν − d_i ζ_0^ν⟩`** (Peterfalvi (7.8.a), `a_φ` step).  With
`β = (ζ_{ind1H} − ζ_0)^τ` and the coherence agreement `ζ_i^ν − d_i ζ_0^ν = (ζ_i − d_i ζ_0)^τ`
(`hagree_i`), the Dade isometry (`hτ : IsDadeIsometry`) turns the `G`-side inner product into the
`L`-side family inner product `⟨ζ_{ind1H} − ζ_0, ζ_i − d_i ζ_0⟩ = star(d_i) ‖ζ_0‖²`
(`inner_family_diff`).  No `ρ`-projection is needed — only the two isometries. -/
theorem inner_beta_nuDiff {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (K : Subgroup ↥L) [K.Normal] [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (diffβ : (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
        - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {i : Fin (n + 1)} (hi0 : i ≠ 0) (hi_ind : i ≠ ind1H)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hagree_i : ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
        - d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      = H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) :
    ClassFunction.inner
        (H71.τ ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
            - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), diffβ⟩)
        (ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
      = star (d i) * ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
          (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) := by
  rw [hagree_i, hτ.inner_eq]
  exact inner_family_diff K θ hinj d hi0 hi_ind hind0

/-- **The inner product `⟨weightedNuSum, ζ_j^ν⟩ = ζ_j(1)/ζ_0(1)`** (Peterfalvi (7.8.a)).  The
weighted sum `Σ_{i ≠ ind1H} (ζ_i(1)/(ζ_0(1)‖ζ_i‖²)) ζ_i^ν` paired against `ζ_j^ν` (`j ≠ ind1H`)
collapses by the `ν`-isometry (`hnu`) + family orthogonality to the single `i = j` term, which is
`(ζ_j(1)/(ζ_0(1)‖ζ_j‖²)) ‖ζ_j‖² = ζ_j(1)/ζ_0(1)`.  This supplies the `a · ⟨weightedNuSum, ζ_j^ν⟩`
term that cancels `⟨β, ζ_j^ν⟩` in the `Gamma_orth_nu` computation. -/
theorem inner_weightedNuSum_nu {G : Type*} [Group G] [Fintype G] {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (K : Subgroup ↥L) [K.Normal] [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu : ∀ φ ψ : ClassFunction ↥L ℂ, ClassFunction.inner (ν φ) (ν ψ) = ClassFunction.inner φ ψ)
    {ind1H j : Fin (n + 1)} (hj : j ≠ ind1H) :
    ClassFunction.inner
      (∑ i ∈ Finset.univ.erase ind1H,
        (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L) /
          (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) *
            ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
              (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) : ℂ) •
          ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
      (ν (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)))
    = ClassFunction.induce K (θ j : ClassFunction ↥K ℂ) (1 : ↥L) /
        ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) := by
  rw [inner_sum_left, Finset.sum_eq_single_of_mem j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      (fun i _ hij => by
        rw [ClassFunction.inner_smul_left, hnu,
          induce_family_orthogonal_of_injective K θ hinj i j hij, mul_zero]),
    ClassFunction.inner_smul_left, hnu]
  have hN : ClassFunction.inner (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)) ≠ 0 := induce_norm_ne_zero K (θ j)
  have hz0 : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero K (θ 0)
  field_simp

/-- **The inner product `⟨β, ζ_j^ν⟩ = star(d_j) · a`** (Peterfalvi (7.8.a)).  With `a = ⟨β, ζ_0^ν⟩ + 1`
and `‖ζ_0‖² = 1` (the distinguished `ζ_0 ∈ Irr L`), `inner_beta_nuDiff` (`⟨β, ζ_j^ν − d_j ζ_0^ν⟩ =
star(d_j) ‖ζ_0‖²`) rearranges to `⟨β, ζ_j^ν⟩ = star(d_j)(⟨β, ζ_0^ν⟩ + 1)` for `j ≠ 0, ind1H`.  This is
the `⟨β, ζ_j^ν⟩` value that cancels `a ⟨weightedNuSum, ζ_j^ν⟩` in `Gamma_orth_nu`. -/
theorem inner_beta_nu_eq {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (K : Subgroup ↥L) [K.Normal] [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (diffβ : (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
        - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {j : Fin (n + 1)} (hj0 : j ≠ 0) (hj_ind : j ≠ ind1H)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hagree_j : ν (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ))
        - d j • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      = H71.τ ⟨ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)
          - d j • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support j⟩)
    (hζ0norm : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) = 1) :
    ClassFunction.inner
        (H71.τ ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
            - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), diffβ⟩)
        (ν (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)))
      = star (d j) * (ClassFunction.inner
          (H71.τ ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), diffβ⟩)
          (ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))) + 1) := by
  have key := inner_beta_nuDiff H71 hτ K θ hinj d psi_support hind0 diffβ hj0 hj_ind ν hagree_j
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_smul_right, hζ0norm, mul_one] at key
  linear_combination key

/-- **Peterfalvi (7.8.a), `Γ ⊥ S^ν`** (the `Gamma_orth_nu` field of `BetaDecomp`).  For the residual
`Γ = β − (1_G − ζ_0^ν + a · W)` with `a = ⟨β, ζ_0^ν⟩ + 1` and `W = Σ_{i≠ind1H} (ζ_i(1)/(ζ_0(1)‖ζ_i‖²))
ζ_i^ν`, every `ζ_j^ν` (`j ≠ ind1H`) is orthogonal to `Γ`:

* `⟨1_G, ζ_j^ν⟩ = 0` (`orth_one`), `⟨ζ_0^ν, ζ_j^ν⟩ = ⟨ζ_0, ζ_j⟩` (`ν`-isometry), `⟨W, ζ_j^ν⟩ =
  ζ_j(1)/ζ_0(1)` (`inner_weightedNuSum_nu`);
* `j = 0`: `⟨β, ζ_0^ν⟩ = a − 1`, `⟨ζ_0, ζ_0⟩ = 1`, so `(a−1) + 1 − a·1 = 0`;
* `j ≠ 0`: `⟨β, ζ_j^ν⟩ = star(d_j)·a` (`inner_beta_nu_eq`), `⟨ζ_0, ζ_j⟩ = 0`, and `star(d_j) = d_j =
  ζ_j(1)/ζ_0(1)` (`induce_apply_one_star`), so `d_j·a − a·d_j = 0`. -/
theorem betaDecomp_gamma_orth_nu {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (K : Subgroup ↥L) [K.Normal] [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (d : Fin (n + 1) → ℂ)
    (hd : ∀ i, d i = ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L) /
      ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L))
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (diffβ : (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
        - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu : ∀ φ ψ : ClassFunction ↥L ℂ, ClassFunction.inner (ν φ) (ν ψ) = ClassFunction.inner φ ψ)
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
        = H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
            - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩)
    (horth1 : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
        (Hypothesis71.constOne G) = 0)
    (hζ0norm : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) = 1)
    (β : ClassFunction G ℂ)
    (hβ : β = H71.τ ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
      - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), diffβ⟩)
    (a : ℂ) (ha : a = ClassFunction.inner β (ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))) + 1)
    (W : ClassFunction G ℂ)
    (hW : W = ∑ i ∈ Finset.univ.erase ind1H,
      (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L) /
        (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) *
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) : ℂ) •
        ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    {j : Fin (n + 1)} (hj : j ≠ ind1H) :
    ClassFunction.inner (β - (Hypothesis71.constOne G
        - ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) + a • W))
      (ν (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ))) = 0 := by
  have hz0 : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero K (θ 0)
  have hc1 : ClassFunction.inner (Hypothesis71.constOne G)
      (ν (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ))) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, horth1 j hj, star_zero]
  have hWj : ClassFunction.inner W (ν (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)))
      = ClassFunction.induce K (θ j : ClassFunction ↥K ℂ) (1 : ↥L) /
        ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) := by
    rw [hW]; exact inner_weightedNuSum_nu K θ hinj ν hnu hj
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, hnu, hc1, hWj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [hζ0norm, div_self hz0, ha]; ring
  · rw [induce_family_orthogonal_of_injective K θ hinj 0 j (Ne.symm hj0), hβ,
      inner_beta_nu_eq H71 hτ K θ hinj d psi_support hind0 diffβ hj0 hj ν (hagree j hj0 hj) hζ0norm,
      ← hβ, ← ha]
    have hstar : star (d j) = ClassFunction.induce K (θ j : ClassFunction ↥K ℂ) (1 : ↥L) /
        ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) := by
      rw [hd j, star_div₀, induce_apply_one_star, induce_apply_one_star]
    rw [hstar]; ring

/-- **Peterfalvi (7.8.a), `Γ ⊥ 1_G`** (the `Gamma_orth_one` field of `BetaDecomp`).  For the residual
`Γ = β − (1_G − ζ_0^ν + a · W)`, `⟨Γ, 1_G⟩ = ⟨β,1_G⟩ − ⟨1_G,1_G⟩ + ⟨ζ_0^ν,1_G⟩ − a⟨W,1_G⟩`, where
`⟨β,1_G⟩ = ⟨Ind 1_K − ζ_0, 1_L⟩ = 1 − 0 = 1` (`inner_tau_supported_constOne` +
`inner_induce_trivialChar_constOne_eq_one`/`inner_induce_constOne_eq_zero`), `⟨1_G,1_G⟩ = 1`,
`⟨ζ_0^ν,1_G⟩ = 0` (`orth_one`), and `⟨W,1_G⟩ = 0` (`orth_one` for each summand) — giving
`1 − 1 + 0 − 0 = 0`. -/
theorem betaDecomp_gamma_orth_one {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (K : Subgroup ↥L) [K.Normal] [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K)
    (diffβ : (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
        - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (horth1 : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
        (Hypothesis71.constOne G) = 0)
    (β : ClassFunction G ℂ)
    (hβ : β = H71.τ ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
      - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), diffβ⟩)
    (a : ℂ) (W : ClassFunction G ℂ)
    (hW : W = ∑ i ∈ Finset.univ.erase ind1H,
      (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L) /
        (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L) *
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) : ℂ) •
        ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) :
    ClassFunction.inner (β - (Hypothesis71.constOne G
        - ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) + a • W))
      (Hypothesis71.constOne G) = 0 := by
  have hθ0 : θ 0 ≠ trivialIrreducibleCharacter ↥K := by
    intro h
    exact hind0 (hinj (by
      show ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
        = ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)
      rw [hzeta_ind1H, h]))
  have hβ1 : ClassFunction.inner β (Hypothesis71.constOne G) = 1 := by
    rw [hβ, inner_tau_supported_constOne, ClassFunction.inner_sub_left,
      show ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
        = ClassFunction.induce K (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) from by
        rw [hzeta_ind1H],
      inner_induce_trivialChar_constOne_eq_one, inner_induce_constOne_eq_zero K (θ 0) hθ0, sub_zero]
  have hW0 : ClassFunction.inner W (Hypothesis71.constOne G) = 0 := by
    rw [hW, inner_sum_left]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [ClassFunction.inner_smul_left, horth1 i (Finset.mem_erase.mp hi).1, mul_zero]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, hβ1, hW0, horth1 0 (Ne.symm hind0),
    Hypothesis71.constOne_inner_self_eq_one]
  ring

/-- **The (7.8.c) collapse of the (7.7.a) sum to a single term.**  If, in the `(7.7.a)`
decomposition `χ^ρ(x) = ∑_{i ≥ 1} (c̄_i/‖ζ_i‖²) ζ_i(x)`, all coefficients `c_i` (`i ≥ 1`) vanish
except at one index `i₁`, and the distinguished member satisfies `ζ_{i₁}(x) = ‖ζ_{i₁}‖²`
(the induced-principal-character identity, both `= e`), then the sum collapses to `star(c_{i₁})`.

This is the algebraic core of Peterfalvi (7.8.c): with `ζ_{i₁} = Ind_H^L 1_H` and
`c_{i₁} = (β,χ)`, `induce_trivialChar_apply_eq_index`/`_normSq_eq_index` give the hypothesis
`ζ_{i₁}(x) = ‖ζ_{i₁}‖²`, and `χ^ρ(x) = star(β,χ)`. -/
theorem sum_collapse_to_single [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (c : Fin (n + 1) → ℂ)
    {x : L} {i₁ : Fin (n + 1)} (hi₁ : (0 : Fin (n + 1)) < i₁)
    (hvanish : ∀ i ∈ Finset.Ioi (0 : Fin (n + 1)), i ≠ i₁ → c i = 0)
    (hcrux : ζ i₁ x = ClassFunction.inner (ζ i₁) (ζ i₁))
    (hnorm : ClassFunction.inner (ζ i₁) (ζ i₁) ≠ 0) :
    (∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (c i) / ClassFunction.inner (ζ i) (ζ i)) * ζ i x) = star (c i₁) := by
  rw [Finset.sum_eq_single_of_mem i₁ (Finset.mem_Ioi.mpr hi₁)
      (fun i hi hne => by rw [hvanish i hi hne]; simp), hcrux]
  exact div_mul_cancel₀ _ hnorm

/-- **The coherence vanishing of a (7.7.a) coefficient** (Peterfalvi (7.8.c)).  If `χ` is orthogonal
to both `a` and `b` in `CF(G)`, then `(a − d·b, χ) = 0`.  In (7.8.c), with `a = ζ_i^ν`, `b = ζ_0^ν`
(`ζ_i, ζ_0 ∈ S`) and the coherence agreement `(ζ_i − d_i ζ_0)^τ = ζ_i^ν − d_i ζ_0^ν`, the hypothesis
`χ ⊥ S^ν` makes the coefficient `c_i = ((ζ_i − d_i ζ_0)^τ, χ)` vanish for the non-distinguished
indices. -/
theorem inner_sub_smul_left_eq_zero {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {a b χ : ClassFunction G ℂ} {d : ℂ}
    (ha : ClassFunction.inner χ a = 0) (hb : ClassFunction.inner χ b = 0) :
    ClassFunction.inner (a - d • b) χ = 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    inner_conj_symm χ a, ha, star_zero, inner_conj_symm χ b, hb, star_zero, mul_zero, sub_zero]

/-- **Discharge of the (7.8.c.i) certificate for an induced family** (Peterfalvi (7.8.c)).  With the
distinguished `ζ = Ind_K^L θ_0` at index `0` (so the induced principal character `Ind_K^L 1_K` is at
some `ind1H ≠ 0`), `χ` orthogonal to `S^ν` (`hortho`), and the coherence agreement
`(ζ_i − d_i ζ_0)^τ = ζ_i^ν − d_i ζ_0^ν` for the non-distinguished, non-`ind1H` indices (`hagree`),
the `(7.7.a)` decomposition collapses to the single `ind1H` term: every other coefficient vanishes
(`inner_sub_smul_left_eq_zero`), and the surviving term simplifies via `ζ_{ind1H}(x) = ‖ζ_{ind1H}‖²`
(`induce_trivialChar_apply_eq_index`/`_normSq_eq_index`, both `= [L:K]`).  Hence
`χ^ρ(x) = star((ζ_{ind1H} − d_{ind1H} ζ_0)^τ, χ)`; with `d_{ind1H} = 1` this is `star(β,χ)`. -/
theorem chiRho_eq_inner_beta_induced {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (K : Subgroup ↥L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L)
        = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L))
    (hAconj : ∀ g h : ↥L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hAK_off : ∀ y : ↥L, y ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L → y ∈ K)
    (hA_one : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
    (hortho : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner χ (ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) = 0)
    {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x = star (ClassFunction.inner (H71.τ
      ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
          - d ind1H • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ),
        psi_support ind1H⟩) χ) := by
  classical
  rw [chiRho_decomp_induced H71 K θ d psi_support hinj hcover hdeg hAconj hAK_off hA_one χ hx]
  have hxK : x ∈ K := hAK_off x (by rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hx)
  refine sum_collapse_to_single (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
    (fun i => ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ)
    (Fin.pos_iff_ne_zero.mpr hind1H) ?_ ?_ (induce_norm_ne_zero K (θ ind1H))
  · -- the non-`ind1H` coefficients vanish by coherence
    intro i hi hne
    show ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ = 0
    rw [hagree i (Finset.mem_Ioi.mp hi).ne' hne]
    exact inner_sub_smul_left_eq_zero (hortho i hne) (hortho 0 (Ne.symm hind1H))
  · -- the distinguished term: `ζ_{ind1H}(x) = ‖ζ_{ind1H}‖² = [L:K]`
    show ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ) x
      = ClassFunction.inner (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
          (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
    rw [hzeta_ind1H,
      show ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
        = trivialClassFunction ↥K from rfl,
      induce_trivialChar_apply_eq_index K hxK, induce_trivialChar_normSq_eq_index K]

/-- **Construction of `Hypothesis78` from coherence data** (Peterfalvi (7.8)).  Given the
`(7.1)`/`(7.6)` data (`H71`, `hτ`, `H ⊴ L`, `A = H^#`), an enumerating family `θ` of the distinct
induced characters with the **distinguished** member `ζ` at index `0` and the induced principal
`Ind 1_H` at `ind1H`, together with the **coherence inputs** of `(7.8)` — the coherent isometric
extension `ν` and the agreement `τ(ψ_i) = ν ζ_i − d_i ν ζ_0` on `S` — the entire `Hypothesis78`
structure is built, *including* the `(7.8.c.i)` certificate `chiRho_eq_inner_beta`, which is
discharged by `chiRho_eq_inner_beta_induced`.

The distinguished `ζ = ζ_0` has `ζ(1) = (Ind 1_H)(1)` (`hdeg_match`), forcing `d_{ind1H} = 1`, so the
certificate's `β = τ(Ind 1_H − ζ)` matches the family-difference `τ(ζ_{ind1H} − ζ_0)`.  Together with
`hypothesis76OfFamily` this realizes the issue-1013 goal: `Hypothesis78` (the §7 floor cited by
`(12.16)` / `(14.11)`) is constructible from `(7.1)` + coherence alone, with no certificate assumed. -/
noncomputable def hypothesis78OfDade
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥(H.subgroupOf L))
    (hdeg_match : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu_isometry : ∀ φ ψ : ClassFunction ↥L ℂ,
      ClassFunction.inner (ν φ) (ν ψ) = ClassFunction.inner φ ψ)
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          - d i • ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) :
    Hypothesis78 G A L := by
  classical
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  -- `d_{ind1H} = 1` from the degree match `ζ_0(1) = ζ_{ind1H}(1)`.
  have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (θ 0)
  have hd1 : d ind1H = 1 := by
    have h := hdeg ind1H
    rw [← hdeg_match] at h
    have h2 : d ind1H * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = 1 * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) := by
      rw [one_mul, ← h]
    exact mul_right_cancel₀ hz0 h2
  -- `ζ_{ind1H} − ζ_0` is supported on `A` (difference of induced characters of equal degree).
  have hdiff : (ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
      - ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    have h := induce_diff_support (θ ind1H) (θ 0) 1 (by rw [one_mul, ← hdeg_match])
    rw [one_smul] at h
    refine h.trans ?_
    intro x hx
    rw [Set.mem_diff, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_iff H hAH x).mpr
      ⟨hx.1, fun h1 => hx.2 (OneMemClass.coe_eq_one.mp h1)⟩
  refine
    { hyp76 := hypothesis76OfFamily H71 hτ H hHL hHnorm hAH θ hinj hcover
      ind1H := ind1H
      zetaDistinct := 0
      zetaDistinct_ne_ind1H := Ne.symm hind1H
      zeta_one_eq_ind1H_one := hdeg_match
      diff_support := hdiff
      nu := ν
      nu_isometry := hnu_isometry
      chiRho_eq_inner_beta := fun χ _ hortho {x} hx => by
        -- Reduce `hyp76.hyp71` to `H71` (`rfl`) so `chiRho_eq_inner_beta_induced` rewrites the LHS.
        rw [show (hypothesis76OfFamily H71 hτ H hHL hHnorm hAH θ hinj hcover).hyp71 = H71 from rfl,
          chiRho_eq_inner_beta_induced H71 (H.subgroupOf L) θ d psi_support hinj hcover hdeg
            (supportInSubgroup_sharp_conj_mem_iff H hAH hHnorm)
            (fun y => supportInSubgroup_sharp_subset_subgroupOf H hAH)
            (one_not_mem_supportInSubgroup_sharp H hAH) ind1H hind1H hzeta_ind1H ν χ hagree hortho hx]
        -- Bridge the `(7.7.a)` coefficient `d_{ind1H}` (`= 1`) to the bare difference `ζ_{ind1H} − ζ_0`.
        refine congrArg star (congrArg (ClassFunction.inner · χ) (congrArg H71.τ ?_))
        apply Subtype.ext
        show ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
            - d ind1H • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) = _
        rw [hd1, one_smul]
        rfl }

/-- **Integrality of the `(7.8.a)` coefficient `a`** (Peterfalvi (7.8.a)).  The weighted-sum
coefficient `a = (β, ζ_0^ν) + 1` is an integer: `β = τ(Ind 1_H − ζ)` is a virtual character (from
`(2.6.b)` Dade preservation, packaged in `beta_mem_ZIrr_of_sourceDiff_mem_ZIrr`, given the source
difference `Ind 1_H − ζ ∈ ℤ[Irr L]`), `ζ_0^ν = ν ζ ∈ ℤ[Irr G]` is the coherent image
(`nu_mem_ZIrr_of_isCoherent`), and `inner_mem_ZIrr_int` makes their inner product an integer.
Supplies the `a : ℤ` field of `BetaDecomp` together with the displayed value `(β, ζ_0^ν) + 1`. -/
theorem exists_betaDecomp_a {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L)
    (hdiffZ : H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L)
    (hζ0nuZ : H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G) :
    ∃ a : ℤ, (a : ℂ) = ClassFunction.inner H78.beta
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) + 1 := by
  obtain ⟨m, hm⟩ :=
    ClassFunction.inner_mem_ZIrr_int (H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr hdiffZ) hζ0nuZ
  exact ⟨m + 1, by push_cast; rw [hm]⟩

/-- **Peterfalvi (7.8.b) coefficient identification, generic index** (`case A`, `ζ_0 = ζ`).  For the
`(7.7.a)` coefficient `c_i = (ψ_i^τ, ζ_0^ν)` with `χ = ζ_0^ν` (the distinguished `ζ = ζ_0` at index
`0`), the coherence agreement `ψ_i^τ = ζ_i^ν − d_i ζ_0^ν` (for `i ≠ 0, ind1H`), the isometry of `ν`,
the family orthogonality `(ζ_i, ζ_0) = 0`, the normalization `‖ζ_0‖² = 1`, and `d_i` real, give
`c_i = −d_i`.  This is the off-distinguished coefficient feeding the (7.8.b) double sum. -/
theorem cCoeff_nu_zeta_zero_eq_neg_d {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    {ind1H : Fin (H76.n + 1)}
    (hagree : ∀ i : Fin (H76.n + 1), i ≠ 0 → i ≠ ind1H →
      H76.hyp71.τ (H76.psiSupp i) = ν (H76.zeta i) - H76.d i • ν (H76.zeta 0))
    (hiso : ∀ φ ψ : ClassFunction ↥L ℂ,
      ClassFunction.inner (ν φ) (ν ψ) = ClassFunction.inner φ ψ)
    (horth : ∀ i : Fin (H76.n + 1), i ≠ 0 →
      ClassFunction.inner (H76.zeta i) (H76.zeta 0) = 0)
    (hnorm : ClassFunction.inner (H76.zeta 0) (H76.zeta 0) = 1)
    (i : Fin (H76.n + 1)) (hi0 : i ≠ 0) (hind : i ≠ ind1H) :
    H76.cCoeff (ν (H76.zeta 0)) i = - H76.d i := by
  unfold Hypothesis76.cCoeff
  rw [hagree i hi0 hind, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    hiso, hiso, horth i hi0, hnorm, mul_one, zero_sub]

/-- **Peterfalvi (7.8.b) coefficient identification, the `Ind 1_H` index.**  At `i = ind1H`, the
`(7.7.a)` coefficient `c_{ind1H} = (ψ_{ind1H}^τ, ζ_0^ν)` equals `(β, ζ_0^ν)`: with `d_{ind1H} = 1`
and `zetaDistinct = 0`, the supported difference `ψ_{ind1H} = ζ_{ind1H} − ζ_0` coincides (as a member
of `CF(L,A)`) with `Ind 1_H − ζ`, whose Dade image is `β`.  This is the distinguished coefficient
feeding the (7.8.b) double sum; combined with `exists_betaDecomp_a` it gives `c_{ind1H} = a − 1`. -/
theorem cCoeff_nu_zeta_zero_ind1H_eq {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hzd : H78.zetaDistinct = 0) (hd1 : H78.hyp76.d H78.ind1H = 1) :
    H78.hyp76.cCoeff (ν (H78.hyp76.zeta 0)) H78.ind1H =
      ClassFunction.inner H78.beta (ν (H78.hyp76.zeta 0)) := by
  have hsupp : H78.hyp76.psiSupp H78.ind1H = H78.indMinusZetaSupp := by
    apply Subtype.ext
    simp only [Hypothesis76.psiSupp_coe, Hypothesis78.indMinusZetaSupp, hd1, one_smul, hzd]
  unfold Hypothesis76.cCoeff Hypothesis78.beta
  rw [hsupp]

/-- **Orthogonality collapse of the `(7.7.b)` double sum.**  When the induced family `ζ_i` is
pairwise orthogonal (`(ζ_i, ζ_j) = 0` for `i ≠ j`, true for the distinct induced characters by
Frobenius reciprocity), the `(7.7.b)` double sum splits into a diagonal part and a rank-one
correction: `‖χ^ρ‖² = Σ_i c̄_i c_i/‖ζ_i‖² − (Σ_i c̄_i ζ_i(1)/‖ζ_i‖²)(Σ_j c_j \overline{ζ_j(1)}/‖ζ_j‖²)/|L|`.
This is the shape used by (7.8.b) (`χ = ζ_0^ν`) before substituting the coefficients. -/
theorem chiRho_norm_sq_collapse {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (χ : ClassFunction G ℂ)
    (horth : ∀ i j : Fin (H76.n + 1), i ≠ j →
      ClassFunction.inner (H76.zeta i) (H76.zeta j) = 0) :
    ClassFunction.inner (H76.hyp71.chiRhoCF χ) (H76.hyp71.chiRhoCF χ) =
      (∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        star (H76.cCoeff χ i) * H76.cCoeff χ i / H76.zetaNormSq i)
      - (∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          star (H76.cCoeff χ i) * H76.zeta i 1 / H76.zetaNormSq i)
        * (∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
            H76.cCoeff χ j * star (H76.zeta j 1) / H76.zetaNormSq j)
        / (Nat.card L : ℂ) := by
  rw [H76.chiRho_norm_sq_double_sum χ]
  have hsplit : ∀ i j : Fin (H76.n + 1),
      star (H76.cCoeff χ i) * H76.cCoeff χ j / (H76.zetaNormSq i * H76.zetaNormSq j) *
          (ClassFunction.inner (H76.zeta i) (H76.zeta j)
            - H76.zeta i 1 * star (H76.zeta j 1) / (Nat.card L : ℂ)) =
        star (H76.cCoeff χ i) * H76.cCoeff χ j / (H76.zetaNormSq i * H76.zetaNormSq j) *
            ClassFunction.inner (H76.zeta i) (H76.zeta j)
          - (star (H76.cCoeff χ i) * H76.zeta i 1 / H76.zetaNormSq i) *
            (H76.cCoeff χ j * star (H76.zeta j 1) / H76.zetaNormSq j) / (Nat.card L : ℂ) := by
    intro i j; ring
  simp only [hsplit, Finset.sum_sub_distrib]
  congr 1
  · -- diagonal collapse via orthogonality
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [horth i j (Ne.symm hji), mul_zero]) (fun hi' => absurd hi hi')]
    rw [show ClassFunction.inner (H76.zeta i) (H76.zeta i) = H76.zetaNormSq i from rfl]
    field_simp
  · -- rank-one factoring
    rw [Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]

/-- **Diagonal-sum split at `ind1H`** for the (7.8.b) collapse.  Splitting the `Ioi 0` diagonal sum
`Σ_i c̄_i c_i / N_i` at the distinguished index `ind1H`, where `c_{ind1H} = cval` and `c_i = −d_i`
for `i ≠ 0, ind1H`, gives `c̄val·cval/N_{ind1H} + Σ_{i ≠ ind1H} d̄_i d_i / N_i` (the sign cancels).
This isolates the `(a−1)²/e` term from the off-distinguished `d_i`-sum. -/
theorem sum_diag_split_ind1H {n : ℕ} (c N d : Fin (n + 1) → ℂ) (cval : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = cval)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i)) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * c i / N i =
      star cval * cval / N ind1H
        + ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, star (d i) * d i / N i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)), hc_ind1H]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
  rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, star_neg, neg_mul, mul_neg, neg_neg]

/-- **Arithmetic core of (7.8.b).**  With the collapsed norm `‖ζ^{νρ}‖² = t₁ − X²/(e·h)` where the
diagonal `t₁ = (a−1)²/e + G/e²` and the rank-one `X = (a−1) − G/e`, and the `(1.5.d)` degree-sum
value `G = e(h−1) − e²`, the norm equals the quadratic `u a² − 2 v a + w` of Peterfalvi (7.8.b),
with `u = (1/e)(1−1/h)`, `v = 1/h`, `w = 1 − e/h`.  Pure field identity (verified by `ring`). -/
theorem normEstimate_matching (a e h G : ℝ) (he : e ≠ 0) (hh : h ≠ 0)
    (hG : G = e * (h - 1) - e ^ 2) :
    ((a - 1) ^ 2 / e + G / e ^ 2) - ((a - 1) - G / e) ^ 2 / (e * h) =
      (1 / e) * (1 - 1 / h) * a ^ 2 - 2 * (1 / h) * a + (1 - e / h) := by
  subst hG
  field_simp
  ring

/-- **Diagonal sum evaluation for (7.8.b)** (`term₁`).  With `c_{ind1H} = a−1`, `c_i = −d_i`
(`i ≠ 0, ind1H`), `N_{ind1H} = e`, `d_i = P_i/e`, and `a` / the `d_i` real, the diagonal sum
`Σ_i c̄_i c_i / N_i` evaluates to `(a−1)²/e + (Σ_{i ≠ ind1H} P_i²/N_i)/e²`. -/
theorem term1_eval_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (d i) = d i)
    (hd : ∀ i, d i = P i / e) (hN_ind1H : N ind1H = e) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * c i / N i =
      (a - 1) ^ 2 / e
        + (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e ^ 2 := by
  rw [sum_diag_split_ind1H c N d (a - 1) hind hc_ind1H hc_rest, hN_ind1H, ha1_real, ← pow_two]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd_real i, ← pow_two, hd i, div_pow]
  ring

/-- **Rank-one sum evaluation for (7.8.b)** (`X`).  With the same data, the rank-one factor
`Σ_i c̄_i P_i / N_i` evaluates to `(a−1) − (Σ_{i ≠ ind1H} P_i²/N_i)/e` (the `Ind 1_H` term gives
`(a−1)·e/e = a−1`; the off-distinguished terms give `−d_i P_i/N_i = −P_i²/(e N_i)`). -/
theorem rank1_eval_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (d i) = d i)
    (hd : ∀ i, d i = P i / e) (hN_ind1H : N ind1H = e) (hP_ind1H : P ind1H = e) (he : e ≠ 0) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * P i / N i =
      (a - 1) - (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)),
    hc_ind1H, ha1_real, hP_ind1H, hN_ind1H, mul_div_assoc, div_self he, mul_one, sub_eq_add_neg]
  congr 1
  rw [show (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, star (c i) * P i / N i)
        = ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i * (-(1 / e)) from
      Finset.sum_congr rfl fun i hi => by
        obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
        rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, star_neg, hd_real i, hd i]; ring,
    ← Finset.sum_mul]
  ring

end OddOrder.Peterfalvi.S09.Cert
