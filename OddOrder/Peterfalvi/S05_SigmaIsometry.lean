/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_SignedTripleGrid

/-!
# Peterfalvi §5: the `σ`-isometry of Theorem (3.2) and its Galois theory (3.6)-(3.9)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§3 (repo chunk 04.3), results (3.2) and (3.6)-(3.9).

組合せ論コア ((3.3)-(3.5) signed-triple/sunflower/grid) は
`S05_SignedTripleGrid.lean` (import 済) に prefix-split (2026-06-11, 粒度規約)。
本ファイル: Peterfalvi (1.3)(a) masking engine / index bridge `Ĉ₁×Ĉ₂ ≃ Irr(W)` /
**(3.2) σ-isometry 本体** (`sigma`, `sigma_inner`, `sigma_eq_tau`, `exists_sigma`) /
(3.6)-(3.8) 係数 grid `sigmaCoeff`・`sigmaNC` / **(3.9)(a)(b)(c)** (§6-keystone
`eq_sigma_of_apply_eq_on_V`, Galois 同変性)。全結果 sorry-free・axiom-clean (凍結)。
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-! ### Peterfalvi (1.3)(a) engine: vanishing on `A` from orthogonality to `CF(H, A)`

The combinatorial heart of Peterfalvi (1.3): a class function `f` orthogonal to *every* class
function supported on a conjugation-closed set `A` must vanish on `A`.  Test against the "masking"
`f · 1_A` — itself a class function precisely because `A` is conjugation-closed — for which
`⟨f · 1_A, f⟩ = ⅟|H| · ∑_{a ∈ A} |f(a)|²`.  This sum of nonnegative reals is `0` only if every
`f(a) = 0`.  This is the orthogonal-complement fact `CF(H, A)^⊥ = CF(H, H ∖ A)` of (1.3)(a). -/

open scoped Classical in
/-- **Peterfalvi (1.3)(a) engine** (vanishing on `A`).  If `f` is orthogonal to every class function
supported on the conjugation-closed set `A`, then `f` vanishes on `A`. -/
theorem eq_zero_of_mem_of_inner_supported_eq_zero
    {H : Type*} [Group H] [Fintype H] [Invertible (Nat.card H : ℂ)]
    {A : Set H} (hA : ∀ x ∈ A, ∀ h : H, h * x * h⁻¹ ∈ A)
    {f : ClassFunction H ℂ}
    (hf : ∀ φ : ClassFunction H ℂ, φ.support ⊆ A → ClassFunction.inner φ f = 0)
    {a : H} (ha : a ∈ A) : f a = 0 := by
  classical
  -- conjugation-closedness is an equivalence (conjugation permutes `A`)
  have hAconj : ∀ g h : H, h * g * h⁻¹ ∈ A ↔ g ∈ A := fun g h => by
    refine ⟨fun hc => ?_, fun hc => hA g hc h⟩
    have := hA _ hc h⁻¹
    simpa [mul_assoc] using this
  -- the masking `m = f · 1_A`, a class function since `A` is conjugation-closed
  have hconj : ∀ g h : H, (if h * g * h⁻¹ ∈ A then f (h * g * h⁻¹) else 0)
      = (if g ∈ A then f g else (0 : ℂ)) := fun g h => by
    by_cases hg : g ∈ A
    · rw [if_pos ((hAconj g h).mpr hg), if_pos hg, f.conj_eq]
    · rw [if_neg (fun hc => hg ((hAconj g h).mp hc)), if_neg hg]
  let m : ClassFunction H ℂ := ⟨fun x => if x ∈ A then f x else 0, hconj⟩
  have hmval : ∀ g, m g = if g ∈ A then f g else 0 := fun _ => rfl
  have hmsupp : m.support ⊆ A := fun g hg => by
    by_contra hgA
    exact (ClassFunction.mem_support.mp hg) (by rw [hmval, if_neg hgA])
  -- `innerSum m f = ↑(∑_g 1_A(g) · ‖f g‖²)`, a sum of nonnegative reals
  have he : ClassFunction.innerSum m f
      = ((∑ g : H, (if g ∈ A then Complex.normSq (f g) else 0) : ℝ) : ℂ) := by
    rw [ClassFunction.innerSum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hmval]
    by_cases hg : g ∈ A
    · rw [if_pos hg, if_pos hg, Complex.star_def, Complex.mul_conj]
    · rw [if_neg hg, if_neg hg, zero_mul, Complex.ofReal_zero]
  -- `⟨m, f⟩ = 0 ⟹ ∑ ‖f‖²·1_A = 0 ⟹ each term 0`
  have h0 : ClassFunction.innerSum m f = 0 := by
    rw [← ClassFunction.card_mul_inner, hf m hmsupp, mul_zero]
  rw [he, Complex.ofReal_eq_zero] at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun g _ => by
    by_cases hg : g ∈ A
    · rw [if_pos hg]; exact Complex.normSq_nonneg _
    · rw [if_neg hg]).mp h0 a (Finset.mem_univ a)
  rw [if_pos ha] at hterm
  exact Complex.normSq_eq_zero.mp hterm

/-- The linear functional `φ ↦ ⟨φ, f⟩` on class functions (linear in the *left* argument,
since `⟨·, ·⟩` is conjugate-linear on the right).  Used to phrase "`f ⊥ CF(H, A)`" as the
vanishing of a linear map on a basis. -/
def innerLeftFunctional {H : Type*} [Group H] [Fintype H] [Invertible (Nat.card H : ℂ)]
    (f : ClassFunction H ℂ) : ClassFunction H ℂ →ₗ[ℂ] ℂ where
  toFun φ := ClassFunction.inner φ f
  map_add' a b := ClassFunction.inner_add_left a b f
  map_smul' c a := by simp only [ClassFunction.inner_smul_left, RingHom.id_apply, smul_eq_mul]

@[simp] theorem innerLeftFunctional_apply {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (f φ : ClassFunction H ℂ) :
    innerLeftFunctional f φ = ClassFunction.inner φ f := rfl

/-- **Abstract (3.8) core.** A `ℂ`-valued grid `a : ι × κ → ℂ` whose mixed differences vanish
(`a(i,j) + a(i',j') = a(i,j') + a(i',j)`, the (3.7) identity) and whose nonzero set is *smaller*
than `min |ι| |κ|` is identically zero.  Such a grid is additively separable, so its rows differ by
a column-independent constant: if two rows differ, every column carries a nonzero entry (`≥ |κ|`
nonzeros); otherwise all rows are equal, and a single nonzero entry fills a whole column (`≥ |ι|`
nonzeros).  Either way `min |ι| |κ| ≤ #support`, contradicting the hypothesis. -/
theorem grid_eq_zero_of_ncard_support_lt {ι κ : Type*} [Finite ι] [Finite κ]
    (a : ι × κ → ℂ)
    (hadd : ∀ i i' (j j' : κ), a (i, j) + a (i', j') = a (i, j') + a (i', j))
    (hlt : {x | a x ≠ 0}.ncard < min (Nat.card ι) (Nat.card κ))
    (x : ι × κ) : a x = 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite _
  haveI : Fintype κ := Fintype.ofFinite _
  haveI : Fintype ↥{x : ι × κ | a x ≠ 0} := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card] at hlt
  by_contra hx
  set S := Finset.univ.filter (fun x => a x ≠ 0) with hS
  have hmem : ∀ {y : ι × κ}, y ∈ S ↔ a y ≠ 0 := by
    intro y; rw [hS, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ y)
  by_cases hrows : ∀ (i i' : ι) (j : κ), a (i, j) = a (i', j)
  · -- all rows equal: the column through `x` is entirely nonzero, so `|ι| ≤ #S`
    have hcol : (Finset.univ.image fun i => (i, x.2)) ⊆ S := by
      intro y hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
      obtain ⟨i, rfl⟩ := hy
      rw [hmem, hrows i x.1 x.2]
      exact hx
    have hcard : Fintype.card ι ≤ S.card := by
      have hinj : Function.Injective fun i : ι => (i, x.2) := fun a b h => by simpa using h
      calc Fintype.card ι = (Finset.univ.image fun i => (i, x.2)).card := by
            rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
        _ ≤ S.card := Finset.card_le_card hcol
    omega
  · -- two rows differ in some column ⟹ they differ in *every* column ⟹ `|κ| ≤ #S`
    push Not at hrows
    obtain ⟨i, i', j₀, hjj⟩ := hrows
    have hdiff : ∀ j, a (i, j) ≠ a (i', j) := fun j hj => by
      apply hjj
      have h1 := hadd i i' j j₀
      linear_combination hj - h1
    -- every column `j` contains a nonzero entry, so `S.image (·.2) = univ`
    have himg : S.image (fun y => y.2) = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro j
      rw [Finset.mem_image]
      by_cases h : a (i, j) = 0
      · exact ⟨(i', j), hmem.mpr fun hi' => hdiff j (h.trans hi'.symm), rfl⟩
      · exact ⟨(i, j), hmem.mpr h, rfl⟩
    have hcard : Fintype.card κ ≤ S.card := by
      calc Fintype.card κ = (S.image fun y => y.2).card := by rw [himg, Finset.card_univ]
        _ ≤ S.card := Finset.card_image_le
    omega

/- 3.5.1 (cont.): the virtual characters `β_{ij} = Ind_W^G α_{ij} - 1_G` -/

namespace TICyclicHypothesis

/-- **Peterfalvi (3.5.1)**: `β_{ij} = Ind_W^G α_{ij} - 1_G` (for `i, j ≥ 1`). -/
noncomputable def beta (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction G ℂ :=
  app.tau.toDadeMap (hyp.alpha hVeq χ₁ χ₂) - trivialClassFunction G

/-- `β_{ij} ∈ ℤ[Irr G]`: `Ind_W^G` preserves virtual characters (`α_{ij} ∈ ℤ[Irr W]`) and `1_G`
is a character. -/
theorem beta_mem_ZIrr (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.beta hVeq app χ₁ χ₂ ∈ ZIrr G :=
  Submodule.sub_mem _
    (app.tau.maps_virtualCharacter (hyp.alpha hVeq χ₁ χ₂) (hyp.alpha_mem_ZIrr hVeq χ₁ χ₂))
    (trivialClassFunction_isIrreducible.mem_ZIrr)

/-- **Peterfalvi (3.5.2)** input: every `β_{ij}` takes the value `-1` at `1 ∈ G`.  Indeed
`Ind_W^G α_{ij}(1) = [G : W] · α_{ij}(1) = 0` because `α_{ij}` vanishes on `W₁ ⊇ {1}`, so
`β_{ij}(1) = 0 - 1_G(1) = -1`.  In particular all the `β_{ij}` agree at `1`, which is what powers
the no-negatives half of `L(ij, i'j')` (Peterfalvi's `2χ₃ = Ind(α₁₁ - α₁₂)` vanishing at `1`). -/
theorem beta_apply_one (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.beta hVeq app χ₁ χ₂ : ClassFunction G ℂ) 1 = -1 := by
  change (app.tau.toDadeIsometryData.toDadeMap (hyp.alpha hVeq χ₁ χ₂) -
    trivialClassFunction G) 1 = -1
  rw [ClassFunction.sub_apply, trivialClassFunction_apply,
    hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq χ₁ χ₂),
    ClassFunction.induce_apply_one, hyp.alpha_coe,
    hyp.alphaCF_eq_zero_of_mem_W1_subgroupOf χ₁ χ₂ (Subgroup.one_mem _), mul_zero, zero_sub]

open Classical in
/-- **Peterfalvi (3.5.1)**: the Gram matrix of the `β_{ij}` family (`i, j ≥ 1`):
`⟨β_{ij}, β_{kl}⟩ = δ_{ik} + δ_{jl} + δ_{(ij),(kl)}`.  Subtracting `1_G` from the induced family
(whose Gram matrix is `tau_alpha_inner`) drops each entry by `1` (Frobenius
`tau_alpha_inner_trivial` and `⟨1_G, 1_G⟩ = 1`), giving `3` on the diagonal, `1` for one shared
index, and `0` when both indices differ. -/
theorem beta_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) =
      (if a₁ = b₁ then 1 else 0) + (if a₂ = b₂ then 1 else 0)
        + (if a₁ = b₁ ∧ a₂ = b₂ then 1 else 0) := by
  change ClassFunction.inner
      (app.tau.toDadeMap (hyp.alpha hVeq a₁ a₂) - trivialClassFunction G)
      (app.tau.toDadeMap (hyp.alpha hVeq b₁ b₂) - trivialClassFunction G) = _
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hyp.tau_alpha_inner hVeq app ha₁ ha₂ hb₁ hb₂,
    hyp.tau_alpha_inner_trivial hVeq app ha₁ ha₂,
    inner_conj_symm (app.tau.toDadeMap (hyp.alpha hVeq b₁ b₂)) (trivialClassFunction G),
    hyp.tau_alpha_inner_trivial hVeq app hb₁ hb₂, inner_trivialClassFunction_self]
  simp only [star_one]
  ring

/-- **Peterfalvi (3.5.1)**: `‖β_{ij}‖² = 3` for `i, j ≥ 1`. -/
theorem beta_inner_self (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app a₁ a₂) = 3 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ ha₁ ha₂]
  norm_num

/-- **Peterfalvi (3.5.1)**: `⟨β_{ij}, 1_G⟩ = 0` for `i, j ≥ 1` (Frobenius `⟨Ind α_{ij}, 1_G⟩ = 1`
cancels `⟨1_G, 1_G⟩ = 1`). -/
theorem beta_inner_trivial (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (trivialClassFunction G) = 0 := by
  change ClassFunction.inner
      (app.tau.toDadeMap (hyp.alpha hVeq a₁ a₂) - trivialClassFunction G)
      (trivialClassFunction G) = 0
  rw [ClassFunction.inner_sub_left, hyp.tau_alpha_inner_trivial hVeq app ha₁ ha₂,
    inner_trivialClassFunction_self, sub_self]

/-- **Peterfalvi (3.5.1)**: `β_{ij} = ∑_{χ ∈ A_{ij}} χ` for a set `A_{ij}` of three pairwise
orthogonal elements of `±(Irr(G) - {1_G})` (`i, j ≥ 1`).  This extracts the set `A_{ij}` from the
norm-`3` virtual character `β_{ij}` (`beta_mem_ZIrr`, `beta_inner_self = 3`, `beta_inner_trivial =
0`) via `exists_signedTriple_of_inner_self_three`.  It is the combinatorial starting point of
(3.5.2)-(3.5.5). -/
theorem exists_betaSet (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ∃ A : Finset (ClassFunction G ℂ),
      A.card = 3 ∧ (∀ x ∈ A, IsSignedNontrivialIrr x) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → ClassFunction.inner x y = 0) ∧
      hyp.beta hVeq app a₁ a₂ = ∑ x ∈ A, x :=
  exists_signedTriple_of_inner_self_three (hyp.beta_mem_ZIrr hVeq app a₁ a₂)
    (hyp.beta_inner_self hVeq app ha₁ ha₂) (hyp.beta_inner_trivial hVeq app ha₁ ha₂)

/-- `β_{ij}` packaged as a signed triple: `∃ A, IsSignedTriple β_{ij} A`. -/
theorem exists_isSignedTriple_beta (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ∃ A : Finset (ClassFunction G ℂ), IsSignedTriple (hyp.beta hVeq app a₁ a₂) A :=
  exists_isSignedTriple_of_inner_self_three (hyp.beta_mem_ZIrr hVeq app a₁ a₂)
    (hyp.beta_inner_self hVeq app ha₁ ha₂) (hyp.beta_inner_trivial hVeq app ha₁ ha₂)

open Classical in
/-- `⟨β_{ij}, β_{i'j'}⟩ = 1` when the two index pairs agree in **exactly one** coordinate
(`i = i', j ≠ j'` or `i ≠ i', j = j'`).  Immediate from the Gram matrix `beta_inner`. -/
theorem beta_inner_eq_one_of_one_shared (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hshared : (a₁ = b₁ ∧ a₂ ≠ b₂) ∨ (a₁ ≠ b₁ ∧ a₂ = b₂)) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) = 1 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ hb₁ hb₂]
  rcases hshared with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; norm_num
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; norm_num

open Classical in
/-- **Peterfalvi (3.5.2)** `L(ij, i'j')` for the `β_{ij}`: signed triples `A`, `A'` of two
`β`-characters whose index pairs share exactly one coordinate intersect in exactly one element and
admit no negated common element.  Combines `beta_inner_eq_one_of_one_shared`, the common value
`β(1) = -1` (`beta_apply_one`), and the abstract `IsSignedTriple.L_of_inner_one`. -/
theorem betaTriple_L (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hshared : (a₁ = b₁ ∧ a₂ ≠ b₂) ∨ (a₁ ≠ b₁ ∧ a₂ = b₂)) :
    ∃ A A' : Finset (ClassFunction G ℂ),
      IsSignedTriple (hyp.beta hVeq app a₁ a₂) A ∧ IsSignedTriple (hyp.beta hVeq app b₁ b₂) A' ∧
      (A ∩ A').card = 1 ∧ ∀ x ∈ A, -x ∉ A' := by
  obtain ⟨A, hA⟩ := hyp.exists_isSignedTriple_beta hVeq app ha₁ ha₂
  obtain ⟨A', hA'⟩ := hyp.exists_isSignedTriple_beta hVeq app hb₁ hb₂
  have hinner := hyp.beta_inner_eq_one_of_one_shared hVeq app ha₁ ha₂ hb₁ hb₂ hshared
  have hone : (hyp.beta hVeq app a₁ a₂) 1 = (hyp.beta hVeq app b₁ b₂) 1 := by
    rw [hyp.beta_apply_one, hyp.beta_apply_one]
  obtain ⟨hcard, hno⟩ := hA.L_of_inner_one hA' hinner hone
  exact ⟨A, A', hA, hA', hcard, hno⟩

open Classical in
/-- `⟨β_{ij}, β_{i'j'}⟩ = 0` when the two index pairs differ in **both** coordinates
(`i ≠ i'`, `j ≠ j'`).  Immediate from the Gram matrix `beta_inner`. -/
theorem beta_inner_eq_zero_of_both_diff (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hd₁ : a₁ ≠ b₁) (hd₂ : a₂ ≠ b₂) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) = 0 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ hb₁ hb₂, if_neg hd₁, if_neg hd₂, if_neg (fun h => hd₁ h.1)]
  norm_num

open Classical in
/-- **Peterfalvi (3.5.2)** `O(ij, i'j')` for the `β_{ij}`: signed triples `A`, `A'` of two
orthogonal `β`-characters (index pairs differing in both coordinates) satisfy
`|A ∩ A'| = |{x ∈ A : -x ∈ A'}|`.  Combines `beta_inner_eq_zero_of_both_diff` and the abstract
`IsSignedTriple.O_card_inter_eq`. -/
theorem betaTriple_O (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hd₁ : a₁ ≠ b₁) (hd₂ : a₂ ≠ b₂) :
    ∃ A A' : Finset (ClassFunction G ℂ),
      IsSignedTriple (hyp.beta hVeq app a₁ a₂) A ∧ IsSignedTriple (hyp.beta hVeq app b₁ b₂) A' ∧
      (A ∩ A').card = (A.filter (fun x => -x ∈ A')).card := by
  obtain ⟨A, hA⟩ := hyp.exists_isSignedTriple_beta hVeq app ha₁ ha₂
  obtain ⟨A', hA'⟩ := hyp.exists_isSignedTriple_beta hVeq app hb₁ hb₂
  exact ⟨A, A', hA, hA',
    hA.O_card_inter_eq hA' (hyp.beta_inner_eq_zero_of_both_diff hVeq app ha₁ ha₂ hb₁ hb₂ hd₁ hd₂)⟩

/- 3.5.3: `sup(w₁, w₂) ≥ 5` -/

/-- **Peterfalvi (3.5.3)**: `sup(w₁, w₂) ≥ 5`.  Both `w₁ = |W₁|` and `w₂ = |W₂|` are odd (dividing
the odd `|W|`), greater than `1` (`W₁`, `W₂` nontrivial), and coprime (Hypothesis (3.1)).  Were
both `≤ 4`, each would equal `3` (the only odd number in `(1, 4]`), contradicting coprimality
(`gcd 3 3 = 3 ≠ 1`).  Peterfalvi then assumes `w₁ ≥ 5` by the `W₁ ↔ W₂` symmetry. -/
theorem sup_card_ge_five (hyp : TICyclicHypothesis G) :
    5 ≤ Nat.card hyp.W1 ∨ 5 ≤ Nat.card hyp.W2 := by
  haveI : Finite G := Finite.of_fintype G
  have h1odd : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have h2odd : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have h1gt : 1 < Nat.card hyp.W1 :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
  have h2gt : 1 < Nat.card hyp.W2 :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
  by_contra h
  obtain ⟨hlt1, hlt2⟩ := not_or.mp h
  rw [not_le] at hlt1 hlt2
  obtain ⟨k, hk⟩ := h1odd
  obtain ⟨l, hl⟩ := h2odd
  have hc1 : Nat.card hyp.W1 = 3 := by omega
  have hc2 : Nat.card hyp.W2 = 3 := by omega
  have hcop := hyp.W_card_coprime
  rw [hc1, hc2] at hcop
  exact absurd hcop (by decide)

/- 3.5.1 (cont.) / 3.5.2: the fixed family of signed triples `A_{ij}` -/

/-- **Peterfalvi (3.5.1)**, family form: a fixed choice of signed-triple set `A_{ij}` for each
`β_{ij}` (`i, j ≥ 1`), indexed by pairs of nontrivial linear characters of `W₁`, `W₂`.  This is
the family the `(3.5.4)`-`(3.5.5)` combinatorics reason about. -/
noncomputable def Afam (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
    (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) : Finset (ClassFunction G ℂ) :=
  (hyp.exists_isSignedTriple_beta hVeq app p.2 q.2).choose

/-- `A_{ij}` is a signed triple for `β_{ij}`. -/
theorem Afam_isSignedTriple (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
    (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) :
    IsSignedTriple (hyp.beta hVeq app p.1 q.1) (hyp.Afam hVeq app p q) :=
  (hyp.exists_isSignedTriple_beta hVeq app p.2 q.2).choose_spec

open Classical in
/-- **Peterfalvi (3.5.2)** `L(ij, i'j')`, family form: `A_{ij}` and `A_{i'j'}` with index pairs
sharing exactly one coordinate intersect in one element, with no negated common element. -/
theorem Afam_L (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p p' : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}}
    {q q' : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}}
    (hshared : (p = p' ∧ q ≠ q') ∨ (p ≠ p' ∧ q = q')) :
    (hyp.Afam hVeq app p q ∩ hyp.Afam hVeq app p' q').card = 1 ∧
      ∀ x ∈ hyp.Afam hVeq app p q, -x ∉ hyp.Afam hVeq app p' q' := by
  refine (hyp.Afam_isSignedTriple hVeq app p q).L_of_inner_one
    (hyp.Afam_isSignedTriple hVeq app p' q') ?_ ?_
  · apply hyp.beta_inner_eq_one_of_one_shared hVeq app p.2 q.2 p'.2 q'.2
    rcases hshared with ⟨rfl, hq⟩ | ⟨hp, rfl⟩
    · exact Or.inl ⟨rfl, fun h => hq (Subtype.ext h)⟩
    · exact Or.inr ⟨fun h => hp (Subtype.ext h), rfl⟩
  · rw [hyp.beta_apply_one, hyp.beta_apply_one]

open Classical in
/-- **Peterfalvi (3.5.2)** `O(ij, i'j')`, family form: `A_{ij}` and `A_{i'j'}` with both indices
different satisfy `|A_{ij} ∩ A_{i'j'}| = |{x ∈ A_{ij} : -x ∈ A_{i'j'}}|`. -/
theorem Afam_O (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p p' : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}}
    {q q' : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}}
    (hp : p ≠ p') (hq : q ≠ q') :
    (hyp.Afam hVeq app p q ∩ hyp.Afam hVeq app p' q').card =
      ((hyp.Afam hVeq app p q).filter (fun x => -x ∈ hyp.Afam hVeq app p' q')).card :=
  (hyp.Afam_isSignedTriple hVeq app p q).O_card_inter_eq (hyp.Afam_isSignedTriple hVeq app p' q')
    (hyp.beta_inner_eq_zero_of_both_diff hVeq app p.2 q.2 p'.2 q'.2
      (fun h => hp (Subtype.ext h)) (fun h => hq (Subtype.ext h)))

/-- The fixed family `Afam` is a signed-triple grid (`IsSignedTripleGrid`), indexed by nontrivial
linear characters of `W₁` (rows) and `W₂` (columns).  Bundles `Afam_isSignedTriple`/`Afam_L`/
`Afam_O` so the abstract (3.5.4) sunflower argument applies to the `β`-family. -/
theorem Afam_isSignedTripleGrid (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp) :
    IsSignedTripleGrid (fun (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
      (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) => hyp.Afam hVeq app p q) where
  card_eq_three p q := (hyp.Afam_isSignedTriple hVeq app p q).card_eq_three
  signed p q := (hyp.Afam_isSignedTriple hVeq app p q).signed
  orthogonal p q := (hyp.Afam_isSignedTriple hVeq app p q).pairwise_orthogonal
  inter_L _ _ _ _ hshared := (hyp.Afam_L hVeq app hshared).1
  noNeg_L _ _ _ _ hshared := (hyp.Afam_L hVeq app hshared).2
  inter_O _ _ _ _ hp hq := hyp.Afam_O hVeq app hp hq

open scoped Classical in
/-- **Peterfalvi (3.5.4)** for the fixed family `A_{ij}`, in the `w₁ ≥ 5` orientation: there is a
*unique* signed irreducible `z = -χ₀₁` common to every `A_{χ₁ χ₂₀}` as `χ₁` ranges over the
nontrivial characters of `W₁`.  This activates the abstract sunflower `existsUnique_common` on the
concrete `Afam` grid: the `≥ 4` rows come from `|W₁| ≥ 5` via `|Irr(W₁') ∖ {1}| = |W₁| − 1`
(Pontryagin `card_charGroup_subgroupOf`).  When only `|W₂| ≥ 5`, apply this to `transpose`. -/
theorem Afam_existsUnique_common (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : 5 ≤ Nat.card hyp.W1)
    {χ₂₀ χ₂₁ : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}} (hne : χ₂₀ ≠ χ₂₁) :
    ∃! z, ∀ χ₁ : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1},
      z ∈ hyp.Afam hVeq app χ₁ χ₂₀ := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have hcard : 4 ≤ Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    have h1 : Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}
        = Nat.card hyp.W1 - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
        hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    rw [h1]; omega
  exact (hyp.Afam_isSignedTripleGrid hVeq app).existsUnique_common hcard hne

open scoped Classical in
/-- **Column-common family** (the `-χ_{0j}` of (3.5)): when `w₁ ≥ 5`, each column `χ₂` (nontrivial)
of the `Afam` grid has a common element `z χ₂ ∈ A_{χ₁, χ₂}` for every row `χ₁` (`existsUnique_common`,
which needs `≥ 4` rows `= w₁ ≥ 5`).  A witness column `χ₂' ≠ χ₂` exists because `w₂ ≥ 3`. -/
theorem exists_colCommon (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) (hw1 : 5 ≤ Nat.card hyp.W1) :
    ∃ z : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} → ClassFunction G ℂ,
      ∀ q p, z q ∈ hyp.Afam hVeq app p q := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Nontrivial {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    have hodd : Odd (Nat.card hyp.W2) :=
      hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
    have hgt : 1 < Nat.card hyp.W2 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
    obtain ⟨k, hk⟩ := hodd; omega
  have hcol : ∀ q, ∃ z, ∀ p, z ∈ hyp.Afam hVeq app p q := fun q => by
    obtain ⟨q', hq'⟩ := exists_ne q
    exact ⟨_, (hyp.Afam_existsUnique_common hVeq app hw1 (Ne.symm hq')).choose_spec.1⟩
  choose z hz using hcol
  exact ⟨z, hz⟩

open scoped Classical in
/-- **Row-common family** (the `-χ_{i0}` of (3.5) in the `w₂ ≥ 5` case): when `w₂ ≥ 5`, each row
`χ₁` (nontrivial) has a common element `w χ₁ ∈ A_{χ₁, χ₂}` for every column `χ₂`.  Obtained by
applying `existsUnique_common` to the `transpose` grid (whose `≥ 4` rows are the `w₂ ≥ 5` columns);
a witness row `χ₁' ≠ χ₁` exists because `w₁ ≥ 3`. -/
theorem exists_rowCommon (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) (hw2 : 5 ≤ Nat.card hyp.W2) :
    ∃ w : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} → ClassFunction G ℂ,
      ∀ p q, w p ∈ hyp.Afam hVeq app p q := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Nontrivial {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    have hodd : Odd (Nat.card hyp.W1) :=
      hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
    have hgt : 1 < Nat.card hyp.W1 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
    obtain ⟨k, hk⟩ := hodd; omega
  have hcardκ : 4 ≤ Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W2_le_W]; omega
  have hrow : ∀ p, ∃ w, ∀ q, w ∈ hyp.Afam hVeq app p q := fun p => by
    obtain ⟨p', hp'⟩ := exists_ne p
    exact ⟨_, ((hyp.Afam_isSignedTripleGrid hVeq app).transpose.existsUnique_common hcardκ
      (Ne.symm hp')).choose_spec.1⟩
  choose w hw using hrow
  exact ⟨w, hw⟩

open scoped Classical in
/-- **(3.5) χ-assembly** (case-independent core): given the `(3.5.5)` cell decomposition of the
`Afam` grid into column-anchors `z`, row-anchors `w`, and interior thirds `φ`
(`A_{pq} = {z q, w p, φ p q}`) together with the orthonormality of `gridFamily z w φ`, build the
family `(χ_{pq})` over `Ĉ₁ × Ĉ₂` of (3.5): `χ_{00} = 1_G`, `χ_{p0} = -w p`, `χ_{0q} = -z q`,
`χ_{pq} = φ p q`.  It is orthonormal, lies in `ZIrr`, and satisfies
`Ind α_{pq} = 1_G - χ_{p0} - χ_{0q} + χ_{pq}`.  The three orientations of (3.5)
(`w₂ ≥ 5` symmetric, `w₂ = 3`, and the transpose `w₁ = 3`) differ only in how `(z, w, φ)` is
produced; the orthonormality lift (negating individual members, adjoining `1_G ⊥` signed) and the
`Ind` relation (cell sum `β = z + w + φ`) are shared here. -/
theorem exists_chiFamily_of_decomposition (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {z : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} → ClassFunction G ℂ}
    {w : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} → ClassFunction G ℂ}
    {φ : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} →
        {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} → ClassFunction G ℂ}
    (hcells : ∀ p q, hyp.Afam hVeq app p q = {z q, w p, φ p q})
    (hdiag0 : ∀ a, ClassFunction.inner
        (IsSignedTripleGrid.gridFamily z w φ a) (IsSignedTripleGrid.gridFamily z w φ a) = 1)
    (hoff0 : ∀ a b, a ≠ b → ClassFunction.inner
        (IsSignedTripleGrid.gridFamily z w φ a) (IsSignedTripleGrid.gridFamily z w φ b) = 0) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Nonempty {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [← Fintype.card_pos_iff, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    have hgt : 1 < Nat.card hyp.W1 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
    omega
  haveI : Nonempty {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [← Fintype.card_pos_iff, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    have hgt : 1 < Nat.card hyp.W2 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
    omega
  have hgrid := hyp.Afam_isSignedTripleGrid hVeq app
  -- every column-anchor, row-anchor, and interior third is a signed nontrivial irreducible
  have hsigw : ∀ p, IsSignedNontrivialIrr (w p) := fun p =>
    hgrid.signed p (Classical.arbitrary _) _ (by
      rw [hcells p (Classical.arbitrary _)]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hsigz : ∀ q, IsSignedNontrivialIrr (z q) := fun q =>
    hgrid.signed (Classical.arbitrary _) q _ (by
      rw [hcells (Classical.arbitrary _) q]; exact Finset.mem_insert_self _ _)
  have hsigφ : ∀ p q, IsSignedNontrivialIrr (φ p q) := fun p q =>
    hgrid.signed p q _ (by
      rw [hcells p q]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  -- repackage the `gridFamily` orthonormality as a single `ite`, elaborated here (concrete index)
  -- so the assembly's `if_neg` rewrites use the matching `Decidable` instance
  have hortho : ∀ a b, ClassFunction.inner
      (IsSignedTripleGrid.gridFamily z w φ a) (IsSignedTripleGrid.gridFamily z w φ b)
      = if a = b then 1 else 0 := fun a b => by
    split_ifs with h
    · subst h; exact hdiag0 a
    · exact hoff0 a b h
  -- abbreviations for the four χ-values
  set χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
      ClassFunction G ℂ := fun pq => if hp : pq.1 = 1 then
        (if hq : pq.2 = 1 then trivialClassFunction G else -z ⟨pq.2, hq⟩)
      else (if hq : pq.2 = 1 then -w ⟨pq.1, hp⟩ else φ ⟨pq.1, hp⟩ ⟨pq.2, hq⟩) with hχdef
  have hχ11 : χ (1, 1) = trivialClassFunction G := by
    simp only [hχdef, dif_pos]
  have hχp1 : ∀ (p) (hp : p ≠ 1), χ (p, 1) = -w ⟨p, hp⟩ := fun p hp => by
    simp only [hχdef, dif_neg hp, dif_pos]
  have hχ1q : ∀ (q) (hq : q ≠ 1), χ (1, q) = -z ⟨q, hq⟩ := fun q hq => by
    simp only [hχdef, dif_pos, dif_neg hq]
  have hχpq : ∀ (p q) (hp : p ≠ 1) (hq : q ≠ 1), χ (p, q) = φ ⟨p, hp⟩ ⟨q, hq⟩ := fun p q hp hq => by
    simp only [hχdef, dif_neg hp, dif_neg hq]
  -- the gridFamily values, as themselves (definitional), and `1_G ⊥ signed`
  have hgw : ∀ p, w p = IsSignedTripleGrid.gridFamily z w φ (Sum.inl p) := fun _ => rfl
  have hgz : ∀ q, z q = IsSignedTripleGrid.gridFamily z w φ (Sum.inr (Sum.inl q)) := fun _ => rfl
  have hgφ : ∀ p q, φ p q = IsSignedTripleGrid.gridFamily z w φ (Sum.inr (Sum.inr (p, q))) :=
    fun _ _ => rfl
  have h1Gx : ∀ {x : ClassFunction G ℂ}, IsSignedNontrivialIrr x →
      ClassFunction.inner (trivialClassFunction G) x = 0 := fun hx => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hx.inner_trivial, star_zero]
  refine ⟨χ, hχ11, ?_, ?_, ?_⟩
  · -- ZIrr
    rintro ⟨p, q⟩
    by_cases hp : p = 1 <;> by_cases hq : q = 1
    · subst hp; subst hq; rw [hχ11]; exact trivialClassFunction_isIrreducible.mem_ZIrr
    · subst hp; rw [hχ1q q hq]; exact Submodule.neg_mem _ (hsigz ⟨q, hq⟩).mem_ZIrr
    · subst hq; rw [hχp1 p hp]; exact Submodule.neg_mem _ (hsigw ⟨p, hp⟩).mem_ZIrr
    · rw [hχpq p q hp hq]; exact (hsigφ ⟨p, hp⟩ ⟨q, hq⟩).mem_ZIrr
  · -- orthonormality, via the diagonal (norm 1) and off-diagonal (orthogonal) facts
    have hdiag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1 := by
      rintro ⟨p, q⟩
      by_cases hp : p = 1 <;> by_cases hq : q = 1
      · subst hp; subst hq; rw [hχ11]; exact inner_trivialClassFunction_self G
      · subst hp; rw [hχ1q q hq, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg]; exact (hsigz _).inner_self
      · subst hq; rw [hχp1 p hp, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg]; exact (hsigw _).inner_self
      · rw [hχpq p q hp hq]; exact (hsigφ _ _).inner_self
    have hoff : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0 := by
      rintro ⟨p, q⟩ ⟨p', q'⟩ hab
      by_cases hp : p = 1 <;> by_cases hq : q = 1 <;> by_cases hp' : p' = 1 <;> by_cases hq' : q' = 1
      · subst hp; subst hq; subst hp'; subst hq'; exact absurd rfl hab
      · subst hp; subst hq; subst hp'
        rw [hχ11, hχ1q q' hq', ClassFunction.inner_neg_right, h1Gx (hsigz _), neg_zero]
      · subst hp; subst hq; subst hq'
        rw [hχ11, hχp1 p' hp', ClassFunction.inner_neg_right, h1Gx (hsigw _), neg_zero]
      · subst hp; subst hq
        rw [hχ11, hχpq p' q' hp' hq', h1Gx (hsigφ _ _)]
      · subst hp; subst hp'; subst hq'
        rw [hχ1q q hq, hχ11, ClassFunction.inner_neg_left, (hsigz _).inner_trivial, neg_zero]
      · subst hp; subst hp'
        rw [hχ1q q hq, hχ1q q' hq', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgz, hgz, hortho, if_neg (by
            simp only [ne_eq, Sum.inr.injEq, Sum.inl.injEq, Subtype.mk.injEq]
            exact fun h => hab (by rw [h]))]
      · subst hp; subst hq'
        rw [hχ1q q hq, hχp1 p' hp', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgz, hgw, hortho, if_neg (by simp)]
      · subst hp
        rw [hχ1q q hq, hχpq p' q' hp' hq', ClassFunction.inner_neg_left, hgz, hgφ, hortho,
          if_neg (by simp), neg_zero]
      · subst hq; subst hp'; subst hq'
        rw [hχp1 p hp, hχ11, ClassFunction.inner_neg_left, (hsigw _).inner_trivial, neg_zero]
      · subst hq; subst hp'
        rw [hχp1 p hp, hχ1q q' hq', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgw, hgz, hortho, if_neg (by simp)]
      · subst hq; subst hq'
        rw [hχp1 p hp, hχp1 p' hp', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgw, hgw, hortho, if_neg (by
            simp only [ne_eq, Sum.inr.injEq, Sum.inl.injEq, Subtype.mk.injEq]
            exact fun h => hab (by rw [h]))]
      · subst hq
        rw [hχp1 p hp, hχpq p' q' hp' hq', ClassFunction.inner_neg_left, hgw, hgφ, hortho,
          if_neg (by simp), neg_zero]
      · subst hp'; subst hq'
        rw [hχpq p q hp hq, hχ11, (hsigφ _ _).inner_trivial]
      · subst hp'
        rw [hχpq p q hp hq, hχ1q q' hq', ClassFunction.inner_neg_right, hgφ, hgz, hortho,
          if_neg (by simp), neg_zero]
      · subst hq'
        rw [hχpq p q hp hq, hχp1 p' hp', ClassFunction.inner_neg_right, hgφ, hgw, hortho,
          if_neg (by simp), neg_zero]
      · rw [hχpq p q hp hq, hχpq p' q' hp' hq', hgφ, hgφ, hortho, if_neg (by
          simp only [ne_eq, Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq]
          exact fun h => hab (by rw [h.1, h.2]))]
    intro a b
    split_ifs with hab
    · subst hab; exact hdiag a
    · exact hoff a b hab
  · -- the Ind relation: `Ind α = 1_G + β` and `β = ∑ (cell) = z + w + φ`
    intro p q hp hq
    have hst := hyp.Afam_isSignedTriple hVeq app ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨hzw, hzφ, hwφ⟩ := triple_distinct (hcells ⟨p, hp⟩ ⟨q, hq⟩ ▸ hst.card_eq_three)
    have hbeta : hyp.beta hVeq app p q
        = z ⟨q, hq⟩ + (w ⟨p, hp⟩ + φ ⟨p, hp⟩ ⟨q, hq⟩) := by
      rw [hst.sum_eq, hcells ⟨p, hp⟩ ⟨q, hq⟩, Finset.sum_insert (by simp [hzw, hzφ]),
        Finset.sum_insert (by simp [hwφ]), Finset.sum_singleton]
    have hind : app.tau.toDadeMap (hyp.alpha hVeq p q)
        = hyp.beta hVeq app p q + trivialClassFunction G := by
      rw [show hyp.beta hVeq app p q
        = app.tau.toDadeMap (hyp.alpha hVeq p q) - trivialClassFunction G from rfl, sub_add_cancel]
    rw [hind, hbeta, hχp1 p hp, hχ1q q hq, hχpq p q hp hq]
    abel

open scoped Classical in
/-- **Peterfalvi (3.5)**, symmetric case `w₁, w₂ ≥ 5`: there is an orthonormal family `(χ_{ij})`
indexed by `Ĉ₁ × Ĉ₂ = Irr(W)` of virtual characters with `χ_{00} = 1_G` and
`Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` for `i, j ≥ 1`.  Assembled from the (3.5.5)
orthonormal `gridFamily` on `Afam` (column-commons `z`, row-commons `w`, interior thirds `φ`):
`χ_{i0} = -w`, `χ_{0j} = -z`, `χ_{ij} = φ`, `χ_{00} = 1_G`.  The orthonormality lifts the
`gridFamily` one (`symm_orthonormal_family`) by negating individual members (sign-invariant) and
adjoining `1_G` (orthogonal to the signed nontrivial irreducibles, `inner_trivial`); the `Ind`
relation is the cell sum `β_{ij} = z + w + φ` (`IsSignedTriple.sum_eq`). -/
theorem exists_chiFamily_symm (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : 5 ≤ Nat.card hyp.W1) (hw2 : 5 ≤ Nat.card hyp.W2) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨z, hz⟩ := hyp.exists_colCommon hVeq app hw1
  obtain ⟨w, hw⟩ := hyp.exists_rowCommon hVeq app hw2
  have hι : 4 ≤ Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W1_le_W]; omega
  have hκ : 4 ≤ Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W2_le_W]; omega
  obtain ⟨φ, hcells, hortho⟩ :=
    (hyp.Afam_isSignedTripleGrid hVeq app).symm_orthonormal_family hι hκ hz hw
  exact hyp.exists_chiFamily_of_decomposition hVeq app hcells
    (fun a => by rw [hortho a a, if_pos rfl]) (fun a b h => by rw [hortho a b, if_neg h])

open scoped Classical in
/-- **Peterfalvi (3.5)**, two-column case `w₁ ≥ 5`, `w₂ = 3`: there is an orthonormal family
`(χ_{ij})` over `Ĉ₁ × Ĉ₂ = Irr(W)` of virtual characters with `χ_{00} = 1_G` and
`Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` for `i, j ≥ 1`.  Here `W₂` has only two nontrivial
characters, so the column-anchors `z` (from `exists_colCommon`, which needs `w₁ ≥ 5`) live over a
two-element index; `two_col_orthonormal_family_reindexed` produces the per-row meets `w` and interior
thirds `φ` with `A_{ij} = {z j, w i, φ i j}` and an orthonormal `gridFamily`, after which the χ-family
is assembled by the shared `exists_chiFamily_of_decomposition`.  (This is the case Peterfalvi calls
"complete" after (3.5.5).) -/
theorem exists_chiFamily_two_col (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : 5 ≤ Nat.card hyp.W1) (hw2 : Nat.card hyp.W2 = 3) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨z, hz⟩ := hyp.exists_colCommon hVeq app hw1
  have hι : 4 ≤ Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W1_le_W]; omega
  have hκ2 : Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} = 2 := by
    have h2 : Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}
        = Nat.card hyp.W2 - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
        hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    omega
  obtain ⟨w, φ, hcells, hortho⟩ :=
    (hyp.Afam_isSignedTripleGrid hVeq app).two_col_orthonormal_family_reindexed hι hκ2 hz
  exact hyp.exists_chiFamily_of_decomposition hVeq app hcells
    (fun a => by rw [hortho a a, if_pos rfl]) (fun a b h => by rw [hortho a b, if_neg h])

open scoped Classical in
/-- **Peterfalvi (3.5)**, transpose case `w₁ = 3`, `w₂ ≥ 5`: the `W₁ ↔ W₂`-swapped counterpart of
`exists_chiFamily_two_col`.  Now `W₁` has only two nontrivial characters, so we run the two-column
construction on the **transposed** `Afam` grid (rows `= Ĉ₂` with `w₂ ≥ 5 ⟹ ≥ 4` rows, columns
`= Ĉ₁` with `w₁ = 3 ⟹ 2` columns), whose column-commons are the original *row*-commons
(`exists_rowCommon`, needs `w₂ ≥ 5`).  The transposed orthonormal `gridFamily` (over
`Ĉ₂ ⊕ Ĉ₁ ⊕ Ĉ₂ × Ĉ₁`) is relabelled to the standard `Ĉ₁ ⊕ Ĉ₂ ⊕ Ĉ₁ × Ĉ₂` layout (swap the two
anchors, transpose the interior product index) via the bijection `toT`, and the χ-family is then the
shared `exists_chiFamily_of_decomposition` with column-anchor `= wMeet` (transposed row-meet) and
row-anchor `= wRow` (original row-common). -/
theorem exists_chiFamily_transpose (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : Nat.card hyp.W1 = 3) (hw2 : 5 ≤ Nat.card hyp.W2) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨wRow, hwRow⟩ := hyp.exists_rowCommon hVeq app hw2
  have hκT : 4 ≤ Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W2_le_W]; omega
  have hιT2 : Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} = 2 := by
    have h2 : Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}
        = Nat.card hyp.W1 - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
        hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    omega
  obtain ⟨wMeet, φT, hcellsT, horthoT⟩ :=
    (hyp.Afam_isSignedTripleGrid hVeq app).transpose.two_col_orthonormal_family_reindexed
      hκT hιT2 (z := wRow) hwRow
  -- the standard-layout decomposition: column-anchor `= wMeet`, row-anchor `= wRow`
  have hcells : ∀ p q, hyp.Afam hVeq app p q = {wMeet q, wRow p, φT q p} := fun p q => by
    rw [hcellsT q p, Finset.insert_comm]
  -- relabel the transposed `gridFamily` layout to the standard one
  let toT : ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ×
          ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) →
      ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ×
          ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) := fun a => match a with
    | Sum.inl p => Sum.inr (Sum.inl p)
    | Sum.inr (Sum.inl q) => Sum.inl q
    | Sum.inr (Sum.inr (p, q)) => Sum.inr (Sum.inr (q, p))
  let fromT : ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ×
          ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) →
      ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ×
          ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) := fun a => match a with
    | Sum.inl q => Sum.inr (Sum.inl q)
    | Sum.inr (Sum.inl p) => Sum.inl p
    | Sum.inr (Sum.inr (q, p)) => Sum.inr (Sum.inr (p, q))
  have htoT_inj : Function.Injective toT :=
    Function.LeftInverse.injective (g := fromT) (by rintro (p | q | ⟨p, q⟩) <;> rfl)
  have hgfeq : ∀ a, IsSignedTripleGrid.gridFamily wMeet wRow (fun p q => φT q p) a
      = IsSignedTripleGrid.gridFamily wRow wMeet φT (toT a) := by
    rintro (p | q | ⟨p, q⟩) <;> rfl
  exact hyp.exists_chiFamily_of_decomposition hVeq app (z := wMeet) (w := wRow)
    (φ := fun p q => φT q p) hcells
    (fun a => by rw [hgfeq a, horthoT (toT a) (toT a), if_pos rfl])
    (fun a b h => by rw [hgfeq a, hgfeq b, horthoT (toT a) (toT b),
      if_neg (fun hh => h (htoT_inj hh))])

open scoped Classical in
/-- **Peterfalvi (3.5)** (full): for any admissible `W = W₁ × W₂` there is an orthonormal family
`(χ_{ij})` indexed by `Ĉ₁ × Ĉ₂ = Irr(W)` of virtual characters with `χ_{00} = 1_G`, all `χ_{ij} ∈
ZIrr G`, and `Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` for `i, j ≥ 1`.  Since `|W₁|, |W₂|` are
odd `> 1` (so `∈ {3, 5, 7, …}`) and `max(|W₁|, |W₂|) ≥ 5` (`sup_card_ge_five`), the three orientations
cover every case: `w₁, w₂ ≥ 5` (`exists_chiFamily_symm`), `w₁ ≥ 5 ∧ w₂ = 3`
(`exists_chiFamily_two_col`), and `w₁ = 3 ∧ w₂ ≥ 5` (`exists_chiFamily_transpose`). -/
theorem exists_chiFamily (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  haveI : Finite G := Finite.of_fintype G
  have hodd1 : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have hodd2 : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have hgt1 : 1 < Nat.card hyp.W1 := Finite.one_lt_card_iff_nontrivial.mpr
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
  have hgt2 : 1 < Nat.card hyp.W2 := Finite.one_lt_card_iff_nontrivial.mpr
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
  rcases hyp.sup_card_ge_five with hw1 | hw2
  · -- `w₁ ≥ 5`: split on `w₂ = 3` vs `w₂ ≥ 5` (odd `> 1`)
    obtain ⟨k, hk⟩ := hodd2
    rcases (by omega : Nat.card hyp.W2 = 3 ∨ 5 ≤ Nat.card hyp.W2) with h3 | h5
    · exact hyp.exists_chiFamily_two_col hVeq app hw1 h3
    · exact hyp.exists_chiFamily_symm hVeq app hw1 h5
  · -- `w₂ ≥ 5`: either `w₁ ≥ 5` (symmetric) or `w₁ = 3` (transpose)
    by_cases hw1 : 5 ≤ Nat.card hyp.W1
    · exact hyp.exists_chiFamily_symm hVeq app hw1 hw2
    · obtain ⟨k, hk⟩ := hodd1
      exact hyp.exists_chiFamily_transpose hVeq app (by omega) hw2

/-! ### The index bridge `Ĉ₁ × Ĉ₂ ≃ Irr(W)` for `σ`

The `χ`-family of (3.5) is indexed by `Ĉ₁ × Ĉ₂ = Hom(W₁) × Hom(W₂)`; the isometry `σ` is defined on
the basis `Irr(W)` of `CF(W)`.  These are identified via the product-character bijection
(`omegaProdChar` is bijective because `W = W₁ × W₂` is an internal direct product) followed by
`omegaEquiv : Hom(W, ℂˣ) ≃ Irr(W)`. -/

/-- **`omegaProdChar` is surjective**: every linear character `ξ : W →* ℂˣ` equals `ω_{i0}·ω_{0j}`
for the restrictions `χ_k = ξ|_{W_k}`.  With `omegaProdChar_inj` this makes the product map a
bijection.  Uses the internal direct product reconstruction `w = wProj1 w · wProj2 w`. -/
theorem omegaProdChar_surjective (hyp : TICyclicHypothesis G) :
    Function.Surjective fun p : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) ×
      ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) => hyp.omegaProdChar p.1 p.2 := by
  intro ξ
  refine ⟨(ξ.comp (hyp.W1.subgroupOf hyp.W).subtype, ξ.comp (hyp.W2.subgroupOf hyp.W).subtype), ?_⟩
  ext w
  simp only [omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← map_mul]
  congr 1
  have e1 : (↑(hyp.wFst w) : hyp.W) = hyp.wProj1 w := by rw [wProj1_apply, wFst_apply]
  have e2 : (↑(hyp.wSnd w) : hyp.W) = hyp.wProj2 w := by rw [wProj2_apply, wSnd_apply]
  rw [e1, e2, wProj1_mul_wProj2]

/-- The product-character bijection `Ĉ₁ × Ĉ₂ ≃ (W →* ℂˣ)` (`omegaProdChar`, injective + surjective).
-/
noncomputable def omegaProdEquiv (hyp : TICyclicHypothesis G) :
    (((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) ≃ (hyp.W →* ℂˣ) :=
  Equiv.ofBijective (fun p => hyp.omegaProdChar p.1 p.2)
    ⟨fun _ _ h => Prod.ext (hyp.omegaProdChar_inj h).1 (hyp.omegaProdChar_inj h).2,
      hyp.omegaProdChar_surjective⟩

@[simp] theorem omegaProdEquiv_apply (hyp : TICyclicHypothesis G)
    (p : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.omegaProdEquiv p = hyp.omegaProdChar p.1 p.2 := rfl

/-- **(3.3) index bridge** `Ĉ₁ × Ĉ₂ ≃ Irr(W)`: the product-character bijection composed with
`omegaEquiv`.  Its inverse turns an irreducible character of `W` into the index pair at which the
(3.5) `χ`-family is evaluated, so `σ` can be defined on the `Irr(W)`-basis. -/
noncomputable def omegaIrrEquiv (hyp : TICyclicHypothesis G) :
    (((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) ≃
      IrreducibleCharacter hyp.W :=
  hyp.omegaProdEquiv.trans hyp.omegaEquiv

@[simp] theorem omegaIrrEquiv_apply (hyp : TICyclicHypothesis G)
    (p : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.omegaIrrEquiv p = hyp.omega (hyp.omegaProdChar p.1 p.2) := rfl

/-! ### The isometry `σ` of Theorem (3.2) -/

/-- A fixed choice of the `(3.5)` orthonormal family `(χ_{ij})` (indexed by `Ĉ₁ × Ĉ₂`), extracted
from `exists_chiFamily`.  `σ` is built from this. -/
noncomputable def chiFam (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) → ClassFunction G ℂ :=
  (hyp.exists_chiFamily hVeq app).choose

open scoped Classical in
theorem chiFam_spec (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    hyp.chiFam hVeq app (1, 1) = trivialClassFunction G ∧
      (∀ pq, hyp.chiFam hVeq app pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (hyp.chiFam hVeq app a) (hyp.chiFam hVeq app b)
        = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - hyp.chiFam hVeq app (p, 1) - hyp.chiFam hVeq app (1, q)
            + hyp.chiFam hVeq app (p, q) :=
  (hyp.exists_chiFamily hVeq app).choose_spec

/-- **Peterfalvi (3.2)**, the map: the linear `σ : CF(W) → CF(G)` defined by `ω^σ = χ` on the
basis `Irr(W)` (`(3.3)`) via the chosen `(3.5)` family (`Module.Basis.constr`).  Linearity is
automatic; the isometry property and (a)-(d) are proved separately. -/
noncomputable def sigma (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    ClassFunction hyp.W ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  (irreducibleCharacterBasis (G := hyp.W)).constr ℂ
    fun ω => hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω)

/-- The defining property of `σ` on the basis `Irr(W)`: `ω^σ = χ` at the matching index pair. -/
theorem sigma_irreducibleCharacter (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) :
    hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω) := by
  conv_lhs => rw [← irreducibleCharacterBasis_apply (G := hyp.W) ω]
  exact (irreducibleCharacterBasis (G := hyp.W)).constr_basis ℂ _ ω

/-- The Gram matrix of `σ` on the basis matches that of `Irr(W)`: `⟨ω^σ, ω'^σ⟩ = ⟨ω, ω'⟩`.  Both
sides are `δ_{ω,ω'}` — the `χ`-family is orthonormal (`chiFam_spec`) and `omegaIrrEquiv.symm` is
injective, while `Irr(W)` is orthonormal (`irreducibleCharacter_inner_eq_ite`). -/
theorem sigma_inner_irreducibleCharacter (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω ω' : IrreducibleCharacter hyp.W) :
    ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
        (hyp.sigma hVeq app (ω' : ClassFunction hyp.W ℂ))
      = ClassFunction.inner (ω : ClassFunction hyp.W ℂ) (ω' : ClassFunction hyp.W ℂ) := by
  rw [sigma_irreducibleCharacter, sigma_irreducibleCharacter, (hyp.chiFam_spec hVeq app).2.2.1,
    irreducibleCharacter_inner_eq_ite]
  by_cases h : ω = ω'
  · rw [if_pos h, if_pos (congrArg _ h)]
  · rw [if_neg h, if_neg fun hh => h (hyp.omegaIrrEquiv.symm.injective hh)]

/-- **Peterfalvi (3.2)** (isometry): `σ` preserves the class-function inner product,
`⟨α^σ, β^σ⟩ = ⟨α, β⟩`.  Expand `α, β` in the `Irr(W)` basis; both inner products become the same
double sum `∑_{ω,ω'} r_ω · conj(s_{ω'}) · ⟨·,·⟩`, and the per-pair Gram entries agree by
`sigma_inner_irreducibleCharacter`. -/
theorem sigma_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (x y : ClassFunction hyp.W ℂ) :
    ClassFunction.inner (hyp.sigma hVeq app x) (hyp.sigma hVeq app y)
      = ClassFunction.inner x y := by
  classical
  haveI : Finite hyp.W := Finite.of_fintype _
  haveI : Finite (IrreducibleCharacter hyp.W) := finite_irreducibleCharacter
  haveI : Fintype (IrreducibleCharacter hyp.W) := Fintype.ofFinite _
  set b := irreducibleCharacterBasis (G := hyp.W) with hb
  have hbω : ∀ ω, b ω = (ω : ClassFunction hyp.W ℂ) := fun ω => by
    rw [hb]; exact irreducibleCharacterBasis_apply ω
  have hσ : ∀ z, hyp.sigma hVeq app z = ∑ ω, b.repr z ω • hyp.sigma hVeq app (b ω) := fun z => by
    conv_lhs => rw [← b.sum_repr z]
    rw [map_sum]; exact Finset.sum_congr rfl fun ω _ => map_smul _ _ _
  -- both inner products expand to the same double sum over the (matching) Gram entries
  have hL := inner_sum_smul_sum (fun ω => b.repr x ω) (fun ω => b.repr y ω)
    (fun ω => hyp.sigma hVeq app (b ω))
  have hR := inner_sum_smul_sum (fun ω => b.repr x ω) (fun ω => b.repr y ω) (fun ω => b ω)
  rw [hσ x, hσ y, hL]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y, hR]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun ω' _ => ?_
  rw [hbω ω, hbω ω', hyp.sigma_inner_irreducibleCharacter hVeq app ω ω']

/-- `omegaProdEquiv.symm` inverts `omegaProdChar`: `(ω_{i0}·ω_{0j})` has index pair `(χ₁, χ₂)`. -/
theorem omegaProdEquiv_symm_omegaProdChar (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.omegaProdEquiv.symm (hyp.omegaProdChar χ₁ χ₂) = (χ₁, χ₂) := by
  rw [show hyp.omegaProdChar χ₁ χ₂ = hyp.omegaProdEquiv (χ₁, χ₂) from rfl, Equiv.symm_apply_apply]

/-- **`omegaProdChar` reconstructs any linear character of `W`**: the product `ω_{i0}·ω_{0j}` of the
`W₁`- and `W₂`-restrictions `χ_k = ξ|_{W_k}` recovers `ξ`.  This is the witness of
`omegaProdChar_surjective`, extracted as a reusable identity (uses `W = W₁ × W₂`,
`wProj1_mul_wProj2`). -/
theorem omegaProdChar_comp_subtype (hyp : TICyclicHypothesis G) (ξ : hyp.W →* ℂˣ) :
    hyp.omegaProdChar (ξ.comp (hyp.W1.subgroupOf hyp.W).subtype)
        (ξ.comp (hyp.W2.subgroupOf hyp.W).subtype) = ξ := by
  ext w
  simp only [omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← map_mul]
  congr 1
  have e1 : (↑(hyp.wFst w) : hyp.W) = hyp.wProj1 w := by rw [wProj1_apply, wFst_apply]
  have e2 : (↑(hyp.wSnd w) : hyp.W) = hyp.wProj2 w := by rw [wProj2_apply, wSnd_apply]
  rw [e1, e2, wProj1_mul_wProj2]

/-- **`omegaProdEquiv.symm` extracts the `W₁`/`W₂`-restrictions**: for any linear `ξ : W →* ℂˣ`,
`omegaProdEquiv.symm ξ = (ξ|_{W₁}, ξ|_{W₂})`.  The §10 (10.6) column-structure argument uses this to
read off the product index `(ρ, κ)` of a transported `ω_{ij}`: each factor of a product character
contributes to exactly one component. -/
theorem omegaProdEquiv_symm_eq (hyp : TICyclicHypothesis G) (ξ : hyp.W →* ℂˣ) :
    hyp.omegaProdEquiv.symm ξ
      = (ξ.comp (hyp.W1.subgroupOf hyp.W).subtype, ξ.comp (hyp.W2.subgroupOf hyp.W).subtype) := by
  conv_lhs => rw [← hyp.omegaProdChar_comp_subtype ξ]
  exact hyp.omegaProdEquiv_symm_omegaProdChar _ _

/-- `σ` on a single linear character: `(ω(ξ))^σ = χ` at the index pair `omegaProdEquiv.symm ξ`. -/
theorem sigma_omega (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) (ξ : hyp.W →* ℂˣ) :
    hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (hyp.omegaProdEquiv.symm ξ) := by
  rw [sigma_irreducibleCharacter]
  congr 1
  show hyp.omegaProdEquiv.symm (hyp.omegaEquiv.symm (hyp.omega ξ)) = hyp.omegaProdEquiv.symm ξ
  congr 1
  exact hyp.omegaEquiv.symm_apply_apply ξ

/-- **Peterfalvi (3.2)(b)**: `1_W^σ = 1_G`.  The trivial character is `ω(1)` at index `(1, 1)`,
and `χ_{00} = 1_G` (`chiFam_spec`). -/
theorem sigma_trivial (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    hyp.sigma hVeq app (trivialClassFunction hyp.W) = trivialClassFunction G := by
  have h1W : trivialClassFunction hyp.W = (hyp.omega 1 : ClassFunction hyp.W ℂ) := by
    ext w; simp
  rw [h1W, sigma_omega,
    show (1 : hyp.W →* ℂˣ) = hyp.omegaProdChar 1 1 from hyp.omegaProdChar_one_one.symm,
    omegaProdEquiv_symm_omegaProdChar, (hyp.chiFam_spec hVeq app).1]

/-- **Peterfalvi (3.2)(a)** on the basis `α_{ij}`: `α_{ij}^σ = Ind_W^G α_{ij}` for `i, j ≥ 1`.
Expand `α_{ij} = ω_{00} - ω_{i0} - ω_{0j} + ω_{ij}` (`alphaCF_eq_omega_combination`), apply `σ`
term-by-term (`sigma_omega`), and recognise the result as the `(3.5)` `Ind` relation
(`chiFam_spec`). -/
theorem sigma_alphaCF (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    (hp : p ≠ 1) (hq : q ≠ 1) :
    hyp.sigma hVeq app (hyp.alphaCF p q) = app.tau.toDadeMap (hyp.alpha hVeq p q) := by
  rw [alphaCF_eq_omega_combination,
    -- normalise each `ω`-argument to `omegaProdChar` form (the product term first, as it is `rfl`)
    show p.comp hyp.wFst * q.comp hyp.wSnd = hyp.omegaProdChar p q from rfl,
    show (1 : hyp.W →* ℂˣ) = hyp.omegaProdChar 1 1 from hyp.omegaProdChar_one_one.symm,
    show p.comp hyp.wFst = hyp.omegaProdChar p 1 from (hyp.omegaProdChar_one_right p).symm,
    show q.comp hyp.wSnd = hyp.omegaProdChar 1 q from (hyp.omegaProdChar_one_left q).symm,
    map_add, map_sub, map_sub, sigma_omega, sigma_omega, sigma_omega, sigma_omega,
    omegaProdEquiv_symm_omegaProdChar, omegaProdEquiv_symm_omegaProdChar,
    omegaProdEquiv_symm_omegaProdChar, omegaProdEquiv_symm_omegaProdChar,
    (hyp.chiFam_spec hVeq app).1]
  exact ((hyp.chiFam_spec hVeq app).2.2.2 p q hp hq).symm

/-- The basis `alphaBasis` evaluated at an index pair: `alphaBasis (p, q) = α_{pq}`
(`coe_basisOfLinearIndependentOfCardEqFinrank` for the family `alphaLinearIndependent`). -/
theorem alphaBasis_apply (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (pq : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} ×
        {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) :
    hyp.alphaBasis hVeq pq = hyp.alpha hVeq pq.1.1 pq.2.1 := by
  classical
  haveI : Finite G := Finite.of_fintype G
  letI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := Fintype.ofFinite _
  letI : Fintype {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := Fintype.ofFinite _
  haveI := hyp.nonempty_charNeOne hyp.W1_le_W hyp.W1_nontrivial
  haveI := hyp.nonempty_charNeOne hyp.W2_le_W hyp.W2_nontrivial
  have h : ⇑(hyp.alphaBasis hVeq) = fun p => hyp.alpha hVeq p.1.1 p.2.1 := by
    unfold TICyclicHypothesis.alphaBasis
    exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact congrFun h pq

/-- `Ind_W^G` packaged as a `ℂ`-linear map `CF(W) →ₗ[ℂ] CF(G)` (linearity from `induce_add` /
`induce_smul`).  Used to phrase (3.2)(a) as an equality of linear maps on the basis `(α_{ij})`. -/
noncomputable def induceLinear (hyp : TICyclicHypothesis G) [Invertible (Nat.card hyp.W : ℂ)] :
    ClassFunction hyp.W ℂ →ₗ[ℂ] ClassFunction G ℂ where
  toFun := ClassFunction.induce hyp.W
  map_add' := ClassFunction.induce_add hyp.W
  map_smul' c θ := ClassFunction.induce_smul hyp.W c θ

@[simp] theorem induceLinear_apply (hyp : TICyclicHypothesis G) [Invertible (Nat.card hyp.W : ℂ)]
    (θ : ClassFunction hyp.W ℂ) :
    hyp.induceLinear θ = ClassFunction.induce hyp.W θ := rfl

/-- **Peterfalvi (3.2)(a)** (full form): on all of `CF(W, V)`, `σ` agrees with the Dade map `τ`,
`α^σ = τ(α) = Ind_W^G α`.  Both `α ↦ σ(↑α)` and `α ↦ Ind_W^G ↑α` are `ℂ`-linear on `CF(W, V)` and
agree on the basis `(α_{ij})` (`alphaBasis`) — LHS by `sigma_alphaCF`, RHS by `tau_eq_induce`
(`τ = Ind`) — hence agree everywhere. -/
theorem sigma_eq_tau (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV ℂ hyp) :
    hyp.sigma hVeq app (α : ClassFunction hyp.W ℂ) = app.tau.toDadeMap α := by
  -- the two `ℂ`-linear maps `CF(W,V) →ₗ CF(G)` (`σ ∘ ↪` and `Ind ∘ ↪`) agree on the basis `α_{ij}`
  have key : ((hyp.sigma hVeq app).comp (Submodule.subtype _) :
        SupportedOnV ℂ hyp →ₗ[ℂ] ClassFunction G ℂ)
      = hyp.induceLinear.comp (Submodule.subtype _) := by
    refine Module.Basis.ext (hyp.alphaBasis hVeq) (fun pq => ?_)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hyp.alphaBasis_apply hVeq,
      induceLinear_apply, hyp.alpha_coe]
    rw [hyp.sigma_alphaCF hVeq app pq.1.1 pq.2.1 pq.1.2 pq.2.2]
    -- LHS `= τ(α_{pq})` (now); RHS `Ind ↑α_{pq} = τ(α_{pq})` by `tau_eq_induce` (`τ = Ind`)
    have h := hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq pq.1.1 pq.2.1)
    rw [hyp.alpha_coe] at h
    exact h
  have hα := DFunLike.congr_fun key α
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hα
  rw [hα, induceLinear_apply]
  exact (hyp.tau_eq_induce app.tau.toDadeIsometryData α).symm

/-- **Peterfalvi (3.2)** (virtual characters): `σ` maps `ZIrr(W)` into `ZIrr(G)`.  Each `Irr(W)`
basis vector maps to a member of the `(3.5)` family `χ ∈ ZIrr(G)` (`chiFam_spec`); a `ℤ`-combination
maps to a `ℤ`-combination, which stays in the `ℤ`-submodule `ZIrr(G)` (`span` induction). -/
theorem sigma_mem_ZIrr (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {z : ClassFunction hyp.W ℂ} (hz : z ∈ ZIrr hyp.W) :
    hyp.sigma hVeq app z ∈ ZIrr G := by
  rw [ZIrr_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
      have hx' : hyp.sigma hVeq app x
          = hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ⟨x, hx⟩) :=
        hyp.sigma_irreducibleCharacter hVeq app ⟨x, hx⟩
      rw [hx']; exact (hyp.chiFam_spec hVeq app).2.1 _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih => rw [map_zsmul]; exact (ZIrr G).smul_mem a ih

/-- **(1.3)(a) → (3.2) bridge** (vanishing on `V`): a class function `f` on `W` orthogonal to
every `α_{ij}` (`i, j ≥ 1`) vanishes on `V`.  The `α_{ij}` are a basis of `CF(W, V)` ((3.4)), so the
linear functional `⟨·, f⟩` is zero on all of `CF(W, V)`; the (1.3)(a) engine
(`eq_zero_of_mem_of_inner_supported_eq_zero`) then forces `f|_V = 0`.  (`V` is conjugation-closed in
the abelian `W`.) -/
theorem vanishOnV_of_inner_alphaCF (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    {f : ClassFunction hyp.W ℂ}
    (hf : ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      p ≠ 1 → q ≠ 1 → ClassFunction.inner (hyp.alphaCF p q) f = 0)
    {v : G} (hv : v ∈ hyp.V) : f ⟨v, hyp.V_subset_W hv⟩ = 0 := by
  classical
  haveI : IsMulCommutative ↥hyp.W := hyp.isMulCommutative_W
  -- `⟨·, f⟩` is zero on `CF(W, V)`: zero on the basis `α_{ij}` (so on the whole submodule)
  have hL0 : (innerLeftFunctional f).comp (Submodule.subtype
      (ClassFunction.supportedSubmodule (G := ↥hyp.W)
        (OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W))) = 0 := by
    refine Module.Basis.ext (hyp.alphaBasis hVeq) (fun pq => ?_)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      innerLeftFunctional_apply, hyp.alphaBasis_apply hVeq, hyp.alpha_coe]
    exact hf pq.1.1 pq.2.1 pq.1.2 pq.2.2
  refine eq_zero_of_mem_of_inner_supported_eq_zero
    (A := OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W) (fun x _ h => ?_)
    (fun φ hφ => ?_) ?_
  · -- `V` is conjugation-closed in the abelian `W`, so `h * x * h⁻¹ = x`
    have hxx : h * x * h⁻¹ = x := by rw [mul_comm' h x, mul_assoc, mul_inv_cancel, mul_one]
    rw [hxx]; assumption
  · -- orthogonal to every `φ ∈ CF(W, V)` via `hL0`
    have := DFunLike.congr_fun hL0 ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
    simpa using this
  · rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hv

open scoped Classical in
/-- **Peterfalvi (3.2)(c)** on a basis character: `ω^σ(v) = ω(v)` for `ω ∈ Irr(W)` and `v ∈ V`.
By the bridge `vanishOnV_of_inner_alphaCF` it suffices that `f = Res_W(ω^σ) - ω ⊥ α_{ij}`; this
holds because `⟨α_{ij}, Res_W(ω^σ)⟩ = ⟨Ind α_{ij}, ω^σ⟩ = ⟨α_{ij}^σ, ω^σ⟩ = ⟨α_{ij}, ω⟩`
(Frobenius `+` (a) `+` isometry). -/
theorem sigma_apply_irreducibleCharacter_of_mem_V (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) {v : G} (hv : v ∈ hyp.V) :
    hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) v
      = (ω : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ := by
  have hkey : ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      p ≠ 1 → q ≠ 1 → ClassFunction.inner (hyp.alphaCF p q)
        (ClassFunction.restrict hyp.W (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
          - (ω : ClassFunction hyp.W ℂ)) = 0 := by
    intro p q hp hq
    have hinduce : ClassFunction.induce hyp.W (hyp.alphaCF p q)
        = hyp.sigma hVeq app (hyp.alphaCF p q) := by
      have h1 := hyp.sigma_eq_tau hVeq app (hyp.alpha hVeq p q)
      have h2 := hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq p q)
      rw [hyp.alpha_coe] at h1 h2
      exact h2.symm.trans h1.symm
    rw [ClassFunction.inner_sub_right, ← ClassFunction.inner_induce_eq_inner_restrict, hinduce,
      hyp.sigma_inner hVeq app, sub_self]
  have hzero := hyp.vanishOnV_of_inner_alphaCF hVeq hkey hv
  rw [ClassFunction.sub_apply, ClassFunction.restrict_apply] at hzero
  exact sub_eq_zero.mp hzero

open scoped Classical in
/-- **Peterfalvi (3.2)(c)**: `α^σ(x) = α(x)` for every `α ∈ CF(W)` and `x ∈ V`.  Both sides are
`ℂ`-linear in `α`, and they agree on the orthonormal basis `Irr(W)`
(`sigma_apply_irreducibleCharacter_of_mem_V`), hence everywhere. -/
theorem sigma_apply_of_mem_V (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (α : ClassFunction hyp.W ℂ) {v : G} (hv : v ∈ hyp.V) :
    hyp.sigma hVeq app α v = α ⟨v, hyp.V_subset_W hv⟩ := by
  classical
  haveI : Finite hyp.W := Finite.of_fintype _
  haveI : Finite (IrreducibleCharacter hyp.W) := finite_irreducibleCharacter
  haveI : Fintype (IrreducibleCharacter hyp.W) := Fintype.ofFinite _
  -- the linear functional `D α = α^σ(v) - α(v)` vanishes on the basis `Irr(W)`, hence is `0`
  let D : ClassFunction hyp.W ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun α => hyp.sigma hVeq app α v - α ⟨v, hyp.V_subset_W hv⟩
      map_add' := fun a b => by
        simp only [map_add, ClassFunction.add_apply]; ring
      map_smul' := fun c a => by
        simp only [map_smul, ClassFunction.smul_apply, RingHom.id_apply, smul_eq_mul]; ring }
  have hD0 : D = 0 := by
    refine Module.Basis.ext (irreducibleCharacterBasis (G := hyp.W)) (fun ω => ?_)
    show hyp.sigma hVeq app (irreducibleCharacterBasis (G := hyp.W) ω) v
        - (irreducibleCharacterBasis (G := hyp.W) ω) ⟨v, hyp.V_subset_W hv⟩ = 0
    rw [irreducibleCharacterBasis_apply,
      hyp.sigma_apply_irreducibleCharacter_of_mem_V hVeq app ω hv, sub_self]
  have hDα : hyp.sigma hVeq app α v - α ⟨v, hyp.V_subset_W hv⟩ = 0 := DFunLike.congr_fun hD0 α
  exact sub_eq_zero.mp hDα

open scoped Classical in
/-- **Peterfalvi (3.2)(d)**: any `χ ∈ CF(G)` orthogonal to every `χ_{ij}` (the images of the basis
`Irr(W)` under `σ`) vanishes on `V`.  Since `σ(α_{ij}) = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` ((3.5)) and
`1_G = χ_{00}`, all four terms are orthogonal to `χ`, so `⟨α_{ij}, Res_W χ⟩ = ⟨σ(α_{ij}), χ⟩ = 0`
(Frobenius `+` (a)); the bridge then gives `χ|_V = 0`.  An irreducible character of `G` not in the
image of `σ` is in particular orthogonal to all `χ_{ij}`, so this is the stated form of (d). -/
theorem eq_zero_of_mem_V_of_inner_chiFam_eq_zero (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ}
    (hχ : ∀ (a : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (b : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      ClassFunction.inner χ (hyp.chiFam hVeq app (a, b)) = 0)
    {v : G} (hv : v ∈ hyp.V) : χ v = 0 := by
  -- each `χ_{ij}` is orthogonal to `χ` (conjugate symmetry of the hypothesis)
  have hcf : ∀ (a : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (b : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      ClassFunction.inner (hyp.chiFam hVeq app (a, b)) χ = 0 := fun a b => by
    rw [inner_conj_symm χ (hyp.chiFam hVeq app (a, b)), hχ a b, star_zero]
  have hkey : ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      p ≠ 1 → q ≠ 1 → ClassFunction.inner (hyp.alphaCF p q)
        (ClassFunction.restrict hyp.W χ) = 0 := by
    intro p q hp hq
    have hinduce : ClassFunction.induce hyp.W (hyp.alphaCF p q)
        = hyp.sigma hVeq app (hyp.alphaCF p q) := by
      have h1 := hyp.sigma_eq_tau hVeq app (hyp.alpha hVeq p q)
      have h2 := hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq p q)
      rw [hyp.alpha_coe] at h1 h2
      exact h2.symm.trans h1.symm
    rw [← ClassFunction.inner_induce_eq_inner_restrict, hinduce,
      hyp.sigma_alphaCF hVeq app p q hp hq, (hyp.chiFam_spec hVeq app).2.2.2 p q hp hq,
      ClassFunction.inner_add_left, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ← (hyp.chiFam_spec hVeq app).1, hcf 1 1, hcf p 1, hcf 1 q, hcf p q]
    ring
  have hzero := hyp.vanishOnV_of_inner_alphaCF hVeq hkey hv
  rwa [ClassFunction.restrict_apply] at hzero

open scoped Classical in
/-- **Peterfalvi Theorem (3.2)** (capstone).  There is a linear isometry `σ : CF(W) → CF(G)`
sending virtual characters of `W` to virtual characters of `G`, such that:
* **(a)** `α^σ = Ind_W^G α` for `α ∈ CF(W, V)`;
* **(b)** `1_W^σ = 1_G`;
* **(c)** `α^σ(x) = α(x)` for `x ∈ V`;
* **(d)** every `χ ∈ CF(G)` orthogonal to the whole image `σ(Irr W)` vanishes on `V` (in
  particular an irreducible character of `G` not in the image of `σ` vanishes on `V`).

The witness is the constructed `σ` (`sigma`); the six conjuncts are `sigma_inner`,
`sigma_mem_ZIrr`, `sigma_eq_tau` ∘ `tau_eq_induce`, `sigma_trivial`, `sigma_apply_of_mem_V`,
and `eq_zero_of_mem_V_of_inner_chiFam_eq_zero` (with the index bridge `χ_{ij} = (ω_{ij})^σ`). -/
theorem exists_sigma (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    ∃ σ : ClassFunction hyp.W ℂ →ₗ[ℂ] ClassFunction G ℂ,
      (∀ x y, ClassFunction.inner (σ x) (σ y) = ClassFunction.inner x y) ∧
      (∀ z ∈ ZIrr hyp.W, σ z ∈ ZIrr G) ∧
      (∀ α : SupportedOnV ℂ hyp,
        σ (α : ClassFunction hyp.W ℂ) = ClassFunction.induce hyp.W (α : ClassFunction hyp.W ℂ)) ∧
      σ (trivialClassFunction hyp.W) = trivialClassFunction G ∧
      (∀ (α : ClassFunction hyp.W ℂ) (v : G) (hv : v ∈ hyp.V),
        σ α v = α ⟨v, hyp.V_subset_W hv⟩) ∧
      (∀ χ : ClassFunction G ℂ,
        (∀ ω : IrreducibleCharacter hyp.W,
          ClassFunction.inner χ (σ (ω : ClassFunction hyp.W ℂ)) = 0) →
        ∀ (v : G), v ∈ hyp.V → χ v = 0) := by
  refine ⟨hyp.sigma hVeq app, hyp.sigma_inner hVeq app,
    fun z hz => hyp.sigma_mem_ZIrr hVeq app hz,
    fun α => (hyp.sigma_eq_tau hVeq app α).trans
      (hyp.tau_eq_induce app.tau.toDadeIsometryData α),
    hyp.sigma_trivial hVeq app,
    fun α v hv => hyp.sigma_apply_of_mem_V hVeq app α hv,
    fun χ hd v hv => ?_⟩
  refine hyp.eq_zero_of_mem_V_of_inner_chiFam_eq_zero hVeq app (fun a b => ?_) hv
  -- index bridge: `χ_{ab} = (ω_{ab})^σ`, so orthogonality to `σ(Irr W)` gives `⟨χ, χ_{ab}⟩ = 0`
  have hbridge : hyp.chiFam hVeq app (a, b)
      = hyp.sigma hVeq app (hyp.omegaIrrEquiv (a, b) : ClassFunction hyp.W ℂ) := by
    rw [hyp.sigma_irreducibleCharacter hVeq app (hyp.omegaIrrEquiv (a, b)),
      Equiv.symm_apply_apply]
  rw [hbridge]
  exact hd (hyp.omegaIrrEquiv (a, b))

/-! ### Peterfalvi (3.6)-(3.8): the coefficient grid `a_{ij} = ⟨ψ, ω_{ij}^σ⟩` and `NC(ψ)` -/

open scoped Classical in
/-- **Peterfalvi (3.7) support input**: the 4-term combination
`ω_{pq} + ω_{p'q'} − ω_{pq'} − ω_{p'q}` lies in `CF(W, V)`.  On `W₁` the `W₂`-parts (`q`) collapse to
`1`, on `W₂` the `W₁`-parts (`p`) collapse, so the combination vanishes on `W₁ ∪ W₂`. -/
theorem omegaCombo_mem_supportedSubmodule (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.omega (hyp.omegaProdChar p q) + hyp.omega (hyp.omegaProdChar p' q')
       - hyp.omega (hyp.omegaProdChar p q') - hyp.omega (hyp.omegaProdChar p' q)
       : ClassFunction hyp.W ℂ)
      ∈ ClassFunction.supportedSubmodule
          (OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W) := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro w hw
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hVeq, mem_Vdiff]
  refine ⟨w.2, fun h1 => (ClassFunction.mem_support.mp hw) ?_,
    fun h2 => (ClassFunction.mem_support.mp hw) ?_⟩
  · -- `↑w ∈ W₁`: the `q`-parts collapse, the four terms cancel
    have hw1 : w ∈ hyp.W1.subgroupOf hyp.W := (Subgroup.mem_subgroupOf).mpr h1
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply, omega_apply,
      TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply,
      hyp.wSnd_eq_one_of_mem_W1 hw1, map_one, mul_one]
    ring
  · -- `↑w ∈ W₂`: the `p`-parts collapse, the four terms cancel
    have hw2 : w ∈ hyp.W2.subgroupOf hyp.W := (Subgroup.mem_subgroupOf).mpr h2
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply, omega_apply,
      TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply,
      hyp.wFst_eq_one_of_mem_W2 hw2, map_one, one_mul]
    ring

/-- The (3.7) test element `ω_{pq} + ω_{p'q'} − ω_{pq'} − ω_{p'q} ∈ CF(W, V)`. -/
noncomputable def omegaCombo (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    SupportedOnV ℂ hyp :=
  ⟨hyp.omega (hyp.omegaProdChar p q) + hyp.omega (hyp.omegaProdChar p' q')
     - hyp.omega (hyp.omegaProdChar p q') - hyp.omega (hyp.omegaProdChar p' q),
   hyp.omegaCombo_mem_supportedSubmodule hVeq p p' q q'⟩

@[simp] theorem omegaCombo_coe (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.omegaCombo hVeq p p' q q' : ClassFunction hyp.W ℂ)
      = hyp.omega (hyp.omegaProdChar p q) + hyp.omega (hyp.omegaProdChar p' q')
        - hyp.omega (hyp.omegaProdChar p q') - hyp.omega (hyp.omegaProdChar p' q) := rfl

/-- For `α ∈ CF(W, V)` and `ψ ∈ CF(G)` vanishing on `V`, `⟨ψ, α^σ⟩ = 0`.  By (3.2)(a),
`α^σ = Ind_W^G α` is supported on `V^G = conjugatesOfSet V`; the class function `ψ` (vanishing on
`V`) vanishes there too, so the supports are disjoint. -/
theorem inner_sigma_eq_zero_of_vanishOnV (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV ℂ hyp) {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0) :
    ClassFunction.inner ψ (hyp.sigma hVeq app (α : ClassFunction hyp.W ℂ)) = 0 := by
  apply ClassFunction.inner_eq_zero_of_disjoint_support
  rw [Set.disjoint_left]
  intro g hgψ hgσ
  -- `g ∈ Supp(α^σ) ⟹ g ∈ conjugatesOfSet V` (else `α^σ g = τ(α) g = 0`)
  have hgconj : g ∈ Group.conjugatesOfSet hyp.V := by
    by_contra hg
    refine (ClassFunction.mem_support.mp hgσ) ?_
    rw [show hyp.sigma hVeq app (α : ClassFunction hyp.W ℂ) = app.tau.toDadeMap α from
      hyp.sigma_eq_tau hVeq app α]
    exact full_map_eq_zero_of_not_mem_conjugatesOfSet_V app α hg
  -- `g ∈ conjugatesOfSet V ⟹ ψ g = 0` (`ψ` vanishes on `V`, class function)
  obtain ⟨v, hv, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hgconj
  exact (ClassFunction.mem_support.mp hgψ) ((ψ.of_isConj hconj).symm.trans (hψ v hv))

/-- **Peterfalvi (3.6)**: the `σ`-image coefficient `a_{ij} = ⟨ψ, ω_{ij}^σ⟩` of `ψ ∈ CF(G)`.  As
`{ω_{ij}^σ} = {χ_{ij}}` (`chiFam`) is orthonormal, these are the Fourier coefficients of `ψ` along
`Im σ`, and `β = ψ − ∑ a_{ij} ω_{ij}^σ` is automatically orthogonal to `Im σ`.  Indexed by
`Ĉ₁ × Ĉ₂` (index `(1, 1) = ω_{00} = 1_W`). -/
noncomputable def sigmaCoeff (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ψ : ClassFunction G ℂ)
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) : ℂ :=
  ClassFunction.inner ψ (hyp.chiFam hVeq app pq)

/-- **Peterfalvi (3.6)**: `NC(ψ)` = number of nonzero `σ`-image coefficients of `ψ`. -/
noncomputable def sigmaNC (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ψ : ClassFunction G ℂ) : ℕ :=
  {pq | hyp.sigmaCoeff hVeq app ψ pq ≠ 0}.ncard

/-- **Peterfalvi (3.7)**: under Hypothesis (3.6) (`ψ` vanishing on `V`), the `σ`-image coefficients
satisfy the additive grid identity `a_{ij} + a_{i'j'} = a_{ij'} + a_{i'j}`.  Apply
`inner_sigma_eq_zero_of_vanishOnV` to `α = ω_{ij} + ω_{i'j'} − ω_{ij'} − ω_{i'j} ∈ CF(W, V)`:
`σ(α) = χ_{ij} + χ_{i'j'} − χ_{ij'} − χ_{i'j}` (σ linear, `sigma_omega`), and `⟨ψ, σ(α)⟩ = 0`. -/
theorem sigmaCoeff_add_eq (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.sigmaCoeff hVeq app ψ (p, q) + hyp.sigmaCoeff hVeq app ψ (p', q')
      = hyp.sigmaCoeff hVeq app ψ (p, q') + hyp.sigmaCoeff hVeq app ψ (p', q) := by
  have hσ : hyp.sigma hVeq app (hyp.omegaCombo hVeq p p' q q' : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (p, q) + hyp.chiFam hVeq app (p', q')
        - hyp.chiFam hVeq app (p, q') - hyp.chiFam hVeq app (p', q) := by
    simp only [omegaCombo_coe, map_add, map_sub, hyp.sigma_omega hVeq app,
      hyp.omegaProdEquiv_symm_omegaProdChar]
  have h0 := hyp.inner_sigma_eq_zero_of_vanishOnV hVeq app (hyp.omegaCombo hVeq p p' q q') hψ
  rw [hσ] at h0
  simp only [ClassFunction.inner_add_right, ClassFunction.inner_sub_right] at h0
  simp only [sigmaCoeff]
  linear_combination h0

/-- **Peterfalvi (3.8) corollary** (`NC` too small for a row or column): if `ψ` vanishes on `V` and
`NC(ψ) < min(w₁, w₂)`, then *all* `σ`-image coefficients of `ψ` vanish — i.e. `ψ = β` is orthogonal
to `Im σ`.  By (3.7) the coefficient grid `a_{ij}` is additively separable; the abstract grid lemma
`grid_eq_zero_of_ncard_support_lt` then forces `a ≡ 0` (a nonzero separable grid fills a whole row
or column, needing `≥ min(w₁, w₂)` nonzeros).  This is the part of (3.8) used by (3.9.a) and most
§6/§7 consumers; the full row/column trichotomy (3.8.b)/(3.8.c) is only needed in §12+. -/
theorem sigmaCoeff_eq_zero_of_sigmaNC_lt (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (hNC : hyp.sigmaNC hVeq app ψ < min (Nat.card hyp.W1) (Nat.card hyp.W2))
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app ψ pq = 0 := by
  haveI : Finite G := Finite.of_fintype G
  refine grid_eq_zero_of_ncard_support_lt (fun pq => hyp.sigmaCoeff hVeq app ψ pq)
    (fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψ p p' q q') ?_ pq
  rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
  exact hNC

/-! ### Peterfalvi (3.9)(a): the `σ`-image of `ω ∈ Irr(W)` is determined by its values on `V` -/

/-- `w₁ = |W₁| ≥ 3`: `|W₁|` is odd (it divides the odd `|W|`) and `> 1` (`W₁` is nontrivial). -/
theorem three_le_card_W1 (hyp : TICyclicHypothesis G) : 3 ≤ Nat.card hyp.W1 := by
  haveI : Finite G := Finite.of_fintype G
  have hodd : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have hgt : 1 < Nat.card hyp.W1 :=
    Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
  obtain ⟨k, hk⟩ := hodd
  omega

/-- `w₂ = |W₂| ≥ 3`: `|W₂|` is odd (it divides the odd `|W|`) and `> 1` (`W₂` is nontrivial). -/
theorem three_le_card_W2 (hyp : TICyclicHypothesis G) : 3 ≤ Nat.card hyp.W2 := by
  haveI : Finite G := Finite.of_fintype G
  have hodd : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have hgt : 1 < Nat.card hyp.W2 :=
    Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **(3.9)(a) support bound**: a norm-`1` virtual character `χ` (i.e. `χ ∈ ±Irr(G)`) has at most
one nonzero inner product against the orthonormal family `(χ_{ij})`.  By the norm-`1` classifier
`χ = ε • μ`, and any `χ_{pq}` with `⟨χ, χ_{pq}⟩ ≠ 0` equals `±μ`; two distinct such indices would
give `⟨χ_{pq}, χ_{p'q'}⟩ = ±1 ≠ 0`, contradicting the orthonormality of the family. -/
theorem ncard_inner_chiFam_ne_zero_le_one (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) (hχ1 : ClassFunction.inner χ χ = 1) :
    {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
      ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0}.ncard ≤ 1 := by
  classical
  haveI : Finite G := Finite.of_fintype G
  obtain ⟨ε, μ, hε, hχrepr⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hχ hχ1
  -- any index in the support has `χ_{pq} = ±μ`
  have hkey : ∀ pq, ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0 →
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
        hyp.chiFam hVeq app pq = δ • (μ : ClassFunction G ℂ) := by
    intro pq hpq
    have hnorm : ClassFunction.inner (hyp.chiFam hVeq app pq) (hyp.chiFam hVeq app pq) = 1 := by
      rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
    obtain ⟨δ, ν, hδ, hνrepr⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one
      ((hyp.chiFam_spec hVeq app).2.1 pq) hnorm
    refine ⟨δ, hδ, ?_⟩
    have hμν : μ = ν := by
      by_contra hne
      apply hpq
      rw [hχrepr, hνrepr, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
        ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
        irreducibleCharacter_inner_eq_ite, if_neg hne, mul_zero, mul_zero]
    rw [hνrepr, hμν]
  -- two indices in the support coincide (their `χ`-values are both `±μ`, hence not orthogonal)
  by_cases hempty :
      {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
        ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0} = ∅
  · rw [hempty]; simp
  · obtain ⟨pq₀, hpq₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨δ₀, hδ₀, hrepr₀⟩ := hkey pq₀ hpq₀
    have hsub : {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
        ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0} ⊆ {pq₀} := by
      intro pq hpq
      obtain ⟨δ, hδ, hrepr⟩ := hkey pq hpq
      have hinner : ClassFunction.inner (hyp.chiFam hVeq app pq)
          (hyp.chiFam hVeq app pq₀) ≠ 0 := by
        rw [hrepr, hrepr₀, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
          ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
          irreducibleCharacter_inner_eq_ite, if_pos rfl, star_intCast, mul_one]
        rcases hδ with rfl | rfl <;> rcases hδ₀ with rfl | rfl <;> norm_num
      rw [(hyp.chiFam_spec hVeq app).2.2.1] at hinner
      by_cases heq : pq = pq₀
      · exact heq
      · rw [if_neg heq] at hinner; exact absurd rfl hinner
    calc {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
          ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0}.ncard
        ≤ ({pq₀} : Set _).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton pq₀

/-- **(3.9)(a)-norm-`2` support bound**: a norm-`2` virtual character `χ ∈ ZIrr(G)` has at most two
nonzero `σ`-image coefficients.  By `mem_ZIrr_inner_self_eq_sum_sq` +
`exists_pair_of_sum_sq_eq_two`, `χ = ε_α·α + ε_β·β` for two distinct irreducibles `α, β`; each has
`≤ 1` nonzero inner product against the orthonormal `χ`-family (`ncard_inner_chiFam_ne_zero_le_one`),
and the coefficient support is contained in `S_α ∪ S_β`.  This is the norm-`2` analogue of
`ncard_inner_chiFam_ne_zero_le_one`, used by the (4.8)/(10.5) Dade-image trichotomy endgames. -/
theorem ncard_sigmaCoeff_ne_zero_le_two (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) (hχ2 : ClassFunction.inner χ χ = 2) :
    {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
      hyp.sigmaCoeff hVeq app χ pq ≠ 0}.ncard ≤ 2 := by
  classical
  haveI : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hχ
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hχ2
  obtain ⟨α, β, hαβ, hs, -, -⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hαZ : α ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨α, hαm⟩ : IrreducibleCharacter G)
  have hβZ : β ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨β, hβm⟩ : IrreducibleCharacter G)
  have hα1 : ClassFunction.inner α α = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ⟨α, hαm⟩
    rwa [if_pos rfl] at this
  have hβ1 : ClassFunction.inner β β = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ⟨β, hβm⟩
    rwa [if_pos rfl] at this
  have hχαβ : χ = (c α : ℂ) • α + (c β : ℂ) • β := by
    rw [hrepr, hs, Finset.sum_pair hαβ]
  refine le_trans (Set.ncard_le_ncard (t :=
    {pq | ClassFunction.inner α (hyp.chiFam hVeq app pq) ≠ 0} ∪
    {pq | ClassFunction.inner β (hyp.chiFam hVeq app pq) ≠ 0})
    ?_ (Set.toFinite _)) (le_trans (Set.ncard_union_le _ _) ?_)
  · intro pq hpq
    simp only [sigmaCoeff, Set.mem_setOf_eq] at hpq
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    exact hpq (by rw [hχαβ, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, hcon.1, hcon.2, mul_zero, mul_zero, add_zero])
  · exact add_le_add
      (hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app hαZ hα1)
      (hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app hβZ hβ1)

open scoped Classical in
/-- **Bessel `NC` bound** (general norm): a virtual character `χ ∈ ZIrr(G)` with squared norm `N`
has at most `N` nonzero `σ`-image coefficients, `NC(χ) ≤ N`.  Writing `χ = ∑_a c_a·a` over its
irreducible constituents (`mem_ZIrr_inner_self_eq_sum_sq`), every index `pq` of the `σ`-coefficient
support has some constituent `a` with `⟨a, χ_{pq}⟩ ≠ 0`; the per-constituent supports each have
`≤ 1` element (`ncard_inner_chiFam_ne_zero_le_one`), so `NC(χ) ≤ |supp(c)| ≤ ∑_a c_a² = ‖χ‖² = N`
(each nonzero `c_a` contributes `c_a² ≥ 1`).  The norm-`1` (`…le_one`) and norm-`2` (`…le_two`)
support bounds are special cases; this is the form used by the coherence-free (10.9) `NC < 2w₁`
estimate (`NC ≤ w₁ + 1`). -/
theorem ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} {N : ℕ} (hχ : χ ∈ ZIrr G)
    (hχN : ClassFunction.inner χ χ = (N : ℂ)) :
    hyp.sigmaNC hVeq app χ ≤ N := by
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hχ
  -- `∑_a c_a² = N` as integers.
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = (N : ℤ) := by
    have h : (∑ a ∈ c.support, (c a : ℂ) ^ 2) = (N : ℂ) := hsq.symm.trans hχN
    have hcast : ((∑ a ∈ c.support, c a ^ 2 : ℤ) : ℂ) = (N : ℂ) := by push_cast; exact h
    exact_mod_cast hcast
  rw [TICyclicHypothesis.sigmaNC,
    show {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
        hyp.sigmaCoeff hVeq app χ pq ≠ 0}
      = ↑(Finset.univ.filter (fun pq => hyp.sigmaCoeff hVeq app χ pq ≠ 0)) by
        ext pq
        simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and],
    Set.ncard_coe_finset]
  calc (Finset.univ.filter (fun pq => hyp.sigmaCoeff hVeq app χ pq ≠ 0)).card
      ≤ (c.support.biUnion (fun a => Finset.univ.filter
            (fun pq => ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0))).card := by
        refine Finset.card_le_card (fun pq hpq => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpq
        rw [Finset.mem_biUnion]
        by_contra hcon
        push Not at hcon
        apply hpq
        change ClassFunction.inner χ (hyp.chiFam hVeq app pq) = 0
        rw [hrepr, inner_sum_left]
        refine Finset.sum_eq_zero (fun a ha => ?_)
        have := hcon a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
        rw [ClassFunction.inner_smul_left, this, mul_zero]
    _ ≤ ∑ a ∈ c.support, (Finset.univ.filter
            (fun pq => ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ a ∈ c.support, 1 := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        have haZ : a ∈ ZIrr G :=
          IrreducibleCharacter.mem_ZIrr (⟨a, hsupp (Finset.mem_coe.mpr ha)⟩ : IrreducibleCharacter G)
        have ha1 : ClassFunction.inner a a = 1 := by
          have := irreducibleCharacter_inner_eq_ite
            (⟨a, hsupp (Finset.mem_coe.mpr ha)⟩ : IrreducibleCharacter G)
            ⟨a, hsupp (Finset.mem_coe.mpr ha)⟩
          rwa [if_pos rfl] at this
        have hle := hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
        rwa [show {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
            ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0}
          = ↑(Finset.univ.filter (fun pq => ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0))
          by
            ext pq
            simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and], Set.ncard_coe_finset] at hle
    _ = c.support.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ N := by
        have hb : (c.support.card : ℤ) ≤ ∑ a ∈ c.support, c a ^ 2 := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          refine Finset.sum_le_sum (fun a ha => ?_)
          have hne : c a ≠ 0 := Finsupp.mem_support_iff.mp ha
          have h0 : (0 : ℤ) ≤ c a ^ 2 := sq_nonneg _
          have hnz : c a ^ 2 ≠ 0 := pow_ne_zero 2 hne
          push_cast; omega
        rw [hsumZ] at hb
        exact_mod_cast hb

/-- **(3.9)(a)-norm-`2` coefficient bound**: the `σ`-image coefficients of a norm-`2` virtual
character `χ ∈ ZIrr(G)` lie in `{0, ±1}`.  Writing `χ = ε_α·α + ε_β·β` (norm-`2` ⟹ two constituents)
and `χ_{pq} = ε·ν` (norm-`1` classifier), the coefficient `⟨χ, χ_{pq}⟩` is `ε_α·ε` if `ν = α`,
`ε_β·ε` if `ν = β`, and `0` otherwise (`α ≠ β`).  Norm-`2` analogue of the norm-`1` support bound,
used by the (4.8)/(10.5) trichotomy endgames to exclude a `±2` row coefficient. -/
theorem sigmaCoeff_eq_zero_or_one_of_inner_self_two (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) (hχ2 : ClassFunction.inner χ χ = 2)
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app χ pq = 0 ∨ hyp.sigmaCoeff hVeq app χ pq = 1 ∨
      hyp.sigmaCoeff hVeq app χ pq = -1 := by
  classical
  haveI : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hχ
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hχ2
  obtain ⟨α, β, hαβ, hs, hcα, hcβ⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  obtain ⟨ε, ν, hε, hν⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one
    ((hyp.chiFam_spec hVeq app).2.1 pq)
    (by rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl])
  have hαν : ClassFunction.inner α (ν : ClassFunction G ℂ)
      = if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ν
  have hβν : ClassFunction.inner β (ν : ClassFunction G ℂ)
      = if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ν
  have hf : hyp.sigmaCoeff hVeq app χ pq
      = (c α : ℂ) * ((ε : ℂ) * (if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0))
        + (c β : ℂ) * ((ε : ℂ) * (if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0)) := by
    rw [sigmaCoeff, hrepr, hs, Finset.sum_pair hαβ, hν,
      ← Int.cast_smul_eq_zsmul ℂ ε, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast, hαν, hβν]
  rw [hf]
  by_cases hαe : (⟨α, hαm⟩ : IrreducibleCharacter G) = ν
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · exact absurd (Subtype.ext_iff.mp (hαe.trans hβe.symm)) hαβ
    · rw [if_pos hαe, if_neg hβe]
      simp only [mul_one, mul_zero, add_zero]
      rcases hcα with hcα | hcα <;> rcases hε with hε | hε <;> rw [hcα, hε] <;> norm_num
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · rw [if_neg hαe, if_pos hβe]
      simp only [mul_one, mul_zero, zero_add]
      rcases hcβ with hcβ | hcβ <;> rcases hε with hε | hε <;> rw [hcβ, hε] <;> norm_num
    · rw [if_neg hαe, if_neg hβe]; left; ring

/-- **Peterfalvi (3.9)(a)** (§6 keystone): if `χ ∈ ±Irr(G)` (a virtual character of norm `1`)
agrees with `ω ∈ Irr(W)` on `V`, then `χ = ω^σ`.  The difference `φ = ω^σ − χ` vanishes on `V`
((3.2)(c) + the hypothesis), and its `σ`-coefficient support is contained in
`{index of ω} ∪ {pq | ⟨χ, χ_{pq}⟩ ≠ 0}`, so `NC(φ) ≤ 2 < 3 ≤ min(w₁, w₂)`; the (3.8) corollary
then kills all coefficients of `φ`.  At the `ω`-index this gives `⟨χ, ω^σ⟩ = 1`, whence
`‖χ − ω^σ‖² = 1 − 1 − 1 + 1 = 0` and positive definiteness concludes. -/
theorem eq_sigma_of_apply_eq_on_V (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) {χ : ClassFunction G ℂ}
    (hχ : χ ∈ ZIrr G) (hχ1 : ClassFunction.inner χ χ = 1)
    (hres : ∀ v (hv : v ∈ hyp.V), χ v = (ω : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩) :
    χ = hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  -- the difference `φ = ω^σ − χ` vanishes on `V` ((3.2)(c) + the hypothesis)
  have hφV : ∀ v ∈ hyp.V,
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ) v = 0 := by
    intro v hv
    rw [ClassFunction.sub_apply, hres v hv, hyp.sigma_apply_of_mem_V hVeq app _ hv, sub_self]
  -- `ω^σ` is the family member at the `ω`-index
  have hσωeq : hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω) :=
    hyp.sigma_irreducibleCharacter hVeq app ω
  -- `NC(φ) ≤ 2 < 3 ≤ min(w₁, w₂)`
  have hNC : hyp.sigmaNC hVeq app (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ)
      < min (Nat.card hyp.W1) (Nat.card hyp.W2) := by
    have hsub : {pq | hyp.sigmaCoeff hVeq app
          (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ) pq ≠ 0}
        ⊆ insert (hyp.omegaIrrEquiv.symm ω)
            {pq | ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0} := by
      intro pq hpq
      simp only [Set.mem_setOf_eq, sigmaCoeff] at hpq
      by_cases h0 : pq = hyp.omegaIrrEquiv.symm ω
      · exact Set.mem_insert_iff.mpr (Or.inl h0)
      · refine Set.mem_insert_iff.mpr (Or.inr ?_)
        simp only [Set.mem_setOf_eq]
        intro hc
        apply hpq
        rw [ClassFunction.inner_sub_left, hc, hσωeq, (hyp.chiFam_spec hVeq app).2.2.1,
          if_neg (fun h => h0 h.symm), sub_zero]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hins := Set.ncard_insert_le (hyp.omegaIrrEquiv.symm ω)
      {pq | ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0}
    have hone := hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app hχ hχ1
    have h31 := hyp.three_le_card_W1
    have h32 := hyp.three_le_card_W2
    simp only [sigmaNC]
    omega
  -- all `σ`-coefficients of `φ` vanish; at the `ω`-index this gives `⟨χ, ω^σ⟩ = 1`
  have hσσ : ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    rw [hyp.sigma_inner hVeq app, irreducibleCharacter_inner_eq_ite, if_pos rfl]
  have hinner : ClassFunction.inner χ (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    have h0 : ClassFunction.inner
        (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ)
        (hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω)) = 0 :=
      hyp.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hφV hNC (hyp.omegaIrrEquiv.symm ω)
    rw [← hσωeq, ClassFunction.inner_sub_left, hσσ] at h0
    linear_combination -h0
  -- `‖χ − ω^σ‖² = 0` ⟹ `χ = ω^σ`
  have hfinal : ClassFunction.inner
      (χ - hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (χ - hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 0 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hχ1, hinner, hσσ,
      inner_conj_symm χ (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)), hinner, star_one]
    norm_num
  have hsub0 : χ - hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) = 0 :=
    eq_zero_of_inner_self_re_eq_zero (by rw [hfinal]; exact Complex.zero_re)
  exact sub_eq_zero.mp hsub0

/-- **Peterfalvi (3.9)(a)** ("in particular"): `σ` commutes with coefficientwise field
automorphisms on `Irr(W)`: `(ω^σ)^u = (ω^u)^σ` for any `u : ℂ ≃+* ℂ`.  Indeed `(ω^σ)^u` is again
a norm-`1` virtual character (`ω^σ = ±μ` by the norm-`1` classifier, and `u` maps `±Irr(G)` into
`±Irr(G)`), and on `V` it agrees with `ω^u` (apply `u` inside (3.2)(c)); the main part of (3.9)(a)
then identifies it with `(ω^u)^σ`.  No star-commutation hypothesis on `u` is needed. -/
theorem sigma_mapRingEquiv_comm (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (u : ℂ ≃+* ℂ) (ω : IrreducibleCharacter hyp.W) :
    ClassFunction.mapRingEquiv u (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      = hyp.sigma hVeq app
          ((IrreducibleCharacter.galoisMap u ω : IrreducibleCharacter hyp.W) :
            ClassFunction hyp.W ℂ) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  have hσZ : hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
    hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr ω.2)
  have hσ1 : ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    rw [hyp.sigma_inner hVeq app, irreducibleCharacter_inner_eq_ite, if_pos rfl]
  obtain ⟨ε, μ, hε, hrepr⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hσZ hσ1
  refine hyp.eq_sigma_of_apply_eq_on_V hVeq app (IrreducibleCharacter.galoisMap u ω)
    (ClassFunction.mapRingEquiv_mem_ZIrr u hσZ) ?_ ?_
  · -- norm `1`: `(ω^σ)^u = ε • μ^u` with `μ^u ∈ Irr(G)`
    rw [hrepr, ClassFunction.mapRingEquiv_zsmul, ← Int.cast_smul_eq_zsmul ℂ,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      star_intCast, ← IrreducibleCharacter.galoisMap_apply_coe,
      irreducibleCharacter_inner_eq_ite, if_pos rfl, mul_one]
    rcases hε with rfl | rfl <;> norm_num
  · -- values on `V`: `u ((ω^σ)(v)) = u (ω(v)) = (ω^u)(v)` by (3.2)(c)
    intro v hv
    rw [ClassFunction.mapRingEquiv_apply, hyp.sigma_apply_of_mem_V hVeq app _ hv,
      IrreducibleCharacter.galoisMap_apply_apply]

/-! ### Peterfalvi (3.9)(b): `σ` and powers of a linear character -/

/-- Every linear character of the finite `W` has finite multiplicative order:
`ξ ^ |W| = 1` pointwise. -/
theorem orderOf_char_ne_zero (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    (ξ : hyp.W →* ℂˣ) : orderOf ξ ≠ 0 := by
  have hξpow : ξ ^ Fintype.card hyp.W = 1 := by
    ext w
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
  exact ((isOfFinOrder_iff_pow_eq_one.mpr
    ⟨Fintype.card hyp.W, Fintype.card_pos, hξpow⟩).orderOf_pos).ne'

/-- **Peterfalvi (3.9)(b)**: let `a` be the multiplicative order of the linear character `ξ` of
`W` and let `k` be coprime to `a`.  There is a ring automorphism `u` of `ℂ` such that
`(ω(ξ^k))^σ = (ω(ξ))^{σu}`; moreover `(ω(ξ^k))^σ(g) = (ω(ξ))^σ(g)` for every `g : G` of order
prime to `a`.

The automorphism is `(· ^ k)` on `a`-th roots of unity and the identity on `B`-th roots, where
`B` is the product of the divisors of `|G|` coprime to `a` ((1.9), CRT form
`exists_complexRingEquiv_pow_and_fixed`).  Since `ξ` takes values in the `a`-th roots,
`ω(ξ^k) = (ω(ξ))^u`, and `σ` commutes with `u` by (3.9)(a); at `g` of order prime to `a` the
eigenvalues of `g` are `B`-th roots of unity, which `u` fixes. -/
theorem exists_mapRingEquiv_sigma_omega_pow (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ξ : hyp.W →* ℂˣ) {k : ℕ} (hk : k.Coprime (orderOf ξ)) :
    ∃ u : ℂ ≃+* ℂ,
      hyp.sigma hVeq app (hyp.omega (ξ ^ k) : ClassFunction hyp.W ℂ)
        = ClassFunction.mapRingEquiv u
            (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ)) ∧
      ∀ g : G, (orderOf g).Coprime (orderOf ξ) →
        hyp.sigma hVeq app (hyp.omega (ξ ^ k) : ClassFunction hyp.W ℂ) g
          = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g := by
  classical
  haveI : Finite G := Finite.of_fintype G
  have ha : orderOf ξ ≠ 0 := hyp.orderOf_char_ne_zero ξ
  -- `B` = product of the divisors of `|G|` coprime to `a`: coprime to `a`, and any
  -- `orderOf g` coprime to `a` divides it
  set B := ((Nat.card G).divisors.filter (fun d => d.Coprime (orderOf ξ))).prod id with hB_def
  have hB : B ≠ 0 :=
    (Finset.prod_pos fun d hd => Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1).ne'
  have hab : (orderOf ξ).Coprime B :=
    Nat.coprime_prod_right_iff.mpr fun d hd =>
      Nat.coprime_comm.mp (Finset.mem_filter.mp hd).2
  obtain ⟨u, hua, huB⟩ := exists_complexRingEquiv_pow_and_fixed ha hB hab hk
  -- the bridge `ω(ξ^k) = (ω(ξ))^u`: the values of `ξ` are `a`-th roots of unity
  have hbridge : (hyp.omega (ξ ^ k) : ClassFunction hyp.W ℂ)
      = (IrreducibleCharacter.galoisMap u (hyp.omega ξ) : ClassFunction hyp.W ℂ) := by
    ext w
    rw [IrreducibleCharacter.galoisMap_apply_apply, omega_apply, omega_apply,
      MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    refine (hua (ξ w : ℂ) ?_).symm
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one ξ,
      MonoidHom.one_apply, Units.val_one]
  refine ⟨u, ?_, ?_⟩
  · rw [hbridge]
    exact (hyp.sigma_mapRingEquiv_comm hVeq app u (hyp.omega ξ)).symm
  · -- the value part: at `g` of order coprime to `a`, the eigenvalues are `B`-th roots
    intro g hg
    have hdvdB : orderOf g ∣ B := by
      refine Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨?_, hg⟩)
      exact Nat.mem_divisors.mpr ⟨orderOf_dvd_natCard g, Nat.card_pos.ne'⟩
    have hσZ : hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
      hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr (hyp.omega ξ).2)
    have hval := mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr hσZ u
      (isOfFinOrder_of_finite g) (k := 1) (fun ζ hζ => by
        rw [pow_one]
        refine huB ζ ?_
        obtain ⟨c, hc⟩ := hdvdB
        rw [hc, pow_mul, hζ, one_pow])
    rw [hbridge, ← hyp.sigma_mapRingEquiv_comm hVeq app u (hyp.omega ξ), hval, pow_one]

end TICyclicHypothesis

/-! ### Peterfalvi (3.9)(c): ingredients

Three `TICyclic`-independent ingredients for (3.9)(c): virtual-character values are algebraic
integers (candidate for `ClassSumAlgebra`), every ring automorphism of `ℂ` acts on `a`-th roots
of unity as a power map (candidate for `CyclotomicGaloisAction`), and a complex number that is
integral over `ℚ` and fixed by every ring automorphism of `ℂ` is rational (candidate for
`CyclotomicGaloisAction`).  They are kept here to leave the active frontier in this leaf. -/

/-- Virtual-character values are algebraic integers: each irreducible character value is a sum
of roots of unity (`character_isIntegral`), and `IsIntegral ℤ` is closed under the `ℤ`-span
operations. -/
theorem isIntegral_apply_of_mem_ZIrr {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (g : G) :
    IsIntegral ℤ (φ g) := by
  haveI : Finite G := Finite.of_fintype G
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ := IsIrreducibleCharacter.isCharacter hx
      rw [show x g = ρ.character g from congrFun hchar g]
      exact character_isIntegral ρ g
  | zero => rw [ClassFunction.zero_apply]; exact isIntegral_zero
  | add a b _ _ ha hb => rw [ClassFunction.add_apply]; exact ha.add hb
  | smul n a _ ha =>
      rw [ClassFunction.zsmul_apply, zsmul_eq_mul]
      exact (isIntegral_algebraMap (x := n)).mul ha

/-- Every ring automorphism of `ℂ` acts on the `a`-th roots of unity as `(· ^ i)` for some `i`
coprime to `a`: the image of a primitive root `ζ₀` is again a primitive root, hence `ζ₀ ^ i`
with `i` coprime to `a`, and every `a`-th root is a power of `ζ₀`. -/
theorem exists_pow_forall_rootsOfUnity (u : ℂ ≃+* ℂ) {a : ℕ} (ha : a ≠ 0) :
    ∃ i : ℕ, i.Coprime a ∧ ∀ ζ : ℂ, ζ ^ a = 1 → u ζ = ζ ^ i := by
  haveI : NeZero a := ⟨ha⟩
  have hζ₀ := Complex.isPrimitiveRoot_exp a ha
  have hupow : u (Complex.exp (2 * Real.pi * Complex.I / a)) ^ a = 1 := by
    rw [← map_pow, hζ₀.pow_eq_one, map_one]
  obtain ⟨i, _, hi⟩ := hζ₀.eq_pow_of_pow_eq_one hupow
  have hprim : IsPrimitiveRoot (u (Complex.exp (2 * Real.pi * Complex.I / a))) a :=
    hζ₀.map_of_injective u.injective
  have hcop : i.Coprime a := by
    rw [← hi] at hprim
    exact (hζ₀.pow_iff_coprime (Nat.pos_of_ne_zero ha) i).mp hprim
  refine ⟨i, hcop, fun ζ hζ => ?_⟩
  obtain ⟨m, _, hm⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [← hm, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm i m]

/-- A complex number that is integral over `ℚ` and fixed by every ring automorphism of `ℂ` is
rational.  The subfield `K = ℚ(rootSet p ℂ)` generated by the roots of `p = minpoly ℚ x` is a
splitting field, hence normal over `ℚ`; any root `y` of `p` is then `v x` for some
`v : K ≃ₐ[ℚ] K` (`IsConjRoot.exists_algEquiv`), and extending `v` to `ℂ`
(`exists_complexRingEquiv_extends`) the fixed-point hypothesis forces `y = x`.  So the separable
`p` has a single root in `ℂ`, hence degree `1`. -/
theorem exists_ratCast_of_forall_complexRingEquiv_eq {x : ℂ} (hint : IsIntegral ℚ x)
    (hfix : ∀ u : ℂ ≃+* ℂ, u x = x) : ∃ q : ℚ, x = (q : ℂ) := by
  classical
  have hsplits : ((minpoly ℚ x).map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  haveI : (minpoly ℚ x).IsSplittingField ℚ
      (IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplits
  haveI : Normal ℚ (IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) :=
    Normal.of_isSplittingField (minpoly ℚ x)
  have hxroot : x ∈ (minpoly ℚ x).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval ℚ x⟩
  have hxK : x ∈ IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ) :=
    IntermediateField.subset_adjoin ℚ _ hxroot
  -- every root of `minpoly ℚ x` equals `x`
  have hall : ∀ y ∈ (minpoly ℚ x).rootSet ℂ, y = x := by
    intro y hy
    have hyK : y ∈ IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ) :=
      IntermediateField.subset_adjoin ℚ _ hy
    -- `⟨y⟩` is a conjugate root of `⟨x⟩` in the normal extension `K/ℚ`
    have hminy : minpoly ℚ y = minpoly ℚ x :=
      (isConjRoot_of_aeval_eq_zero hint (Polynomial.mem_rootSet.mp hy).2).symm
    have hconj : IsConjRoot ℚ
        (⟨y, hyK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ))
        (⟨x, hxK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) := by
      show minpoly ℚ _ = minpoly ℚ _
      calc minpoly ℚ (⟨y, hyK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ))
          = minpoly ℚ y := IntermediateField.minpoly_eq _
        _ = minpoly ℚ x := hminy
        _ = minpoly ℚ (⟨x, hxK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) :=
            (IntermediateField.minpoly_eq
              (⟨x, hxK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ))).symm
    obtain ⟨v, hv⟩ := hconj.exists_algEquiv
    obtain ⟨u, hu⟩ := exists_complexRingEquiv_extends _ v.toRingEquiv
    have hux : u x = y := by
      have h := hu ⟨x, hxK⟩
      rw [show v.toRingEquiv ⟨x, hxK⟩ = v ⟨x, hxK⟩ from rfl, hv] at h
      exact h
    rw [← hux, hfix u]
  -- `minpoly ℚ x` is separable with a single root, hence has degree `1`
  have hone : Fintype.card ((minpoly ℚ x).rootSet ℂ) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨x, hxroot⟩, fun z => Subtype.ext (hall z.1 z.2)⟩
  have hdeg : (minpoly ℚ x).natDegree = 1 := by
    rw [← Polynomial.card_rootSet_eq_natDegree (minpoly.irreducible hint).separable hsplits,
      hone]
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp hdeg
  exact ⟨q, by rw [← hq, eq_ratCast]⟩

namespace TICyclicHypothesis

/-- **Peterfalvi (3.9)(c)**: if `g : G` has order prime to the multiplicative order `a` of the
linear character `ξ` of `W`, then `(ω(ξ))^σ(g) ∈ ℤ`.

The value is an algebraic integer (`isIntegral_apply_of_mem_ZIrr`), and it is fixed by every
ring automorphism `u` of `ℂ`: `u` acts on `a`-th roots of unity as `(· ^ i)` with `i` coprime
to `a` (`exists_pow_forall_rootsOfUnity`), so `(ω(ξ))^{σu} = (ω(ξ^i))^σ` by (3.9)(a), whose
value at `g` is `(ω(ξ))^σ(g)` by the value part of (3.9)(b).  Rationality follows by
`exists_ratCast_of_forall_complexRingEquiv_eq`, and a rational algebraic integer is an
integer. -/
theorem exists_intCast_sigma_omega_apply (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ξ : hyp.W →* ℂˣ) {g : G} (hg : (orderOf g).Coprime (orderOf ξ)) :
    ∃ n : ℤ, hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g = (n : ℂ) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  have ha : orderOf ξ ≠ 0 := hyp.orderOf_char_ne_zero ξ
  have hσZ : hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
    hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr (hyp.omega ξ).2)
  -- the value is fixed by every ring automorphism of `ℂ`
  have hfix : ∀ u : ℂ ≃+* ℂ,
      u (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g)
        = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g := by
    intro u
    obtain ⟨i, hicop, hipow⟩ := exists_pow_forall_rootsOfUnity u ha
    -- `(ω(ξ))^u = ω(ξ^i)`: `u` is `(· ^ i)` on the values of `ξ`
    have hbridge : (IrreducibleCharacter.galoisMap u (hyp.omega ξ) : ClassFunction hyp.W ℂ)
        = (hyp.omega (ξ ^ i) : ClassFunction hyp.W ℂ) := by
      ext w
      rw [IrreducibleCharacter.galoisMap_apply_apply, omega_apply, omega_apply,
        MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
      refine hipow (ξ w : ℂ) ?_
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one ξ,
        MonoidHom.one_apply, Units.val_one]
    obtain ⟨_, _, hval⟩ := hyp.exists_mapRingEquiv_sigma_omega_pow hVeq app ξ hicop
    calc u (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g)
        = ClassFunction.mapRingEquiv u
            (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ)) g :=
          (ClassFunction.mapRingEquiv_apply u _ g).symm
      _ = hyp.sigma hVeq app
            (IrreducibleCharacter.galoisMap u (hyp.omega ξ) : ClassFunction hyp.W ℂ) g := by
          rw [hyp.sigma_mapRingEquiv_comm hVeq app u (hyp.omega ξ)]
      _ = hyp.sigma hVeq app (hyp.omega (ξ ^ i) : ClassFunction hyp.W ℂ) g := by
          rw [hbridge]
      _ = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g := hval g hg
  -- algebraic integer and rational, hence an integer
  have hint : IsIntegral ℤ (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g) :=
    isIntegral_apply_of_mem_ZIrr hσZ g
  obtain ⟨q, hq⟩ := exists_ratCast_of_forall_complexRingEquiv_eq (hint.tower_top (A := ℚ)) hfix
  obtain ⟨n, hn⟩ := isIntegral_rat_imp_int (hq ▸ hint)
  exact ⟨n, hq.trans hn⟩


end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
