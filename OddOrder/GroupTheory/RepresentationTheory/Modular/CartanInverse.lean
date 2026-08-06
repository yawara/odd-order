/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularClassIndex
import OddOrder.GroupTheory.RepresentationTheory.Modular.ProjectiveCharacterVanishing

/-!
# The orthogonality of `Φ_θ` against `IBr(G)`

Navarro (2.13) says `[Φ_θ, φ]⁰ = δ_{θφ}`, and hence that `([θ,φ]⁰)` inverts the Cartan matrix.
This file proves the matrix content of that statement.

Index the `p`-regular classes by `ι` (`PRegularClassIndex`) and write `x_j` for the chosen
`p`-regular representative.  Then

`A_{j φ} := Φ_φ(x_j)`,  `B_{φ j} := φ(x_j⁻¹) / |C_G(x_j)|`

satisfy `A · B = 1`: that is exactly
`∑_φ Φ_φ(x_j) φ(x_{j'}⁻¹) = |C_G(x_{j'})| δ_{j j'}`
(`algebraMap_sum_projectiveIndecomposableCharacter_mul_inv`), and the classes are pairwise
non-conjugate.  Both matrices are **square**, because `|IBr(G)| = #cl(G°)`, so the inverse is
two-sided and `B · A = 1` — which is `[Φ_θ, φ]⁰ = δ_{θφ}` once the pairing is written as a sum
over the `p`-regular classes.

## Main results

* `OddOrder.RepresentationTheory.Modular.isUnit_card_centralizer`
* `OddOrder.RepresentationTheory.Modular.projMatrix_mul_brauerMatrix` — `A · B = 1`
* `OddOrder.RepresentationTheory.Modular.brauerMatrix_mul_projMatrix` — `B · A = 1`
* `OddOrder.RepresentationTheory.Modular.sum_brauer_mul_projectiveIndecomposableCharacter` —
  `∑_j |C_G(x_j)|⁻¹ φ(x_j⁻¹) Φ_θ(x_j) = δ_{φθ}`
* `OddOrder.RepresentationTheory.Modular.pairingZero` — Navarro's `[a, b]⁰`
* `OddOrder.RepresentationTheory.Modular.pairingZero_projectiveIndecomposableCharacter` —
  `[Φ_θ, φ]⁰ = δ_{φθ}`
* `OddOrder.RepresentationTheory.Modular.sum_cartanMatrix_mul_pairingZero` — `([μ,φ]⁰)` inverts
  the Cartan matrix
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]

/-- The order of a centralizer is invertible in `K`: it divides `|G|`, which is. -/
theorem isUnit_card_centralizer (g : G) :
    IsUnit ((Nat.card (Subgroup.centralizer ({g} : Set G)) : K)) := by
  refine isUnit_of_mul_isUnit_right (x := (conjugacyClassSize (ConjClasses.mk g) : K)) ?_
  rw [show (conjugacyClassSize (ConjClasses.mk g) : K)
      * (Nat.card (Subgroup.centralizer ({g} : Set G)) : K) = (Nat.card G : K) from
    mod_cast congrArg (Nat.cast : ℕ → K)
      (conjugacyClassSize_mk_mul_card_centralizer (G := G) g)]
  exact isUnit_of_invertible _

variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-- The matrix of projective indecomposable characters on the `p`-regular classes. -/
noncomputable def projMatrix : Matrix ι ι K := fun j φ =>
  algebraMap 𝒪 K (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ
    (pRegularRep hp hπ hlin hkerJ j))

/-- The matrix of irreducible Brauer characters at inverses, weighted by `|C_G|⁻¹`. -/
noncomputable def brauerMatrix : Matrix ι ι K := fun φ j =>
  (Nat.card (Subgroup.centralizer ({pRegularRep hp hπ hlin hkerJ j} : Set G)) : K)⁻¹ *
    algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ
      (pRegularRep hp hπ hlin hkerJ j)⁻¹)

/-- **`A · B = 1`** — the defining relation of the projective indecomposable characters, read on
the `p`-regular class representatives. -/
theorem projMatrix_mul_brauerMatrix :
    projMatrix hp hω hω' hπ hlin hkerJ e * brauerMatrix hp hπ hlin hkerJ = 1 := by
  classical
  ext j j'
  set y := pRegularRep hp hπ hlin hkerJ j' with hy
  have hyreg : IsPRegular p y := isPRegular_pRegularRep hp hπ hlin hkerJ j'
  have hrel := algebraMap_sum_projectiveIndecomposableCharacter_mul_inv hp hω hω' hπ hlin hkerJ e
    (pRegularRep hp hπ hlin hkerJ j) hyreg
  rw [map_sum] at hrel
  have hunit := isUnit_card_centralizer (K := K) y
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hexp : ∀ φ : ι, projMatrix hp hω hω' hπ hlin hkerJ e j φ
      * brauerMatrix hp hπ hlin hkerJ φ j'
      = (Nat.card (Subgroup.centralizer ({y} : Set G)) : K)⁻¹ *
        algebraMap 𝒪 K (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ
            (pRegularRep hp hπ hlin hkerJ j)
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y⁻¹) := by
    intro φ
    simp only [projMatrix, brauerMatrix, map_mul, hy]
    ring
  rw [Finset.sum_congr rfl fun φ _ => hexp φ, ← Finset.mul_sum, hrel]
  by_cases h : j = j'
  · rw [if_pos h, if_pos (by rw [h]), inv_mul_cancel₀ hunit.ne_zero]
  · rw [if_neg h, if_neg fun hc =>
      h ((pRegularRep_isConj_iff hp hπ hlin hkerJ j' j).mp hc).symm, mul_zero]

/-- **`B · A = 1`** — the character table of the `p`-regular classes is square (`|IBr(G)| =
#cl(G°)`), so the one-sided inverse of `projMatrix_mul_brauerMatrix` is two-sided. -/
theorem brauerMatrix_mul_projMatrix :
    brauerMatrix hp hπ hlin hkerJ * projMatrix hp hω hω' hπ hlin hkerJ e = 1 :=
  mul_eq_one_comm.mp (projMatrix_mul_brauerMatrix hp hω hω' hπ hlin hkerJ e)

/-! ### Summing over the `p`-regular elements -/

omit [IsDomain 𝒪] [ValuationRing 𝒪] [DecidableEq ι] in
include hp hπ hlin hkerJ in
/-- **A class function vanishing off `G°` is summed over `G` by its `p`-regular class
representatives**, weighted by class size. -/
theorem sum_eq_sum_pRegularRep [Fintype G] {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ g h : G, IsConj g h → f g = f h) (hv : ∀ g : G, ¬ IsPRegular p g → f g = 0) :
    ∑ g : G, f g
      = ∑ j : ι, conjugacyClassSize (ConjClasses.mk (pRegularRep hp hπ hlin hkerJ j))
          • f (pRegularRep hp hπ hlin hkerJ j) := by
  classical
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hzero : ∀ C : ConjClasses G, C ∈ Finset.univ →
      C ∉ Finset.univ.filter (fun C : ConjClasses G => IsPRegularClass p C) →
      conjugacyClassSize C • f (conjugacyClassRepresentative C) = 0 := by
    intro C _ hC
    have hCreg : ¬ IsPRegularClass p C := by simpa using hC
    have : ¬ IsPRegular p (conjugacyClassRepresentative C) := by
      rw [← isPRegularClass_mk (p := p), conjugacyClassRepresentative_mk_eq]
      exact hCreg
    rw [hv _ this, smul_zero]
  have h1 : ∑ g : G, f g
      = ∑ C ∈ Finset.univ.filter (fun C : ConjClasses G => IsPRegularClass p C),
        conjugacyClassSize C • f (conjugacyClassRepresentative C) := by
    rw [sum_eq_sum_conjClasses f hf]
    exact (Finset.sum_subset (Finset.subset_univ _) hzero).symm
  have h2 : ∑ C ∈ Finset.univ.filter (fun C : ConjClasses G => IsPRegularClass p C),
        conjugacyClassSize C • f (conjugacyClassRepresentative C)
      = ∑ C : {C : ConjClasses G // IsPRegularClass p C},
        conjugacyClassSize (C : ConjClasses G) • f (conjugacyClassRepresentative C) :=
    Finset.sum_subtype _ (fun C => by simp) _
  rw [h1, h2, ← Equiv.sum_comp (equivPRegularClass hp hπ hlin hkerJ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmk := mk_pRegularRep hp hπ hlin hkerJ j
  have hconj : IsConj (conjugacyClassRepresentative
      (equivPRegularClass hp hπ hlin hkerJ j : ConjClasses G))
      (pRegularRep hp hπ hlin hkerJ j) := by
    refine ConjClasses.mk_eq_mk_iff_isConj.mp ?_
    rw [conjugacyClassRepresentative_mk_eq, hmk]
  rw [hmk, hf _ _ hconj]

omit [IsDomain 𝒪] [ValuationRing 𝒪] [DecidableEq ι] in
include hp hπ hlin hkerJ in
open scoped Classical in
/-- **A class function summed over the `p`-regular elements** is the class-size-weighted sum over
the `p`-regular class representatives. -/
theorem sum_pRegular_eq_sum_pRegularRep [Fintype G] {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ g h : G, IsConj g h → f g = f h) :
    ∑ g ∈ Finset.univ.filter (fun g : G => IsPRegular p g), f g
      = ∑ j : ι, conjugacyClassSize (ConjClasses.mk (pRegularRep hp hπ hlin hkerJ j))
          • f (pRegularRep hp hπ hlin hkerJ j) := by
  classical
  have hclass : ∀ g h : G, IsConj g h →
      (if IsPRegular p g then f g else 0) = (if IsPRegular p h then f h else 0) := by
    intro g h hc
    by_cases hg : IsPRegular p g
    · rw [if_pos hg, if_pos (isPRegular_of_isConj hg hc), hf _ _ hc]
    · rw [if_neg hg, if_neg fun hh => hg (isPRegular_of_isConj hh hc.symm)]
  have hvan : ∀ g : G, ¬ IsPRegular p g → (if IsPRegular p g then f g else 0) = 0 :=
    fun g hg => if_neg hg
  have hkey := sum_eq_sum_pRegularRep hp hπ hlin hkerJ
    (fun g => if IsPRegular p g then f g else 0) hclass hvan
  rw [← Finset.sum_filter] at hkey
  rw [hkey]
  exact Finset.sum_congr rfl fun j _ => by
    rw [if_pos (isPRegular_pRegularRep hp hπ hlin hkerJ j)]

/-- **`[Φ_θ, φ]⁰ = δ_{φθ}`, as a sum over the `p`-regular classes** — the matrix content of
Navarro (2.13). -/
theorem sum_brauer_mul_projectiveIndecomposableCharacter (φ θ : ι) :
    ∑ j : ι, (Nat.card (Subgroup.centralizer
          ({pRegularRep hp hπ hlin hkerJ j} : Set G)) : K)⁻¹ *
        algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ
            (pRegularRep hp hπ hlin hkerJ j)⁻¹
          * projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e θ
            (pRegularRep hp hπ hlin hkerJ j))
      = if φ = θ then 1 else 0 := by
  classical
  have hmul := congrFun (congrFun (brauerMatrix_mul_projMatrix hp hω hω' hπ hlin hkerJ e) φ) θ
  rw [Matrix.mul_apply, Matrix.one_apply] at hmul
  rw [← hmul]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [projMatrix, brauerMatrix, map_mul]
    ring

/-! ### Navarro's pairing `[a, b]⁰` -/

omit [HenselianLocalRing 𝒪] [DecidableEq ι] [Fintype ι'] [∀ (i : ι'), Nonempty (m i)]
  [Invertible (Nat.card G : K)] in
/-- The ordinary characters are class functions. -/
theorem ordinaryCharacter_eq_of_isConj (i : ι') {g h : G} (hc : IsConj g h) :
    ordinaryCharacter (𝒪 := 𝒪) e i g = ordinaryCharacter (𝒪 := 𝒪) e i h := by
  refine IsFractionRing.injective 𝒪 K ?_
  rw [algebraMap_ordinaryCharacter, algebraMap_ordinaryCharacter]
  exact character_eq_of_isConj _ hc

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsPModularSystem p 𝒪] [Finite G] [Fintype ι]
  [DecidableEq ι] [∀ (i : ι), Nonempty (nn i)] in
/-- The irreducible Brauer characters are class functions, in `IsConj` form. -/
theorem irreducibleBrauerCharacter_eq_of_isConj (φ : ι) {g h : G} (hc : IsConj g h) :
    irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g
      = irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ h := by
  obtain ⟨u, hu⟩ := hc
  have hh : (u : G) * g * ((u : G))⁻¹ = h := by rw [hu.eq]; group
  rw [← hh, irreducibleBrauerCharacter_conj]

omit [DecidableEq ι] [∀ (i : ι'), Nonempty (m i)] [Invertible (Nat.card G : K)] in
/-- The projective indecomposable characters are class functions. -/
theorem projectiveIndecomposableCharacter_eq_of_isConj (θ : ι) {g h : G} (hc : IsConj g h) :
    projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e θ g
      = projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e θ h :=
  Finset.sum_congr rfl fun i _ => by rw [ordinaryCharacter_eq_of_isConj e i hc]

open scoped Classical in
/-- **Navarro's pairing** `[a, b]⁰ = (1/|G|) ∑_{g ∈ G°} a(g) b(g⁻¹)`, for `𝒪`-valued class
functions, with values in the fraction field (`|G|` is not invertible in `𝒪`). -/
noncomputable def pairingZero (p : ℕ) (K : Type*) [Field K] [Algebra 𝒪 K] [Fintype G]
    [Invertible (Nat.card G : K)] (a b : G → 𝒪) : K :=
  (Nat.card G : K)⁻¹ * ∑ g ∈ Finset.univ.filter (fun g : G => IsPRegular p g),
    algebraMap 𝒪 K (a g * b g⁻¹)

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] [DecidableEq ι] in
include hp hπ hlin hkerJ in
open scoped Classical in
/-- **The pairing as a sum over the `p`-regular classes**, with the class sizes traded for
centralizer orders through `|C| · |C_G| = |G|`. -/
theorem pairingZero_eq_sum_pRegularRep [Fintype G] (a b : G → 𝒪)
    (ha : ∀ g h : G, IsConj g h → a g = a h) (hb : ∀ g h : G, IsConj g h → b g = b h) :
    pairingZero (𝒪 := 𝒪) p K a b
      = ∑ j : ι, (Nat.card (Subgroup.centralizer
            ({pRegularRep hp hπ hlin hkerJ j} : Set G)) : K)⁻¹ *
          algebraMap 𝒪 K (a (pRegularRep hp hπ hlin hkerJ j)
            * b (pRegularRep hp hπ hlin hkerJ j)⁻¹) := by
  classical
  have hclass : ∀ g h : G, IsConj g h →
      algebraMap 𝒪 K (a g * b g⁻¹) = algebraMap 𝒪 K (a h * b h⁻¹) := fun g h hc => by
    rw [ha _ _ hc, hb _ _ (IsConj.inv' hc)]
  rw [pairingZero, sum_pRegular_eq_sum_pRegularRep hp hπ hlin hkerJ _ hclass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set x := pRegularRep hp hπ hlin hkerJ j with hx
  have hsize : (conjugacyClassSize (ConjClasses.mk x) : K)
      * (Nat.card (Subgroup.centralizer ({x} : Set G)) : K) = (Nat.card G : K) :=
    mod_cast congrArg (Nat.cast : ℕ → K) (conjugacyClassSize_mk_mul_card_centralizer (G := G) x)
  have hGunit : ((Nat.card G : K)) ≠ 0 := (isUnit_of_invertible (Nat.card G : K)).ne_zero
  have hCunit : ((Nat.card (Subgroup.centralizer ({x} : Set G)) : K)) ≠ 0 :=
    (isUnit_card_centralizer (K := K) x).ne_zero
  rw [nsmul_eq_mul, ← mul_assoc]
  congr 1
  field_simp
  linear_combination hsize

include hp hπ hlin hkerJ in
/-- **`[Φ_θ, φ]⁰ = δ_{φθ}`** — Navarro (2.13). -/
theorem pairingZero_projectiveIndecomposableCharacter [Fintype G] (φ θ : ι) :
    pairingZero (𝒪 := 𝒪) p K
        (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e θ)
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ)
      = if φ = θ then 1 else 0 := by
  classical
  rw [pairingZero_eq_sum_pRegularRep hp hπ hlin hkerJ _ _
      (fun g h hc => projectiveIndecomposableCharacter_eq_of_isConj hp hω hω' hπ hlin hkerJ e θ hc)
      (fun g h hc => irreducibleBrauerCharacter_eq_of_isConj φ hc),
    ← sum_brauer_mul_projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ θ]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm (irreducibleBrauerCharacter _ _ _)]

omit [DecidableEq ι] in
include hp hω hω' hπ hlin hkerJ in
open scoped Classical in
/-- **`[Φ_μ, F]⁰ = d_μ`** for any function `F` that is given on the `p`-regular elements by an
expansion `F(y) = ∑_τ d_τ τ(y⁻¹)` in the irreducible Brauer characters:

`∑_{y ∈ G⁰} Φ_μ(y) F(y) = |G| d_μ`.

This is the only way `[Φ_θ, φ]⁰ = δ_{θφ}` gets used downstream.  The sum runs over an arbitrary
`Finset` cut out by `p`-regularity rather than over a literal `Finset.filter`, so that callers
never have to match the decidability instance baked into `pairingZero`. -/
theorem sum_projectiveIndecomposableCharacter_mul_eq (μ : ι)
    (F : G → K) (d : ι → K)
    (hF : ∀ y : G, IsPRegular p y →
      ∑ τ, d τ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹) = F y)
    (s : Finset G) (hs : ∀ y : G, y ∈ s ↔ IsPRegular p y) :
    ∑ y ∈ s, algebraMap 𝒪 K
        (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e μ y) * F y
      = (Nat.card G : K) * d μ := by
  letI : Fintype G := Fintype.ofFinite G
  have hGne : (Nat.card G : K) ≠ 0 := (isUnit_of_invertible _).ne_zero
  have hpair : ∀ τ : ι, (∑ y ∈ s, algebraMap 𝒪 K
        (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e μ y
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹))
      = (Nat.card G : K) * (if τ = μ then 1 else 0) := fun τ => by
    rw [← pairingZero_projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e τ μ,
      pairingZero, ← mul_assoc, mul_inv_cancel₀ hGne, one_mul]
    exact Finset.sum_congr (Finset.ext fun y => by simp [hs y]) fun _ _ => rfl
  calc (∑ y ∈ s, algebraMap 𝒪 K
        (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e μ y) * F y)
      = ∑ y ∈ s, ∑ τ, d τ * algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e μ y
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [← hF y ((hs y).mp hy), Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by rw [map_mul]; ring
    _ = ∑ τ, d τ * ((Nat.card G : K) * (if τ = μ then 1 else 0)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun τ _ => by rw [← Finset.mul_sum, hpair τ]
    _ = (Nat.card G : K) * d μ := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq' Finset.univ μ,
          Finset.mem_univ, if_true]
        ring

include hp hπ hlin hkerJ in
/-- **`([μ,φ]⁰)` is the inverse of the Cartan matrix** — Navarro (2.13).  Substitute
`Φ_θ|_{G°} = ∑_μ c_{μθ} μ` into `[Φ_θ, φ]⁰ = δ_{φθ}`. -/
theorem sum_cartanMatrix_mul_pairingZero [Fintype G] (φ θ : ι) :
    ∑ μ, ((cartanMatrix hp hω hω' hπ hlin hkerJ e μ θ : ℕ) : K) *
        pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ)
          (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ)
      = if φ = θ then 1 else 0 := by
  classical
  have hexp : ∀ μ : ι, pairingZero (𝒪 := 𝒪) p K
      (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ)
      (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ)
      = ∑ j : ι, (Nat.card (Subgroup.centralizer
            ({pRegularRep hp hπ hlin hkerJ j} : Set G)) : K)⁻¹ *
          algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ
              (pRegularRep hp hπ hlin hkerJ j)
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ
              (pRegularRep hp hπ hlin hkerJ j)⁻¹) := fun μ =>
    pairingZero_eq_sum_pRegularRep hp hπ hlin hkerJ _ _
      (fun _ _ hc => irreducibleBrauerCharacter_eq_of_isConj μ hc)
      (fun _ _ hc => irreducibleBrauerCharacter_eq_of_isConj φ hc)
  rw [← pairingZero_projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ θ,
    pairingZero_eq_sum_pRegularRep hp hπ hlin hkerJ _ _
      (fun _ _ hc => projectiveIndecomposableCharacter_eq_of_isConj hp hω hω' hπ hlin hkerJ e θ hc)
      (fun _ _ hc => irreducibleBrauerCharacter_eq_of_isConj φ hc),
    Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => by rw [hexp μ, Finset.mul_sum],
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set x := pRegularRep hp hπ hlin hkerJ j with hx
  have hxreg : IsPRegular p x := isPRegular_pRegularRep hp hπ hlin hkerJ j
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) =>
      show ((cartanMatrix hp hω hω' hπ hlin hkerJ e μ θ : ℕ) : K) *
          ((Nat.card (Subgroup.centralizer ({x} : Set G)) : K)⁻¹ *
            algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ x
              * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ x⁻¹))
        = (Nat.card (Subgroup.centralizer ({x} : Set G)) : K)⁻¹ *
          algebraMap 𝒪 K ((cartanMatrix hp hω hω' hπ hlin hkerJ e μ θ : 𝒪) *
            irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ x
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ x⁻¹) from by
        simp only [map_mul, map_natCast]; ring,
    ← Finset.mul_sum, ← map_sum]
  congr 2
  rw [← Finset.sum_mul,
    ← projectiveIndecomposableCharacter_eq_sum_cartanMatrix hp hω hω' hπ hlin hkerJ e θ x hxreg]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
include hp hω hω' hkerJ e in
/-- **The decomposition matrix has no zero column**: every irreducible Brauer character occurs in
some ordinary one.

If the column of `φ` vanished, `Φ_φ = ∑_i d_{iφ} χ_i` would be identically zero, contradicting
`∑_j |C_G(x_j)|⁻¹ φ(x_j⁻¹) Φ_φ(x_j) = 1` (`sum_brauer_mul_projectiveIndecomposableCharacter` at
`φ = θ`). -/
theorem exists_decompositionMatrix_ne_zero (φ : ι) :
    ∃ i : ι', decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ ≠ 0 := by
  classical
  by_contra hex
  have hall : ∀ i : ι', decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ = 0 :=
    fun i => not_not.mp fun hc => hex ⟨i, hc⟩
  have hΦ : ∀ g : G, projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ g = 0 := by
    intro g
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hall i, Nat.cast_zero, zero_mul]
  have h1 := sum_brauer_mul_projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ φ
  rw [if_pos rfl] at h1
  rw [Finset.sum_congr rfl fun j _ => by rw [hΦ, mul_zero, map_zero, mul_zero],
    Finset.sum_const_zero] at h1
  exact zero_ne_one h1

end OddOrder.RepresentationTheory.Modular
