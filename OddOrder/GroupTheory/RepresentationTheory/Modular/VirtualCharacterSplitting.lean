/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.BrauerInductionIdeal
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality

/-!
# `ch(G)` through a Wedderburn splitting: the integrality criterion

`virtualCharacters K G` is defined without reference to any splitting.  Once a Wedderburn
splitting `e : K[G] ≃ₐ[K] ∏_i M_{m_i}(K)` is available, the block characters
`χ_i = (wedderburnRepresentation e i).character` form an orthonormal family
(`OrdinaryOrthogonality`) whose character table is invertible
(`OrdinaryColumnOrthogonality`), and that pins `ch(G)` down completely:

`θ ∈ ch(G) ⟺ θ is a class function and every (θ, χ_i)_G is a rational integer`.

This is the *only* place in the Brauer–Tate development where a splitting is needed.  It is also
what gives `Ind_H^G (ch(H)) ⊆ ch(G)` with no induced module in sight: Frobenius reciprocity turns
`(Ind_H^G ψ, χ_i)_G` into `(ψ, Res_H χ_i)_H`, and that is an integer because both arguments are
virtual characters of `H` (`charPairing_mem_intRange`, which needs no splitting for `H`).

⚠ A splitting is genuinely required for the criterion: over a non-split field `(χ_i, χ_i)_G` is
`dim End(V_i) > 1`, and integrality of all the pairings would only place `θ` in a *larger* lattice
than `ℤ[Irr(G)]`.

## Main results

* `OddOrder.RepresentationTheory.Modular.charPairing_wedderburnRepresentation` — orthonormality
* `OddOrder.RepresentationTheory.Modular.exists_eq_sum_wedderburnRepresentation` — the block
  characters span the class functions
* `OddOrder.RepresentationTheory.Modular.mem_virtualCharacters_iff` — the criterion
* `OddOrder.RepresentationTheory.Modular.induceFun_mem_virtualCharacters` —
  `Ind_H^G (ch(H)) ⊆ ch(G)`

## References

* D. Gorenstein, *Finite Groups*, §4.7 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.RepresentationTheory

variable {K G : Type*} [Field K] [Group G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  [Finite G] [Invertible (Nat.card G : K)]

omit [∀ i, Nonempty (m i)] [Finite G] [Invertible (Nat.card G : K)] in
/-- The block characters are genuine characters. -/
theorem isRepCharacter_wedderburnRepresentation (i : ι') :
    IsRepCharacter K (wedderburnRepresentation e i).character :=
  isRepCharacter_of_finite _

omit [∀ i, Nonempty (m i)] [Finite G] [Invertible (Nat.card G : K)] in
theorem mem_virtualCharacters_wedderburnRepresentation (i : ι') :
    (wedderburnRepresentation e i).character ∈ virtualCharacters K G :=
  (isRepCharacter_wedderburnRepresentation e i).mem_virtualCharacters

omit [Finite G] in
/-- **Orthonormality of the block characters** for the bilinear pairing — first orthogonality
read through `charPairing`. -/
theorem charPairing_wedderburnRepresentation [Fintype G] [DecidableEq ι'] (i i' : ι') :
    charPairing K (wedderburnRepresentation e i).character
        (wedderburnRepresentation e i').character = if i = i' then 1 else 0 := by
  have hGne : (Nat.card G : K) ≠ 0 := (isUnit_of_invertible (Nat.card G : K)).ne_zero
  rw [charPairing, Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) =>
      mul_comm ((wedderburnRepresentation e i).character g⁻¹) _,
    sum_character_mul_character_inv e i i']
  split
  · rw [inv_mul_cancel₀ hGne]
  · rw [mul_zero]

/-- **The block characters span the class functions.**  Solve the linear system on class
representatives using the inverse of the character table, then transport to arbitrary elements by
conjugation. -/
theorem exists_eq_sum_wedderburnRepresentation [Fintype ι'] {θ : G → K}
    (hθ : ∀ g h : G, θ (h * g * h⁻¹) = θ g) :
    ∃ a : ι' → K, ∀ g : G, θ g = ∑ i : ι', a i * (wedderburnRepresentation e i).character g := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  refine ⟨fun i => ∑ j : ι', θ (classRep e j) * characterMatrixInv e j i, fun g => ?_⟩
  -- reduce to a class representative
  set j₀ := (equivConjClasses e).symm (ConjClasses.mk g) with hj₀
  have hgc : IsConj g (classRep e j₀) := by
    refine ConjClasses.mk_eq_mk_iff_isConj.mp ?_
    rw [classRep, conjugacyClassRepresentative_mk_eq, hj₀, Equiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := hgc
  have hg : (u : G) * g * ((u : G))⁻¹ = classRep e j₀ := by rw [hu.eq]; group
  rw [show θ g = θ (classRep e j₀) from by rw [← hg, hθ],
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [show (wedderburnRepresentation e i).character g
        = (wedderburnRepresentation e i).character (classRep e j₀) from
        character_eq_of_isConj _ ⟨u, hu⟩]]
  -- now it is `(θ|_reps · W) · X = θ|_reps`, i.e. `W · X = 1`
  have hmul := characterMatrixInv_mul_characterMatrix e
  refine Eq.symm ?_
  change (∑ i : ι', (∑ j : ι', θ (classRep e j) * characterMatrixInv e j i)
      * (wedderburnRepresentation e i).character (classRep e j₀)) = θ (classRep e j₀)
  calc ∑ i : ι', (∑ j : ι', θ (classRep e j) * characterMatrixInv e j i)
        * (wedderburnRepresentation e i).character (classRep e j₀)
      = ∑ i : ι', ∑ j : ι', θ (classRep e j) * (characterMatrixInv e j i
          * (wedderburnRepresentation e i).character (classRep e j₀)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j : ι', ∑ i : ι', θ (classRep e j) * (characterMatrixInv e j i
          * (wedderburnRepresentation e i).character (classRep e j₀)) := Finset.sum_comm
    _ = ∑ j : ι', θ (classRep e j)
          * ∑ i : ι', characterMatrixInv e j i * characterMatrix e i j₀ :=
        Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    _ = θ (classRep e j₀) := by
        refine (Finset.sum_eq_single j₀ (fun j _ hj => ?_)
          (fun h => absurd (Finset.mem_univ _) h)).trans ?_
        · rw [show (∑ i : ι', characterMatrixInv e j i * characterMatrix e i j₀)
            = (characterMatrixInv e * characterMatrix e) j j₀ from (Matrix.mul_apply).symm, hmul,
            Matrix.one_apply_ne hj, mul_zero]
        · rw [show (∑ i : ι', characterMatrixInv e j₀ i * characterMatrix e i j₀)
            = (characterMatrixInv e * characterMatrix e) j₀ j₀ from (Matrix.mul_apply).symm, hmul,
            Matrix.one_apply_eq, mul_one]

omit [Finite G] in
/-- **The integrality criterion for `ch(G)`.**  A class function is a virtual character exactly
when all of its pairings against the block characters are rational integers. -/
theorem mem_virtualCharacters_iff [Fintype G] [Finite ι'] {θ : G → K} :
    θ ∈ virtualCharacters K G ↔ (∀ g h : G, θ (h * g * h⁻¹) = θ g) ∧
      ∀ i : ι', charPairing K θ (wedderburnRepresentation e i).character
        ∈ (Int.castRingHom K).range := by
  classical
  letI : Fintype ι' := Fintype.ofFinite ι'
  constructor
  · intro hθ
    exact ⟨fun g h => virtualCharacters_conj hθ g h, fun i =>
      charPairing_mem_intRange hθ (mem_virtualCharacters_wedderburnRepresentation e i)⟩
  · rintro ⟨hclass, hint⟩
    obtain ⟨a, ha⟩ := exists_eq_sum_wedderburnRepresentation e hclass
    -- the coefficients are the pairings, hence integers
    have hcoeff : ∀ i' : ι', a i'
        = charPairing K θ (wedderburnRepresentation e i').character := by
      intro i'
      rw [funext ha, charPairing]
      have hexp : ∀ g : G, (∑ i : ι', a i * (wedderburnRepresentation e i).character g⁻¹)
          * (wedderburnRepresentation e i').character g
          = ∑ i : ι', a i * ((wedderburnRepresentation e i).character g⁻¹
            * (wedderburnRepresentation e i').character g) := fun g => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hexp g, Finset.sum_comm,
        Finset.mul_sum]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        show (Nat.card G : K)⁻¹ * ∑ g : G, a i * ((wedderburnRepresentation e i).character g⁻¹
              * (wedderburnRepresentation e i').character g)
            = a i * charPairing K (wedderburnRepresentation e i).character
              (wedderburnRepresentation e i').character from by
          rw [charPairing, ← Finset.mul_sum]; ring,
        Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
          rw [charPairing_wedderburnRepresentation e i i']]
      simp
    -- so `θ` is a `ℤ`-combination of the block characters
    have hsplit : θ = ∑ i : ι', (fun g => a i * (wedderburnRepresentation e i).character g) := by
      funext g
      rw [ha g]
      simp
    rw [hsplit]
    refine sum_mem fun i _ => ?_
    obtain ⟨n, hn⟩ := hint i
    rw [hcoeff i, ← hn]
    have hz : (fun g => (Int.castRingHom K) n * (wedderburnRepresentation e i).character g)
        = n • (wedderburnRepresentation e i).character := by
      funext g
      simp [zsmul_eq_mul]
    rw [hz]
    exact zsmul_mem (mem_virtualCharacters_wedderburnRepresentation e i) n

omit [Finite G] in
include e in
/-- **`Ind_H^G` maps virtual characters to virtual characters.**  Frobenius reciprocity turns the
pairings on `G` into pairings on `H`, where integrality is splitting-free. -/
theorem induceFun_mem_virtualCharacters [Fintype G] [Finite ι'] {H : Subgroup G} {ψ : ↥H → K}
    (hψ : ψ ∈ virtualCharacters K ↥H) : induceFun H ψ ∈ virtualCharacters K G := by
  classical
  letI : Fintype ↥H := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥H : K) :=
    invertibleOfNonzero (natCast_card_subgroup_ne_zero H)
  refine (mem_virtualCharacters_iff e).mpr ⟨fun g h => induceFun_conj ψ g h, fun i => ?_⟩
  rw [charPairing_induceFun ψ (fun g h =>
    virtualCharacters_conj (mem_virtualCharacters_wedderburnRepresentation e i) g h)]
  exact charPairing_mem_intRange hψ
    (comp_mem_virtualCharacters H.subtype (mem_virtualCharacters_wedderburnRepresentation e i))

end OddOrder.RepresentationTheory.Modular
