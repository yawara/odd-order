/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.Peterfalvi.S07_Coherence

/-!
# Peterfalvi (5.9)(a): Galois automorphisms commute with coherent isometries

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §5, p. 29.

**(5.9)(a)**: assume Hypothesis (2.2) (the §4 Dade situation `S04.Hypothesis G A L`).  Let
`𝒮 ⊆ Irr L` with `ℤ[𝒮, L^#] = ℤ[𝒮, A]` and `|𝒮| ≥ 2`, let `u` be a field automorphism with
`𝒮^u ⊆ 𝒮`, and let `τ₁` be a linear isometry `ℤ[𝒮] → ℤ[Irr G]` agreeing with the Dade map
`τ` on `ℤ[𝒮, A]`.  Then `χ^{τ₁u} = χ^{uτ₁}` for `χ ∈ 𝒮`.

We take `u = σc : ℂ ≃+* ℂ` (the cyclotomic automorphisms of `CyclotomicGaloisAction`
restrict to the book's automorphisms of `ℚ_{|G|}`) and `τ₁ = hτ.extension` for a coherence
witness `hτ : IsCoherent (dadeIntegralCharacterMap hyp dade) S A'`; the lattice condition
`τ₁(𝒮) ⊆ ℤ[Irr G]` is a separate hypothesis `hlat` (`IsCoherent` does not record it), and
the book's span condition `ℤ[𝒮, L^#] = ℤ[𝒮, A]` is taken in the unfolded form `hspan`
("members of `ℤ[𝒮]` vanishing at `1` are supported on `A'`").

The two Dade-specific inputs are isolated:
* `dadeIntegralCharacterMap_mapRingEquiv_comm` — the explicit Dade map (2.5) is pointwise
  evaluation `α ↦ α(a)` at `A`-base points, so it commutes with coefficientwise
  automorphisms (the book's "by the definition of `τ`");
* `dadeIntegralCharacterMap_apply_one` — Dade images vanish at `1`
  (`one_notMem_dadeSupport`), which forces the uniform sign `ε` with `ε·φ^{τ₁} ∈ Irr G`.

Note that (5.9.a) does **not** transport inner products along `u`, so no star-commutation
hypothesis on `σc` is needed — this is what makes it applicable to the wild automorphisms
of `ℂ` produced by `CyclotomicGaloisAction` (which never commute with conjugation
globally).  Used by (6.8.2.1) together with (1.9.b).
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S04

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G} [Fintype G] [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **The explicit Dade map commutes with coefficientwise ring automorphisms** on the
supported subspace: its value at `g ∈ dadeSupport` is the evaluation `α(a)` at an `A`-base
point, and `0` elsewhere, so applying `σc` to coefficients commutes with it. -/
theorem dadeIntegralCharacterMap_mapRingEquiv_comm
    (hyp : S04.Hypothesis G A L) (dade : S04.FullDadeIsometryData (G := G) hyp)
    (σc : ℂ ≃+* ℂ) {φ : ClassFunction (↥L) ℂ}
    (hφ : φ.support ⊆ supportInSubgroup A L) :
    dadeIntegralCharacterMap hyp dade (ClassFunction.mapRingEquiv σc φ) =
      ClassFunction.mapRingEquiv σc (dadeIntegralCharacterMap hyp dade φ) := by
  have hφ' : (ClassFunction.mapRingEquiv σc φ).support ⊆ supportInSubgroup A L := by
    rwa [ClassFunction.support_mapRingEquiv]
  rw [dadeIntegralCharacterMap_apply_of_support hyp dade hφ',
    dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
  ext g
  simp only [ClassFunction.mapRingEquiv_apply, Hypothesis.dadeMap_apply]
  by_cases hg : g ∈ hyp.dadeSupport
  · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
    rw [hyp.dadeValue_eq _ hh hga, hyp.dadeValue_eq _ hh hga]
    rfl
  · rw [hyp.dadeValue_of_not_mem_dadeSupport _ hg, hyp.dadeValue_of_not_mem_dadeSupport _ hg,
      map_zero]

/-- **Dade images vanish at the identity**: `1 ∉ dadeSupport`. -/
theorem dadeIntegralCharacterMap_apply_one
    (hyp : S04.Hypothesis G A L) (dade : S04.FullDadeIsometryData (G := G) hyp)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ.support ⊆ supportInSubgroup A L) :
    dadeIntegralCharacterMap hyp dade φ 1 = 0 := by
  rw [dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
  simp only [Hypothesis.dadeMap_apply]
  exact hyp.dadeValue_of_not_mem_dadeSupport _ hyp.one_notMem_dadeSupport

/-- **Peterfalvi (5.9)(a).**  In the Dade situation, let `S ⊆ Irr L` with `|S| ≥ 2`, closed
under the coefficientwise automorphism `σc`, such that members of `ℤ[S]` vanishing at `1`
are supported on `A'` (the condition `ℤ[S, L^#] = ℤ[S, A]`).  If `τ₁ = hτ.extension` is a
coherent isometric extension of the Dade map `τ` mapping `S` into `ℤ[Irr G]`, then `τ₁`
commutes with `σc` on `S`:

`(τ₁ χ)^{σc} = τ₁ (χ^{σc})` for all `χ ∈ S`.

Proof: `ψ(1)·χ − χ(1)·ψ` vanishes at `1`, hence is supported and `τ₁ = τ` there; `τ`
commutes with `σc` by its pointwise definition, giving
`ψ(1)·(τ₁χ)^{σc} − χ(1)·(τ₁ψ)^{σc} = ψ(1)·τ₁(χ^{σc}) − χ(1)·τ₁(ψ^{σc})`.  Each `τ₁φ`
(`φ ∈ S`) is `ε·ξ_φ` with `ξ_φ ∈ Irr G` and a sign `ε` *independent of `φ`* (norm `1`
forces `±`; vanishing of Dade images at `1` forces a uniform sign).  Comparing coefficients
of the irreducible `(ξ_χ)^{σc}` in the displayed equation forces
`(ξ_χ)^{σc} = ξ_{χ^{σc}}`. -/
theorem IsCoherent.extension_mapRingEquiv_comm
    {hyp : S04.Hypothesis G A L} {dade : S04.FullDadeIsometryData (G := G) hyp}
    {S : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L}
    (hτ : IsCoherent (dadeIntegralCharacterMap hyp dade) S A')
    (hA' : A' ⊆ supportInSubgroup A L)
    (hSirr : S ⊆ irreducibleCharacters ↥L)
    (hspan : ∀ φ ∈ zSpan (L := ↥L) S, φ 1 = 0 → φ.support ⊆ A')
    (σc : ℂ ≃+* ℂ) (hSu : ∀ φ ∈ S, ClassFunction.mapRingEquiv σc φ ∈ S)
    (hlat : ∀ φ ∈ S, hτ.extension φ ∈ ZIrr G)
    {χ : ClassFunction (↥L) ℂ} (hχ : χ ∈ S)
    (h2 : ∃ ψ ∈ S, ψ ≠ χ) :
    ClassFunction.mapRingEquiv σc (hτ.extension χ) =
      hτ.extension (ClassFunction.mapRingEquiv σc χ) := by
  classical
  obtain ⟨ψ, hψ, hψχ⟩ := h2
  set τ₁ := hτ.extension with hτ₁def
  -- (i) `τ₁` commutes with `σc` on the vanishing-at-1 part of `ℤ[S]`
  have hcomm : ∀ ζ, ζ ∈ zSpan (L := ↥L) S → ζ 1 = 0 →
      ClassFunction.mapRingEquiv σc (τ₁ ζ) = τ₁ (ClassFunction.mapRingEquiv σc ζ) := by
    intro ζ hζ hζ1
    have hζsupp : ζ.support ⊆ A' := hspan ζ hζ hζ1
    have hζu : ClassFunction.mapRingEquiv σc ζ ∈ zSupportedSpan (L := ↥L) S A' := by
      refine ⟨?_, ?_⟩
      · exact Submodule.span_mono (Set.image_subset_iff.mpr hSu)
          (ClassFunction.mapRingEquiv_mem_zSpan_image σc hζ)
      · rw [ClassFunction.support_mapRingEquiv]
        exact hζsupp
    calc ClassFunction.mapRingEquiv σc (τ₁ ζ)
        = ClassFunction.mapRingEquiv σc (dadeIntegralCharacterMap hyp dade ζ) := by
          rw [hτ.extends_on_supported ζ ⟨hζ, hζsupp⟩]
      _ = dadeIntegralCharacterMap hyp dade (ClassFunction.mapRingEquiv σc ζ) :=
          (dadeIntegralCharacterMap_mapRingEquiv_comm hyp dade σc
            (hζsupp.trans hA')).symm
      _ = τ₁ (ClassFunction.mapRingEquiv σc ζ) := (hτ.extends_on_supported _ hζu).symm
  -- (ii) degrees of the members of `S`
  have hdeg : ∀ φ, φ ∈ S → ∃ d : ℕ, 0 < d ∧ φ 1 = (d : ℂ) := by
    intro φ hφ
    obtain ⟨e, he, h1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨φ, hSirr hφ⟩ : IrreducibleCharacter ↥L)
    exact ⟨e, he, h1⟩
  choose d hdpos hd1 using hdeg
  -- (iii) `τ₁ φ = ε_φ • ξ_φ` with `ε_φ = ±1`, `ξ_φ ∈ Irr G`
  have hpm : ∀ φ (hφ : φ ∈ S), ∃ (e : ℤ) (ξ : IrreducibleCharacter G),
      (e = 1 ∨ e = -1) ∧ τ₁ φ = e • (ξ : ClassFunction G ℂ) := by
    intro φ hφ
    have hnorm : ClassFunction.inner (τ₁ φ) (τ₁ φ) = 1 := by
      rw [hτ.extension_inner_eq φ φ (Submodule.subset_span hφ) (Submodule.subset_span hφ)]
      have h := irreducibleCharacter_inner_eq_ite
        (⟨φ, hSirr hφ⟩ : IrreducibleCharacter ↥L) (⟨φ, hSirr hφ⟩ : IrreducibleCharacter ↥L)
      rw [if_pos rfl] at h
      exact h
    exact exists_zsmul_irreducibleCharacter_of_inner_self_one (hlat φ hφ) hnorm
  choose ε ξ hεpm hξrepr using hpm
  -- (iv) the signs agree pairwise (vanishing at 1 of Dade images)
  have hsign : ∀ φ₁ (h₁ : φ₁ ∈ S) φ₂ (h₂ : φ₂ ∈ S), ε φ₁ h₁ = ε φ₂ h₂ := by
    intro φ₁ h₁ φ₂ h₂
    set ζ : ClassFunction (↥L) ℂ := (d φ₂ h₂ : ℤ) • φ₁ - (d φ₁ h₁ : ℤ) • φ₂ with hζdef
    have hζspan : ζ ∈ zSpan (L := ↥L) S :=
      sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span h₁))
        (Submodule.smul_mem _ _ (Submodule.subset_span h₂))
    have hζ1 : ζ 1 = 0 := by
      rw [hζdef]
      simp only [ClassFunction.sub_apply, ClassFunction.zsmul_apply,
        hd1 φ₁ h₁, hd1 φ₂ h₂, zsmul_eq_mul]
      push_cast
      ring
    have hτζ1 : τ₁ ζ 1 = 0 := by
      rw [hτ.extends_on_supported ζ ⟨hζspan, hspan ζ hζspan hζ1⟩]
      exact dadeIntegralCharacterMap_apply_one hyp dade ((hspan ζ hζspan hζ1).trans hA')
    have hτζ : τ₁ ζ = (d φ₂ h₂ : ℤ) • τ₁ φ₁ - (d φ₁ h₁ : ℤ) • τ₁ φ₂ := by
      rw [hζdef, map_sub, map_smul, map_smul]
    obtain ⟨e₁, he₁, hξ₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (ξ φ₁ h₁)
    obtain ⟨e₂, he₂, hξ₂⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (ξ φ₂ h₂)
    have hkey : (d φ₂ h₂ : ℂ) * ((ε φ₁ h₁ : ℂ) * (e₁ : ℂ)) =
        (d φ₁ h₁ : ℂ) * ((ε φ₂ h₂ : ℂ) * (e₂ : ℂ)) := by
      have h0 := hτζ1
      rw [hτζ, hξrepr φ₁ h₁, hξrepr φ₂ h₂] at h0
      simp only [ClassFunction.sub_apply, ClassFunction.zsmul_apply, hξ₁, hξ₂,
        zsmul_eq_mul] at h0
      push_cast at h0
      linear_combination h0
    rcases hεpm φ₁ h₁ with hε₁ | hε₁ <;> rcases hεpm φ₂ h₂ with hε₂ | hε₂
    case inl.inl => rw [hε₁, hε₂]
    case inl.inr =>
      exfalso
      rw [hε₁, hε₂] at hkey
      push_cast at hkey
      have hsum : ((d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination hkey
      have h0 : d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ = 0 := Nat.cast_eq_zero.mp hsum
      have hp1 : 0 < d φ₂ h₂ * e₁ := Nat.mul_pos (hdpos φ₂ h₂) he₁
      omega
    case inr.inl =>
      exfalso
      rw [hε₁, hε₂] at hkey
      push_cast at hkey
      have hsum : ((d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination -hkey
      have h0 : d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ = 0 := Nat.cast_eq_zero.mp hsum
      have hp1 : 0 < d φ₂ h₂ * e₁ := Nat.mul_pos (hdpos φ₂ h₂) he₁
      omega
    case inr.inr => rw [hε₁, hε₂]
  -- abbreviations: the four irreducible constituents
  have hχu : ClassFunction.mapRingEquiv σc χ ∈ S := hSu χ hχ
  have hψu : ClassFunction.mapRingEquiv σc ψ ∈ S := hSu ψ hψ
  -- decomposed forms of the four images, all with the sign `ε χ hχ`
  have huτχ : ClassFunction.mapRingEquiv σc (τ₁ χ) =
      ε χ hχ • (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ) := by
    rw [hξrepr χ hχ, ClassFunction.mapRingEquiv_zsmul]
    rfl
  have huτψ : ClassFunction.mapRingEquiv σc (τ₁ ψ) =
      ε χ hχ • (IrreducibleCharacter.galoisMap σc (ξ ψ hψ) : ClassFunction G ℂ) := by
    rw [hξrepr ψ hψ, ClassFunction.mapRingEquiv_zsmul, hsign ψ hψ χ hχ]
    rfl
  have hτuχ : τ₁ (ClassFunction.mapRingEquiv σc χ) =
      ε χ hχ • (ξ _ hχu : ClassFunction G ℂ) := by
    rw [hξrepr _ hχu, hsign _ hχu χ hχ]
  have hτuψ : τ₁ (ClassFunction.mapRingEquiv σc ψ) =
      ε χ hχ • (ξ _ hψu : ClassFunction G ℂ) := by
    rw [hξrepr _ hψu, hsign _ hψu χ hχ]
  -- (v) the main equation, with the sign `ε χ hχ` cancelled
  have hE2 : ε χ hχ * ε χ hχ = 1 := by
    rcases hεpm χ hχ with h1 | h1 <;> rw [h1] <;> norm_num
  have hmain : (d ψ hψ : ℤ) • (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ)
        - (d χ hχ : ℤ) • (IrreducibleCharacter.galoisMap σc (ξ ψ hψ) : ClassFunction G ℂ)
      = (d ψ hψ : ℤ) • (ξ _ hχu : ClassFunction G ℂ)
        - (d χ hχ : ℤ) • (ξ _ hψu : ClassFunction G ℂ) := by
    set ζ₀ : ClassFunction (↥L) ℂ := (d ψ hψ : ℤ) • χ - (d χ hχ : ℤ) • ψ with hζ₀def
    have hζ₀span : ζ₀ ∈ zSpan (L := ↥L) S :=
      sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span hχ))
        (Submodule.smul_mem _ _ (Submodule.subset_span hψ))
    have hζ₀1 : ζ₀ 1 = 0 := by
      rw [hζ₀def]
      simp only [ClassFunction.sub_apply, ClassFunction.zsmul_apply,
        hd1 χ hχ, hd1 ψ hψ, zsmul_eq_mul]
      push_cast
      ring
    have h := hcomm ζ₀ hζ₀span hζ₀1
    have hL : ClassFunction.mapRingEquiv σc (τ₁ ζ₀) =
        ε χ hχ • ((d ψ hψ : ℤ) •
            (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ)
          - (d χ hχ : ℤ) •
            (IrreducibleCharacter.galoisMap σc (ξ ψ hψ) : ClassFunction G ℂ)) := by
      rw [hζ₀def, map_sub, map_smul, map_smul, ClassFunction.mapRingEquiv_sub,
        ClassFunction.mapRingEquiv_zsmul, ClassFunction.mapRingEquiv_zsmul, huτχ, huτψ,
        smul_sub, smul_comm (ε χ hχ) ((d ψ hψ : ℤ)), smul_comm (ε χ hχ) ((d χ hχ : ℤ))]
    have hR : τ₁ (ClassFunction.mapRingEquiv σc ζ₀) =
        ε χ hχ • ((d ψ hψ : ℤ) • (ξ _ hχu : ClassFunction G ℂ)
          - (d χ hχ : ℤ) • (ξ _ hψu : ClassFunction G ℂ)) := by
      rw [hζ₀def, ClassFunction.mapRingEquiv_sub, ClassFunction.mapRingEquiv_zsmul,
        ClassFunction.mapRingEquiv_zsmul, map_sub, map_smul, map_smul, hτuχ, hτuψ,
        smul_sub, smul_comm (ε χ hχ) ((d ψ hψ : ℤ)), smul_comm (ε χ hχ) ((d χ hχ : ℤ))]
    rw [hL, hR] at h
    have h' := congrArg (fun x => ε χ hχ • x) h
    simpa only [smul_smul, hE2, one_smul] using h'
  -- (vi) the second constituent differs from the first
  have hτne : τ₁ ψ ≠ τ₁ χ := by
    intro heq
    have hiso := hτ.extension_inner_eq (ψ - χ) (ψ - χ)
      (sub_mem (Submodule.subset_span hψ) (Submodule.subset_span hχ))
      (sub_mem (Submodule.subset_span hψ) (Submodule.subset_span hχ))
    rw [map_sub, heq, sub_self] at hiso
    have hzero : ClassFunction.inner (0 : ClassFunction G ℂ) (0 : ClassFunction G ℂ) = 0 := by
      rw [show (0 : ClassFunction G ℂ) = (0 : ℂ) • (0 : ClassFunction G ℂ) from
        (zero_smul ℂ _).symm, ClassFunction.inner_smul_left, zero_mul]
    rw [hzero] at hiso
    have hψχ' : (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hSirr hχ⟩ := by
      intro h
      exact hψχ (congrArg (fun ξ' : IrreducibleCharacter ↥L => (ξ' : ClassFunction ↥L ℂ)) h)
    have h11 := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L) (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L)
    have h22 := irreducibleCharacter_inner_eq_ite
      (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L) (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L)
    have h12 := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L) (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L)
    have h21 := irreducibleCharacter_inner_eq_ite
      (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L) (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L)
    rw [if_pos rfl] at h11 h22
    rw [if_neg hψχ'] at h12
    rw [if_neg (Ne.symm hψχ')] at h21
    have htwo : ClassFunction.inner (ψ - χ) (ψ - χ) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h11, h22, h12, h21]
      ring
    rw [htwo] at hiso
    exact two_ne_zero hiso.symm
  have hB21 : IrreducibleCharacter.galoisMap σc (ξ ψ hψ) ≠
      IrreducibleCharacter.galoisMap σc (ξ χ hχ) := by
    intro h
    have hξne : ξ ψ hψ = ξ χ hχ := by
      have hinj : Function.Injective (IrreducibleCharacter.galoisMap (G := G) σc) := by
        intro x y hxy
        have := congrArg (IrreducibleCharacter.galoisMap σc.symm) hxy
        simpa using this
      exact hinj h
    refine hτne ?_
    rw [hξrepr ψ hψ, hξrepr χ hχ, hsign ψ hψ χ hχ, hξne]
  -- (vii) compare the coefficient of `(ξ_χ)^{σc}` in the main equation
  have hexp : ∀ (n m : ℕ) (X Y : IrreducibleCharacter G),
      ClassFunction.inner
          ((n : ℤ) • (X : ClassFunction G ℂ) - (m : ℤ) • (Y : ClassFunction G ℂ))
          (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ) =
        (n : ℂ) * (if X = IrreducibleCharacter.galoisMap σc (ξ χ hχ) then 1 else 0)
          - (m : ℂ) * (if Y = IrreducibleCharacter.galoisMap σc (ξ χ hχ) then 1 else 0) := by
    intro n m X Y
    rw [ClassFunction.inner_sub_left, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      irreducibleCharacter_inner_eq_ite X (IrreducibleCharacter.galoisMap σc (ξ χ hχ)),
      irreducibleCharacter_inner_eq_ite Y (IrreducibleCharacter.galoisMap σc (ξ χ hχ))]
    push_cast
    ring
  have hcmp := congrArg
    (fun x : ClassFunction G ℂ =>
      ClassFunction.inner x (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ))
    hmain
  simp only [hexp (d ψ hψ) (d χ hχ)] at hcmp
  rw [if_neg hB21] at hcmp
  simp only [if_true] at hcmp
  -- conclude: the goal reduces to `ξ_{χ^{σc}} = (ξ_χ)^{σc}`
  by_cases h31 : ξ _ hχu = IrreducibleCharacter.galoisMap σc (ξ χ hχ)
  · rw [huτχ, hτuχ, h31]
  · exfalso
    rw [if_neg h31] at hcmp
    by_cases h41 : ξ _ hψu = IrreducibleCharacter.galoisMap σc (ξ χ hχ)
    · rw [if_pos h41] at hcmp
      have hsum : ((d ψ hψ + d χ hχ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination hcmp
      have h0 : d ψ hψ + d χ hχ = 0 := Nat.cast_eq_zero.mp hsum
      have := hdpos ψ hψ
      omega
    · rw [if_neg h41] at hcmp
      have hsum : ((d ψ hψ : ℕ) : ℂ) = 0 := by
        linear_combination hcmp
      have h0 : d ψ hψ = 0 := Nat.cast_eq_zero.mp hsum
      have := hdpos ψ hψ
      omega

end OddOrder.Peterfalvi.S07
