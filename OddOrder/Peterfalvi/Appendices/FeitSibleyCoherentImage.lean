/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyTheorem
import OddOrder.Peterfalvi.Appendices.FeitSibleySsetCoherence
import OddOrder.Peterfalvi.Appendices.FeitSibleyInduction
import OddOrder.Peterfalvi.Appendices.FeitSibleyQ1Component
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

/-!
# Peterfalvi Appendix IV: member images under the coherent extension

Peterfalvi Part II, Ch. III, Theorem C, step (9) (p. 116) reads:

> Let `𝒮 = {χ₁,…,χₙ}`, with `χᵢ(1) = aᵢ|D|` and `a₁ = 1`, and let
> `eᵢ ∈ ±Irr(G)` be such that `Ind_H^G(χᵢ − aᵢχ₁) = eᵢ − aᵢe₁` for `i ≥ 2`;
> the coherence of `𝒮` makes this possible.

This leaf provides the three ingredients in coherence-extension form
(`eᵢ := hcoh.extension χᵢ` for a coherence witness
`hcoh : IsCoherent hyp.tau hyp.Sset hyp.A` of the Feit–Sibley Theorem):

* `exists_anchor` — an anchor `χ₁ ∈ 𝒮` of degree exactly `d`, every `χ ∈ 𝒮`
  having degree `a·χ₁(1)` with `a ∈ ℕ`, `a ≥ 1` (the book's `χᵢ(1) = aᵢ|D|`,
  `a₁ = 1`);
* `extension_zsmul_irr` — `hcoh.extension χ ∈ ±Irr(G)` (the book's
  `eᵢ ∈ ±Irr(G)`): the extension is a norm-preserving map into `ℤ[Irr G]`;
* `induce_sub_nsmul_extension` — the displayed identity
  `Ind_H^G(χ − a·χ') = e_χ − a·e_{χ'}`: the difference is `A`-supported, where
  the extension agrees with `τ = Ind_H^G`.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-- **The anchor `χ₁` of Theorem C, step (9)** (p. 116, "`χᵢ(1) = aᵢ|D|` and
`a₁ = 1`"): a member `χ₁ ∈ 𝒮` of degree exactly `d`, such that every member's
degree is a positive natural multiple of `χ₁(1)`.

`𝒮(Q′) ≠ ∅` (`ssetOf_Qder_nonempty`, from `S·Q′ < Q`), its members have degree
exactly `d` (`apply_one_eq_d_of_mem_SsetOf_Qder`), and every member of `𝒮` has
degree `d·m` (`exists_apply_one_eq_d_mul`). -/
theorem exists_anchor [Finite G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.H : ℂ)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hnil : Group.IsNilpotent ↥hyp.Q1) :
    ∃ χ₁ ∈ hyp.Sset, χ₁ (1 : ↥hyp.H) = (hyp.d : ℂ) ∧
      ∀ χ ∈ hyp.Sset, ∃ a : ℕ, 0 < a ∧
        χ (1 : ↥hyp.H) = (a : ℂ) * χ₁ (1 : ↥hyp.H) := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.ssetOf_Qder_nonempty (hyp.sup_S_Qder_lt_Q hnil)
  have hd : χ₁ (1 : ↥hyp.H) = (hyp.d : ℂ) :=
    hyp.apply_one_eq_d_of_mem_SsetOf_Qder hχ₁
  refine ⟨χ₁, hyp.SsetOf_subset hyp.Qder hχ₁, hd, fun χ hχ => ?_⟩
  obtain ⟨m, hm, hval⟩ := hyp.exists_apply_one_eq_d_mul hχ
  exact ⟨m, hm, by rw [hval, hd]; ring⟩

section CoherentImage

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
  [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]

/-- **`e_χ ∈ ±Irr(G)`** (Theorem C, step (9), p. 116: "let `eᵢ ∈ ±Irr(G)`"):
the coherent extension sends each member of `𝒮` to a signed irreducible
character of `G`.

The extension preserves inner products on `ℤ[𝒮]` and lands in `ℤ[Irr G]`, so
`‖e_χ‖² = ‖χ‖² = 1` and `e_χ = ε·ξ` with `ε = ±1`, `ξ ∈ Irr(G)`
(`exists_zsmul_irreducibleCharacter_of_inner_self_one`). -/
theorem extension_zsmul_irr
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
      hcoh.extension χ = ε • (ξ : ClassFunction G ℂ) := by
  have hmem : χ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset :=
    Submodule.subset_span hχ
  have hnorm : ClassFunction.inner (hcoh.extension χ) (hcoh.extension χ) = 1 := by
    rw [hcoh.extension_inner_eq χ χ hmem hmem]
    exact hχ.1.inner_self_eq_one
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one
    (hcoh.extension_mem_ZIrr χ hmem) hnorm

/-- **The coherent extension is an isometry on members**: for `χ, χ' ∈ 𝒮`,
`⟨e_χ, e_{χ'}⟩ = ⟨χ, χ'⟩`. -/
theorem extension_inner_member
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ χ' : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset) :
    ClassFunction.inner (hcoh.extension χ) (hcoh.extension χ')
      = ClassFunction.inner χ χ' :=
  hcoh.extension_inner_eq χ χ' (Submodule.subset_span hχ) (Submodule.subset_span hχ')

/-- **Theorem C, step (9), displayed identity** (p. 116):
`Ind_H^G(χ − a·χ') = e_χ − a·e_{χ'}` whenever `χ, χ' ∈ 𝒮` and
`χ(1) = a·χ'(1)`.

The degree-matched difference `χ − a·χ'` is supported on `A = Q^#`
(`scaled_diff_support_subset_A_of_mem_Sset`), where the coherent extension
agrees with `τ = Ind_H^G` (`extends_on_supported`); `ℤ`-linearity of the
extension splits the image. -/
theorem induce_sub_nsmul_extension [Finite G]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ χ' : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset)
    {a : ℕ} (hdeg : χ (1 : ↥hyp.H) = (a : ℂ) * χ' (1 : ↥hyp.H)) :
    ClassFunction.induce hyp.H (χ - a • χ')
      = hcoh.extension χ - a • hcoh.extension χ' := by
  have hspan : χ - a • χ' ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset :=
    Submodule.sub_mem _ (Submodule.subset_span hχ)
      (nsmul_mem (Submodule.subset_span hχ') a)
  have hsupp : (χ - a • χ' : ClassFunction ↥hyp.H ℂ).support ⊆ hyp.A := by
    have h := hyp.scaled_diff_support_subset_A_of_mem_Sset hχ hχ' (n := 1) (m := a)
      (by rw [Nat.cast_one, one_mul]; exact hdeg)
    simpa using h
  have h1 : hcoh.extension (χ - a • χ') = hyp.tau (χ - a • χ') :=
    hcoh.extends_on_supported _ ⟨hspan, hsupp⟩
  have h2 : hcoh.extension (χ - a • χ')
      = hcoh.extension χ - a • hcoh.extension χ' := by
    rw [map_sub, map_nsmul]
  rw [← h2, h1, tau_apply]

end CoherentImage

/-- **Elements of `H` of order dividing `|Q|` lie in `Q`** — the normal-Hall
property behind the book's "since `Q` is a Hall subgroup of `H`" (Theorem C,
step (10), p. 116).  The image of `x` in `H/Q` has order dividing both `|Q|`
and `[H : Q] = d`, which are coprime. -/
theorem mem_Q_of_orderOf_dvd_card_Q [Finite G] {x : G} (hx : x ∈ hyp.H)
    (hord : orderOf x ∣ Nat.card ↥hyp.Q) : x ∈ hyp.Q := by
  haveI : (hyp.Q.subgroupOf hyp.H).Normal := hyp.Q_subgroupOf_H_normal
  have h1 : orderOf (QuotientGroup.mk' (hyp.Q.subgroupOf hyp.H) ⟨x, hx⟩)
      ∣ Nat.card ↥hyp.Q :=
    dvd_trans (orderOf_map_dvd _ _) (by rw [Subgroup.orderOf_mk]; exact hord)
  have h2 : orderOf (QuotientGroup.mk' (hyp.Q.subgroupOf hyp.H) ⟨x, hx⟩)
      ∣ hyp.d := by
    rw [← hyp.index_Q_subgroupOf_eq_d, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hone : QuotientGroup.mk' (hyp.Q.subgroupOf hyp.H) ⟨x, hx⟩ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hyp.coprime_Q_D h1 h2)
  have hmem : (⟨x, hx⟩ : ↥hyp.H) ∈ hyp.Q.subgroupOf hyp.H :=
    (QuotientGroup.eq_one_iff _).mp hone
  exact Subgroup.mem_subgroupOf.mp hmem

section RestrictInduce

variable [Fintype G] [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]

omit [Fintype ↥hyp.H] in
/-- **[Is] CTFG Lemma 7.7, value form** (Theorem C, step (10), p. 116: "By
[Is], Lemma 7.7, `Res_H^G(eᵢ − e′ᵢ) = χᵢ − χ̄ᵢ` since `Q` is a Hall subgroup of
`H` and `χᵢ − χ̄ᵢ` vanishes on `H − Q`"): a class function supported on
`A = Q^#` is recovered by inducing to `G` and restricting back to `H`.

On `Q^#` this is the TI value identity (`induce_apply_coe_of_isTISubset`, with
`isTISubset_Q_sdiff_one`); at `1` both sides vanish (`φ(1) = 0`); and on
`H − Q` the induced function vanishes because no `G`-conjugate of such an
element lands in `Q^#` — its order does not divide `|Q|`
(`mem_Q_of_orderOf_dvd_card_Q`). -/
theorem restrict_induce_eq_of_support_subset_A [Finite G]
    {φ : ClassFunction ↥hyp.H ℂ} (hφ : φ.support ⊆ hyp.A) :
    ClassFunction.restrict hyp.H (ClassFunction.induce hyp.H φ) = φ := by
  classical
  have hvanish : ∀ x : ↥hyp.H, (x : G) ∉ ((hyp.Q : Set G) \ {1}) → φ x = 0 := by
    intro x hxA
    by_contra hne
    have hmem := hφ (ClassFunction.mem_support.mpr hne)
    refine hxA ⟨hmem.1, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h1
    exact hmem.2 (Subtype.ext h1)
  ext x
  rw [ClassFunction.restrict_apply]
  by_cases hxA : (x : G) ∈ ((hyp.Q : Set G) \ {1})
  · exact ClassFunction.induce_apply_coe_of_isTISubset hyp.H
      hyp.isTISubset_Q_sdiff_one hvanish hxA
  · rw [hvanish x hxA]
    by_cases hx1 : x = (1 : ↥hyp.H)
    · subst hx1
      rw [show ((1 : ↥hyp.H) : G) = (1 : G) from rfl,
        ClassFunction.induce_apply_one, hvanish 1 (fun h => h.2 rfl), mul_zero]
    · refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet
        (A := hyp.A) hφ ?_
      rintro ⟨g, hgH, hgA⟩
      have hordeq : orderOf (x : G) = orderOf (g⁻¹ * (x : G) * g) := by
        have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective (x : G)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
        rw [← h]
        congr 1
        group
      have hxQ : (x : G) ∈ hyp.Q := by
        refine hyp.mem_Q_of_orderOf_dvd_card_Q x.2 ?_
        rw [hordeq]
        exact Subgroup.orderOf_dvd_natCard hyp.Q hgA.1
      by_cases hone : (x : G) = 1
      · exact hx1 (Subtype.ext hone)
      · exact hxA ⟨hxQ, hone⟩

/-- **Theorem C, step (10), conjugate-pair identity** (p. 116): for `χ ∈ 𝒮`,
`Ind_H^G(χ̄ − χ) = e_{χ̄} − e_χ` — the `a = 1` case of the coherence identity
applied to the conjugate pair (`χ̄ ∈ 𝒮`, same degree). -/
theorem induce_conj_sub_extension [Finite G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    ClassFunction.induce hyp.H (χ.conj - χ)
      = hcoh.extension χ.conj - hcoh.extension χ := by
  have hdeg : χ.conj (1 : ↥hyp.H) = ((1 : ℕ) : ℂ) * χ (1 : ↥hyp.H) := by
    have h0 := hyp.conj_diff_apply_one_of_mem_Sset hχ
    rw [ClassFunction.sub_apply, sub_eq_zero] at h0
    rw [Nat.cast_one, one_mul]
    exact h0
  have h := hyp.induce_sub_nsmul_extension hcoh (hyp.conj_mem_Sset hχ) hχ
    (a := 1) hdeg
  simpa using h

/-- **Theorem C, step (10), inner-product transport** (p. 116:
"`(Ind_H^G λ, eᵢ − e′ᵢ) = (λ, χᵢ − χ̄ᵢ)`", stated for the conjugate pair in the
`χ̄ − χ` orientation): for every class function `θ` on `H`,
`⟨Ind_H^G θ, e_{χ̄} − e_χ⟩ = ⟨θ, χ̄ − χ⟩`.

Frobenius reciprocity followed by the Lemma 7.7 value identity
(`restrict_induce_eq_of_support_subset_A`, applicable since `χ̄ − χ` is
supported on `A = Q^#`). -/
theorem inner_induce_extension_conj_sub [Finite G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset)
    (θ : ClassFunction ↥hyp.H ℂ) :
    ClassFunction.inner (ClassFunction.induce hyp.H θ)
        (hcoh.extension χ.conj - hcoh.extension χ)
      = ClassFunction.inner θ (χ.conj - χ) := by
  rw [← hyp.induce_conj_sub_extension hcoh hχ,
    ClassFunction.inner_induce_eq_inner_restrict,
    hyp.restrict_induce_eq_of_support_subset_A
      (hyp.conj_diff_support_subset_A_of_mem_Sset hχ)]

/-- **The conjugate-pair image difference has degree zero**:
`(e_{χ̄} − e_χ)(1) = 0`, being `Ind_H^G` of the degree-zero difference `χ̄ − χ`
(Theorem C, step (10): the input to "`|Q| + 1 = ±2eᵢ(1)`"). -/
theorem extension_conj_sub_apply_one [Finite G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    (hcoh.extension χ.conj - hcoh.extension χ) (1 : G) = 0 := by
  rw [← hyp.induce_conj_sub_extension hcoh hχ, ClassFunction.induce_apply_one,
    hyp.conj_diff_apply_one_of_mem_Sset hχ, mul_zero]

/-- **Distinct members have orthogonal images**: for `χ ≠ χ'` in `𝒮`,
`⟨e_χ, e_{χ'}⟩ = 0` — the coherent extension transports the orthogonality of
distinct irreducible characters. -/
theorem extension_inner_eq_zero_of_ne [Finite G] [Invertible (Nat.card G : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ χ' : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset)
    (hne : χ ≠ χ') :
    ClassFunction.inner (hcoh.extension χ) (hcoh.extension χ') = 0 := by
  rw [hyp.extension_inner_member hcoh hχ hχ']
  exact hyp.Sset_pairwiseOrthogonal hχ hχ' hne

omit [Fintype G] in
/-- **A non-member is orthogonal to the conjugate difference of a member**:
for an irreducible `θ ∉ 𝒮` and `χ ∈ 𝒮`, `⟨θ, χ̄ − χ⟩ = 0` — both `χ` and `χ̄`
are members, hence distinct from `θ` (Theorem C, step (10):
"`(λ, χᵢ − χ̄ᵢ) = 0`"). -/
theorem inner_conj_sub_eq_zero_of_notMem [Finite G]
    {θ : ClassFunction ↥hyp.H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hθS : θ ∉ hyp.Sset)
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    ClassFunction.inner θ (χ.conj - χ) = 0 := by
  have hχc : χ.conj ∈ hyp.Sset := hyp.conj_mem_Sset hχ
  have h1 : ClassFunction.inner θ χ = 0 := by
    have h := OddOrder.RepresentationTheory.irr_cf_inner
      (mem_irreducibleCharacters.mpr hθ) (mem_irreducibleCharacters.mpr hχ.1)
    rwa [if_neg (fun h : θ = χ => hθS (h.symm ▸ hχ))] at h
  have h2 : ClassFunction.inner θ χ.conj = 0 := by
    have h := OddOrder.RepresentationTheory.irr_cf_inner
      (mem_irreducibleCharacters.mpr hθ) (mem_irreducibleCharacters.mpr hχc.1)
    rwa [if_neg (fun h : θ = χ.conj => hθS (h.symm ▸ hχc))] at h
  rw [ClassFunction.inner_sub_right, h1, h2, sub_zero]

/-- **Peterfalvi Part II, Ch. III, Theorem C, step (10)** (p. 116): if
`Ind_H^G θ = f + f'` splits a degree-one induced character into two distinct
irreducible constituents and `[G : H]` is odd, then each constituent is
orthogonal to every member image `e_χ` of the coherent extension.

By contradiction: `⟨f, e_χ⟩ ≠ 0` forces `f = ξ` (the irreducible carrier of
`e_χ = ε·ξ`).  The conjugate member gives `e_{χ̄} = ε'·ξ'` with `ξ' ≠ ξ`
(orthogonality of distinct member images), and
`⟨Ind θ, e_{χ̄} − e_χ⟩ = ⟨θ, χ̄ − χ⟩ = 0` transfers the nonzero coefficient to
`ξ'`, forcing `f' = ξ'`.  The degree-zero identity `(e_{χ̄} − e_χ)(1) = 0`
gives `ξ(1) = ξ'(1)`, so `[G : H] = (Ind θ)(1) = 2·ξ(1)` is even —
contradiction. -/
theorem inner_constituent_extension_eq_zero [Finite G]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    [Invertible (Nat.card G : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    (hidx : Odd hyp.H.index)
    {θ : ClassFunction ↥hyp.H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hdeg : (θ : ↥hyp.H → ℂ) 1 = 1) (hθS : θ ∉ hyp.Sset)
    {f f' : ClassFunction G ℂ} (hf : IsIrreducibleCharacter f)
    (hf' : IsIrreducibleCharacter f') (hff' : f ≠ f')
    (hsum : ClassFunction.induce hyp.H θ = f + f')
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    ClassFunction.inner f (hcoh.extension χ) = 0 := by
  classical
  by_contra hne0
  -- `e_χ = ε·ξ` and `⟨f, e_χ⟩ ≠ 0` force `f = ξ`
  obtain ⟨ε, ξ, hε, hεξ⟩ := hyp.extension_zsmul_irr hcoh hχ
  have hfξ : f = (ξ : ClassFunction G ℂ) := by
    by_contra hne
    apply hne0
    rw [hεξ, ← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hf)
        (mem_irreducibleCharacters.mpr ξ.isIrreducible),
      if_neg hne, mul_zero]
  -- the conjugate member and its image `e_{χ̄} = ε'·ξ'`
  have hχc : χ.conj ∈ hyp.Sset := hyp.conj_mem_Sset hχ
  obtain ⟨ε', ξ', hε', hεξ'⟩ := hyp.extension_zsmul_irr hcoh hχc
  have hχne : χ ≠ χ.conj := fun h =>
    hasNoRealCharacters_Sset hyp hd hQ1odd hχ h.symm
  -- distinct members have orthogonal images, so `ξ ≠ ξ'`
  have hξξ' : (ξ : ClassFunction G ℂ) ≠ (ξ' : ClassFunction G ℂ) := by
    intro heq
    have horth := hyp.extension_inner_eq_zero_of_ne hcoh hχ hχc hχne
    rw [hεξ, hεξ', ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, ← heq,
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr ξ.isIrreducible)
        (mem_irreducibleCharacters.mpr ξ.isIrreducible),
      if_pos rfl, mul_one, star_intCast] at horth
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num at horth
  -- `⟨Ind θ, e_{χ̄} − e_χ⟩ = ⟨θ, χ̄ − χ⟩ = 0`
  have hdagger : ClassFunction.inner (ClassFunction.induce hyp.H θ)
      (hcoh.extension χ.conj - hcoh.extension χ) = 0 := by
    rw [hyp.inner_induce_extension_conj_sub hcoh hχ θ]
    exact hyp.inner_conj_sub_eq_zero_of_notMem hθ hθS hχ
  -- `⟨Ind θ, e_χ⟩ = ε`
  have hIθχ : ClassFunction.inner (ClassFunction.induce hyp.H θ)
      (hcoh.extension χ) = (ε : ℂ) := by
    rw [hsum, hεξ, ← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_add_left,
      ClassFunction.inner_smul_right, ClassFunction.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hf)
        (mem_irreducibleCharacters.mpr ξ.isIrreducible),
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hf')
        (mem_irreducibleCharacters.mpr ξ.isIrreducible),
      if_pos hfξ, if_neg (fun h => hff' (hfξ.trans h.symm)), mul_one, mul_zero,
      add_zero, star_intCast]
  -- hence `⟨Ind θ, e_{χ̄}⟩ = ε ≠ 0`, forcing `f' = ξ'`
  have hIθχc : ClassFunction.inner (ClassFunction.induce hyp.H θ)
      (hcoh.extension χ.conj) = (ε : ℂ) := by
    have h := hdagger
    rw [ClassFunction.inner_sub_right, sub_eq_zero] at h
    rw [h, hIθχ]
  have hf'ξ' : f' = (ξ' : ClassFunction G ℂ) := by
    by_contra hne
    have h := hIθχc
    rw [hsum, hεξ', ← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_add_left,
      ClassFunction.inner_smul_right, ClassFunction.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hf)
        (mem_irreducibleCharacters.mpr ξ'.isIrreducible),
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hf')
        (mem_irreducibleCharacters.mpr ξ'.isIrreducible),
      if_neg (fun h' => hξξ' (hfξ ▸ h')), if_neg hne, mul_zero, add_zero] at h
    rcases hε with rfl | rfl <;> norm_num at h
  -- degrees: `ε'·ξ'(1) = ε·ξ(1)`, both positive naturals, so `ξ(1) = ξ'(1)`
  obtain ⟨a, ha, haval⟩ := ξ.isIrreducible.exists_apply_one_eq_pos_natCast
  obtain ⟨b, hb, hbval⟩ := ξ'.isIrreducible.exists_apply_one_eq_pos_natCast
  have hd0 := hyp.extension_conj_sub_apply_one hcoh hχ
  rw [hεξ, hεξ', ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
    ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.smul_apply,
    sub_eq_zero, haval, hbval] at hd0
  have hZ : (ε' * b : ℤ) = ε * a := by
    have h : ((ε' * b : ℤ) : ℂ) = ((ε * a : ℤ) : ℂ) := by push_cast; exact hd0
    exact_mod_cast h
  have haeqb : a = b := by
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> omega
  -- the degree count: `[G : H] = a + b = 2a`, contradicting `[G : H]` odd
  have hval : ClassFunction.induce hyp.H θ (1 : G)
      = (hyp.H.index : ℂ) := by
    rw [ClassFunction.induce_apply_one,
      show θ (1 : ↥hyp.H) = 1 from hdeg, mul_one]
  rw [hsum, ClassFunction.add_apply, hfξ, hf'ξ', haval, hbval] at hval
  have hN : a + b = hyp.H.index := by
    have h : ((a + b : ℕ) : ℂ) = ((hyp.H.index : ℕ) : ℂ) := by
      push_cast
      rw [← hval]
    exact_mod_cast h
  obtain ⟨k, hk⟩ := hidx
  omega

/-- **Theorem C, step (11), member multiplicities** (p. 116,
"`(Res_H^G f_j, χᵢ − aᵢχ₁) = 0`"): if `f` is orthogonal to every member image
(step (10)), then the multiplicity of a member `χ` in `Res_H^G f` is
proportional to its degree: `⟨Res f, χ⟩ = a·⟨Res f, χ₁⟩` when
`χ(1) = a·χ₁(1)`.

Frobenius reciprocity turns `⟨e_χ − a·e_{χ₁}, f⟩ = 0` (step (9) plus the
orthogonality hypothesis) into `⟨χ − a·χ₁, Res f⟩ = 0`. -/
theorem inner_restrict_eq_mul [Finite G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {f : ClassFunction G ℂ}
    (hforth : ∀ ψ ∈ hyp.Sset, ClassFunction.inner f (hcoh.extension ψ) = 0)
    {χ₁ χ : ClassFunction ↥hyp.H ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ : χ ∈ hyp.Sset)
    {a : ℕ} (hdeg : χ (1 : ↥hyp.H) = (a : ℂ) * χ₁ (1 : ↥hyp.H)) :
    ClassFunction.inner (ClassFunction.restrict hyp.H f) χ
      = (a : ℂ) * ClassFunction.inner (ClassFunction.restrict hyp.H f) χ₁ := by
  have h9 := hyp.induce_sub_nsmul_extension hcoh hχ hχ₁ hdeg
  have hrec := ClassFunction.inner_induce_eq_inner_restrict hyp.H (χ - a • χ₁) f
  rw [h9, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a (hcoh.extension χ₁),
    ← Nat.cast_smul_eq_nsmul ℂ a χ₁,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left] at hrec
  have hzχ : ClassFunction.inner (hcoh.extension χ) f = 0 := by
    rw [ClassFunction.inner_star_comm, hforth χ hχ, star_zero]
  have hzχ₁ : ClassFunction.inner (hcoh.extension χ₁) f = 0 := by
    rw [ClassFunction.inner_star_comm, hforth χ₁ hχ₁, star_zero]
  rw [hzχ, hzχ₁, mul_zero, sub_zero] at hrec
  -- hrec : 0 = ⟨χ, Res f⟩ − a·⟨χ₁, Res f⟩
  have h := sub_eq_zero.mp hrec.symm
  -- transpose through `star`
  calc ClassFunction.inner (ClassFunction.restrict hyp.H f) χ
      = star (ClassFunction.inner χ (ClassFunction.restrict hyp.H f)) := by
        rw [ClassFunction.inner_star_comm]
    _ = star ((a : ℂ) * ClassFunction.inner χ₁ (ClassFunction.restrict hyp.H f)) := by
        rw [h]
    _ = (a : ℂ) * ClassFunction.inner (ClassFunction.restrict hyp.H f) χ₁ := by
        rw [star_mul', star_natCast, ClassFunction.inner_star_comm, star_star]

omit [Fintype G] in
/-- **Theorem C, step (12), kernel conclusion** (p. 116, "`b_j = 0` and so
`Q₁ ⊂ Ker f_j`"): if no member of `𝒮` occurs in `Res_H^G f` (`f` a genuine
character of `G`), then `Q₁` lies in the kernel of `f`.

Every irreducible constituent of `Res f` is then outside `𝒮`, i.e. has `Q₁`
in its kernel, so the constituent sum takes its degree value on `Q₁`. -/
theorem mem_characterKernel_of_forall_inner_restrict_eq_zero [Finite G]
    {f : ClassFunction G ℂ} (hfchar : IsCharacter f)
    (hzero : ∀ χ ∈ hyp.Sset,
      ClassFunction.inner (ClassFunction.restrict hyp.H f) χ = 0)
    {x : G} (hx : x ∈ hyp.Q1) :
    x ∈ OddOrder.Peterfalvi.S03.characterKernel f := by
  classical
  have hres : IsCharacter (ClassFunction.restrict hyp.H f) :=
    isCharacter_restrict hyp.H hfchar
  obtain ⟨m, hsupp, hrepr, hcoeff⟩ := hres.exists_natFinsupp_eq_sum
  have hxH : x ∈ hyp.H := hyp.Q_le_H (hyp.Q1_le_Q hx)
  -- every constituent lies outside `𝒮`, hence kills `Q₁`
  have hker : ∀ a ∈ m.support,
      (a : ClassFunction ↥hyp.H ℂ) ⟨x, hxH⟩ = a (1 : ↥hyp.H) := by
    intro a ha
    have hairr : IsIrreducibleCharacter a := mem_irreducibleCharacters.mp (hsupp ha)
    have haS : a ∉ hyp.Sset := by
      intro haS
      have h0 := hzero a haS
      rw [← hcoeff a hairr] at h0
      exact Finsupp.mem_support_iff.mp ha (by exact_mod_cast h0)
    have hLK : hyp.LeKer a hyp.Q1 := by
      by_contra hnk
      exact haS ⟨hairr, hnk⟩
    exact hLK ⟨x, hxH⟩ hx
  -- evaluate the constituent sum at `x` and at `1`
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def]
  have hres_x : f x = ClassFunction.restrict hyp.H f ⟨x, hxH⟩ :=
    (ClassFunction.restrict_apply hyp.H f ⟨x, hxH⟩).symm
  have hres_1 : f 1 = ClassFunction.restrict hyp.H f (1 : ↥hyp.H) := by
    rw [ClassFunction.restrict_apply]
    norm_num
  rw [hres_x, hres_1, hrepr, ClassFunction.sum_apply, ClassFunction.sum_apply]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [ClassFunction.smul_apply, ClassFunction.smul_apply, hker a ha]

end RestrictInduce

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
