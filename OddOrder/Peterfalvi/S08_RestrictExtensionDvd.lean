/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_XBlockCounting

/-!
# S08_RestrictExtensionDvd

Prefix-split from `OddOrder.Peterfalvi.S08_CoherenceCore` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis
variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]


/-- **(6.8.1) `a ∣ c`**, case (A) / c2 mirror of `dvd_inner_restrict_extension_Yset_of_frobenius`.
`X`-irreducibility uses `isIrreducibleCharacter_of_mem_Xset_c2_caseA`, and the value/congruence
inputs use the case-(A) `restrict_extension_Yset_degree_value_eq_c2_caseA` /
`restrict_extension_Yset_charValue_cong_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem dvd_inner_restrict_extension_Yset_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cc : ℤ,
      ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁ = (cc : ℂ)
        ∧ (a : ℤ) ∣ cc := by
  classical
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  -- `c := ⟨R, χ₁⟩` is an integer (`R ∈ ZIrr L`, `χ₁` irreducible).
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : R ∈ ZIrr (↥L) := OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
  obtain ⟨cc, hcc⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ₁ from rfl] at hcc
  refine ⟨cc, hcc, ?_⟩
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hHne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- pick `z ∈ Zc^#`.
  obtain ⟨⟨z, hz⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (hyp.centralCommutator_ne_bot hHnonab)
  have hz1 : z ≠ 1 := fun h => hzne (Subtype.ext h)
  -- value identity: `χ₁(1)·(R z − R 1) = −c·|L|`, with `χ₁(1) = a|W₁|`, `c = cc`, `|L| = |H||W₁|`.
  have hval := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz hz1
  rw [← hRdef, hcc, ha] at hval
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card hyp.W1 : ℂ) := by
    have h := Subgroup.index_mul_card H
    rw [hyp.index_H_eq_card_W1] at h
    have hc : ((Nat.card hyp.W1 * Nat.card ↥H : ℕ) : ℂ) = (Nat.card ↥L : ℂ) := by rw [h]
    push_cast at hc; linear_combination -hc
  rw [hLcard] at hval
  -- cancel `|W₁|`: `a·(R z − R 1) = −c·|H|`.
  have haD : (a : ℂ) * (R z - R 1) = -(cc : ℂ) * (Nat.card ↥H : ℂ) := by
    apply mul_left_cancel₀ hW1ne
    linear_combination hval
  -- the (6.7)-congruence: `(R z − R 1)/|H|` is an algebraic integer.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hz hz1
  rw [← hRdef, OddOrder.AlgInt.cong_def, Int.cast_natCast] at hcong
  -- `c/a = −((R z − R 1)/|H|)`, so `c/a` is an algebraic integer.
  have hccdiv : (cc : ℂ) / (a : ℂ) = -((R z - R 1) / (Nat.card ↥H : ℂ)) := by
    rw [← neg_div, div_eq_div_iff hane hHne]
    linear_combination haD
  have hintc : IsIntegral ℤ ((cc : ℂ) / (a : ℂ)) := by rw [hccdiv]; exact hcong.neg
  -- a rational algebraic integer is an integer ⟹ `a ∣ c`.
  have hqcast : (((cc : ℚ) / (a : ℚ) : ℚ) : ℂ) = (cc : ℂ) / (a : ℂ) := by push_cast; ring
  obtain ⟨n, hn⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int
    (q := (cc : ℚ) / (a : ℚ)) (by rw [hqcast]; exact hintc)
  rw [hqcast, div_eq_iff hane] at hn
  refine ⟨n, ?_⟩
  have : (cc : ℂ) = ((a : ℤ) * n : ℤ) := by rw [hn]; push_cast; ring
  exact_mod_cast this

/-- **(6.8.1) `a ∣ b`** (mmd 04.8 L176, the `b ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η = η₁ ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|` (`a > 0`), the
`η₁^{τ₁}`-coefficient
of the cross-diagonal image `(χ₁−aη₁)^τ` — namely `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩`, which is `b − a` in the
Peterfalvi decomposition (168) `(χ₁−aη₁)^τ = X − aη₁^{τ₁} + b∑η_j^{τ₁}` — is an **integer divisible
by `a`**.  Since `a ∣ (b − a) ⟺ a ∣ b`, this is exactly Peterfalvi's `b ≡ 0 (mod a)`.

Direct route via Dade reciprocity (no need for the full (168) decomposition): `χ₁−aη₁` is supported
on `H^#` (`sMember_scaledDiffSupport_of_charValue_eq`, `χ₁(1) = a·η₁(1)` from `Yset_apply_one`), so
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, Res^G_L(η₁^{τ₁})⟩` (`inner_tau_eq_inner_restrict`)
`= ⟨χ₁, R⟩ − a·⟨η₁, R⟩ = c − a·e` (`R = Res^G_L(η₁^{τ₁})`; conjugate symmetry `inner_conj_symm` +
reality of the integers `c = ⟨R,χ₁⟩`, `e = ⟨R,η₁⟩`, `mem_ZIrr_inner_int`).  Since `a ∣ c`
(`dvd_inner_restrict_extension_Yset_of_frobenius`, step 2) and `a ∣ a·e`, `a ∣ (c − a·e)`. -/
theorem dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ bb : ℤ,
      ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.coherentYset.extension η) = (bb : ℂ)
        ∧ (a : ℤ) ∣ bb := by
  classical
  -- step 2: `c = ⟨R, χ₁⟩` is an integer with `a ∣ c`.
  obtain ⟨cc, hcc, hacc⟩ :=
    hyp.dvd_inner_restrict_extension_Yset_of_frobenius hF hHnonab hp hp3 hHp hη hχ₁ ha_pos ha
  -- `R ∈ ZIrr L`, `η₁` irreducible ⟹ `e := ⟨R, η₁⟩ ∈ ℤ`.
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : ClassFunction.restrict L (hyp.coherentYset.extension η) ∈ ZIrr (↥L) :=
    OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  obtain ⟨e, he⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨η, hηirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η from rfl] at he
  -- `χ₁ − a•η₁` is supported on `H^#`.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  -- reciprocity: `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩`.
  have hrec := hyp.inner_tau_eq_inner_restrict hsupp (hyp.coherentYset.extension η)
  refine ⟨cc - a * e, ?_, ?_⟩
  · rw [hrec, ClassFunction.inner_sub_left, ← Nat.cast_smul_eq_nsmul ℂ a η,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm _ χ₁, hcc,
      OddOrder.RepresentationTheory.inner_conj_symm _ η, he]
    simp only [star_intCast]
    push_cast; ring
  · exact dvd_sub hacc (dvd_mul_right _ _)

/-- **(6.8.1) `a ∣ b`**, case (A) / c2 mirror of `dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius`.
The `a ∣ c` input uses the case-(A) `dvd_inner_restrict_extension_Yset_c2_caseA`
(cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ bb : ℤ,
      ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.coherentYset.extension η) = (bb : ℂ)
        ∧ (a : ℤ) ∣ bb := by
  classical
  -- step 2: `c = ⟨R, χ₁⟩` is an integer with `a ∣ c`.
  obtain ⟨cc, hcc, hacc⟩ :=
    hyp.dvd_inner_restrict_extension_Yset_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ ha_pos ha
  -- `R ∈ ZIrr L`, `η₁` irreducible ⟹ `e := ⟨R, η₁⟩ ∈ ℤ`.
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : ClassFunction.restrict L (hyp.coherentYset.extension η) ∈ ZIrr (↥L) :=
    OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  obtain ⟨e, he⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨η, hηirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η from rfl] at he
  -- `χ₁ − a•η₁` is supported on `H^#`.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  -- reciprocity: `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩`.
  have hrec := hyp.inner_tau_eq_inner_restrict hsupp (hyp.coherentYset.extension η)
  refine ⟨cc - a * e, ?_, ?_⟩
  · rw [hrec, ClassFunction.inner_sub_left, ← Nat.cast_smul_eq_nsmul ℂ a η,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm _ χ₁, hcc,
      OddOrder.RepresentationTheory.inner_conj_symm _ η, he]
    simp only [star_intCast]
    push_cast; ring
  · exact dvd_sub hacc (dvd_mul_right _ _)

/-- **(6.8.1) cross-diagonal/`Y`-difference isometry** (mmd 04.8 L166, the constancy ingredient of
decomposition (168)).  For `η = η₁`, `η' = η_j ∈ Y` with `η' ≠ η`, and an `X`-anchor `χ₁ ∈ X(Zc)`
with `χ₁(1) = a·|W₁|` (`a > 0`):
`⟨(χ₁−aη₁)^τ, (η_j−η₁)^τ⟩ = a`.

By the Dade isometry on the supported pair `{χ₁−aη₁, η_j−η₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; `χ₁−aη₁` supported by
`sMember_scaledDiffSupport_of_charValue_eq`, `η_j−η₁` by `sMember_diffSupport_of_charValue_eq` at
the
common degree `|W₁|`), the inner product equals the source `⟨χ₁−aη₁, η_j−η₁⟩`, which expands by
`X ⊥ Y` (`⟨χ₁,η_j⟩ = ⟨χ₁,η₁⟩ = 0`) and `Y`-orthonormality (`⟨η₁,η_j⟩ = 0`, `⟨η₁,η₁⟩ = 1`) to
`a·⟨η₁,η₁⟩ = a`.  This gives the constancy `β_j − β₁ = a` (j>1) of the `η_j^{τ₁}`-coefficients
`β_j = ⟨(χ₁−aη₁)^τ, η_j^{τ₁}⟩` of decomposition (168). -/
theorem inner_tau_scaledDiff_tau_Yset_diff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (η' - η)) = (a : ℂ) := by
  classical
  -- irreducibility + disjointness `X(Zc) ⊥ Y`.
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported difference inputs.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsuppX : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hsuppY : (η' - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη).symm)
  -- Dade isometry on the supported pair.
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η, η' - η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- the source orthogonality computation `⟨χ₁ − a•η, η' − η⟩ = a`.
  have hXY : ∀ ψ ∈ hyp.Yset, ClassFunction.inner χ₁ ψ = 0 := by
    intro ψ hψ
    exact inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hXirr φ hφ) (fun φ hφ => hYirr φ hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      ψ (Submodule.subset_span hψ)
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXY η' hη', hXY η hη, hYon η η' hη hη', hYon η η hη hη, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) cross-diagonal/`Y`-difference isometry**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`.  `X`-irreducibility comes from the certain-type
input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Yset_diff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (η' - η)) = (a : ℂ) := by
  classical
  -- irreducibility + disjointness `X(Zc) ⊥ Y`.
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported difference inputs.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsuppX : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hsuppY : (η' - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη).symm)
  -- Dade isometry on the supported pair.
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η, η' - η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- the source orthogonality computation `⟨χ₁ − a•η, η' − η⟩ = a`.
  have hXY : ∀ ψ ∈ hyp.Yset, ClassFunction.inner χ₁ ψ = 0 := by
    intro ψ hψ
    exact inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hXirr φ hφ) (fun φ hφ => hYirr φ hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      ψ (Submodule.subset_span hψ)
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXY η' hη', hXY η hη, hYon η η' hη hη', hYon η η hη hη, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) norm of the cross-diagonal image** (mmd 04.8 L176: `‖χ₁−aη₁‖² = 1+a²`).  For `η = η₁ ∈ Y`
and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`:
`⟨(χ₁−aη₁)^τ, (χ₁−aη₁)^τ⟩ = 1 + a²`.

By the Dade isometry on the supported singleton `{χ₁−aη₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`) this equals the source norm
`⟨χ₁−aη₁, χ₁−aη₁⟩`, which expands by `χ₁`/`η₁`-orthonormality (`⟨χ₁,χ₁⟩ = ⟨η₁,η₁⟩ = 1`) and `X ⊥ Y`
(`⟨χ₁,η₁⟩ = ⟨η₁,χ₁⟩ = 0`) to `1 + a²`.  This is the LHS of Peterfalvi's norm identity
`1+a² = ‖X‖² + (b−a)² + (m−1)b²` for the `b = 0` step. -/
theorem inner_self_tau_scaledDiff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (χ₁ - a • η)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- orthonormality / orthogonality scalars.
  have hχ₁n : ClassFunction.inner χ₁ χ₁ = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηn : ClassFunction.inner η η = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hXY : ClassFunction.inner χ₁ η = (0 : ℂ) :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      η (Submodule.subset_span hη)
  have hYX : ClassFunction.inner η χ₁ = (0 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm χ₁ η, hXY, star_zero]
  -- supported singleton ⟹ Dade isometry.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hχ₁n, hηn,
    hXY, hYX, star_natCast]
  ring

/-- **(6.8.1) norm of the cross-diagonal image**, case (A) / c2 mirror of
`inner_self_tau_scaledDiff_of_frobenius`.  `X`-irreducibility comes from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_self_tau_scaledDiff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (χ₁ - a • η)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- orthonormality / orthogonality scalars.
  have hχ₁n : ClassFunction.inner χ₁ χ₁ = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηn : ClassFunction.inner η η = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hXY : ClassFunction.inner χ₁ η = (0 : ℂ) :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      η (Submodule.subset_span hη)
  have hYX : ClassFunction.inner η χ₁ = (0 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm χ₁ η, hXY, star_zero]
  -- supported singleton ⟹ Dade isometry.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hχ₁n, hηn,
    hXY, hYX, star_natCast]
  ring

/-- **(6.8.1) the degree ratio `a` satisfies `a ≥ 2`** (mmd 04.8 L176: "Since `X ∩ Y = ∅`, `a > 1`").
For an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, the ratio `a ≥ 2`.

If `a ≤ 1` then (as `χ₁` is a positive-degree irreducible, `a ≥ 1`, so) `a = 1`, hence the source
`θ` (with `χ₁ = Ind_H^L θ`, `θ ≠ 1`, `χ₁(1) = |W₁|·θ(1)`) has degree `θ(1) = a = 1`, so `θ` is a
nontrivial **linear** character (`exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`); then
`χ₁ = Ind_H^L θ ∈ Y = S(H')` (`mem_Yset_iff_exists_linear_source`), contradicting `χ₁ ∈ X` and the
disjointness `X(Zc) ∩ Y = ∅`.  This is the `2 ≤ a` input of `eq_zero_or_edge_of_dvd_of_normBound`. -/
theorem two_le_degreeRatio_of_mem_Xset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) : 2 ≤ a := by
  classical
  -- extract the source `θ` of `χ₁ ∈ S`.
  have hχ₁S : χ₁ ∈ hyp.S := hyp.Xset_subset_S hχ₁
  rw [hyp.S_eq] at hχ₁S
  obtain ⟨θ, hθne, hχ₁eq⟩ := hχ₁S
  -- `χ₁(1) = |W₁|·θ(1)`.
  have hdeg : χ₁ 1 = (Nat.card hyp.W1 : ℂ) * (θ : ClassFunction ↥H ℂ) 1 := by
    rw [hχ₁eq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      hyp.index_H_eq_card_W1]
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- `(a : ℂ) = θ(1)`.
  have haθ : (a : ℂ) = (θ : ClassFunction ↥H ℂ) 1 := by
    have h : (a : ℂ) * (Nat.card hyp.W1 : ℂ)
        = (θ : ClassFunction ↥H ℂ) 1 * (Nat.card hyp.W1 : ℂ) := by rw [← ha, hdeg]; ring
    exact mul_right_cancel₀ hW1ne h
  -- `θ(1) = d > 0`, so `a = d ≥ 1`.
  obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have had : a = d := by have := haθ.trans hd_eq; exact_mod_cast this
  by_contra hlt
  push Not at hlt
  -- `a ≤ 1` with `a = d ≥ 1` ⟹ `a = 1` ⟹ `θ(1) = 1`.
  have ha1 : a = 1 := by omega
  have hθ1 : (θ : ClassFunction ↥H ℂ) 1 = 1 := by rw [← haθ, ha1]; norm_num
  -- `θ` is a nontrivial linear character ⟹ `χ₁ ∈ Y`, contradicting `χ₁ ∈ X`.
  obtain ⟨ψ, hψeq⟩ := θ.2.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hθ1
  have hlinθ : OddOrder.RepresentationTheory.linearIrreducibleCharacter ψ = θ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.ext hψeq
  have hψne : ψ ≠ 1 := by
    intro hψ1
    apply hθne
    rw [← hlinθ, hψ1]
    exact OddOrder.RepresentationTheory.linearIrreducibleCharacter_eq_trivial_iff.mpr rfl
  have hχ₁Y : χ₁ ∈ hyp.Yset := by
    rw [hyp.mem_Yset_iff_exists_linear_source]
    exact ⟨ψ, hψne, by rw [hχ₁eq, hψeq]⟩
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact absurd hχ₁Y (Set.disjoint_left.mp hdisj hχ₁)

open scoped Classical in
/-- **(6.8.1) step-4 dichotomy** (mmd 04.8 L176, "`b ≡ c ≡ 0 (mod a)` ⟹ `b = 0` or the `m=2`
edge").  For `η₁ ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, the
`η₁^{τ₁}`-coefficient `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩` (Peterfalvi's `b − a`) is either `−a` (the `b = 0`
case) or `0` with
`|Y| = 2` (the `b = a ∧ m = 2` edge case).

Bessel's inequality (`sum_sq_le_inner_self_re`) over the orthonormal `Y^{τ₁}`-family with
`v = (χ₁−aη₁)^τ`: the coefficient is `bb = ⟨v,η₁^{τ₁}⟩` (`= b−a`, `a ∣ bb`, step 3) on `η₁^{τ₁}`
and `bb + a` on the other `m−1` members (the constancy
`inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`); their squares sum to
`bb² + (m−1)(bb+a)² ≤ ‖v‖² = 1 + a²` (norm `inner_self_tau_scaledDiff_of_frobenius`).  With
`a ∣ (bb+a)`, `2 ≤ a` (`two_le_degreeRatio_of_mem_Xset_of_frobenius`), `2 ≤ m`
(`two_le_Yset_ncard`), `eq_zero_or_edge_of_dvd_of_normBound` gives
`bb+a = 0 ∨ (bb+a = a ∧ m = 2)`. -/
theorem coeff_eq_neg_or_edge_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  classical
  -- step 3: `bb = ⟨v, η₁^{τ₁}⟩ ∈ ℤ`, `a ∣ bb`.
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha
  -- `Y`-orthonormality and injectivity of the extension on `Y`.
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Yset hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Yset hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hEinj : ∀ η ∈ hyp.Yset, ∀ η' ∈ hyp.Yset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' := by
    intro η hη η' hη' heq
    by_contra hne
    have h0 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 0 := by
      rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span hη)
        (Submodule.subset_span hη'), hYon η η' hη hη', if_neg hne]
    have h1 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1] at h0; exact one_ne_zero h0
  -- coefficient values `⟨v, η^{τ₁}⟩`.
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hsuppd : (η - η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
        hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
          ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
      have htaud : hyp.tau (η - η₁)
          = hyp.coherentYset.extension η - hyp.coherentYset.extension η₁ := by
        rw [← hyp.coherentYset.extends_on_supported (η - η₁)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
          map_sub]
      have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη hee hχ₁ ha
      rw [htaud, ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  -- the orthonormal `Y^{τ₁}`-image Finset.
  have hmemt : ∀ {η}, η ∈ hyp.Yset_finite.toFinset ↔ η ∈ hyp.Yset :=
    fun {η} => hyp.Yset_finite.mem_toFinset
  have hEinj_t : ∀ η ∈ hyp.Yset_finite.toFinset, ∀ η' ∈ hyp.Yset_finite.toFinset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' :=
    fun η hη η' hη' => hEinj η (hmemt.mp hη) η' (hmemt.mp hη')
  have horth : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ∀ ψ' ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ hψ ψ' hψ'
    rw [Finset.mem_image] at hψ hψ'
    obtain ⟨η, hη, rfl⟩ := hψ
    obtain ⟨η', hη', rfl⟩ := hψ'
    rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span (hmemt.mp hη))
      (Submodule.subset_span (hmemt.mp hη')), hYon η η' (hmemt.mp hη) (hmemt.mp hη')]
    by_cases hee : η = η'
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η' hη' h))]
  have hη₁t : η₁ ∈ hyp.Yset_finite.toFinset := hmemt.mpr hη₁
  have hβval : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  -- Bessel + norm ⟹ the integer norm inequality.
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (χ₁ - a • η₁)) hβval
  have hnorm_re : (ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₁ - a • η₁))).re
      = ((1 + a ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_scaledDiff_of_frobenius hF hη₁ hχ₁ ha,
      show (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + a ^ 2 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + a) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hc : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  -- the integer inequality and `eq_zero_or_edge`.
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 ≤ 1 + (a : ℤ) ^ 2 := by
    exact_mod_cast hbessel
  have ha2 : (2 : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hnorm_lemma : ((bb + a) - (a : ℤ)) ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2
      ≤ 1 + (a : ℤ) ^ 2 := by
    rw [show (bb + (a : ℤ)) - (a : ℤ) = bb by ring]; exact hnorm_ineq
  have hdich := eq_zero_or_edge_of_dvd_of_normBound ha2 hm2 (dvd_add habb (dvd_refl _)) hnorm_lemma
  -- translate `bb+a = 0 ∨ (bb+a = a ∧ m = 2)` to the coefficient dichotomy.
  rcases hdich with h | ⟨h1, h2⟩
  · left
    rw [hbb]
    have : bb = -(a : ℤ) := by omega
    rw [this]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have : bb = 0 := by omega
    rw [this]; norm_num

open scoped Classical in
/-- **(6.8.1) step-4 dichotomy**, case (A) / c2 mirror of `coeff_eq_neg_or_edge_of_frobenius`.
The divisibility/constancy/norm inputs use their case-(A) counterparts
(`dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA`, `inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`,
`inner_self_tau_scaledDiff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem coeff_eq_neg_or_edge_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  classical
  -- step 3: `bb = ⟨v, η₁^{τ₁}⟩ ∈ ℤ`, `a ∣ bb`.
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos
        ha
  -- `Y`-orthonormality and injectivity of the extension on `Y`.
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Yset hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Yset hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hEinj : ∀ η ∈ hyp.Yset, ∀ η' ∈ hyp.Yset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' := by
    intro η hη η' hη' heq
    by_contra hne
    have h0 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 0 := by
      rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span hη)
        (Submodule.subset_span hη'), hYon η η' hη hη', if_neg hne]
    have h1 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1] at h0; exact one_ne_zero h0
  -- coefficient values `⟨v, η^{τ₁}⟩`.
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hsuppd : (η - η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
        hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
          ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
      have htaud : hyp.tau (η - η₁)
          = hyp.coherentYset.extension η - hyp.coherentYset.extension η₁ := by
        rw [← hyp.coherentYset.extends_on_supported (η - η₁)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
          map_sub]
      have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη hee hχ₁ ha
      rw [htaud, ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  -- the orthonormal `Y^{τ₁}`-image Finset.
  have hmemt : ∀ {η}, η ∈ hyp.Yset_finite.toFinset ↔ η ∈ hyp.Yset :=
    fun {η} => hyp.Yset_finite.mem_toFinset
  have hEinj_t : ∀ η ∈ hyp.Yset_finite.toFinset, ∀ η' ∈ hyp.Yset_finite.toFinset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' :=
    fun η hη η' hη' => hEinj η (hmemt.mp hη) η' (hmemt.mp hη')
  have horth : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ∀ ψ' ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ hψ ψ' hψ'
    rw [Finset.mem_image] at hψ hψ'
    obtain ⟨η, hη, rfl⟩ := hψ
    obtain ⟨η', hη', rfl⟩ := hψ'
    rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span (hmemt.mp hη))
      (Submodule.subset_span (hmemt.mp hη')), hYon η η' (hmemt.mp hη) (hmemt.mp hη')]
    by_cases hee : η = η'
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η' hη' h))]
  have hη₁t : η₁ ∈ hyp.Yset_finite.toFinset := hmemt.mpr hη₁
  have hβval : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  -- Bessel + norm ⟹ the integer norm inequality.
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (χ₁ - a • η₁)) hβval
  have hnorm_re : (ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₁ - a • η₁))).re
      = ((1 + a ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ ha,
      show (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + a ^ 2 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + a) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hc : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  -- the integer inequality and `eq_zero_or_edge`.
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 ≤ 1 + (a : ℤ) ^ 2 := by
    exact_mod_cast hbessel
  have ha2 : (2 : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hnorm_lemma : ((bb + a) - (a : ℤ)) ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2
      ≤ 1 + (a : ℤ) ^ 2 := by
    rw [show (bb + (a : ℤ)) - (a : ℤ) = bb by ring]; exact hnorm_ineq
  have hdich := eq_zero_or_edge_of_dvd_of_normBound ha2 hm2 (dvd_add habb (dvd_refl _)) hnorm_lemma
  -- translate `bb+a = 0 ∨ (bb+a = a ∧ m = 2)` to the coefficient dichotomy.
  rcases hdich with h | ⟨h1, h2⟩
  · left
    rw [hbb]
    have : bb = -(a : ℤ) := by omega
    rw [this]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have : bb = 0 := by omega
    rw [this]; norm_num

open scoped Classical in
/-- **(6.8.1) step-4 good-case `X`-structure** (mmd 04.8 L176: "`b = 0` ⟹
`(χ₁ − aη₁)^τ = X − aη₁^{τ₁}`, `‖X‖² = ‖χ₁‖² = 1`").  In the good case
`⟨(χ₁ − aη₁)^τ, η₁^{τ₁}⟩ = −a` (the `b = 0` branch of `coeff_eq_neg_or_edge_of_frobenius`), the
element `X := (χ₁ − aη₁)^τ + a·η₁^{τ₁}` is orthogonal to the whole coherent `Y`-image family
`Y^{τ₁}`, has norm `1`, and lies in `ℤ[Irr G]`.  Step 5 then identifies `X = χ₁^{τ₂}`, giving the
crux `(χ₁ − aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`.

The orthogonality uses the constancy `inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`
(`⟨v, (η − η₁)^τ⟩ = a`, so `⟨v, η^{τ₁}⟩ = ⟨v, η₁^{τ₁}⟩ + a = 0` for `η ≠ η₁`) and the norm
`‖v‖² = 1 + a²` (`inner_self_tau_scaledDiff_of_frobenius`); the norm of `X` is
`(1 + a²) − a² − a² + a² = 1`. -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- Y-image orthonormality: `⟨η^{τ₁}, η'^{τ₁}⟩ = ⟨η, η'⟩ = δ`.
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη)
      (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  -- `⟨v, η^{τ₁}⟩ = 0` for `η ≠ η₁` (constancy `⟨v, (η−η₁)^τ⟩ = a` plus `⟨v, η₁^{τ₁}⟩ = −a`).
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner v (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη hne hχ₁ ha
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁)
        = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  -- norm and the conjugate of the good-case coefficient.
  have hvv : ClassFunction.inner v v = 1 + (a : ℂ) ^ 2 :=
    hyp.inner_self_tau_scaledDiff_of_frobenius hF hη₁ hχ₁ ha
  have he₁e₁ : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  have he₁v : ClassFunction.inner (cY.extension η₁) v = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm v (cY.extension η₁), hgood]
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- orthogonality `⟨X, η^{τ₁}⟩ = 0`.
    intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee
      rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (fun h => hee h.symm)]; ring
  · -- norm `⟨X, X⟩ = 1`.
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    rw [hvv, hgood, he₁v, he₁e₁, star_natCast]; ring
  · -- `X ∈ ℤ[Irr G]`.
    have hdeg : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
    have hsuppX : (χ₁ - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁)
        (hyp.Yset_subset_S hη₁) hdeg
    have hsrcZ : χ₁ - a • η₁ ∈ ZIrr (↥L) :=
      sub_mem (hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁).mem_ZIrr
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr a)
    have hvZ : v ∈ ZIrr G := by
      rw [hv]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hyp.hconj hsuppX hsrcZ
    have he₁Z : cY.extension η₁ ∈ ZIrr G :=
      cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)
    have haZ : (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem he₁Z a
    exact add_mem hvZ haZ

open scoped Classical in
/-- **(6.8.1) step-4 good-case `X`-structure**, case (A) / c2 mirror of
`orthogonal_normOne_tau_scaledDiff_add_extension_general`.  The constancy/norm/`X`-irreducibility
inputs use their case-(A) counterparts (`inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`,
`inner_self_tau_scaledDiff_c2_caseA`, `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF`
(cert data `hK`/`hW1`/`hA`). -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- Y-image orthonormality: `⟨η^{τ₁}, η'^{τ₁}⟩ = ⟨η, η'⟩ = δ`.
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη)
      (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  -- `⟨v, η^{τ₁}⟩ = 0` for `η ≠ η₁` (constancy `⟨v, (η−η₁)^τ⟩ = a` plus `⟨v, η₁^{τ₁}⟩ = −a`).
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner v (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη hne hχ₁ ha
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁)
        = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  -- norm and the conjugate of the good-case coefficient.
  have hvv : ClassFunction.inner v v = 1 + (a : ℂ) ^ 2 :=
    hyp.inner_self_tau_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ ha
  have he₁e₁ : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  have he₁v : ClassFunction.inner (cY.extension η₁) v = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm v (cY.extension η₁), hgood]
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- orthogonality `⟨X, η^{τ₁}⟩ = 0`.
    intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee
      rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (fun h => hee h.symm)]; ring
  · -- norm `⟨X, X⟩ = 1`.
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    rw [hvv, hgood, he₁v, he₁e₁, star_natCast]; ring
  · -- `X ∈ ℤ[Irr G]`.
    have hdeg : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
    have hsuppX : (χ₁ - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁)
        (hyp.Yset_subset_S hη₁) hdeg
    have hsrcZ : χ₁ - a • η₁ ∈ ZIrr (↥L) :=
      sub_mem (hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁).mem_ZIrr
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr a)
    have hvZ : v ∈ ZIrr G := by
      rw [hv]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hyp.hconj hsuppX hsrcZ
    have he₁Z : cY.extension η₁ ∈ ZIrr G :=
      cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)
    have haZ : (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem he₁Z a
    exact add_mem hvZ haZ

/-- **(6.8.1) step-4 good-case `X`-structure** at the fixed witness `τ₁ = coherentYset`
(specialization of `orthogonal_normOne_tau_scaledDiff_add_extension_general`). -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.coherentYset.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁ ∈ ZIrr G :=
  hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general hF hyp.coherentYset hη₁ hχ₁ ha hgood

/-- **(6.8.1) step-4 good-case `X`-structure** at the fixed witness, case (A) / c2 mirror of
`orthogonal_normOne_tau_scaledDiff_add_extension_of_frobenius` (specialization of
`orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA`). -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.coherentYset.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁ ∈ ZIrr G :=
  hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA hK hW1 hA hyp.coherentYset
    hη₁ hχ₁ ha hgood

/-- **(6.8.1) `X`-difference isometry** (mmd 04.8 L176, the step-5 input).  For `η₁ ∈ Y`, an
`X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, and a second `X`-member `χ₂ ∈ X(Zc)`, `χ₂ ≠ χ₁`, of
the **same degree** `χ₂(1) = χ₁(1)`:
`⟨(χ₁−aη₁)^τ, (χ₂−χ₁)^τ⟩ = −1`.

By the Dade isometry on the supported pair `{χ₁−aη₁, χ₂−χ₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; `χ₂−χ₁` supported by
`sMember_diffSupport_of_charValue_eq` at the common degree), the inner product equals the source
`⟨χ₁−aη₁, χ₂−χ₁⟩`, which expands by `X`-orthonormality (`⟨χ₁,χ₂⟩=0`, `⟨χ₁,χ₁⟩=1`) and `X ⊥ Y`
(`⟨η₁,χ₂⟩=⟨η₁,χ₁⟩=0`) to `(0 − a·0) − (1 − a·0) = −1`.  Combined with `himg_ortho`
(`η₁^{τ₁} ⊥ X^{τ₂}`) and the `X`-coherence `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}`, this gives
`⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1` for the step-5 element `X` (good case), pinning `X = χ₁^{τ₂}`. -/
theorem inner_tau_scaledDiff_tau_Xset_diff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₂ - χ₁)) = -1 := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported inputs.
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX2 : (χ₂ - χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₂ - χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX2)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- source orthogonality `⟨χ₁ − a•η₁, χ₂ − χ₁⟩ = −1`.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXon χ₁ χ₂ hχ₁ hχ₂, hXon χ₁ χ₁ hχ₁ hχ₁, hYXz χ₂ hχ₂, hYXz χ₁ hχ₁,
    if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) `X`-difference isometry**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius`.  `X`-irreducibility comes from the certain-type
input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Xset_diff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₂ - χ₁)) = -1 := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported inputs.
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX2 : (χ₂ - χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₂ - χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX2)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- source orthogonality `⟨χ₁ − a•η₁, χ₂ − χ₁⟩ = −1`.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXon χ₁ χ₂ hχ₁ hχ₂, hXon χ₁ χ₁ hχ₁ hχ₁, hYXz χ₂ hχ₂, hYXz χ₁ hχ₁,
    if_neg (Ne.symm hne), if_pos rfl]
  ring

open scoped Classical in
/-- **(6.8.1) step-5 inner-product relation** (mmd 04.8 L176).  For the good-case element
`X := (χ₁−aη₁)^τ + a·η₁^{τ₁}`, the `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, and a second
equal-degree `X`-member `χ₂ ∈ X(Zc)`, `χ₂ ≠ χ₁`:
`⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1`.

`X = (χ₁−aη₁)^τ + a·η₁^{τ₁}` and `η₁^{τ₁} ⊥ X^{τ₂}` (himg_ortho
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`) give
`⟨X, χ_j^{τ₂}⟩ = ⟨(χ₁−aη₁)^τ, χ_j^{τ₂}⟩`; the `X`-coherence
`(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (`extends_on_supported` on the supported equal-degree difference)
and the isometry value `⟨(χ₁−aη₁)^τ, (χ₂−χ₁)^τ⟩ = −1`
(`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius`) close it.  Together with `‖X‖² = 1` and Bessel
over the orthonormal `{χ₁^{τ₂}, χ₂^{τ₂}}`, this pins `X = χ₁^{τ₂}` (or `−χ₂^{τ₂}`, the `n = 2`
edge). -/
theorem inner_extension_Xset_sub_eq_neg_one_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁)
      = -1 := by
  classical
  set hXc := cX with hXc_def
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- `⟨X, χ_j^{τ₂}⟩ = ⟨v, χ_j^{τ₂}⟩` (himg_ortho `η₁^{τ₁} ⊥ X^{τ₂}`).
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (hXc.extension χ)
        = ClassFunction.inner v (hXc.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hχ hη₁
    rw [← hXc_def] at h
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  -- `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (X-coherence `extends_on_supported`).
  have hsuppX2 : (χ₂ - χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hXcoh : hyp.tau (χ₂ - χ₁) = hXc.extension χ₂ - hXc.extension χ₁ := by
    have h := hXc.extends_on_supported (χ₂ - χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₂) (Submodule.subset_span hχ₁), hsuppX2⟩
    rw [map_sub] at h
    exact h.symm
  -- isometry value `⟨v, (χ₂−χ₁)^τ⟩ = −1`.
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_diff_of_frobenius hF hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [hXcoh, ClassFunction.inner_sub_right] at hiso
  rw [hXv χ₂ hχ₂, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) step-5 inner-product relation**, case (A) / c2 mirror of
`inner_extension_Xset_sub_eq_neg_one_general`.  The himg_ortho/isometry inputs use their case-(A)
counterparts (`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`,
`inner_tau_scaledDiff_tau_Xset_diff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_sub_eq_neg_one_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁)
      = -1 := by
  classical
  set hXc := cX with hXc_def
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- `⟨X, χ_j^{τ₂}⟩ = ⟨v, χ_j^{τ₂}⟩` (himg_ortho `η₁^{τ₁} ⊥ X^{τ₂}`).
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (hXc.extension χ)
        = ClassFunction.inner v (hXc.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
      hK hW1 hA cX cY hχ hη₁
    rw [← hXc_def] at h
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  -- `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (X-coherence `extends_on_supported`).
  have hsuppX2 : (χ₂ - χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hXcoh : hyp.tau (χ₂ - χ₁) = hXc.extension χ₂ - hXc.extension χ₁ := by
    have h := hXc.extends_on_supported (χ₂ - χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₂) (Submodule.subset_span hχ₁), hsuppX2⟩
    rw [map_sub] at h
    exact h.symm
  -- isometry value `⟨v, (χ₂−χ₁)^τ⟩ = −1`.
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_diff_c2_caseA hK hW1 hA hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [hXcoh, ClassFunction.inner_sub_right] at hiso
  rw [hXv χ₂ hχ₂, hXv χ₁ hχ₁]
  exact hiso

/-- **(6.8.1) step-5 relation** at the fixed witnesses (specialization of
`inner_extension_Xset_sub_eq_neg_one_general`). -/
theorem inner_extension_Xset_sub_eq_neg_one_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁)
      = -1 :=
  hyp.inner_extension_Xset_sub_eq_neg_one_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2

/-- **(6.8.1) step-5 relation** at the fixed witnesses, case (A) / c2 mirror of
`inner_extension_Xset_sub_eq_neg_one_of_frobenius` (the `X`-coherence is
`Xset_centralCommutator_isCoherent_of_c2_caseA`; cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_sub_eq_neg_one_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension
            χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁)
        ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension
            χ₁)
      = -1 :=
  hyp.inner_extension_Xset_sub_eq_neg_one_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2

open scoped Classical in
/-- **(6.8.1) step-5 dichotomy `X = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`** (mmd 04.8 L176).  In the good case
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = −a`, the element `X := (χ₁−aη₁)^τ + a·η₁^{τ₁}` (norm `1`, `⊥ Y^{τ₁}`)
equals either `χ₁^{τ₂}` or `−χ₂^{τ₂}` for the second equal-degree anchor `χ₂`.

From the step-5 relation `⟨X,χ₂^{τ₂}⟩ − ⟨X,χ₁^{τ₂}⟩ = −1` (`inner_extension_Xset_sub_eq_neg_one`)
and Bessel `c₁² + c₂² ≤ ‖X‖² = 1` (`sum_sq_le_inner_self_re` over the orthonormal
`{χ₁^{τ₂},χ₂^{τ₂}}`, `c_j = ⟨X,χ_j^{τ₂}⟩ ∈ ℤ`), the integers satisfy `c₂−c₁=−1`, `c₁²+c₂²≤1`,
forcing `(1,0)` or `(0,−1)`; `⟨X,χ₁^{τ₂}⟩=1` (resp. `⟨X,−χ₂^{τ₂}⟩=1`) with both norm `1` gives
`X=χ₁^{τ₂}` (resp. `X=−χ₂^{τ₂}`) by positive-definiteness.  The `n=2` edge `X=−χ₂^{τ₂}` is
resolved by relabelling (deferred); for `n≥3` a third anchor pins `X=χ₁^{τ₂}`. -/
theorem extension_eq_or_eq_neg_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = cX.extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = -cX.extension χ₂
      := by
  classical
  set hXc := cX with hXc_def
  set X := hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ with hX_def
  -- good-case structure: `‖X‖² = 1`, `X ∈ ZIrr` (fold the unfolded `X` from the good-case lemma).
  obtain ⟨_, hXnorm, hXZ⟩ := hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general
    hF cY hη₁ hχ₁ ha hgood
  rw [← hX_def] at hXnorm hXZ
  -- `X`-image orthonormality, ZIrr membership, distinctness.
  have hX1Z : hXc.extension χ₁ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₁ (Submodule.subset_span hχ₁)
  have hX2Z : hXc.extension χ₂ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₂ (Submodule.subset_span hχ₂)
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hX1norm : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₁) = 1 := by
    rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have hX2norm : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₂) = 1 := by
    rw [hXon χ₂ χ₂ hχ₂ hχ₂, if_pos rfl]
  have hX12 : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₂) = 0 := by
    rw [hXon χ₁ χ₂ hχ₁ hχ₂, if_neg (Ne.symm hne)]
  have hX1ne2 : hXc.extension χ₁ ≠ hXc.extension χ₂ := by
    intro heq; rw [heq, hX2norm] at hX12; exact one_ne_zero hX12
  -- integer coefficients `c₁ = ⟨X,χ₁^{τ₂}⟩`, `c₂ = ⟨X,χ₂^{τ₂}⟩`.
  obtain ⟨c₁, hc₁⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX1Z
  obtain ⟨c₂, hc₂⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX2Z
  -- the step-5 relation `c₂ − c₁ = −1`.
  have hrel := hyp.inner_extension_Xset_sub_eq_neg_one_general hF cX cY
    hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [← hXc_def, ← hX_def, hc₁, hc₂] at hrel
  have hrelℤ : c₂ - c₁ = -1 := by exact_mod_cast hrel
  -- Bessel `c₁² + c₂² ≤ ‖X‖² = 1` via positive-definiteness of the projection residual
  -- `X − c₁·χ₁^{τ₂} − c₂·χ₂^{τ₂}`.
  have hAX : ClassFunction.inner (hXc.extension χ₁) X = (c₁ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₁), hc₁, star_intCast]
  have hBX : ClassFunction.inner (hXc.extension χ₂) X = (c₂ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₂), hc₂, star_intCast]
  have hX21 : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₁) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ₁) (hXc.extension χ₂), hX12,
      star_zero]
  have hww : ClassFunction.inner
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      = ((1 - (c₁ ^ 2 + c₂ ^ 2) : ℤ) : ℂ) := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hXnorm, hc₁, hc₂, hAX, hBX, hX1norm, hX2norm, hX12, hX21, star_intCast]
    push_cast; ring
  have hbℤ : c₁ ^ 2 + c₂ ^ 2 ≤ 1 := by
    have hnn := OddOrder.RepresentationTheory.inner_self_re_nonneg
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
    rw [hww, Complex.intCast_re] at hnn
    have hb : (0 : ℤ) ≤ 1 - (c₁ ^ 2 + c₂ ^ 2) := by exact_mod_cast hnn
    linarith
  -- positive-definiteness: `⟨w₁,w₁⟩=⟨w₂,w₂⟩=⟨w₁,w₂⟩=1 ⟹ w₁=w₂`.
  have heq : ∀ w₁ w₂ : ClassFunction G ℂ, ClassFunction.inner w₁ w₁ = 1 →
      ClassFunction.inner w₂ w₂ = 1 → ClassFunction.inner w₁ w₂ = 1 → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ h₁₂
    have hsub : ClassFunction.inner (w₁ - w₂) (w₁ - w₂) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h₁, h₂, h₁₂,
        OddOrder.RepresentationTheory.inner_conj_symm w₁ w₂, h₁₂, star_one]
      ring
    have hz : w₁ - w₂ = 0 := OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
      (by rw [hsub, Complex.zero_re])
    exact sub_eq_zero.mp hz
  -- the integer dichotomy `(c₁,c₂) = (1,0) ∨ (0,−1)` from `c₂ = c₁−1` and `c₁²+c₂² ≤ 1`.
  have hc2eq : c₂ = c₁ - 1 := by omega
  rw [hc2eq] at hbℤ
  obtain ⟨hb0, hb1⟩ : 0 ≤ c₁ ∧ c₁ ≤ 1 := by
    constructor <;> nlinarith [hbℤ, sq_nonneg c₁, sq_nonneg (c₁ - 1)]
  interval_cases c₁
  · -- `c₁ = 0`, `c₂ = −1` ⟹ `X = −χ₂^{τ₂}`.
    right
    have hc₂m : c₂ = -1 := by omega
    subst hc₂m
    refine heq X (-hXc.extension χ₂) hXnorm ?_ ?_
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hX2norm]; ring
    · rw [ClassFunction.inner_neg_right, hc₂]; norm_num
  · -- `c₁ = 1`, `c₂ = 0` ⟹ `X = χ₁^{τ₂}`.
    left
    refine heq X (hXc.extension χ₁) hXnorm hX1norm ?_
    rw [hc₁]; norm_num

open scoped Classical in
/-- **(6.8.1) step-5 dichotomy `X = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`**, case (A) / c2 mirror of
`extension_eq_or_eq_neg_general`.  The good-case structure/relation/`X`-irreducibility inputs use
their case-(A) counterparts (`orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA`,
`inner_extension_Xset_sub_eq_neg_one_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem extension_eq_or_eq_neg_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = cX.extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = -cX.extension χ₂
      := by
  classical
  set hXc := cX with hXc_def
  set X := hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ with hX_def
  -- good-case structure: `‖X‖² = 1`, `X ∈ ZIrr` (fold the unfolded `X` from the good-case lemma).
  obtain ⟨_, hXnorm, hXZ⟩ := hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA
    hK hW1 hA cY hη₁ hχ₁ ha hgood
  rw [← hX_def] at hXnorm hXZ
  -- `X`-image orthonormality, ZIrr membership, distinctness.
  have hX1Z : hXc.extension χ₁ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₁ (Submodule.subset_span hχ₁)
  have hX2Z : hXc.extension χ₂ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₂ (Submodule.subset_span hχ₂)
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter
          ↥L)
    simpa using h
  have hX1norm : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₁) = 1 := by
    rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have hX2norm : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₂) = 1 := by
    rw [hXon χ₂ χ₂ hχ₂ hχ₂, if_pos rfl]
  have hX12 : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₂) = 0 := by
    rw [hXon χ₁ χ₂ hχ₁ hχ₂, if_neg (Ne.symm hne)]
  have hX1ne2 : hXc.extension χ₁ ≠ hXc.extension χ₂ := by
    intro heq; rw [heq, hX2norm] at hX12; exact one_ne_zero hX12
  -- integer coefficients `c₁ = ⟨X,χ₁^{τ₂}⟩`, `c₂ = ⟨X,χ₂^{τ₂}⟩`.
  obtain ⟨c₁, hc₁⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX1Z
  obtain ⟨c₂, hc₂⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX2Z
  -- the step-5 relation `c₂ − c₁ = −1`.
  have hrel := hyp.inner_extension_Xset_sub_eq_neg_one_general_c2_caseA hK hW1 hA cX cY
    hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [← hXc_def, ← hX_def, hc₁, hc₂] at hrel
  have hrelℤ : c₂ - c₁ = -1 := by exact_mod_cast hrel
  -- Bessel `c₁² + c₂² ≤ ‖X‖² = 1` via positive-definiteness of the projection residual
  -- `X − c₁·χ₁^{τ₂} − c₂·χ₂^{τ₂}`.
  have hAX : ClassFunction.inner (hXc.extension χ₁) X = (c₁ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₁), hc₁, star_intCast]
  have hBX : ClassFunction.inner (hXc.extension χ₂) X = (c₂ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₂), hc₂, star_intCast]
  have hX21 : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₁) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ₁) (hXc.extension χ₂), hX12,
      star_zero]
  have hww : ClassFunction.inner
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      = ((1 - (c₁ ^ 2 + c₂ ^ 2) : ℤ) : ℂ) := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hXnorm, hc₁, hc₂, hAX, hBX, hX1norm, hX2norm, hX12, hX21, star_intCast]
    push_cast; ring
  have hbℤ : c₁ ^ 2 + c₂ ^ 2 ≤ 1 := by
    have hnn := OddOrder.RepresentationTheory.inner_self_re_nonneg
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
    rw [hww, Complex.intCast_re] at hnn
    have hb : (0 : ℤ) ≤ 1 - (c₁ ^ 2 + c₂ ^ 2) := by exact_mod_cast hnn
    linarith
  -- positive-definiteness: `⟨w₁,w₁⟩=⟨w₂,w₂⟩=⟨w₁,w₂⟩=1 ⟹ w₁=w₂`.
  have heq : ∀ w₁ w₂ : ClassFunction G ℂ, ClassFunction.inner w₁ w₁ = 1 →
      ClassFunction.inner w₂ w₂ = 1 → ClassFunction.inner w₁ w₂ = 1 → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ h₁₂
    have hsub : ClassFunction.inner (w₁ - w₂) (w₁ - w₂) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h₁, h₂, h₁₂,
        OddOrder.RepresentationTheory.inner_conj_symm w₁ w₂, h₁₂, star_one]
      ring
    have hz : w₁ - w₂ = 0 := OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
      (by rw [hsub, Complex.zero_re])
    exact sub_eq_zero.mp hz
  -- the integer dichotomy `(c₁,c₂) = (1,0) ∨ (0,−1)` from `c₂ = c₁−1` and `c₁²+c₂² ≤ 1`.
  have hc2eq : c₂ = c₁ - 1 := by omega
  rw [hc2eq] at hbℤ
  obtain ⟨hb0, hb1⟩ : 0 ≤ c₁ ∧ c₁ ≤ 1 := by
    constructor <;> nlinarith [hbℤ, sq_nonneg c₁, sq_nonneg (c₁ - 1)]
  interval_cases c₁
  · -- `c₁ = 0`, `c₂ = −1` ⟹ `X = −χ₂^{τ₂}`.
    right
    have hc₂m : c₂ = -1 := by omega
    subst hc₂m
    refine heq X (-hXc.extension χ₂) hXnorm ?_ ?_
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hX2norm]; ring
    · rw [ClassFunction.inner_neg_right, hc₂]; norm_num
  · -- `c₁ = 1`, `c₂ = 0` ⟹ `X = χ₁^{τ₂}`.
    left
    refine heq X (hXc.extension χ₁) hXnorm hX1norm ?_
    rw [hc₁]; norm_num

end SibleyDadeHypothesis
end OddOrder.Peterfalvi.S08
