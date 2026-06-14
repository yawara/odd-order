/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBCoherence
import OddOrder.Peterfalvi.S06_CertainTypeCoherence

/-!
# Peterfalvi §8: Case (B) coherence — the `τ₂` assembly

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37, the **(6.8.2)** branch of the (6.8) coherence capstone.

This continues `S08_CaseBCoherence` (which holds the §3 helpers, (6.8.2.1), and the (6.8.2.2)
decomposition + uniform Y-coherence witness `exists_Ycoherence_hgood_caseB`).  Here we assemble the
decomposition into the case-(B) `X ∪ Y` coherence:

* the **general** good-case `X`-structure (consuming an arbitrary `Y`-coherence witness `cY`, as
  produced by `exists_Ycoherence_hgood_caseB`),
* the crux `α^τ = X − |H:Z|·cY η₁`,
* **(6.8.2.3)** the `X`-side `(χ − a η₁)^τ` decomposition ([Is] Lemma 2.27),
* the final `τ₂` assembly.

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` ("session 40 cont.⁹+").
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.2) good-case `X`-structure, general `Y`-coherence witness.**  The `cY`-parametrized
version of `orthogonal_tau_indW2_add_extension_caseB`: for *any* `Y`-coherence witness `cY` (e.g. the
swapped witness from `exists_Ycoherence_hgood_caseB` in the `|Y| = 2` edge), the good value
`⟨α^τ, cY.extension η₁⟩ = −|H:Z|` makes `X := α^τ + |H:Z|·cY.extension η₁` orthogonal to the whole
family `{cY.extension η}` and lie in `ℤ[Irr G]`, giving `α^τ = X − |H:Z|·cY.extension η₁`.

The agreement `cY.extension η − cY.extension η₁ = (η − η₁)^τ` is `cY.extends_on_supported` + `map_sub`
(inlined, since `cY` need not be `coherentYset`). -/
theorem SibleyDadeHypothesis.orthogonal_tau_indW2_add_extension_general_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) (hW2comm : W2 ≤ ⁅H, H⁆)
    [Invertible (Nat.card ↥W2 : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
      = -((W2.subgroupOf H).index : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη) (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm φ hη₁ hη hne
      ((W2.subgroupOf H).index : ℂ) h1
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁) = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  have he₁e₁ : ClassFunction.inner (cY.extension η₁) (cY.extension η₁) = 1 := by
    rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  refine ⟨?_, ?_⟩
  · intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee; rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (Ne.symm hee)]; ring
  · have hsuppX : (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁).support
        ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ _ h1
    have hsrcZ : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁ ∈ ZIrr (↥L) := by
      rw [Nat.cast_smul_eq_nsmul]
      exact sub_mem (ClassFunction.induce_mem_ZIrr W2 (IsIrreducibleCharacter.mem_ZIrr φ.2))
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr (W2.subgroupOf H).index)
    have hvZ : hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hyp.hconj hsuppX hsrcZ
    have he₁Z : ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) (W2.subgroupOf H).index
    exact add_mem hvZ he₁Z

/-- **Peterfalvi (6.8.2.2): the `X − |H:Z|·Y` decomposition.**  For `α = Ind^L_{W₂}φ − |H:Z|·η₁`
(`φ` nontrivial linear), there is a `Y`-coherence witness `cY` and an `X ∈ ℤ[Irr G]` orthogonal to the
whole family `{cY.extension η : η ∈ Y}` with `α^τ = X − |H:Z|·cY.extension η₁`.

Combines the uniform good-value witness `exists_Ycoherence_hgood_caseB` (handling the `|Y| = 2`
relabel) with the general `X`-structure `orthogonal_tau_indW2_add_extension_general_caseB`.  This is
the case-(B) decomposition consumed by the τ₂ assembly (Peterfalvi (6.8.2)); `Y := cY.extension η₁`
is the (6.8.2.2) `Y` (`= η₁^{τ₁}`, or `−η₂^{τ₁}` in the edge).  `hc2`/`hFPF` are the deferred
`W₁`-FPF-on-`H/W₂` inputs. -/
theorem SibleyDadeHypothesis.exists_decomposition_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2) :
    ∃ (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
        (X : ClassFunction G ℂ),
      (∀ η ∈ hyp.Yset, ClassFunction.inner X (cY.extension η) = 0)
        ∧ X ∈ ZIrr G
        ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          = X - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  obtain ⟨cY, hgood⟩ :=
    hyp.exists_Ycoherence_hgood_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hc2 hFPF
  obtain ⟨horth, hXZ⟩ :=
    hyp.orthogonal_tau_indW2_add_extension_general_caseB hW2H hW2comm cY hη₁ φ hφ1 h1 hgood
  refine ⟨cY, hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)
      + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁, horth, hXZ, ?_⟩
  abel

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] in
/-- **(6.8) case-(B) structural discharge: `W₂ ⊆ Z(↥L)`.**  In the (4.2)/certain-type structure
`L = K ⋊ W₁` (with `W₂ ≤ K`), if `W₂` *centralizes `K`* (the math-(B) condition `W₂ ⊆ Z(K) = Z(H)`,
the `Z(H) ∩ W₂ = W₂` branch of `eq_bot_or_eq_of_le_of_card_prime`), then `W₂` is central in `↥L`.
Indeed `W₂` also centralizes `W₁` (`Hypothesis.commute_of_mem_W1_of_mem_W2`), and every `g ∈ ↥L`
factors as `g = k·w₁` (`K ⋊ W₁` complement), so `g·w = k·w₁·w = k·w·w₁ = w·k·w₁ = w·g` for `w ∈ W₂`.

This discharges the `W₂ ≤ Z(↥L)` hypothesis (`hW2cen`) of the (6.8.2.2) case-(B) lemmas, supplied at
capstone wiring from the `cases` `Hypothesis46` and the math-(B) sub-case. -/
theorem certainType_W2_le_center (h : OddOrder.Peterfalvi.S06.Hypothesis ↥L)
    (hW2cenK : h.W2 ≤ Subgroup.centralizer (↑h.K : Set ↥L)) :
    h.W2 ≤ Subgroup.center ↥L := by
  intro w hw
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨k, w₁⟩, hkw0⟩ := h.isComplement.surjective g
  have hkw : (k : ↥L) * (w₁ : ↥L) = g := hkw0
  have hck : (k : ↥L) * w = w * (k : ↥L) :=
    Subgroup.mem_centralizer_iff.mp (hW2cenK hw) (k : ↥L) k.2
  have hcw1 : (w₁ : ↥L) * w = w * (w₁ : ↥L) :=
    (h.commute_of_mem_W1_of_mem_W2 w₁.2 hw).eq
  calc g * w
      = (k : ↥L) * (w₁ : ↥L) * w := by rw [← hkw]
    _ = (k : ↥L) * (w * (w₁ : ↥L)) := by rw [mul_assoc, hcw1]
    _ = w * ((k : ↥L) * (w₁ : ↥L)) := by rw [← mul_assoc, hck, mul_assoc]
    _ = w * g := by rw [hkw]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **(6.8) case-(B) structural discharge: the FPF index bounds `hc2`/`hFPF`.**

In the (4.2)/certain-type structure `L = K ⋊ W₁` with `C_K(x) = W₂` (`x ∈ W₁^#`) and the math-(B)
condition `W₂ ⊆ Z(K)` (so `W₂` is central, `certainType_W2_le_center`), the quotient `↥L / W₂` is a
**Frobenius group** with kernel `K/W₂` and complement `W₁W₂/W₂`: the centralizer-meet-kernel
condition lifts from `C_K(x) = W₂` via coprime action
(`fixedPoint_lift_of_generator_quotient_fixed`), since a quotient-fixed `c ∈ K` lies in
`C_L(x) ∩ K = W₂`, so its image is `1`.  Isaacs Lemma 6.1
(`IsFrobeniusGroup.card_kernel_modEq_one`) then gives `|K : W₂| ≡ 1 (mod |W₁|)`, whence
`|W₁| < |K : W₂|` (using `W₂ ⊊ K`, i.e. `¬ K ≤ W₂`).

This discharges the deferred FPF inputs of `exists_decomposition_caseB` (with `H := K`, `W2 := W₂`):
* `hc2 : 2 ≤ |K : W₂|` (from `W₂ ⊊ K`),
* `hFPF : |L : W₂| < |K : W₂|²` (from `|L : W₂| = |K : W₂| · |W₁|` and `|W₁| < |K : W₂|`). -/
theorem certainType_index_bounds (h : OddOrder.Peterfalvi.S06.Hypothesis ↥L)
    (hW2cenK : h.W2 ≤ Subgroup.centralizer (↑h.K : Set ↥L))
    (hKW2 : ¬ h.K ≤ h.W2) :
    2 ≤ (h.W2.subgroupOf h.K).index ∧
    (h.W2.index : ℤ) < ((h.W2.subgroupOf h.K).index : ℤ) ^ 2 := by
  classical
  haveI : Finite ↥L := inferInstance
  haveI : Finite ↥h.K := inferInstance
  -- `W₂` is central, hence normal in `↥L`.
  have hW2cen : h.W2 ≤ Subgroup.center ↥L := certainType_W2_le_center h hW2cenK
  haveI hW2N : h.W2.Normal := ⟨fun w hw g => by
    have hc : g * w = w * g := Subgroup.mem_center_iff.mp (hW2cen hw) g
    have hgw : g * w * g⁻¹ = w := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [hgw]; exact hw⟩
  haveI hKN : h.K.Normal := h.K_normal
  set Nk := h.K.map (QuotientGroup.mk' h.W2) with hNk
  set Aw := h.W1.map (QuotientGroup.mk' h.W2) with hAw
  -- Frobenius group structure on the quotient `↥L / W₂`.
  have hC : Subgroup.IsComplement' Nk Aw :=
    OddOrder.BG.Ch1.S03.quotient_complement_of_normal_le_kernel h.isComplement h.W2_le_K
  have hNk_ne : Nk ≠ ⊥ :=
    OddOrder.BG.Ch1.S03.quotient_kernel_map_ne_bot_of_not_le hKW2
  have hAw_ne : Aw ≠ ⊥ :=
    OddOrder.BG.Ch1.S03.quotient_complement_map_ne_bot_of_le_kernel h.isComplement h.W2_le_K
      h.W1_nontrivial
  haveI hNkN : Nk.Normal := hKN.map (QuotientGroup.mk' h.W2) (QuotientGroup.mk'_surjective h.W2)
  have hcentral : ∀ x ∈ Aw, x ≠ 1 →
      Subgroup.centralizer ({x} : Set (↥L ⧸ h.W2)) ⊓ Nk = ⊥ := by
    intro qx hqxA hqx_ne
    rw [eq_bot_iff]
    intro qz hqz
    rw [Subgroup.mem_inf] at hqz
    obtain ⟨hqz_cen, hqz_Nk⟩ := hqz
    obtain ⟨x, hxW1, hxq⟩ := hqxA
    have hx_ne : x ≠ 1 := by
      rintro rfl; exact hqx_ne (by rw [← hxq]; simp)
    obtain ⟨y, hyK, hyq⟩ := hqz_Nk
    -- the centralizer condition lifts to `mk(x y x⁻¹) = mk y`.
    have hgen : (QuotientGroup.mk' h.W2) (x * y * x⁻¹) = (QuotientGroup.mk' h.W2) y := by
      have hcomm : (QuotientGroup.mk' h.W2) x * (QuotientGroup.mk' h.W2) y
          = (QuotientGroup.mk' h.W2) y * (QuotientGroup.mk' h.W2) x := by
        have hc := (Subgroup.mem_centralizer_singleton_iff.mp hqz_cen).symm
        rw [← hxq, ← hyq] at hc; exact hc
      rw [map_mul, map_mul, map_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    -- coprime-action fixed-point lift (`zpowers x` is cyclic ⇒ solvable; `(|⟨x⟩|, |K|) = 1`).
    have hCopx : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥h.K) := by
      have hle : Subgroup.zpowers x ≤ h.W1 := Subgroup.zpowers_le.mpr hxW1
      exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hle) h.card_coprime.symm
    have hSolv : IsSolvable ↥(Subgroup.zpowers x) ∨ IsSolvable ↥h.K :=
      Or.inl (isSolvable_of_comm fun a b => by
        obtain ⟨m, hm⟩ := a.2
        obtain ⟨n, hn⟩ := b.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul, ← hm, ← hn]
        exact (((Commute.refl x).zpow_zpow m n)))
    obtain ⟨c, hcK, hcq, hcfix⟩ :=
      OddOrder.BG.Ch1.S03.fixedPoint_lift_of_generator_quotient_fixed h.W2_le_K hCopx hSolv hyK hgen
    -- `c` centralizes `x` and lies in `K`, hence `c ∈ C_L(x) ∩ K = W₂`, so `mk c = 1`.
    have hc_cen : c ∈ Subgroup.centralizer ({x} : Set ↥L) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hxc : x * c = c * x := by
        have h2 := congrArg (· * x) hcfix
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2
      exact hxc.symm
    have hc_W2 : c ∈ h.W2 := by
      rw [← h.centralizer_W2 x hxW1 hx_ne]; exact Subgroup.mem_inf.mpr ⟨hc_cen, hcK⟩
    have hcq1 : (QuotientGroup.mk' h.W2) c = 1 := (QuotientGroup.eq_one_iff c).mpr hc_W2
    rw [Subgroup.mem_bot, ← hyq, ← hcq, hcq1]
  have hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L ⧸ h.W2) Nk Aw :=
    (OddOrder.BG.Ch1.S03.isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot
      hNkN hC hNk_ne hAw_ne).mpr hcentral
  have hmod : Nat.card ↥Nk ≡ 1 [MOD Nat.card ↥Aw] := hFrob.card_kernel_modEq_one
  -- translate the kernel/complement orders to `|K : W₂|` and `|W₁|`.
  have hcardNk : Nat.card ↥Nk = (h.W2.subgroupOf h.K).index := by
    have hrange : (QuotientGroup.mk' h.W2 |>.comp h.K.subtype).range = Nk := by
      ext z
      simp only [MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype, hNk,
        Subgroup.mem_map]
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨k, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
    have hker : (QuotientGroup.mk' h.W2 |>.comp h.K.subtype).ker = h.W2.subgroupOf h.K := by
      ext k
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← hrange,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (QuotientGroup.mk' h.W2 |>.comp h.K.subtype)).toEquiv, hker]
    rfl
  have hcardAw : Nat.card ↥Aw = Nat.card ↥h.W1 := by
    have hrange : (QuotientGroup.mk' h.W2 |>.comp h.W1.subtype).range = Aw := by
      ext z
      simp only [MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype, hAw,
        Subgroup.mem_map]
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨w, w.2, rfl⟩
      · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
    have hker : (QuotientGroup.mk' h.W2 |>.comp h.W1.subtype).ker = (⊥ : Subgroup ↥h.W1) := by
      ext w
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_bot]
      constructor
      · intro hwW2
        exact Subtype.ext (by simpa using Subgroup.disjoint_def.mp h.W_disjoint w.2 hwW2)
      · rintro rfl; simp
    rw [← hrange,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (QuotientGroup.mk' h.W2 |>.comp h.W1.subtype)).toEquiv, hker]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  rw [hcardNk, hcardAw] at hmod
  -- `|W₁| ∣ |K : W₂| − 1`, and `|K : W₂| ≥ 2`, so `|W₁| < |K : W₂|`.
  have hd2 : 2 ≤ (h.W2.subgroupOf h.K).index := by
    rcases Nat.lt_or_ge (h.W2.subgroupOf h.K).index 2 with hlt | hge
    · exfalso
      have hne0 : (h.W2.subgroupOf h.K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 : (h.W2.subgroupOf h.K).index = 1 := by omega
      exact hKW2 (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1))
    · exact hge
  have hdvd : Nat.card ↥h.W1 ∣ (h.W2.subgroupOf h.K).index - 1 :=
    (Nat.modEq_iff_dvd' (by omega : (1 : ℕ) ≤ (h.W2.subgroupOf h.K).index)).mp hmod.symm
  have hw1lt : Nat.card ↥h.W1 < (h.W2.subgroupOf h.K).index := by
    have := Nat.le_of_dvd (by omega) hdvd; omega
  refine ⟨hd2, ?_⟩
  -- `|L : W₂| = |K : W₂| · |W₁|`, then `|K : W₂| · |W₁| < |K : W₂|²`.
  have hindex : h.W2.index = (h.W2.subgroupOf h.K).index * Nat.card ↥h.W1 := by
    have h1 : h.W2.relIndex h.K * h.K.index = h.W2.index :=
      Subgroup.relIndex_mul_index h.W2_le_K
    have h3 : h.K.index = Nat.card ↥h.W1 := h.isComplement.symm.index_eq_card
    rw [← h1, h3]; rfl
  rw [hindex]
  have hpos : (0 : ℤ) < ((h.W2.subgroupOf h.K).index : ℤ) := by
    exact_mod_cast (by omega : 0 < (h.W2.subgroupOf h.K).index)
  have hlt : (Nat.card ↥h.W1 : ℤ) < ((h.W2.subgroupOf h.K).index : ℤ) := by exact_mod_cast hw1lt
  push_cast
  nlinarith [hpos, hlt]

/-- **Norm of a character induced from a central subgroup** (a (6.8.2.3) ingredient).  If `N` is a
central subgroup of a finite group `M` and `φ ∈ Irr N` (necessarily linear), then
`‖Ind^M_N φ‖² = |M : N|`.  Indeed `N ⊴ M` (central), conjugation acts trivially on `N`, so the Mackey
restriction `|N|·Res_N(Ind^M_N φ) = ∑_{x∈M} φ^{x⁻¹} = |M|·φ` collapses; Frobenius reciprocity
`⟨Ind φ, Ind φ⟩ = ⟨φ, Res(Ind φ)⟩` then gives `|N|·‖Ind φ‖² = |M|`, i.e. `‖Ind φ‖² = |M:N|`.

This is the `∑ aᵢ² = |H : Z|` step of Peterfalvi (6.8.2.3) (`Z = W₂ ⊆ Z(H)`, applied with `M = ↥H`,
`N = W₂.subgroupOf H`): the squared multiplicities of `Ind^H_Z φ` sum to `‖Ind^H_Z φ‖² = |H : Z|`. -/
theorem inner_induce_self_eq_index_of_le_center
    {M : Type*} [Group M] [Fintype M] [Invertible (Nat.card M : ℂ)]
    {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (hN : N ≤ Subgroup.center M)
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) :
    ClassFunction.inner (ClassFunction.induce N φ) (ClassFunction.induce N φ)
      = (N.index : ℂ) := by
  classical
  haveI hNnorm : N.Normal := by
    constructor
    intro n hn g
    have hc : g * n = n * g := (Subgroup.mem_center_iff.mp (hN hn)) g
    have : g * n * g⁻¹ = n := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hn
  -- conjugation acts trivially on the central `N`.
  have hconjtriv : ∀ x : M, ClassFunction.conjBy x⁻¹ φ = φ := by
    intro x
    ext h
    rw [ClassFunction.conjBy_apply]
    have hheq : x⁻¹ * (h : M) * (x⁻¹)⁻¹ = (h : M) := by
      have hcomm : x⁻¹ * (h : M) = (h : M) * x⁻¹ :=
        Subgroup.mem_center_iff.mp (hN h.2) x⁻¹
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg (fun y : ↥N => φ y) (Subtype.ext hheq)
  -- Mackey: `|N|·Res(Ind φ) = ∑_x φ^{x⁻¹} = |M|·φ`.
  have hmackey : (Nat.card ↥N : ℂ) • ClassFunction.restrict N (ClassFunction.induce N φ)
      = (Nat.card M : ℂ) • φ := by
    rw [card_smul_restrict_induce]
    simp only [hconjtriv]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card]
  -- Frobenius reciprocity + the Mackey collapse give `|N|·‖Ind φ‖² = |M|`.
  have hfrob : ClassFunction.inner (ClassFunction.induce N φ) (ClassFunction.induce N φ)
      = ClassFunction.inner φ (ClassFunction.restrict N (ClassFunction.induce N φ)) :=
    ClassFunction.inner_induce_eq_inner_restrict N φ (ClassFunction.induce N φ)
  have hself : ClassFunction.inner φ φ = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨φ, hφ⟩ : IrreducibleCharacter ↥N) ⟨φ, hφ⟩
    simpa using this
  haveI : Nonempty ↥N := ⟨1⟩
  have hstep : (Nat.card ↥N : ℂ) *
      ClassFunction.inner φ (ClassFunction.restrict N (ClassFunction.induce N φ))
      = (Nat.card M : ℂ) := by
    have h := congrArg (ClassFunction.inner φ) hmackey
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast, star_natCast, hself,
      mul_one] at h
    exact h
  have hcardN : (Nat.card ↥N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardeq : (Nat.card ↥N : ℂ) * (N.index : ℂ) = (Nat.card M : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index N]
  rw [← hfrob, ← hcardeq] at hstep
  exact mul_left_cancel₀ hcardN hstep

/-- **Constituent decomposition of an induced character** (the `Ind^H_Z φ = ∑ aᵢ θᵢ` step of
Peterfalvi (6.8.2.3)).  For any class function `φ` of a subgroup `N ≤ M`, the induced character
expands in the `Irr M` basis with coefficients the Frobenius multiplicities:
`Ind^M_N φ = ∑_{θ ∈ Irr M} ⟨φ, Res_N θ⟩ • θ`.  Fourier expansion
(`classFunction_eq_sum_inner_smul`) plus Frobenius reciprocity (`inner_induce_eq_inner_restrict`)
on each coefficient.

The multiplicities `aᵢ = ⟨φ, Res_N θᵢ⟩` are the `θᵢ(1)` of (6.8.2.3) when `θᵢ` lies over the central
linear `φ` (`Res_N θᵢ = θᵢ(1)·φ` by [Is] 2.27), and vanish otherwise. -/
theorem induce_eq_sum_inner_restrict_smul {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (φ : ClassFunction ↥N ℂ) :
    ClassFunction.induce N φ
      = ∑ θ : IrreducibleCharacter M,
        ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          • (θ : ClassFunction M ℂ) := by
  conv_lhs => rw [classFunction_eq_sum_inner_smul (ClassFunction.induce N φ)]
  exact Finset.sum_congr rfl
    (fun θ _ => by rw [ClassFunction.inner_induce_eq_inner_restrict])

/-- **The class-function inner product is preserved by pullback along a group isomorphism.**  For a
`MulEquiv e : H ≃* G` and `a, b ∈ CF(G)`, `⟨a ∘ e, b ∘ e⟩_H = ⟨a, b⟩_G`: reindexing the inner sum
`∑_{h ∈ H} a(e h)·\overline{b(e h)} = ∑_{g ∈ G} a(g)·\overline{b(g)}` along the bijection `e` (and
`|H| = |G|`).  A transport tool for the (6.8.2.3) induction-transitivity seam `W₂ ≅ W₂.subgroupOf H`. -/
theorem inner_compHom_of_mulEquiv {G' H' : Type*} [Group G'] [Group H'] [Fintype G'] [Fintype H']
    [Invertible (Nat.card G' : ℂ)] [Invertible (Nat.card H' : ℂ)]
    (e : H' ≃* G') (a b : ClassFunction G' ℂ) :
    ClassFunction.inner (ClassFunction.compHom e.toMonoidHom a)
        (ClassFunction.compHom e.toMonoidHom b) = ClassFunction.inner a b := by
  have hcard : (Nat.card H' : ℂ) = (Nat.card G' : ℂ) := by rw [Nat.card_congr e.toEquiv]
  have hsum : (∑ h : H', (ClassFunction.compHom e.toMonoidHom a) h *
        star ((ClassFunction.compHom e.toMonoidHom b) h))
      = ∑ g : G', a g * star (b g) := by
    simp only [ClassFunction.compHom_apply]
    exact Equiv.sum_comp e.toEquiv (fun g => a g * star (b g))
  have hinv : ⅟(Nat.card H' : ℂ) = ⅟(Nat.card G' : ℂ) :=
    invOf_eq_right_inv (by rw [hcard, mul_invOf_self])
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum, ClassFunction.innerSum, hsum, hinv]

/-- **Induction in stages** (Peterfalvi (6.8.2.3) `Ind^H(Ind^H_Z φ) = Ind^L_Z φ`).  For nested
subgroups `K ≤ H ≤ M`, inducing a class function `ψ` of `K` to `M` in one step agrees with inducing
first to `H` (of `ψ` transported to `K.subgroupOf H`) and then to `M`:
`Ind^M_H (Ind^H_{K.subgroupOf H} (ψ ∘ e)) = Ind^M_K ψ`, where `e : K.subgroupOf H ≃* K`.

Proved by completeness (`classFunction_eq_zero_of_orthogonal`): for every `χ ∈ Irr M`, double
Frobenius reciprocity reduces `⟨LHS, χ⟩` to `⟨ψ∘e, Res_{K.subgroupOf H}(Res_H χ)⟩`, the restriction
`Res_{K.subgroupOf H}(Res_H χ) = (Res_K χ)∘e` is the same `M`-value, and `inner_compHom_of_mulEquiv`
strips the transport to give `⟨ψ, Res_K χ⟩ = ⟨Ind^M_K ψ, χ⟩` (Frobenius). -/
theorem induce_induce_subgroupOf {M : Type*} [Group M] [Fintype M] [Invertible (Nat.card M : ℂ)]
    {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (ψ : ClassFunction ↥K ℂ) :
    ClassFunction.induce H (ClassFunction.induce (K.subgroupOf H)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom ψ))
      = ClassFunction.induce K ψ := by
  set e := Subgroup.subgroupOfEquivOfLe hKH with he
  have hres : ∀ χ : IrreducibleCharacter M,
      ClassFunction.restrict (K.subgroupOf H)
          (ClassFunction.restrict H (χ : ClassFunction M ℂ))
        = ClassFunction.compHom e.toMonoidHom (ClassFunction.restrict K (χ : ClassFunction M ℂ)) := by
    intro χ; ext y
    rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, ClassFunction.compHom_apply,
      ClassFunction.restrict_apply]
    congr 1
  refine sub_eq_zero.mp (classFunction_eq_zero_of_orthogonal _ (fun χ => ?_))
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_induce_eq_inner_restrict, hres χ, inner_compHom_of_mulEquiv,
    ClassFunction.inner_induce_eq_inner_restrict, sub_self]

/-- **Induction commutes with a `ℂ`-linear combination over a `Finset`** (the binary `induce_add` /
`induce_smul` extended to `Ind_H (∑ cᵢ • fᵢ) = ∑ cᵢ • Ind_H fᵢ`). -/
theorem induce_finset_sum_smul {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    [Invertible (Nat.card H : ℂ)] {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → ClassFunction ↥H ℂ) :
    ClassFunction.induce H (∑ i ∈ s, c i • f i)
      = ∑ i ∈ s, c i • ClassFunction.induce H (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ClassFunction.induce]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.induce_add,
      ClassFunction.induce_smul, ih]

/-- **(6.8.2.3) aggregate, the `∑ aᵢχᵢ = Ind^L_{W₂} φ` half.**  Summing the constituent characters
`χθ = Ind^M_H θ` weighted by the multiplicities `aθ = ⟨φ∘e, Res_{K.subgroupOf H} θ⟩` of the
decomposition `Ind^H_{K.subgroupOf H}(φ∘e) = ∑ aθ·θ` recovers `Ind^M_K φ` in one step:
`∑_θ aθ • Ind^M_H θ = Ind^M_K φ`.  Combine the constituent decomposition
(`induce_eq_sum_inner_restrict_smul`), `ℂ`-linearity of `Ind_H` (`induce_finset_sum_smul`), and
induction in stages (`induce_induce_subgroupOf`). -/
theorem sum_inner_restrict_smul_induce_eq_induce {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (φ : ClassFunction ↥K ℂ) :
    ∑ θ : IrreducibleCharacter ↥H,
        ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)
            (ClassFunction.restrict (K.subgroupOf H) (θ : ClassFunction ↥H ℂ))
          • ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = ClassFunction.induce K φ := by
  rw [← induce_finset_sum_smul, ← induce_eq_sum_inner_restrict_smul]
  exact induce_induce_subgroupOf hKH φ

/-- **Parseval for an induced character** (the `∑ aᵢ² = ‖Ind φ‖²` step of the (6.8.2.3) aggregate).
`‖Ind^M_N φ‖² = ∑_{θ ∈ Irr M} aθ·\overline{aθ}` where `aθ = ⟨φ, Res_N θ⟩` are the constituent
multiplicities: expand `Ind^M_N φ = ∑ aθ·θ` (`induce_eq_sum_inner_restrict_smul`) and use
orthonormality of `Irr M` (`inner_sum_smul_sum` + `irreducibleCharacter_inner_eq_ite`). -/
theorem inner_self_induce_eq_sum_mul_star {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (φ : ClassFunction ↥N ℂ) :
    ClassFunction.inner (ClassFunction.induce N φ) (ClassFunction.induce N φ)
      = ∑ θ : IrreducibleCharacter M,
          ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          * star (ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))) := by
  rw [induce_eq_sum_inner_restrict_smul φ, OddOrder.Peterfalvi.S05.inner_sum_smul_sum]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  rw [Finset.sum_eq_single θ]
  · rw [irreducibleCharacter_inner_eq_ite, if_pos rfl, mul_one]
  · intro θ' _ hne
    rw [irreducibleCharacter_inner_eq_ite, if_neg (Ne.symm hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ θ) h

/-- **(6.8.2.3) aggregate: `∑ aᵢ² = |M : N|`** for a central `N ≤ Z(M)` and an irreducible (linear)
`φ ∈ Irr N`.  The squared constituent multiplicities `aθ = ⟨φ, Res_N θ⟩` sum to the index:
`∑_θ aθ² = ∑_θ aθ·\overline{aθ}` (the `aθ` are integer multiplicities, `inner_mem_ZIrr_int`, hence
real) `= ‖Ind^M_N φ‖²` (`inner_self_induce_eq_sum_mul_star`) `= |M : N|`
(`inner_induce_self_eq_index_of_le_center`).  This is the `∑ aᵢ² = |H : Z|` term of the
Peterfalvi (6.8.2.3) `αᵢ = χᵢ − aᵢη₁` aggregate. -/
theorem sum_inner_restrict_sq_eq_index {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (hN : N ≤ Subgroup.center M) {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) :
    ∑ θ : IrreducibleCharacter M,
        ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          * ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
      = (N.index : ℂ) := by
  have hreal : ∀ θ : IrreducibleCharacter M,
      ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
        = star (ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))) := by
    intro θ
    obtain ⟨m, hm⟩ :=
      ClassFunction.inner_mem_ZIrr_int hφ.mem_ZIrr (ClassFunction.restrict_mem_ZIrr N θ.2.mem_ZIrr)
    rw [hm, star_intCast]
  rw [show (∑ θ : IrreducibleCharacter M,
        ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          * ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ)))
        = ∑ θ : IrreducibleCharacter M,
          ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
            * star (ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ)))
      from Finset.sum_congr rfl (fun θ _ => by rw [← hreal θ]),
    ← inner_self_induce_eq_sum_mul_star]
  exact inner_induce_self_eq_index_of_le_center hN hφ

/-- **(6.8.2.3) `αᵢ` aggregate** (Peterfalvi (6.8.2.3): `∑ aᵢαᵢ = Ind^L_{W₂} φ − |H:Z|·η₁`).  Summing
the differences `αθ = χθ − aθ·η₁` (`χθ = Ind^M_H θ`, `aθ = ⟨φ∘e, Res_{K.subgroupOf H} θ⟩`) weighted by
`aθ` recovers `Ind^M_K φ − |H:K|·η₁`.  Mechanical combination of the two aggregate halves:
`∑ aθ·χθ = Ind^M_K φ` (`sum_inner_restrict_smul_induce_eq_induce`) and `∑ aθ² = |H:K|`
(`sum_inner_restrict_sq_eq_index`, the index `|↥H : K.subgroupOf H| = |H:K|`). -/
theorem sum_smul_constituent_diff_eq {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (hcen : K.subgroupOf H ≤ Subgroup.center ↥H)
    (φ : ClassFunction ↥K ℂ)
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ))
    (η₁ : ClassFunction M ℂ) :
    ∑ θ : IrreducibleCharacter ↥H,
        ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)
            (ClassFunction.restrict (K.subgroupOf H) (θ : ClassFunction ↥H ℂ))
          • (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
              - ClassFunction.inner
                  (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)
                  (ClassFunction.restrict (K.subgroupOf H) (θ : ClassFunction ↥H ℂ)) • η₁)
      = ClassFunction.induce K φ - ((K.subgroupOf H).index : ℂ) • η₁ := by
  simp_rw [smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib, sum_inner_restrict_smul_induce_eq_induce, ← Finset.sum_smul,
    sum_inner_restrict_sq_eq_index hcen hφ']

/-- **(6.8.2.3) pinning** (Peterfalvi (6.8.2.3): `bᵢ = aᵢ` for all `i`).  Given nonnegative integer
weights `aᵢ ≥ 0` with `bᵢ ≤ aᵢ` and `∑ aᵢbᵢ = ∑ aᵢ²`, every *positive* weight forces `bᵢ = aᵢ`.

This is the final pinning step of (6.8.2.3): from `∑ aᵢbᵢ = |H:Z| = ∑ aᵢ²` (the index, via
`sum_inner_restrict_sq_eq_index` combined with `(6.8.2.2)` `∑ aᵢαᵢ^τ = X − |H:Z|Y`) and the
per-constituent bound `bᵢ ≤ aᵢ` ((5.4.a) `‖Xᵢ‖² ≥ ‖χᵢ‖²`), the slackness
`∑ aᵢ(aᵢ − bᵢ) = ∑ aᵢ² − ∑ aᵢbᵢ = 0` of nonnegative terms forces each `aᵢ(aᵢ − bᵢ) = 0`, hence
`bᵢ = aᵢ` whenever `aᵢ > 0` (the constituent multiplicities `aᵢ = θᵢ(1) > 0`; the `aᵢ = 0`
non-constituents drop out of the `αᵢ` aggregate). -/
theorem eq_of_sum_mul_eq_sum_sq {ι : Type*} (s : Finset ι) (a b : ι → ℤ)
    (hnonneg : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, b i ≤ a i)
    (hsum : ∑ i ∈ s, a i * b i = ∑ i ∈ s, a i * a i) :
    ∀ i ∈ s, 0 < a i → b i = a i := by
  have hsum0 : ∑ i ∈ s, a i * (a i - b i) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hnn : ∀ i ∈ s, 0 ≤ a i * (a i - b i) := fun i hi =>
    mul_nonneg (hnonneg i hi) (sub_nonneg.mpr (hab i hi))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  intro i hi hpos
  rcases mul_eq_zero.mp (hzero i hi) with h | h
  · exact absurd h (ne_of_gt hpos)
  · linarith [sub_eq_zero.mp h]

/-- **Cauchy–Schwarz for the `Y`-coefficient of a (5.4) decomposition** (the (6.8.2.3) per-step
bound `bᵢ² ≤ ‖Y‖²`).  For a `CharacterPsiDecomposition` `D` and a norm-`1` vector `Y`, the integer
coefficient `b = ⟨D.Y, Y⟩` satisfies `b² ≤ ‖D.Y‖²`.  Pythagoras against the orthogonal split
`D.Y = b·Y + (D.Y − b·Y)` (the complement `W` is orthogonal to `Y`, since `b` is real:
`⟨Y, W⟩ = \overline{⟨D.Y, Y⟩} − \overline{b} = 0`), with `‖W‖² ≥ 0` (`inner_self_re_nonneg`). -/
theorem inner_Y_coeff_sq_le {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ ψ : ClassFunction ↥L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ)
    {Y : ClassFunction G ℂ} (hYnorm : ClassFunction.inner Y Y = 1)
    {b : ℤ} (hb : ClassFunction.inner D.Y Y = (b : ℂ)) :
    (b : ℝ) ^ 2 ≤ (ClassFunction.inner D.Y D.Y).re := by
  set W := D.Y - (b : ℂ) • Y with hWdef
  have hYW : ClassFunction.inner Y W = 0 := by
    rw [hWdef, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      hYnorm, mul_one, OddOrder.RepresentationTheory.inner_conj_symm D.Y Y, hb, star_intCast,
      sub_self]
  have hWY : ClassFunction.inner W Y = 0 := by
    rw [hWdef, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hb, hYnorm, mul_one,
      sub_self]
  have hexpand : ClassFunction.inner D.Y D.Y = (b : ℂ) * (b : ℂ) + ClassFunction.inner W W := by
    conv_lhs => rw [show D.Y = (b : ℂ) • Y + W by rw [hWdef]; abel]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hYnorm, hYW,
      hWY, mul_one, mul_zero, star_intCast, add_zero, zero_add]
  rw [hexpand, Complex.add_re,
    show ((b : ℂ) * (b : ℂ)).re = (b : ℝ) ^ 2 by
      rw [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]; ring]
  have := inner_self_re_nonneg W
  linarith

/-- **Per-step coefficient bound `bᵢ ≤ aᵢ`** (Peterfalvi (6.8.2.3), the integer tail of the
Cauchy–Schwarz step).  For a (5.4) decomposition `Da : CharacterPsiDecomposition τ χ (a·η)` with
`η` a norm-`1` vector and `Y` a norm-`1` vector, the integer coefficient `b = ⟨Da.Y, Y⟩` is bounded
by the multiplicity `a`.

Chaining `inner_Y_coeff_sq_le` (`b² ≤ ‖Da.Y‖²`) with the (5.6.2) opening bound
`inner_self_Y_re_le_inner_self_psi` (`‖Da.Y‖² ≤ ‖a·η‖² = a²`) gives `b² ≤ a²` over `ℤ`; with
`a ≥ 0` the integer tail `b² ≤ a² ∧ 0 ≤ a ⟹ b ≤ a` finishes.  This is the per-constituent input to
the (6.8.2.3) pinning `eq_of_sum_mul_eq_sum_sq`. -/
theorem inner_Y_coeff_le_of_psi_nsmul {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ η : ClassFunction ↥L ℂ} {a : ℕ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ (a • η))
    (hηnorm : ClassFunction.inner η η = 1)
    {Y : ClassFunction G ℂ} (hYnorm : ClassFunction.inner Y Y = 1)
    {b : ℤ} (hb : ClassFunction.inner D.Y Y = (b : ℂ)) :
    b ≤ (a : ℤ) := by
  -- `‖ψ‖² = ‖a·η‖² = a²` (`η` norm `1`).
  have hψnorm : (ClassFunction.inner (a • η : ClassFunction ↥L ℂ) (a • η)).re = (a : ℝ) ^ 2 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hηnorm, mul_one, star_natCast,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  -- `b² ≤ ‖Da.Y‖² ≤ ‖ψ‖² = a²`, over `ℝ` then `ℤ`.
  have hsq := inner_Y_coeff_sq_le D hYnorm hb
  have hYle := D.inner_self_Y_re_le_inner_self_psi
  rw [hψnorm] at hYle
  have hb2z : b ^ 2 ≤ (a : ℤ) ^ 2 := by exact_mod_cast le_trans hsq hYle
  -- Integer tail: `b² ≤ a² ∧ 0 ≤ a ⟹ b ≤ a`.
  by_contra hcon
  push_neg at hcon
  have ha : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  nlinarith [mul_nonneg ha (le_of_lt (sub_pos.mpr hcon)),
    mul_pos (lt_of_le_of_lt ha hcon) (sub_pos.mpr hcon), hb2z]

/-- **Transport of coherence across maps agreeing on the supported lattice.**  A coherent isometry
`IsCoherent τ₁ S A` stays coherent for any `τ₂` that agrees with `τ₁` on the supported lattice
`ℤ[S, A]`: the coherent extension is unchanged, and only `extends_on_supported` (the single field
referring to the ambient map) is re-routed through the agreement.

This is the (6.8) case-(B) bridge mechanism: the certain-type coherence `certainType_isCoherent`
(Peterfalvi (4.9)) is stated for `dadeIntegralCharacterMap h.dade0 h.tau`, while the §8 assembly
needs a coherence for the Sibley–Dade `hyp.tau`; both Dade maps coincide with `Ind_L^G` on the
`H^#`-supported lattice (`dadeIntegralCharacterMap_apply_of_support` + `dade_H_eq_bot`), so the
agreement hypothesis is supplied at capstone wiring. -/
def _root_.OddOrder.Peterfalvi.S07.IsCoherent.congrMap
    {M N : Type*} [Group M] [Group N] [Fintype M] [Fintype N]
    [Invertible (Nat.card M : ℂ)] [Invertible (Nat.card N : ℂ)]
    {τ₁ τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap M N}
    {S : Set (ClassFunction M ℂ)} {A : Set M}
    (c : OddOrder.Peterfalvi.S07.IsCoherent τ₁ S A)
    (h : ∀ φ : ClassFunction M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := M) S A → τ₁ φ = τ₂ φ) :
    OddOrder.Peterfalvi.S07.IsCoherent τ₂ S A where
  nonzero := c.nonzero
  extension := c.extension
  extension_inner_eq := c.extension_inner_eq
  extends_on_supported := fun φ hφ => (c.extends_on_supported φ hφ).trans (h φ hφ)
  extension_mem_ZIrr := c.extension_mem_ZIrr

/-- **Span orthogonality from pairwise-orthogonal generators.**  If every `χ ∈ X` is orthogonal to
every `η ∈ Y`, then every element of `ℤ[X]` is orthogonal to every element of `ℤ[Y]` — a pure
`ℤ`-bilinearity fact (`Submodule.span_induction`).

This generalizes `inner_eq_zero_of_mem_span_of_disjoint_irreducible` (which derives the pairwise
orthogonality from distinct-irreducible) so it applies in case (B), where `X = S − S(W₂)` contains the
**reducible** column characters `μ_j = ∑ᵢ μ_{ij}`: `⟨μ_j, η⟩ = ∑ᵢ ⟨μ_{ij}, η⟩ = 0` (each grid
character `μ_{ij} ∈ X` is a distinct irreducible from `η ∈ Y = S(H')`), supplied as the `hpair`
hypothesis at the case-(B) `X ∪ Y` glue. -/
theorem inner_eq_zero_of_mem_span_of_pairwise_orthogonal
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X Y : Set (ClassFunction Γ ℂ)}
    (hpair : ∀ χ ∈ X, ∀ η ∈ Y, ClassFunction.inner χ η = 0) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem χ hχ =>
      intro v hv
      exact OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan
        (fun η hη => hpair χ hχ η hη) hv
  | zero => intro v _hv; exact ClassFunction.inner_zero_left v
  | add x y _hx _hy ihx ihy =>
      intro v hv; rw [ClassFunction.inner_add_left, ihx v hv, ihy v hv, zero_add]
  | smul a x _hx ih =>
      intro v hv
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih v hv, mul_zero]

/-- **Restrict-invariance of the Dade integral character map on the smaller supported lattice.**
If `A₁ ⊆ A` (with `A₁` `L`-invariant), then on `CF(L, A₁)` the integral character map of the
restricted Dade datum `(hyp.restrict, dade.restrict)` agrees with that of `(hyp, dade)`: both reduce
(via `dadeIntegralCharacterMap_apply_of_support`) to `hyp.dadeMap`, related by Peterfalvi (2.11)
(`Hypothesis.dadeMap_restrict_apply`).

This is the (6.8) case-(B) `map-agreement` core: Peterfalvi (4.9)'s certain-type coherence
`certainType_isCoherent` uses the *enlarged* datum `dade0` on `A₀ = A ∪ V^L`, while `hyp.tau` is the
base datum on `A = H^#`; the `μ_j`-differences are `A`-supported, so once the wiring identifies
`dade0.restrict A` with the base datum, this lemma + `IsCoherent.congrMap` transport the certain-type
coherence onto `hyp.tau`. -/
theorem dadeIntegralCharacterMap_restrict_eq_of_support
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {A A₁ : Set G} (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (dade : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp)
    (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : ↥L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ L) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.restrict hA₁A hA₁norm)
        (dade.restrict hA₁A hA₁norm) φ
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade φ := by
  have hφA : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    hφ.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA₁A)
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
        (hyp.restrict hA₁A hA₁norm) (dade.restrict hA₁A hA₁norm) hφ,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp dade hφA,
      OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_restrict_apply hyp hA₁A hA₁norm]
  rfl

/-- **(6.8.2) case-(B) `X ∪ Y` coherence, glued form.**  The case-(B) counterpart of
`coherentXunionYset_centralCommutator_of_glued_of_frobenius`: glue the case-(B) `X`-coherence `cX`
(on `X = S − S(W₂)`, which now contains the reducible column characters `μ_j`) with the `Y`-coherence
`coherentYset` via the §7 diagonal-aware engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`.

The only case-(B) difference from the Frobenius assembly is the **source orthogonality** `X ⊥ Y`:
since `X` is no longer all-irreducible, it is supplied by `inner_eq_zero_of_mem_span_of_pairwise_orthogonal`
from the pairwise `⟨x, y⟩ = 0` (`x ∈ X`, `y ∈ Y`) — for `x = μ_j = ∑ᵢ μ_{ij}` this is
`∑ᵢ ⟨μ_{ij}, η⟩ = 0`.  The combined extension `ν` (the (6.8.2) `τ₂`), its agreements, the mixed inner
products `hmixed` (the (6.8.2.3) content), and the cross-diagonal set `D`/`hDτ` (with the satisfiable
generation `hgen`) are supplied at capstone wiring. -/
noncomputable def SibleyDadeHypothesis.coherentXunionYset_caseB_of_glued
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L}
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset W2, ν x = cX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hpair : ∀ x ∈ hyp.Xset W2, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0)
    (hmixed : ∀ x ∈ hyp.Xset W2, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ)) (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset W2 ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset W2)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset W2 ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    cX hyp.coherentYset ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_pairwise_orthogonal hpair) hmixed D hDτ hgen

/-- **(6.8.2) case-(B) `{μ_j}`-coherence transported to `hyp.tau`.**  The reducible column characters
`μ_j` (`= certainTypeSet h46 k`, the certain-type set of Peterfalvi (4.9)) are coherent via
`certainType_isCoherent`, but with respect to the *enlarged* Dade map
`dadeIntegralCharacterMap h46.dade0 h46.tau` on `A₀ = A ∪ V^L`.  Since the `μ_j`-differences are
`A`-supported (`A = H^#`), `IsCoherent.congrMap` re-targets that coherence to the Sibley–Dade
`hyp.tau`, given the map-agreement `hmapagree` on the supported lattice (established at capstone wiring
from `dadeIntegralCharacterMap_restrict_eq_of_support` + the construction fact `dade0.restrict A`
agrees with the base Dade datum `hyp.dade`, since `h46.dade = hyp.dade`).

This is the reducible side of the case-(B) `X`-coherence `cX`; glued with the `X_irr`-coherence
(`xChainCoherent` on the irreducible part) it yields `IsCoherent hyp.tau (Xset W₂)`. -/
noncomputable def SibleyDadeHypothesis.certainTypeSet_isCoherent_tau
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1)
    (hmapagree : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau φ = hyp.tau φ) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  (OddOrder.Peterfalvi.S06.certainType_isCoherent h46 (k := k) hk).congrMap hmapagree

/-- **(6.8.2) case-(B), `μ_j ∈ S`** (cont.²¹ item 2a): the certain-type column character
`μ_j = columnSum h46 χ₂` (for a nontrivial column `χ₂ ≠ 1`) lies in the Sibley set
`S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1}`.

With `h46.K = H` (case (c2)): `μ_j = Ind_K^L χ_j` ((4.5.a) `induce_restrict_certainType_eq`,
`χ_j = Res_K μ_{0j}`), and transporting the source along `h46.K = H` (`induce_congr_of_subgroup_eq`)
gives `μ_j = Ind_H^L (Res_H μ_{0j})` with `Res_H μ_{0j}` a *nontrivial irreducible* of `H`
(`certainTypeRestrict_isIrreducible` and `chiRestrict_ne_trivialIrreducibleCharacter`, both
transported by `rw [hHK]`). -/
theorem SibleyDadeHypothesis.columnSum_mem_S
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ hyp.S := by
  -- the source `θ = Res_H μ_{0j} : Irr ↥H`, with irreducibility transported from `↥h46.K`
  have hirr : IsIrreducibleCharacter
      (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) := by
    have h := h46.certainTypeRestrict_isIrreducible χ₂
    rwa [hHK] at h
  rw [hyp.S_eq]
  refine ⟨⟨ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ), hirr⟩,
    ?_, ?_⟩
  · -- `θ ≠ 1_H`: transport `chiRestrict_ne_trivial` back along `h46.K = H`
    intro hθtriv
    refine OddOrder.Peterfalvi.S06.chiRestrict_ne_trivialIrreducibleCharacter h46 hχ₂
      (Subtype.ext ?_)
    show ClassFunction.restrict h46.K ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)
        = trivialClassFunction ↥h46.K
    have h1 : ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)
        = trivialClassFunction ↥H := Subtype.ext_iff.mp hθtriv
    refine ClassFunction.ext (fun g => ?_)
    have hg : (g : ↥L) ∈ H := hHK.le g.2
    have hval := congrArg (fun f : ClassFunction ↥H ℂ => f ⟨(g : ↥L), hg⟩) h1
    simpa using hval
  · -- `μ_j = Ind_H^L θ`: `(4.5.a)` then transport the induction source along `h46.K = H`
    rw [OddOrder.Peterfalvi.S06.columnSum_def,
      ← h46.induce_restrict_certainType_eq χ₂]
    exact OddOrder.Peterfalvi.S04.Hypothesis.induce_congr_of_subgroup_eq hHK
      (fun x hx₁ hx₂ => by simp [ClassFunction.restrict_apply])

/-- **(6.8.2) case-(B), `μ_j = Ind_H^L (Res_H μ_{0j})`.**  The transported form of (4.5.a)
`induce_restrict_certainType_eq`: with `h46.K = H`, the column character `μ_j = columnSum h46 χ₂`
is induced from `H` of the source `Res_H μ_{0j}` (the H-presentation of `χ_j`).  Reuses the
`induce_congr_of_subgroup_eq` transport of `columnSum_mem_S`. -/
theorem columnSum_eq_induce_H
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂
      = ClassFunction.induce H
        (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, ← h46.induce_restrict_certainType_eq χ₂]
  exact OddOrder.Peterfalvi.S04.Hypothesis.induce_congr_of_subgroup_eq hHK
    (fun x hx₁ hx₂ => by simp [ClassFunction.restrict_apply])

/-- **(6.8.2) case-(B), `Res_H μ_{ij} = Res_H μ_{0j}`.**  The H-presentation of (4.8) step 1
`restrict_certainType_eq` (`Res_K μ_{ij} = Res_K μ_{0j} = χ_j`), transported pointwise along
`h46.K = H`. -/
theorem restrict_H_certainType_eq
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ClassFunction.restrict H ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) := by
  refine ClassFunction.ext (fun g => ?_)
  have hgK : (g : ↥L) ∈ h46.K := hHK.ge g.2
  have hval := congrArg (fun f : ClassFunction ↥h46.K ℂ => f ⟨(g : ↥L), hgK⟩)
    (h46.restrict_certainType_eq χ₂ i)
  simpa using hval

/-- **(6.8.2) case-(B), `μ_j ∉ S(W₂)`** (cont.²² item 2b): the certain-type column character
`μ_j = columnSum h46 χ₂` (for `χ₂ ≠ 1`) does **not** lie in the filtration `S(W₂)` — no nontrivial
irreducible `θ` of `H` with `W₂ ⊆ Ker θ` induces to `μ_j`.

**Clifford-uniqueness.**  Any `θ` with `Ind_H^L θ = μ_j` is forced to be `Res_H μ_{0j}`: writing
`ψ = Res_H μ_{0j}` (irreducible, `μ_j = Ind_H^L ψ`), Frobenius reciprocity term-by-term over
`μ_j = ∑_i μ_{ij}` (with `Res_H μ_{ij} = ψ`) gives `∑_i ⟨θ, ψ⟩ = ⟨μ_j, μ_j⟩ = ∑_i ⟨ψ, ψ⟩`, so
`w₁·⟨θ, ψ⟩ = w₁·1` and `⟨θ, ψ⟩ = 1 ≠ 0`, whence `θ = ψ` (both irreducible).  But then `W₂ ⊆ Ker ψ`,
contradicting (4.7) `not_subset_characterKernel_chiRestrict_of_ne_one`. -/
theorem SibleyDadeHypothesis.columnSum_notMem_SsubFiltration
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∉ hyp.SsubFiltration h46.W2 := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  set ψ : ClassFunction ↥H ℂ :=
    ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) with hψdef
  have hψirr : IsIrreducibleCharacter ψ := by
    have h := h46.certainTypeRestrict_isIrreducible χ₂
    rwa [hHK] at h
  set ψirr : IrreducibleCharacter ↥H := ⟨ψ, hψirr⟩ with hψirrdef
  intro hmem
  rw [hyp.mem_SsubFiltration] at hmem
  obtain ⟨θ, hθne, hθker, hθind⟩ := hmem
  -- `μ_j = Ind_H^L ψ` in `ψ`-form.
  have hcind : ClassFunction.induce H ψ = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ := by
    rw [hψdef]; exact (columnSum_eq_induce_H h46 hHK χ₂).symm
  -- Per-term Frobenius: for any source `φ`, `⟨Ind_H φ, μ_j⟩ = ∑_i ⟨φ, ψ⟩`.
  have key : ∀ φ : ClassFunction ↥H ℂ,
      ClassFunction.inner (ClassFunction.induce H φ) (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        = ∑ _i : Fin (Nat.card h46.W1), ClassFunction.inner φ ψ := by
    intro φ
    rw [OddOrder.Peterfalvi.S06.columnSum_def, inner_sum_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ClassFunction.inner_induce_eq_inner_restrict, restrict_H_certainType_eq h46 hHK χ₂ i,
      ← hψdef]
  -- `⟨μ_j, μ_j⟩` computed two ways, via `θ` and via `ψ`.
  have hθeq : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        = ∑ _i : Fin (Nat.card h46.W1), ClassFunction.inner (θ : ClassFunction ↥H ℂ) ψ := by
    have hk := key (θ : ClassFunction ↥H ℂ); rwa [← hθind] at hk
  have hψeq : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        = ∑ _i : Fin (Nat.card h46.W1), ClassFunction.inner ψ ψ := by
    have hk := key ψ; rwa [hcind] at hk
  -- `w₁·⟨θ, ψ⟩ = w₁·⟨ψ, ψ⟩`, cancel `w₁ ≠ 0`, then `⟨θ, ψ⟩ = ⟨ψ, ψ⟩ = 1 ≠ 0`.
  have hsum : (Nat.card h46.W1 : ℂ) * ClassFunction.inner (θ : ClassFunction ↥H ℂ) ψ
      = (Nat.card h46.W1 : ℂ) * ClassFunction.inner ψ ψ := by
    have h := hθeq.symm.trans hψeq
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hw1 : (Nat.card h46.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hinner : ClassFunction.inner (θ : ClassFunction ↥H ℂ) ψ = ClassFunction.inner ψ ψ :=
    mul_left_cancel₀ hw1 hsum
  -- `⟨θ, ψirr⟩ = ⟨ψ, ψ⟩ = ⟨ψirr, ψirr⟩ = 1 ≠ 0`, so `θ = ψirr`.
  have hθeqψ : θ = ψirr := by
    by_contra hc
    have e0 : ClassFunction.inner (θ : ClassFunction ↥H ℂ) (ψirr : ClassFunction ↥H ℂ) = 0 := by
      rw [irreducibleCharacter_inner_eq_ite, if_neg hc]
    have e1 : ClassFunction.inner (ψirr : ClassFunction ↥H ℂ) (ψirr : ClassFunction ↥H ℂ) = 1 := by
      rw [irreducibleCharacter_inner_eq_ite, if_pos rfl]
    rw [show (ψirr : ClassFunction ↥H ℂ) = ψ from rfl] at e0 e1
    rw [hinner] at e0
    exact zero_ne_one (e0.symm.trans e1)
  -- contradiction: `W₂ ⊆ Ker ψ = Ker(Res_K μ_{0j}) = Ker χ_j`
  rw [hθeqψ] at hθker
  refine OddOrder.Peterfalvi.S06.Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one
    h46.toCertainTypeHypothesis.toHypothesis hχ₂ (fun x hx => ?_)
  have hxW2 : (x : ↥L) ∈ h46.W2 := Subgroup.mem_subgroupOf.mp hx
  have hxH : (x : ↥L) ∈ H := hHK.le x.2
  have hxker : (⟨(x : ↥L), hxH⟩ : ↥H)
      ∈ OddOrder.Peterfalvi.S03.characterKernel (ψirr : ClassFunction ↥H ℂ) :=
    hθker (Subgroup.mem_subgroupOf.mpr hxW2)
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def] at hxker
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
  simp only [show (ψirr : ClassFunction ↥H ℂ) = ψ from rfl, hψdef,
    OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, ClassFunction.restrict_apply,
    OneMemClass.coe_one] at hxker ⊢
  exact hxker

/-- **(6.8.2) case-(B), `𝒯 ⊆ X(W₂)`** (cont.²² item 2): the certain-type set `𝒯 = {μ_j}` of
Peterfalvi (4.9) is contained in the (6.8) set `X(W₂) = S − S(W₂)`.  Each `μ_j = columnSum h46 χ₂`
(`χ₂ ≠ 1`) lies in `S` (`columnSum_mem_S`, item 2a) but not in `S(W₂)`
(`columnSum_notMem_SsubFiltration`, item 2b), hence in `X(W₂)`. -/
theorem SibleyDadeHypothesis.certainTypeSet_subset_Xset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    OddOrder.Peterfalvi.S06.certainTypeSet h46 k ⊆ hyp.Xset h46.W2 := by
  rintro φ ⟨χ₂, hχ₂, _, rfl⟩
  exact hyp.mem_Xset.mpr ⟨hyp.columnSum_mem_S h46 hHK hχ₂,
    hyp.columnSum_notMem_SsubFiltration h46 hHK hχ₂⟩

/-- **(6.8.2) case-(B): `W₂` is central in `H`.**  In case (B), `W₂ ⊆ Z(↥L)`
(`certainType_W2_le_center`), so its trace `W₂.subgroupOf H` lies in `Z(↥H)`: a `W₂`-element
commutes with all of `↥L`, hence with `↥H`.  This is the [Is] 2.27 hypothesis `Z ≤ Z(G)` (with
`G = ↥H`, `Z = W₂.subgroupOf H`) for the (6.8.2.3) central restriction `Res^H_{W₂} θ = a·φ`. -/
theorem subgroupOf_le_center_of_le_center {W2 : Subgroup ↥L}
    (hW2cen : W2 ≤ Subgroup.center ↥L) :
    W2.subgroupOf H ≤ Subgroup.center ↥H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_center_iff]
  exact fun h => Subtype.ext (Subgroup.mem_center_iff.mp (hW2cen hx) (h : ↥L))

/-- **(6.8.2.3) entry point:** every `χ ∈ X(Z)` is induced from a nontrivial irreducible `θ` of `H`
with `Z ⊄ Ker θ`.

Peterfalvi (6.8.2.3) opens "Let `χ = Ind_H^L θ` where `θ ∈ Irr H` with `Z ⊄ Ker θ`."  Since
`χ ∈ X(Z) = S − S(Z)`: `χ ∈ S` gives `χ = Ind_H^L θ` with `θ ≠ 1` (`S_eq`); and were
`Z ⊆ Ker θ`, that same `θ` would witness `χ ∈ S(Z)` (`mem_SsubFiltration`), contradicting
`χ ∉ S(Z)`.  Route-agnostic (no case split, any `Z : Subgroup ↥L`). -/
theorem SibleyDadeHypothesis.mem_Xset_exists_inducing
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset Z) :
    ∃ θ : IrreducibleCharacter ↥H, θ ≠ trivialIrreducibleCharacter ↥H ∧
      ¬ ((Z.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ)) ∧
      χ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) := by
  obtain ⟨hχS, hχnotZ⟩ := hyp.mem_Xset.mp hχ
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, hθne, hθind⟩ := hχS
  exact ⟨θ, hθne, fun hker => hχnotZ (hyp.mem_SsubFiltration.mpr ⟨θ, hθne, hker, hθind⟩), hθind⟩

/-- **(6.8.2.3) step 2 ([Is] 2.27 central restriction):** for an irreducible `θ` of `H` whose kernel
does not contain the central subgroup `Z = W₂.subgroupOf H`, the restriction `Res^H_Z θ` is `θ(1)` times
a **nontrivial linear** character `φ` of `Z`.

Direct application of `IsIrreducibleCharacter.exists_central_linear_restriction` (Schur central
scalars).  `φ ≠ 1_Z` follows from `Z ⊄ Ker θ`: were `φ` trivial, `θ(z) = φ(z)·θ(1) = θ(1)` for every
`z ∈ Z`, i.e. `Z ⊆ Ker θ`.  `φ` is kept over `↥(W₂.subgroupOf H)` here; the identification with a
character of `↥W₂` (for the (6.8.2.2) `Ind_{W₂}` interface) is a localized transport at that seam. -/
theorem certainType_central_restriction
    (θ : IrreducibleCharacter ↥H) {W2 : Subgroup ↥L}
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hker : ¬ ((W2.subgroupOf H : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    ∃ φ : ClassFunction ↥(W2.subgroupOf H) ℂ, IsIrreducibleCharacter φ ∧
      φ ≠ trivialClassFunction ↥(W2.subgroupOf H) ∧ φ 1 = 1 ∧
      ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ)
        = (θ : ClassFunction ↥H ℂ) 1 • φ := by
  obtain ⟨φ, hφirr, hφ1, hres, hpt⟩ :=
    θ.2.exists_central_linear_restriction (W2.subgroupOf H) hcen
  refine ⟨φ, hφirr, ?_, hφ1, hres⟩
  intro htriv
  refine hker (fun z hz => ?_)
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
  have hzval := hpt ⟨z, hz⟩
  rw [htriv, trivialClassFunction_apply, one_mul] at hzval
  exact hzval

end OddOrder.Peterfalvi.S08
