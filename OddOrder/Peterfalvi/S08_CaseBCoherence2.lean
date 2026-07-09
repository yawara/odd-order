/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedTransport
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

/-! The generic transport lemmas `induce_eq_sum_inner_restrict_smul` /
`inner_compHom_of_mulEquiv` / `induce_induce_subgroupOf` formerly declared here moved to
`OddOrder/GroupTheory/RepresentationTheory/InducedTransport.lean` (hub prefix-split,
issue 9005); they resolve below through `open OddOrder.RepresentationTheory`.
Peterfalvi-context reading: `induce_eq_sum_inner_restrict_smul` is the `Ind^H_Z φ = ∑ aᵢ θᵢ`
step of (6.8.2.3) (the multiplicities `aᵢ = ⟨φ, Res θᵢ⟩` are the `θᵢ(1)` over a central linear
`φ` by [Is] 2.27); `induce_induce_subgroupOf` is its `Ind^H(Ind^H_Z φ) = Ind^L_Z φ` seam, with
`inner_compHom_of_mulEquiv` transporting across `W₂ ≅ W₂.subgroupOf H`. -/

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

/-- **Cauchy–Schwarz against a norm-`1` vector** (integer-coefficient form).  If `⟨u, w⟩ = b ∈ ℤ`
and `‖w‖² = 1`, then `b² ≤ ‖u‖²`.  Pythagoras against the orthogonal split `u = b·w + (u − b·w)`
(the complement `W` is orthogonal to `w`, since `b` is real: `⟨w, W⟩ = \overline{⟨u, w⟩} − \overline{b}
= 0`), with `‖W‖² ≥ 0` (`inner_self_re_nonneg`).

Specializes (with `u = D.Y`, `w = Y`) to the (6.8.2.3) per-step bound `bᵢ² ≤ ‖D.Y‖²`
(`inner_Y_coeff_le_of_psi_nsmul`), and (with `‖u‖² = 1`) gives the integrality bound `|b| ≤ 1` used
in the orthogonality extraction for the disjointness `R(μ_j) ⊥ Y`. -/
theorem inner_intCast_sq_le {u w : ClassFunction G ℂ}
    (hw : ClassFunction.inner w w = 1)
    {b : ℤ} (hb : ClassFunction.inner u w = (b : ℂ)) :
    (b : ℝ) ^ 2 ≤ (ClassFunction.inner u u).re := by
  set W := u - (b : ℂ) • w with hWdef
  have hwW : ClassFunction.inner w W = 0 := by
    rw [hWdef, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      hw, mul_one, OddOrder.RepresentationTheory.inner_conj_symm u w, hb, star_intCast,
      sub_self]
  have hWw : ClassFunction.inner W w = 0 := by
    rw [hWdef, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hb, hw, mul_one,
      sub_self]
  have hexpand : ClassFunction.inner u u = (b : ℂ) * (b : ℂ) + ClassFunction.inner W W := by
    conv_lhs => rw [show u = (b : ℂ) • w + W by rw [hWdef]; abel]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hw, hwW,
      hWw, mul_one, mul_zero, star_intCast, add_zero, zero_add]
  rw [hexpand, Complex.add_re,
    show ((b : ℂ) * (b : ℂ)).re = (b : ℝ) ^ 2 by
      rw [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]; ring]
  have := inner_self_re_nonneg W
  linarith

/-- **Per-step coefficient bound `bᵢ ≤ aᵢ`** (Peterfalvi (6.8.2.3), the integer tail of the
Cauchy–Schwarz step).  For a (5.4) decomposition `Da : CharacterPsiDecomposition τ χ (a·η)` with
`η` a norm-`1` vector and `Y` a norm-`1` vector, the integer coefficient `b = ⟨Da.Y, Y⟩` is bounded
by the multiplicity `a`.

Chaining `inner_intCast_sq_le` (`b² ≤ ‖Da.Y‖²`) with the (5.6.2) opening bound
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
  have hsq := inner_intCast_sq_le hYnorm hb
  have hYle := D.inner_self_Y_re_le_inner_self_psi
  rw [hψnorm] at hYle
  have hb2z : b ^ 2 ≤ (a : ℤ) ^ 2 := by exact_mod_cast le_trans hsq hYle
  -- Integer tail: `b² ≤ a² ∧ 0 ≤ a ⟹ b ≤ a`.
  by_contra hcon
  push Not at hcon
  have ha : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  nlinarith [mul_nonneg ha (le_of_lt (sub_pos.mpr hcon)),
    mul_pos (lt_of_le_of_lt ha hcon) (sub_pos.mpr hcon), hb2z]

/-- **(6.8.2.3) pinning input `∑ aᵢbᵢ = n`.**  Taking the inner product against the `Y`-anchor of
the (6.8.2.2) aggregate identity `Xagg − n·Y = ∑ᵢ aᵢ·(Xᵢ − Yᵢ)` (each `αᵢ^τ = Xᵢ − Yᵢ` a
per-constituent (5.4) image, `bᵢ = ⟨Yᵢ, Y⟩`): the `X`-sides are orthogonal to `Y`
(`⟨Xagg,Y⟩ = 0`, `⟨Xᵢ,Y⟩ = 0`), so `⟨LHS,Y⟩ = −n` and `⟨RHS,Y⟩ = −∑ aᵢbᵢ`, forcing `∑ aᵢbᵢ = n`.
With `∑ aᵢ² = |H:Z| = n` (`sum_inner_restrict_sq_eq_index`) and the per-step bound `bᵢ ≤ aᵢ`
(`inner_Y_coeff_le_of_psi_nsmul`), this is the `hsum` input to the pinning
`eq_of_sum_mul_eq_sum_sq`. -/
theorem sum_coeff_eq_of_aggregate {ι : Type*} (s : Finset ι) (a b : ι → ℤ)
    (X Yv : ι → ClassFunction G ℂ) (Xagg Y : ClassFunction G ℂ) (n : ℤ)
    (hagg : Xagg - (n : ℂ) • Y = ∑ i ∈ s, (a i : ℂ) • (X i - Yv i))
    (hXorth : ∀ i ∈ s, ClassFunction.inner (X i) Y = 0)
    (hb : ∀ i ∈ s, ClassFunction.inner (Yv i) Y = (b i : ℂ))
    (hXaggorth : ClassFunction.inner Xagg Y = 0)
    (hYY : ClassFunction.inner Y Y = 1) :
    ∑ i ∈ s, a i * b i = n := by
  have key : ClassFunction.inner (Xagg - (n : ℂ) • Y) Y
      = ClassFunction.inner (∑ i ∈ s, (a i : ℂ) • (X i - Yv i)) Y := by rw [hagg]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hXaggorth, hYY, mul_one,
    zero_sub, inner_sum_left] at key
  -- `⟨LHS,Y⟩ = −n`; each `RHS` term `⟨aᵢ•(Xᵢ−Yᵢ), Y⟩ = −aᵢbᵢ`.
  have hterm : ∑ i ∈ s, ClassFunction.inner ((a i : ℂ) • (X i - Yv i)) Y
      = ∑ i ∈ s, -((a i : ℂ) * (b i : ℂ)) :=
    Finset.sum_congr rfl fun i hi => by
      rw [ClassFunction.inner_smul_left, ClassFunction.inner_sub_left, hXorth i hi, hb i hi]; ring
  rw [hterm, Finset.sum_neg_distrib] at key
  -- `key : −n = −∑ aᵢbᵢ` over `ℂ`; cancel the sign and descend to `ℤ`.
  have hcast : (n : ℂ) = ∑ i ∈ s, (a i : ℂ) * (b i : ℂ) := neg_injective key
  exact_mod_cast hcast.symm

/-- **Cauchy–Schwarz equality ⟹ parallel** (the (6.8.2.3) `Yᵢ = aᵢ·Y` bridge).  For a norm-`1`
vector `w`, an integer `a`, and a vector `v` with `⟨v, w⟩ = a` and `‖v‖² = a²`, the equality case of
Cauchy–Schwarz forces `v = a·w`: indeed `‖v − a·w‖² = ‖v‖² − a⟨v,w⟩ − a⟨w,v⟩ + a²‖w‖² = 0`, so the
positive-definiteness `eq_zero_of_inner_self_re_eq_zero` gives `v − a·w = 0`.

This is the bridge from the (6.8.2.3) pinning `bᵢ = ⟨Yᵢ,Y⟩ = aᵢ` together with `‖Yᵢ‖² = ‖aᵢ·η₁‖² = aᵢ²`
((5.4.b)) to the per-step image `Yᵢ = aᵢ·Y`, which then assembles the per-`χ` identity
`(χ − a·η₁)^τ = X₁ − a·Y`. -/
theorem eq_smul_of_inner_self_eq {v w : ClassFunction G ℂ} {a : ℤ}
    (hvw : ClassFunction.inner v w = (a : ℂ))
    (hvv : ClassFunction.inner v v = (a : ℂ) ^ 2)
    (hww : ClassFunction.inner w w = 1) :
    v = (a : ℂ) • w := by
  have hnorm : ClassFunction.inner (v - (a : ℂ) • w) (v - (a : ℂ) • w) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_conj_symm v w, hvw, hvv, hww, star_intCast]
    ring
  have hre : (ClassFunction.inner (v - (a : ℂ) • w) (v - (a : ℂ) • w)).re = 0 := by
    rw [hnorm]; simp
  exact sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero hre)

/-- **Aggregate τ-image of integer-weighted constituents** (the (6.8.2.2)→(6.8.2.3) bridge).  For a
`ℤ`-linear character map `τ` and per-constituent images `τ(αᵢ) = Xᵢ − Yᵢ`, the integer-weighted
aggregate maps termwise: `τ(∑ᵢ aᵢ·αᵢ) = ∑ᵢ aᵢ·(Xᵢ − Yᵢ)`.  Pure `ℤ`-linearity (`map_sum` +
`map_zsmul`, with the `(aᵢ : ℂ)`-scalar smul reduced to the `ℤ`-action via `Int.cast_smul_eq_zsmul`).

Combined with `sum_smul_constituent_diff_eq` (`∑ aᵢ·αᵢ = Ind^L_{W₂}φ − |H:Z|·η₁`) and the (6.8.2.2)
decomposition `exists_decomposition_caseB` (`τ(Ind φ − |H:Z|·η₁) = Xagg − |H:Z|·Y`), this supplies the
`hagg` input `Xagg − n·Y = ∑ᵢ aᵢ·(Xᵢ − Yᵢ)` of the pinning lemma `sum_coeff_eq_of_aggregate`. -/
theorem tau_sum_smul_image {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {ι : Type*} (s : Finset ι) (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G)
    (α : ι → ClassFunction ↥L ℂ) (Xv Yv : ι → ClassFunction G ℂ) (a : ι → ℤ)
    (himg : ∀ i ∈ s, τ (α i) = Xv i - Yv i) :
    τ (∑ i ∈ s, (a i : ℂ) • α i) = ∑ i ∈ s, (a i : ℂ) • (Xv i - Yv i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Int.cast_smul_eq_zsmul ℂ (a i) (α i), map_zsmul, himg i hi,
    ← Int.cast_smul_eq_zsmul ℂ (a i) (Xv i - Yv i)]

/-- **(6.8.2.2)→(6.8.2.3) aggregate `hagg` builder.**  Assembles the `hagg` input of
`per_constituent_Y_eq_smul` from the three (6.8.2.2) pieces: the image decomposition
`τ β = Xagg − n·Y` (`exists_decomposition_caseB`, `β = Ind^L_{W₂}φ − |H:Z|·η₁`, `n = |H:Z|`), the
constituent sum `β = ∑ aᵢ·αᵢ` (`sum_smul_constituent_diff_eq`), and the per-constituent images
`τ(αᵢ) = Xᵢ − Yᵢ` (each `CharacterPsiDecomposition.tau1_image`, with `τ₁ = τ` for the certain-type
`certainTypeDecompositionDa`).  Rewriting `Xagg − n·Y = τ β = τ(∑ aᵢαᵢ) = ∑ aᵢ(Xᵢ − Yᵢ)` via
`tau_sum_smul_image` gives the aggregate `Xagg − n·Y = ∑ aᵢ·(Xᵢ − Yᵢ)`. -/
theorem aggregate_eq_sum_of_constituent {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)]
    {ι : Type*} (s : Finset ι) (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G)
    (α : ι → ClassFunction ↥L ℂ) (Xv Yv : ι → ClassFunction G ℂ) (a : ι → ℤ)
    {β : ClassFunction ↥L ℂ} {Xagg Y : ClassFunction G ℂ} {n : ℤ}
    (hmemimg : ∀ i ∈ s, τ (α i) = Xv i - Yv i)
    (hconstit : β = ∑ i ∈ s, (a i : ℂ) • α i)
    (hdecomp : τ β = Xagg - (n : ℂ) • Y) :
    Xagg - (n : ℂ) • Y = ∑ i ∈ s, (a i : ℂ) • (Xv i - Yv i) := by
  rw [← hdecomp, hconstit]
  exact tau_sum_smul_image s τ α Xv Yv a hmemimg

/-- **Reindex a finite sum to the positive-weight subtype.**  Terms with zero weight (`a i = 0`)
drop out, so a sum over all of `ι` equals the sum over the subtype `{i // 0 < a i}`.

This restricts the (6.8.2.3) constituent aggregate — indexed by *all* of `Irr H`, with the
zero-multiplicity constituents `Ind^L_H θ` (`aθ = ⟨φ, Res_{W₂}θ⟩ = 0`) contributing nothing — to the
positive-multiplicity constituents `{θ // 0 < aθ}`.  The restriction is forced: `Ind^L_H θ` has
degree `≠ 0`, so it is *not* `H^#`-supported and admits **no** `CharacterPsiDecomposition` with the
zero anchor `0 • η₁`; the per-`φ` decomposition family can only be defined on the positive-weight
subtype. -/
theorem sum_eq_sum_pos_weight_subtype {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (a : ι → ℕ) (f : ι → M) (hf : ∀ i, a i = 0 → f i = 0) :
    ∑ i : ι, f i = ∑ i : {i : ι // 0 < a i}, f i.val := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => 0 < a i)) (fun x => by simp) f]
  exact (Finset.sum_filter_of_ne
    (fun i _ hne => Nat.pos_of_ne_zero (fun h0 => hne (hf i h0)))).symm

/-- **(6.8.2.3) constituent weight as a natural number.**  For an irreducible `φ` of a subgroup
`N ≤ M` and an irreducible character `θ` of `M`, the multiplicity `⟨φ, Res^M_N θ⟩` is a natural
number (Clifford [Is] Thm 6.5, `restrictionMultiplicity_natCast`): a nonnegative integer, repackaged
for the `φ`-first inner-product slot used by the (6.8.2.3) constituent aggregate
`sum_smul_constituent_diff_eq` (which weights `αθ = Ind^M_H θ − aθ·η₁` by `aθ = ⟨φ, Res θ⟩`).  This is
the source of the natural-number weight `a : ι → ℕ` consumed by the pinning `per_constituent_Y_eq_smul`. -/
theorem exists_inner_restrict_natCast {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) :
    ∃ k : ℕ, ClassFunction.inner φ
      (ClassFunction.restrict N (θ : ClassFunction M ℂ)) = (k : ℂ) := by
  obtain ⟨k, hk⟩ := ClassFunction.restrictionMultiplicity_natCast N θ.2 hφ
  exact ⟨k, by rw [OddOrder.RepresentationTheory.inner_conj_symm,
    ← ClassFunction.restrictionMultiplicity_def, hk, star_natCast]⟩

/-- **(6.8.2.3) constituent weight** `aθ = ⟨φ, Res^M_N θ⟩ : ℕ` (the Clifford multiplicity of `φ`
in `Res^M_N θ`).  The natural-number weight indexing the (6.8.2.3) `αθ`-aggregate and consumed by
the pinning `per_constituent_Y_eq_smul`.  The defining `ℂ`-equation is `constituentWeight_spec`. -/
noncomputable def constituentWeight {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) : ℕ :=
  (exists_inner_restrict_natCast hφ θ).choose

/-- The defining equation of `constituentWeight`: `⟨φ, Res^M_N θ⟩ = (aθ : ℂ)`. -/
theorem constituentWeight_spec {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) :
    ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
      = (constituentWeight hφ θ : ℂ) :=
  (exists_inner_restrict_natCast hφ θ).choose_spec

/-- A constituent has positive weight iff `φ` actually occurs in `Res^M_N θ` (i.e. `θ` "lies over"
`φ`).  This is the membership test for the positive-weight subtype `{θ // 0 < aθ}` (the per-`φ`
decomposition family index, `sum_eq_sum_pos_weight_subtype`). -/
theorem constituentWeight_pos_iff {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) :
    0 < constituentWeight hφ θ ↔
      ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ)) ≠ 0 := by
  rw [constituentWeight_spec hφ θ, ne_eq, Nat.cast_eq_zero, ← ne_eq, ← Nat.pos_iff_ne_zero]

/-- **(6.8.2.3) constituent aggregate over the positive-weight subtype.**  The `αθ`-aggregate
`sum_smul_constituent_diff_eq` (indexed by all of `Irr H`, with weight `aθ = ⟨φ, Res θ⟩` written as
the `ℂ`-valued multiplicity) reindexed to the positive-weight subtype `{θ // 0 < aθ}` with the weight
in natural-number form `constituentWeight`:
`Ind^M_K φ − |H:K|·η₁ = ∑_{θ : 0 < aθ} aθ·(Ind^M_H θ − aθ·η₁)`.

This is the `hconstit` source aggregate for the per-`φ` pinning: the index matches the per-`φ`
decomposition family `{θ // 0 < aθ}`, and the weight is the `ℕ` consumed by
`per_constituent_Y_eq_smul` (the `ℂ`-coefficient `⟨φ, Res θ⟩` is `(constituentWeight … : ℂ)` by
`constituentWeight_spec`; the `aθ = 0` constituents drop out by `sum_eq_sum_pos_weight_subtype`). -/
theorem sum_smul_constituent_diff_pos_weight_subtype {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (hcen : K.subgroupOf H ≤ Subgroup.center ↥H)
    (φ : ClassFunction ↥K ℂ)
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ))
    (η₁ : ClassFunction M ℂ) :
    ClassFunction.induce K φ - ((K.subgroupOf H).index : ℂ) • η₁
      = ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
          (constituentWeight hφ' i.val : ℂ) •
            (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
              - (constituentWeight hφ' i.val : ℂ) • η₁) := by
  rw [← sum_smul_constituent_diff_eq hKH hcen φ hφ' η₁]
  simp only [constituentWeight_spec hφ']
  exact sum_eq_sum_pos_weight_subtype (constituentWeight hφ')
    (fun θ => (constituentWeight hφ' θ : ℂ) • (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      - (constituentWeight hφ' θ : ℂ) • η₁)) (fun θ hθ => by
        simp only [hθ, Nat.cast_zero, zero_smul])

/-- **(6.8.2.3) per-constituent pinned image `Yᵢ = aᵢ·Y`.**  The capstone of the (6.8.2.3) per-step
bound + pinning + Cauchy–Schwarz-equality bridge, packaging the whole `pinning → image` algebra so the
case-(B) instantiation need only discharge the named structural hypotheses.

For per-constituent (5.4) decompositions `Dᵢ : CharacterPsiDecomposition τ χᵢ (aᵢ·η)` (the `χᵢ` the
constituents of `Ind^L_{W₂}φ`, `η` the norm-`1` `Y`-anchor at source), given:
* the (6.8.2.2) aggregate `Xagg − n·Y = ∑ᵢ aᵢ·(Dᵢ.X − Dᵢ.Y)` (`tau_sum_smul_image` +
  `sum_smul_constituent_diff_eq` + `exists_decomposition_caseB`), `∑ aᵢ² = n` (`= |H:Z|`,
  `sum_inner_restrict_sq_eq_index`), and `‖Y‖² = 1`;
* the orthogonalities `⟨Dᵢ.X, Y⟩ = 0` (`inner_decomposition_X_extension_member_eq_zero`),
  `⟨Xagg, Y⟩ = 0`, and the integrality `⟨Dᵢ.Y, Y⟩ = bᵢ ∈ ℤ`;
the pinning `∑ aᵢbᵢ = n = ∑ aᵢ²` (`sum_coeff_eq_of_aggregate`) with the per-step bound `bᵢ ≤ aᵢ`
(`inner_Y_coeff_le_of_psi_nsmul`) forces `bᵢ = aᵢ` (`eq_of_sum_mul_eq_sum_sq`), whence
`aᵢ² = bᵢ² ≤ ‖Dᵢ.Y‖² ≤ ‖aᵢ·η‖² = aᵢ²` gives `‖Dᵢ.Y‖² = aᵢ²` and the Cauchy–Schwarz equality
`eq_smul_of_inner_self_eq` yields `Dᵢ.Y = aᵢ·Y`. -/
theorem per_constituent_Y_eq_smul {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {ι : Type*} (s : Finset ι) {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ : ι → ClassFunction ↥L ℂ} {η : ClassFunction ↥L ℂ} {a : ι → ℕ}
    (D : (i : ι) → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ (χ i) (a i • η))
    {Y Xagg : ClassFunction G ℂ} {b : ι → ℤ} {n : ℤ}
    (hηnorm : ClassFunction.inner η η = 1)
    (hYY : ClassFunction.inner Y Y = 1)
    (hXaggorth : ClassFunction.inner Xagg Y = 0)
    (hagg : Xagg - (n : ℂ) • Y = ∑ i ∈ s, ((a i : ℤ) : ℂ) • ((D i).X - (D i).Y))
    (hsq : ∑ i ∈ s, ((a i : ℤ)) ^ 2 = n)
    (hXorth : ∀ i ∈ s, ClassFunction.inner (D i).X Y = 0)
    (hbi : ∀ i ∈ s, ClassFunction.inner (D i).Y Y = (b i : ℂ))
    (i : ι) (hi : i ∈ s) (hpos : 0 < a i) :
    (D i).Y = (a i : ℂ) • Y := by
  -- Pinning: `∑ aᵢbᵢ = n = ∑ aᵢ²`, with `bᵢ ≤ aᵢ` and `aᵢ ≥ 0`, forces `bᵢ = aᵢ`.
  have hsumab : ∑ j ∈ s, (a j : ℤ) * b j = n :=
    sum_coeff_eq_of_aggregate s (fun j => (a j : ℤ)) b (fun j => (D j).X) (fun j => (D j).Y)
      Xagg Y n hagg hXorth hbi hXaggorth hYY
  have hbound : ∀ j ∈ s, b j ≤ (a j : ℤ) := fun j hj =>
    inner_Y_coeff_le_of_psi_nsmul (D j) hηnorm hYY (hbi j hj)
  have hsumeq : ∑ j ∈ s, (a j : ℤ) * b j = ∑ j ∈ s, (a j : ℤ) * (a j : ℤ) := by
    rw [hsumab, ← hsq]; exact Finset.sum_congr rfl fun j _ => pow_two (a j : ℤ)
  have hbeq : b i = (a i : ℤ) :=
    eq_of_sum_mul_eq_sum_sq s (fun j => (a j : ℤ)) b (fun j _ => Int.natCast_nonneg (a j))
      hbound hsumeq i hi (show (0 : ℤ) < ((a i : ℕ) : ℤ) by exact_mod_cast hpos)
  -- `‖Dᵢ.Y‖² = aᵢ²`:  `aᵢ² = bᵢ² ≤ ‖Dᵢ.Y‖² ≤ ‖aᵢ·η‖² = aᵢ²`.
  have hCS := inner_intCast_sq_le hYY (hbi i hi)
  have h562 := (D i).inner_self_Y_re_le_inner_self_psi
  have hψnorm : (ClassFunction.inner (a i • η : ClassFunction ↥L ℂ) (a i • η)).re
      = (a i : ℝ) ^ 2 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ (a i) η, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hηnorm, mul_one, star_natCast,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hψnorm] at h562
  have hYinorm_re : (ClassFunction.inner (D i).Y (D i).Y).re = (a i : ℝ) ^ 2 := by
    have hba : (b i : ℝ) = (a i : ℝ) := by exact_mod_cast hbeq
    rw [hba] at hCS; linarith
  -- Realness `⟨Dᵢ.Y, Dᵢ.Y⟩ = ((⟨Dᵢ.Y,Dᵢ.Y⟩).re : ℂ)` upgrades the `.re` to a `ℂ`-equation.
  have hreal : ClassFunction.inner (D i).Y (D i).Y
      = ((ClassFunction.inner (D i).Y (D i).Y).re : ℂ) := by
    rw [inner_self_eq_realCast, Complex.ofReal_re]
  -- Cauchy–Schwarz equality `Dᵢ.Y = aᵢ·Y` (via the `ℤ`-cast scalar, then `Int.cast_natCast`).
  have key := eq_smul_of_inner_self_eq (v := (D i).Y) (w := Y) (a := (a i : ℤ))
    (by rw [hbi i hi]; exact_mod_cast hbeq)
    (by rw [hreal, hYinorm_re]; push_cast; ring) hYY
  rwa [Int.cast_natCast] at key

/-- **Seam-1 orthogonality `⟨Dᵢ.X, Y⟩ = 0`** (Peterfalvi (6.8.2.3): "`R(χᵢ)` is orthogonal to
`Y^{τ₁}` by (5.3) and (5.5)").  Since `Dᵢ.X ∈ ℤ[R(χᵢ)]`, orthogonality of `Y` to the image family
`R(χᵢ)` (the `(5.3)/(5.5)` disjointness, supplied at the case-(B) instantiation — e.g. `Y = ε·ξ` for
an irreducible `ξ ∉ R(χᵢ)` via `coherentYset_extension_eq_zsmul_irreducible`) propagates to `Dᵢ.X`
(`inner_X_eq_zero_of_orthogonal_imageSet`), and conjugate symmetry flips the slot.

This is the `hXorth` input of `per_constituent_Y_eq_smul`. -/
theorem inner_X_Y_eq_zero_of_orthogonal {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ ψ : ClassFunction ↥L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) {Y : ClassFunction G ℂ}
    (hY : ∀ α ∈ D.imageFamily.imageSet, ClassFunction.inner Y α = 0) :
    ClassFunction.inner D.X Y = 0 := by
  rw [OddOrder.RepresentationTheory.inner_conj_symm Y D.X,
    D.inner_X_eq_zero_of_orthogonal_imageSet hY, star_zero]

/-- **Orthogonality extraction from a two-irreducible difference** (the (6.8.2.3) disjointness
core).  If `ξ`, `ξ'` are orthonormal (`‖ξ‖² = 1`, `⟨ξ, ξ'⟩ = 0`), `θ` is a norm-`1` vector with
`⟨ξ, θ⟩ ∈ ℤ`, and `c·ξ − c'·ξ' ⊥ θ` for `c ≠ 0`, then `⟨ξ, θ⟩ = 0`.

This is the extraction step of the disjointness `R(μ_j) ⊥ Y`: writing `Y = ε·ξ` (`ξ` the `Y`-anchor
irreducible image, `coherentYset_extension_eq_zsmul_irreducible`) so that
`(η₁ − η̄₁)^τ = ε·ξ − ε'·ξ'` is orthogonal to every `σ`-image `θ = ω^σ` (by (3.8) /
`grid_eq_zero_of_ncard_support_lt`, since `NC ≤ 2 < min(w₁, w₂)`), the integrality bound
`|⟨ξ, θ⟩| ≤ 1` (`inner_intCast_sq_le`) forces `⟨ξ, θ⟩ = 0`: otherwise `⟨ξ, θ⟩ = ±1` makes
`ξ = ±θ` (Cauchy–Schwarz equality `eq_smul_of_inner_self_eq`), so `⟨ξ', θ⟩ = 0` (from `⟨ξ, ξ'⟩ = 0`)
and the orthogonality collapses to `c·⟨ξ, θ⟩ = 0`, contradicting `c ≠ 0`. -/
theorem inner_eq_zero_of_smul_sub_smul_orthogonal {ξ ξ' θ : ClassFunction G ℂ}
    (hξ : ClassFunction.inner ξ ξ = 1) (hθ : ClassFunction.inner θ θ = 1)
    (hξξ' : ClassFunction.inner ξ ξ' = 0)
    {m : ℤ} (hm : ClassFunction.inner ξ θ = (m : ℂ))
    {c c' : ℂ} (hc : c ≠ 0)
    (horth : ClassFunction.inner (c • ξ - c' • ξ') θ = 0) :
    ClassFunction.inner ξ θ = 0 := by
  rw [hm]
  by_contra hne
  have hmne : m ≠ 0 := fun h => hne (by rw [h]; simp)
  -- `|m| ≤ 1` from the norm-`1` Cauchy–Schwarz bound, hence `m = ±1`.
  have hmsqz : m ^ 2 ≤ 1 := by
    have h := inner_intCast_sq_le hθ hm
    rw [hξ, Complex.one_re] at h
    exact_mod_cast h
  have hlo : -1 ≤ m := by nlinarith [sq_nonneg (m + 1)]
  have hhi : m ≤ 1 := by nlinarith [sq_nonneg (m - 1)]
  have hmsq1 : (m : ℂ) ^ 2 = 1 := by interval_cases m <;> simp_all
  -- `‖ξ‖² = (m:ℂ)²`, so `ξ = (m:ℂ)·θ` by the equality case of Cauchy–Schwarz.
  have hξeq : ξ = (m : ℂ) • θ := eq_smul_of_inner_self_eq hm (by rw [hξ, hmsq1]) hθ
  -- `⟨ξ, ξ'⟩ = (m:ℂ)·⟨θ, ξ'⟩ = 0` with `(m:ℂ) ≠ 0` ⟹ `⟨ξ', θ⟩ = 0`.
  rw [hξeq, ClassFunction.inner_smul_left] at hξξ'
  have hξ'θ : ClassFunction.inner ξ' θ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm θ ξ',
      (mul_eq_zero.mp hξξ').resolve_left hne, star_zero]
  -- `horth` collapses to `c·(m:ℂ) = 0`, contradicting `c ≠ 0`, `(m:ℂ) ≠ 0`.
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hξ'θ, mul_zero, sub_zero, hm] at horth
  exact (mul_ne_zero hc hne) horth

/-- **`σ`-coefficient vanishing from a small support** (the (3.2.d)/(3.8) "all coefficients zero"
case, via `grid_eq_zero_of_ncard_support_lt`).  For `ψ` vanishing on `V` with `NC(ψ) < min(w₁, w₂)`,
every `σ`-image coefficient `sigmaCoeff ψ = ⟨ψ, ω^σ⟩` vanishes: the (3.7) additive identity
`sigmaCoeff_add_eq` (from `ψ` vanishing on `V`) makes the coefficient grid additively separable, so a
support smaller than `min(w₁, w₂)` forces it identically zero.

This is the (6.8.2.3) disjointness driver: applied to `ψ = (η₁ − η̄₁)^τ` (vanishing on `V` since
`η₁ − η̄₁` is `A`-supported, with `NC ≤ 2 < min(w₁, w₂)` as a difference of two irreducibles), it
gives `(η₁ − η̄₁)^τ ⊥ Im σ`, feeding the extraction `inner_eq_zero_of_smul_sub_smul_orthogonal`.
The simpler `grid_eq_zero_of_ncard_support_lt` (no `w₁ + 2 ≤ w₂` gap) suffices here, unlike the full
trichotomy `sigmaCoeff_trichotomy`. -/
theorem sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (hNC : hyp.sigmaNC hVeq app ψ < min (Nat.card hyp.W1) (Nat.card hyp.W2))
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app ψ pq = 0 := by
  refine OddOrder.Peterfalvi.S05.grid_eq_zero_of_ncard_support_lt
    (fun pq => hyp.sigmaCoeff hVeq app ψ pq)
    (fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψ p p' q q') ?_ pq
  rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
  exact hNC

/-- **`NC ≤ 2` for a two-irreducible difference** (the (6.8.2.3) `NC((η₁ − η̄₁)^τ) ≤ 2` bound).  If
every nonzero `σ`-coefficient of `ψ` forces a nonzero inner product with one of two norm-`1` virtual
characters `ξ`, `ξ' ∈ ±Irr(G)` (the case `ψ = c·ξ − c'·ξ'`), then `NC(ψ) ≤ 2`: by (3.9)(a)
(`ncard_inner_chiFam_ne_zero_le_one`) each of `ξ`, `ξ'` has at most one nonzero `σ`-coefficient, and
the support of `ψ` lies in their union.  With `min(w₁, w₂) ≥ 3` (odd-order Hall), this feeds the
`grid_eq_zero` driver `sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt`. -/
theorem sigmaNC_le_two_of_inner_chiFam
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication hyp)
    {ξ ξ' : ClassFunction G ℂ} (hξZ : ξ ∈ ZIrr G) (hξ1 : ClassFunction.inner ξ ξ = 1)
    (hξ'Z : ξ' ∈ ZIrr G) (hξ'1 : ClassFunction.inner ξ' ξ' = 1)
    {ψ : ClassFunction G ℂ}
    (hψsupp : ∀ pq, hyp.sigmaCoeff hVeq app ψ pq ≠ 0 →
      ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0 ∨
        ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0) :
    hyp.sigmaNC hVeq app ψ ≤ 2 := by
  classical
  haveI : Finite G := Finite.of_fintype G
  have hsub : {pq | hyp.sigmaCoeff hVeq app ψ pq ≠ 0} ⊆
      {pq | ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0} ∪
        {pq | ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0} :=
    fun pq hpq => hψsupp pq hpq
  calc hyp.sigmaNC hVeq app ψ
      = {pq | hyp.sigmaCoeff hVeq app ψ pq ≠ 0}.ncard := rfl
    _ ≤ ({pq | ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {pq | ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0}.ncard +
          {pq | ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0}.ncard := Set.ncard_union_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · exact OddOrder.Peterfalvi.S05.TICyclicHypothesis.ncard_inner_chiFam_ne_zero_le_one
            hyp hVeq app hξZ hξ1
        · exact OddOrder.Peterfalvi.S05.TICyclicHypothesis.ncard_inner_chiFam_ne_zero_le_one
            hyp hVeq app hξ'Z hξ'1
    _ = 2 := rfl

/-- **(6.8.2.3) anchor, group-theoretic core: `V` avoids the `G`-conjugates of `K`-elements.**
A point `v` of the `(ticVdiff h)`-exceptional set `V = W − (W₁ ∪ W₂)` is never `G`-conjugate to an
element of the kernel `K = h.K` (viewed in `G` via `L ↪ G`).

Indeed, write `v = ↑w` with `w = x·y ∈ W₁ × W₂` (`exists_mul_of_mem_sup`); since `v ∉ W₂` the
`W₁`-component `x ≠ 1`, and `x = w ^ n` (`exists_zpow_proj`) gives `orderOf x ∣ orderOf w = orderOf v`.
If `v` were `G`-conjugate to `↑k` (`k ∈ K`) then `orderOf v = orderOf k ∣ |K|` (conjugation preserves
order), so `orderOf x ∣ gcd(|K|, |W₁|) = 1` (`card_coprime`), forcing `x = 1` — a contradiction.

This is the structural disjointness `V ∩ (K^#)^G = ∅` powering the anchor: since
`Supp(η₁ − η̄₁) ⊆ H^# ⊆ K^#` and `(η₁ − η̄₁)^τ` is a Dade image (vanishing off `conjugatesOfSet H^#`),
it vanishes on `V`. -/
theorem ticVdiffV_not_mem_conjugatesOfSet_K {A : Set G}
    (h : OddOrder.Peterfalvi.S06.Hypothesis46 A L) {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h).V) :
    v ∉ Group.conjugatesOfSet ((h.K.map L.subtype : Subgroup G) : Set G) := by
  intro hconj
  -- `v` is `G`-conjugate to `a = ↑k` with `k ∈ K`
  obtain ⟨a, haK, hav⟩ := Group.mem_conjugatesOfSet_iff.mp hconj
  obtain ⟨k, hkK, hka⟩ := Subgroup.mem_map.mp haK
  -- `orderOf a = orderOf v` (conjugation preserves order)
  obtain ⟨c, hc⟩ := isConj_iff.mp hav
  have hsemi : SemiconjBy c a v := by
    show c * a = v * c
    rw [← hc]; group
  have hav_ord : orderOf a = orderOf v := SemiconjBy.orderOf_eq c hsemi
  -- `orderOf a = orderOf k ∣ |K|`
  have hak : a = ((k : ↥L) : G) := hka.symm
  have hoak : orderOf a = orderOf k := by rw [hak]; exact Subgroup.orderOf_coe k
  have hok_dvd : orderOf k ∣ Nat.card ↥h.K := by
    rw [← Subgroup.orderOf_mk (H := h.K) k hkK]; exact orderOf_dvd_natCard _
  -- `v ∈ tic.W`, `v ∉ tic.W2`
  have hvmem : v ∈ (↑h.tic.W : Set G) \ ((↑h.tic.W1 : Set G) ∪ ↑h.tic.W2) := hv
  have hvW : v ∈ h.tic.W := hvmem.1
  rw [OddOrder.Peterfalvi.S06.tic_W_eq_map h] at hvW
  obtain ⟨w, hwW12, hwv⟩ := Subgroup.mem_map.mp hvW
  -- `v ∉ tic.W2 ⟹ w ∉ W₂`
  have hvnW2 : v ∉ h.tic.W2 := fun hc => hvmem.2 (Or.inr hc)
  have hwnW2 : w ∉ h.W2 := by
    intro hwW2
    exact hvnW2 (h.tic_W2 ▸ Subgroup.mem_map.mpr ⟨w, hwW2, hwv⟩)
  -- decompose `w = x·y` with `x ∈ W₁`, `y ∈ W₂`; `w ∉ W₂` forces `x ≠ 1`
  obtain ⟨x, hxW1, y, hyW2, hxy⟩ := h.exists_mul_of_mem_sup hwW12
  have hx1 : x ≠ 1 := by
    intro hx
    exact hwnW2 (by rw [← hxy, hx, one_mul]; exact hyW2)
  -- `x = w ^ n`, so `orderOf x ∣ orderOf w = orderOf v`
  obtain ⟨n, hn⟩ := h.exists_zpow_proj
  have hxwn : w ^ n = x := by rw [← hxy]; exact hn x hxW1 y hyW2
  have hox_dvd_ow : orderOf x ∣ orderOf w :=
    orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨n, hxwn⟩)
  have how_ov : orderOf w = orderOf v := by rw [← hwv]; exact (Subgroup.orderOf_coe w).symm
  -- `orderOf x ∣ |K|` and `orderOf x ∣ |W₁|`, coprime ⟹ `x = 1`, contradiction
  have how_K : orderOf w ∣ Nat.card ↥h.K := by
    rw [how_ov, ← hav_ord, hoak]; exact hok_dvd
  have hox_K : orderOf x ∣ Nat.card ↥h.K := hox_dvd_ow.trans how_K
  have hox_W1 : orderOf x ∣ Nat.card ↥h.W1 := by
    rw [← Subgroup.orderOf_mk (H := h.W1) x hxW1]; exact orderOf_dvd_natCard _
  exact hx1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h.card_coprime hox_K hox_W1))

/-- **(6.8.2.3) anchor: the Dade image of an `H^#`-supported function vanishes on `V`.**
For `α` supported on `H^# = sharpImage H`, the Sibley Dade image `α^τ = hyp.tau α` vanishes on the
`(ticVdiff h46)`-exceptional set `V`.  Since `α^τ = dadeIntegralCharacterMap hyp.dade …` is a genuine
Dade image, it vanishes off `conjugatesOfSet H^#` (`map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot`
via `dade_H_eq_bot`); and `V` is disjoint from `conjugatesOfSet H^# ⊆ conjugatesOfSet (K^G)` by
`ticVdiffV_not_mem_conjugatesOfSet_K` (using `h46.K = H`, so `H^# ⊆ K^G`).  This is the **anchor**
`hvanish` input of `inner_smul_chiFam_eq_zero_of_diff_vanishOnV`: with `α = η₁ − η̄₁`
(`Supp ⊆ H^#`, Peterfalvi (4.7)) it gives that `(η₁ − η̄₁)^τ` vanishes on `V`. -/
theorem tau_apply_eq_zero_of_mem_ticVdiffV
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V) :
    (hyp.tau α) v = 0 := by
  rw [SibleyDadeHypothesis.tau, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    hyp.dade _ hαsupp]
  refine OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
    hyp.dade.isDadeMap_dadeMap hyp.dade_H_eq_bot _ ?_
  intro hvconj
  have hbridge : sharpImage H ⊆ ((h46.K.map L.subtype : Subgroup G) : Set G) := by
    rw [hHK]; exact Set.sdiff_subset
  exact ticVdiffV_not_mem_conjugatesOfSet_K h46 hv (Group.conjugatesOfSet_mono hbridge hvconj)

/-- **(6.8.2.3) anchor, generic coherent-extension form: a difference of coherent images of two
`H^#`-supported-difference members vanishes on `V`.**  For *any* coherence `cS : IsCoherent hyp.tau S₁ H^#`
and members `η, η' ∈ S₁` whose difference `η − η'` is `H^#`-supported, the image difference
`cS.extension η − cS.extension η'` vanishes on the `(ticVdiff h46)`-exceptional set `V`: the coherent
extension agrees with the Dade map on the supported lattice (`extends_on_supported`,
`cS.extension η − cS.extension η' = (η − η')^τ`), and `(η − η')^τ` vanishes on `V` by the anchor
`tau_apply_eq_zero_of_mem_ticVdiffV`.

This is the uniform `hvanish` input of `inner_smul_chiFam_eq_zero_of_diff_vanishOnV` for *every*
certain-type cross-orthogonality: with `η' = η̄` (the conjugate, equal degree so `η − η̄` is
`H^#`-supported) and `η^{τ₁} = ε·ξ`, it gives `ε·ξ − ε'·ξ'` vanishes on `V` — for `η ∈ Y` (seam-1)
*and* for an irreducible `η ∈ X` (the column–irreducible cross-orthogonality of the case-(B)
`X`-coherence glue). -/
theorem coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (cS : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ S₁) (hη' : η' ∈ S₁)
    (hsupp : (η - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V) :
    (cS.extension η - cS.extension η') v = 0 := by
  have htaud : cS.extension η - cS.extension η' = hyp.tau (η - η') := by
    rw [← map_sub]
    exact cS.extends_on_supported (η - η')
      ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη'), hsupp⟩
  rw [htaud]
  exact tau_apply_eq_zero_of_mem_ticVdiffV hyp h46 hHK hsupp hv

/-- **(6.8.2.3) anchor, `Y`-extension form** (specialization of
`coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV` to `S₁ = Y`).  All members of `Y = S(H')`
share the degree `|W₁|` (`Yset_apply_one`), so `η − η'` is `H^#`-supported
(`sMember_diffSupport_of_charValue_eq`).  This is the `hvanish` input of the seam-1 disjointness
machine with `η' = η̄`, `η^{τ₁} = ε·ξ`. -/
theorem coherentYset_extension_diff_apply_eq_zero_of_mem_ticVdiffV
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V) :
    (hyp.coherentYset.extension η - hyp.coherentYset.extension η') v = 0 :=
  coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV hyp h46 hHK hyp.coherentYset hη hη'
    (hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη')
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη').symm)) hv

/-- **The (6.8.2.3) disjointness machine** (modulo the anchor).  For orthonormal `ξ`, `ξ' ∈ ±Irr(G)`
and `c ≠ 0`, if the two-irreducible difference `c·ξ − c'·ξ'` vanishes on `V` (the **anchor**), then
`⟨c·ξ, ω^σ⟩ = 0` for every `σ`-image `ω^σ = chiFam pq`.  Chains the four disjointness bricks:
`sigmaNC_le_two_of_inner_chiFam` (`NC ≤ 2`) → `sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt`
(`grid_eq_zero`, all `σ`-coefficients vanish since `2 < min(w₁, w₂)`) →
`inner_eq_zero_of_smul_sub_smul_orthogonal` (extract `⟨ξ, ω^σ⟩ = 0` from `⟨c·ξ − c'·ξ', ω^σ⟩ = 0`,
integrality `⟨ξ, ω^σ⟩ ∈ ℤ`).

This is Peterfalvi (5.3.b) for the certain-type column families: with `c·ξ = Y = cY.extension η₁`
and `c·ξ − c'·ξ' = (η₁ − η̄₁)^τ`, it gives `⟨Y, certainTypeOmegaSigma⟩ = 0`, the seam-1 `hXorth`
input of the capstone `per_constituent_Y_eq_smul`.  Only the anchor `(η₁ − η̄₁)^τ` vanishes on `V`
(the structural `V ∩ dadeSupport = ∅`) remains to be supplied. -/
theorem inner_smul_chiFam_eq_zero_of_diff_vanishOnV
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication hyp)
    {ξ ξ' : ClassFunction G ℂ} (hξZ : ξ ∈ ZIrr G) (hξ1 : ClassFunction.inner ξ ξ = 1)
    (hξ'Z : ξ' ∈ ZIrr G) (hξ'1 : ClassFunction.inner ξ' ξ' = 1)
    (hξξ' : ClassFunction.inner ξ ξ' = 0)
    {c c' : ℂ} (hc : c ≠ 0)
    (hvanish : ∀ v ∈ hyp.V, (c • ξ - c' • ξ') v = 0)
    (hmin : 2 < min (Nat.card hyp.W1) (Nat.card hyp.W2))
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    ClassFunction.inner (c • ξ) (hyp.chiFam hVeq app pq) = 0 := by
  -- `NC(ψ) ≤ 2` where `ψ = c•ξ − c'•ξ'`.
  have hNC : hyp.sigmaNC hVeq app (c • ξ - c' • ξ') ≤ 2 := by
    refine sigmaNC_le_two_of_inner_chiFam hyp hVeq app hξZ hξ1 hξ'Z hξ'1 (fun pq' hpq' => ?_)
    by_contra hcon
    push Not at hcon
    refine hpq' ?_
    change ClassFunction.inner (c • ξ - c' • ξ') (hyp.chiFam hVeq app pq') = 0
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hcon.1, hcon.2, mul_zero, mul_zero, sub_zero]
  -- All `σ`-coefficients vanish (`grid_eq_zero`, `NC < min`).
  have hpsi : ClassFunction.inner (c • ξ - c' • ξ') (hyp.chiFam hVeq app pq) = 0 :=
    sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt hyp hVeq app hvanish (lt_of_le_of_lt hNC hmin) pq
  -- Extract `⟨ξ, chiFam pq⟩ = 0`, then `⟨c•ξ, chiFam pq⟩ = 0`.
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hξZ ((hyp.chiFam_spec hVeq app).2.1 pq)
  have hθ : ClassFunction.inner (hyp.chiFam hVeq app pq) (hyp.chiFam hVeq app pq) = 1 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  rw [ClassFunction.inner_smul_left,
    inner_eq_zero_of_smul_sub_smul_orthogonal hξ1 hθ hξξ' hm hc hpsi, mul_zero]

/-- **Coherent image of an irreducible member is `±` an irreducible (generic form).**  Generalizes
`coherentYset_extension_eq_zsmul_irreducible` to any coherence `cS : IsCoherent τ S₁ A`: an
irreducible member `η ∈ S₁` has `cS.extension η = ε·ξ` for `ε = ±1`, `ξ ∈ Irr G` (the image is
norm-`1` in `ZIrr G`, `exists_zsmul_irreducibleCharacter_of_inner_self_one`, Peterfalvi (5.9.a)). -/
theorem coherent_extension_eq_zsmul_irreducible
    {S₁ : Set (ClassFunction ↥L ℂ)} {A : Set ↥L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    (cS : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A)
    {η : ClassFunction ↥L ℂ} (hirr : IsIrreducibleCharacter η) (hη : η ∈ S₁) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧ cS.extension η = ε • (ξ : ClassFunction G ℂ) := by
  have hηnorm : ClassFunction.inner η η = 1 := by
    have h := irreducibleCharacter_inner (⟨η, hirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηspan : η ∈ OddOrder.Peterfalvi.S07.zSpan S₁ := Submodule.subset_span hη
  have hextnorm : ClassFunction.inner (cS.extension η) (cS.extension η) = 1 := by
    rw [cS.extension_inner_eq η η hηspan hηspan, hηnorm]
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one (cS.extension_mem_ZIrr η hηspan) hextnorm

/-- **(6.8.2.3) seam-1 orthogonality, generic coherent form `⟨η^{τ₁}, ω_{ij}^σ⟩ = 0`.**  For *any*
coherence `cS : IsCoherent hyp.tau S₁ H^#` and two irreducible members `η, η' ∈ S₁` with `⟨η, η'⟩ = 0`
and `η − η'` `H^#`-supported, the image `cS.extension η` is orthogonal to every certain-type `σ`-image
`ω_{ij}^σ = certainTypeOmegaSigma h46 χ₂ i`.

Writing `η^{τ₁} = ε·ξ`, `η'^{τ₁} = ε'·ξ'` (`coherent_extension_eq_zsmul_irreducible`), the images are
orthonormal (`⟨ξ, ξ'⟩ = 0` from `extension_inner_eq` + `⟨η, η'⟩ = 0`), and the difference
`ε·ξ − ε'·ξ' = η^{τ₁} − η'^{τ₁}` vanishes on `V`
(`coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV`, the anchor); the disjointness machine
`inner_smul_chiFam_eq_zero_of_diff_vanishOnV` then gives `⟨ε·ξ, ω_{ij}^σ⟩ = 0`
(`ω_{ij}^σ = chiFam P_{ij}`).  Instantiating `η' = η̄` (`⟨η, η̄⟩ = 0`, `η − η̄` `H^#`-supported by equal
degree) covers both the `Y`-anchor (seam-1) and an irreducible `X`-member (the column–irreducible
cross-orthogonality of the case-(B) `X`-coherence glue). -/
theorem inner_coherent_extension_certainTypeOmegaSigma_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (cS : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ S₁) (hη' : η' ∈ S₁)
    (hηirr : IsIrreducibleCharacter η) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η η' = 0)
    (hsupp : (η - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ClassFunction.inner (cS.extension η)
      (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i) = 0 := by
  obtain ⟨ε, ξ, hε, hηext⟩ := coherent_extension_eq_zsmul_irreducible cS hηirr hη
  obtain ⟨ε', ξ', hε', hη'ext⟩ := coherent_extension_eq_zsmul_irreducible cS hη'irr hη'
  have hεC : (ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hε'C : (ε' : ℂ) ≠ 0 := by rcases hε' with h | h <;> simp [h]
  have hηextC : cS.extension η = (ε : ℂ) • (ξ : ClassFunction G ℂ) := by
    rw [hηext, Int.cast_smul_eq_zsmul]
  have hη'extC : cS.extension η' = (ε' : ℂ) • (ξ' : ClassFunction G ℂ) := by
    rw [hη'ext, Int.cast_smul_eq_zsmul]
  have hee0 : ClassFunction.inner (cS.extension η) (cS.extension η') = 0 := by
    rw [cS.extension_inner_eq η η' (Submodule.subset_span hη) (Submodule.subset_span hη'), hee]
  have hξξ' : ClassFunction.inner (ξ : ClassFunction G ℂ) (ξ' : ClassFunction G ℂ) = 0 := by
    rw [hηextC, hη'extC, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast] at hee0
    rcases mul_eq_zero.mp hee0 with h | h
    · exact absurd h hεC
    · exact (mul_eq_zero.mp h).resolve_left hε'C
  have hξZ : (ξ : ClassFunction G ℂ) ∈ ZIrr G := ξ.2.mem_ZIrr
  have hξ'Z : (ξ' : ClassFunction G ℂ) ∈ ZIrr G := ξ'.2.mem_ZIrr
  have hξ1 : ClassFunction.inner (ξ : ClassFunction G ℂ) (ξ : ClassFunction G ℂ) = 1 := by
    have h := irreducibleCharacter_inner_eq_ite ξ ξ; rwa [if_pos rfl] at h
  have hξ'1 : ClassFunction.inner (ξ' : ClassFunction G ℂ) (ξ' : ClassFunction G ℂ) = 1 := by
    have h := irreducibleCharacter_inner_eq_ite ξ' ξ'; rwa [if_pos rfl] at h
  have hvanish : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      ((ε : ℂ) • (ξ : ClassFunction G ℂ) - (ε' : ℂ) • (ξ' : ClassFunction G ℂ)) v = 0 := by
    intro v hv
    have h := coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV hyp h46 hHK cS hη hη' hsupp hv
    rwa [hηextC, hη'extC] at h
  have hmin : 2 < min (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W2
    omega
  rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam, hηextC]
  exact inner_smul_chiFam_eq_zero_of_diff_vanishOnV (OddOrder.Peterfalvi.S06.ticVdiff h46) rfl
    (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46) hξZ hξ1 hξ'Z hξ'1 hξξ' hεC hvanish
    hmin _

/-- **(6.8.2.3) seam-1 orthogonality `⟨η^{τ₁}, ω_{ij}^σ⟩ = 0`** (Y-anchor specialization of
`inner_coherent_extension_certainTypeOmegaSigma_eq_zero`).  For distinct `Y`-anchors `η ≠ η' ∈ Y`,
`η^{τ₁} = coherentYset.extension η ⊥ ω_{ij}^σ`.  `⟨η, η'⟩ = 0` (distinct `Y`-irreducibles) and
`η − η'` is `H^#`-supported (equal degree `|W₁|`).  This is the `hXorth` input of
`per_constituent_Y_eq_smul`. -/
theorem inner_coherentYset_extension_certainTypeOmegaSigma_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η ≠ η')
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ClassFunction.inner (hyp.coherentYset.extension η)
      (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i) = 0 := by
  refine inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK hyp.coherentYset hη hη'
    (hyp.isIrreducibleCharacter_of_mem_Yset hη) (hyp.isIrreducibleCharacter_of_mem_Yset hη') ?_ ?_ χ₂ i
  · have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at h
    simpa using h
  · exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη')
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη').symm)

/-- **(6.8.2.3) seam-1, `R(μ_j)`-family form: `Y^{τ₁} ⊥ R(μ_j)`.**  For distinct `Y`-anchors
`η ≠ η' ∈ Y`, the image `η^{τ₁}` is orthogonal to every member of the reducible image family
`R(μ_j) = {±δ_j ω_{ij}^σ}` (`certainTypeRImage`, Peterfalvi (5.2.d)/(5.3.b)).  Each `R(μ_j)`-member is
a signed `σ`-image `±δ_j · certainTypeOmegaSigma h46 χ₂⁽ʼ⁾ i`, so this is the seam-1 orthogonality
`inner_coherentYset_extension_certainTypeOmegaSigma_eq_zero` scaled by the sign.

Summed over the family (`inner_X_eq_zero_of_orthogonal_imageSet`) this is the `R(μ_j) ⊥ Y^{τ₁}`
input `hXorth` of `per_constituent_Y_eq_smul` for the reducible certain-type decomposition
`certainTypeR`. -/
theorem inner_coherentYset_extension_certainTypeRImage_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η ≠ η')
    (χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ)
    (p : Bool × Fin (Nat.card h46.W1)) :
    ClassFunction.inner (hyp.coherentYset.extension η)
      (OddOrder.Peterfalvi.S06.certainTypeRImage h46 χ₂ χ₂' p) = 0 := by
  obtain ⟨b, i⟩ := p
  cases b <;>
    simp only [OddOrder.Peterfalvi.S06.certainTypeRImage,
      OddOrder.RepresentationTheory.inner_smul_right]
  · rw [inner_coherentYset_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK hη hη' hne χ₂ i,
      mul_zero]
  · rw [inner_coherentYset_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK hη hη' hne χ₂' i,
      mul_zero]

/-- **(6.8.2.3) seam-1, decomposition form: `⟨D.X, Y^{τ₁}⟩ = 0` (the `hXorth` for `per_constituent`).**
For any `(5.4)` decomposition `D` whose image-family members are covered by the reducible `R(μ_j)` set
(`himg`: every `α ∈ D.imageFamily.imageSet` is some `certainTypeRImage h46 χ₂ χ₂' p`), the
`R(χᵢ)`-part `D.X ∈ ℤ[R(μ_j)]` is orthogonal to the `Y`-coherence image `η^{τ₁}` (for distinct
anchors `η ≠ η' ∈ Y`).  This is `inner_X_Y_eq_zero_of_orthogonal` fed by the `R(μ_j)`-member
orthogonality `inner_coherentYset_extension_certainTypeRImage_eq_zero`.

This is the capstone-ready `hXorth` input of `per_constituent_Y_eq_smul`: the certain-type
decomposition `certainTypeDecompositionDa` (via `ofProjection (certainTypeR …)`) has
`imageFamily.imageSet = Finset.univ.image (certainTypeRImage h46 χ₂ χ₂⁻¹)`, so `himg` is discharged at
the capstone by `Finset.mem_image` (the coverage form avoids a `DecidableEq (ClassFunction G ℂ)`
obligation here). -/
theorem inner_decomposition_X_coherentYset_extension_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η ≠ η')
    {χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ ψ : ClassFunction ↥L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ)
    (himg : ∀ α ∈ D.imageFamily.imageSet,
      ∃ p, OddOrder.Peterfalvi.S06.certainTypeRImage h46 χ₂ χ₂' p = α) :
    ClassFunction.inner D.X (hyp.coherentYset.extension η) = 0 := by
  refine inner_X_Y_eq_zero_of_orthogonal D ?_
  intro α hα
  obtain ⟨p, rfl⟩ := himg α hα
  exact inner_coherentYset_extension_certainTypeRImage_eq_zero hyp h46 hHK hη hη' hne χ₂ χ₂' p

/-- **(6.8.2.3) seam-1, capstone-facing form: `⟨D.X, η₁^{τ₁}⟩ = 0` from `η₁ ∈ Y` alone.**
Specializes `inner_decomposition_X_coherentYset_extension_eq_zero` to the textbook choice of the
distinct second anchor `η' = η̄₁` (the complex conjugate): `η̄₁ ∈ Y` (`Yset_closedUnderConjugate`)
and `η₁ ≠ η̄₁` since `Y` has no real characters (`Yset_hasNoRealCharacters`, Peterfalvi (5.2.a): an
odd-order group has no nontrivial real irreducible).  So the `hXorth` `⟨D.X, η₁^{τ₁}⟩ = 0` needs only
`η₁ ∈ Y` — the second anchor is internalized.  This is the exact `hXorth` the capstone supplies to
`per_constituent_Y_eq_smul` for `Y = η₁^{τ₁}`. -/
theorem inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ ψ : ClassFunction ↥L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ)
    (himg : ∀ α ∈ D.imageFamily.imageSet,
      ∃ p, OddOrder.Peterfalvi.S06.certainTypeRImage h46 χ₂ χ₂' p = α) :
    ClassFunction.inner D.X (hyp.coherentYset.extension η₁) = 0 := by
  have hconj : η₁.conj ∈ hyp.Yset := hyp.Yset_closedUnderConjugate hη₁
  have hne : η₁ ≠ η₁.conj := fun heq =>
    hyp.Yset_hasNoRealCharacters.not_mem_of_isReal (heq.symm : η₁.IsReal) hη₁
  exact inner_decomposition_X_coherentYset_extension_eq_zero hyp h46 hHK hη₁ hconj hne D himg

/-- **(6.8.2) case-(B) `X`–`Y` / `X`–`X_irr` mixed orthogonality for a column `μ_j`, generic form.**
The `(4.9)` certain-type coherent extension of a column sum is `ν(μ_j) = δ_j ∑_i ω_{ij}^σ`
(`certainTypeExtension_columnSum`), a `ℤ`-combination of `σ`-images; so for *any* coherence
`cS : IsCoherent hyp.tau S₁ H^#` and irreducible member `χ ∈ S₁` (with `χ̄ ∈ S₁`, `⟨χ, χ̄⟩ = 0`,
`χ − χ̄` `H^#`-supported), the generic seam-1 `inner_coherent_extension_certainTypeOmegaSigma_eq_zero`
gives `⟨ν(μ_j), cS.extension χ⟩ = 0` directly.  This is the **mixed-inner input** of the case-(B)
`X`-coherence glue, uniformly for `χ ∈ Y` (column–`Y`) *and* an irreducible `χ ∈ X` (column–irreducible).
**No per-constituent pinning needed.** -/
theorem inner_certainTypeExtension_columnSum_coherent_extension_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (cS : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ S₁) (hχconj : χ.conj ∈ S₁)
    (hχirr : IsIrreducibleCharacter χ)
    (hee : ClassFunction.inner χ χ.conj = 0)
    (hsupp : (χ - χ.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    ClassFunction.inner (OddOrder.Peterfalvi.S06.certainTypeExtension h46
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂))
      (cS.extension χ) = 0 := by
  have hsum : ClassFunction.inner
      (∑ i, OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i) (cS.extension χ) = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK cS hχ hχconj hχirr
        hχirr.conj hee hsupp χ₂ i, star_zero]
  rw [OddOrder.Peterfalvi.S06.certainTypeExtension_columnSum, ← Int.cast_smul_eq_zsmul ℂ,
    ClassFunction.inner_smul_left, hsum, mul_zero]

/-- **(6.8.2) case-(B) column–`Y` mixed orthogonality** (`Y`-specialization of
`inner_certainTypeExtension_columnSum_coherent_extension_eq_zero`).  `⟨ν(μ_j), η^{τ₁}⟩ = 0` for
`η ∈ Y`: the conjugate `η̄ ∈ Y` (`Yset_closedUnderConjugate`), `⟨η, η̄⟩ = 0` and `η − η̄` is
`H^#`-supported (equal degree).  The column-`Y` `hmixed` input of `coherentXunionYset_caseB_of_glued`. -/
theorem inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    ClassFunction.inner (OddOrder.Peterfalvi.S06.certainTypeExtension h46
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂))
      (hyp.coherentYset.extension η) = 0 := by
  have hηirr := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hconj : η.conj ∈ hyp.Yset := hyp.Yset_closedUnderConjugate hη
  have hne : η ≠ η.conj := fun heq =>
    hyp.Yset_hasNoRealCharacters.not_mem_of_isReal (heq.symm : η.IsReal) hη
  have hee : ClassFunction.inner η η.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η.conj, hηirr.conj⟩ : IrreducibleCharacter ↥L)
    rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at h
    simpa using h
  exact inner_certainTypeExtension_columnSum_coherent_extension_eq_zero hyp h46 hHK
    hyp.coherentYset hη hconj hηirr hee
    (hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hconj)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hconj).symm)) χ₂

/-- **(6.8.2.3) per-constituent pinning, certain-type form: `Dᵢ.Y = aᵢ·η₁^{τ₁}`.**  The certain-type
specialization of `per_constituent_Y_eq_smul`: for a family of `(5.4)` decompositions
`D : ι → CharacterPsiDecomposition τ (χ i) (aᵢ·η₁)` whose image families are covered by the reducible
`R(μ_j)` sets (`himg`), the (6.8.2.2) aggregate (`hagg`/`hsq`/`hXaggorth`) plus the per-step coefficient
data (`hbi`) pin each `Dᵢ.Y = aᵢ·η₁^{τ₁}` (`η₁^{τ₁} = coherentYset.extension η₁`).

The three structural inputs of `per_constituent_Y_eq_smul` are discharged internally: `hηnorm`
(`η₁` irreducible, `Y ⊆ Irr L`), `hYY` (the `Y`-coherence isometry `extension_inner_eq`), and the
seam-1 `hXorth` (`inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset`, needing only
`η₁ ∈ Y`).  Only the (6.8.2.2)-aggregate data remains for the capstone. -/
theorem certainType_per_constituent_Y_eq_smul
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {ι : Type*} (s : Finset ι) {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ : ι → ClassFunction ↥L ℂ} {a : ι → ℕ}
    (D : (i : ι) → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ (χ i) (a i • η₁))
    {χ₂ χ₂' : ι → (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (himg : ∀ i ∈ s, ∀ α ∈ (D i).imageFamily.imageSet,
      ∃ p, OddOrder.Peterfalvi.S06.certainTypeRImage h46 (χ₂ i) (χ₂' i) p = α)
    {Xagg : ClassFunction G ℂ} {b : ι → ℤ} {n : ℤ}
    (hXaggorth : ClassFunction.inner Xagg (hyp.coherentYset.extension η₁) = 0)
    (hagg : Xagg - (n : ℂ) • hyp.coherentYset.extension η₁
      = ∑ i ∈ s, ((a i : ℤ) : ℂ) • ((D i).X - (D i).Y))
    (hsq : ∑ i ∈ s, ((a i : ℤ)) ^ 2 = n)
    (hbi : ∀ i ∈ s, ClassFunction.inner (D i).Y (hyp.coherentYset.extension η₁) = (b i : ℂ))
    (i : ι) (hi : i ∈ s) (hpos : 0 < a i) :
    (D i).Y = (a i : ℂ) • hyp.coherentYset.extension η₁ := by
  have hηirr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηnorm : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L) (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hYY : ClassFunction.inner (hyp.coherentYset.extension η₁)
      (hyp.coherentYset.extension η₁) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η₁ η₁
      (Submodule.subset_span hη₁) (Submodule.subset_span hη₁)]
    exact hηnorm
  exact per_constituent_Y_eq_smul s D hηnorm hYY hXaggorth hagg hsq
    (fun j hj => inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset
      hyp h46 hHK hη₁ (D j) (himg j hj)) hbi i hi hpos

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
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset W2, ν x = cX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = cY.extension y)
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
    cX cY ν hagreeX hagreeY
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

/-- **(6.8.2.3) column constituent decomposition (`Ind^L_H`-form).**  The (5.4) decomposition data
for a reducible column constituent `μ_j`, recast from `certainTypeDecompositionDa` (whose
`χ`-component is `columnSum χ₂`) to the `Ind^L_H`-form `induce H (Res_H μ_{0j})` via the (4.5.a)
transport `columnSum_eq_induce_H` (`h46.K = H`).  This puts the column decompositions in the same
`Ind^L_H θ`-indexed shape as the irreducible constituents
(`decompositionDaFromDadeOfDiff h46.dade0 h46.dade0.hconj`), so a single per-`φ` family
(`{θ : Irr H // 0 < aθ}`) feeds `per_constituent_Y_eq_smul` against the one map
`τ = dadeIntegralCharacterMap h46.dade0 h46.tau` (which ignores its isometry-data argument). -/
noncomputable def columnConstituentDecomposition
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hμη₁supp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (sharpImage H ∪ OddOrder.GroupTheory.conjClassSetIn L h46.tic.V) L)
    (htau1_mema : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    (hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (ClassFunction.induce H
        (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)))
      (a • η₁) := by
  rw [← columnSum_eq_induce_H h46 hHK χ₂]
  exact OddOrder.Peterfalvi.S06.certainTypeDecompositionDa h46 hχ₂ hdeg hμη₁supp htau1_mema hχψ hχbarψ

/-- **(6.8.2.3) reducible `R(μ_j)` image family, retargeted to `hyp.tau`.**  The certain-type column
image family `certainTypeR` is built against the *enlarged* certain-type map
`τ_enl = dadeIntegralCharacterMap h46.dade0 h46.tau` (the only map whose isometry data supports the
`σ`-image construction).  Its `imageSet`/`mem_ZIrr`/`orthonormal` are pure facts about the σ-image
*set* (`R(μ_j) ⊆ ℤ[Irr G]`, orthonormal), independent of the Dade map; only the image equation
`(μ_j − μ̄_j)^τ = ∑ R(μ_j)` mentions `τ`.

This rebuilds the family against the Sibley–Dade map `hyp.tau`, reusing the three map-independent
fields and transferring the image equation along the `H^#`-agreement `hmapagree`
(`(μ_j − μ̄_j)^{hyp.tau} = (μ_j − μ̄_j)^{τ_enl}`, valid since `μ_j − μ̄_j` is `H^#`-supported in case c2
`K = H` and both maps coincide there).  This puts the column `R(μ_j)` and the irreducible Dade
families `dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade hyp.hconj` in the *same* map `hyp.tau`,
the single `τ` of the per-`φ` family.  `hmapagree` is supplied at capstone wiring (as for
`certainTypeSet_isCoherent_tau`). -/
noncomputable def columnRFamilyTau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) where
  imageSet := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).imageSet
  mem_ZIrr := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).mem_ZIrr
  orthonormal := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).orthonormal
  image_eq := by
    rw [hmapagree]; exact (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).image_eq

/-- **(6.8.2.3) column constituent decomposition for `hyp.tau`.**  The (5.4) decomposition data for a
reducible column `μ_j = columnSum χ₂` against the Sibley–Dade map `hyp.tau`, built by `ofProjection`
from the retargeted family `columnRFamilyTau` and `hyp.tau`'s `H^#`-inner-preservation
(`dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade hyp.hconj`).  This is the column branch
of the per-`φ` family living in the *same* `τ = hyp.tau` as the irreducible constituents
(`decompositionDaFromDadeOfDiff hyp.dade hyp.hconj`).  The column differences `μ_j − μ̄_j`,
`μ_j − a·η₁` are `H^#`-supported (`hSdiff`, case c2 `K = H`); `hmapagree` transfers the family's image
equation; both are discharged at capstone wiring. -/
noncomputable def columnDecompositionTau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
    (hSdiff : ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    (hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) (a • η₁) := by
  have hχχbar : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj = 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner,
      if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂).symm]
  exact OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (columnRFamilyTau hyp h46 hχ₂ hdeg hmapagree) hyp.tau
    (fun _φ _ζ hφ hζ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
        hyp.dade hyp.hconj hSdiff hφ hζ)
    rfl htau1_mema hχψ hχbarψ hχχbar

/-- **(6.8.2.3) irreducible constituent decomposition for `hyp.tau`.**  The (5.4) decomposition data
for an irreducible induced constituent `Ind^L_H θ` (non-column `θ`), via `decompositionDaFromDadeOfDiff`
for the Sibley–Dade datum `hyp.dade` (which carries `hyp.hconj : HConjInvariant`).  Since
`hyp.tau = dadeIntegralCharacterMap hyp.dade (hyp.dade.fullDadeIsometryData hyp.hconj)`, this lands
directly in `hyp.tau` — the *same* map as the column decompositions (`columnDecompositionTau`), so
both branches feed one per-`φ` family.  The per-`θ` orthonormality/support/`ZIrr` hypotheses are
discharged at the family (from the §5 X-member machinery, as in the case-A chain). -/
noncomputable def irreducibleDecompositionTau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (θ : IrreducibleCharacter ↥H)
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hreal : ¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    (hdiffsupp : ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
        - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hdiffasupp : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχχbar' : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (a • η₁) :=
  OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp.dade hyp.hconj
    ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ hreal hdiffsupp hdiffasupp htau1_mema
    hχaχ1 hχbaraχ1 hχχbar'

/-- **(6.8.2.3) per-constituent anchored image, mixed family (assembly skeleton).**  Given the per-`φ`
decomposition family `D` (one (5.4) decomposition `CharacterPsiDecomposition hyp.tau (χ i) (aᵢ·η₁)`
per constituent — built by dispatching `columnDecompositionTau` / `irreducibleDecompositionTau`), with
`(D i).tau1 = hyp.tau` (`htau1`, immediate for both branches), the (6.8.2.2) aggregate
(`hagg`/`hsq`/`hXaggorth`), and the per-step `R(χᵢ) ⊥ Y₀` / coefficient data (`hXorth`/`hbi`), the
pinning `per_constituent_Y_eq_smul` forces `(D i).Y = aᵢ·Y₀`, and the decomposition image equation
`(D i).tau1_image` then gives the **(6.8.2.3) anchored image**
`(χᵢ − aᵢ·η₁)^{hyp.tau} = (D i).X − aᵢ·Y₀` (`Y₀ = cY.extension η₁`).

The `Y`-coherence `cY` is arbitrary (not fixed to `hyp.coherentYset`): the case-(B) aggregate
`exists_decomposition_caseB` threads the witness `cY` of `exists_Ycoherence_hgood_caseB`, which is
`hyp.coherentYset` in the main branch but a *swapped* witness in the `|Y| = 2` edge.  All facts used
(`extension_inner_eq`, the norm-`1` anchor) hold for any coherence on `hyp.Yset`.

This is the route-independent (6.8.2.3) core, parametric in the family `D`; only the family
construction (the constituent dispatch + per-`θ` hypothesis discharge) remains for the capstone. -/
theorem per_phi_anchored_image
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {ι : Type*} (s : Finset ι) {χ : ι → ClassFunction ↥L ℂ} {a : ι → ℕ}
    (D : (i : ι) → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau (χ i) (a i • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg : ClassFunction G ℂ} {b : ι → ℤ} {n : ℤ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hagg : Xagg - (n : ℂ) • cY.extension η₁
      = ∑ i ∈ s, ((a i : ℤ) : ℂ) • ((D i).X - (D i).Y))
    (hsq : ∑ i ∈ s, ((a i : ℤ)) ^ 2 = n)
    (hXorth : ∀ i ∈ s, ClassFunction.inner (D i).X (cY.extension η₁) = 0)
    (hbi : ∀ i ∈ s,
      ClassFunction.inner (D i).Y (cY.extension η₁) = (b i : ℂ))
    (i : ι) (hi : i ∈ s) (hpos : 0 < a i) :
    hyp.tau (χ i - a i • η₁)
      = (D i).X - (a i : ℂ) • cY.extension η₁ := by
  have hηirr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηnorm : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L) (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hYY : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by
    rw [cY.extension_inner_eq η₁ η₁
      (Submodule.subset_span hη₁) (Submodule.subset_span hη₁)]
    exact hηnorm
  have hY := per_constituent_Y_eq_smul s D hηnorm hYY hXaggorth hagg hsq hXorth hbi i hi hpos
  have h1 : hyp.tau (χ i - a i • η₁) = (D i).X - (D i).Y := by
    have h := (D i).tau1_image
    rw [htau1 i] at h
    exact h
  rw [h1, hY]

/-- **(6.8.2.3) column constituent decomposition for `hyp.tau`, `Ind^L_H`-form.**  The
family-ready column branch: `columnDecompositionTau` (whose `χ`-component is `columnSum χ₂`) recast to
the `Ind^L_H θ`-form `induce H (Res_H μ_{0j})` via the (4.5.a) transport `columnSum_eq_induce_H`
(`h46.K = H`).  This matches the per-`φ` family's `χ`-component `induce H i.val` (the column index
`θ = ⟨Res_H μ_{0j}, _⟩`), so it slots directly into the dispatch alongside
`irreducibleDecompositionTau`. -/
noncomputable def columnConstituentDecompositionTau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
    (hSdiff : ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    (hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (ClassFunction.induce H
        (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)))
      (a • η₁) := by
  rw [← columnSum_eq_induce_H h46 hHK χ₂]
  exact columnDecompositionTau hyp h46 hχ₂ hdeg hmapagree hSdiff htau1_mema hχψ hχbarψ

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

/-- **(6.8.2) case-(B), `μ_j ∉ S(A)` for `W₂ ≤ A`** (filtration generalization of
`columnSum_notMem_SsubFiltration`).  Since `S(A) ⊆ S(W₂)` whenever `W₂ ≤ A`
(`SsubFiltration_antitone`: a larger kernel constraint gives a smaller filtration set) and the column
`μ_j = columnSum h46 χ₂` (`χ₂ ≠ 1`) already lies outside `S(W₂)`
(`columnSum_notMem_SsubFiltration`), it lies outside `S(A)` too.

This is the **break-irreducibility ingredient** for the (6.3) induction at a filtration level
`A ⊇ W₂`: the only reducible members of `S` are the `w₂ − 1` certain-type columns, so on any `S(A)`
with `W₂ ≤ A` every member is irreducible — exactly the `hψirr` the (5.6) member-family bound
(`sSubFiltration_sum_le_two_psi_caseB`) demands of the break. -/
theorem SibleyDadeHypothesis.columnSum_notMem_SsubFiltration_of_le
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {A : Subgroup ↥L} (hAW2 : h46.W2 ≤ A)
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∉ hyp.SsubFiltration A :=
  fun hmem => hyp.columnSum_notMem_SsubFiltration h46 hHK hχ₂
    (hyp.SsubFiltration_antitone hAW2 hmem)

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

/-- **(6.8.2.3) constituent weight = degree (central multiplicity).**  For an irreducible `θ` of `H`
whose central restriction is `Res^H_Z θ = θ(1)·φ` (`certainType_central_restriction`, `Z = W₂.subgroupOf H`
central), the multiplicity of `φ` in `Res^H_Z θ` is `θ(1)`:
`⟨φ, Res^H_Z θ⟩ = ⟨φ, θ(1)·φ⟩ = θ(1)·⟨φ, φ⟩ = θ(1)` (with `θ(1)` real, `= (d : ℂ)` a positive integer
by `irreducibleCharacter_apply_one_eq_pos_natCast`, so `star (θ(1)) = θ(1)`).

This is the weight reconciliation `aθ = θ(1)` for the (6.8.2.3) `αθ`-aggregate: the multiplicity
`aθ = ⟨φ, Res θ⟩` (`sum_smul_constituent_diff_eq`) equals the degree ratio `θ(1) = χθ(1)/|W₁|` used in
the per-constituent decomposition, so the two index conventions coincide on the constituents. -/
theorem inner_central_restrict_eq_apply_one [Fintype ↥H]
    (θ : IrreducibleCharacter ↥H) {W2 : Subgroup ↥L}
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥(W2.subgroupOf H) ℂ} (hφ : IsIrreducibleCharacter φ)
    (hres : ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ)
      = (θ : ClassFunction ↥H ℂ) 1 • φ) :
    ClassFunction.inner φ
        (ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ))
      = (θ : ClassFunction ↥H ℂ) 1 := by
  have hφφ : ClassFunction.inner φ φ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨φ, hφ⟩ : IrreducibleCharacter ↥(W2.subgroupOf H))
      (⟨φ, hφ⟩ : IrreducibleCharacter ↥(W2.subgroupOf H))
    rwa [if_pos rfl] at h
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  rw [hres, OddOrder.RepresentationTheory.inner_smul_right, hφφ, mul_one, hd, star_natCast]

end OddOrder.Peterfalvi.S08
