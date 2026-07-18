/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedTransport
import OddOrder.Peterfalvi.S08_CaseBCoherence
import OddOrder.Peterfalvi.S06_CertainTypeCoherence

/-!
# S08_CaseBTransport

Prefix-split from `OddOrder.Peterfalvi.S08_CaseBCoherence2` (2000-line limit, issue 0103 第 2 パス).
-/

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
version of `orthogonal_tau_indW2_add_extension_caseB`: for *any* `Y`-coherence witness `cY` (e.g.
the
swapped witness from `exists_Ycoherence_hgood_caseB` in the `|Y| = 2` edge), the good value
`⟨α^τ, cY.extension η₁⟩ = −|H:Z|` makes `X := α^τ + |H:Z|·cY.extension η₁` orthogonal to the whole
family `{cY.extension η}` and lie in `ℤ[Irr G]`, giving `α^τ = X − |H:Z|·cY.extension η₁`.

The agreement `cY.extension η − cY.extension η₁ = (η − η₁)^τ` is `cY.extends_on_supported` +
`map_sub`
(inlined, since `cY` need not be `coherentYset`). -/
theorem SibleyDadeHypothesis.orthogonal_tau_indW2_add_extension_general_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) (hW2comm : W2 ≤ ⁅H, H⁆)
    [Invertible (Nat.card ↥W2 : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (_hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
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
(`φ` nontrivial linear), there is a `Y`-coherence witness `cY` and an `X ∈ ℤ[Irr G]` orthogonal to
the
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

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] in
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
theorem certainType_index_bounds (h : OddOrder.Peterfalvi.S06.Hypothesis ↥L) [Finite ↥L]
    (hW2cenK : h.W2 ≤ Subgroup.centralizer (↑h.K : Set ↥L))
    (hKW2 : ¬ h.K ≤ h.W2) :
    2 ≤ (h.W2.subgroupOf h.K).index ∧
    (h.W2.index : ℤ) < ((h.W2.subgroupOf h.K).index : ℤ) ^ 2 := by
  classical
  haveI : Fintype ↥L := Fintype.ofFinite _
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
`‖Ind^M_N φ‖² = |M : N|`.  Indeed `N ⊴ M` (central), conjugation acts trivially on `N`, so the
Mackey
restriction `|N|·Res_N(Ind^M_N φ) = ∑_{x∈M} φ^{x⁻¹} = |M|·φ` collapses; Frobenius reciprocity
`⟨Ind φ, Ind φ⟩ = ⟨φ, Res(Ind φ)⟩` then gives `|N|·‖Ind φ‖² = |M|`, i.e. `‖Ind φ‖² = |M:N|`.

This is the `∑ aᵢ² = |H : Z|` step of Peterfalvi (6.8.2.3) (`Z = W₂ ⊆ Z(H)`, applied with `M = ↥H`,
`N = W₂.subgroupOf H`): the squared multiplicities of `Ind^H_Z φ` sum to
`‖Ind^H_Z φ‖² = |H : Z|`. -/
theorem inner_induce_self_eq_index_of_le_center
    {M : Type*} [Group M] [Fintype M] [Invertible (Nat.card M : ℂ)]
    {N : Subgroup M} [Finite ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (hN : N ≤ Subgroup.center M)
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) :
    ClassFunction.inner (ClassFunction.induce N φ) (ClassFunction.induce N φ)
      = (N.index : ℂ) := by
  classical
  haveI : Fintype ↥N := Fintype.ofFinite _
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

end OddOrder.Peterfalvi.S08
