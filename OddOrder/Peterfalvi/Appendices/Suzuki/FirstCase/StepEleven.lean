/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTen
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal

/-!
# Peterfalvi Part II, Ch. II, step (11): `R = T × P` and the regular action

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (11), p. 111.

Step (11) sets `R` := the inverse image of `F` in `G` — the preimage of the
translation subgroup `emb(F) ⊴ C_G(P)/N` under the quotient map
`C_G(P) → C_G(P)/N`, pushed forward along `C_G(P) ↪ G` — and proves:

* `R = T × P`, with `T` a subgroup normalized by `C_Q(P)·C_W(P)` and
  `T ⋊ C_Q(P) ≅ F ⋊ F^*` (proved in `StepElevenSemidirect.lean`:
  `sInvertedTEquivField` + `fieldCoord_conj`);
* `C_Q(P)` acts regularly on `𝒜 − {P}`, where `𝒜` denotes the set of
  subgroups of `R` of order `p` which are not contained in `T`.

This file lays the **construction layer**: the definition `invImageF` of `R`
and its first structural facts (`R ≤ C_G(P)`, `P ≤ R`, membership transport
to the quotient).  The abelianity of `R`, the `T = [R, s]` decomposition and
the regularity claim land in subsequent commits (campaign issue 2053; proof
plan recorded there from the p. 111 reading).
-/

set_option autoImplicit false

open scoped Pointwise

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Step (11), the subgroup `R`** (p. 111): the inverse image of `F` in
`G`.  Concretely: the translation subgroup `emb(F)` of the affine near-field
model lives in the faithful quotient `C_G(P)/N`; `R` is its preimage under
the quotient map, pushed forward along `C_G(P) ↪ G`.  With `N = P`
(step (7)) this has order `p^{m+1} = |F|·p`. -/
noncomputable def invImageF {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F) : Subgroup G :=
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  (((MonoidHom.range model.emb).comap
      (QuotientGroup.mk'
        ((fc.toHypothesis.H.subgroupOf
          (Subgroup.centralizer (fc.P : Set G))).normalCore))).map
    (Subgroup.centralizer (fc.P : Set G)).subtype)

variable {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

/-- `R ≤ C_G(P)`: the inverse image consists of elements of `L = C_G(P)`. -/
theorem invImageF_le_centralizer :
    fc.invImageF model ≤ Subgroup.centralizer (fc.P : Set G) := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- `P ≤ R`: the base `p`-subgroup lies in the inverse image, because `P ≤ N`
(step (7) direction `P_le_kernelN`) is killed by the quotient map, and `1`
lies in the translation subgroup. -/
theorem P_le_invImageF : fc.P ≤ fc.invImageF model := by
  intro x hx
  have hxL : x ∈ Subgroup.centralizer (fc.P : Set G) := fc.P_le_centralizer hx
  refine ⟨⟨x, hxL⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
  obtain ⟨y, hyN, hyx⟩ := fc.P_le_kernelN hx
  have hye : y = (⟨x, hxL⟩ : ↥(Subgroup.centralizer (fc.P : Set G))) :=
    Subtype.ext hyx
  rw [← hye, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hyN]
  exact one_mem _

/-- Membership transport: an element of `C_G(P)` lies in `R` iff its class in
the faithful quotient is a translation (lies in `emb(F)`). -/
theorem mem_invImageF_iff {x : G}
    (hxL : x ∈ Subgroup.centralizer (fc.P : Set G)) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    x ∈ fc.invImageF model ↔
      QuotientGroup.mk'
        ((fc.toHypothesis.H.subgroupOf
          (Subgroup.centralizer (fc.P : Set G))).normalCore) ⟨x, hxL⟩ ∈
        MonoidHom.range model.emb := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hye : y = (⟨x, hxL⟩ : ↥(Subgroup.centralizer (fc.P : Set G))) :=
      Subtype.ext hyx
    rw [← hye]
    exact Subgroup.mem_comap.mp hy
  · intro h
    exact ⟨⟨x, hxL⟩, Subgroup.mem_comap.mpr h, rfl⟩

include model in
/-- **`st ∈ R`** (Part II, Ch. II (14), the remark "`Z₁ ⊂ T`"): both `s` and `t`
centralize `P`, and their images in `C_G(P)/N` are distinct involutions, so the
image of `st` is a translation (`mk_distinguishedInvolution_mul_t_mem_range_emb`)
— that is, `st` lies in the preimage `R` of `emb(F)`. -/
theorem distinguishedInvolution_mul_t_mem_invImageF :
    fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
      ∈ fc.invImageF model := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  have hsL : fc.toHypothesis.distinguishedInvolution
      ∈ Subgroup.centralizer (fc.P : Set G) :=
    fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V
  have htL : fc.toHypothesis.t ∈ Subgroup.centralizer (fc.P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (fc.toHypothesis.commute_t_of_mem_V (fc.P_le_V hx)).eq
  have hst : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
      ∈ Subgroup.centralizer (fc.P : Set G) := mul_mem hsL htL
  rw [fc.mem_invImageF_iff model hst]
  exact fc.mk_distinguishedInvolution_mul_t_mem_range_emb model hst

/-- `R` is normal in `C_G(P)`: the translation subgroup `emb(F)` is normal in the
quotient (`range_normal`), and normality pulls back along the quotient map. -/
theorem conj_mem_invImageF {c r : G}
    (hc : c ∈ Subgroup.centralizer (fc.P : Set G))
    (hr : r ∈ fc.invImageF model) : c * r * c⁻¹ ∈ fc.invImageF model := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  obtain ⟨y, hy, rfl⟩ := hr
  haveI hn : ((MonoidHom.range model.emb).comap
      (QuotientGroup.mk' ((fc.toHypothesis.H.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))).normalCore))).Normal :=
    model.range_normal.comap _
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, hn.conj_mem y hy ⟨c, hc⟩, rfl⟩

end FirstCaseHypothesis

/-- **A subgroup of `(F, +)` invariant under right multiplication by every unit is `⊥` or
`⊤`** (near-field division: `t = x·(x⁻¹·t)` for `x, t ≠ 0`).  This is the mechanism behind
step (11)'s "`C_Q(P)` acts transitively on `F^*`" collapse: any `C_G(P)`-invariant subgroup
of `R` strictly between `P` and `R` would project to a proper nonzero `F^*`-invariant
subgroup of `F`. -/
theorem addSubgroup_eq_bot_or_top_of_mul_units_mem {F : Type*} [NearFields.NearField F]
    (S : AddSubgroup F) (hS : ∀ x ∈ S, ∀ u : Fˣ, x * (u : F) ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  · refine Or.inr ?_
    have hex : ∃ x ∈ S, x ≠ (0 : F) := by
      by_contra hall
      push Not at hall
      refine h0 (le_antisymm (fun y hy => ?_) bot_le)
      rw [AddSubgroup.mem_bot]
      exact hall y hy
    obtain ⟨x, hxS, hx0⟩ := hex
    rw [eq_top_iff]
    intro t _
    by_cases ht : t = 0
    · rw [ht]; exact S.zero_mem
    · have hu : IsUnit (x⁻¹ * t) :=
        isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero hx0) ht)
      obtain ⟨u, hu⟩ := hu
      have hmem := hS x hxS u
      rwa [hu, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at hmem

/-- **Model-level transitivity collapse**: a subgroup of the affine quotient contained in
the translation subgroup `emb(F)` and invariant under `Q`-conjugation is `⊥` or all of
`emb(F)` — via `qEquiv_conj`, `Q ≅ F^*` acts on the nonzero translations exactly as right
multiplication, and `addSubgroup_eq_bot_or_top_of_mul_units_mem` applies to the additive
shadow.  This is the "`C_Q(P)` acts transitively on `F^*`" mechanism of step (11). -/
theorem conjInvariant_eq_bot_or_range_emb
    {G' Ω' : Type*} [Group G'] [MulAction G' Ω'] [Finite G']
    {hyp : NearFields.RankOneHypothesis G' Ω'} {F : Type*} [NearFields.NearField F]
    (model : NearFields.AffineNearFieldModel hyp F) {S : Subgroup G'}
    (hle : S ≤ MonoidHom.range model.emb)
    (hinv : ∀ q : ↥hyp.Q, ∀ z ∈ S, (q : G') * z * (q : G')⁻¹ ∈ S) :
    S = ⊥ ∨ S = MonoidHom.range model.emb := by
  classical
  -- the additive shadow of `S` in `F`
  set A : AddSubgroup F :=
    { carrier := {x | model.emb (Multiplicative.ofAdd x) ∈ S}
      zero_mem' := by
        change model.emb (Multiplicative.ofAdd 0) ∈ S
        rw [show Multiplicative.ofAdd (0 : F) = 1 from rfl, map_one]
        exact S.one_mem
      add_mem' := fun {a b} ha hb => by
        change model.emb (Multiplicative.ofAdd (a + b)) ∈ S
        rw [show Multiplicative.ofAdd (a + b)
            = Multiplicative.ofAdd a * Multiplicative.ofAdd b from rfl, map_mul]
        exact S.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        change model.emb (Multiplicative.ofAdd (-a)) ∈ S
        rw [show Multiplicative.ofAdd (-a) = (Multiplicative.ofAdd a)⁻¹ from rfl, map_inv]
        exact S.inv_mem ha } with hAdef
  have hAinv : ∀ x ∈ A, ∀ u : Fˣ, x * (u : F) ∈ A := by
    intro x hx u
    set q : ↥hyp.Q := (model.qEquiv.symm u)⁻¹ with hqdef
    have hconj := model.qEquiv_conj q x
    have hqq : model.qEquiv q⁻¹ = u := by
      rw [hqdef, inv_inv, MulEquiv.apply_symm_apply]
    rw [hqq] at hconj
    have hmem := hinv q _ hx
    rw [hconj] at hmem
    exact hmem
  rcases addSubgroup_eq_bot_or_top_of_mul_units_mem A hAinv with hA | hA
  · left
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨y, hy⟩ := hle hz
    have hxA : (Multiplicative.toAdd y) ∈ A := by
      change model.emb (Multiplicative.ofAdd (Multiplicative.toAdd y)) ∈ S
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd y) = y from rfl, hy]
      exact hz
    rw [hA, AddSubgroup.mem_bot] at hxA
    have hy1 : y = 1 := by
      have h1 := congrArg Multiplicative.ofAdd hxA
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd y) = y from rfl] at h1
      rw [h1]; rfl
    rw [Subgroup.mem_bot, ← hy, hy1, map_one]
  · right
    refine le_antisymm hle ?_
    rintro z ⟨y, rfl⟩
    have hxA : Multiplicative.toAdd y ∈ A := hA ▸ AddSubgroup.mem_top _
    have : model.emb (Multiplicative.ofAdd (Multiplicative.toAdd y)) ∈ S := hxA
    rwa [show Multiplicative.ofAdd (Multiplicative.toAdd y) = y from rfl] at this

/-- **Generic center-normalizer nesting**: if `S ⊓ C_G(S) = P` (the center of `S`
realized in the ambient group equals `P`), then `N_G(S) ≤ N_G(P)` — conjugation by a
normalizer of `S` permutes `S ⊓ C_G(S)`.  Consumed by both arms of the step (11)
Sylow contradiction (relocation candidate: `OddOrder/GroupTheory`). -/
theorem normalizer_set_le_normalizer_of_inf_centralizer_eq {G' : Type*} [Group G']
    {S P : Subgroup G'} (h : S ⊓ Subgroup.centralizer (S : Set G') = P) :
    Subgroup.normalizer (S : Set G') ≤ Subgroup.normalizer (P : Set G') := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  intro x
  have key : ∀ y : G', y ∈ S ⊓ Subgroup.centralizer (S : Set G') ↔
      g * y * g⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set G') := by
    intro y
    constructor
    · rintro ⟨hyR, hyC⟩
      refine ⟨(hg y).mp hyR, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hr' : g⁻¹ * r * g ∈ S := by
        have h1 := (hg (g⁻¹ * r * g)).mpr
        simp only [mul_assoc, mul_inv_cancel_left] at h1 ⊢
        exact h1 (by simpa [mul_assoc] using hr)
      have hc := Subgroup.mem_centralizer_iff.mp hyC _ hr'
      have h2 := congrArg (fun z => g * z * g⁻¹) hc
      simpa [mul_assoc] using h2
    · rintro ⟨hyR, hyC⟩
      refine ⟨(hg y).mpr hyR, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hr' : g * r * g⁻¹ ∈ S := (hg r).mp hr
      have hc := Subgroup.mem_centralizer_iff.mp hyC _ hr'
      have h2 := congrArg (fun z => g⁻¹ * z * g) hc
      simpa [mul_assoc] using h2
  rw [← h]
  exact key x


namespace FirstCaseHypothesis

universe uG' uΩ'

variable {G : Type uG'} {Ω : Type uΩ'} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG'} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

/-- **Step (11) invariant-subgroup dichotomy** (the "`C_Q(P)` acts transitively on `F^*`"
consequence at the `G`-level): a `C_G(P)`-conjugation-invariant subgroup `S` with
`P ≤ S ≤ R` is `P` or `R`.  The image of `S` in the faithful quotient is a
`Q`-conjugation-invariant subgroup of the translations, hence `⊥` or all of `emb(F)`
(`conjInvariant_eq_bot_or_range_emb`); pulling back, `S ≤ N = P` (step (7), inheriting
`ind`) or `R ≤ S·N = S`. -/
theorem eq_P_or_eq_invImageF_of_conj_invariant
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    {S : Subgroup G} (hPS : fc.P ≤ S) (hSR : S ≤ fc.invImageF model)
    (hinv : ∀ c ∈ Subgroup.centralizer (fc.P : Set G), ∀ s ∈ S, c * s * c⁻¹ ∈ S) :
    S = fc.P ∨ S = fc.invImageF model := by
  classical
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  have hSL : S ≤ L := hSR.trans (fc.invImageF_le_centralizer model)
  -- the image of `S` in the faithful quotient
  set Sbar : Subgroup (fc.toHypothesis.centralizerActionQuotient fc.P) :=
    (S.subgroupOf L).map (QuotientGroup.mk' N') with hSbardef
  have hSbar_le : Sbar ≤ MonoidHom.range model.emb := by
    rintro z ⟨y, hy, rfl⟩
    have hyS : (y : G) ∈ S := Subgroup.mem_subgroupOf.mp hy
    have h := (fc.mem_invImageF_iff model y.2).mp (hSR hyS)
    have hye : (⟨(y : G), y.2⟩ : ↥L) = y := Subtype.ext rfl
    rwa [hye] at h
  have hSbar_inv : ∀ q : ↥(fc.rankOneQuotient).Q, ∀ z ∈ Sbar,
      (q : fc.toHypothesis.centralizerActionQuotient fc.P) * z *
        (q : fc.toHypothesis.centralizerActionQuotient fc.P)⁻¹ ∈ Sbar := by
    intro q z hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N' (q : _)
    refine ⟨c * y * c⁻¹,
      Subgroup.mem_subgroupOf.mpr
        (hinv (c : G) c.2 (y : G) (Subgroup.mem_subgroupOf.mp hy)),
      by rw [map_mul, map_mul, map_inv, hc]⟩
  rcases conjInvariant_eq_bot_or_range_emb model hSbar_le hSbar_inv with hbot | htop
  · -- `S̄ = ⊥`: every element of `S` lies in `N`, and `N = P` (step (7)).
    left
    refine le_antisymm (fun s hs => ?_) hPS
    have hsL : s ∈ L := hSL hs
    have hz : QuotientGroup.mk' N' ⟨s, hsL⟩ ∈ Sbar :=
      ⟨⟨s, hsL⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hz
    have hsN : (⟨s, hsL⟩ : ↥L) ∈ N' := (QuotientGroup.eq_one_iff _).mp hz
    have hker : s ∈ fc.kernelN := ⟨⟨s, hsL⟩, hsN, rfl⟩
    rwa [fc.kernelN_eq_P ind] at hker
  · -- `S̄ = emb(F)`: every element of `R` differs from one of `S` by `N = P ≤ S`.
    right
    refine le_antisymm hSR (fun r hr => ?_)
    have hrL : r ∈ L := fc.invImageF_le_centralizer model hr
    have hz : QuotientGroup.mk' N' ⟨r, hrL⟩ ∈ Sbar := by
      rw [htop]
      have h := (fc.mem_invImageF_iff model hrL).mp hr
      exact h
    obtain ⟨y, hy, hyr⟩ := hz
    have hyS : (y : G) ∈ S := Subgroup.mem_subgroupOf.mp hy
    -- `mk' y = mk' ⟨r⟩` forces `⟨r⟩·y⁻¹ ∈ N'`, i.e. `r·y⁻¹ ∈ N = P ≤ S`.
    have h1 : QuotientGroup.mk' N' ((⟨r, hrL⟩ : ↥L) * y⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hyr, mul_inv_cancel]
    have hdiff : (⟨r, hrL⟩ : ↥L) * y⁻¹ ∈ N' := by
      rw [QuotientGroup.mk'_apply] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hkG : r * (y : G)⁻¹ ∈ fc.kernelN := ⟨_, hdiff, rfl⟩
    rw [fc.kernelN_eq_P ind] at hkG
    have hre : r = (r * (y : G)⁻¹) * (y : G) := by group
    rw [hre]
    exact S.mul_mem (hPS hkG) hyS

/-- `P` is central in `R`: every element of `R ≤ C_G(P)` centralizes `P`. -/
theorem P_le_center_invImageF {x r : G} (hx : x ∈ fc.P)
    (hr : r ∈ fc.invImageF model) : r * x = x * r :=
  (Subgroup.mem_centralizer_iff.mp (fc.invImageF_le_centralizer model hr) x hx).symm

/-- The commutator of `R` lands in `P`: the faithful quotient image of `R` is the
translation subgroup `emb(F)`, which is abelian, so commutators die in `N = P`
(step (7), inheriting `ind`). -/
theorem commutator_invImageF_le_P (ind : Hypothesis.TheoremAInductionBelow G Ω)
    {r₁ r₂ : G} (h₁ : r₁ ∈ fc.invImageF model) (h₂ : r₂ ∈ fc.invImageF model) :
    r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ fc.P := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  have h₁L : r₁ ∈ L := fc.invImageF_le_centralizer model h₁
  have h₂L : r₂ ∈ L := fc.invImageF_le_centralizer model h₂
  -- both classes are translations; translations commute (`F` is abelian);
  -- so the commutator class is `1`, i.e. the commutator lies in `N = P`.
  obtain ⟨y₁, hy₁⟩ := (fc.mem_invImageF_iff model h₁L).mp h₁
  obtain ⟨y₂, hy₂⟩ := (fc.mem_invImageF_iff model h₂L).mp h₂
  have hcommQ : QuotientGroup.mk' N'
      ((⟨r₁, h₁L⟩ : ↥L) * ⟨r₂, h₂L⟩ * (⟨r₁, h₁L⟩ : ↥L)⁻¹ * (⟨r₂, h₂L⟩ : ↥L)⁻¹) = 1 := by
    have e1 : QuotientGroup.mk' N' (⟨r₁, h₁L⟩ : ↥L) = model.emb y₁ := hy₁.symm
    have e2 : QuotientGroup.mk' N' (⟨r₂, h₂L⟩ : ↥L) = model.emb y₂ := hy₂.symm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, e1, e2, ← map_inv, ← map_inv,
      ← map_mul, ← map_mul, ← map_mul,
      show y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = 1 by rw [mul_comm y₁ y₂]; group,
      map_one]
  have hmemN : ((⟨r₁, h₁L⟩ : ↥L) * ⟨r₂, h₂L⟩ * (⟨r₁, h₁L⟩ : ↥L)⁻¹ * (⟨r₂, h₂L⟩ : ↥L)⁻¹)
      ∈ N' := by
    rw [QuotientGroup.mk'_apply] at hcommQ
    exact (QuotientGroup.eq_one_iff _).mp hcommQ
  have hkG : r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ fc.kernelN := ⟨_, hmemN, rfl⟩
  rwa [fc.kernelN_eq_P ind] at hkG

/-- **`|R| = |F|·|P| (= p^{m+1})`** (p. 111): Lagrange through the quotient — the image of
`R` in the faithful quotient is `emb(F)` of order `|F|`, and the fibre is `N = P`
(step (7), inheriting `ind`). -/
theorem card_invImageF (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nat.card ↥(fc.invImageF model) = Nat.card F * Nat.card ↥fc.P := by
  classical
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  set Sbar : Subgroup (↥L ⧸ N') := MonoidHom.range model.emb with hSbardef
  set Rsub : Subgroup ↥L := Sbar.comap (QuotientGroup.mk' N') with hRsubdef
  -- `|R| = |Rsub|` (push-forward along the injective inclusion).
  have hcard_R : Nat.card ↥(fc.invImageF model) = Nat.card ↥Rsub :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective L)).symm.toEquiv
  -- `Rsub.index = Sbar.index` (`index_comap` + surjectivity of `mk'`).
  have hidx : Rsub.index = Sbar.index := by
    rw [hRsubdef, Subgroup.index_comap,
      MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N'),
      Subgroup.relIndex_top_right]
  -- Lagrange in `L` and in the quotient, then cancel the common (nonzero) index.
  have h1 : Nat.card ↥Rsub * Rsub.index = Nat.card ↥L := Rsub.card_mul_index
  have h2 : Nat.card ↥Sbar * Sbar.index = Nat.card (↥L ⧸ N') := Sbar.card_mul_index
  have h3 : Nat.card ↥L = Nat.card (↥L ⧸ N') * Nat.card ↥N' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  -- `|Sbar| = |F|` (the embedding is injective).
  have hSF : Nat.card ↥Sbar = Nat.card F := by
    rw [hSbardef]
    exact Nat.card_congr (MonoidHom.ofInjective model.emb_injective).symm.toEquiv
  -- `|N'| = |P|` (step (7): `kernelN = P`).
  have hNP : Nat.card ↥N' = Nat.card ↥fc.P := by
    have h := fc.kernelN_eq_P ind
    have hcongr : Nat.card ↥fc.kernelN = Nat.card ↥N' :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _
        (Subgroup.subtype_injective L)).symm.toEquiv
    rw [← hcongr, h]
  -- assemble
  have hne : Sbar.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hkey : Nat.card ↥Rsub * Sbar.index
      = (Nat.card F * Nat.card ↥fc.P) * Sbar.index := by
    calc Nat.card ↥Rsub * Sbar.index
        = Nat.card ↥Rsub * Rsub.index := by rw [hidx]
      _ = Nat.card ↥L := h1
      _ = Nat.card (↥L ⧸ N') * Nat.card ↥N' := h3
      _ = (Nat.card ↥Sbar * Sbar.index) * Nat.card ↥N' := by rw [h2]
      _ = (Nat.card F * Nat.card ↥fc.P) * Sbar.index := by rw [hSF, hNP]; ring
  rw [hcard_R]
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) hkey

include model in
/-- **`|C_G(P)| = |P|·(|F|·(|Q̄|·|Σ|))`** (order accounting for the Sylow step of (11)):
Lagrange through the faithful quotient (fibre `N = P`, step (7)) and the affine
decomposition `C_G(P)/N = F ⋊ H̄` with `H̄ = Q̄·Σ` of the model. -/
theorem card_centralizer_P (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    Nat.card ↥(Subgroup.centralizer (fc.P : Set G))
      = Nat.card ↥fc.P * (Nat.card F *
          (Nat.card ↥(fc.rankOneQuotient).Q * Nat.card ↥(fc.rankOneQuotient).D)) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  -- `|L| = |L⧸N'|·|N'|`, `|L⧸N'| = |F|·|H̄|`, `|H̄| = |Q̄|·|D̄|`.
  have h3 : Nat.card ↥L = Nat.card (↥L ⧸ N') * Nat.card ↥N' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  have h4 : Nat.card ↥(MonoidHom.range model.emb) * Nat.card ↥(fc.rankOneQuotient).H
      = Nat.card (↥L ⧸ N') := model.isComplement.card_mul
  have hDH : (fc.rankOneQuotient).D ≤ (fc.rankOneQuotient).H := by
    rw [(fc.rankOneQuotient).D_def]; exact inf_le_left
  have hmul : ∀ x ∈ (fc.rankOneQuotient).H, ∃ q ∈ (fc.rankOneQuotient).Q,
      ∃ d ∈ (fc.rankOneQuotient).D, q * d = x := by
    intro x hx
    have hx' : x ∈ ((fc.rankOneQuotient).Q :
        Set (fc.toHypothesis.centralizerActionQuotient fc.P)) * ((fc.rankOneQuotient).D :
        Set (fc.toHypothesis.centralizerActionQuotient fc.P)) := by
      rw [(fc.rankOneQuotient).Q_mul_D_eq_H]; exact hx
    obtain ⟨q, hq, d, hd, hqd⟩ := hx'
    exact ⟨q, hq, d, hd, hqd⟩
  have hDQbot : (fc.rankOneQuotient).D ⊓ (fc.rankOneQuotient).Q = ⊥ := by
    rw [inf_comm]; exact (fc.rankOneQuotient).Q_inf_D_eq_bot
  have h5 := (Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    hDH (fc.rankOneQuotient).Q_le_H hDQbot hmul).card_mul
  have hQc : Nat.card ↥((fc.rankOneQuotient).Q.subgroupOf (fc.rankOneQuotient).H)
      = Nat.card ↥(fc.rankOneQuotient).Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fc.rankOneQuotient).Q_le_H).toEquiv
  have hDc : Nat.card ↥((fc.rankOneQuotient).D.subgroupOf (fc.rankOneQuotient).H)
      = Nat.card ↥(fc.rankOneQuotient).D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
  have hHQD : Nat.card ↥(fc.rankOneQuotient).Q * Nat.card ↥(fc.rankOneQuotient).D
      = Nat.card ↥(fc.rankOneQuotient).H := by
    rw [← hQc, ← hDc]; exact h5
  have hSF : Nat.card ↥(MonoidHom.range model.emb) = Nat.card F :=
    Nat.card_congr (MonoidHom.ofInjective model.emb_injective).symm.toEquiv
  have hNP : Nat.card ↥N' = Nat.card ↥fc.P := by
    have h := fc.kernelN_eq_P ind
    have hcongr : Nat.card ↥fc.kernelN = Nat.card ↥N' :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _
        (Subgroup.subtype_injective L)).symm.toEquiv
    rw [← hcongr, h]
  calc Nat.card ↥L
      = Nat.card (↥L ⧸ N') * Nat.card ↥N' := h3
    _ = (Nat.card ↥(MonoidHom.range model.emb) * Nat.card ↥(fc.rankOneQuotient).H)
        * Nat.card ↥fc.P := by rw [h4, hNP]
    _ = (Nat.card F * (Nat.card ↥(fc.rankOneQuotient).Q
        * Nat.card ↥(fc.rankOneQuotient).D)) * Nat.card ↥fc.P := by
        rw [hSF, hHQD]
    _ = Nat.card ↥fc.P * (Nat.card F * (Nat.card ↥(fc.rankOneQuotient).Q
        * Nat.card ↥(fc.rankOneQuotient).D)) := by ring

/-- **`Z(R) = P` when `R` is nonabelian** (p. 111, proof of (11), first paragraph):
the center of `R` (as `R ⊓ C_G(R)`) is `C_G(P)`-invariant and sits between `P` and `R`,
so the dichotomy applies; the top case would make `R` abelian. -/
theorem center_eq_P_of_not_isMulCommutative
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hnab : ∃ r₁ ∈ fc.invImageF model, ∃ r₂ ∈ fc.invImageF model, r₁ * r₂ ≠ r₂ * r₁) :
    fc.invImageF model ⊓ Subgroup.centralizer (fc.invImageF model : Set G) = fc.P := by
  set R : Subgroup G := fc.invImageF model with hRdef
  set ZR : Subgroup G := R ⊓ Subgroup.centralizer (R : Set G) with hZRdef
  have hPZ : fc.P ≤ ZR := by
    intro x hx
    refine ⟨fc.P_le_invImageF model hx, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    exact fc.P_le_center_invImageF model hx hr
  have hZR : ZR ≤ R := inf_le_left
  have hZinv : ∀ c ∈ Subgroup.centralizer (fc.P : Set G), ∀ s ∈ ZR,
      c * s * c⁻¹ ∈ ZR := by
    intro c hc s hs
    obtain ⟨hsR, hsC⟩ := hs
    refine ⟨fc.conj_mem_invImageF model hc hsR, Subgroup.mem_centralizer_iff.mpr
      fun r hr => ?_⟩
    -- `r` commutes with `c s c⁻¹` because `c⁻¹ r c ∈ R` commutes with `s`.
    have hrc : c⁻¹ * r * c ∈ R := by
      have := fc.conj_mem_invImageF model (Subgroup.inv_mem _ hc) hr
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hsC _ hrc
    -- `(c⁻¹ r c) s = s (c⁻¹ r c)`  ⟹  `r (c s c⁻¹) = (c s c⁻¹) r`
    have h1 := congrArg (fun z => c * z * c⁻¹) hcomm
    simpa [mul_assoc] using h1
  rcases fc.eq_P_or_eq_invImageF_of_conj_invariant model ind hPZ hZR hZinv with h | h
  · exact h
  · exfalso
    obtain ⟨r₁, h₁, r₂, h₂, hne⟩ := hnab
    exact hne (Subgroup.mem_centralizer_iff.mp ((h.ge h₁).2) r₂ h₂).symm

/-- **`N_G(R) ≤ N_G(P)` when `R` is nonabelian** (p. 111): a normalizer of `R` permutes
`Z(R) = R ⊓ C_G(R)` (conjugation is a group automorphism), and `Z(R) = P` by
`center_eq_P_of_not_isMulCommutative`. -/
theorem normalizer_invImageF_le_normalizer_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hnab : ∃ r₁ ∈ fc.invImageF model, ∃ r₂ ∈ fc.invImageF model, r₁ * r₂ ≠ r₂ * r₁) :
    Subgroup.normalizer (fc.invImageF model : Set G)
      ≤ Subgroup.normalizer (fc.P : Set G) :=
  normalizer_set_le_normalizer_of_inf_centralizer_eq
    (fc.center_eq_P_of_not_isMulCommutative model ind hnab)


/-- **Shared Sylow-contradiction engine for step (11)** (both arms): there is no
`p`-subgroup `S ≤ C_G(P)` of full `p`-part (`|S| = p^k`, `|C_G(P)| = p^k·c`, `p ∤ c`) with
`S ⊓ C_G(S) = P`, once `p^{k+1} ∣ |G|`: normalizer growth inside a Sylow `p`-subgroup of
`G` produces a `p`-subgroup of `N_G(S) ≤ N_G(P) = C_G(P)` (step (1)) strictly larger than
`p^k`. -/
theorem false_of_ppart_subgroup_center_P {S : Subgroup G} {k c : ℕ}
    (hZ : S ⊓ Subgroup.centralizer (S : Set G) = fc.P)
    (hcard : Nat.card ↥S = fc.p ^ k)
    (hC : Nat.card ↥(Subgroup.centralizer (fc.P : Set G)) = fc.p ^ k * c)
    (hpc : ¬ fc.p ∣ c)
    (hGdvd : fc.p ^ (k + 1) ∣ Nat.card G) : False := by
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  have hSp : IsPGroup fc.p ↥S := IsPGroup.of_card hcard
  obtain ⟨X, hSX⟩ := hSp.exists_le_sylow
  have hXdvd : fc.p ^ (k + 1) ∣ Nat.card ↥(X : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity]
    exact pow_dvd_pow _ ((Nat.Prime.pow_dvd_iff_le_factorization fc.p_prime
      Nat.card_pos.ne').mp hGdvd)
  have hSltX : S < (X : Subgroup G) := by
    refine lt_of_le_of_ne hSX fun h => ?_
    rw [← h, hcard, Nat.pow_dvd_pow_iff_le_right fc.p_prime.one_lt] at hXdvd
    omega
  have hgrow := OddOrder.BG.Ch2.S08.lt_inf_normalizer_of_isPGroup_lt
    (p := fc.p) X.isPGroup' hSltX
  set Y : Subgroup G := (X : Subgroup G) ⊓ Subgroup.normalizer (S : Set G) with hYdef
  have hYC : Y ≤ Subgroup.centralizer (fc.P : Set G) := by
    refine le_trans inf_le_right ?_
    rw [← fc.normalizer_P_eq_centralizer]
    exact normalizer_set_le_normalizer_of_inf_centralizer_eq hZ
  have hYp : IsPGroup fc.p ↥Y := X.isPGroup'.to_le inf_le_left
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hYp
  have hlt : fc.p ^ k < Nat.card ↥Y := by
    rw [← hcard]
    have hdvd : Nat.card ↥S ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hgrow.le
    refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun heq => ?_
    exact hgrow.ne (Subgroup.eq_of_le_of_card_ge hgrow.le heq.ge)
  have hYdvd : Nat.card ↥Y ∣ Nat.card ↥(Subgroup.centralizer (fc.P : Set G)) :=
    Subgroup.card_dvd_of_le hYC
  rw [hC, hj] at hYdvd
  have hpc' : Nat.Coprime fc.p c := (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr hpc
  have hjdvd : fc.p ^ j ∣ fc.p ^ k :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left j hpc')) hYdvd
  have hle : Nat.card ↥Y ≤ fc.p ^ k := by
    rw [hj]
    exact Nat.le_of_dvd (Nat.pow_pos fc.p_prime.pos) hjdvd
  omega

include model in
/-- **`R` is abelian — case (10.1) arm** (p. 111, proof of (11) ¶1): under `p ∤ |Σ|` and
`p^{m+2} ∣ |G|`, a nonabelian `R` would have `Z(R) = P`, hence
`N_G(R) ≤ N_G(P) = C_G(P)` (step (1)); `R` is then a `p`-subgroup of `C_G(P)` of full
`p`-part `p^{m+1}`, while normalizer growth inside a Sylow `p`-subgroup of `G`
(`lt_inf_normalizer_of_isPGroup_lt`) manufactures a strictly larger `p`-subgroup of
`C_G(P)` — impossible. -/
theorem invImageF_mul_comm_of_not_dvd_card_D
    (ind : Hypothesis.TheoremAInductionBelow G Ω) {m : ℕ}
    (hFcard : Nat.card F = fc.p ^ m)
    (hGp : fc.p ^ (m + 2) ∣ Nat.card G) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D →
      ∀ r₁ ∈ fc.invImageF model, ∀ r₂ ∈ fc.invImageF model, r₁ * r₂ = r₂ * r₁ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI : Finite F := Nat.finite_of_card_ne_zero
    (by rw [hFcard]; exact (Nat.pow_pos fc.p_prime.pos).ne')
  intro hSigma
  by_contra hcon
  push Not at hcon
  obtain ⟨r₁, h₁, r₂, h₂, hne⟩ := hcon
  have hnab : ∃ x ∈ fc.invImageF model, ∃ y ∈ fc.invImageF model, x * y ≠ y * x :=
    ⟨r₁, h₁, r₂, h₂, hne⟩
  have hcardR : Nat.card ↥(fc.invImageF model) = fc.p ^ (m + 1) := by
    rw [fc.card_invImageF model ind, hFcard, fc.card_P]; ring
  have hCeq : Nat.card ↥(Subgroup.centralizer (fc.P : Set G))
      = fc.p ^ (m + 1) * (Nat.card ↥(fc.rankOneQuotient).Q
        * Nat.card ↥(fc.rankOneQuotient).D) := by
    rw [fc.card_centralizer_P model ind, fc.card_P, hFcard]; ring
  have hQcard : Nat.card ↥(fc.rankOneQuotient).Q = fc.p ^ m - 1 := by
    haveI := Fintype.ofFinite F
    haveI := Classical.decEq F
    rw [Nat.card_congr model.qEquiv.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, hFcard]
  have hm1 : 1 ≤ m := by
    by_contra hm0
    push Not at hm0
    interval_cases m
    have h2 : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hFcard] at h2
    simp at h2
  have hpQ : ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).Q := by
    rw [hQcard]
    intro hdvd
    have hple : fc.p ∣ fc.p ^ m := dvd_pow_self _ (by omega)
    have h1 : fc.p ∣ 1 := by
      have := Nat.dvd_sub hple hdvd
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ fc.p_prime.pos)] at this
    exact fc.p_prime.one_lt.ne' (Nat.dvd_one.mp h1)
  exact fc.false_of_ppart_subgroup_center_P
    (fc.center_eq_P_of_not_isMulCommutative model ind hnab) hcardR hCeq
    (fun hdvd => ((fc.p_prime.dvd_mul).mp hdvd).elim hpQ hSigma) hGp

include model in
/-- **`Σ`-faithfulness core**: a `w ∈ C_W(P)` whose `Σ`-class acts trivially on `F`
(`dAut (sigmaElt w) = id`) is the identity — `dAut_injective` collapses `[w]` to `1`,
step (7) (`N = P`, inheriting `ind`) puts `w ∈ P`, and `P ⊓ W = ⊥` finishes. -/
theorem eq_one_of_dAut_sigmaElt_eq_id
    (ind : Hypothesis.TheoremAInductionBelow G Ω) {w : G}
    (hwW : w ∈ fc.toHypothesis.W) (hwP : w ∈ Subgroup.centralizer (fc.P : Set G))
    (hdw : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ∀ x : F, model.dAut (fc.sigmaElt hwW hwP) x = x) : w = 1 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  -- `dAut 1 = id` (specialize `dAut_conj` at the identity).
  have hdone : ∀ x : F, model.dAut 1 x = x := by
    intro x
    have h := model.dAut_conj 1 x
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
    exact (model.emb_injective h).symm ▸ rfl
  have hone : fc.sigmaElt hwW hwP = 1 := by
    apply model.dAut_injective
    ext x
    rw [hdw x, hdone x]
  have hwN : (⟨w, hwP⟩ : ↥L) ∈ N' := by
    have h2 : ((fc.sigmaElt hwW hwP : ↥fc.rankOneQuotient.D) : ↥L ⧸ N')
        = ((1 : ↥fc.rankOneQuotient.D) : ↥L ⧸ N') :=
      congrArg (fun z : ↥fc.rankOneQuotient.D => (z : ↥L ⧸ N')) hone
    rw [OneMemClass.coe_one] at h2
    have h1 : QuotientGroup.mk' N' ⟨w, hwP⟩ = 1 := h2
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hwP' : w ∈ fc.P := by
    have hker : w ∈ fc.kernelN := ⟨_, hwN, rfl⟩
    rwa [fc.kernelN_eq_P ind] at hker
  have hmem : w ∈ fc.P ⊓ fc.toHypothesis.W := ⟨hwP', hwW⟩
  rwa [fc.P_inf_W_eq_bot, Subgroup.mem_bot] at hmem

include model in
/-- **A nonidentity element of `C_W(P)` does not centralize `R`** ((10.2) arm of (11)):
if `w` centralized `R`, its class `[w] ∈ Σ` would act trivially on the translations
(`dAut_conj` + injectivity of `emb`), so `w = 1` by the faithfulness core. -/
theorem not_forall_comm_of_mem_centralizer_W
    (ind : Hypothesis.TheoremAInductionBelow G Ω) {w : G}
    (hwW : w ∈ fc.toHypothesis.W) (hwP : w ∈ Subgroup.centralizer (fc.P : Set G))
    (hw1 : w ≠ 1) :
    ¬ (∀ r ∈ fc.invImageF model, w * r = r * w) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro hcen
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  refine hw1 (fc.eq_one_of_dAut_sigmaElt_eq_id model ind hwW hwP ?_)
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N' (model.emb (Multiplicative.ofAdd x))
  have hyR : (y : G) ∈ fc.invImageF model :=
    ⟨y, Subgroup.mem_comap.mpr (by rw [hy]; exact ⟨Multiplicative.ofAdd x, rfl⟩), rfl⟩
  have hcomm := hcen (y : G) hyR
  have hconj := model.dAut_conj (fc.sigmaElt hwW hwP) x
  have hwy : (⟨w, hwP⟩ : ↥L) * y * (⟨w, hwP⟩ : ↥L)⁻¹ = y := by
    apply Subtype.ext
    have h3 : w * (y : G) * w⁻¹ = (y : G) := by
      rw [hcomm]; group
    simpa using h3
  have hlhs : ((fc.sigmaElt hwW hwP : ↥fc.rankOneQuotient.D) : ↥L ⧸ N')
      * model.emb (Multiplicative.ofAdd x)
      * ((fc.sigmaElt hwW hwP : ↥fc.rankOneQuotient.D) : ↥L ⧸ N')⁻¹
      = model.emb (Multiplicative.ofAdd x) := by
    have hcoe : ((fc.sigmaElt hwW hwP : ↥fc.rankOneQuotient.D) : ↥L ⧸ N')
        = QuotientGroup.mk' N' ⟨w, hwP⟩ := rfl
    rw [hcoe, ← hy, ← map_inv, ← map_mul, ← map_mul, hwy]
  rw [hlhs] at hconj
  exact model.emb_injective hconj.symm

include model in
/-- **`R ⊓ C_W(P) = ⊥`**: an element of both maps into `emb(F) ⊓ H̄ = ⊥` in the faithful
quotient (the affine complement), hence lies in `N = P` (step (7)); and `P ⊓ W = ⊥`. -/
theorem invImageF_inf_centralizer_W_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    fc.invImageF model ⊓ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) = ⊥ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  rw [eq_bot_iff]
  rintro w ⟨hwR, hwW, hwP⟩
  rw [Subgroup.mem_bot]
  -- `[w]` is both a translation and in `H̄ ⊇ Σ`; the complement forces `[w] = 1`.
  have hrange : QuotientGroup.mk' N' ⟨w, hwP⟩ ∈ MonoidHom.range model.emb :=
    (fc.mem_invImageF_iff model hwP).mp hwR
  have hH : QuotientGroup.mk' N' ⟨w, hwP⟩ ∈ (fc.rankOneQuotient).H := by
    have hD : QuotientGroup.mk' N' ⟨w, hwP⟩ ∈ (fc.rankOneQuotient).D :=
      (fc.sigmaElt hwW hwP).2
    have hDH : (fc.rankOneQuotient).D ≤ (fc.rankOneQuotient).H := by
      rw [(fc.rankOneQuotient).D_def]; exact inf_le_left
    exact hDH hD
  have hone : QuotientGroup.mk' N' ⟨w, hwP⟩ = 1 := by
    have hb := model.isComplement.disjoint.le_bot ⟨hrange, hH⟩
    rwa [Subgroup.mem_bot] at hb
  have hwN : (⟨w, hwP⟩ : ↥L) ∈ N' := by
    rw [QuotientGroup.mk'_apply] at hone
    exact (QuotientGroup.eq_one_iff _).mp hone
  have hwPm : w ∈ fc.P := by
    have hker : w ∈ fc.kernelN := ⟨_, hwN, rfl⟩
    rwa [fc.kernelN_eq_P ind] at hker
  have hmem : w ∈ fc.P ⊓ fc.toHypothesis.W := ⟨hwPm, hwW⟩
  rwa [fc.P_inf_W_eq_bot, Subgroup.mem_bot] at hmem

include model in
/-- The carrier of `R ⊔ C_W(P)` is the set product `↑R * ↑C_W(P)`: `C_W(P) ≤ C_G(P)`
normalizes `R` (`conj_mem_invImageF`). -/
theorem coe_sup_invImageF_centralizer_W :
    ((fc.invImageF model ⊔
        (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) : Set G)
      = (fc.invImageF model : Set G)
        * ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.coe_mul_of_right_le_normalizer_left _ _ ?_
  intro w hw
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact fc.conj_mem_invImageF model hw.2 hn
  · intro hn
    have h1 := fc.conj_mem_invImageF model (Subgroup.inv_mem _ hw.2) hn
    simpa [mul_assoc] using h1

include model in
/-- **`|R ⊔ C_W(P)| = |R|·|C_W(P)|`** (the two factors intersect trivially,
`invImageF_inf_centralizer_W_eq_bot`). -/
theorem card_sup_invImageF_centralizer_W
    (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nat.card ↥(fc.invImageF model ⊔
        (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
      = Nat.card ↥(fc.invImageF model)
        * Nat.card ↥(fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
  set R : Subgroup G := fc.invImageF model with hRdef
  set CW : Subgroup G := fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) with hCWdef
  have hmul : ∀ x ∈ R ⊔ CW, ∃ m ∈ R, ∃ h ∈ CW, m * h = x := by
    intro x hx
    have hx' : x ∈ ((R : Set G) * (CW : Set G)) := by
      rw [← fc.coe_sup_invImageF_centralizer_W model]
      exact hx
    obtain ⟨r, hr, w, hw, rfl⟩ := hx'
    exact ⟨r, hr, w, hw, rfl⟩
  have hbot : CW ⊓ R = ⊥ := by
    rw [inf_comm]
    exact fc.invImageF_inf_centralizer_W_eq_bot model ind
  have hcompl := (Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    (le_sup_right : CW ≤ R ⊔ CW) (le_sup_left : R ≤ R ⊔ CW) hbot hmul).card_mul
  have hRc : Nat.card ↥(R.subgroupOf (R ⊔ CW)) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hCWc : Nat.card ↥(CW.subgroupOf (R ⊔ CW)) = Nat.card ↥CW :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [← hRc, ← hCWc]
  exact hcompl.symm

include model in
/-- **`Z(R·C_W(P)) = P` when `R` is nonabelian** ((10.2) arm, p. 112 top): a central
element decomposes as `r·w`; its class centralizes the translations, and `[r]` does too
(the translations are abelian), so `[w]` acts trivially and `w = 1` by the faithfulness
core; then `z = r ∈ R ⊓ C_G(R) = Z(R) = P`. -/
theorem sup_centralizer_W_inf_centralizer_eq_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hnab : ∃ r₁ ∈ fc.invImageF model, ∃ r₂ ∈ fc.invImageF model, r₁ * r₂ ≠ r₂ * r₁) :
    (fc.invImageF model ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
      ⊓ Subgroup.centralizer
        ((fc.invImageF model ⊔
          (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) : Set G)
      = fc.P := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  set R : Subgroup G := fc.invImageF model with hRdef
  set CW : Subgroup G := fc.toHypothesis.W ⊓ L with hCWdef
  apply le_antisymm
  · rintro z ⟨hzS, hzC⟩
    have hz' : z ∈ ((R : Set G) * (CW : Set G)) := by
      rw [← fc.coe_sup_invImageF_centralizer_W model]
      exact hzS
    obtain ⟨r, hr, w, hw, rfl⟩ := hz'
    have hrL : r ∈ L := fc.invImageF_le_centralizer model hr
    have hwL : w ∈ L := hw.2
    -- the `w`-component is trivial
    have hw1 : w = 1 := by
      refine fc.eq_one_of_dAut_sigmaElt_eq_id model ind hw.1 hw.2 ?_
      intro x
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N' (model.emb (Multiplicative.ofAdd x))
      have hyR : (y : G) ∈ R :=
        ⟨y, Subgroup.mem_comap.mpr (by rw [hy]; exact ⟨Multiplicative.ofAdd x, rfl⟩), rfl⟩
      -- `z = r·w` centralizes `y ∈ R ≤ R ⊔ CW`
      have hcomm : (y : G) * (r * w) = (r * w) * (y : G) :=
        Subgroup.mem_centralizer_iff.mp hzC (y : G) (le_sup_left (a := R) hyR)
      have hzy : (⟨r, hrL⟩ * ⟨w, hwL⟩ : ↥L) * y * ((⟨r, hrL⟩ * ⟨w, hwL⟩ : ↥L))⁻¹ = y := by
        apply Subtype.ext
        have h3 : (r * w) * (y : G) * (r * w)⁻¹ = (y : G) := by
          rw [← hcomm]; group
        simpa using h3
      -- push to the quotient and cancel the abelian `[r]`
      have hq := congrArg (QuotientGroup.mk' N') hzy
      rw [map_mul, map_mul, map_inv, map_mul, hy] at hq
      set a : ↥L ⧸ N' := QuotientGroup.mk' N' ⟨r, hrL⟩ with hadef
      set b : ↥L ⧸ N' := QuotientGroup.mk' N' ⟨w, hwL⟩ with hbdef
      -- `a` is a translation, hence commutes with `emb x`
      have haR : a ∈ MonoidHom.range model.emb := (fc.mem_invImageF_iff model hrL).mp hr
      obtain ⟨x', hx'⟩ := haR
      have hacomm : a * model.emb (Multiplicative.ofAdd x)
          = model.emb (Multiplicative.ofAdd x) * a := by
        rw [← hx', ← map_mul, ← map_mul, mul_comm]
      -- conclude `b (emb x) b⁻¹ = emb x`
      have hb : b * model.emb (Multiplicative.ofAdd x) * b⁻¹
          = model.emb (Multiplicative.ofAdd x) := by
        have h5 : a * (b * model.emb (Multiplicative.ofAdd x) * b⁻¹) * a⁻¹
            = model.emb (Multiplicative.ofAdd x) := by
          rw [mul_inv_rev] at hq
          simp only [mul_assoc] at hq ⊢
          exact hq
        have h8 : a * (b * model.emb (Multiplicative.ofAdd x) * b⁻¹)
            = model.emb (Multiplicative.ofAdd x) * a := by
          calc a * (b * model.emb (Multiplicative.ofAdd x) * b⁻¹)
              = (a * (b * model.emb (Multiplicative.ofAdd x) * b⁻¹) * a⁻¹) * a := by group
            _ = model.emb (Multiplicative.ofAdd x) * a := by rw [h5]
        have h9 : a * (b * model.emb (Multiplicative.ofAdd x) * b⁻¹)
            = a * model.emb (Multiplicative.ofAdd x) := by
          rw [h8, ← hacomm]
        exact mul_left_cancel h9
      -- identify with `dAut_conj`
      have hconj := model.dAut_conj (fc.sigmaElt hw.1 hw.2) x
      have hcoe : ((fc.sigmaElt hw.1 hw.2 : ↥fc.rankOneQuotient.D) : ↥L ⧸ N') = b := rfl
      rw [hcoe, hb] at hconj
      exact model.emb_injective hconj.symm
    -- `z = r ∈ R ⊓ C_G(R) = P`
    subst hw1
    simp only [mul_one] at hzC ⊢
    have hzCR : r ∈ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.centralizer_le ?_ hzC
      intro g hg
      exact le_sup_left (a := R) hg
    have hmem : r ∈ R ⊓ Subgroup.centralizer (R : Set G) := ⟨hr, hzCR⟩
    rwa [fc.center_eq_P_of_not_isMulCommutative model ind hnab] at hmem
  · intro x hx
    refine ⟨(le_sup_left : R ≤ R ⊔ CW) (fc.P_le_invImageF model hx),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro g hg
    have hg' : g ∈ ((R : Set G) * (CW : Set G)) := by
      rw [← fc.coe_sup_invImageF_centralizer_W model]
      exact hg
    obtain ⟨r, hr, w, hw, rfl⟩ := hg'
    have h1 : r * x = x * r := fc.P_le_center_invImageF model hx hr
    have h2 : w * x = x * w :=
      (Subgroup.mem_centralizer_iff.mp hw.2 x hx).symm
    calc r * w * x = r * x * w := by rw [mul_assoc, h2, ← mul_assoc]
      _ = x * (r * w) := by rw [h1]; group

include model in
/-- **`R` is abelian — case (10.2) arm** (p. 112 top): under `|F| = p²`, `|Σ| = p` and
`p^5 ∣ |G|`, a nonabelian `R` would make `S := R·C_W(P)` a `p`-subgroup of `C_G(P)` of
full `p`-part `p^4` with `S ⊓ C_G(S) = P` — killed by the shared Sylow engine. -/
theorem invImageF_mul_comm_of_card_D_eq_p
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hF : Nat.card F = fc.p ^ 2)
    (hG5 : fc.p ^ 5 ∣ Nat.card G) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    Nat.card ↥(fc.rankOneQuotient).D = fc.p →
      ∀ r₁ ∈ fc.invImageF model, ∀ r₂ ∈ fc.invImageF model, r₁ * r₂ = r₂ * r₁ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI : Finite F := Nat.finite_of_card_ne_zero
    (by rw [hF]; exact (Nat.pow_pos fc.p_prime.pos).ne')
  intro hD
  by_contra hcon
  push Not at hcon
  obtain ⟨r₁, h₁, r₂, h₂, hne⟩ := hcon
  have hnab : ∃ x ∈ fc.invImageF model, ∃ y ∈ fc.invImageF model, x * y ≠ y * x :=
    ⟨r₁, h₁, r₂, h₂, hne⟩
  -- `|C_W(P)| = |Σ| = p` (step (7) isomorphism).
  obtain ⟨e⟩ := fc.sigma_mulEquiv_centralizer_W ind
  have hCW : Nat.card ↥(fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))
      = fc.p := by
    rw [← Nat.card_congr e.toEquiv, hD]
  -- `|S| = p^4`.
  have hcardS : Nat.card ↥(fc.invImageF model ⊔
      (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) = fc.p ^ 4 := by
    rw [fc.card_sup_invImageF_centralizer_W model ind, fc.card_invImageF model ind,
      hF, fc.card_P, hCW]
    ring
  -- `|C_G(P)| = p^4 · |Q̄|` with `p ∤ |Q̄|`.
  have hCeq : Nat.card ↥(Subgroup.centralizer (fc.P : Set G))
      = fc.p ^ 4 * Nat.card ↥(fc.rankOneQuotient).Q := by
    rw [fc.card_centralizer_P model ind, fc.card_P, hF, hD]
    ring
  have hQcard : Nat.card ↥(fc.rankOneQuotient).Q = fc.p ^ 2 - 1 := by
    haveI := Fintype.ofFinite F
    haveI := Classical.decEq F
    rw [Nat.card_congr model.qEquiv.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  have hpQ : ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).Q := by
    rw [hQcard]
    intro hdvd
    have hple : fc.p ∣ fc.p ^ 2 := dvd_pow_self _ (by omega)
    have h1 : fc.p ∣ 1 := by
      have := Nat.dvd_sub hple hdvd
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ fc.p_prime.pos)] at this
    exact fc.p_prime.one_lt.ne' (Nat.dvd_one.mp h1)
  exact fc.false_of_ppart_subgroup_center_P
    (fc.sup_centralizer_W_inf_centralizer_eq_P model ind hnab) hcardS hCeq hpQ hG5

include model in
/-- **Step (11), first assertion: `R` is abelian** (p. 111–112): both branches of the
step (10) dichotomy kill a nonabelian `R` via the shared Sylow engine — case (10.1)
through `R` itself, case (10.2) through `R·C_W(P)`.  Depends on step (2)(b)
 + Higman through `step_ten_dichotomy`. -/
theorem invImageF_mul_comm
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    ∀ r₁ ∈ fc.invImageF model, ∀ r₂ ∈ fc.invImageF model, r₁ * r₂ = r₂ * r₁ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  obtain ⟨e⟩ := fc.sigma_mulEquiv_centralizer_W ind
  have hDCW : Nat.card ↥(fc.rankOneQuotient).D
      = Nat.card ↥(fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) :=
    Nat.card_congr e.toEquiv
  rcases fc.step_ten_dichotomy ind model hB2 hm with ⟨hnd, hfact⟩ | ⟨hd, -, -, -, hW, hfact⟩
  · -- case (10.1): the `R`-arm.
    refine fc.invImageF_mul_comm_of_not_dvd_card_D model ind hm ?_ ?_
    · have h1 : fc.p ^ (m + 2) = fc.p ^ ((Nat.card G).factorization fc.p) := by
        rw [hfact]
      rw [h1]
      exact (Nat.Prime.pow_dvd_iff_le_factorization fc.p_prime
        Nat.card_pos.ne').mpr le_rfl
    · rw [hDCW]
      exact hnd
  · -- case (10.2): the `R·C_W(P)`-arm.
    obtain ⟨hp3, hF9, -, hCW3, -⟩ :=
      fc.card_field_eq_nine_of_p_dvd_card_centralizer_W ind model hB2 hd
    refine fc.invImageF_mul_comm_of_card_D_eq_p model ind ?_ ?_ ?_
    · rw [hF9, hp3]
      norm_num
    · -- `p^5 ∣ |G|` from `3^{|G|_3} = 3^4·|W|`, `|W| ∈ {3, 9}`.
      rw [hp3]
      have hf5 : 5 ≤ (Nat.card G).factorization 3 := by
        rcases hW with h3 | h9
        · rw [h3] at hfact
          have h35 : (3 : ℕ) ^ ((Nat.card G).factorization 3) = 3 ^ 5 := by
            rw [hfact]; norm_num
          have := Nat.pow_right_injective (by norm_num) h35
          omega
        · rw [h9] at hfact
          have h36 : (3 : ℕ) ^ ((Nat.card G).factorization 3) = 3 ^ 6 := by
            rw [hfact]; norm_num
          have := Nat.pow_right_injective (by norm_num) h36
          omega
      exact dvd_trans (pow_dvd_pow 3 hf5)
        ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
          Nat.card_pos.ne').mpr le_rfl)
    · rw [hDCW, hCW3, hp3]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
