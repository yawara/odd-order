/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTen

/-!
# Peterfalvi Part II, Ch. II, step (11): `R = T × P` and the regular action

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (11), p. 111.

Step (11) sets `R` := the inverse image of `F` in `G` — the preimage of the
translation subgroup `emb(F) ⊴ C_G(P)/N` under the quotient map
`C_G(P) → C_G(P)/N`, pushed forward along `C_G(P) ↪ G` — and proves:

* `R = T × P`, with `T` a subgroup normalized by `C_Q(P)·C_W(P)` and
  `T ⋊ C_Q(P) ≅ F ⋊ F^*`;
* `C_Q(P)` acts regularly on `𝒜 − {P}`, where `𝒜` denotes the set of
  subgroups of `R` of order `p` which are not contained in `T`.

This file lays the **construction layer**: the definition `invImageF` of `R`
and its first structural facts (`R ≤ C_G(P)`, `P ≤ R`, membership transport
to the quotient).  The abelianity of `R`, the `T = [R, s]` decomposition and
the regularity claim land in subsequent commits (campaign issue 2053; proof
plan recorded there from the p. 111 reading).
-/

set_option autoImplicit false

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
      ≤ Subgroup.normalizer (fc.P : Set G) := by
  set R : Subgroup G := fc.invImageF model with hRdef
  have hZP := fc.center_eq_P_of_not_isMulCommutative model ind hnab
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  intro x
  -- conjugation by `g` preserves `R ⊓ C_G(R)`, which equals `P`.
  have key : ∀ y : G, y ∈ R ⊓ Subgroup.centralizer (R : Set G) ↔
      g * y * g⁻¹ ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
    intro y
    constructor
    · rintro ⟨hyR, hyC⟩
      refine ⟨(hg y).mp hyR, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hr' : g⁻¹ * r * g ∈ R := by
        have h1 := (hg (g⁻¹ * r * g)).mpr
        simp only [mul_assoc, mul_inv_cancel_left] at h1 ⊢
        exact h1 (by simpa [mul_assoc] using hr)
      have hc := Subgroup.mem_centralizer_iff.mp hyC _ hr'
      -- `(g⁻¹ r g)·y = y·(g⁻¹ r g)` ⟹ `r·(g y g⁻¹) = (g y g⁻¹)·r`
      have h2 := congrArg (fun z => g * z * g⁻¹) hc
      simpa [mul_assoc] using h2
    · rintro ⟨hyR, hyC⟩
      refine ⟨(hg y).mpr hyR, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hr' : g * r * g⁻¹ ∈ R := (hg r).mp hr
      have hc := Subgroup.mem_centralizer_iff.mp hyC _ hr'
      -- `(g r g⁻¹)·(g y g⁻¹) = (g y g⁻¹)·(g r g⁻¹)` ⟹ `r y = y r`
      have h2 := congrArg (fun z => g⁻¹ * z * g) hc
      simpa [mul_assoc] using h2
  rw [← hZP]
  exact key x

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
