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

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
