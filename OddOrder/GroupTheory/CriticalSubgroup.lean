/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.OmegaSubgroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Critical subgroups (Gorenstein Thm 5.3.11 / 5.3.13)

`OddOrder.GroupTheory` shared module: Thompson の **critical subgroup**.

**BG Theorem 1.13** (J. G. Thompson, `references/bg/local-analysis.mmd:461`) の土台.
BG は証明本体を **Gorenstein "Finite Groups" Thm 5.3.11 (critical の存在) + 5.3.13
(`Ω₁(C)` の性質)** に委譲する. Isaacs に対応定理は無い (3 調査で確認) ため,
CLAUDE.md が定める「`G, Thm` 引用で Isaacs が欠く場合のみ Gorenstein 原文参照」ケース.
原典: `references/gorenstein/finite-groups.mmd` L3878-3945. 設計: `notes/bg/thm113_design.md`.

## Main definitions

* `IsCritical C`: `C ≤ G` が critical (Gorenstein 5.3.11 の (i)(ii)(iii)):
  characteristic, `cl(C) ≤ 2`, `[G,C] ≤ Z(C)`, `C_G(C) = Z(C)`.

## Main results (段階実装, `notes/bg/thm113_design.md` の S1-S8)

* `IsCritical.*`: 射影 (本ファイル).
* (予定 S1-S2) `isCritical_exists`: Gorenstein 5.3.11 存在定理.
* (予定 S6) `IsCritical.omega1_exponent`: 5.3.13 = `Ω₁(C)` exponent `p` (odd).
* (予定 S3-S7) faithful `p'`-action, `C_{Aut G}(Ω₁ C)` が `p`-群.

## Implementation notes

predicate `IsCritical : Subgroup G → Prop` を採用 (mathlib 互換, no-wrapper 方針).
`G` 自身が `p`-群の文脈で `C ≤ G` を critical と呼ぶ (Gorenstein の `P = G = ⊤`).
Gorenstein の (i) は `C/Z(C)` elementary abelian も含むが, それは (i-a)+commutator
から導出可能なので def には入れず補題で与える.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Gorenstein "Finite Groups" Thm 5.3.11** の条件を満たす部分群 `C ≤ G` =
`G` の **critical subgroup**:

* (char) `C` は `G` で characteristic;
* (i) `cl(C) ≤ 2`, すなわち `⁅C, C⁆ ≤ Z(C)`;
* (ii) `[G, C] ≤ Z(C)` (ambient `G` 側で, `Z(C)` は `C.subtype` 像);
* (iii) `C_G(C) = Z(C)` (self-centralizing).

Gorenstein の (i) に含まれる `C/Z(C)` elementary abelian は導出可能なので
def には入れない. -/
def IsCritical (C : Subgroup G) : Prop :=
  C.Characteristic
    ∧ _root_.commutator ↥C ≤ Subgroup.center ↥C
    ∧ ⁅(⊤ : Subgroup G), C⁆ ≤ (Subgroup.center ↥C).map C.subtype
    ∧ Subgroup.centralizer (C : Set G) = (Subgroup.center ↥C).map C.subtype

namespace IsCritical

variable {C : Subgroup G}

/-- critical ⇒ `C` characteristic. -/
theorem characteristic (hC : IsCritical C) : C.Characteristic := hC.1

/-- critical ⇒ `cl(C) ≤ 2` (`⁅C, C⁆ ≤ Z(C)`). -/
theorem commutator_le_center (hC : IsCritical C) :
    _root_.commutator ↥C ≤ Subgroup.center ↥C := hC.2.1

/-- critical ⇒ `[G, C] ≤ Z(C)` (ambient `G`). -/
theorem commutator_top_le_center (hC : IsCritical C) :
    ⁅(⊤ : Subgroup G), C⁆ ≤ (Subgroup.center ↥C).map C.subtype := hC.2.2.1

/-- critical ⇒ `C_G(C) = Z(C)` (self-centralizing). -/
theorem centralizer_eq (hC : IsCritical C) :
    Subgroup.centralizer (C : Set G) = (Subgroup.center ↥C).map C.subtype := hC.2.2.2

end IsCritical

/-! ## Gorenstein Lemma 5.3.12: self-centralizing maximal abelian normal subgroup

If `M` is a normal subgroup of a `p`-group `P` that is maximal subject to being
abelian, then `C_P(M) = M`. This is `S1` of `notes/bg/thm113_design.md`, a
prerequisite for the existence of critical subgroups (Gorenstein 5.3.11). -/

section MaximalAbelianNormal

variable {P : Type*} [Group P]

/-- A nontrivial normal subgroup `K` of a finite `p`-group meets the center
nontrivially: there is a nonidentity element of `K` lying in `Z(P)`.

Proof mirrors `IsPGroup.center_nontrivial`: `ConjAct P` is a `p`-group acting on
`↥K` by conjugation (well-defined as `K` is normal); its fixed points are the
elements of `K` central in `P`. Fixed-point counting (`p ∣ |K|` since `K ≠ ⊥`,
and `1` is a fixed point) yields a second fixed point. -/
private theorem exists_mem_center_of_normal_ne_bot {p : ℕ} [Fact p.Prime] [Finite P]
    (hP : IsPGroup p P) {K : Subgroup P} [K.Normal] (hK : K ≠ ⊥) :
    ∃ x : P, x ∈ K ∧ x ∈ Subgroup.center P ∧ x ≠ 1 := by
  -- `ConjAct P` is a `p`-group acting on `↥K`.
  have hConj : IsPGroup p (ConjAct P) := hP.of_equiv ConjAct.toConjAct
  -- `p ∣ |K|` since `K` is a nontrivial finite `p`-group.
  have hKp : IsPGroup p K := hP.to_subgroup K
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
  have hdvd : p ∣ Nat.card K := by
    obtain ⟨n, hn0, hn⟩ := hKp.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  -- `1 : ↥K` is a fixed point of the conjugation action.
  have h1fix : (1 : K) ∈ MulAction.fixedPoints (ConjAct P) K := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    rw [ConjAct.Subgroup.val_conj_smul]
    simp
  -- A second fixed point exists.
  obtain ⟨b, hb_fix, hb_ne⟩ :=
    hConj.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := K) hdvd h1fix
  refine ⟨(b : P), b.2, ?_, ?_⟩
  · -- A fixed point of conjugation is central in `P`.
    rw [Subgroup.mem_center_iff]
    intro g
    have hfix := (MulAction.mem_fixedPoints.mp hb_fix) (ConjAct.toConjAct g)
    have hval : ((ConjAct.toConjAct g • b : K) : P) = g * (b : P) * g⁻¹ := by
      rw [ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul]
    rw [Subtype.ext_iff, hval] at hfix
    -- `g * b * g⁻¹ = b` ⟺ `g * b = b * g`.
    rwa [mul_inv_eq_iff_eq_mul] at hfix
  · -- `b ≠ 1` in `↥K` gives `(b : P) ≠ 1`.
    exact fun h => hb_ne (Subtype.ext (by simpa using h.symm))

variable [Finite P] {p : ℕ} [Fact p.Prime]

/-- **Gorenstein "Finite Groups" Lemma 5.3.12.** If `M` is a normal subgroup of a
finite `p`-group `P` that is maximal subject to being abelian, then `M` is
self-centralizing: `C_P(M) = M`.

`hM_comm` witnesses that `M` is abelian, and `hM_max` its maximality among abelian
normal subgroups (any abelian normal `N ⊇ M` equals `M`).

Proof (Gorenstein): `M ≤ H := C_P(M)` since `M` is abelian. If `M < H`, pass to
`P̄ = P/M`; the image `H̄` is normal and nonzero, so it meets `Z(P̄)` in a
nonidentity central element `x̄`. The preimage `X` of `⟨x̄⟩` is normal in `P`,
contains `M`, has `M ≤ Z(X)` (as `X ≤ H` centralizes `M`), and `X/M ≅ ⟨x̄⟩` is
cyclic, hence `X` is abelian. Then `M < X` contradicts maximality of `M`. -/
theorem centralizer_eq_self_of_maximal_abelian_normal
    (hP : IsPGroup p P) {M : Subgroup P} [M.Normal]
    (hM_comm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hM_max : ∀ N : Subgroup P, N.Normal → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) →
      M ≤ N → N = M) :
    Subgroup.centralizer (M : Set P) = M := by
  -- `M ≤ C_P(M)` because `M` is abelian.
  have hM_le : M ≤ Subgroup.centralizer (M : Set P) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hM_comm h hh m hm)
  refine le_antisymm ?_ hM_le
  -- Suppose `C_P(M) ⊄ M`; derive a contradiction.
  by_contra hnot
  -- Then `M < H := C_P(M)`.
  set H := Subgroup.centralizer (M : Set P) with hH_def
  have hMH : M < H := lt_of_le_of_ne hM_le (fun h => hnot (h ▸ le_refl _))
  -- `H` is normal in `P` (centralizer of a normal subgroup).
  haveI : H.Normal := inferInstance
  -- Image of `H` in `P̄ = P/M`.
  set q := QuotientGroup.mk' M with hq_def
  set Hbar := H.map q with hHbar_def
  haveI : Hbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective M)
  -- `H̄ ≠ ⊥`: pick `h ∈ H \ M`, then `q h ≠ 1`.
  have hHbar_ne : Hbar ≠ ⊥ := by
    obtain ⟨h, hhH, hhM⟩ := SetLike.exists_of_lt hMH
    intro hbot
    apply hhM
    have : q h ∈ Hbar := Subgroup.mem_map_of_mem q hhH
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff h).mp this
  -- `P̄` is a `p`-group.
  have hPbar : IsPGroup p (P ⧸ M) := hP.to_quotient M
  -- A nonidentity central element of `H̄`.
  obtain ⟨xbar, hxbar_H, hxbar_center, hxbar_ne⟩ :=
    exists_mem_center_of_normal_ne_bot hPbar hHbar_ne
  -- `⟨x̄⟩` is central, hence normal; its preimage `X` is normal in `P`.
  have hzp_le_center : Subgroup.zpowers xbar ≤ Subgroup.center (P ⧸ M) :=
    Subgroup.zpowers_le.mpr hxbar_center
  haveI hzp_normal : (Subgroup.zpowers xbar).Normal :=
    { conj_mem := fun n hn g => by
        rw [Subgroup.mem_center_iff.mp (hzp_le_center hn) g, mul_assoc,
          mul_inv_cancel, mul_one]
        exact hn }
  -- The preimage `X` of `⟨x̄⟩` in `P`; it is normal in `P`.
  set X := (Subgroup.zpowers xbar).comap q with hX_def
  haveI : X.Normal := inferInstance
  -- `M ≤ X` (since `q` sends `M` to `1 ∈ ⟨x̄⟩`).
  have hMX : M ≤ X := by
    intro m hm
    rw [hX_def, Subgroup.mem_comap, hq_def, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff m).mpr hm]
    exact one_mem _
  -- `X ≤ H`: `X ≤ comap q H̄ = H ⊔ M = H`.
  have hXH : X ≤ H := by
    have h1 : X ≤ Hbar.comap q :=
      Subgroup.comap_mono (Subgroup.zpowers_le.mpr hxbar_H)
    have h2 : Hbar.comap q = M ⊔ H := by
      rw [hHbar_def, hq_def, QuotientGroup.comap_map_mk']
    rw [h2, sup_eq_right.mpr hMH.le] at h1
    exact h1
  -- `f : ↥X →* ⟨x̄⟩`, the quotient map restricted to `X`.
  have hf_mem : ∀ g : X, q (g : P) ∈ Subgroup.zpowers xbar := fun g => g.2
  set f : X →* Subgroup.zpowers xbar :=
    (q.comp X.subtype).codRestrict (Subgroup.zpowers xbar) hf_mem with hf_def
  -- `ker f ≤ Z(X)`: `f g = 1 ⟹ g ∈ M`, and `X ≤ H = C_P(M)` centralizes `M`.
  have hker : f.ker ≤ Subgroup.center X := by
    intro g hg
    rw [MonoidHom.mem_ker, hf_def] at hg
    have hgM : (g : P) ∈ M := by
      have : q (g : P) = 1 := by
        have := congrArg (Subtype.val) hg
        simpa [MonoidHom.codRestrict_apply] using this
      exact (QuotientGroup.eq_one_iff (g : P)).mp this
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    -- `h ∈ X ≤ H = C_P(M)` commutes with `g ∈ M`.
    have hhH : (h : P) ∈ Subgroup.centralizer (M : Set P) := hXH h.2
    have := Subgroup.mem_centralizer_iff.mp hhH (g : P) hgM
    simpa using this.symm
  -- `X` is abelian (cyclic quotient by central kernel).
  have hX_comm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    have := commutative_of_cyclic_center_quotient f hker ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  -- `X = M` by maximality, but `x ∈ X \ M` — contradiction.
  obtain ⟨x, hx_eq⟩ := QuotientGroup.mk'_surjective M xbar
  have hxX : x ∈ X := by
    rw [hX_def, Subgroup.mem_comap, hq_def, hx_eq]
    exact Subgroup.mem_zpowers xbar
  have hxM : x ∉ M := by
    intro hmem
    apply hxbar_ne
    rw [← hx_eq, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff x).mpr hmem
  have hXeqM : X = M := hM_max X inferInstance hX_comm hMX
  exact hxM (hXeqM ▸ hxX)

end MaximalAbelianNormal

end OddOrder.GroupTheory
