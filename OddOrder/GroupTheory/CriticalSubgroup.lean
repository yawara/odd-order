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
* (S1) `centralizer_eq_self_of_maximal_abelian_normal`: Gorenstein 5.3.12.
* (S2) `isCritical_exists`: Gorenstein 5.3.11 存在定理 (two-case 構成, 完成).
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

/-- **Gorenstein "Finite Groups" Theorem 2.6.4 (`Ω₁(Z(P))` form).** A nontrivial
normal subgroup `N` of a finite `p`-group `P` meets `Ω₁(Z(P))` nontrivially: there
is `x ∈ N ∩ Z(P)` with `x ≠ 1` and `x ^ p = 1`.

Proof: `exists_mem_center_of_normal_ne_bot` gives a nonidentity `y ∈ N ∩ Z(P)`.
As `P` is a `p`-group, `orderOf y = p ^ k` with `k ≥ 1`; then `x = y ^ (p ^ (k-1))`
has order `p`, lies in `N` and in `Z(P)`, and satisfies `x ^ p = 1`. -/
theorem exists_mem_omega1_center_of_normal_ne_bot
    (hP : IsPGroup p P) {N : Subgroup P} [N.Normal] (hN : N ≠ ⊥) :
    ∃ x : P, x ∈ N ∧ x ∈ Subgroup.center P ∧ x ≠ 1 ∧ x ^ p = 1 := by
  obtain ⟨y, hyN, hyZ, hy1⟩ := exists_mem_center_of_normal_ne_bot hP hN
  -- `orderOf y = p ^ k` with `k ≥ 1`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) y
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])) hy1
    · exact hk0
  -- `x = y ^ (p ^ (k-1))` has order `p`.
  refine ⟨y ^ (p ^ (k - 1)), N.pow_mem hyN _, (Subgroup.center P).pow_mem hyZ _, ?_, ?_⟩
  · -- `x ≠ 1` because `orderOf x = p ≠ 1`.
    have hp1 : (1 : ℕ) < p := (Fact.out (p := p.Prime)).one_lt
    have hox : orderOf (y ^ (p ^ (k - 1))) = p := by
      rw [orderOf_pow_of_dvd (by positivity) (hk ▸ pow_dvd_pow p (Nat.sub_le k 1)), hk,
        Nat.div_eq_iff_eq_mul_left (by positivity) (pow_dvd_pow p (Nat.sub_le k 1)),
        ← pow_succ', Nat.sub_add_cancel hkpos]
    intro hx1
    rw [hx1, orderOf_one] at hox
    exact hp1.ne hox
  · -- `x ^ p = y ^ (p ^ k) = 1`.
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hkpos, ← hk, pow_orderOf_eq_one]

end MaximalAbelianNormal

/-! ## `Ω₁(Z(P))` as a characteristic subgroup

For the second case of Gorenstein 5.3.11 we need `Ω₁(Z(P)) = {g ∈ Z(P) | g^p = 1}`
to be characteristic in `P`, so that its preimage under a quotient map stays
characteristic (`Subgroup.Characteristic.comap_quotient_mk`). The center is abelian,
so `omega1OfAbelian P (center P) p _` is a genuine subgroup; an automorphism `φ`
preserves both `Z(P)` (characteristic) and the property `g ^ p = 1`. -/

section Omega1Center

variable {P : Type*} [Group P] {p : ℕ}

/-- `Ω₁(Z(P)) = {g ∈ Z(P) | g ^ p = 1}` packaged as a subgroup of `P` via
`omega1OfAbelian` (the center is abelian). -/
private def omega1Center (P : Type*) [Group P] (p : ℕ) : Subgroup P :=
  omega1OfAbelian P (Subgroup.center P) p
    (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)

private theorem mem_omega1Center {g : P} :
    g ∈ omega1Center P p ↔ g ∈ Subgroup.center P ∧ g ^ p = 1 := Iff.rfl

private theorem omega1Center_le_center : omega1Center P p ≤ Subgroup.center P :=
  fun _ hg => hg.1

/-- `Ω₁(Z(P))` is characteristic in `P`: any `φ : P ≃* P` preserves `Z(P)` and
`g ^ p = 1`. -/
private instance omega1Center.characteristic : (omega1Center P p).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  -- `φ g ∈ Z(P) ↔ g ∈ Z(P)` from `centerCharacteristic`.
  have hcZ : ∀ g : P, φ g ∈ Subgroup.center P ↔ g ∈ Subgroup.center P := by
    intro g
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h h'
      have := h (φ h')
      rwa [← map_mul, ← map_mul, φ.injective.eq_iff] at this
    · intro h h'
      obtain ⟨h'', rfl⟩ := φ.surjective h'
      rw [← map_mul, ← map_mul, φ.injective.eq_iff]
      exact h h''
  ext g
  simp only [Subgroup.mem_comap, mem_omega1Center, MulEquiv.coe_toMonoidHom]
  rw [hcZ g]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hpow
    have := congrArg φ.symm hpow
    rwa [map_pow, φ.symm_apply_apply, map_one] at this
  · intro hpow
    rw [← map_pow, hpow, map_one]

end Omega1Center

/-! ## Existence of a critical subgroup (Gorenstein Thm 5.3.11)

The two-case construction. We take a maximal characteristic abelian subgroup `D`.
If `D` is self-centralizing (`C_P(D) = D`) we take `C = D` directly. Otherwise
`H = C_P(D) ⊋ D` and we pass to `P̄ = P/D`, intersecting the image of `H` with
`Ω₁(Z(P̄))`; the preimage `C` is the critical subgroup with `Z(C) = D`. -/

section Existence

open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

/-- A characteristic subgroup of a characteristic subgroup is characteristic in
the ambient group (char-in-char transitivity). Needed to identify `Z(C)` as a
characteristic abelian subgroup of `P` when `C` is characteristic. -/
theorem characteristic_map_subtype_of_characteristic
    {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup H}
    (hH : H.Characteristic) (hK : K.Characteristic) :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨x, hxK, rfl⟩ := hy
  rw [Subgroup.mem_map] at hxK
  obtain ⟨k, hkK, rfl⟩ := hxK
  -- `φ` restricts to `H ≃* H` since `H` is characteristic.
  have hHfix : H.map φ.toMonoidHom = H := Subgroup.characteristic_iff_map_eq.mp hH φ
  let φH : H ≃* H := (MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr hHfix)
  have hφH_coe : ∀ h : H, (φH h : G) = φ (h : G) := fun h => rfl
  -- `K` is characteristic in `H`, so `φH k ∈ K`.
  have hk_image : φH k ∈ K :=
    (Subgroup.characteristic_iff_map_le.mp hK φH) (Subgroup.mem_map_of_mem φH.toMonoidHom hkK)
  exact ⟨φH k, hk_image, hφH_coe k⟩

/-- The predicate "`N` is a characteristic abelian subgroup" used to extract a
maximal one. -/
private def IsCharAbelian (N : Subgroup P) : Prop :=
  N.Characteristic ∧ ∀ x ∈ N, ∀ y ∈ N, x * y = y * x

/-- A finite group has a maximal characteristic abelian subgroup (the trivial
subgroup is one, and the subgroup lattice is finite hence well-founded). -/
private theorem exists_maximal_charAbelian :
    ∃ D : Subgroup P, Maximal (IsCharAbelian (P := P)) D := by
  haveI : Finite (Subgroup P) := Finite.of_injective _ (SetLike.coe_injective (A := Subgroup P))
  haveI : WellFoundedGT (Subgroup P) := Finite.to_wellFoundedGT
  obtain ⟨D, _, hD⟩ := exists_maximal_ge_of_wellFoundedGT (IsCharAbelian (P := P)) ⊥
    ⟨Subgroup.botCharacteristic, by simp⟩
  exact ⟨D, hD⟩

omit [Finite P] in
/-- If `C` is characteristic, then `Z(C)` (as an ambient subgroup) is a
characteristic abelian subgroup of `P`. -/
private theorem center_map_subtype_isCharAbelian {C : Subgroup P} (hC : C.Characteristic) :
    IsCharAbelian ((Subgroup.center ↥C).map C.subtype) := by
  refine ⟨characteristic_map_subtype_of_characteristic hC Subgroup.centerCharacteristic, ?_⟩
  rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg C.subtype ((Subgroup.mem_center_iff.mp hx' y').symm)

/-- **Gorenstein "Finite Groups" Theorem 5.3.11** (J. G. Thompson). Every finite
`p`-group `P` possesses a **critical subgroup** `C`: a characteristic subgroup with
`cl(C) ≤ 2`, `[P, C] ⊆ Z(C)`, and `C_P(C) = Z(C)` (self-centralizing).

This is the existence half of the definition; the derived faithfulness property
(every nontrivial `p'`-automorphism acts nontrivially) is `IsCritical`-downstream.
`S2` of `notes/bg/thm113_design.md`.

Proof (Gorenstein, two cases). Let `D` be a maximal characteristic abelian
subgroup and `H = C_P(D)`.

* If `H = D`, then `C = D` is critical: `D` is abelian (`cl = 1`), characteristic,
  `[P, D] ⊆ D = Z(D)`, and `C_P(D) = D = Z(D)`.
* If `D < H`, pass to `P̄ = P/D`. The image `H̄` of `H` is a nontrivial normal
  subgroup, so it meets `Ω₁(Z(P̄))`. Let `C` be the preimage of
  `C̄ = H̄ ∩ Ω₁(Z(P̄))`. Then `C = H ∩ K` (with `K` the preimage of `Ω₁(Z(P̄))`,
  characteristic by `Characteristic.comap_quotient_mk`) is characteristic;
  `D ⊆ Z(C)` (as `C ⊆ H` centralizes `D`); `Z(C) = D` by maximality of `D`;
  `C/Z(C) = C̄` is elementary abelian (so `cl(C) ≤ 2`); `[P, C] ⊆ D = Z(C)`
  (as `C̄ ⊆ Z(P̄)`); and `C_P(C) = Z(C)` via the second-center theorem applied to
  `C_P(C)/D`. -/
theorem isCritical_exists (hG : IsPGroup p P) : ∃ C : Subgroup P, IsCritical C := by
  obtain ⟨D, hD_max⟩ := exists_maximal_charAbelian (P := P)
  obtain ⟨hD_char, hD_ab⟩ := hD_max.prop
  haveI : D.Characteristic := hD_char
  -- `H = C_P(D)`, characteristic, and `D ≤ H` since `D` is abelian.
  set H := Subgroup.centralizer (D : Set P) with hH_def
  haveI hH_char : H.Characteristic := Subgroup.characteristic_centralizer
  have hDH : D ≤ H := by
    intro d hd
    rw [hH_def, Subgroup.mem_centralizer_iff]
    exact fun g hg => hD_ab g hg d hd
  -- Case split on whether `D` is self-centralizing.
  -- `D` abelian ⇒ `Z(D) = ⊤`, so `(Z(D)).map subtype = D`.
  have hcenterD : Subgroup.center ↥D = ⊤ := by
    rw [Subgroup.center_eq_top_iff, isMulCommutative_iff]
    exact fun x y => Subtype.ext (hD_ab x x.2 y y.2)
  have hZD : (Subgroup.center ↥D).map D.subtype = D := by
    rw [hcenterD, ← MonoidHom.range_eq_map, D.range_subtype]
  by_cases hcase : H ≤ D
  · -- **Case A**: `C_P(D) = D`. Take `C = D`.
    have hHD : H = D := le_antisymm hcase hDH
    haveI : D.Normal := inferInstance
    refine ⟨D, hD_char, ?_, ?_, ?_⟩
    · -- `commutator ↥D ≤ center ↥D = ⊤`.
      rw [hcenterD]; exact le_top
    · -- `[P, D] ⊆ Z(D).map subtype = D`.
      rw [hZD]; exact Subgroup.commutator_le_right _ _
    · -- `C_P(D) = Z(D).map subtype = D`.
      rw [hZD, ← hH_def, hHD]
  · -- **Case B**: `D < H`.
    have hDH_lt : D < H := lt_of_le_of_ne hDH (fun h => hcase (h ▸ le_rfl))
    -- Pass to `P̄ = P / D`.
    set q := QuotientGroup.mk' D with hq_def
    have hPbar : IsPGroup p (P ⧸ D) := hG.to_quotient D
    -- `K = preimage of Ω₁(Z(P̄))`, characteristic in `P`.
    set K := (omega1Center (P ⧸ D) p).comap q with hK_def
    haveI hK_char : K.Characteristic :=
      Subgroup.Characteristic.comap_quotient_mk omega1Center.characteristic
    -- `C = H ⊓ K`.
    set C := H ⊓ K with hC_def
    -- `C` is characteristic (`H`, `K` both characteristic).
    have hC_char : C.Characteristic := by
      rw [hC_def, Subgroup.characteristic_iff_comap_eq]
      intro φ
      rw [Subgroup.comap_inf, Subgroup.characteristic_iff_comap_eq.mp hH_char φ,
        Subgroup.characteristic_iff_comap_eq.mp hK_char φ]
    -- `q x = 1 ↔ x ∈ D`.
    have hker : ∀ x : P, q x = 1 ↔ x ∈ D := fun x => by
      rw [hq_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    -- `D ≤ K` (kernel maps to `1 ∈ Ω₁(Z(P̄))`).
    have hDK : D ≤ K := by
      intro d hd
      rw [hK_def, Subgroup.mem_comap, (hker d).mpr hd]
      exact one_mem _
    -- `D ≤ C`.
    have hDC : D ≤ C := le_inf hDH hDK
    -- For `c ∈ C`, `q c ∈ Z(P̄)`.
    have hqc_center : ∀ c ∈ C, q c ∈ Subgroup.center (P ⧸ D) := by
      intro c hc
      exact omega1Center_le_center (Subgroup.mem_comap.mp hc.2)
    -- (F-CD) `D` is central in `C`: every `c ∈ C ⊆ H = C_P(D)` centralizes `D`.
    have hDcentralC : ∀ d ∈ D, ∀ c ∈ C, d * c = c * d := by
      intro d hd c hc
      have : c ∈ Subgroup.centralizer (D : Set P) := hc.1
      exact Subgroup.mem_centralizer_iff.mp this d hd
    -- Membership bridge: `x ∈ C` centralizing all of `C` lies in `Z(C)`-image.
    have hmem_ZC : ∀ x : P, x ∈ C → (∀ c ∈ C, x * c = c * x) →
        x ∈ (Subgroup.center ↥C).map C.subtype := by
      intro x hxC hxcent
      have hcent : (⟨x, hxC⟩ : ↥C) ∈ Subgroup.center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro c
        exact Subtype.ext (hxcent c c.2).symm
      exact Subgroup.mem_map_of_mem C.subtype hcent
    -- `(center ↥C).map subtype = D` (bridge), via maximality of `D`.
    have hD_le_ZC : D ≤ (Subgroup.center ↥C).map C.subtype :=
      fun d hd => hmem_ZC d (hDC hd) (fun c hc => hDcentralC d hd c hc)
    have hZC : (Subgroup.center ↥C).map C.subtype = D := by
      refine le_antisymm ?_ hD_le_ZC
      exact hD_max.le_of_ge (center_map_subtype_isCharAbelian hC_char) hD_le_ZC
    refine ⟨C, hC_char, ?_, ?_, ?_⟩
    · -- (i) `commutator ↥C ≤ center ↥C`: `[c, c'] ∈ D` since `q c, q c'` central.
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← Subgroup.mem_map_iff_mem C.subtype_injective, hZC, map_commutatorElement]
      have hcomm : q ⁅C.subtype a, C.subtype b⁆ = 1 := by
        rw [map_commutatorElement]
        exact Commute.commutator_eq
          (Subgroup.mem_center_iff.mp (hqc_center a a.2) (q (C.subtype b))).symm
      exact (hker _).mp hcomm
    · -- (ii) `⁅⊤, C⁆ ≤ (center ↥C).map subtype = D`.
      rw [hZC, Subgroup.commutator_le]
      intro g _ c hc
      have hcomm : q ⁅g, c⁆ = 1 := by
        rw [map_commutatorElement]
        exact Commute.commutator_eq
          (Subgroup.mem_center_iff.mp (hqc_center c hc) (q g))
      exact (hker _).mp hcomm
    · -- (iii) `C_P(C) = (center ↥C).map subtype = D`.
      rw [hZC]
      refine le_antisymm ?_ ?_
      · -- `C_P(C) ≤ D`: any element centralizing `C` lies in `C` (second center), then in `D`.
        -- First, `Q := C_P(C)` is contained in `H = C_P(D)` (it centralizes `D ⊆ C`).
        have hQH : Subgroup.centralizer (C : Set P) ≤ H := by
          intro x hx
          rw [hH_def, Subgroup.mem_centralizer_iff]
          intro d hd
          exact (Subgroup.mem_centralizer_iff.mp hx d (hDC hd))
        -- `Q ≤ C`.
        have hQC : Subgroup.centralizer (C : Set P) ≤ C := by
          by_contra hQnotC
          rw [SetLike.not_le_iff_exists] at hQnotC
          obtain ⟨q₀, hq₀Q, hq₀C⟩ := hQnotC
          -- `Q̄ := Q.map q` is normal and nontrivial.
          haveI hQchar : (Subgroup.centralizer (C : Set P)).Characteristic :=
            Subgroup.characteristic_centralizer (H := C) (hH := hC_char)
          set Qbar := (Subgroup.centralizer (C : Set P)).map q with hQbar_def
          haveI : Qbar.Normal :=
            Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective D)
          have hQbar_ne : Qbar ≠ ⊥ := by
            intro hbot
            apply hq₀C
            have hmem : q q₀ ∈ Qbar := Subgroup.mem_map_of_mem q hq₀Q
            rw [hbot, Subgroup.mem_bot] at hmem
            exact hDC ((hker q₀).mp hmem)
          -- Second center: `Q̄ ∩ Ω₁(Z(P̄)) ≠ 1`.
          obtain ⟨xbar, hxbarQ, hxbarZ, hxbar_ne, hxbar_p⟩ :=
            exists_mem_omega1_center_of_normal_ne_bot hPbar hQbar_ne
          -- Lift `xbar` to `q'' ∈ Q`.
          rw [hQbar_def, Subgroup.mem_map] at hxbarQ
          obtain ⟨q'', hq''Q, hq''eq⟩ := hxbarQ
          -- `q'' ∈ H` (since `Q ≤ H`) and `q q'' ∈ Ω₁(Z(P̄))`, so `q'' ∈ K`, hence `q'' ∈ C`.
          have hq''K : q'' ∈ K := by
            rw [hK_def, Subgroup.mem_comap, hq''eq, mem_omega1Center]
            exact ⟨hxbarZ, hxbar_p⟩
          have hq''C : q'' ∈ C := Subgroup.mem_inf.mpr ⟨hQH hq''Q, hq''K⟩
          -- `q''` centralizes `C` and lies in `C`, so `q'' ∈ Z(C)`-image `= D`, giving `q q'' = 1`.
          have hq''ZC : q'' ∈ (Subgroup.center ↥C).map C.subtype :=
            hmem_ZC q'' hq''C (fun c hc =>
              (Subgroup.mem_centralizer_iff.mp hq''Q c hc).symm)
          rw [hZC] at hq''ZC
          have : q q'' = 1 := (hker q'').mpr hq''ZC
          rw [hq''eq] at this
          exact hxbar_ne this
        -- Now `Q ≤ C` and `Q` centralizes `C`, so `Q ⊆ Z(C)`-image `= D`.
        intro x hx
        have hxC : x ∈ C := hQC hx
        have := hmem_ZC x hxC (fun c hc => (Subgroup.mem_centralizer_iff.mp hx c hc).symm)
        rwa [hZC] at this
      · -- `D ≤ C_P(C)`: `D` centralizes `C` (F-CD).
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact (hDcentralC d hd c hc).symm

end Existence

end OddOrder.GroupTheory
