/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.SetTheory.Cardinal.Finite
import OddOrder.GroupTheory.SemiDihedral
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch04_Commutators.Main

/-!
# OddOrder.Isaacs.Ch06 — Frobenius Actions

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 6
"Frobenius Actions" (pp. 177-200) の Lean 化.

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 6A | Frobenius action の定義と equivalences | 6.1 – 6.7 | 進行中: 6.1/6.2/6.3/6.4/6.5/6.6 ✅, 6.7 保留 |
| 6B | Frobenius complement Sylow 構造 | 6.8 – 6.21 | 進行中: 6.13/6.14/6.16 ✅ |
| 6C | Frobenius kernel nilpotent + Thompson | 6.22 – 6.24 | 未着手 |

## 方針

mathlib カバレッジ薄 (~21%; `DihedralGroup`/`QuaternionGroup` の具体群以外は新規実装).
**`FrobeniusGroup` / `FrobeniusAction` は mathlib 完全未収載** — 本ファイルで一次定義.

設計: Isaacs 本文に従い **action ベース** (`IsFrobeniusAction A N` on `MulDistribMulAction A N`) を
中核に置き, subgroup-pair 版 (`IsFrobeniusGroup G N A`) は conjugation action で導出.

## 先行章依存

本ファイル §6A の実装済み範囲は, 6.2 が Ch.4 forward の Cor 3.28 を使う以外,
大きな先行章依存なし. 6.7 (Schur-Zassenhaus / Ch.5 normal p-complement 周辺) は保留.

ノート: [`notes/isaacs/ch06_frobenius_actions.md`](../../notes/isaacs/ch06_frobenius_actions.md)
-/

namespace OddOrder.Isaacs.Ch06

section /- 6A: Frobenius action basics (pp. 177-183) -/

/-! ### Definition of Frobenius action

Isaacs Defn (p. 177): an action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity
element of `A` fixes any nonidentity element of `N`. Equivalently `C_N(a) = 1` for all `1 ≠ a ∈ A`,
or `C_A(n) = 1` for all `1 ≠ n ∈ N`, or the action of `A` on `N \ {1}` is semiregular. -/

/-- An action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity element of `A`
fixes any nonidentity element of `N`.

Isaacs p. 177: "the action of `A` on `N` is said to be Frobenius if `n^a ≠ n` whenever `n ∈ N`
and `a ∈ A` are nonidentity elements." -/
def IsFrobeniusAction (A N : Type*) [Group A] [Group N] [MulDistribMulAction A N] : Prop :=
  ∀ a : A, a ≠ 1 → ∀ n : N, n ≠ 1 → a • n ≠ n

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

namespace IsFrobeniusAction

/-- The orbit of `1 ∈ N` under any `MulDistribMulAction` is `{1}`. (Structural, not Frobenius.) -/
theorem orbit_one : MulAction.orbit A (1 : N) = {1} := by
  ext n
  simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩; exact smul_one a
  · rintro rfl; exact ⟨1, smul_one 1⟩

/-- **Frobenius action ⇒ stabilizer trivial on nonidentity.** -/
theorem stabilizer_eq_bot (h : IsFrobeniusAction A N) {n : N} (hn : n ≠ 1) :
    MulAction.stabilizer A n = ⊥ := by
  ext a
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  refine ⟨fun hax => ?_, ?_⟩
  · by_contra ha; exact h a ha n hn hax
  · rintro rfl; exact one_smul A n

/-- **Frobenius action: `fixedBy N a = {1}` for `a ≠ 1`.** -/
theorem fixedBy_eq_singleton_one (h : IsFrobeniusAction A N) {a : A} (ha : a ≠ 1) :
    MulAction.fixedBy N a = {1} := by
  ext n
  simp only [MulAction.mem_fixedBy, Set.mem_singleton_iff]
  refine ⟨fun hn => ?_, ?_⟩
  · by_contra hne; exact h a ha n hne hn
  · rintro rfl; exact smul_one a

@[reducible] def invariantSubgroupMulDistribMulAction (M : Subgroup N)
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : MulDistribMulAction A M := by
  letI : SMul A M := ⟨fun a m => ⟨a • (m : N), hM a m m.2⟩⟩
  exact Subtype.coe_injective.mulDistribMulAction M.subtype (fun _ _ => rfl)

/-- A Frobenius action restricts to every invariant subgroup. -/
theorem subgroup (h : IsFrobeniusAction A N) (M : Subgroup N)
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) :
    @IsFrobeniusAction A M _ _ (invariantSubgroupMulDistribMulAction M hM) := by
  letI : MulDistribMulAction A M := invariantSubgroupMulDistribMulAction M hM
  intro a ha m hm hfix
  have hmN : (m : N) ≠ 1 := fun hmN => hm (Subtype.ext hmN)
  exact h a ha (m : N) hmN (Subtype.ext_iff.mp hfix)

/-- A Frobenius action remains Frobenius after restricting the acting group to a subgroup. -/
theorem actorSubgroup (h : IsFrobeniusAction A N) (B : Subgroup A) :
    IsFrobeniusAction B N := by
  intro b hb n hn hfix
  have hbA : (b : A) ≠ 1 := fun hbA => hb (Subtype.ext hbA)
  exact h (b : A) hbA n hn (by simpa using hfix)

@[reducible] def invariantQuotientMulAut (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) (a : A) : MulAut (N ⧸ M) := by
  let f : N ⧸ M →* N ⧸ M :=
    QuotientGroup.map M M (MulDistribMulAction.toMulAut A N a).toMonoidHom
      (by
        intro m hm
        exact hM a m hm)
  let g : N ⧸ M →* N ⧸ M :=
    QuotientGroup.map M M (MulDistribMulAction.toMulAut A N a⁻¹).toMonoidHom
      (by
        intro m hm
        exact hM a⁻¹ m hm)
  exact MonoidHom.toMulEquiv f g
    (by
      ext n
      simp [f, g])
    (by
      ext n
      simp [f, g])

@[reducible] def invariantQuotientMulAutHom (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : A →* MulAut (N ⧸ M) where
  toFun := invariantQuotientMulAut M hM
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro n
    simp [invariantQuotientMulAut]
  map_mul' := by
    intro a b
    ext q
    refine QuotientGroup.induction_on q ?_
    intro n
    simp [invariantQuotientMulAut, mul_smul]

@[reducible] def invariantQuotientMulDistribMulAction (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : MulDistribMulAction A (N ⧸ M) :=
  MulDistribMulAction.compHom (N ⧸ M) (invariantQuotientMulAutHom M hM)

/-- **Isaacs Lemma 6.1**: a Frobenius action gives `|N| ≡ 1 (mod |A|)`.

Proof via Burnside's lemma:
`∑_{a ∈ A} |fixedBy N a| = (#orbits) * |A|`. For `a = 1` the fixed-set is all of `N` (size `|N|`),
and for `a ≠ 1` it is `{1}` (size 1). So `|N| + (|A| - 1) = (#orbits) * |A|`, hence
`|A| ∣ |N| - 1`. -/
theorem card_modEq_one [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Fintype.card N ≡ 1 [MOD Fintype.card A] := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient A N) := Quotient.fintype _
  -- Burnside.
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group A N
  -- Compute LHS: split `a = 1` from `a ≠ 1`.
  have h_one : Fintype.card (MulAction.fixedBy N (1 : A)) = Fintype.card N := by
    have h_eq : MulAction.fixedBy N (1 : A) = Set.univ := by
      ext n; simp
    calc Fintype.card (MulAction.fixedBy N (1 : A))
        = Fintype.card ((Set.univ : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = Fintype.card N := Fintype.card_congr (Equiv.Set.univ N)
  have h_other : ∀ a ∈ Finset.univ.erase (1 : A),
      Fintype.card (MulAction.fixedBy N a) = 1 := by
    intro a ha
    have ha_ne : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have h_eq := fixedBy_eq_singleton_one h ha_ne
    calc Fintype.card (MulAction.fixedBy N a)
        = Fintype.card (({1} : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = 1 := by simp
  have hLHS : ∑ a : A, Fintype.card (MulAction.fixedBy N a)
            = Fintype.card N + (Fintype.card A - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : A)), h_one,
        Finset.sum_congr rfl h_other, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, add_comm]
  rw [hLHS] at hburn
  -- Now: |N| + (|A| - 1) = (#orbits) * |A|, so |A| ∣ |N| - 1.
  haveI : Nonempty (MulAction.orbitRel.Quotient A N) := ⟨⟦1⟧⟩
  set k := Fintype.card (MulAction.orbitRel.Quotient A N)
  set a := Fintype.card A
  set n := Fintype.card N
  have ha_pos : 0 < a := Fintype.card_pos
  have hn_pos : 0 < n := Fintype.card_pos
  have hk_pos : 0 < k := Fintype.card_pos
  -- |N| - 1 = a * (k - 1).
  have hdvd : a ∣ n - 1 := by
    refine ⟨k - 1, ?_⟩
    rw [mul_comm a (k - 1), tsub_mul, one_mul]
    omega
  exact ((Nat.modEq_iff_dvd' hn_pos).mpr hdvd).symm

/-- Corollary of Lemma 6.1: a Frobenius action implies `|N|` and `|A|` are coprime. -/
theorem coprime_card [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Nat.Coprime (Fintype.card N) (Fintype.card A) := by
  unfold Nat.Coprime
  rw [(card_modEq_one h).gcd_eq, Nat.gcd_one_left]

/-- **Isaacs Corollary 6.2**: a Frobenius action descends to every invariant normal quotient. -/
theorem quotient [Finite A] [Finite N] (h : IsFrobeniusAction A N) (M : Subgroup N)
    [M.Normal] (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) :
    @IsFrobeniusAction A (N ⧸ M) _ _ (invariantQuotientMulDistribMulAction M hM) := by
  classical
  letI : MulDistribMulAction A (N ⧸ M) := invariantQuotientMulDistribMulAction M hM
  intro a ha q hq_ne hfix
  revert hq_ne hfix
  refine QuotientGroup.induction_on q ?_
  intro n hq_ne hfix
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let P : Subgroup A :=
    { carrier := {b | ∃ m ∈ M, φ b n = n * m}
      one_mem' := by
        refine ⟨1, M.one_mem, ?_⟩
        simp [φ]
      mul_mem' := by
        intro b c hb hc
        rcases hb with ⟨mb, hmb, hb⟩
        rcases hc with ⟨mc, hmc, hc⟩
        refine ⟨mb * (φ b) mc, M.mul_mem hmb (hM b mc hmc), ?_⟩
        calc
          φ (b * c) n = φ b (φ c n) := by
            change (b * c) • n = b • c • n
            rw [mul_smul]
          _ = φ b (n * mc) := by rw [hc]
          _ = φ b n * φ b mc := by simp
          _ = n * (mb * φ b mc) := by rw [hb]; group
      inv_mem' := by
        intro b hb
        rcases hb with ⟨m, hm, hb⟩
        refine ⟨((φ b⁻¹) m)⁻¹, M.inv_mem (hM b⁻¹ m hm), ?_⟩
        have hb' : n = φ b⁻¹ n * φ b⁻¹ m := by
          calc
            n = φ b⁻¹ (φ b n) := by simp [φ]
            _ = φ b⁻¹ (n * m) := by rw [hb]
            _ = φ b⁻¹ n * φ b⁻¹ m := by simp
        calc
          φ b⁻¹ n = (φ b⁻¹ n * φ b⁻¹ m) * (φ b⁻¹ m)⁻¹ := by group
          _ = n * (φ b⁻¹ m)⁻¹ := by rw [← hb'] }
  have haP : a ∈ P := by
    have hfix' : ((a • n : N) : N ⧸ M) = (n : N ⧸ M) := by
      simpa [invariantQuotientMulDistribMulAction, invariantQuotientMulAutHom,
        invariantQuotientMulAut] using hfix
    have hdiv : (a • n) / n ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hfix'
    have hMN : M.Normal := inferInstance
    have hm : n⁻¹ * (a • n) ∈ M := by
      rw [← hMN.mem_comm_iff]
      simpa [div_eq_mul_inv] using hdiv
    refine ⟨n⁻¹ * (a • n), hm, ?_⟩
    simp [φ]
  let C : Subgroup A := Subgroup.zpowers a
  let φC : C →* MulAut N := φ.comp C.subtype
  have hC_le_P : C ≤ P := Subgroup.zpowers_le.mpr haP
  have hM_inv_C : OddOrder.Isaacs.Ch03.IsAInvariant φC M := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro c m hm
    exact hM (c : A) m hm
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype N := Fintype.ofFinite N
  have hCopAN : Nat.Coprime (Nat.card A) (Nat.card N) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact (coprime_card h).symm
  have hCopCN : Nat.Coprime (Nat.card C) (Nat.card N) :=
    hCopAN.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  haveI : IsCyclic C := Subgroup.isCyclic_zpowers a
  letI : CommGroup C := IsCyclic.commGroup
  have hSolvC : IsSolvable C ∨ IsSolvable N := Or.inl inferInstance
  have hg_fix_C : ∀ c : C, ∃ m ∈ M, φC c n = n * m := by
    intro c
    simpa [φC] using hC_le_P c.2
  obtain ⟨x, hx_fixed, hx_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
      (A := C) (G := N) (φ := φC) hCopCN hSolvC hM_inv_C hg_fix_C
  have hx_ne : x ≠ 1 := by
    intro hx_one
    rcases hx_coset with ⟨m, hm, hx_eq⟩
    have hn_eq : n = m⁻¹ := by
      calc
        n = n * m * m⁻¹ := by group
        _ = x * m⁻¹ := by rw [hx_eq]
        _ = m⁻¹ := by rw [hx_one, one_mul]
    have hnM : n ∈ M := by
      rw [hn_eq]
      exact M.inv_mem hm
    exact hq_ne ((QuotientGroup.eq_one_iff n).mpr hnM)
  have hax : a • x = x := by
    have := hx_fixed ⟨a, Subgroup.mem_zpowers a⟩
    simpa [φC, φ] using this
  exact h a ha x hx_ne hax

/-! ### Theorem 6.3: even-order Frobenius complements

If `|A|` is even and `N` is nontrivial under a Frobenius action, then `A` contains a *unique*
involution and `N` is abelian.

The proof leverages mathlib's `MonoidHom.FixedPointFree` machinery (`Mathlib/GroupTheory/
FixedPointFree.lean`): for each `t ∈ A`, the map `n ↦ t • n` is an automorphism of `N`, and the
Frobenius condition (with `t ≠ 1`) is exactly fixed-point-freeness. When `t² = 1` (involution),
the map is involutive, so by `commute_all_of_involutive` `N` is commutative, and the unique
involution follows from the fact that any involution inverts every element. -/

/-- The action of `t ∈ A` on `N` (as `MulDistribMulAction.toMulAut`) is fixed-point-free whenever
`t ≠ 1` and the action of `A` on `N` is Frobenius. -/
theorem fixedPointFree_toMulAut (h : IsFrobeniusAction A N) {t : A} (ht : t ≠ 1) :
    MonoidHom.FixedPointFree (MulDistribMulAction.toMulAut A N t) := by
  intro n hn
  by_contra hne
  exact h t ht n hne (by simpa using hn)

/-- If `t ∈ A` satisfies `t² = 1`, then its action on `N` is involutive (as a function). -/
theorem involutive_toMulAut_of_sq_eq_one {t : A} (ht_sq : t ^ 2 = 1) :
    Function.Involutive ((MulDistribMulAction.toMulAut A N t : MulAut N) : N → N) := by
  intro n
  change t • (t • n) = n
  rw [← mul_smul, ← sq, ht_sq, one_smul]

/-- **Key lemma for Thm 6.3**: an involution `t ∈ A` (`t ≠ 1`, `t² = 1`) inverts every element
of `N` under a Frobenius action. -/
theorem involution_smul_eq_inv [Finite N] (h : IsFrobeniusAction A N)
    {t : A} (ht_ne : t ≠ 1) (ht_sq : t ^ 2 = 1) (n : N) : t • n = n⁻¹ := by
  have hfree := fixedPointFree_toMulAut h ht_ne
  have hinv := involutive_toMulAut_of_sq_eq_one (A := A) (N := N) ht_sq
  have h_eq := hfree.coe_eq_inv_of_involutive hinv
  -- h_eq : ⇑(MulDistribMulAction.toMulAut A N t) = (·⁻¹)
  have := congrFun h_eq n
  simpa using this

/-- **Isaacs Theorem 6.3** (commutativity part): `|A|` even + Frobenius action on nontrivial `N`
⇒ every pair in `N` commutes. -/
theorem commute_of_card_even [Finite A] [Finite N] (h : IsFrobeniusAction A N)
    (h_even : 2 ∣ Nat.card A) (x y : N) : Commute x y := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht_ord⟩ :=
    exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at h_even)
  have ht_ne : t ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at ht_ord; norm_num at ht_ord
  have ht_sq : t ^ 2 = 1 := by rw [← ht_ord, pow_orderOf_eq_one]
  exact (fixedPointFree_toMulAut h ht_ne).commute_all_of_involutive
    (involutive_toMulAut_of_sq_eq_one ht_sq) x y

/-- **Isaacs Theorem 6.3** (uniqueness of involution): `|A|` even + Frobenius action on nontrivial
`N` ⇒ `A` has exactly one element of order 2. -/
theorem unique_involution [Finite A] [Finite N] (h : IsFrobeniusAction A N)
    (h_even : 2 ∣ Nat.card A) (hN : Nontrivial N) :
    ∃! t : A, t ≠ 1 ∧ t ^ 2 = 1 := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht_ord⟩ :=
    exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at h_even)
  have ht_ne : t ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at ht_ord; norm_num at ht_ord
  have ht_sq : t ^ 2 = 1 := by rw [← ht_ord, pow_orderOf_eq_one]
  refine ⟨t, ⟨ht_ne, ht_sq⟩, ?_⟩
  rintro s ⟨hs_ne, hs_sq⟩
  -- Both `s` and `t` invert every element of `N`. Hence `s * t⁻¹` fixes a nontrivial `n`.
  obtain ⟨n, hn_ne⟩ := exists_ne (1 : N)
  have hs_inv : s • n = n⁻¹ := involution_smul_eq_inv h hs_ne hs_sq n
  have ht_inv : t • n = n⁻¹ := involution_smul_eq_inv h ht_ne ht_sq n
  -- `t⁻¹ = t` since `t² = 1`.
  have ht_inv_eq : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ht_sq]
  -- `(s * t⁻¹) • n = s • (t • n) = s • n⁻¹ = (s • n)⁻¹ = n`.
  have h_st_n : (s * t⁻¹) • n = n := by
    rw [mul_smul, ht_inv_eq, ht_inv, smul_inv', hs_inv, inv_inv]
  -- By Frobenius, `s * t⁻¹ = 1`, i.e., `s = t`.
  by_contra h_neq
  have h_st_ne : s * t⁻¹ ≠ 1 := by
    intro h_eq
    exact h_neq (mul_inv_eq_one.mp h_eq)
  exact h _ h_st_ne n hn_ne h_st_n

end IsFrobeniusAction

end

section /- 6A (continued): Lemma 6.5 — TI subgroup counting (pp. 178-179) -/

/-! ### Isaacs Lemma 6.5 (TI subgroup counting)

If `A ≤ G` satisfies `A ∩ A^g = 1` for all `g ∈ G - A` (the **TI**, "trivial intersection",
condition), then the set `X = { x ∈ G | x is not conjugate to any nonidentity element of A }`
has cardinality `|G : A|`.

The proof (Isaacs p. 179) goes via:

1. (Case `A = ⊥`) trivially `X = G` and `A.index = |G|`.
2. (Case `A > ⊥`) Show `N_G(A) = A` from TI: if `gAg⁻¹ = A` and `g ∉ A`, then
   `A = A ∩ gAg⁻¹ = ⊥`, contradiction.
3. The orbit of `A` under `ConjAct G` (the set of conjugates) has size `[G : N_G(A)] = A.index`.
4. Distinct conjugates of `A` have trivial intersection (by TI applied to a representative).
5. The carriers of the conjugates partition `Xᶜ ⊔ {1}`, so
   `|Xᶜ| = A.index · (|A| − 1)`, hence `|X| = |G| − A.index(|A|−1) = A.index`.

We work with `Set.ncard` (the natural-number cardinality of a `Set`) since the conclusion is
phrased as the size of a `Set G`. -/

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Auxiliary: the set of elements of `G` **not conjugate to any nonidentity element of `A`**. -/
private def notConjugateSet (A : Subgroup G) : Set G :=
  { x : G | ∀ a ∈ A, a ≠ 1 → ¬ IsConj a x }

/-- Helper for Lem 6.5: under the TI condition, the normalizer of `A` is `A` itself
(provided `A ≠ ⊥`). -/
private lemma normalizer_eq_self_of_TI
    {A : Subgroup G} (hA_ne : A ≠ ⊥)
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    Subgroup.normalizer A = A := by
  refine le_antisymm ?_ A.le_normalizer
  intro g hg
  by_contra hgA
  -- `g ∈ N_G(A)` means conjugation by `g` preserves `A`, so `MulAut.conj g • A = A`.
  have hconj : MulAut.conj g • A = A := by
    have hgN : g ∈ Subgroup.normalizer A := hg
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm x ∈ A ↔ x ∈ A
    rw [MulAut.conj_symm_apply]
    -- Goal: `g⁻¹ * x * g ∈ A ↔ x ∈ A`, which is `mem_normalizer_iff''`.
    exact ((Subgroup.mem_normalizer_iff''.mp hgN) x).symm
  -- Then `A ⊓ MulAut.conj g • A = A`, but TI gives `⊥`, so `A = ⊥`, contradicting `hA_ne`.
  have h_eq : A ⊓ (MulAut.conj g • A) = A := by rw [hconj]; exact inf_idem A
  have h_bot : A ⊓ (MulAut.conj g • A) = ⊥ := h_TI g hgA
  exact hA_ne (h_eq.symm.trans h_bot)

/-- Helper for Lem 6.5: the carrier set `(B : Set G)` of any conjugate `B = MulAut.conj h • A`
satisfies the same TI hypothesis with respect to elements outside `B`. (This is just a relabelling
of the TI assumption.) Used to show distinct conjugates are disjoint outside `{1}`. -/
private lemma TI_conjugate
    {A : Subgroup G}
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥)
    (h k : G) (hhk : (MulAut.conj h • A : Subgroup G) ≠ MulAut.conj k • A) :
    (MulAut.conj h • A : Subgroup G) ⊓ (MulAut.conj k • A) = ⊥ := by
  -- Let `g := h⁻¹ * k`.  If `g ∈ A`, then `MulAut.conj h • A = MulAut.conj k • A`, contradiction.
  set g : G := h⁻¹ * k with hg_def
  have hg_notmem : g ∉ A := by
    intro hgA
    apply hhk
    -- `k = h * g`, so `MulAut.conj k • A = MulAut.conj h • (MulAut.conj g • A)`.
    have hk_eq : k = h * g := by simp [hg_def]
    have hconjg : MulAut.conj g • A = A :=
      Subgroup.conj_smul_eq_self_of_mem hgA
    calc (MulAut.conj h • A : Subgroup G)
        = MulAut.conj h • (MulAut.conj g • A) := by rw [hconjg]
      _ = MulAut.conj (h * g) • A := by rw [← mul_smul, ← map_mul]
      _ = MulAut.conj k • A := by rw [← hk_eq]
  -- Now apply TI for `g` and conjugate by `h`.
  have h_TI_g : A ⊓ (MulAut.conj g • A) = ⊥ := h_TI g hg_notmem
  -- Conjugating by `h`: `MulAut.conj h` is a `MulEquiv`, so it preserves `⊓` and `⊥`.
  have hsmul : MulAut.conj h • (A ⊓ (MulAut.conj g • A) : Subgroup G)
      = (MulAut.conj h • A) ⊓ (MulAut.conj h • (MulAut.conj g • A)) :=
    Subgroup.smul_inf _ _ _
  have hsmul_bot : MulAut.conj h • (⊥ : Subgroup G) = (⊥ : Subgroup G) := Subgroup.smul_bot _
  -- `MulAut.conj h • (MulAut.conj g • A) = MulAut.conj k • A` (since `h * g = k`).
  have hk_smul : MulAut.conj h • (MulAut.conj g • A) = MulAut.conj k • A := by
    rw [← mul_smul]
    congr 1
    rw [← map_mul]
    congr 1
    simp [hg_def]
  rw [h_TI_g, hsmul_bot] at hsmul
  rw [← hk_smul]
  exact hsmul.symm

/-- Under the TI condition, the number of conjugates of `A` is `[G : A]`.

This is the conjugate-counting part of Isaacs Lemma 6.5, extracted because the same count is
also the cardinality calculation for the Frobenius-group partition in §6B. -/
private theorem ncard_conjugates_eq_index_of_TI [Finite G]
    {A : Subgroup G} (hA_ne : A ≠ ⊥)
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    (Set.range (fun g : G => MulAut.conj g • A)).ncard = A.index := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hNGA : Subgroup.normalizer A = A := normalizer_eq_self_of_TI hA_ne h_TI
  set conjs : Set (Subgroup G) := Set.range (fun g : G => MulAut.conj g • A) with hconjs_def
  -- Define `f : G → conjs` by `g ↦ ⟨MulAut.conj g • A, ⟨g, rfl⟩⟩`.
  -- `f g₁ = f g₂ ↔ g₂⁻¹ * g₁ ∈ N_G(A) = A ↔ g₁, g₂ in the same left coset of `A`.
  let f : G → conjs := fun g => ⟨MulAut.conj g • A, ⟨g, rfl⟩⟩
  have hf_lift : ∀ g₁ g₂ : G, (QuotientGroup.leftRel A) g₁ g₂ → f g₁ = f g₂ := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    have h_in_N : g₁⁻¹ * g₂ ∈ Subgroup.normalizer A := by rw [hNGA]; exact hrel
    have h_conj : MulAut.conj (g₁⁻¹ * g₂) • A = A :=
      Subgroup.conj_smul_eq_self_of_mem (by rw [hNGA] at h_in_N; exact h_in_N)
    ext1
    simp only [f]
    have heq : MulAut.conj g₂ = MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂) := by
      rw [← map_mul]; congr 1; group
    calc (MulAut.conj g₁ • A : Subgroup G)
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • A) := by rw [h_conj]
      _ = (MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂)) • A := by rw [mul_smul]
      _ = MulAut.conj g₂ • A := by rw [← heq]
  let f' : G ⧸ A → conjs := Quotient.lift f (fun a b => hf_lift a b)
  have hf_surj : Function.Surjective f' := by
    rintro ⟨B, g, rfl⟩
    exact ⟨⟦g⟧, rfl⟩
  have hf_inj : Function.Injective f' := by
    rintro ⟨g₁⟩ ⟨g₂⟩ hfeq
    change f g₁ = f g₂ at hfeq
    have hsub : (MulAut.conj g₁ • A : Subgroup G) = MulAut.conj g₂ • A := by
      exact Subtype.ext_iff.mp hfeq
    have h_step : (MulAut.conj (g₂⁻¹ * g₁) • A : Subgroup G) = A := by
      have heq : MulAut.conj (g₂⁻¹ * g₁) = MulAut.conj g₂⁻¹ * MulAut.conj g₁ := by
        rw [← map_mul]
      rw [heq, mul_smul, hsub, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have h_mem : g₂⁻¹ * g₁ ∈ Subgroup.normalizer A := by
      rw [Subgroup.mem_normalizer_iff'']
      intro y
      have hmem : y ∈ MulAut.conj (g₂⁻¹ * g₁) • A ↔ y ∈ A := by rw [h_step]
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
      have hcalc : (MulAut.conj (g₂⁻¹ * g₁))⁻¹ • y = (g₂⁻¹ * g₁)⁻¹ * y * (g₂⁻¹ * g₁) := by
        change (MulAut.conj (g₂⁻¹ * g₁)).symm y = _
        rw [MulAut.conj_symm_apply]
      rw [hcalc] at hmem
      exact hmem.symm
    rw [hNGA] at h_mem
    apply Quotient.sound
    change (QuotientGroup.leftRel A) g₁ g₂
    rw [QuotientGroup.leftRel_apply]
    have : (g₂⁻¹ * g₁)⁻¹ ∈ A := A.inv_mem h_mem
    simpa [mul_inv_rev] using this
  have hbij : Function.Bijective f' := ⟨hf_inj, hf_surj⟩
  have h_card_eq : Nat.card conjs = Nat.card (G ⧸ A) :=
    (Nat.card_congr (Equiv.ofBijective f' hbij)).symm
  have h_card_conjs : conjs.ncard = A.index := by
    rw [← Nat.card_coe_set_eq, h_card_eq, ← Subgroup.index]
  simpa [hconjs_def] using h_card_conjs

/-- **Isaacs Lemma 6.5**: Let `A` be a subgroup of a finite group `G`, and suppose `A ∩ A^g = 1`
for all `g ∈ G \ A`. Then the set of elements of `G` not conjugate to any nonidentity element of `A`
has cardinality `|G : A|`. -/
theorem card_notConjugateSet_eq_index [Finite G]
    (A : Subgroup G)
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    (notConjugateSet A).ncard = A.index := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rcases eq_or_ne A ⊥ with rfl | hA_ne
  · -- Case `A = ⊥`: every element of `G` lies in `notConjugateSet ⊥`.
    have h_univ : notConjugateSet (⊥ : Subgroup G) = Set.univ := by
      ext x
      simp only [notConjugateSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro a ha h_ne
      rw [Subgroup.mem_bot] at ha
      exact absurd ha h_ne
    rw [h_univ, Set.ncard_univ, Subgroup.index_bot]
  · -- Case `A ≠ ⊥`.  Build the orbit of `A` under conjugation; counted to give `A.index`.
    -- The complement of `notConjugateSet A` is `⋃_{B ∈ orbit} (B.carrier \ {1})`.
    -- Pairwise disjoint outside `{1}`; sum gives `index · (|A| - 1)`.
    -- The set of conjugates of `A` (indexed as subgroups of `G`).
    set conjs : Set (Subgroup G) := Set.range (fun g : G => MulAut.conj g • A) with hconjs_def
    -- (Step a) Identify the complement.
    have h_compl :
        (notConjugateSet A)ᶜ = ⋃ B ∈ conjs, ((B : Set G) \ {1}) := by
      ext x
      constructor
      · -- `x ∈ Xᶜ`: exists `a ∈ A`, `a ≠ 1`, `IsConj a x`.
        intro hx
        rw [Set.mem_compl_iff, notConjugateSet, Set.mem_setOf_eq] at hx
        push Not at hx
        obtain ⟨a, haA, ha_ne, hIsConj⟩ := hx
        -- `IsConj a x` means `∃ c, c * a * c⁻¹ = x`.
        rcases (isConj_iff (a := a) (b := x)).1 hIsConj with ⟨c, hcax⟩
        rw [Set.mem_iUnion]
        refine ⟨MulAut.conj c • A, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨⟨c, rfl⟩, ?_, ?_⟩
        · -- `x = c * a * c⁻¹ ∈ MulAut.conj c • A`.
          rw [← hcax]
          have hca : c * a * c⁻¹ = MulAut.conj c a := by simp [MulAut.conj_apply]
          rw [hca, Subgroup.coe_pointwise_smul]
          exact Set.smul_mem_smul_set haA
        · -- `x ≠ 1` since `a ≠ 1` and `x = c a c⁻¹`.
          rw [Set.mem_singleton_iff]
          rw [← hcax]
          intro hcax_one
          apply ha_ne
          have heq : c⁻¹ * (c * a * c⁻¹) * c = a := by group
          rw [hcax_one] at heq
          group at heq
          exact heq.symm
      · -- `x ∈ ⋃...`: extract `c`, get `IsConj a x`.
        intro hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨B, hB⟩ := hx
        rw [Set.mem_iUnion] at hB
        obtain ⟨hBconj, hxB_diff⟩ := hB
        rw [hconjs_def, Set.mem_range] at hBconj
        obtain ⟨c, rfl⟩ := hBconj
        obtain ⟨hxB, hx_ne⟩ := hxB_diff
        rw [Set.mem_singleton_iff] at hx_ne
        rw [Subgroup.coe_pointwise_smul] at hxB
        rcases hxB with ⟨a, haA, hax⟩
        rw [Set.mem_compl_iff]
        intro h_all
        apply h_all a haA
        · -- `a ≠ 1` since `x ≠ 1` and `x = MulAut.conj c a`.
          intro ha_one
          apply hx_ne
          rw [← hax, ha_one]; simp
        · -- `IsConj a x` from `x = MulAut.conj c a = c * a * c⁻¹`.
          refine (isConj_iff (a := a) (b := x)).2 ⟨c, ?_⟩
          rw [← hax]; simp [MulAut.conj_apply]
    -- (Step b) `conjs` is finite (image of finite type).
    have h_conjs_fin : conjs.Finite := by
      rw [hconjs_def]; exact Set.finite_range _
    -- (Step c) Pairwise disjoint outside `{1}`.
    have h_disj : conjs.PairwiseDisjoint (fun B : Subgroup G => (B : Set G) \ {1}) := by
      intro B hB B' hB' hBB'
      simp only [hconjs_def, Set.mem_range] at hB hB'
      obtain ⟨h, rfl⟩ := hB
      obtain ⟨k, rfl⟩ := hB'
      have h_inter_bot : (MulAut.conj h • A : Subgroup G) ⊓ (MulAut.conj k • A) = ⊥ :=
        TI_conjugate h_TI h k hBB'
      -- Now derive Set-level disjointness of the `\ {1}` subsets.
      rw [Function.onFun, Set.disjoint_left]
      intro x hxB hxB'
      have hx_inter : x ∈ ((MulAut.conj h • A : Subgroup G) ⊓ (MulAut.conj k • A) :
          Subgroup G) := by
        rw [Subgroup.mem_inf]
        exact ⟨hxB.1, hxB'.1⟩
      rw [h_inter_bot, Subgroup.mem_bot] at hx_inter
      exact hxB.2 hx_inter
    -- (Step d) Cardinality of each diff is `Nat.card A - 1` (independent of conjugate).
    have h_card_each : ∀ B ∈ conjs, ((B : Set G) \ {1}).ncard = Nat.card A - 1 := by
      intro B hB
      simp only [hconjs_def, Set.mem_range] at hB
      obtain ⟨g, rfl⟩ := hB
      -- `MulAut.conj g • A` has the same cardinality as `A` (subgroup map is a MulEquiv).
      have h_card_B : ((MulAut.conj g • A : Subgroup G) : Set G).ncard = Nat.card A := by
        rw [← Nat.card_coe_set_eq]
        exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) A).toEquiv).symm
      -- Now `(B.carrier \ {1}).ncard = |B| - 1`.
      have h1_mem : (1 : G) ∈ ((MulAut.conj g • A : Subgroup G) : Set G) :=
        Subgroup.one_mem _
      rw [Set.ncard_diff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
          Set.ncard_singleton, h_card_B]
    -- (Step e) Cardinality of `conjs` is `A.index`.
    have h_card_conjs : conjs.ncard = A.index := by
      simpa [hconjs_def] using ncard_conjugates_eq_index_of_TI hA_ne h_TI
    -- (Step f) Apply `Set.Finite.ncard_biUnion` (disjoint union counting).
    have h_card_union :
        (⋃ B ∈ conjs, ((B : Set G) \ {1})).ncard = ∑ᶠ B ∈ conjs, ((B : Set G) \ {1}).ncard :=
      Set.Finite.ncard_biUnion h_conjs_fin (fun _ _ => Set.toFinite _) h_disj
    -- (Step g) The finsum is `conjs.ncard * (Nat.card A - 1)`.
    have h_finsum :
        ∑ᶠ B ∈ conjs, ((B : Set G) \ {1}).ncard = conjs.ncard * (Nat.card A - 1) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ h_conjs_fin]
      rw [Finset.sum_congr rfl (fun B hB => h_card_each B
            ((Set.Finite.mem_toFinset h_conjs_fin).mp hB))]
      rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [Set.ncard_eq_toFinset_card _ h_conjs_fin]
    -- (Step h) Combine: |Xᶜ| = |G| - |X| = A.index · (|A| - 1).  Solve for |X| = A.index.
    have hX_fin : (notConjugateSet A).Finite := Set.toFinite _
    have hXc_fin : (notConjugateSet A)ᶜ.Finite := Set.toFinite _
    have h_total : (notConjugateSet A).ncard + ((notConjugateSet A)ᶜ).ncard = Nat.card G :=
      Set.ncard_add_ncard_compl _ hX_fin hXc_fin
    rw [h_compl, h_card_union, h_finsum, h_card_conjs] at h_total
    -- |G| = A.index * |A| (Lagrange).
    have h_lagrange : A.index * Nat.card A = Nat.card G := by
      rw [mul_comm]; exact Subgroup.card_mul_index A
    -- |A| ≥ 1 since A is a subgroup.
    have hA_pos : 0 < Nat.card A := Nat.card_pos
    -- Rewrite `A.index * (|A| - 1) = A.index * |A| - A.index` so omega can finish.
    have h_expand : A.index * (Nat.card A - 1) = A.index * Nat.card A - A.index := by
      rw [Nat.mul_sub_one]
    rw [h_expand, h_lagrange] at h_total
    -- h_total : (notConjugateSet A).ncard + (Nat.card G - A.index) = Nat.card G
    -- and A.index ≤ Nat.card G (from h_lagrange and hA_pos), so:
    have hA_index_le : A.index ≤ Nat.card G := by
      have := h_lagrange
      nlinarith
    omega

end

section /- 6B structural helper: subgroup partitions and orbit products -/

/-! ### Subgroup partitions and orbit products

Isaacs Lemma 6.8 is the counting lemma for a finite group partitioned by proper nonidentity
subgroups. The final counting argument is still downstream, but the following definitions and
lemmas fix the exact Lean surface: a partition is represented by a finite set of subgroups, and
for an action on an abelian group the product `u_H = ∏ h ∈ H, h • u` is fixed by `H`.
-/

/-- A finite partition of a group by proper nonidentity subgroups, in the sense of Isaacs §6B.

The parts are a `Finset` because Lemma 6.8 uses the cardinality of the partition. -/
structure SubgroupPartition (G : Type*) [Group G] where
  /-- The finite set of subgroup parts. -/
  parts : Finset (Subgroup G)
  /-- Every part is nonidentity. -/
  nontrivial : ∀ X, X ∈ parts → X ≠ ⊥
  /-- Every part is proper. -/
  proper : ∀ X, X ∈ parts → X ≠ ⊤
  /-- The parts cover the whole group. -/
  cover : ∀ g : G, ∃ X, X ∈ parts ∧ g ∈ X
  /-- Distinct parts intersect trivially. -/
  inf_eq_bot_of_ne : ∀ {X Y}, X ∈ parts → Y ∈ parts → X ≠ Y → X ⊓ Y = ⊥

namespace SubgroupPartition

private theorem finite_subgroups_of_finite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

private noncomputable def subgroupsOfCard (G : Type*) [Group G] [Finite G] (n : ℕ) :
    Finset (Subgroup G) := by
  classical
  haveI : Finite (Subgroup G) := finite_subgroups_of_finite (G := G)
  haveI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  exact Finset.univ.filter fun H => Nat.card H = n

private theorem mem_subgroupsOfCard {G : Type*} [Group G] [Finite G] {n : ℕ}
    {H : Subgroup G} :
    H ∈ subgroupsOfCard G n ↔ Nat.card H = n := by
  classical
  unfold subgroupsOfCard
  haveI : Finite (Subgroup G) := finite_subgroups_of_finite (G := G)
  haveI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  simp

variable {G : Type*} [Group G] (partn : SubgroupPartition G)

/-- The set of parts is nonempty. -/
theorem parts_card_pos : 0 < partn.parts.card := by
  obtain ⟨X, hX, _⟩ := partn.cover (1 : G)
  exact Finset.card_pos.mpr ⟨X, hX⟩

/-- Every part contains a nonidentity element. -/
theorem exists_ne_one_mem {X : Subgroup G} (hX : X ∈ partn.parts) :
    ∃ x : G, x ∈ X ∧ x ≠ 1 := by
  by_contra h
  push Not at h
  apply partn.nontrivial X hX
  ext x
  constructor
  · intro hx
    rw [h x hx]
    exact Subgroup.one_mem ⊥
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact X.one_mem

/-- A nonidentity element cannot lie in two distinct parts. -/
theorem eq_of_mem_ne_one {X Y : Subgroup G}
    (hX : X ∈ partn.parts) (hY : Y ∈ partn.parts)
    {g : G} (hgX : g ∈ X) (hgY : g ∈ Y) (hg : g ≠ 1) :
    X = Y := by
  by_contra hXY
  have hInf : X ⊓ Y = ⊥ := partn.inf_eq_bot_of_ne hX hY hXY
  have hgInf : g ∈ X ⊓ Y := ⟨hgX, hgY⟩
  have hg_one : g = 1 := by
    simpa [hInf] using hgInf
  exact hg hg_one

/-- Every nonidentity element lies in a unique partition part. -/
theorem existsUnique_part_of_ne_one {g : G} (hg : g ≠ 1) :
    ∃! X : Subgroup G, X ∈ partn.parts ∧ g ∈ X := by
  obtain ⟨X, hX, hgX⟩ := partn.cover g
  refine ⟨X, ⟨hX, hgX⟩, ?_⟩
  intro Y hY
  exact partn.eq_of_mem_ne_one hY.1 hX hY.2 hgX hg

/-- The unique partition part containing a nonidentity element. -/
noncomputable def partOfNeOne (g : {g : G // g ≠ 1}) :
    {X : Subgroup G // X ∈ partn.parts} :=
  ⟨(partn.existsUnique_part_of_ne_one g.2).choose,
    (partn.existsUnique_part_of_ne_one g.2).choose_spec.1.1⟩

/-- The chosen part really contains the nonidentity element. -/
theorem mem_partOfNeOne (g : {g : G // g ≠ 1}) :
    (g : G) ∈ (partn.partOfNeOne g).1 :=
  (partn.existsUnique_part_of_ne_one g.2).choose_spec.1.2

/-- Any partition part containing `g ≠ 1` is the chosen part. -/
theorem partOfNeOne_eq_of_mem {g : {g : G // g ≠ 1}} {X : Subgroup G}
    (hX : X ∈ partn.parts) (hgX : (g : G) ∈ X) :
    partn.partOfNeOne g = ⟨X, hX⟩ := by
  apply Subtype.ext
  exact ((partn.existsUnique_part_of_ne_one g.2).choose_spec.2 X ⟨hX, hgX⟩).symm

/-- Forget the partition part from a partition-indexed nonidentity element. -/
def nonidentitySigmaTo
    (p : Σ X : {X : Subgroup G // X ∈ partn.parts}, {x : X.1 // x ≠ 1}) :
    {g : G // g ≠ 1} :=
  ⟨(p.2.1 : G), fun hg => p.2.2 (Subtype.ext hg)⟩

/-- Forgetting the partition part is injective because nonidentity elements occur in a unique
part. -/
theorem nonidentitySigmaTo_injective :
    Function.Injective partn.nonidentitySigmaTo := by
  intro p q hpq
  rcases p with ⟨X, x⟩
  rcases q with ⟨Y, y⟩
  have hxyA : ((x.1 : X.1) : G) = ((y.1 : Y.1) : G) :=
    congrArg Subtype.val hpq
  have hx_ne : ((x.1 : X.1) : G) ≠ 1 := fun hx => x.2 (Subtype.ext hx)
  have hY_mem_x : ((x.1 : X.1) : G) ∈ Y.1 := by
    simpa [hxyA] using y.1.2
  have hXY : X = Y := by
    apply Subtype.ext
    exact partn.eq_of_mem_ne_one X.2 Y.2 x.1.2 hY_mem_x hx_ne
  cases hXY
  have hxy : x = y := by
    apply Subtype.ext
    apply Subtype.ext
    exact hxyA
  cases hxy
  rfl

/-- Forgetting the partition part is surjective: choose the unique part containing `g`. -/
theorem nonidentitySigmaTo_surjective :
    Function.Surjective partn.nonidentitySigmaTo := by
  intro g
  refine ⟨⟨partn.partOfNeOne g,
    ⟨⟨g.1, partn.mem_partOfNeOne g⟩, ?_⟩⟩, ?_⟩
  · intro h
    exact g.2 (congrArg Subtype.val h)
  · ext
    rfl

/-- The number of nonidentity elements in a finite group, as a subtype. -/
private theorem card_ne_one_subtype {G : Type*} [Group G] [Finite G] :
    Nat.card {g : G // g ≠ 1} = Nat.card G - 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hfilter :
      (Finset.univ.filter fun g : G => g ≠ 1) = Finset.univ.erase 1 := by
    ext g
    simp
  calc
    Nat.card {g : G // g ≠ 1}
        = Fintype.card {g : G // g ≠ 1} := Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun g : G => g ≠ 1).card := Fintype.card_subtype _
    _ = Fintype.card G - 1 := by
      rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ (1 : G)), Finset.card_univ]
    _ = Nat.card G - 1 := by rw [Nat.card_eq_fintype_card]

/-- Counting nonidentity elements through a subgroup partition. If every part has size `c`,
then `|Π| * (c - 1) = |G| - 1`. -/
theorem parts_card_mul_sub_one_eq_card_sub_one [Finite G] {c : ℕ}
    (hcard : ∀ X, X ∈ partn.parts → Nat.card X = c) :
    partn.parts.card * (c - 1) = Nat.card G - 1 := by
  classical
  let domain :=
    Σ X : {X : Subgroup G // X ∈ partn.parts}, {x : X.1 // x ≠ 1}
  let codomain := {g : G // g ≠ 1}
  haveI : Fintype {X : Subgroup G // X ∈ partn.parts} := inferInstance
  have hdomain_sigma :
      Nat.card domain =
        ∑ X : {X : Subgroup G // X ∈ partn.parts}, Nat.card {x : X.1 // x ≠ 1} := by
    rw [Nat.card_sigma]
  have hdomain_const :
      Nat.card domain = partn.parts.card * (c - 1) := by
    calc
      Nat.card domain
          = ∑ X : {X : Subgroup G // X ∈ partn.parts},
              Nat.card {x : X.1 // x ≠ 1} := hdomain_sigma
      _ = ∑ _X : {X : Subgroup G // X ∈ partn.parts}, (c - 1) := by
        refine Finset.sum_congr rfl ?_
        intro X _hX
        rw [card_ne_one_subtype (G := X.1), hcard X.1 X.2]
      _ = Fintype.card {X : Subgroup G // X ∈ partn.parts} * (c - 1) := by
        simp
      _ = partn.parts.card * (c - 1) := by
        rw [Fintype.card_coe partn.parts]
  have hbij : Function.Bijective partn.nonidentitySigmaTo :=
    ⟨partn.nonidentitySigmaTo_injective, partn.nonidentitySigmaTo_surjective⟩
  have hdomain_codomain : Nat.card domain = Nat.card codomain :=
    Nat.card_congr (Equiv.ofBijective partn.nonidentitySigmaTo hbij)
  rw [hdomain_const, card_ne_one_subtype (G := G)] at hdomain_codomain
  exact hdomain_codomain

/-- The textbook partition of an elementary abelian group of order `p^2`: its parts are all
subgroups of order `p`. -/
noncomputable def elementaryAbelianPrimeSquare
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p G) (hCard : Nat.card G = p ^ 2) :
    SubgroupPartition G where
  parts := subgroupsOfCard G p
  nontrivial := by
    intro X hX hX_bot
    have hX_card : Nat.card X = p := mem_subgroupsOfCard.mp hX
    have hp_eq_one : p = 1 := by
      rw [← hX_card, hX_bot, Subgroup.card_bot]
    exact hp.ne_one hp_eq_one
  proper := by
    intro X hX hX_top
    have hX_card : Nat.card X = p := mem_subgroupsOfCard.mp hX
    have hp_eq_sq : p = p ^ 2 := by
      calc p = Nat.card X := hX_card.symm
        _ = Nat.card G := by rw [hX_top, Subgroup.card_top]
        _ = p ^ 2 := hCard
    have hp_lt_sq : p < p ^ 2 := by
      nth_rewrite 1 [← pow_one p]
      exact pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 2)
    exact (ne_of_lt hp_lt_sq) hp_eq_sq
  cover := by
    haveI : Fact p.Prime := ⟨hp⟩
    intro g
    by_cases hg : g = 1
    · have hCard_gt_one : 1 < Nat.card G := by
        rw [hCard]
        exact one_lt_pow₀ hp.one_lt two_ne_zero
      haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hCard_gt_one
      obtain ⟨x, hx_ne⟩ := exists_ne (1 : G)
      let X : Subgroup G := Subgroup.zpowers x
      have hX_card : Nat.card X = p := by
        rw [show X = Subgroup.zpowers x from rfl, Nat.card_zpowers,
          orderOf_eq_prime (hElem.pow_eq_one x) hx_ne]
      refine ⟨X, mem_subgroupsOfCard.mpr hX_card, ?_⟩
      rw [hg]
      exact X.one_mem
    · let X : Subgroup G := Subgroup.zpowers g
      have hX_card : Nat.card X = p := by
        rw [show X = Subgroup.zpowers g from rfl, Nat.card_zpowers,
          orderOf_eq_prime (hElem.pow_eq_one g) hg]
      exact ⟨X, mem_subgroupsOfCard.mpr hX_card, Subgroup.mem_zpowers g⟩
  inf_eq_bot_of_ne := by
    intro X Y hX hY hXY
    have hX_card : Nat.card X = p := mem_subgroupsOfCard.mp hX
    have hY_card : Nat.card Y = p := mem_subgroupsOfCard.mp hY
    by_contra hInf_ne
    have hInf_gt_one : 1 < Nat.card (X ⊓ Y : Subgroup G) := by
      have hpos : 0 < Nat.card (X ⊓ Y : Subgroup G) := Nat.card_pos
      have hne_one : Nat.card (X ⊓ Y : Subgroup G) ≠ 1 := by
        intro hcard
        exact hInf_ne (Subgroup.eq_bot_of_card_eq (X ⊓ Y : Subgroup G) hcard)
      omega
    have hInf_dvd_X : Nat.card (X ⊓ Y : Subgroup G) ∣ Nat.card X :=
      Subgroup.card_dvd_of_le inf_le_left
    have hInf_card : Nat.card (X ⊓ Y : Subgroup G) = p := by
      rw [hX_card] at hInf_dvd_X
      rcases (Nat.dvd_prime hp).mp hInf_dvd_X with h | h
      · exact False.elim ((not_lt_of_ge (le_of_eq h)) hInf_gt_one)
      · exact h
    have hInf_eq_X : X ⊓ Y = X := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hX_card, hInf_card]
    have hX_le_Y : X ≤ Y := by
      intro x hx
      have hxInf : x ∈ X ⊓ Y := by simpa [hInf_eq_X] using hx
      exact hxInf.2
    have hXY_eq : X = Y := by
      apply Subgroup.eq_of_le_of_card_ge hX_le_Y
      rw [hX_card, hY_card]
    exact hXY hXY_eq

/-- The elementary abelian `p^2` partition has the textbook cardinality `p + 1`. -/
theorem elementaryAbelianPrimeSquare_parts_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p G) (hCard : Nat.card G = p ^ 2) :
    (elementaryAbelianPrimeSquare hp hElem hCard).parts.card = p + 1 := by
  let partn := elementaryAbelianPrimeSquare hp hElem hCard
  have hcount :
      partn.parts.card * (p - 1) = Nat.card G - 1 :=
    parts_card_mul_sub_one_eq_card_sub_one (partn := partn)
      (fun X hX => mem_subgroupsOfCard.mp hX)
  have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using (Nat.sq_sub_sq p 1)
  have hmul : partn.parts.card * (p - 1) = (p + 1) * (p - 1) := by
    rw [hcount, hCard, hfactor]
  exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) hmul

end SubgroupPartition

/-- Fixed points of the subgroup `H` under an action encoded by `φ : A →* MulAut U`. -/
def actionFixedPoints {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) (H : Subgroup A) : Subgroup U :=
  Subgroup.fixedPointsOfMulAut (φ.comp H.subtype)

@[simp]
theorem mem_actionFixedPoints {A U : Type*} [Group A] [Group U]
    {φ : A →* MulAut U} {H : Subgroup A} {u : U} :
    u ∈ actionFixedPoints φ H ↔ ∀ h : H, (φ h) u = u :=
  Iff.rfl

/-- Fixed points of a single acting element, i.e. the action-centralizer `C_U(a)`. -/
def actionFixedBy {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) (a : A) : Subgroup U where
  carrier := {u | (φ a) u = u}
  one_mem' := map_one (φ a)
  mul_mem' := by
    intro u v hu hv
    change (φ a) (u * v) = u * v
    rw [map_mul, hu, hv]
  inv_mem' := by
    intro u hu
    change (φ a) u⁻¹ = u⁻¹
    rw [map_inv, hu]

@[simp]
theorem mem_actionFixedBy {A U : Type*} [Group A] [Group U]
    {φ : A →* MulAut U} {a : A} {u : U} :
    u ∈ actionFixedBy φ a ↔ (φ a) u = u :=
  Iff.rfl

/-- The centralizer of an element equals the fixed subgroup of its cyclic closure. -/
theorem actionFixedBy_eq_actionFixedPoints_zpowers
    {A U : Type*} [Group A] [Group U] (φ : A →* MulAut U) (a : A) :
    actionFixedBy φ a = actionFixedPoints φ (Subgroup.zpowers a) := by
  ext u
  constructor
  · intro hu h
    have hh : (h : A) ∈ Subgroup.closure ({a} : Set A) := by
      simpa [Subgroup.zpowers_eq_closure] using h.property
    refine Subgroup.closure_induction
      (p := fun b _ => (φ b) u = u) ?mem ?one ?mul ?inv hh
    · intro b hb
      rw [Set.mem_singleton_iff.mp hb]
      exact hu
    · simp
    · intro b c _ _ hb hc
      simp [map_mul, hc, hb]
    · intro b _ hb
      calc
        (φ b⁻¹) u = (φ b)⁻¹ u := by rw [map_inv]
        _ = (φ b)⁻¹ ((φ b) u) := by rw [hb]
        _ = u := by simp
  · intro hu
    exact hu ⟨a, Subgroup.mem_zpowers a⟩

/-- `K = ⟨ C_U(a) | 1 ≠ a ∈ A ⟩`, the subgroup generated by all nontrivial
single-element action-centralizers. This is the subgroup denoted `K` in Isaacs Thm 6.21. -/
def nontrivialActionFixedByClosure {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) : Subgroup U :=
  Subgroup.closure {u | ∃ a : A, a ≠ 1 ∧ u ∈ actionFixedBy φ a}

/-- Each nonidentity element's action-centralizer is contained in the generated subgroup `K`. -/
theorem actionFixedBy_le_nontrivialActionFixedByClosure
    {A U : Type*} [Group A] [Group U] {φ : A →* MulAut U} {a : A} (ha : a ≠ 1) :
    actionFixedBy φ a ≤ nontrivialActionFixedByClosure φ := by
  intro u hu
  exact Subgroup.subset_closure ⟨a, ha, hu⟩

/-- To show `K ≤ L`, it is enough and necessary to show `C_U(a) ≤ L` for every `a ≠ 1`. -/
theorem nontrivialActionFixedByClosure_le_iff
    {A U : Type*} [Group A] [Group U] {φ : A →* MulAut U} {L : Subgroup U} :
    nontrivialActionFixedByClosure φ ≤ L ↔
      ∀ a : A, a ≠ 1 → actionFixedBy φ a ≤ L := by
  constructor
  · intro h a ha
    exact (actionFixedBy_le_nontrivialActionFixedByClosure (φ := φ) ha).trans h
  · intro h
    rw [nontrivialActionFixedByClosure]
    exact (Subgroup.closure_le _).mpr (by
      rintro u ⟨a, ha, hu⟩
      exact h a ha hu)

/-- If an invariant subgroup satisfies the Isaacs 6.21 generated-centralizer conclusion
internally, then it lies in the ambient generated-centralizer subgroup. -/
theorem subgroup_le_nontrivialActionFixedByClosure_of_closure_eq_top
    {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    {M : Subgroup N} [MulDistribMulAction A M]
    (hcompat : ∀ a : A, ∀ m : M, ((a • m : M) : N) = a • (m : N))
    (hMtop : nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A M) = ⊤) :
    M ≤ nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) := by
  let φM : A →* MulAut M := MulDistribMulAction.toMulAut A M
  let φN : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let K : Subgroup N := nontrivialActionFixedByClosure φN
  intro n hn
  let m : M := ⟨n, hn⟩
  have hm : m ∈ nontrivialActionFixedByClosure φM := by
    rw [hMtop]
    exact Subgroup.mem_top m
  rw [nontrivialActionFixedByClosure] at hm
  have hmK : (m : N) ∈ K := by
    refine Subgroup.closure_induction
      (p := fun (x : M) _ => (x : N) ∈ K) ?mem ?one ?mul ?inv hm
    · rintro x ⟨a, ha, hx⟩
      have hxN : a • (x : N) = (x : N) := by
        have hx' := congrArg (fun y : M => (y : N)) hx
        simpa [φM, hcompat a x] using hx'
      exact Subgroup.subset_closure ⟨a, ha, by simpa [φN] using hxN⟩
    · simp [K]
    · intro x y _ _ hx hy
      exact K.mul_mem hx hy
    · intro x _ hx
      exact K.inv_mem hx
  change (m : N) ∈ K
  exact hmK

/-- If two acting elements commute, the second preserves the fixed subgroup of the first. -/
theorem actionFixedBy_invariant_of_commute
    {A U : Type*} [Group A] [Group U] {φ : A →* MulAut U}
    {a b : A} (hab : a * b = b * a) :
    ∀ u ∈ actionFixedBy φ a, (φ b) u ∈ actionFixedBy φ a := by
  intro u hu
  calc
    (φ a) ((φ b) u) = (φ (a * b)) u := by simp [map_mul]
    _ = (φ (b * a)) u := by rw [hab]
    _ = (φ b) ((φ a) u) := by simp [map_mul]
    _ = (φ b) u := by rw [hu]

/-- For abelian `A`, Isaacs's subgroup `K = ⟨C_U(a) | a ≠ 1⟩` is invariant under `A`. -/
theorem nontrivialActionFixedByClosure_invariant_of_commutative
    {A U : Type*} [Group A] [Group U] [IsMulCommutative A] (φ : A →* MulAut U) :
    ∀ b : A, ∀ u ∈ nontrivialActionFixedByClosure φ,
      (φ b) u ∈ nontrivialActionFixedByClosure φ := by
  intro b u hu
  rw [nontrivialActionFixedByClosure] at hu ⊢
  refine Subgroup.closure_induction
    (p := fun u _ => (φ b) u ∈
      Subgroup.closure {u | ∃ a : A, a ≠ 1 ∧ u ∈ actionFixedBy φ a})
    ?mem ?one ?mul ?inv hu
  · rintro u ⟨a, ha, hu⟩
    exact Subgroup.subset_closure
      ⟨a, ha, actionFixedBy_invariant_of_commute (φ := φ) (mul_comm a b) u hu⟩
  · simp
  · intro u v _ _ hu hv
    simpa [map_mul] using Subgroup.mul_mem _ hu hv
  · intro u _ hu
    simpa [map_inv] using Subgroup.inv_mem _ hu

/-- If every nonidentity fixed subgroup lies in an invariant normal subgroup `M`, then the
induced action on `N/M` is Frobenius.

This is the formal "fixed points come from fixed points" step in Isaacs Thm 6.21. -/
theorem quotient_isFrobeniusAction_of_fixedBy_le
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    {M : Subgroup N} [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M)
    (hCopAM : Nat.Coprime (Nat.card A) (Nat.card M))
    (hfixed : ∀ a : A, a ≠ 1 →
      actionFixedBy (MulDistribMulAction.toMulAut A N) a ≤ M) :
    @IsFrobeniusAction A (N ⧸ M) _ _
      (IsFrobeniusAction.invariantQuotientMulDistribMulAction M hM) := by
  classical
  letI : MulDistribMulAction A (N ⧸ M) :=
    IsFrobeniusAction.invariantQuotientMulDistribMulAction M hM
  intro a ha q hq_ne hfix
  revert hq_ne hfix
  refine QuotientGroup.induction_on q ?_
  intro n hq_ne hfix
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let P : Subgroup A :=
    { carrier := {b | ∃ m ∈ M, φ b n = n * m}
      one_mem' := by
        refine ⟨1, M.one_mem, ?_⟩
        simp [φ]
      mul_mem' := by
        intro b c hb hc
        rcases hb with ⟨mb, hmb, hb⟩
        rcases hc with ⟨mc, hmc, hc⟩
        refine ⟨mb * (φ b) mc, M.mul_mem hmb (hM b mc hmc), ?_⟩
        calc
          φ (b * c) n = φ b (φ c n) := by
            change (b * c) • n = b • c • n
            rw [mul_smul]
          _ = φ b (n * mc) := by rw [hc]
          _ = φ b n * φ b mc := by simp
          _ = n * (mb * φ b mc) := by rw [hb]; group
      inv_mem' := by
        intro b hb
        rcases hb with ⟨m, hm, hb⟩
        refine ⟨((φ b⁻¹) m)⁻¹, M.inv_mem (hM b⁻¹ m hm), ?_⟩
        have hb' : n = φ b⁻¹ n * φ b⁻¹ m := by
          calc
            n = φ b⁻¹ (φ b n) := by simp [φ]
            _ = φ b⁻¹ (n * m) := by rw [hb]
            _ = φ b⁻¹ n * φ b⁻¹ m := by simp
        calc
          φ b⁻¹ n = (φ b⁻¹ n * φ b⁻¹ m) * (φ b⁻¹ m)⁻¹ := by group
          _ = n * (φ b⁻¹ m)⁻¹ := by rw [← hb'] }
  have haP : a ∈ P := by
    have hfix' : ((a • n : N) : N ⧸ M) = (n : N ⧸ M) := by
      simpa [IsFrobeniusAction.invariantQuotientMulDistribMulAction,
        IsFrobeniusAction.invariantQuotientMulAutHom,
        IsFrobeniusAction.invariantQuotientMulAut] using hfix
    have hdiv : (a • n) / n ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hfix'
    have hMN : M.Normal := inferInstance
    have hm : n⁻¹ * (a • n) ∈ M := by
      rw [← hMN.mem_comm_iff]
      simpa [div_eq_mul_inv] using hdiv
    refine ⟨n⁻¹ * (a • n), hm, ?_⟩
    simp [φ]
  let C : Subgroup A := Subgroup.zpowers a
  let φC : C →* MulAut N := φ.comp C.subtype
  have hC_le_P : C ≤ P := Subgroup.zpowers_le.mpr haP
  have hM_inv_C : OddOrder.Isaacs.Ch03.IsAInvariant φC M := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro c m hm
    exact hM (c : A) m hm
  have hCopCM : Nat.Coprime (Nat.card C) (Nat.card M) :=
    hCopAM.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  haveI : IsCyclic C := Subgroup.isCyclic_zpowers a
  letI : CommGroup C := IsCyclic.commGroup
  have hSolvC : IsSolvable C ∨ IsSolvable M := Or.inl inferInstance
  have hg_fix_C : ∀ c : C, ∃ m ∈ M, φC c n = n * m := by
    intro c
    simpa [φC] using hC_le_P c.2
  obtain ⟨x, hx_fixed, hx_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      (A := C) (G := N) (φ := φC) hCopCM hSolvC hM_inv_C hg_fix_C
  have hxM : x ∈ M :=
    hfixed a ha (by
      have := hx_fixed ⟨a, Subgroup.mem_zpowers a⟩
      simpa [φC, φ] using this)
  rcases hx_coset with ⟨m, hm, hx_eq⟩
  have hnM : n ∈ M := by
    have hxm : x * m⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem hm)
    convert hxm using 1
    rw [hx_eq]
    group
  exact hq_ne ((QuotientGroup.eq_one_iff n).mpr hnM)

/-- A subgroup containing the commutator subgroup is normal.

This is the group-theoretic step used in Isaacs Thm 6.21 after proving `N' ≤ K`. -/
theorem normal_of_commutator_le {G : Type*} [Group G] {K : Subgroup G}
    (hcomm : _root_.commutator G ≤ K) : K.Normal := by
  rw [_root_.commutator_def] at hcomm
  exact (Subgroup.commutator_top_left_le_iff (H := K)).mp
    ((Subgroup.commutator_mono le_rfl (show K ≤ (⊤ : Subgroup G) from le_top)).trans hcomm)

/-- If `p` divides the index of `K`, no Sylow `p`-subgroup can lie inside `K`. -/
theorem sylow_not_le_of_prime_dvd_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {K : Subgroup G} (hpK : p ∣ K.index) :
    ¬ (P : Subgroup G) ≤ K := by
  intro hPK
  exact P.not_dvd_index (hpK.trans (Subgroup.index_dvd_of_le hPK))

/-- The Sylow step in Isaacs Thm 6.21.

If every proper `A`-invariant subgroup of `N` lies in `K`, and `p ∣ |N : K|`, then the
`A`-invariant Sylow `p`-subgroup supplied by Isaacs Thm 3.23(a) is all of `N`. -/
theorem exists_aInvariant_sylow_eq_top_of_prime_dvd_index_of_proper_invariant_le
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    {K : Subgroup N} {p : ℕ} [Fact p.Prime]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hSolv : IsSolvable A ∨ IsSolvable N)
    (hpK : p ∣ K.index)
    (hproper : ∀ P : Subgroup N,
      (∀ a : A, ∀ n ∈ P, a • n ∈ P) → P ≠ ⊤ → P ≤ K) :
    ∃ P : Sylow p N,
      OddOrder.Isaacs.Ch03.IsAInvariant (MulDistribMulAction.toMulAut A N) (P : Subgroup N) ∧
        (P : Subgroup N) = ⊤ := by
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  obtain ⟨P, hP_inv⟩ :=
    OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (G := N) (A := A) (φ := φ)
      hCop hSolv p
  refine ⟨P, hP_inv, ?_⟩
  by_contra hP_top
  have hP_smul : ∀ a : A, ∀ n ∈ (P : Subgroup N), a • n ∈ (P : Subgroup N) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem] at hP_inv
    intro a n hn
    simpa [φ] using hP_inv a n hn
  have hP_le_K : (P : Subgroup N) ≤ K :=
    hproper (P : Subgroup N) hP_smul hP_top
  exact sylow_not_le_of_prime_dvd_index P hpK hP_le_K

/-- The commutator subgroup is the proper invariant subgroup used in Isaacs Thm 6.21.

In the theorem's p-group case, `N` is solvable, so `N' < N`; invariance is functorial under
automorphisms. -/
theorem commutator_le_of_proper_invariant_le_of_isSolvable
    {A N : Type*} [Group A] [Group N] [Finite N] [Nontrivial N] [IsSolvable N]
    [MulDistribMulAction A N] {K : Subgroup N}
    (hproper : ∀ P : Subgroup N,
      (∀ a : A, ∀ n ∈ P, a • n ∈ P) → P ≠ ⊤ → P ≤ K) :
    _root_.commutator N ≤ K := by
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  have hcomm_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (_root_.commutator N) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.commutator_self φ
  have hcomm_smul :
      ∀ a : A, ∀ n ∈ _root_.commutator N, a • n ∈ _root_.commutator N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem] at hcomm_inv
    intro a n hn
    simpa [φ] using hcomm_inv a n hn
  exact hproper (_root_.commutator N) hcomm_smul
    (IsSolvable.commutator_lt_top_of_nontrivial N).ne

/-- Isaacs's product `u_H = ∏_{h ∈ H} u^h`, written for an action by automorphisms. -/
noncomputable def orbitProduct {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) : U :=
  ∏ h : H, (φ h) u

/-- The orbit product over the nonidentity elements of a subgroup. -/
noncomputable def subgroupNonidentityOrbitProduct
    {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) : U :=
  by
    classical
    exact ∏ h : {h : H // h ≠ 1}, (φ (h.1 : A)) u

/-- The orbit product over the nonidentity elements of the whole group. -/
noncomputable def nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (u : U) : U :=
  by
    classical
    letI : Fintype A := Fintype.ofFinite A
    exact ∏ a : {a : A // a ≠ 1}, (φ a.1) u

/-- The orbit product `u_H` is fixed by every element of `H`. -/
theorem orbitProduct_mem_actionFixedPoints {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) :
    orbitProduct φ H u ∈ actionFixedPoints φ H := by
  intro x
  calc
    (φ (x : A)) (orbitProduct φ H u)
        = ∏ h : H, (φ (x : A)) ((φ h) u) := by
            simp [orbitProduct]
    _ = ∏ h : H, (φ ((x * h : H) : A)) u := by
          refine Finset.prod_congr rfl ?_
          intro h _hh
          simp [map_mul]
    _ = ∏ h : H, (φ (h : A)) u := by
          exact Fintype.prod_equiv (Equiv.mulLeft x)
            (fun h : H => (φ ((x * h : H) : A)) u)
            (fun h : H => (φ (h : A)) u)
            (fun h => rfl)

/-- Split an orbit product into the identity contribution and the nonidentity contributions. -/
theorem orbitProduct_eq_mul_subgroupNonidentityOrbitProduct
    {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) :
    orbitProduct φ H u = u * subgroupNonidentityOrbitProduct φ H u := by
  classical
  rw [orbitProduct, subgroupNonidentityOrbitProduct]
  simpa using Fintype.prod_eq_mul_prod_subtype_ne
    (fun h : H => (φ (h : A)) u) (1 : H)

/-- Fixed points are antitone in the acting subgroup. -/
theorem actionFixedPoints_antitone {A U : Type*} [Group A] [Group U]
    {φ : A →* MulAut U} {H K : Subgroup A} (hHK : H ≤ K) :
    actionFixedPoints φ K ≤ actionFixedPoints φ H := by
  intro u hu h
  exact hu ⟨h, hHK h.property⟩

/-- If the fixed points of `H` are trivial, then Isaacs's orbit product over `H` is `1`. -/
theorem orbitProduct_eq_one_of_actionFixedPoints_eq_bot
    {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U)
    (hH : actionFixedPoints φ H = ⊥) :
    orbitProduct φ H u = 1 := by
  have hmem := orbitProduct_mem_actionFixedPoints φ H u
  have : orbitProduct φ H u ∈ (⊥ : Subgroup U) := by
    simpa [hH] using hmem
  simpa using this

/-- The product over all partition parts of the orbit products. -/
noncomputable def partitionOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) : U :=
  ∏ x ∈ partn.parts,
    (letI : Fintype x := Fintype.ofFinite x
     orbitProduct φ x u)

/-- The product over all partition parts and all nonidentity elements in those parts. -/
noncomputable def partitionNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) : U :=
  ∏ X ∈ partn.parts,
    (letI : Fintype X := Fintype.ofFinite X
     subgroupNonidentityOrbitProduct φ X u)

/-- The same nonidentity product, indexed by the sigma type of partition parts and
nonidentity elements in each part. The finite instances are supplied internally so callers do
not need to expose dependent `Fintype` arguments. -/
noncomputable def partitionSigmaNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) : U := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype {X : Subgroup A // X ∈ partn.parts} := Fintype.ofFinite _
  letI : ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype X.1 :=
    fun X => Fintype.ofFinite X.1
  letI :
      ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype {x : X.1 // x ≠ 1} :=
    fun X => Subtype.fintype (fun x : X.1 => x ≠ 1)
  exact ∏ p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}),
    (φ ((p.2.1 : p.1.1) : A)) u

/-- The partition nonidentity product is the sigma-indexed nonidentity product. -/
theorem partitionNonidentityOrbitProduct_eq_partitionSigmaNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionNonidentityOrbitProduct φ partn u =
      partitionSigmaNonidentityOrbitProduct φ partn u := by
  classical
  rw [partitionNonidentityOrbitProduct, partitionSigmaNonidentityOrbitProduct]
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype {X : Subgroup A // X ∈ partn.parts} := Fintype.ofFinite _
  letI : ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype X.1 :=
    fun X => Fintype.ofFinite X.1
  letI :
      ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype {x : X.1 // x ≠ 1} :=
    fun X => Subtype.fintype (fun x : X.1 => x ≠ 1)
  rw [Finset.prod_subtype partn.parts (fun X => Iff.rfl)
    (fun X : Subgroup A =>
      (letI : Fintype X := Fintype.ofFinite X
       subgroupNonidentityOrbitProduct φ X u))]
  change (∏ X : {X : Subgroup A // X ∈ partn.parts},
      (letI : Fintype X.1 := Fintype.ofFinite X.1
       subgroupNonidentityOrbitProduct φ X.1 u)) =
    ∏ p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}),
      (φ ((p.2.1 : p.1.1) : A)) u
  simpa [subgroupNonidentityOrbitProduct] using
    (Fintype.prod_sigma
      (fun p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}) =>
        (φ ((p.2.1 : p.1.1) : A)) u)).symm

/-- The sigma-indexed nonidentity product over a partition is the ordinary nonidentity product:
nonidentity elements occur in exactly one partition part. -/
theorem partitionSigmaNonidentityOrbitProduct_eq_nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionSigmaNonidentityOrbitProduct φ partn u =
      nonidentityOrbitProduct φ u := by
  classical
  rw [partitionSigmaNonidentityOrbitProduct, nonidentityOrbitProduct]
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype {X : Subgroup A // X ∈ partn.parts} := Fintype.ofFinite _
  letI : ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype X.1 :=
    fun X => Fintype.ofFinite X.1
  letI :
      ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype {x : X.1 // x ≠ 1} :=
    fun X => Subtype.fintype (fun x : X.1 => x ≠ 1)
  exact Fintype.prod_bijective partn.nonidentitySigmaTo
    ⟨partn.nonidentitySigmaTo_injective, partn.nonidentitySigmaTo_surjective⟩
    (fun p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}) =>
      (φ ((p.2.1 : p.1.1) : A)) u)
    (fun a : {a : A // a ≠ 1} => (φ a.1) u)
    (fun _ => rfl)

/-- The nonidentity factors over a subgroup partition multiply to the nonidentity factors over
the whole group. -/
theorem partitionNonidentityOrbitProduct_eq_nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionNonidentityOrbitProduct φ partn u =
      nonidentityOrbitProduct φ u := by
  rw [partitionNonidentityOrbitProduct_eq_partitionSigmaNonidentityOrbitProduct φ partn u,
    partitionSigmaNonidentityOrbitProduct_eq_nonidentityOrbitProduct φ partn u]

/-- The orbit product over the top subgroup, with the finite instance supplied from `A`. -/
noncomputable def topOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (u : U) : U :=
  letI : Fintype (⊤ : Subgroup A) := Fintype.ofFinite (⊤ : Subgroup A)
  orbitProduct φ (⊤ : Subgroup A) u

/-- Split the top orbit product into the identity contribution and nonidentity contributions. -/
theorem topOrbitProduct_eq_mul_nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (u : U) :
    topOrbitProduct φ u = u * nonidentityOrbitProduct φ u := by
  classical
  rw [topOrbitProduct, orbitProduct, nonidentityOrbitProduct]
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (⊤ : Subgroup A) := Fintype.ofFinite (⊤ : Subgroup A)
  calc
    (∏ h : (⊤ : Subgroup A), (φ (h : A)) u)
        = ∏ a : A, (φ a) u := by
            exact Fintype.prod_equiv Subgroup.topEquiv.toEquiv
              (fun h : (⊤ : Subgroup A) => (φ (h : A)) u)
              (fun a : A => (φ a) u)
              (fun _ => rfl)
    _ = u * ∏ a : {a : A // a ≠ 1}, (φ a.1) u := by
          simpa using Fintype.prod_eq_mul_prod_subtype_ne
            (fun a : A => (φ a) u) (1 : A)

/-- Split the partition product into the identity contributions and the nonidentity
contributions. -/
theorem partitionOrbitProduct_eq_pow_mul_partitionNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionOrbitProduct φ partn u =
      u ^ partn.parts.card * partitionNonidentityOrbitProduct φ partn u := by
  classical
  rw [partitionOrbitProduct, partitionNonidentityOrbitProduct]
  calc
    (∏ X ∈ partn.parts,
      (letI : Fintype X := Fintype.ofFinite X
       orbitProduct φ X u))
        = ∏ X ∈ partn.parts,
            (u *
              (letI : Fintype X := Fintype.ofFinite X
               subgroupNonidentityOrbitProduct φ X u)) := by
            refine Finset.prod_congr rfl ?_
            intro X hX
            letI : Fintype X := Fintype.ofFinite X
            exact orbitProduct_eq_mul_subgroupNonidentityOrbitProduct φ X u
    _ = (∏ X ∈ partn.parts, u) *
          ∏ X ∈ partn.parts,
            (letI : Fintype X := Fintype.ofFinite X
             subgroupNonidentityOrbitProduct φ X u) := by
            simp_rw [Finset.prod_mul_distrib]
    _ = u ^ partn.parts.card *
          ∏ X ∈ partn.parts,
            (letI : Fintype X := Fintype.ofFinite X
             subgroupNonidentityOrbitProduct φ X u) := by
            simp

/-- Isaacs 6.8 counting identity for orbit products over a subgroup partition. -/
theorem partitionOrbitProduct_identity
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionOrbitProduct φ partn u =
      topOrbitProduct φ u * u ^ (partn.parts.card - 1) := by
  classical
  have hcard : partn.parts.card = partn.parts.card.pred.succ :=
    (Nat.succ_pred_eq_of_pos partn.parts_card_pos).symm
  have hpow : u ^ partn.parts.card = u * u ^ (partn.parts.card - 1) := by
    calc
      u ^ partn.parts.card
          = u ^ partn.parts.card.pred.succ := by
              exact congrArg (fun n => u ^ n) hcard
      _ = u ^ partn.parts.card.pred * u := by
            rw [pow_succ]
      _ = u ^ (partn.parts.card - 1) * u := by
            rw [Nat.pred_eq_sub_one]
      _ = u * u ^ (partn.parts.card - 1) := by
            rw [mul_comm]
  calc
    partitionOrbitProduct φ partn u
        = u ^ partn.parts.card * partitionNonidentityOrbitProduct φ partn u := by
            exact partitionOrbitProduct_eq_pow_mul_partitionNonidentityOrbitProduct φ partn u
    _ = u ^ partn.parts.card * nonidentityOrbitProduct φ u := by
          rw [partitionNonidentityOrbitProduct_eq_nonidentityOrbitProduct φ partn u]
    _ = (u * u ^ (partn.parts.card - 1)) * nonidentityOrbitProduct φ u := by
          rw [hpow]
    _ = (u * nonidentityOrbitProduct φ u) * u ^ (partn.parts.card - 1) := by
          ac_rfl
    _ = topOrbitProduct φ u * u ^ (partn.parts.card - 1) := by
          rw [← topOrbitProduct_eq_mul_nonidentityOrbitProduct φ u]

/-- If every partition part has trivial fixed points, then every part orbit product is `1`. -/
theorem partitionOrbitProduct_eq_one_of_parts_fixedPoints_eq_bot
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U)
    (hfix : ∀ X, X ∈ partn.parts → actionFixedPoints φ X = ⊥) :
    partitionOrbitProduct φ partn u = 1 := by
  classical
  rw [partitionOrbitProduct, Finset.prod_eq_one]
  intro X hX
  letI : Fintype X := Fintype.ofFinite X
  exact orbitProduct_eq_one_of_actionFixedPoints_eq_bot φ X u (hfix X hX)

/-- If every partition part has trivial fixed points, then the full fixed-point subgroup is
trivial. -/
theorem actionFixedPoints_top_eq_bot_of_parts_fixedPoints_eq_bot
    {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A)
    (hfix : ∀ X, X ∈ partn.parts → actionFixedPoints φ X = ⊥) :
    actionFixedPoints φ (⊤ : Subgroup A) = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  obtain ⟨X, hX, _h1X⟩ := partn.cover (1 : A)
  have huX : u ∈ actionFixedPoints φ X :=
    actionFixedPoints_antitone (show X ≤ (⊤ : Subgroup A) from le_top) hu
  simpa [hfix X hX] using huX

/-- Once the Isaacs 6.8 counting identity is known, some part has nontrivial fixed points.

This packages the non-counting half of Lemma 6.8: assuming the product identity
`∏_{X∈Π} u_X = u_A * u^(|Π|-1)`, any `u` with `u^(|Π|-1) ≠ 1` forces a partition
part whose action on `U` has nontrivial fixed points. -/
theorem exists_part_actionFixedPoints_ne_bot_of_orbitProduct_identity
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A)
    (hidentity : ∀ u : U,
      partitionOrbitProduct φ partn u =
        topOrbitProduct φ u * u ^ (partn.parts.card - 1))
    {u : U} (hu : u ^ (partn.parts.card - 1) ≠ 1) :
    ∃ X, X ∈ partn.parts ∧ actionFixedPoints φ X ≠ ⊥ := by
  by_contra hnone
  have hfix : ∀ X, X ∈ partn.parts → actionFixedPoints φ X = ⊥ := by
    intro X hX
    by_contra hne
    exact hnone ⟨X, hX, hne⟩
  have hprod :
      partitionOrbitProduct φ partn u = 1 :=
    partitionOrbitProduct_eq_one_of_parts_fixedPoints_eq_bot φ partn u hfix
  have htop :
      actionFixedPoints φ (⊤ : Subgroup A) = ⊥ :=
    actionFixedPoints_top_eq_bot_of_parts_fixedPoints_eq_bot φ partn hfix
  have htop_one :
      topOrbitProduct φ u = 1 := by
    rw [topOrbitProduct]
    letI : Fintype (⊤ : Subgroup A) := Fintype.ofFinite (⊤ : Subgroup A)
    exact orbitProduct_eq_one_of_actionFixedPoints_eq_bot φ (⊤ : Subgroup A) u htop
  have hident := hidentity u
  rw [hprod, htop_one, one_mul] at hident
  exact hu hident.symm

/-- Isaacs Lemma 6.8: if `A` is partitioned by proper nonidentity subgroups and
`u^(|Π|-1) ≠ 1`, then some partition part has nontrivial fixed points on `U`. -/
theorem exists_part_actionFixedPoints_ne_bot
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A)
    {u : U} (hu : u ^ (partn.parts.card - 1) ≠ 1) :
    ∃ X, X ∈ partn.parts ∧ actionFixedPoints φ X ≠ ⊥ :=
  exists_part_actionFixedPoints_ne_bot_of_orbitProduct_identity φ partn
    (fun u => partitionOrbitProduct_identity φ partn u) hu

/-- A nontrivial acting subgroup has trivial fixed points under a Frobenius action. -/
theorem actionFixedPoints_eq_bot_of_isFrobeniusAction
    {A U : Type*} [Group A] [Group U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {H : Subgroup A} (hH : H ≠ ⊥) :
    actionFixedPoints (MulDistribMulAction.toMulAut A U) H = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  by_contra hu_ne
  obtain ⟨a, haH, ha_ne⟩ : ∃ a : A, a ∈ H ∧ a ≠ 1 := by
    by_contra hnone
    push Not at hnone
    apply hH
    ext a
    constructor
    · intro ha
      rw [hnone a ha]
      exact Subgroup.one_mem ⊥
    · intro ha
      rw [Subgroup.mem_bot] at ha
      rw [ha]
      exact H.one_mem
  have hfix := hu ⟨a, haH⟩
  have hsmul : a • u = u := by
    simpa using hfix
  exact hFrob a ha_ne u hu_ne hsmul

/-- In a finite group, an element whose order is coprime to `n` cannot satisfy `u ^ n = 1`. -/
theorem pow_ne_one_of_ne_one_of_coprime_natCard
    {U : Type*} [Group U] [Finite U] {n : ℕ}
    (hcop : n.Coprime (Nat.card U)) {u : U} (hu : u ≠ 1) :
    u ^ n ≠ 1 := by
  intro hpow
  have horder_n : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have horder_card : orderOf u ∣ Nat.card U := orderOf_dvd_natCard u
  have horder_eq_one : orderOf u = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop.symm horder_card horder_n
  exact hu (orderOf_eq_one_iff.mp horder_eq_one)

/-- A nontrivial finite group has an element with `u ^ n ≠ 1` whenever `n` is coprime to
its order. -/
theorem exists_pow_ne_one_of_nontrivial_coprime_natCard
    {U : Type*} [Group U] [Finite U] [Nontrivial U] {n : ℕ}
    (hcop : n.Coprime (Nat.card U)) :
    ∃ u : U, u ^ n ≠ 1 := by
  obtain ⟨u, hu⟩ := exists_ne (1 : U)
  exact ⟨u, pow_ne_one_of_ne_one_of_coprime_natCard hcop hu⟩

/-- Lemma 6.8 immediately contradicts a Frobenius action once the counting identity supplies
a suitable element. -/
theorem false_of_frobeniusAction_orbitProduct_identity
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    (hidentity : ∀ u : U,
      partitionOrbitProduct (MulDistribMulAction.toMulAut A U) partn u =
        topOrbitProduct (MulDistribMulAction.toMulAut A U) u * u ^ (partn.parts.card - 1))
    {u : U} (hu : u ^ (partn.parts.card - 1) ≠ 1) :
    False := by
  obtain ⟨X, hX, hXfix_ne⟩ :=
    exists_part_actionFixedPoints_ne_bot_of_orbitProduct_identity
      (MulDistribMulAction.toMulAut A U) partn hidentity hu
  have hXfix_eq :
      actionFixedPoints (MulDistribMulAction.toMulAut A U) X = ⊥ :=
    actionFixedPoints_eq_bot_of_isFrobeniusAction hFrob (partn.nontrivial X hX)
  exact hXfix_ne hXfix_eq

/-- Lemma 6.8 rules out a Frobenius action whenever a subgroup partition has a part-count
exponent detected by some element of `U`. -/
theorem false_of_frobeniusAction_partition_of_nontrivial_power
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    {u : U} (hu : u ^ (partn.parts.card - 1) ≠ 1) :
    False :=
  false_of_frobeniusAction_orbitProduct_identity hFrob partn
    (fun u => partitionOrbitProduct_identity (MulDistribMulAction.toMulAut A U) partn u) hu

/-- Lemma 6.8 in the coprime form used in Theorem 6.9. -/
theorem false_of_frobeniusAction_partition_identity_of_coprime_card
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    (hidentity : ∀ u : U,
      partitionOrbitProduct (MulDistribMulAction.toMulAut A U) partn u =
        topOrbitProduct (MulDistribMulAction.toMulAut A U) u * u ^ (partn.parts.card - 1))
    (hcop : (partn.parts.card - 1).Coprime (Nat.card U)) :
    False := by
  obtain ⟨u, hu⟩ :=
    exists_pow_ne_one_of_nontrivial_coprime_natCard (U := U) hcop
  exact false_of_frobeniusAction_orbitProduct_identity hFrob partn hidentity hu

/-- Lemma 6.8 in the coprime form used in Theorem 6.9, with the counting identity discharged. -/
theorem false_of_frobeniusAction_partition_of_coprime_card
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    (hcop : (partn.parts.card - 1).Coprime (Nat.card U)) :
    False := by
  obtain ⟨u, hu⟩ :=
    exists_pow_ne_one_of_nontrivial_coprime_natCard (U := U) hcop
  exact false_of_frobeniusAction_partition_of_nontrivial_power hFrob partn hu

/-- Isaacs Theorem 6.9 contradiction package: if the acting group has a subgroup partition
whose part count is `1 + n` with `n ∣ |A|`, then it cannot act Frobeniusly on a nontrivial
finite abelian group. -/
theorem false_of_frobeniusAction_partition_of_sub_one_dvd_actor_card
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    (hdvd : partn.parts.card - 1 ∣ Nat.card A) :
    False := by
  have hcop_AU : (Nat.card A).Coprime (Nat.card U) := by
    classical
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype U := Fintype.ofFinite U
    simpa only [Fintype.card_eq_nat_card] using
      (IsFrobeniusAction.coprime_card (A := A) (N := U) hFrob).symm
  exact false_of_frobeniusAction_partition_of_coprime_card hFrob partn
    (hcop_AU.coprime_dvd_left hdvd)

/-- Same contradiction package, in the textual `|Π| = 1 + n` form used in Isaacs 6.9. -/
theorem false_of_frobeniusAction_partition_of_card_eq_succ_and_dvd_actor_card
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A) {n : ℕ}
    (hcard : partn.parts.card = n + 1) (hdvd : n ∣ Nat.card A) :
    False := by
  apply false_of_frobeniusAction_partition_of_sub_one_dvd_actor_card hFrob partn
  rwa [hcard, Nat.add_sub_cancel]

/-- Subgroup form of the Isaacs 6.9 contradiction package: a subgroup of the acting group with
such a partition already contradicts a Frobenius action of the ambient group. -/
theorem false_of_frobeniusAction_actorSubgroup_partition_of_sub_one_dvd_actor_card
    {A U : Type*} [Group A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    (partn : SubgroupPartition B) (hdvd : partn.parts.card - 1 ∣ Nat.card B) :
    False :=
  false_of_frobeniusAction_partition_of_sub_one_dvd_actor_card
    (IsFrobeniusAction.actorSubgroup hFrob B) partn hdvd

/-- Subgroup form of the Isaacs 6.9 contradiction package, with `|Π| = 1 + n`. -/
theorem false_of_frobeniusAction_actorSubgroup_partition_of_card_eq_succ_and_dvd_actor_card
    {A U : Type*} [Group A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    (partn : SubgroupPartition B) {n : ℕ}
    (hcard : partn.parts.card = n + 1) (hdvd : n ∣ Nat.card B) :
    False :=
  false_of_frobeniusAction_partition_of_card_eq_succ_and_dvd_actor_card
    (IsFrobeniusAction.actorSubgroup hFrob B) partn hcard hdvd

/-- **Isaacs Thm 6.9**: a Frobenius actor cannot be elementary abelian of order `p^2`. -/
theorem false_of_frobeniusAction_isElementaryAbelian_card_prime_sq
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p A) (hCard : Nat.card A = p ^ 2) :
    False := by
  let partn := SubgroupPartition.elementaryAbelianPrimeSquare hp hElem hCard
  have hparts :
      partn.parts.card = p + 1 :=
    SubgroupPartition.elementaryAbelianPrimeSquare_parts_card hp hElem hCard
  have hdvd : p ∣ Nat.card A := by
    rw [hCard, pow_two]
    exact dvd_mul_right p p
  exact false_of_frobeniusAction_partition_of_card_eq_succ_and_dvd_actor_card
    hFrob partn hparts hdvd

/-- Subgroup form of Isaacs Thm 6.9: an elementary abelian `p^2` subgroup cannot occur in a
Frobenius actor. -/
theorem false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq
    {A U : Type*} [Group A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p B) (hCard : Nat.card B = p ^ 2) :
    False :=
  false_of_frobeniusAction_isElementaryAbelian_card_prime_sq
    (IsFrobeniusAction.actorSubgroup hFrob B) hp hElem hCard

end

section /- 6B structural helper: finite abelian Z-groups -/

/-! ### Finite abelian Z-group helpers

Isaacs Lemma 6.20 uses Corollary 6.17 to show that the Sylow subgroups of an abelian
Frobenius complement are cyclic, and then concludes that the complement itself is cyclic.
Mathlib packages the Sylow-cyclic condition as `IsZGroup`; these helpers expose exactly the
abelian specialization needed for the 6.20 route. -/

/-- A finite abelian group whose Sylow subgroups are all cyclic is cyclic. -/
theorem isCyclic_of_sylow_isCyclic
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hSylow : ∀ p : ℕ, p.Prime → ∀ P : Sylow p A, IsCyclic P) :
    IsCyclic A := by
  haveI : IsZGroup A := ⟨hSylow⟩
  exact inferInstance

/-- If a finite abelian group is not cyclic, then some Sylow subgroup is not cyclic. -/
theorem exists_prime_sylow_not_isCyclic_of_not_isCyclic
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : ¬ IsCyclic A) :
    ∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p A, ¬ IsCyclic P := by
  by_contra hnone
  apply hA
  exact isCyclic_of_sylow_isCyclic (A := A) fun p hp P => by
    by_contra hP
    exact hnone ⟨p, hp, P, hP⟩

end

section /- 6B (number-theoretic prelude): Lemma 6.16 (pp. 191-193) -/

/-! ### Isaacs Lemma 6.16

Pure number-theoretic fact used in §6B for the Sylow structure of Frobenius complements
(Cor 6.17). Independent of all preceding chapters and of §6A.

* For `p` odd: relies on the Lifting-the-Exponent lemma (mathlib
  `Int.emultiplicity_pow_sub_pow`); conclusion `i ≡ 1 (mod p^{e-1})` always holds.
* For `p = 2`: direct factorization `i^2 - 1 = (i-1)(i+1)` plus coprimality of the two
  factors with the odd residual. Three sub-cases according to which factor carries the
  bulk of the `2`-power and whether the residual is even or odd. -/

open Int

/-- Helper for the `p = 2` branch of Lemma 6.16: if `2 ^ (e + 1) ∣ i ^ 2 - 1`, then
`2 ^ e` divides one of `i - 1` or `i + 1`. -/
private theorem two_pow_dvd_or_of_sq_sub_one {e : ℕ} {i : ℤ}
    (h : (2 : ℤ) ^ (e + 1) ∣ i ^ 2 - 1) :
    (2 : ℤ) ^ e ∣ i - 1 ∨ (2 : ℤ) ^ e ∣ i + 1 := by
  -- `i` must be odd, otherwise `i^2 - 1` is odd, contradicting even divisibility.
  have h_fact : (i ^ 2 - 1 : ℤ) = (i - 1) * (i + 1) := by ring
  rw [h_fact] at h
  have h_i_odd : Odd i := by
    rcases Int.even_or_odd i with ⟨k, rfl⟩ | hodd
    · -- `i = k + k`, so `(i - 1)(i + 1) = (k+k-1)(k+k+1)` is a product of two odd numbers; odd.
      exfalso
      have h2 : (2 : ℤ) ∣ (k + k - 1) * (k + k + 1) :=
        (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans h
      rcases Int.prime_two.dvd_or_dvd h2 with h2' | h2'
      · -- `2 ∣ k + k - 1` is impossible mod 2.
        omega
      · omega
    · exact hodd
  obtain ⟨j, rfl⟩ := h_i_odd
  -- Now `i = 2 j + 1`. Factorization: `(i-1)(i+1) = (2j)(2j+2) = 4 · j · (j+1)`.
  have h_dvd' : (2 : ℤ) ^ (e + 1) ∣ 4 * (j * (j + 1)) := by
    have h_re : ((2 * j + 1) - 1) * ((2 * j + 1) + 1) = 4 * (j * (j + 1)) := by ring
    rwa [h_re] at h
  -- Case split on parity of `j` (then either `j` or `j + 1` contributes a 2-power).
  rcases Int.even_or_odd j with hjeven | hjodd
  · -- `j = 2k` (well, `j = k + k`). Then `i - 1 = 4k`.
    obtain ⟨k, rfl⟩ := hjeven
    -- Coprimality: `2k + 1` (i.e. `(k + k) + 1`) is odd.
    have h_coprime : IsCoprime ((2 : ℤ) ^ (e + 1)) ((k + k) + 1) := by
      apply IsCoprime.pow_left
      exact ⟨-k, 1, by ring⟩
    -- Rewrite `4 * ((k + k) * ((k + k) + 1))` as `(4 * (k + k)) * ((k + k) + 1)` to factor.
    have h_dvd'' : (2 : ℤ) ^ (e + 1) ∣ (4 * (k + k)) * ((k + k) + 1) := by
      convert h_dvd' using 1; ring
    have h_dvd_bulk : (2 : ℤ) ^ (e + 1) ∣ 4 * (k + k) :=
      h_coprime.dvd_of_dvd_mul_right h_dvd''
    -- `4 * (k + k) = 8 k = 2 · (4 k)`. Divide by 2: `2^e ∣ 4k = i - 1`.
    left
    rcases h_dvd_bulk with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2pow : (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have hm' : (4 : ℤ) * (k + k) = 2 * (2 ^ e * m) := by rw [hm, h2pow]; ring
    -- `((k + k) + 1) - 1 = k + k`, so `i - 1 = (2 j + 1) - 1` with `j = k + k`.
    linarith
  · -- `j = 2k + 1` for some `k`. Then `i + 1 = 2(2k+1) + 2 = 4(k+1)`.
    obtain ⟨k, rfl⟩ := hjodd
    right
    -- `2 k + 1` is odd.
    have h_coprime : IsCoprime ((2 : ℤ) ^ (e + 1)) (2 * k + 1) := by
      apply IsCoprime.pow_left
      exact ⟨-k, 1, by ring⟩
    -- `4 * ((2k+1) * ((2k+1) + 1)) = (4 * (2 * (k + 1))) * (2 k + 1)`.
    have h_dvd'' : (2 : ℤ) ^ (e + 1) ∣ (4 * (2 * (k + 1))) * (2 * k + 1) := by
      convert h_dvd' using 1; ring
    have h_dvd_bulk : (2 : ℤ) ^ (e + 1) ∣ 4 * (2 * (k + 1)) :=
      h_coprime.dvd_of_dvd_mul_right h_dvd''
    rcases h_dvd_bulk with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2pow : (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have hm' : (4 : ℤ) * (2 * (k + 1)) = 2 * (2 ^ e * m) := by rw [hm, h2pow]; ring
    -- `(2 * (2 k + 1) + 1) + 1 = 4 k + 4 = 4 (k + 1)`, so this is `i + 1`.
    linarith

/-- **Isaacs Lemma 6.16**. Let `p` be a prime and `e` a positive integer. If `i : ℤ` satisfies
`i ^ p ≡ 1 (mod p ^ e)`, then one of the following holds:
* `i ≡ 1 (mod p ^ (e - 1))`,
* `p = 2` and `i ≡ -1 (mod 2 ^ e)`,
* `p = 2` and `i ≡ 2 ^ (e - 1) - 1 (mod 2 ^ e)`. -/
theorem pow_prime_modEq_one_cases {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) {i : ℤ}
    (h : i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)]) :
    i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] ∨
    (p = 2 ∧ i ≡ -1 [ZMOD ((2 : ℤ) ^ e)]) ∨
    (p = 2 ∧ i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) := by
  -- Normalise `e = e' + 1` so `e - 1 = e'` is definitionally clean.
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.sub_add_cancel he).symm⟩
  simp only [Nat.add_sub_cancel]
  -- Convert hypothesis to divisibility (`a ≡ b [ZMOD n]` gives `n ∣ b - a`).
  have h_dvd : ((p : ℤ) ^ (e' + 1)) ∣ i ^ p - 1 := h.symm.dvd
  rcases hp.eq_two_or_odd' with rfl | hp_odd
  · -- ##### Case p = 2 #####
    rcases two_pow_dvd_or_of_sq_sub_one h_dvd with h_left | h_right
    · -- (a) holds: `2 ^ e' ∣ i - 1` ⇒ `i ≡ 1 (mod 2^e')`.
      left
      refine Int.modEq_iff_dvd.mpr ?_
      have : (1 - i : ℤ) = -(i - 1) := by ring
      rw [this]
      exact dvd_neg.mpr h_left
    · -- `2 ^ e' ∣ i + 1`. Case-split on whether `2 ^ (e' + 1) ∣ i + 1`.
      by_cases h_b : (2 : ℤ) ^ (e' + 1) ∣ i + 1
      · -- (b): `2 ^ (e' + 1) ∣ i + 1`, i.e. `i ≡ -1 (mod 2 ^ (e' + 1))`.
        right; left
        refine ⟨rfl, Int.modEq_iff_dvd.mpr ?_⟩
        have : (-1 - i : ℤ) = -(i + 1) := by ring
        rw [this]
        exact dvd_neg.mpr h_b
      · -- (c): write `i + 1 = 2 ^ e' * a` with `a` odd (else (b) would hold).
        right; right
        refine ⟨rfl, Int.modEq_iff_dvd.mpr ?_⟩
        obtain ⟨a, ha⟩ := h_right
        have ha_odd : Odd a := by
          rcases Int.even_or_odd a with hev | hodd
          · -- `a = b + b`, so `i + 1 = 2 ^ e' * (b + b) = 2 * (2^e' * b)`, contradicting `h_b`.
            exfalso
            obtain ⟨b, rfl⟩ := hev
            apply h_b
            refine ⟨b, ?_⟩
            rw [ha, pow_succ]; ring
          · exact hodd
        obtain ⟨b, rfl⟩ := ha_odd
        -- `i + 1 = 2^e' * (2 b + 1)`, so `i = 2^e' * (2 b + 1) - 1 = (2^e' - 1) + 2^(e'+1) * b`.
        -- Goal: `2 ^ (e' + 1) ∣ (2 ^ e' - 1) - i`.
        refine ⟨-b, ?_⟩
        have hi : i = (2 : ℤ) ^ e' * (2 * b + 1) - 1 := by linarith
        rw [hi, pow_succ]; ring
  · -- ##### Case p odd ##### (LTE).
    left
    -- Step 1: `p ∣ i - 1` from Fermat + hypothesis reduced modulo `p`.
    have h_p_dvd_sub : (p : ℤ) ∣ i - 1 := by
      have h_fermat : i ^ p ≡ i [ZMOD (p : ℤ)] := Int.ModEq.pow_prime_eq_self hp i
      have h_mod_p : i ^ p ≡ 1 [ZMOD (p : ℤ)] :=
        h.of_dvd (dvd_pow_self _ (Nat.succ_ne_zero _))
      exact (h_fermat.symm.trans h_mod_p).symm.dvd
    -- Step 2: `p ∤ i` (else `p ∣ 1`).
    have h_p_not_dvd_i : ¬ (p : ℤ) ∣ i := by
      intro hpi
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub hpi h_p_dvd_sub
        simpa using this
      have hp_eq : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
      have hp_eq' : p = 1 := by exact_mod_cast hp_eq
      exact hp.one_lt.ne' hp_eq'
    -- Step 3: LTE: `emultiplicity p (i^p - 1) = emultiplicity p (i - 1) + emultiplicity p p`.
    have h_LTE :=
      Int.emultiplicity_pow_sub_pow hp hp_odd (x := i) (y := 1) (by simpa using h_p_dvd_sub)
        h_p_not_dvd_i p
    rw [one_pow, hp.emultiplicity_self] at h_LTE
    -- Convert the hypothesis into an `emultiplicity` lower bound.
    have h_e_le : ((e' + 1 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ) (i ^ p - 1) :=
      pow_dvd_iff_le_emultiplicity.mp h_dvd
    rw [h_LTE] at h_e_le
    -- `(e' + 1 : ℕ∞) ≤ m + 1 ⇒ (e' : ℕ∞) ≤ m`.
    have h_em : (e' : ℕ∞) ≤ emultiplicity (p : ℤ) (i - 1) := by
      have h_cast : ((e' + 1 : ℕ) : ℕ∞) = (e' : ℕ∞) + 1 := by push_cast; rfl
      rw [h_cast] at h_e_le
      exact (WithTop.add_le_add_iff_right WithTop.one_ne_top).mp h_e_le
    have h_pe'_dvd : (p : ℤ) ^ e' ∣ i - 1 := pow_dvd_iff_le_emultiplicity.mpr h_em
    refine Int.modEq_iff_dvd.mpr ?_
    have : (1 - i : ℤ) = -(i - 1) := by ring
    rw [this]
    exact dvd_neg.mpr h_pe'_dvd

end
section /- 6A continued: Frobenius group (subgroup pair, Thm 6.4) -/

/-! ### Definition of Frobenius group (subgroup-pair version)

A **Frobenius group** is a group `G` together with a nontrivial proper normal subgroup `N`
(the *kernel*) and a nontrivial complement `A` (the *Frobenius complement*) such that the
conjugation action of `A` on `N` is Frobenius (Isaacs's condition (1) of Thm 6.4).

Thm 6.4 in Isaacs asserts the equivalence of four conditions:
1. (conjugation-Frobenius) `∀ 1 ≠ a ∈ A, 1 ≠ n ∈ N, a n a⁻¹ ≠ n`.
2. (TI) `∀ g ∉ A, A ∩ A^g = 1`.
3. (centralizer-in-A) `∀ 1 ≠ a ∈ A, C_G(a) ⊆ A`.
4. (centralizer-in-N) `∀ 1 ≠ n ∈ N, C_G(n) ⊆ N`.

We adopt (1) as the canonical condition (it is the most directly elementary). We then prove
the cyclic equivalence of (1) ⇔ (2) ⇔ (3) directly, and supply constructors from (3) and (4).
The direction (1) ⇒ (4) requires Cor 6.6 (Frobenius's theorem on Frobenius kernels) and is
deferred. -/

/-- A **Frobenius group**: `G` has a nontrivial normal subgroup `N` (the *Frobenius kernel*)
complemented by a nontrivial subgroup `A` (the *Frobenius complement*), with the conjugation
action of `A` on `N` being Frobenius.

This is Isaacs's condition (1) of Thm 6.4; the other three equivalent conditions are proven
separately as `trivialIntersection`, `centralizer_complement_le`, and the constructors
`of_centralizer_complement_le` / `of_centralizer_kernel_le`. -/
structure IsFrobeniusGroup (G : Type*) [Group G] (N A : Subgroup G) : Prop where
  /-- The kernel `N` is normal in `G`. -/
  isNormal : N.Normal
  /-- `N` and `A` are complements: `N ⊓ A = ⊥` and the product map `N × A → G` is a bijection. -/
  isComplement : Subgroup.IsComplement' N A
  /-- The kernel is nontrivial. -/
  ne_bot_kernel : N ≠ ⊥
  /-- The complement is nontrivial. -/
  ne_bot_complement : A ≠ ⊥
  /-- The conjugation action of `A` on `N` is Frobenius (Isaacs Thm 6.4 condition (1)). -/
  conj_frobenius : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ N, n ≠ 1 → a * n * a⁻¹ ≠ n

namespace IsFrobeniusGroup

variable {G : Type*} [Group G] {N A : Subgroup G}

/-- A subgroup-pair Frobenius group gives a Frobenius action of the complement on the kernel by
conjugation. This is the bridge between the pair form of Isaacs Thm 6.4 and the action-based
definition used for Lemma 6.1. -/
theorem toFrobeniusAction (h : IsFrobeniusGroup G N A) :
    letI : N.Normal := h.isNormal
    @IsFrobeniusAction A N _ _
      (MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)) := by
  letI : N.Normal := h.isNormal
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  intro a ha n hn hfix
  have haG : (a : G) ≠ 1 := fun haG => ha (Subtype.ext haG)
  have hnG : (n : G) ≠ 1 := fun hnG => hn (Subtype.ext hnG)
  have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = n := Subtype.ext_iff.mp hfix
  exact h.conj_frobenius (a : G) a.2 haG (n : G) n.2 hnG hfixG

/-- Subgroup-pair version of Isaacs Lemma 6.1: in a finite Frobenius group,
`|N| ≡ 1 (mod |A|)`. -/
theorem card_kernel_modEq_one [Finite G] (h : IsFrobeniusGroup G N A) :
    Nat.card N ≡ 1 [MOD Nat.card A] := by
  classical
  letI : N.Normal := h.isNormal
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype A := Fintype.ofFinite A
  simpa only [Fintype.card_eq_nat_card] using
    IsFrobeniusAction.card_modEq_one (A := A) (N := N) h.toFrobeniusAction

/-- Subgroup-pair version of Isaacs Lemma 6.1: in a finite Frobenius group, the kernel and
complement have coprime orders. -/
theorem coprime_card_kernel_complement [Finite G] (h : IsFrobeniusGroup G N A) :
    Nat.Coprime (Nat.card N) (Nat.card A) := by
  classical
  letI : N.Normal := h.isNormal
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype A := Fintype.ofFinite A
  simpa only [Fintype.card_eq_nat_card] using
    IsFrobeniusAction.coprime_card (A := A) (N := N) h.toFrobeniusAction

/-- **Isaacs Thm 6.4 (3) ⇒ (1)** (constructor). If `C_G(a) ⊆ A` for every nontrivial `a ∈ A`,
then the conjugation action of `A` on `N` is Frobenius. -/
theorem of_centralizer_complement_le
    (hN : N.Normal) (hC : Subgroup.IsComplement' N A)
    (hN_ne : N ≠ ⊥) (hA_ne : A ≠ ⊥)
    (h3 : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ A) :
    IsFrobeniusGroup G N A where
  isNormal := hN
  isComplement := hC
  ne_bot_kernel := hN_ne
  ne_bot_complement := hA_ne
  conj_frobenius := by
    intro a haA ha n hnN hn h_conj
    -- `a * n * a⁻¹ = n` ⇒ `n * a = a * n` ⇒ `n ∈ C_G(a) ⊆ A`.
    have h_an : a * n = n * a := by
      have := congrArg (· * a) h_conj
      simpa using this
    have h_comm : n * a = a * n := h_an.symm
    have hnA : n ∈ A :=
      h3 a haA ha (Subgroup.mem_centralizer_singleton_iff.mpr h_comm)
    -- `n ∈ N ∩ A = ⊥` ⇒ `n = 1`, contradicting `hn`.
    have hdisj : Disjoint N A := hC.disjoint
    exact hn (Subgroup.disjoint_def.mp hdisj hnN hnA)

/-- **Isaacs Thm 6.4 (4) ⇒ (1)** (constructor). If `C_G(n) ⊆ N` for every nontrivial `n ∈ N`,
then the conjugation action of `A` on `N` is Frobenius. -/
theorem of_centralizer_kernel_le
    (hN : N.Normal) (hC : Subgroup.IsComplement' N A)
    (hN_ne : N ≠ ⊥) (hA_ne : A ≠ ⊥)
    (h4 : ∀ n ∈ N, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ N) :
    IsFrobeniusGroup G N A where
  isNormal := hN
  isComplement := hC
  ne_bot_kernel := hN_ne
  ne_bot_complement := hA_ne
  conj_frobenius := by
    intro a haA ha n hnN hn h_conj
    -- `a * n * a⁻¹ = n` ⇒ `a * n = n * a` ⇒ `a ∈ C_G(n) ⊆ N`.
    have h_an : a * n = n * a := by
      have := congrArg (· * a) h_conj
      simpa using this
    -- We need `a ∈ C_G(n) = { x : x * n = n * x }`.
    have h_comm : a * n = n * a := h_an
    have haN : a ∈ N :=
      h4 n hnN hn (Subgroup.mem_centralizer_singleton_iff.mpr h_comm)
    -- `a ∈ N ∩ A = ⊥` ⇒ `a = 1`, contradicting `ha`.
    have hdisj : Disjoint N A := hC.disjoint
    exact ha (Subgroup.disjoint_def.mp hdisj haN haA)

/-- Given `IsComplement' N A`, every `g : G` factors uniquely as `n * a` with `n ∈ N`, `a ∈ A`. -/
private theorem _root_.Subgroup.IsComplement'.factor
    (hC : Subgroup.IsComplement' N A) (g : G) :
    ∃ (n : G) (a : G), n ∈ N ∧ a ∈ A ∧ n * a = g := by
  obtain ⟨⟨n, a⟩, hna⟩ := (hC.existsUnique g).exists
  exact ⟨n, a, n.2, a.2, hna⟩

/-- **Isaacs Thm 6.4 (1) ⇒ (2)**: Frobenius group ⇒ trivial intersection.

If `g ∉ A`, then `A ⊓ A^g = ⊥`. (Here `A^g = g A g⁻¹ = (MulAut.conj g) '' A`.) -/
theorem trivialIntersection (h : IsFrobeniusGroup G N A) :
    ∀ g : G, g ∉ A → A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A = ⊥ := by
  intro g hg
  -- Outline: assume `A ⊓ A^g ≠ ⊥`, derive `g ∈ A`, contradiction.
  by_contra h_ne
  apply hg
  -- Factor `g = n * a` with `n ∈ N`, `a ∈ A` (from `IsComplement' N A`).
  obtain ⟨n, a, hnN, haA, hna⟩ := h.isComplement.factor g
  -- Get a nontrivial `x ∈ A ⊓ A^g`.
  have h_ne_bot : A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A ≠ ⊥ := h_ne
  obtain ⟨x, hxAg, hx_ne⟩ : ∃ x ∈ A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A, x ≠ 1 := by
    by_contra h_all
    apply h_ne_bot
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy_ne
    exact h_all ⟨y, hy, hy_ne⟩
  rw [Subgroup.mem_inf] at hxAg
  obtain ⟨hxA, hxAg⟩ := hxAg
  -- `x = g * b * g⁻¹` for some `b ∈ A`.
  rw [Subgroup.mem_map] at hxAg
  obtain ⟨b, hbA, hxeq⟩ := hxAg
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hxeq
  -- Substitute `g = n * a`. Then `x = (n * a) * b * (n * a)⁻¹ = n * (a b a⁻¹) * n⁻¹`.
  have hxeq' : x = n * (a * b * a⁻¹) * n⁻¹ := by
    rw [← hxeq, ← hna]
    group
  -- Let `b' := a * b * a⁻¹ ∈ A`. Then `x = n * b' * n⁻¹` and `b' ∈ A`.
  set b' := a * b * a⁻¹ with hb'_def
  have hb'_mem : b' ∈ A := by
    rw [hb'_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haA hbA) (Subgroup.inv_mem _ haA)
  have hx_eq2 : x = n * b' * n⁻¹ := hxeq'
  -- Consider `b'⁻¹ * x = b'⁻¹ * (n * b' * n⁻¹)`.
  -- This is in `A` (both `b'⁻¹` and `x` are in `A`).
  -- This is also in `N`: rewrite as `(b'⁻¹ * n * b') * n⁻¹`. The factor `b'⁻¹ * n * b' ∈ N`
  -- by normality of `N`, and `n⁻¹ ∈ N`, so the product is in `N`.
  have h_comm_elem : b'⁻¹ * (n * b' * n⁻¹) ∈ A := by
    apply Subgroup.mul_mem
    · exact Subgroup.inv_mem _ hb'_mem
    · rw [← hx_eq2]; exact hxA
  have h_comm_elem' : b'⁻¹ * (n * b' * n⁻¹) ∈ N := by
    -- Rewrite as `(b'⁻¹ * n * b') * n⁻¹`.
    have h_eq : b'⁻¹ * (n * b' * n⁻¹) = (b'⁻¹ * n * b') * n⁻¹ := by group
    rw [h_eq]
    apply Subgroup.mul_mem _ _ (Subgroup.inv_mem _ hnN)
    -- `b'⁻¹ * n * b' ∈ N` by normality.
    have := h.isNormal.conj_mem' n hnN b'
    exact this
  have hdisj : Disjoint N A := h.isComplement.disjoint
  -- So `b'⁻¹ * (n * b' * n⁻¹) = 1`, i.e., `n * b' * n⁻¹ = b'`, i.e., `b'` commutes with `n`.
  have h_one : b'⁻¹ * (n * b' * n⁻¹) = 1 := Subgroup.disjoint_def.mp hdisj h_comm_elem' h_comm_elem
  have h_conj_b' : n * b' * n⁻¹ = b' := by
    have := h_one
    -- `b'⁻¹ * Y = 1` ⇒ `Y = b'`.
    have h_mul := congrArg (b' * ·) this
    simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h_mul
    exact h_mul
  -- By Frobenius condition, if `b' ≠ 1` and `n ≠ 1`, then... wait, we have `b' * n * b'⁻¹ ≠ n`.
  -- Reformulate `h_conj_b'`: `n * b' * n⁻¹ = b'` ⇔ `n * b' = b' * n` ⇔ `b' * n * b'⁻¹ = n`.
  -- So if `b' ≠ 1` and `n ≠ 1`, Frobenius gives contradiction. Hence `b' = 1` or `n = 1`.
  have h_conj_n : b' * n * b'⁻¹ = n := by
    -- `n * b' * n⁻¹ = b'` ⇒ `n * b' = b' * n`.
    have h_nb' : n * b' = b' * n := by
      have := congrArg (· * n) h_conj_b'
      simpa using this
    -- `b' * n * b'⁻¹ = (b' * n) * b'⁻¹ = (n * b') * b'⁻¹ = n`.
    rw [← h_nb', mul_inv_cancel_right]
  -- Case analysis: either `b' = 1` or `n = 1`.
  by_cases h_n_one : n = 1
  · -- `n = 1` ⇒ `g = n * a = a ∈ A`.
    rw [← hna, h_n_one, one_mul]
    exact haA
  · -- `n ≠ 1`. By Frobenius, `b' = 1`. Then `x = n * 1 * n⁻¹ = 1`, contradiction.
    by_cases h_b'_one : b' = 1
    · exfalso
      have : x = 1 := by rw [hx_eq2, h_b'_one, mul_one, mul_inv_cancel]
      exact hx_ne this
    · exfalso
      exact h.conj_frobenius b' hb'_mem h_b'_one n hnN h_n_one h_conj_n

/-- **Isaacs Thm 6.4 (2) ⇒ (3)**: Frobenius group ⇒ centralizer of any nontrivial element of `A`
is contained in `A`. -/
theorem centralizer_complement_le (h : IsFrobeniusGroup G N A) :
    ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ A := by
  intro a haA ha x hx
  -- `x * a = a * x`, so `x * a * x⁻¹ = a`, so `a = (MulAut.conj x) a⁻¹⁻¹ ∈ A.map (MulAut.conj x)`.
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  -- Want: `x ∈ A`. Assume for contradiction `x ∉ A`.
  by_contra hxA
  -- By (2), `A ⊓ A^x = ⊥`.
  have h_ti := h.trivialIntersection x hxA
  -- `a ∈ A ⊓ A^x`: indeed `a ∈ A`, and `a = (MulAut.conj x) a` (from commutativity).
  have h_a_in_conj : a ∈ Subgroup.map (MulAut.conj x).toMonoidHom A := by
    rw [Subgroup.mem_map]
    refine ⟨a, haA, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    -- `x * a * x⁻¹ = a` follows from `x * a = a * x`.
    have := hx
    calc x * a * x⁻¹ = (x * a) * x⁻¹ := by rfl
      _ = (a * x) * x⁻¹ := by rw [hx]
      _ = a := by rw [mul_inv_cancel_right]
  have h_a_in : a ∈ A ⊓ Subgroup.map (MulAut.conj x).toMonoidHom A :=
    Subgroup.mem_inf.mpr ⟨haA, h_a_in_conj⟩
  rw [h_ti, Subgroup.mem_bot] at h_a_in
  exact ha h_a_in

/-- **Isaacs Corollary 6.6**: In a Frobenius group `G` with kernel `N` and complement `A`, the
kernel `N` is exactly the set of elements **not** conjugate to any nonidentity element of `A`.

Proof: For `n ∈ N`, if `IsConj a n` with `a ∈ A`, write `g * a * g⁻¹ = n`. Then `a = g⁻¹ * n * g`
lies in `N` (by normality of `N`), so `a ∈ N ⊓ A = ⊥`, i.e., `a = 1`. Hence `N ⊆ notConjugateSet A`.
Equality follows by cardinality: `|N| = A.index = |notConjugateSet A|` (Lagrange + Lem 6.5). -/
theorem kernel_eq_notConjugateSet [Finite G] (h : IsFrobeniusGroup G N A) :
    (N : Set G) = notConjugateSet A := by
  classical
  -- Step 1: N ⊆ notConjugateSet A.
  have h_subset : (N : Set G) ⊆ notConjugateSet A := by
    intro n hnN a haA ha_ne h_conj
    rw [SetLike.mem_coe] at hnN
    rw [isConj_iff] at h_conj
    obtain ⟨g, hg⟩ := h_conj
    -- hg : g * a * g⁻¹ = n. Rearrange: a = g⁻¹ * n * g.
    have hag : a = g⁻¹ * n * g := by rw [← hg]; group
    -- g⁻¹ * n * g ∈ N (normality), so a ∈ N.
    have h_gng_in_N : g⁻¹ * n * g ∈ N := by
      have := h.isNormal.conj_mem n hnN g⁻¹
      simpa using this
    have ha_in_N : a ∈ N := hag ▸ h_gng_in_N
    have hdisj : Disjoint N A := h.isComplement.disjoint
    exact ha_ne (Subgroup.disjoint_def.mp hdisj ha_in_N haA)
  -- Step 2: Equal cardinalities + subset ⇒ equal.
  have h_ncard_N : (N : Set G).ncard = A.index := h.isComplement.ncard_left
  have h_ncard_X : (notConjugateSet A).ncard = A.index :=
    card_notConjugateSet_eq_index A fun g hg => h.trivialIntersection g hg
  have h_finite : (notConjugateSet A).Finite := Set.toFinite _
  exact Set.eq_of_subset_of_ncard_le h_subset (h_ncard_X.trans h_ncard_N.symm).le h_finite

/-- **Isaacs Thm 6.4 (1) ⇒ (4)**: Frobenius group ⇒ centralizer of any nontrivial element of `N`
is contained in `N`. Together with `of_centralizer_kernel_le` this completes the four-way
equivalence of Thm 6.4.

Proof uses Cor 6.6 (`kernel_eq_notConjugateSet`): suppose `c ∈ C_G(n) \ N`. Then `c` is conjugate
to some `1 ≠ a ∈ A`, say `c = g a g⁻¹`. Set `m := g⁻¹ n g ∈ N` (by normality, `m ≠ 1`). From
`c * n * c⁻¹ = n` we get `a * m * a⁻¹ = m`, contradicting the Frobenius condition. -/
theorem centralizer_kernel_le [Finite G] (h : IsFrobeniusGroup G N A) :
    ∀ n ∈ N, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ N := by
  intro n hnN hn_ne c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  -- hc : c * n = n * c
  by_contra hcN
  -- c ∉ N. Use Cor 6.6: N = notConjugateSet A, so c ∉ notConjugateSet A.
  have hX_eq := h.kernel_eq_notConjugateSet
  have hcX : c ∉ notConjugateSet A := by
    intro h_mem
    apply hcN
    have h_in_N_set : c ∈ (N : Set G) := hX_eq ▸ h_mem
    exact h_in_N_set
  -- ¬ (∀ a ∈ A, a ≠ 1 → ¬ IsConj a c) ⇒ ∃ a ∈ A, a ≠ 1, IsConj a c.
  simp only [notConjugateSet, Set.mem_setOf_eq, not_forall, not_not] at hcX
  obtain ⟨a, haA, ha_ne, h_conj⟩ := hcX
  rw [isConj_iff] at h_conj
  obtain ⟨g, hgac⟩ := h_conj
  -- hgac : g * a * g⁻¹ = c
  -- Set m := g⁻¹ * n * g; by normality m ∈ N, and m ≠ 1 since n ≠ 1.
  set m := g⁻¹ * n * g with hm_def
  have hmN : m ∈ N := by
    have := h.isNormal.conj_mem n hnN g⁻¹
    simpa using this
  have hm_ne : m ≠ 1 := by
    intro hm_one
    apply hn_ne
    have h_n_eq : n = g * m * g⁻¹ := by rw [hm_def]; group
    rw [h_n_eq, hm_one, mul_one, mul_inv_cancel]
  -- From c * n = n * c and c = g a g⁻¹, conjugating both sides by g⁻¹/g gives a * m = m * a.
  have h_am : a * m * a⁻¹ = m := by
    have h_eq : a * m = m * a := by
      have h_cn : c * n = n * c := hc
      have h_cong : g⁻¹ * (c * n) * g = g⁻¹ * (n * c) * g :=
        congrArg (fun x => g⁻¹ * x * g) h_cn
      have hLHS : g⁻¹ * (c * n) * g = a * m := by
        rw [← hgac, hm_def]; group
      have hRHS : g⁻¹ * (n * c) * g = m * a := by
        rw [← hgac, hm_def]; group
      rw [hLHS, hRHS] at h_cong
      exact h_cong
    -- a * m = m * a ⇒ a * m * a⁻¹ = m.
    calc a * m * a⁻¹ = (m * a) * a⁻¹ := by rw [h_eq]
      _ = m := mul_inv_cancel_right m a
  exact h.conj_frobenius a haA ha_ne m hmN hm_ne h_am

open scoped Pointwise

/-- In a Frobenius group, the kernel has trivial intersection with every conjugate of the
complement. This is the `N ∩ A^g = 1` part used in the partition construction of §6B. -/
theorem disjoint_kernel_conjugate_complement (h : IsFrobeniusGroup G N A) (g : G) :
    Disjoint N (MulAut.conj g • A : Subgroup G) := by
  rw [Subgroup.disjoint_def]
  intro x hxN hxAconj
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxAconj
  have haN : (MulAut.conj g)⁻¹ x ∈ N := by
    have hx_conj_N := h.isNormal.conj_mem x hxN g⁻¹
    change (MulAut.conj g).symm x ∈ N
    simpa [MulAut.conj_symm_apply] using hx_conj_N
  have hdisj : Disjoint N A := h.isComplement.disjoint
  have ha_one : (MulAut.conj g)⁻¹ x = 1 :=
    Subgroup.disjoint_def.mp hdisj haN hxAconj
  have hx_one : x = 1 := by
    have hraw : g⁻¹ * x * g = 1 := by
      simpa [MulAut.conj_symm_apply] using ha_one
    calc
      x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by
        rw [hraw]
        group
  exact hx_one

end IsFrobeniusGroup

namespace SubgroupPartition

open scoped Pointwise

variable {G : Type*} [Group G]

private theorem exists_ne_one_mem_of_ne_bot {H : Subgroup G} (hH : H ≠ ⊥) :
    ∃ x : G, x ∈ H ∧ x ≠ 1 := by
  by_contra hnone
  push Not at hnone
  apply hH
  exact (Subgroup.eq_bot_iff_forall H).mpr fun x hx => hnone x hx

private noncomputable def conjugatesFinset [Finite G] (A : Subgroup G) :
    Finset (Subgroup G) := by
  classical
  exact (Set.finite_range (fun g : G => MulAut.conj g • A)).toFinset

private theorem mem_conjugatesFinset [Finite G] {A B : Subgroup G} :
    B ∈ conjugatesFinset A ↔ ∃ g : G, B = MulAut.conj g • A := by
  classical
  unfold conjugatesFinset
  rw [Set.Finite.mem_toFinset, Set.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩

private theorem conjugatesFinset_card_eq_index [Finite G] {A : Subgroup G}
    (hA_ne : A ≠ ⊥)
    (hTI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    (conjugatesFinset A).card = A.index := by
  classical
  have hcard :=
    Set.ncard_eq_toFinset_card
      (Set.range (fun g : G => MulAut.conj g • A)) (Set.finite_range _)
  rw [conjugatesFinset, ← hcard]
  exact ncard_conjugates_eq_index_of_TI hA_ne hTI

/-- Isaacs §6B partition attached to a Frobenius group: the kernel together with all conjugates
of the complement. -/
noncomputable def frobeniusGroup [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) :
    SubgroupPartition G where
  parts := by
    classical
    exact insert N (conjugatesFinset A)
  nontrivial := by
    classical
    intro X hX hX_bot
    rcases Finset.mem_insert.mp hX with hXN | hX
    · apply h.ne_bot_kernel
      rw [← hXN]
      exact hX_bot
    · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hX
      obtain ⟨a, haA, ha_ne⟩ := exists_ne_one_mem_of_ne_bot h.ne_bot_complement
      apply ha_ne
      have hmem_conj : MulAut.conj g a ∈ (MulAut.conj g • A : Subgroup G) := by
        simpa using Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) A haA
      have hmem : MulAut.conj g a ∈ (⊥ : Subgroup G) := by
        simpa [hX_bot] using hmem_conj
      rw [Subgroup.mem_bot] at hmem
      have ha_one : a = 1 := by
        have hraw : g⁻¹ * (g * a * g⁻¹) * g = 1 := by
          simpa [MulAut.conj_apply, MulAut.conj_symm_apply] using
            congrArg (MulAut.conj g).symm hmem
        calc
          a = g⁻¹ * (g * a * g⁻¹) * g := by group
          _ = 1 := hraw
      exact ha_one
  proper := by
    classical
    intro X hX hX_top
    rcases Finset.mem_insert.mp hX with hXN | hX
    · apply h.ne_bot_complement
      exact (Subgroup.eq_bot_iff_forall A).mpr fun a haA => by
        have haN : a ∈ N := by
          rw [← hXN, hX_top]
          exact Subgroup.mem_top a
        exact Subgroup.disjoint_def.mp h.isComplement.disjoint haN haA
    · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hX
      apply h.ne_bot_kernel
      exact (Subgroup.eq_bot_iff_forall N).mpr fun n hnN => by
        have hnAconj : n ∈ (MulAut.conj g • A : Subgroup G) := by
          rw [hX_top]
          exact Subgroup.mem_top n
        exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hnN hnAconj
  cover := by
    classical
    intro x
    by_cases hxN : x ∈ N
    · exact ⟨N, Finset.mem_insert_self _ _, hxN⟩
    · have hkernel := h.kernel_eq_notConjugateSet
      have hx_not : x ∉ notConjugateSet A := by
        intro hx
        have hxN' : x ∈ (N : Set G) := by
          rw [hkernel]
          exact hx
        exact hxN hxN'
      simp only [notConjugateSet, Set.mem_setOf_eq, not_forall, not_not] at hx_not
      obtain ⟨a, haA, ha_ne, hconj⟩ := hx_not
      rw [isConj_iff] at hconj
      obtain ⟨g, hgax⟩ := hconj
      refine ⟨MulAut.conj g • A, ?_, ?_⟩
      · exact Finset.mem_insert.mpr (Or.inr (mem_conjugatesFinset.mpr ⟨g, rfl⟩))
      · rw [← hgax]
        simpa using Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) A haA
  inf_eq_bot_of_ne := by
    classical
    intro X Y hX hY hXY
    rcases Finset.mem_insert.mp hX with hXN | hX
    · rcases Finset.mem_insert.mp hY with hYN | hY
      · exact False.elim (hXY (hXN.trans hYN.symm))
      · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hY
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        have hxN : x ∈ N := by
          rw [← hXN]
          exact hx.1
        exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hxN hx.2
    · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hX
      rcases Finset.mem_insert.mp hY with hYN | hY
      · rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        have hxN : x ∈ N := by
          rw [← hYN]
          exact hx.2
        exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hxN hx.1
      · obtain ⟨k, rfl⟩ := mem_conjugatesFinset.mp hY
        have hTI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥ := by
          intro g hg
          simpa [Subgroup.pointwise_smul_def] using h.trivialIntersection g hg
        exact TI_conjugate hTI g k hXY

/-- The Frobenius-group partition has cardinality `1 + |N|`, where `N` is the kernel. -/
theorem frobeniusGroup_parts_card [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) :
    (frobeniusGroup h).parts.card = Nat.card N + 1 := by
  classical
  have hTI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥ := by
    intro g hg
    simpa [Subgroup.pointwise_smul_def] using h.trivialIntersection g hg
  have hN_not_mem : N ∉ conjugatesFinset A := by
    intro hNmem
    obtain ⟨g, hNg⟩ := mem_conjugatesFinset.mp hNmem
    apply h.ne_bot_kernel
    exact (Subgroup.eq_bot_iff_forall N).mpr fun n hnN => by
      have hnAconj : n ∈ (MulAut.conj g • A : Subgroup G) := by
        rw [← hNg]
        exact hnN
      exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hnN hnAconj
  have hindex : A.index = Nat.card N := by
    have hn : Nat.card N = (N : Set G).ncard := by
      simpa using (Nat.card_coe_set_eq (N : Set G))
    rw [hn, h.isComplement.ncard_left]
  rw [frobeniusGroup, Finset.card_insert_of_notMem hN_not_mem,
    conjugatesFinset_card_eq_index h.ne_bot_complement hTI, hindex]

end SubgroupPartition

/-- **Isaacs Thm 6.9** (Frobenius-group branch, abelian target): a Frobenius actor cannot
itself be a Frobenius group.  The proof uses the §6B partition by the kernel and conjugates of
the complement, whose part count is `1 + |N|`. -/
theorem false_of_frobeniusAction_isFrobeniusGroup_on_abelian
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    {N C : Subgroup A} (hGroup : IsFrobeniusGroup A N C) :
    False := by
  let partn := SubgroupPartition.frobeniusGroup hGroup
  have hparts :
      partn.parts.card = Nat.card N + 1 :=
    SubgroupPartition.frobeniusGroup_parts_card hGroup
  have hdvd : Nat.card N ∣ Nat.card A := by
    have htop : Nat.card N ∣ Nat.card (⊤ : Subgroup A) :=
      Subgroup.card_dvd_of_le (show N ≤ (⊤ : Subgroup A) from le_top)
    simpa [Subgroup.card_top] using htop
  exact false_of_frobeniusAction_partition_of_card_eq_succ_and_dvd_actor_card
    hFrob partn hparts hdvd

/-- **Isaacs Thm 6.9** reduction step: if a solvable subgroup `B` of the actor acts
Frobeniusly on a finite nontrivial target, then the target contains a nontrivial abelian
`B`-invariant subgroup.  This is the reusable form of the textbook move in L3495: choose an
invariant Sylow subgroup `R` by Isaacs Thm 3.23, then pass to `Z(R)`. -/
theorem exists_actorSubgroup_invariant_nontrivial_abelian_subgroup_of_solvable
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    (B : Subgroup A) [Finite B] [IsSolvable B] :
    ∃ M : Subgroup U, Nontrivial M ∧ IsMulCommutative M ∧
      ∀ b : B, ∀ m ∈ M, (b : A) • m ∈ M := by
  classical
  let φ : B →* MulAut U := MulDistribMulAction.toMulAut B U
  have hFrobB : IsFrobeniusAction B U := IsFrobeniusAction.actorSubgroup hFrob B
  have hCop : Nat.Coprime (Nat.card B) (Nat.card U) := by
    haveI : Fintype B := Fintype.ofFinite B
    haveI : Fintype U := Fintype.ofFinite U
    simpa only [Nat.card_eq_fintype_card] using
      (IsFrobeniusAction.coprime_card (A := B) (N := U) hFrobB).symm
  have hU_gt_one : 1 < Nat.card U :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hU_gt_one.ne'
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR_inv⟩ :=
    OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (G := U) (A := B) (φ := φ)
      hCop (Or.inl (inferInstance : IsSolvable B)) p
  let M : Subgroup U := (Subgroup.center R).map (R : Subgroup U).subtype
  have hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M := by
    simpa [M] using
      (OddOrder.Isaacs.Ch03.IsAInvariant.map_subtype_of_characteristic
        (φ := φ) hR_inv (K := Subgroup.center R))
  have hR_ne_bot : (R : Subgroup U) ≠ ⊥ := R.ne_bot_of_dvd_card hp_dvd
  haveI hR_nontrivial : Nontrivial R :=
    (Subgroup.nontrivial_iff_ne_bot (R : Subgroup U)).mpr hR_ne_bot
  haveI hCenter_nontrivial : Nontrivial (Subgroup.center R) :=
    R.isPGroup'.center_nontrivial
  have hM_ne_bot : M ≠ ⊥ := by
    dsimp [M]
    rw [Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.center R) (R : Subgroup U).subtype_injective]
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center R)).mp hCenter_nontrivial
  refine ⟨M, (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot, ?_, ?_⟩
  · dsimp [M]
    infer_instance
  · intro b m hm
    simpa [φ] using hM_inv.smul_mem b hm

/-- **Isaacs Thm 6.9** reduction hook: if a subgroup `B` of the Frobenius actor is itself a
Frobenius group and the target contains a nontrivial `B`-invariant abelian subgroup, then the
Frobenius action is impossible.  The remaining textbook step is to obtain such a subgroup as
`Z(R)` from an invariant Sylow subgroup `R` via Isaacs Thm 3.23. -/
theorem false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup_on_invariant_abelian_subgroup
    {A U : Type*} [Group A] [Group U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {N C : Subgroup B} (hGroup : IsFrobeniusGroup B N C)
    (M : Subgroup U) [Finite M] [Nontrivial M] [IsMulCommutative M]
    (hM : ∀ b : B, ∀ m ∈ M, (b : A) • m ∈ M) :
    False := by
  letI : CommGroup M := inferInstance
  letI : MulDistribMulAction B M := by
    letI : SMul B M := ⟨fun b m => ⟨(b : A) • (m : U), hM b m m.2⟩⟩
    exact Subtype.coe_injective.mulDistribMulAction M.subtype (fun _ _ => rfl)
  have hFrobM : IsFrobeniusAction B M := by
    intro b hb m hm hfix
    have hbA : (b : A) ≠ 1 := fun hbA => hb (Subtype.ext hbA)
    have hmU : (m : U) ≠ 1 := fun hmU => hm (Subtype.ext hmU)
    exact hFrob (b : A) hbA (m : U) hmU (Subtype.ext_iff.mp hfix)
  exact false_of_frobeniusAction_isFrobeniusGroup_on_abelian hFrobM hGroup

/-- **Isaacs Thm 6.9** (solvable Frobenius-group branch): a Frobenius actor cannot contain a
solvable Frobenius group.  This is the full reduction in L3495: choose an invariant Sylow
subgroup `R` of the target by Isaacs Thm 3.23, pass to the nontrivial invariant abelian subgroup
`Z(R)`, and apply the abelian-target Frobenius-group contradiction. -/
theorem false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    (B : Subgroup A) [Finite B] [IsSolvable B]
    {N C : Subgroup B} (hGroup : IsFrobeniusGroup B N C) :
    False := by
  obtain ⟨M, hM_nontrivial, hM_comm, hM_inv⟩ :=
    exists_actorSubgroup_invariant_nontrivial_abelian_subgroup_of_solvable hFrob B
  haveI : Nontrivial M := hM_nontrivial
  haveI : IsMulCommutative M := hM_comm
  exact
    false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup_on_invariant_abelian_subgroup
      hFrob B hGroup M hM_inv

/-- **Isaacs Thm 6.9** reduction hook for the elementary-abelian branch: if a subgroup `B` of
the Frobenius actor is elementary abelian of order `p^2` and the target contains a nontrivial
`B`-invariant abelian subgroup, then the action is impossible. -/
theorem false_of_invariant_abelian_target_actorSubgroup_isElementaryAbelian_card_prime_sq
    {A U : Type*} [Group A] [Group U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p B) (hCard : Nat.card B = p ^ 2)
    (M : Subgroup U) [Finite M] [Nontrivial M] [IsMulCommutative M]
    (hM : ∀ b : B, ∀ m ∈ M, (b : A) • m ∈ M) :
    False := by
  letI : CommGroup M := inferInstance
  letI : MulDistribMulAction B M := by
    letI : SMul B M := ⟨fun b m => ⟨(b : A) • (m : U), hM b m m.2⟩⟩
    exact Subtype.coe_injective.mulDistribMulAction M.subtype (fun _ _ => rfl)
  have hFrobM : IsFrobeniusAction B M := by
    intro b hb m hm hfix
    have hbA : (b : A) ≠ 1 := fun hbA => hb (Subtype.ext hbA)
    have hmU : (m : U) ≠ 1 := fun hmU => hm (Subtype.ext hmU)
    exact hFrob (b : A) hbA (m : U) hmU (Subtype.ext_iff.mp hfix)
  exact false_of_frobeniusAction_isElementaryAbelian_card_prime_sq hFrobM hp hElem hCard

/-- **Isaacs Thm 6.9** (elementary-abelian branch, finite target): a Frobenius actor cannot
contain an elementary abelian subgroup of order `p^2`.  The abelian-target partition argument is
applied after the invariant-Sylow-center reduction. -/
theorem false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p B) (hCard : Nat.card B = p ^ 2) :
    False := by
  haveI : IsMulCommutative B := ⟨⟨fun x y => hElem.comm x y⟩⟩
  letI : CommGroup B := inferInstance
  haveI : IsSolvable B := inferInstance
  obtain ⟨M, hM_nontrivial, hM_comm, hM_inv⟩ :=
    exists_actorSubgroup_invariant_nontrivial_abelian_subgroup_of_solvable hFrob B
  haveI : Nontrivial M := hM_nontrivial
  haveI : IsMulCommutative M := hM_comm
  exact
    false_of_invariant_abelian_target_actorSubgroup_isElementaryAbelian_card_prime_sq
      hFrob B hp hElem hCard M hM_inv

/-- **Isaacs Thm 6.9** (elementary-abelian branch, large order): a Frobenius actor cannot
contain an elementary abelian `p`-subgroup whose order is at least `p^2`.  This packages the
textbook reduction "replace by a subgroup so that `e = 2`". -/
theorem false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_ge_prime_sq
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p B)
    (hCard : p ^ 2 ≤ Nat.card B) :
    False := by
  obtain ⟨E, hE_elem, hE_card⟩ :=
    hElem.exists_subgroup_card_prime_sq hp hCard
  exact
    false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
      (A := B) (U := U) (IsFrobeniusAction.actorSubgroup hFrob B)
      E hp hE_elem hE_card

/-- **Isaacs Thm 6.9** (`p = q` branch for subgroups of order `pq`): a Frobenius actor cannot
contain a noncyclic subgroup of order `p^2`; hence such a subgroup must be cyclic. -/
theorem false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_prime_sq
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime) (hCard : Nat.card B = p ^ 2)
    (hNotCyclic : ¬ IsCyclic B) :
    False := by
  exact
    false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
      hFrob B hp
      (OddOrder.GroupTheory.IsElementaryAbelian.of_card_prime_sq_of_not_isCyclic
        hp hCard hNotCyclic)
      hCard

private lemma orderOf_eq_prime_of_mem_subgroup_card_prime
    {G : Type*} [Group G] {H : Subgroup G} [Finite H] {p : ℕ}
    (hp : p.Prime) (hH_card : Nat.card H = p)
    {x : G} (hxH : x ∈ H) (hx : x ≠ 1) :
    orderOf x = p := by
  let xH : H := ⟨x, hxH⟩
  have hxH_ne : xH ≠ 1 := fun hxH_one => hx (Subtype.ext_iff.mp hxH_one)
  have h_dvd : orderOf xH ∣ p := by
    simpa [hH_card] using orderOf_dvd_natCard xH
  have h_order : orderOf xH = p := by
    rcases (Nat.dvd_prime hp).mp h_dvd with h_one | h_prime
    · exact False.elim (hxH_ne (orderOf_eq_one_iff.mp h_one))
    · exact h_prime
  exact (Subgroup.orderOf_coe xH).trans h_order

/-- **Isaacs Thm 6.9** (`p > q` branch for subgroups of order `pq`): a Frobenius actor cannot
contain a noncyclic subgroup of order `p*q` with `q < p`.  Such a subgroup would be a solvable
Frobenius group: its Sylow `p`-subgroup is normal, a Sylow `q`-subgroup is a complement, and any
fixed nonidentity pair would generate the whole group cyclically. -/
theorem false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hqp : q < p) (hCard : Nat.card B = p * q)
    (hNotCyclic : ¬ IsCyclic B) :
    False := by
  classical
  have hpq_ne : p ≠ q := fun hpq => (Nat.lt_irrefl q (hpq ▸ hqp))
  have hcop_qp : Nat.Coprime q p := (Nat.coprime_primes hq.out hp.out).mpr hpq_ne.symm
  have hcop_pq : Nat.Coprime p q := hcop_qp.symm
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := B)
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := B)
  have hCard' : Nat.card B = q * p := by rw [hCard, mul_comm]
  have hfact_p : (Nat.card B).factorization p = 1 := by
    rw [hCard, Nat.factorization_mul_apply_of_coprime hcop_pq,
        hp.out.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd
          (fun hd => hpq_ne ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hd))]
  have hfact_q : (Nat.card B).factorization q = 1 := by
    rw [hCard', Nat.factorization_mul_apply_of_coprime hcop_qp,
        hq.out.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd
          (fun hd => hpq_ne.symm ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hd))]
  have hP_card : Nat.card (P : Subgroup B) = p := by
    rw [P.card_eq_multiplicity, hfact_p, pow_one]
  have hQ_card : Nat.card (Q : Subgroup B) = q := by
    rw [Q.card_eq_multiplicity, hfact_q, pow_one]
  have hP_normal : (P : Subgroup B).Normal :=
    OddOrder.Isaacs.Ch01.sylow_normal_of_card_eq_mul_prime_lt
      (G := B) hqp hCard P
  have h_disjoint : Disjoint (P : Subgroup B) (Q : Subgroup B) :=
    IsPGroup.disjoint_of_ne p q hpq_ne _ _ P.isPGroup' Q.isPGroup'
  have h_compl : Subgroup.IsComplement' (P : Subgroup B) (Q : Subgroup B) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint
      (by rw [hP_card, hQ_card, hCard]) h_disjoint
  have hP_ne_bot : (P : Subgroup B) ≠ ⊥ := by
    intro hbot
    have hp_eq_one : p = 1 := by
      rw [← hP_card, hbot]
      simp
    exact hp.out.ne_one hp_eq_one
  have hQ_ne_bot : (Q : Subgroup B) ≠ ⊥ := by
    intro hbot
    have hq_eq_one : q = 1 := by
      rw [← hQ_card, hbot]
      simp
    exact hq.out.ne_one hq_eq_one
  letI : (P : Subgroup B).Normal := hP_normal
  have hFrobGroup : IsFrobeniusGroup B (P : Subgroup B) (Q : Subgroup B) := by
    refine
      { isNormal := hP_normal
        isComplement := h_compl
        ne_bot_kernel := hP_ne_bot
        ne_bot_complement := hQ_ne_bot
        conj_frobenius := ?_ }
    intro a haQ ha_ne n hnP hn_ne h_conj
    have h_an : a * n = n * a := by
      have := congrArg (fun x => x * a) h_conj
      simpa [mul_assoc] using this
    have hcomm : Commute n a := h_an.symm
    have hn_order : orderOf n = p :=
      orderOf_eq_prime_of_mem_subgroup_card_prime hp.out hP_card hnP hn_ne
    have ha_order : orderOf a = q :=
      orderOf_eq_prime_of_mem_subgroup_card_prime hq.out hQ_card haQ ha_ne
    have hcop_orders : Nat.Coprime (orderOf n) (orderOf a) := by
      rw [hn_order, ha_order]
      exact hcop_pq
    have horder : orderOf (n * a) = p * q := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders,
        hn_order, ha_order]
    exact hNotCyclic (isCyclic_of_orderOf_eq_card (n * a) (by rw [horder, hCard]))
  haveI : IsSolvable B := by
    haveI : IsCyclic (P : Subgroup B) := isCyclic_of_prime_card hP_card
    have hP_index : (P : Subgroup B).index = q := by
      have hmul := (P : Subgroup B).card_mul_index
      rw [hP_card, hCard] at hmul
      exact Nat.eq_of_mul_eq_mul_left hp.out.pos hmul
    have hquot_card : Nat.card (B ⧸ (P : Subgroup B)) = q := by
      rw [← Subgroup.index_eq_card, hP_index]
    haveI : IsCyclic (B ⧸ (P : Subgroup B)) := isCyclic_of_prime_card hquot_card
    letI : CommGroup (P : Subgroup B) := IsCyclic.commGroup
    letI : CommGroup (B ⧸ (P : Subgroup B)) := IsCyclic.commGroup
    exact solvable_of_ker_le_range (P : Subgroup B).subtype
      (QuotientGroup.mk' (P : Subgroup B)) (by
        rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact
    false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup
      hFrob B hFrobGroup

/-- **Isaacs Thm 6.9** (order `pq` branch): a Frobenius actor cannot contain a noncyclic
subgroup of order `p*q`, for primes `p` and `q` that may be equal. -/
theorem false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hCard : Nat.card B = p * q) (hNotCyclic : ¬ IsCyclic B) :
    False := by
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · have hCard' : Nat.card B = q * p := by rw [hCard, mul_comm]
    exact
      false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
        (p := q) (q := p) hFrob B hpq hCard' hNotCyclic
  · subst q
    exact
      false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_prime_sq
        hFrob B hp.out (by simpa [pow_two] using hCard) hNotCyclic
  · exact
      false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
        (p := p) (q := q) hFrob B hqp hCard hNotCyclic

/-- **Isaacs Cor 6.10**: if `P` is a Sylow `p`-subgroup of a finite Frobenius
complement, then `P` contains at most one subgroup of order `p`. -/
theorem subgroups_card_prime_unique_of_frobeniusAction_sylow
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {p : ℕ} [hp : Fact p.Prime] (P : Sylow p A) :
    ∀ K L : Subgroup P, Nat.card K = p → Nat.card L = p → K = L := by
  intro K L hK_card hL_card
  by_contra hKL_ne
  obtain ⟨E, hE_elem, hE_card⟩ :=
    P.isPGroup'.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne
      hK_card hL_card hKL_ne
  exact
    false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
      (A := P) (U := U) (IsFrobeniusAction.actorSubgroup hFrob (P : Subgroup A))
      E hp.out hE_elem hE_card

/-- **Isaacs Thm 6.11 (abelian branch, in Frobenius-complement form)**: a commutative
Sylow `p`-subgroup of a finite Frobenius complement is cyclic.  Corollary 6.10 supplies the
unique order-`p` subgroup hypothesis, and the finite abelian p-group structure theorem turns it
into cyclicity. -/
theorem sylow_isCyclic_of_frobeniusAction_of_isMulCommutative
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {p : ℕ} [Fact p.Prime]
    (P : Sylow p A) [IsMulCommutative P] :
    IsCyclic P :=
  P.isPGroup'.isCyclic_of_subgroups_card_prime_unique
    (subgroups_card_prime_unique_of_frobeniusAction_sylow hFrob P)

/-- **Isaacs Cor 6.17 observation (abelian complement branch)**: a finite abelian Frobenius
complement is cyclic.  This is the part needed later in Theorem 6.21 to rule out a noncyclic
abelian group acting Frobeniusly. -/
theorem isCyclic_of_frobeniusAction_of_isMulCommutative
    {A U : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group U] [Finite U] [Nontrivial U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) :
    IsCyclic A := by
  exact isCyclic_of_sylow_isCyclic (A := A) fun p hp P => by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsMulCommutative P := ⟨⟨fun x y => by
      ext
      exact mul_comm (x : A) (y : A)⟩⟩
    exact sylow_isCyclic_of_frobeniusAction_of_isMulCommutative hFrob P

/-- The contradiction step in Isaacs Thm 6.21 after the induction hypothesis has shown that
every proper `A`-invariant subgroup of `N` lies in `K = ⟨C_N(a) | a ≠ 1⟩`. -/
theorem nontrivialActionFixedByClosure_eq_top_of_proper_invariant_le
    {A N : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N)) (hNotCyclic : ¬ IsCyclic A)
    (hproper : ∀ P : Subgroup N,
      (∀ a : A, ∀ n ∈ P, a • n ∈ P) → P ≠ ⊤ →
        P ≤ nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N)) :
    nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤ := by
  classical
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let K : Subgroup N := nontrivialActionFixedByClosure φ
  change K = ⊤
  by_contra hK_ne_top
  have hidx_gt : 1 < K.index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  obtain ⟨p, hp_prime, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt hidx_gt)
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hSolvA : IsSolvable A := isSolvable_of_comm fun a b : A => mul_comm a b
  obtain ⟨P, _hP_inv, hP_top⟩ :=
    exists_aInvariant_sylow_eq_top_of_prime_dvd_index_of_proper_invariant_le
      (A := A) (N := N) (K := K) (p := p) hCop (Or.inl hSolvA) hp_dvd
      (by simpa [K, φ] using hproper)
  have hN_pgroup : IsPGroup p N := by
    have hP_pgroup : IsPGroup p (P : Subgroup N) := P.isPGroup'
    rw [hP_top] at hP_pgroup
    exact hP_pgroup.of_equiv Subgroup.topEquiv
  have hN_solv : IsSolvable N := by
    haveI : Group.IsNilpotent N := hN_pgroup.isNilpotent
    exact IsNilpotent.to_isSolvable
  letI : IsSolvable N := hN_solv
  have hcomm : _root_.commutator N ≤ K :=
    commutator_le_of_proper_invariant_le_of_isSolvable (A := A) (N := N) (K := K)
      (by simpa [K, φ] using hproper)
  letI : K.Normal := normal_of_commutator_le hcomm
  have hK_inv : ∀ a : A, ∀ n ∈ K, a • n ∈ K := by
    simpa [K, φ] using nontrivialActionFixedByClosure_invariant_of_commutative φ
  have hCopAK : Nat.Coprime (Nat.card A) (Nat.card K) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card K)
  have hfixed : ∀ a : A, a ≠ 1 → actionFixedBy φ a ≤ K := by
    intro a ha
    exact actionFixedBy_le_nontrivialActionFixedByClosure (φ := φ) ha
  letI : MulDistribMulAction A (N ⧸ K) :=
    IsFrobeniusAction.invariantQuotientMulDistribMulAction K hK_inv
  haveI : Nontrivial (N ⧸ K) := Subgroup.nontrivial_quotient_of_ne_top hK_ne_top
  have hFrobQuot : IsFrobeniusAction A (N ⧸ K) :=
    quotient_isFrobeniusAction_of_fixedBy_le (A := A) (N := N) (M := K)
      hK_inv hCopAK hfixed
  exact hNotCyclic (isCyclic_of_frobeniusAction_of_isMulCommutative hFrobQuot)

universe uA uN

/-- **Isaacs Thm 6.21** (nontrivial case): if a finite abelian noncyclic group `A` acts
coprimely on a finite nontrivial group `N`, then the subgroups `C_N(a)` for `a ≠ 1`
generate `N`. -/
theorem nontrivialActionFixedByClosure_eq_top_of_not_isCyclic_of_nontrivial
    {A : Type uA} {N : Type uN} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N)) (hNotCyclic : ¬ IsCyclic A) :
    nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤ := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (N : Type uN) [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N],
      Nat.card N = n →
      Nat.Coprime (Nat.card A) (Nat.card N) →
      nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤
  have hmain : motive (Nat.card N) := by
    refine Nat.strong_induction_on (Nat.card N) ?_
    intro n ih N _ _ _ _ hcard hCopN
    refine nontrivialActionFixedByClosure_eq_top_of_proper_invariant_le
      (A := A) (N := N) hCopN hNotCyclic ?_
    intro M hM hM_ne_top
    by_cases hM_nontriv : Nontrivial M
    · letI : Nontrivial M := hM_nontriv
      letI : MulDistribMulAction A M :=
        IsFrobeniusAction.invariantSubgroupMulDistribMulAction M hM
      have hM_card_lt_N : Nat.card M < Nat.card N := by
        have h_dvd : Nat.card M ∣ Nat.card N := Subgroup.card_subgroup_dvd_card M
        have h_le : Nat.card M ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos h_dvd
        have h_ne : Nat.card M ≠ Nat.card N := fun heq =>
          hM_ne_top (Subgroup.eq_top_of_card_eq M heq)
        exact Nat.lt_of_le_of_ne h_le h_ne
      have hM_card_lt : Nat.card M < n := by
        simpa [hcard] using hM_card_lt_N
      have hCopM : Nat.Coprime (Nat.card A) (Nat.card M) :=
        hCopN.coprime_dvd_right (Subgroup.card_subgroup_dvd_card M)
      have hMtop :
          nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A M) = ⊤ :=
        (ih (Nat.card M) hM_card_lt) M rfl hCopM
      exact
        subgroup_le_nontrivialActionFixedByClosure_of_closure_eq_top
          (M := M) (by intro a m; rfl) hMtop
    · haveI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM_nontriv
      intro n hn
      have hn_one : n = 1 := by
        have hsub : (⟨n, hn⟩ : M) = 1 := Subsingleton.elim _ _
        exact congrArg Subtype.val hsub
      rw [hn_one]
      exact Subgroup.one_mem _
  exact hmain N rfl hCop

/-- **Isaacs Thm 6.21**: if a finite abelian noncyclic group `A` acts coprimely on a finite
group `N`, then the subgroups `C_N(a)` for `a ≠ 1` generate `N`. -/
theorem nontrivialActionFixedByClosure_eq_top_of_not_isCyclic
    {A : Type uA} {N : Type uN} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [MulDistribMulAction A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N)) (hNotCyclic : ¬ IsCyclic A) :
    nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤ := by
  by_cases hN_nontriv : Nontrivial N
  · letI : Nontrivial N := hN_nontriv
    exact nontrivialActionFixedByClosure_eq_top_of_not_isCyclic_of_nontrivial
      hCop hNotCyclic
  · haveI : Subsingleton N := not_nontrivial_iff_subsingleton.mp hN_nontriv
    rw [eq_top_iff]
    intro n _hn
    have hn_one : n = 1 := Subsingleton.elim n 1
    rw [hn_one]
    exact Subgroup.one_mem _

/-- **Isaacs Lem 6.20**: if a finite abelian group acts faithfully and coprimely on `N`,
and acts trivially on every proper invariant subgroup of `N`, then it is cyclic. -/
theorem isCyclic_of_faithful_trivial_on_proper_invariant
    {A : Type uA} {N : Type uN} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [MulDistribMulAction A N] [FaithfulSMul A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hproper :
      ∀ M : Subgroup N,
        (∀ a : A, ∀ n ∈ M, a • n ∈ M) →
        M ≠ ⊤ →
        ∀ a : A, ∀ n ∈ M, a • n = n) :
    IsCyclic A := by
  classical
  by_contra hNotCyclic
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let fixedTop : Subgroup N := actionFixedPoints φ ⊤
  have hKtop : nontrivialActionFixedByClosure φ = ⊤ :=
    nontrivialActionFixedByClosure_eq_top_of_not_isCyclic hCop hNotCyclic
  have hK_le_fixedTop : nontrivialActionFixedByClosure φ ≤ fixedTop := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro a ha
    let M : Subgroup N := actionFixedBy φ a
    have hM_inv : ∀ b : A, ∀ n ∈ M, b • n ∈ M := by
      intro b n hn
      have hmem :
          (φ b) n ∈ actionFixedBy φ a :=
        actionFixedBy_invariant_of_commute (φ := φ) (a := a) (b := b)
          (mul_comm a b) n hn
      simpa [φ, M] using hmem
    have hM_ne_top : M ≠ ⊤ := by
      intro hMtop
      have ha_one : a = 1 := by
        exact eq_of_smul_eq_smul fun n : N => by
          have hn : n ∈ M := by
            rw [hMtop]
            exact Subgroup.mem_top n
          change (φ a) n = n at hn
          simpa [φ] using hn
      exact ha ha_one
    have hM_trivial := hproper M hM_inv hM_ne_top
    intro n hn
    change ∀ b : (⊤ : Subgroup A), (φ b) n = n
    intro b
    have hfix := hM_trivial (b : A) n hn
    simpa [φ] using hfix
  have hfixedTop_eq_top : fixedTop = ⊤ := by
    rw [eq_top_iff]
    intro n _hn
    exact hK_le_fixedTop (by
      rw [hKtop]
      exact Subgroup.mem_top n)
  have hA_subsingleton : Subsingleton A := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := by
      exact eq_of_smul_eq_smul fun n : N => by
        have hn : n ∈ fixedTop := by
          rw [hfixedTop_eq_top]
          exact Subgroup.mem_top n
        have hfix := hn ⟨a, Subgroup.mem_top a⟩
        change (φ a) n = n at hfix
        simpa [φ] using hfix
    have hb : b = 1 := by
      exact eq_of_smul_eq_smul fun n : N => by
        have hn : n ∈ fixedTop := by
          rw [hfixedTop_eq_top]
          exact Subgroup.mem_top n
        have hfix := hn ⟨b, Subgroup.mem_top b⟩
        change (φ b) n = n at hfix
        simpa [φ] using hfix
    exact ha.trans hb.symm
  exact hNotCyclic (@isCyclic_of_subsingleton A _ hA_subsingleton)

end

section /- 6B: Lemma 6.13 + Cor 6.14 — D / Q / SD recognition (pp. 192-193) -/

open OddOrder.GroupTheory

/-! ### Isaacs Lemma 6.13 + Cor 6.14: D / Q / SD recognition

mmd L3523-3531 (Lem 6.13) + L3533 (Cor 6.14).

Lem 6.13 takes a finite 2-group `P` with a cyclic subgroup `C = ⟨c⟩` of index 2 and an element
`a ∈ P − C`, and classifies `P` according to the action of `a` on `c`:

- If `a * c * a⁻¹ = c⁻¹`, then `P ≃* DihedralGroup (orderOf c)` (when `a² = 1`) or
  `P ≃* QuaternionGroup (orderOf c / 2)` (when `a² ≠ 1`, in which case `a² = z`, the unique
  involution in `C`).
- If `a * c * a⁻¹ = z * c⁻¹` where `z` is the unique involution in `C`, then
  `P ≃* SemiDihedralGroup k` with `2^k = orderOf c`.

Cor 6.14 specializes to `|P| = 8` nonabelian and concludes `P ≃* D_8` or `P ≃* Q_8`
(i.e., `DihedralGroup 4` or `QuaternionGroup 2` in mathlib indexing).

The iso constructions follow mathlib's `quaternionGroupZeroEquivDihedralGroupZero` pattern
(Quaternion.lean L152): element-by-element mapping using the partition `P = C ⊔ aC`, then
`map_mul'` verified by case analysis on the defining relations. -/

/-! ### Dihedral / quaternion recognition helpers -/

/-- A nontrivial subgroup of a finite `2`-group contains an involution.

This is the internal-involution half of the Isaacs 6.12 → 6.11 reduction: once a
dihedral or semidihedral alternative supplies an involution outside the cyclic index-two
subgroup, this lemma supplies the nontrivial involution inside that subgroup. -/
theorem exists_involution_mem_of_nontrivial_two_subgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} (hC_ne : C ≠ ⊥) :
    ∃ z : P, z ∈ C ∧ z ^ 2 = 1 ∧ z ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC_two : IsPGroup 2 C := hP.to_subgroup C
  have hC_card_ne_one : Nat.card C ≠ 1 := by
    intro hC_card
    exact hC_ne (Subgroup.eq_bot_of_card_eq C hC_card)
  have hC_card_gt_one : 1 < Nat.card C := by
    have hC_pos : 0 < Nat.card C := Nat.card_pos
    omega
  haveI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp hC_card_gt_one
  obtain ⟨n, hn_pos, hC_card⟩ := hC_two.nontrivial_iff_card.mp inferInstance
  have h_two_dvd_card : 2 ∣ Nat.card C := by
    rw [hC_card]
    cases n with
    | zero => omega
    | succ n => exact ⟨2 ^ n, by rw [pow_succ']⟩
  obtain ⟨z, hz_order⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h_two_dvd_card
  refine ⟨(z : P), z.2, ?_, ?_⟩
  · have hz_sq : z ^ 2 = 1 := by
      rw [← hz_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hz_sq
  · intro hz_eq_one
    have hz_eq_one' : z = 1 := Subtype.ext hz_eq_one
    have : orderOf z = 1 := by rw [hz_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hz_order.symm.trans this)

/-- A finite commutative `2`-group with a unique nontrivial involution is cyclic.

This is the element-level version needed in Isaacs Thm 6.12: it adapts the textbook
“unique involution” hypothesis to the subgroup-level uniqueness used by the finite abelian
`p`-group structure bridge from Thm 6.11. -/
theorem isCyclic_of_comm_two_group_unique_involution
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcomm : ∀ x y : P, x * y = y * x)
    (hUnique : ∀ x y : P, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y) :
    IsCyclic P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsMulCommutative P := ⟨⟨hcomm⟩⟩
  refine hP.isCyclic_of_subgroups_card_prime_unique ?_
  intro K L hK_card hL_card
  have hK_two_dvd : 2 ∣ Nat.card K := by rw [hK_card]
  have hL_two_dvd : 2 ∣ Nat.card L := by rw [hL_card]
  obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hK_two_dvd
  obtain ⟨y, hy_order⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 hL_two_dvd
  have hx_sq : (x : P) ^ 2 = 1 := by
    have hx_sq_sub : x ^ 2 = 1 := by
      rw [← hx_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hx_sq_sub
  have hy_sq : (y : P) ^ 2 = 1 := by
    have hy_sq_sub : y ^ 2 = 1 := by
      rw [← hy_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hy_sq_sub
  have hx_ne : (x : P) ≠ 1 := by
    intro hx_eq_one
    have hx_eq_one' : x = 1 := Subtype.ext hx_eq_one
    have : orderOf x = 1 := by rw [hx_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hx_order.symm.trans this)
  have hy_ne : (y : P) ≠ 1 := by
    intro hy_eq_one
    have hy_eq_one' : y = 1 := Subtype.ext hy_eq_one
    have : orderOf y = 1 := by rw [hy_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hy_order.symm.trans this)
  have hxy : (x : P) = (y : P) :=
    hUnique (x : P) (y : P) hx_ne hx_sq hy_ne hy_sq
  have hx_order_P : orderOf (x : P) = 2 := orderOf_eq_prime (p := 2) hx_sq hx_ne
  have hy_order_P : orderOf (y : P) = 2 := orderOf_eq_prime (p := 2) hy_sq hy_ne
  have hK_zpowers : Subgroup.zpowers (x : P) = K := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
    rw [hK_card, Nat.card_zpowers, hx_order_P]
  have hL_zpowers : Subgroup.zpowers (y : P) = L := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2)
    rw [hL_card, Nat.card_zpowers, hy_order_P]
  rw [← hK_zpowers, ← hL_zpowers, hxy]

/-- If every nontrivial involution in a commutative actor inverts a fixed element whose square
is nontrivial, then that actor has a unique nontrivial involution.

This is the action-theoretic core of the Isaacs 6.12 quotient argument: two distinct
involutions would have a product that fixes the element, while the hypothesis says that the
product must invert it. -/
theorem unique_involution_of_comm_of_involutions_invert_element
    {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    (hcomm : ∀ a b : A, a * b = b * a) {n : N} (hn_sq_ne : n ^ 2 ≠ 1)
    (hinv : ∀ a : A, a ≠ 1 → a ^ 2 = 1 → a • n = n⁻¹) :
    ∀ a b : A, a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 → a = b := by
  intro a b ha_ne ha_sq hb_ne hb_sq
  by_contra hab
  have hb_inv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hb_sq]
  have hab_prod_ne : a * b ≠ 1 := by
    intro hprod
    apply hab
    calc a = a * 1 := by rw [mul_one]
      _ = a * (b * b⁻¹) := by rw [mul_inv_cancel]
      _ = (a * b) * b⁻¹ := by group
      _ = b := by rw [hprod, one_mul, hb_inv]
  have hab_prod_sq : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * b * (a * b) := by rw [pow_two]
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm b a]
      _ = a ^ 2 * b ^ 2 := by
        simp [pow_two, mul_assoc]
      _ = 1 := by rw [ha_sq, hb_sq, one_mul]
  have ha_inv : a • n = n⁻¹ := hinv a ha_ne ha_sq
  have hb_inv_n : b • n = n⁻¹ := hinv b hb_ne hb_sq
  have hab_prod_inv : (a * b) • n = n⁻¹ :=
    hinv (a * b) hab_prod_ne hab_prod_sq
  have hab_prod_fix : (a * b) • n = n := by
    rw [mul_smul, hb_inv_n, smul_inv', ha_inv, inv_inv]
  have hn_eq_inv : n = n⁻¹ := hab_prod_fix.symm.trans hab_prod_inv
  apply hn_sq_ne
  rw [pow_two]
  nth_rewrite 1 [hn_eq_inv]
  exact inv_mul_cancel n

/-- A finite commutative `2`-group acting with all involutions inverting a fixed element of
square not equal to `1` is cyclic.

This packages the two Isaacs 6.12 quotient steps: inversion of `c²` gives uniqueness of the
quotient involution, and a commutative finite `2`-group with a unique involution is cyclic. -/
theorem isCyclic_of_comm_two_group_involutions_invert_element
    {A N : Type*} [Group A] [Finite A] [Group N] [MulDistribMulAction A N]
    (hA : IsPGroup 2 A) (hcomm : ∀ a b : A, a * b = b * a)
    {n : N} (hn_sq_ne : n ^ 2 ≠ 1)
    (hinv : ∀ a : A, a ≠ 1 → a ^ 2 = 1 → a • n = n⁻¹) :
    IsCyclic A :=
  isCyclic_of_comm_two_group_unique_involution hA hcomm
    (unique_involution_of_comm_of_involutions_invert_element hcomm hn_sq_ne hinv)

/-- If a subgroup `C` contains a nontrivial involution `z` and there is another involution `a`
outside `C`, then the ambient group has two distinct subgroups of order `2`.

This is the small bridge used to eliminate the dihedral and semidihedral alternatives when
deducing Isaacs Thm 6.11 from Thm 6.12: those groups have an involution outside their cyclic
index-`2` subgroup, whereas generalized quaternion groups do not. -/
theorem exists_distinct_subgroups_card_two_of_external_involution
    {P : Type*} [Group P] [Finite P] {C : Subgroup P} {a z : P}
    (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1)
    (hz_mem : z ∈ C) (hz_sq : z ^ 2 = 1) (hz_ne : z ≠ 1) :
    ∃ K L : Subgroup P, Nat.card K = 2 ∧ Nat.card L = 2 ∧ K ≠ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha_ne : a ≠ 1 := by
    intro ha
    exact ha_notmem (ha ▸ C.one_mem)
  have ha_order : orderOf a = 2 := orderOf_eq_prime (p := 2) ha_sq ha_ne
  have hz_order : orderOf z = 2 := orderOf_eq_prime (p := 2) hz_sq hz_ne
  refine ⟨Subgroup.zpowers a, Subgroup.zpowers z, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, ha_order]
  · rw [Nat.card_zpowers, hz_order]
  · intro h_eq
    exact ha_notmem ((Subgroup.zpowers_le.mpr hz_mem) (by
      rw [← h_eq]
      exact Subgroup.mem_zpowers a))

/-- If a group has a unique subgroup of order `2`, then it cannot have a nontrivial involution
inside `C` and another involution outside `C`.

This is the contradiction form of the preceding bridge, used when deriving Isaacs Thm 6.11
from Thm 6.12: the dihedral and semidihedral alternatives supply such an outside involution. -/
theorem false_of_unique_subgroups_card_two_of_external_involution
    {P : Type*} [Group P] [Finite P] {C : Subgroup P} {a z : P}
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1)
    (hz_mem : z ∈ C) (hz_sq : z ^ 2 = 1) (hz_ne : z ≠ 1) :
    False := by
  obtain ⟨K, L, hK_card, hL_card, hKL_ne⟩ :=
    exists_distinct_subgroups_card_two_of_external_involution
      ha_notmem ha_sq hz_mem hz_sq hz_ne
  exact hKL_ne (hUnique K L hK_card hL_card)

/-- If a finite `2`-group has a unique subgroup of order `2`, then no nontrivial subgroup `C`
can have an involution outside it.

This is the packaged 6.12 → 6.11 exclusion used for the dihedral and semidihedral
alternatives: `C` supplies the internal involution, while the alternative supplies the external
one. -/
theorem false_of_unique_subgroups_card_two_of_external_involution_of_nontrivial_two_subgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P}
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (hC_ne : C ≠ ⊥) {a : P} (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1) :
    False := by
  obtain ⟨z, hz_mem, hz_sq, hz_ne⟩ :=
    exists_involution_mem_of_nontrivial_two_subgroup hP hC_ne
  exact false_of_unique_subgroups_card_two_of_external_involution
    hUnique ha_notmem ha_sq hz_mem hz_sq hz_ne

/-- Index-two form of the external-involution obstruction.

If `C` has index `2` in a finite `2`-group of order not equal to `2`, then `C` is nontrivial.
Thus any involution outside `C` contradicts uniqueness of the subgroup of order `2`.
This is the exact shape needed for the dihedral and semidihedral alternatives in the
Isaacs 6.12 → 6.11 reduction. -/
theorem false_of_unique_subgroups_card_two_of_external_involution_of_index_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P}
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (hC_index : C.index = 2) (hP_card_ne_two : Nat.card P ≠ 2)
    {a : P} (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1) :
    False := by
  have hC_ne : C ≠ ⊥ := by
    intro hC_bot
    apply hP_card_ne_two
    have hcard := C.index_mul_card
    rw [hC_index, hC_bot, Subgroup.card_bot] at hcard
    simpa using hcard.symm
  exact false_of_unique_subgroups_card_two_of_external_involution_of_nontrivial_two_subgroup
    hP hUnique hC_ne ha_notmem ha_sq

/-! ### The first enlargement step in Theorem 6.12 -/

/-- **Isaacs Thm 6.12 setup**: if `C` is a normal subgroup of a finite `p`-group `P` and
`C < C_P(C)`, then there is a normal abelian subgroup `B` with `C < B ≤ C_P(C)` and
`|B : C| = p`.

This is the formal version of the first paragraph of the proof of Thm 6.12.  Ch.1 Lemma 1.23
supplies the normal intermediate subgroup of prime relative index; since `B ≤ C_P(C)`,
`C` is central in `B`, and the prime quotient `B/C` is cyclic, so `B` is abelian by
`commutative_of_cyclic_center_quotient`. -/
theorem exists_normal_isMulCommutative_relIndex_prime_of_lt_centralizer
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal]
    (hC_lt_cent : C < Subgroup.centralizer (C : Set P)) :
    ∃ B : Subgroup P, B.Normal ∧ C < B ∧ B ≤ Subgroup.centralizer (C : Set P) ∧
      C.relIndex B = p ∧ IsMulCommutative B := by
  haveI hCent_normal : (Subgroup.centralizer (C : Set P)).Normal :=
    Subgroup.normal_centralizer
  obtain ⟨B, hB_normal, hC_lt_B, hB_le_cent, hC_rel⟩ :=
    OddOrder.Isaacs.Ch01.IsPGroup.exists_normal_index_eq_prime
      hP (N := C) (M := Subgroup.centralizer (C : Set P)) hC_lt_cent
  haveI hC_sub_normal : (C.subgroupOf B).Normal := inferInstance
  have hC_sub_le_center : C.subgroupOf B ≤ Subgroup.center B := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have hb_cent : ((b : B) : P) ∈ Subgroup.centralizer (C : Set P) :=
      hB_le_cent b.2
    have hc_mem : ((c : B) : P) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hc
    have h_comm :
        ((c : B) : P) * ((b : B) : P) = ((b : B) : P) * ((c : B) : P) :=
      (Subgroup.mem_centralizer_iff.mp hb_cent) ((c : B) : P) hc_mem
    exact h_comm.symm
  have h_card_quot : Nat.card (B ⧸ C.subgroupOf B) = p := by
    rw [← Subgroup.index_eq_card]
    simpa [Subgroup.relIndex] using hC_rel
  have h_cyclic_quot : IsCyclic (B ⧸ C.subgroupOf B) :=
    isCyclic_of_prime_card h_card_quot
  have hB_comm : ∀ x y : B, x * y = y * x := by
    haveI : IsCyclic (B ⧸ C.subgroupOf B) := h_cyclic_quot
    exact commutative_of_cyclic_center_quotient
      (QuotientGroup.mk' (C.subgroupOf B)) (by
        rw [QuotientGroup.ker_mk']
        exact hC_sub_le_center)
  exact ⟨B, hB_normal, hC_lt_B, hB_le_cent, hC_rel, ⟨⟨hB_comm⟩⟩⟩

/-- **Isaacs Thm 6.12 setup**: a maximal normal abelian subgroup `C` of a finite `p`-group
is self-centralizing.

The maximality hypothesis is stated in the form needed for the proof: no strictly larger
normal abelian subgroup contains `C`.  If `C < C_P(C)`, the preceding theorem produces such
a larger normal abelian subgroup, contradiction. -/
theorem centralizer_eq_of_maximal_normal_isMulCommutative
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal] (hC_comm : IsMulCommutative C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False) :
    Subgroup.centralizer (C : Set P) = C := by
  have hC_le_cent : C ≤ Subgroup.centralizer (C : Set P) := by
    haveI : IsMulCommutative C := hC_comm
    exact Subgroup.le_centralizer (H := C)
  have hcent_le_C : Subgroup.centralizer (C : Set P) ≤ C := by
    by_contra hnot
    have hne : C ≠ Subgroup.centralizer (C : Set P) := by
      intro h_eq
      exact hnot (le_of_eq h_eq.symm)
    have hlt : C < Subgroup.centralizer (C : Set P) := lt_of_le_of_ne hC_le_cent hne
    obtain ⟨B, hB_normal, hC_lt_B, _hB_le_cent, _hC_rel, hB_comm⟩ :=
      exists_normal_isMulCommutative_relIndex_prime_of_lt_centralizer hP hlt
    exact hC_max B hB_normal hB_comm hC_lt_B
  exact le_antisymm hcent_le_C hC_le_cent

/-- **Isaacs Thm 6.12 setup**: if `C` is cyclic and self-centralizing in `P`, then
`P/C` is abelian.

The conjugation homomorphism `P → Aut(C)` has kernel `C_P(C)`.  Under the self-centralizing
hypothesis this kernel is exactly `C`, so it induces an embedding `P/C ↪ Aut(C)`.  Since the
automorphism group of a cyclic group is abelian, the quotient `P/C` is abelian. -/
theorem quotient_commutative_of_isCyclic_of_self_centralizing
    {P : Type*} [Group P]
    {C : Subgroup P} [C.Normal] (hC_cyclic : IsCyclic C)
    (hCent : Subgroup.centralizer (C : Set P) = C) :
    ∀ x y : P ⧸ C, x * y = y * x := by
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  have hker : φ.ker = C := by
    ext g
    constructor
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      have hg_cent : g ∈ Subgroup.centralizer (C : Set P) := by
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        let cC : C := ⟨c, hc⟩
        have hfix : φ g cC = cC := by
          have h := congrArg (fun ψ : MulAut C => ψ cC) hg
          simpa using h
        have hconj : g * c * g⁻¹ = c := by
          have hval := congrArg Subtype.val hfix
          simpa [φ, cC] using hval
        have hgc : g * c = c * g := by
          calc g * c = (g * c * g⁻¹) * g := by simp [mul_assoc]
            _ = c * g := by rw [hconj]
        exact hgc.symm
      simpa [hCent] using hg_cent
    · intro hgC
      rw [MonoidHom.mem_ker]
      ext c
      have hg_cent : g ∈ Subgroup.centralizer (C : Set P) := by
        simpa [hCent] using hgC
      have hcomm : (c : P) * g = g * (c : P) :=
        (Subgroup.mem_centralizer_iff.mp hg_cent) (c : P) c.2
      calc ((φ g c : C) : P) = g * (c : P) * g⁻¹ := by rfl
        _ = ((c : P) * g) * g⁻¹ := by rw [← hcomm]
        _ = (c : P) := by simp [mul_assoc]
        _ = (((1 : MulAut C) c : C) : P) := by rfl
  let ψ : P ⧸ C →* MulAut C := QuotientGroup.lift C φ (by rw [hker])
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp [ψ]
    rw [QuotientGroup.ker_lift, hker]
    simp
  haveI : IsCyclic C := hC_cyclic
  let e := IsCyclic.mulAutMulEquiv C
  letI : CommGroup (MulAut C) := e.toMonoidHom.commGroupOfInjective e.injective
  letI : CommGroup (P ⧸ C) := ψ.commGroupOfInjective hψ_inj
  exact mul_comm

/-- **Isaacs Thm 6.12 setup**: a maximal normal cyclic subgroup `C` makes `P/C`
abelian.

This packages the first paragraph of the proof of Theorem 6.12: maximal normal abelian
subgroups self-centralize in a finite `p`-group, and a cyclic self-centralizing subgroup
forces the quotient to embed in the abelian automorphism group of `C`. -/
theorem quotient_commutative_of_maximal_normal_isCyclic
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal] (hC_cyclic : IsCyclic C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False) :
    ∀ x y : P ⧸ C, x * y = y * x := by
  have hC_comm : IsMulCommutative C := by
    haveI : IsCyclic C := hC_cyclic
    infer_instance
  have hCent : Subgroup.centralizer (C : Set P) = C :=
    centralizer_eq_of_maximal_normal_isMulCommutative hP hC_comm hC_max
  exact quotient_commutative_of_isCyclic_of_self_centralizing hC_cyclic hCent

/-- **Isaacs Thm 6.12 setup**: if `C ≤ T` and `P/C` is abelian, then `T ⊴ P`.

This is the quotient-correspondence step used after choosing `T/C ≤ P/C`: in an abelian
quotient every subgroup is normal, and normality pulls back along the quotient map. -/
theorem normal_of_le_of_quotient_commutative
    {P : Type*} [Group P] {C T : Subgroup P} [C.Normal]
    (hC_le_T : C ≤ T) (hquot_comm : ∀ x y : P ⧸ C, x * y = y * x) :
    T.Normal := by
  let Q : Subgroup (P ⧸ C) := T.map (QuotientGroup.mk' C)
  have hQ_normal : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hconj : g * n * g⁻¹ = n := by
      rw [hquot_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn
  have hcomap : Q.comap (QuotientGroup.mk' C) = T := by
    dsimp [Q]
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hC_le_T
  rw [← hcomap]
  exact hQ_normal.comap (QuotientGroup.mk' C)

/-- **Isaacs Thm 6.12 setup**: after choosing `T/C` of order `p`, a self-centralizing
`C` satisfies `Z(T) < C`.

The inclusion `Z(T) ≤ C` comes from self-centralizing: any central element of `T` centralizes
`C`.  It is strict because otherwise `T/C` is cyclic of prime order and central, forcing `T`
to be abelian. -/
theorem center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal]
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T) :
    Subgroup.center T < C.subgroupOf T := by
  have hZ_le_C : Subgroup.center T ≤ C.subgroupOf T := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    have hz_cent : ((z : T) : P) ∈ Subgroup.centralizer (C : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcomm_T :
          (⟨c, hC_le_T hc⟩ : T) * z = z * ⟨c, hC_le_T hc⟩ :=
        Subgroup.mem_center_iff.mp hz ⟨c, hC_le_T hc⟩
      exact congrArg Subtype.val hcomm_T
    simpa [hCent] using hz_cent
  have hne : Subgroup.center T ≠ C.subgroupOf T := by
    intro hEq
    haveI hCsub_normal : (C.subgroupOf T).Normal := inferInstance
    have h_card_quot : Nat.card (T ⧸ C.subgroupOf T) = p := by
      rw [← Subgroup.index_eq_card]
      simpa [Subgroup.relIndex] using hC_rel
    haveI : IsCyclic (T ⧸ C.subgroupOf T) := isCyclic_of_prime_card h_card_quot
    have hker_le : (QuotientGroup.mk' (C.subgroupOf T)).ker ≤ Subgroup.center T := by
      rw [QuotientGroup.ker_mk']
      exact le_of_eq hEq.symm
    have hT_comm : ∀ x y : T, x * y = y * x :=
      commutative_of_cyclic_center_quotient (QuotientGroup.mk' (C.subgroupOf T)) hker_le
    exact hT_not_comm ⟨⟨hT_comm⟩⟩
  exact lt_of_le_of_ne hZ_le_C hne

/-- **Isaacs Thm 6.12 setup**: the relative-index computation used before applying
Lemma 6.15.

If `C.subgroupOf T` has index `p` in `T` and `Z(T)` has index `p` in `C.subgroupOf T`,
then `|T : Z(T)| = p²`. -/
theorem center_index_eq_prime_sq_of_subgroupOf_relIndex_prime
    {P : Type*} [Group P] {p : ℕ}
    {C T : Subgroup P}
    (hC_rel : C.relIndex T = p)
    (hZ_le_C : Subgroup.center T ≤ C.subgroupOf T)
    (hZ_rel : (Subgroup.center T).relIndex (C.subgroupOf T) = p) :
    (Subgroup.center T).index = p ^ 2 := by
  have hCsub_index : (C.subgroupOf T).index = p := by
    simpa [Subgroup.relIndex] using hC_rel
  have hmul :
      (Subgroup.center T).relIndex (C.subgroupOf T) * (C.subgroupOf T).index =
        (Subgroup.center T).index :=
    Subgroup.relIndex_mul_index hZ_le_C
  rw [hZ_rel, hCsub_index] at hmul
  simpa [pow_two] using hmul.symm

/-- **Isaacs Thm 6.12 setup**: if `C = ⟨c⟩` and `c^p ∈ Z(T)`, then
`|C : Z(T)| = p`.

The quotient `C / (Z(T) ∩ C)` is cyclic.  The image of `c` has `p`-th power `1`, so
the quotient cardinal divides `p`; because it is also a nontrivial quotient of a `p`-group,
`p` divides its cardinal. -/
theorem center_relIndex_zpowers_eq_prime_of_pow_mem_center
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hT : IsPGroup p T) {c : T}
    (hZ_lt_C : Subgroup.center T < Subgroup.zpowers c)
    (hcp : c ^ p ∈ Subgroup.center T) :
    (Subgroup.center T).relIndex (Subgroup.zpowers c) = p := by
  let C : Subgroup T := Subgroup.zpowers c
  let ZC : Subgroup C := (Subgroup.center T).subgroupOf C
  change (Subgroup.center T).relIndex C = p
  have hZC_le_center : ZC ≤ Subgroup.center C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hz_center : ((z : C) : T) ∈ Subgroup.center T := by
      simpa [ZC, Subgroup.mem_subgroupOf] using hz
    exact Subgroup.mem_center_iff.mp hz_center ((x : C) : T)
  haveI hZC_normal : ZC.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn_center : n ∈ Subgroup.center C := hZC_le_center hn
    have hgn : g * n = n * g := Subgroup.mem_center_iff.mp hn_center g
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = n * g * g⁻¹ := by rw [hgn]
        _ = n := by simp
    rwa [hconj]
  let Q := C ⧸ ZC
  haveI hC_cyclic : IsCyclic C := Subgroup.isCyclic_zpowers c
  haveI hQ_cyclic : IsCyclic Q :=
    isCyclic_of_surjective (QuotientGroup.mk' ZC) (QuotientGroup.mk'_surjective ZC)
  have hQ_exp_dvd : Monoid.exponent Q ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ZC q
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff (N := ZC) (x ^ p)).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    change ((x : T) ^ p) ∈ Subgroup.center T
    have hx_mem : (x : T) ∈ Subgroup.zpowers c := x.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx_mem
    have hxpow : (x : T) ^ p = (c ^ p) ^ k := by
      rw [← hk]
      calc
        (c ^ k) ^ p = (c ^ k) ^ (p : ℤ) := by rw [zpow_natCast]
        _ = c ^ (k * (p : ℤ)) := by rw [← zpow_mul]
        _ = c ^ ((p : ℤ) * k) := by rw [mul_comm]
        _ = (c ^ (p : ℤ)) ^ k := by rw [zpow_mul]
        _ = (c ^ p) ^ k := by rw [zpow_natCast]
    simpa [hxpow] using zpow_mem hcp k
  have hQ_card_dvd_p : Nat.card Q ∣ p := by
    have hcard_exp : Nat.card Q = Monoid.exponent Q :=
      (IsCyclic.exponent_eq_card (α := Q)).symm
    rw [hcard_exp]
    exact hQ_exp_dvd
  have hrel_card : (Subgroup.center T).relIndex C = Nat.card Q := by
    change ZC.index = Nat.card (C ⧸ ZC)
    rw [Subgroup.index_eq_card]
  have hrel_ne_one : (Subgroup.center T).relIndex C ≠ 1 := by
    intro hrel
    have hC_le_Z : C ≤ Subgroup.center T := Subgroup.relIndex_eq_one.mp hrel
    exact hZ_lt_C.ne (le_antisymm hZ_lt_C.le hC_le_Z)
  have hp_dvd_Q_card : p ∣ Nat.card Q := by
    have hQ_p : IsPGroup p Q := (hT.to_subgroup C).to_quotient ZC
    rcases hQ_p.card_eq_or_dvd with hQ_card_one | hdiv
    · exfalso
      exact hrel_ne_one (by rw [hrel_card, hQ_card_one])
    · exact hdiv
  rw [hrel_card]
  exact Nat.dvd_antisymm hQ_card_dvd_p hp_dvd_Q_card

/-- **Dihedral recognition helper** (used in Lem 6.13 inverting case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `a² = 1`, and `a c a⁻¹ = c⁻¹`, then
`P ≃* DihedralGroup (orderOf c)`. -/
private noncomputable def dihedralIsoOfInverting
    {P : Type*} [Group P] [Finite P]
    (c a : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = 1) (h_conj : a * c * a⁻¹ = c⁻¹) :
    P ≃* DihedralGroup (orderOf c) := by
  classical
  set N := orderOf c with hN_def
  haveI : Fintype P := Fintype.ofFinite P
  -- N > 0 since `P` is finite.
  have hc_fin : IsOfFinOrder c := isOfFinOrder_of_finite c
  have hN_pos : 0 < N := hc_fin.orderOf_pos
  haveI : NeZero N := ⟨hN_pos.ne'⟩
  -- Conjugation by `a` inverts every power of `c`.
  have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
    have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
      have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
        (MulAut.conj a : P ≃* P).bijective
      simpa using (map_zpow (MulAut.conj a : P →* P) c k).symm
    rw [step1, h_conj, inv_zpow, ← zpow_neg]
  -- Cardinality computation: |P| = 2 * N.
  have hcard_P : Nat.card P = 2 * N := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers] at h
    omega
  -- Forward map `DihedralGroup N → P`.
  let fwd : DihedralGroup N → P
    | DihedralGroup.r i => c ^ i.val
    | DihedralGroup.sr i => a * c ^ i.val
  -- Helper: `c ^ (i.val + j.val) = c ^ ((i + j).val)` for `i j : ZMod N`.
  have hc_addval : ∀ i j : ZMod N, c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add]
    -- `c ^ k = c ^ (k % N)` via `pow_eq_pow_iff_modEq` (since `N = orderOf c`).
    rw [pow_eq_pow_iff_modEq, Nat.ModEq, ← hN_def]
    -- `(i + j).val % N = (i.val + j.val) % N` from `ZMod.val_add`.
    rw [ZMod.val_add, Nat.mod_mod]
  have hc_subval : ∀ i j : ZMod N, c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹ := by
    intro i j
    have h := hc_addval (j - i) i
    rw [sub_add_cancel] at h
    -- h : c ^ j.val = c ^ (j - i).val * c ^ i.val
    exact eq_mul_inv_iff_mul_eq.mpr h.symm
  -- `a⁻¹ = a` from `a² = 1`.
  have ha_inv : a⁻¹ = a := by
    have h1 : a * a = 1 := by rw [← sq, h_a_sq]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  -- Commutation: `c ^ k * a = a * c ^ (-k)` for `k : ℤ`.
  have h_zpow_a : ∀ k : ℤ, c ^ k * a = a * c ^ (-k) := fun k => by
    have h := h_conj_zpow (-k)
    rw [neg_neg] at h
    -- h : a * c ^ (-k) * a⁻¹ = c ^ k
    -- Goal: c ^ k * a = a * c ^ (-k)
    rw [show (c ^ k : P) = a * c ^ (-k) * a⁻¹ from h.symm,
        mul_assoc (a * c ^ (-k)), inv_mul_cancel, mul_one]
  -- Bridge: `c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹` (already proved as `hc_subval`).
  -- For `h_sr_r`: `c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val`. Use the conjugation
  -- relation, then bridge via `pow_eq_pow_iff_modEq` and ZMod-arithmetic.
  have h_sr_r : ∀ i j : ZMod N, c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val := by
    intro i j
    -- LHS = c^i.val * (a * c^j.val) = c^i.val * a * c^j.val (associativity)
    -- Use h_zpow_a (i.val : ℤ): c^(i.val : ℤ) * a = a * c^(-(i.val : ℤ))
    -- Then combine c^(-(i.val : ℤ)) * c^(j.val : ℤ) = c^(j.val - i.val : ℤ).
    -- Finally show c^(j.val - i.val : ℤ) = c^((j - i).val : ℕ) via mod N.
    have step1 : c ^ i.val * a = a * c ^ (-(i.val : ℤ)) := by
      have := h_zpow_a (i.val : ℤ)
      rw [zpow_natCast] at this; exact this
    rw [step1, mul_assoc, ← zpow_natCast c j.val, ← zpow_add]
    -- Goal: a * c ^ (-(i.val : ℤ) + (j.val : ℤ)) = a * c ^ (j - i).val
    congr 1
    rw [show (c ^ (j - i).val : P) = c ^ ((j - i).val : ℤ) from (zpow_natCast c _).symm,
        zpow_eq_zpow_iff_modEq, ← hN_def]
    -- Bridge `(-i.val + j.val : ℤ) ≡ ((j - i).val : ℤ) [ZMOD (N : ℤ)]` via ZMod equality.
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  -- Injectivity: `fwd` does not collapse `c^i.val` and `a * c^j.val` (since `a ∉ ⟨c⟩`),
  -- and is injective on each branch by `orderOf c = N`.
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · -- `c^i.val = c^j.val` ⇒ `i = j` via `pow_eq_pow_iff_modEq`
      congr 1
      have hmod : i.val ≡ j.val [MOD N] := (pow_eq_pow_iff_modEq).mp h
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
    · -- `c^i.val = a * c^j.val` ⇒ `a ∈ ⟨c⟩`, contradiction
      exfalso
      apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by
        rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · -- `a * c^i.val = c^j.val` ⇒ `a ∈ ⟨c⟩`, contradiction
      exfalso
      apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by
        rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · -- `a * c^i.val = a * c^j.val` ⇒ `i = j`
      congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD N] := (pow_eq_pow_iff_modEq).mp heq
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
  -- Cardinality equality.
  have hcard_eq : Nat.card (DihedralGroup N) = Nat.card P := by
    rw [DihedralGroup.nat_card, hcard_P]
  -- Build the Equiv via bijectivity.
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [DihedralGroup.card]
    rw [← Nat.card_eq_fintype_card, hcard_P]
  -- Build map_mul (4 cases).
  have hfwd_mul : ∀ x y : DihedralGroup N, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd]
    · -- r i * r j = r (i+j)
      show c ^ (i + j).val = c ^ i.val * c ^ j.val
      exact hc_addval i j
    · -- r i * sr j = sr (j - i)
      show a * c ^ (j - i).val = c ^ i.val * (a * c ^ j.val)
      rw [← mul_assoc]
      exact (h_sr_r i j).symm
    · -- sr i * r j = sr (i + j)
      show a * c ^ (i + j).val = a * c ^ i.val * c ^ j.val
      rw [mul_assoc, ← hc_addval]
    · -- sr i * sr j = r (j - i)
      show c ^ (j - i).val = a * c ^ i.val * (a * c ^ j.val)
      rw [mul_assoc, ← mul_assoc (c ^ i.val), h_sr_r, ← mul_assoc]
      rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
  -- Assemble.
  let setEquiv : DihedralGroup N ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

/-- **Quaternion recognition helper** (used in Lem 6.13 inverting case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `orderOf c = 2 * M` with `M > 0`,
`a² = c ^ M` (the unique involution in `⟨c⟩`), and `a c a⁻¹ = c⁻¹`, then
`P ≃* QuaternionGroup M`. -/
private noncomputable def quaternionIsoOfInverting
    {P : Type*} [Group P] [Finite P]
    (c a : P) (M : ℕ) (hM_pos : 0 < M) (h_order : orderOf c = 2 * M)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = c ^ M) (h_conj : a * c * a⁻¹ = c⁻¹) :
    P ≃* QuaternionGroup M := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  set N := 2 * M with hN_def
  haveI : NeZero M := ⟨hM_pos.ne'⟩
  haveI : NeZero N := ⟨by positivity⟩
  have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h_orderOf : orderOf c = N := h_order
  -- Conjugation by `a` inverts every power of `c`.
  have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
    have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
      have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
        (MulAut.conj a : P ≃* P).bijective
      simpa using (map_zpow (MulAut.conj a : P →* P) c k).symm
    rw [step1, h_conj, inv_zpow, ← zpow_neg]
  -- Cardinality computation: |P| = 2 * N = 4 * M.
  have hcard_P : Nat.card P = 4 * M := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_orderOf] at h
    omega
  -- Forward map `QuaternionGroup M → P`.
  let fwd : QuaternionGroup M → P
    | QuaternionGroup.a i => c ^ i.val
    | QuaternionGroup.xa i => a * c ^ i.val
  -- Helpers (mirror dihedral case, with `N = 2 * M`).
  have hc_addval : ∀ i j : ZMod N, c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_orderOf, ZMod.val_add, Nat.mod_mod]
  have hc_subval : ∀ i j : ZMod N, c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹ := by
    intro i j
    have h := hc_addval (j - i) i
    rw [sub_add_cancel] at h
    exact eq_mul_inv_iff_mul_eq.mpr h.symm
  -- Commutation: `c ^ k * a = a * c ^ (-k)` for `k : ℤ` (uses no `a²` assumption).
  have h_zpow_a : ∀ k : ℤ, c ^ k * a = a * c ^ (-k) := fun k => by
    have h := h_conj_zpow (-k)
    rw [neg_neg] at h
    rw [show (c ^ k : P) = a * c ^ (-k) * a⁻¹ from h.symm,
        mul_assoc (a * c ^ (-k)), inv_mul_cancel, mul_one]
  -- Cross-relation: `c^i.val * a * c^j.val = a * c^(j-i).val`.
  have h_sr_r : ∀ i j : ZMod N, c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val := by
    intro i j
    have step1 : c ^ i.val * a = a * c ^ (-(i.val : ℤ)) := by
      have := h_zpow_a (i.val : ℤ); rw [zpow_natCast] at this; exact this
    rw [step1, mul_assoc, ← zpow_natCast c j.val, ← zpow_add]
    congr 1
    rw [show (c ^ (j - i).val : P) = c ^ ((j - i).val : ℤ) from (zpow_natCast c _).symm,
        zpow_eq_zpow_iff_modEq, h_orderOf]
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  -- Injectivity.
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · congr 1
      have hmod : i.val ≡ j.val [MOD N] := by
        rw [← h_orderOf]; exact (pow_eq_pow_iff_modEq).mp h
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
    · exfalso; apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · exfalso; apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD N] := by
        rw [← h_orderOf]; exact (pow_eq_pow_iff_modEq).mp heq
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
  -- Bijectivity from cardinality + injectivity.
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [QuaternionGroup.card, ← Nat.card_eq_fintype_card, hcard_P]
  -- map_mul (4 cases: a/a, a/xa, xa/a, xa/xa). Note xa/xa uses `a² = c^M`.
  have hfwd_mul : ∀ x y : QuaternionGroup M, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd]
    · -- a i * a j = a (i+j)
      change c ^ (i + j).val = c ^ i.val * c ^ j.val
      exact hc_addval i j
    · -- a i * xa j = xa (j - i)
      change a * c ^ (j - i).val = c ^ i.val * (a * c ^ j.val)
      rw [← mul_assoc]; exact (h_sr_r i j).symm
    · -- xa i * a j = xa (i + j)
      change a * c ^ (i + j).val = a * c ^ i.val * c ^ j.val
      rw [mul_assoc, ← hc_addval]
    · -- xa i * xa j = a (↑M + j - i). Uses a² = c^M.
      change c ^ ((↑M + j - i : ZMod N)).val = a * c ^ i.val * (a * c ^ j.val)
      -- Compute RHS: a * c^i.val * a * c^j.val = a² * c^(j-i).val = c^M * c^(j-i).val
      --            = c^(M + j - i).val
      rw [mul_assoc, ← mul_assoc (c ^ i.val), h_sr_r, ← mul_assoc, ← sq, h_a_sq]
      -- Goal: c ^ (↑M + j - i).val = c ^ M * c ^ (j - i).val
      have : c ^ M * c ^ (j - i).val = c ^ ((↑M + (j - i) : ZMod N)).val := by
        rw [hc_addval]
        congr 1
        -- Need: c^M = c^((↑M : ZMod N).val). i.e., `(M : ZMod N).val = M` since M < N.
        rw [show ((↑M : ZMod N).val : ℕ) = M from by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt (by rw [hN_def]; omega)]
      rw [this]
      congr 1
      ring_nf
  let setEquiv : QuaternionGroup M ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

private lemma eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one
    {P : Type*} [Group P] [Finite P] (c y : P)
    (hy_mem : y ∈ Subgroup.zpowers c) (hy_sq : y ^ 2 = 1) (hy_ne : y ≠ 1) :
    y = c ^ (orderOf c / 2) ∧ orderOf c = 2 * (orderOf c / 2) ∧ 0 < orderOf c / 2 := by
  classical
  have hc_fin : IsOfFinOrder c := isOfFinOrder_of_finite c
  have hN_pos : 0 < orderOf c := hc_fin.orderOf_pos
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < orderOf c := Finset.mem_range.mp hm_range
  have hpow2 : c ^ (2 * m) = 1 := by
    have := hy_sq
    rw [← hm_eq, pow_two, ← pow_add] at this
    simpa [two_mul] using this
  have h_dvd : orderOf c ∣ 2 * m := orderOf_dvd_of_pow_eq_one hpow2
  have h_not_dvd : ¬ orderOf c ∣ m := by
    intro hdm
    apply hy_ne
    rw [← hm_eq]
    exact orderOf_dvd_iff_pow_eq_one.mp hdm
  have hm_pos : 0 < m := by
    by_contra hm_nonpos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm_nonpos
    exact h_not_dvd (by rw [hm0]; exact dvd_zero _)
  rcases h_dvd with ⟨q, hq⟩
  have hq_pos : 0 < q := by
    by_contra hq_nonpos
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq_nonpos
    nlinarith
  have hq_lt_two : q < 2 := by
    have hlt : orderOf c * q < orderOf c * 2 := by nlinarith
    exact (Nat.mul_lt_mul_left hN_pos).mp hlt
  have hq_eq : q = 1 := by omega
  have htwo_m : 2 * m = orderOf c := by
    rw [hq_eq, mul_one] at hq
    exact hq
  have hm_half : m = orderOf c / 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hm_half]
    exact hm_eq.symm
  · omega
  · omega

theorem dihedralOrQuaternion_of_invertingConjugation
    {P : Type*} [Group P] [Finite P] (_hP : IsPGroup 2 P)
    (c a : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_conj : a * c * a⁻¹ = c⁻¹) :
    Nonempty (P ≃* DihedralGroup (orderOf c)) ∨
      Nonempty (P ≃* QuaternionGroup (orderOf c / 2)) := by
  classical
  by_cases h_a_sq_one : a ^ 2 = 1
  · left
    exact ⟨dihedralIsoOfInverting c a h_idx h_a_notmem h_a_sq_one h_conj⟩
  · right
    have h_a_sq_mem : a ^ 2 ∈ Subgroup.zpowers c :=
      Subgroup.sq_mem_of_index_two h_idx a
    have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
      have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
        have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
          (MulAut.conj a : P ≃* P).bijective
        simpa using (map_zpow (MulAut.conj a : P →* P) c k).symm
      rw [step1, h_conj, inv_zpow, ← zpow_neg]
    have h_a_sq_sq : (a ^ 2) ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h_a_sq_mem
      have h_fixed : a * (c ^ k) * a⁻¹ = c ^ k := by
        rw [hk]
        group
      have h_inv : c ^ k = c ^ (-k) := by
        rw [← h_fixed]
        exact h_conj_zpow k
      calc (a ^ 2) ^ 2 = c ^ k * c ^ k := by rw [← hk, pow_two]
        _ = c ^ k * c ^ (-k) := congrArg (fun t => c ^ k * t) h_inv
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    obtain ⟨h_a_sq_half, h_order, h_half_pos⟩ :=
      eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c (a ^ 2)
        h_a_sq_mem h_a_sq_sq h_a_sq_one
    exact ⟨quaternionIsoOfInverting c a (orderOf c / 2)
      h_half_pos h_order h_idx h_a_notmem h_a_sq_half h_conj⟩

/-- **Semidihedral recognition helper** (normalised twist case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `a² = 1`,
`orderOf c = 2^k`, and conjugation by `a` sends `c` to the semidihedral twist
`c ^ (SemiDihedralGroup.twist k).val`, then `P ≃* SemiDihedralGroup k`. -/
private noncomputable def semiDihedralIsoOfTwistNormalized
    {P : Type*} [Group P] [Finite P]
    (c a : P) (k : ℕ) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = 1)
    (h_conj : a * c * a⁻¹ = c ^ (SemiDihedralGroup.twist k).val) :
    P ≃* SemiDihedralGroup k := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have hN_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  haveI : NeZero (2 ^ k) := ⟨hN_pos.ne'⟩
  set r : ZMod (2 ^ k) := SemiDihedralGroup.twist k with hr_def
  have hcard_P : Nat.card P = 2 * 2 ^ k := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_order] at h
    omega
  let fwd : SemiDihedralGroup k → P
    | SemiDihedralGroup.c i => c ^ i.val
    | SemiDihedralGroup.ca i => a * c ^ i.val
  have hc_addval : ∀ i j : ZMod (2 ^ k), c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_order, ZMod.val_add, Nat.mod_mod]
  have h_conj_pow :
      ∀ i : ZMod (2 ^ k), a * c ^ i.val * a⁻¹ = c ^ (r * i).val := by
    intro i
    have h_map : a * c ^ i.val * a⁻¹ = (a * c * a⁻¹) ^ i.val := by
      simpa using (map_pow (MulAut.conj a : P →* P) c i.val).symm
    rw [h_map, h_conj, ← pow_mul]
    rw [pow_eq_pow_iff_modEq, Nat.ModEq, h_order]
    rw [ZMod.val_mul, Nat.mod_mod]
  have ha_inv : a⁻¹ = a := by
    have h1 : a * a = 1 := by rw [← sq, h_a_sq]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have h_pow_a : ∀ i : ZMod (2 ^ k), c ^ i.val * a = a * c ^ (r * i).val := by
    intro i
    have h := h_conj_pow i
    rw [ha_inv] at h
    calc c ^ i.val * a
        = (a * a) * c ^ i.val * a := by rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
      _ = a * (a * c ^ i.val * a) := by group
      _ = a * c ^ (r * i).val := by rw [h]
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · congr 1
      have hmod : i.val ≡ j.val [MOD 2 ^ k] := by
        have hmod0 : i.val ≡ j.val [MOD orderOf c] := (pow_eq_pow_iff_modEq).mp h
        rwa [h_order] at hmod0
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective (2 ^ k) hmod
    · exfalso; apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · exfalso; apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD 2 ^ k] := by
        have hmod0 : i.val ≡ j.val [MOD orderOf c] := (pow_eq_pow_iff_modEq).mp heq
        rwa [h_order] at hmod0
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective (2 ^ k) hmod
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [SemiDihedralGroup.card, ← Nat.card_eq_fintype_card, hcard_P]
    rw [pow_succ, mul_comm]
  have hfwd_mul : ∀ x y : SemiDihedralGroup k, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd, SemiDihedralGroup.c_mul_c,
      SemiDihedralGroup.c_mul_ca, SemiDihedralGroup.ca_mul_c, SemiDihedralGroup.ca_mul_ca,
      ← hr_def]
    · change c ^ (i + j).val = c ^ i.val * c ^ j.val
      exact hc_addval i j
    · change a * c ^ (r * i + j).val = c ^ i.val * (a * c ^ j.val)
      rw [← mul_assoc, h_pow_a, mul_assoc, ← hc_addval]
    · change a * c ^ (i + j).val = a * c ^ i.val * c ^ j.val
      rw [mul_assoc, ← hc_addval]
    · change c ^ (r * i + j).val = a * c ^ i.val * (a * c ^ j.val)
      calc c ^ (r * i + j).val
          = c ^ (r * i).val * c ^ j.val := hc_addval (r * i) j
        _ = (a * a) * c ^ (r * i).val * c ^ j.val := by
          rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
        _ = a * (a * c ^ (r * i).val) * c ^ j.val := by group
        _ = a * (c ^ i.val * a) * c ^ j.val := by rw [h_pow_a]
        _ = a * c ^ i.val * (a * c ^ j.val) := by group
  let setEquiv : SemiDihedralGroup k ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

private lemma pow_twist_eq_pow_half_mul_inv
    {P : Type*} [Group P] [Finite P] (c : P) {k : ℕ}
    (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k) :
    c ^ (SemiDihedralGroup.twist k).val = c ^ (2 ^ (k - 1)) * c⁻¹ := by
  rw [← zpow_natCast]
  have hrhs : c ^ (2 ^ (k - 1)) * c⁻¹ =
      c ^ (((2 : ℕ) ^ (k - 1) : ℤ) - 1) := by
    simpa [div_eq_mul_inv] using (zpow_natCast_sub_one c (2 ^ (k - 1))).symm
  rw [hrhs, zpow_eq_zpow_iff_modEq, h_order]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  rcases k with _ | _ | n
  · omega
  · omega
  · simp [SemiDihedralGroup.twist]

private lemma twist_conj_zmod_pow
    {P : Type*} [Group P] [Finite P]
    (c a z : P) {k : ℕ} (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    ∀ i : ZMod (2 ^ k),
      a * c ^ i.val * a⁻¹ = c ^ (SemiDihedralGroup.twist k * i).val := by
  intro i
  have h_conj_twist : a * c * a⁻¹ = c ^ (SemiDihedralGroup.twist k).val := by
    rw [h_conj, h_z_pow, ← pow_twist_eq_pow_half_mul_inv c hk h_order]
  have h_map : a * c ^ i.val * a⁻¹ = (a * c * a⁻¹) ^ i.val := by
    simpa using (map_pow (MulAut.conj a : P →* P) c i.val).symm
  rw [h_map, h_conj_twist, ← pow_mul]
  rw [pow_eq_pow_iff_modEq, Nat.ModEq, h_order]
  rw [ZMod.val_mul, Nat.mod_mod]

private lemma two_mul_eq_zero_of_twist_fixed
    {k : ℕ} (hk : 3 ≤ k) {i : ZMod (2 ^ k)}
    (hfix : SemiDihedralGroup.twist k * i = i) :
    (2 : ZMod (2 ^ k)) * i = 0 := by
  rcases k with _ | _ | _ | n
  · omega
  · omega
  · omega
  · change (2 : ZMod (2 ^ (n + 3))) * i = 0
    change ((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 1) * i = i at hfix
    have hzero : (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) * i = 0) := by
      have hcalc : (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) * i) =
          (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 1) * i - i) := by
        ring
      rw [hcalc, hfix]
      ring
    have hfactor :
        ((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) =
          (2 : ZMod (2 ^ (n + 3))) *
            ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3))) := by
      rw [Nat.cast_sub (by exact Nat.one_le_two_pow)]
      push_cast
      rw [pow_succ']
      ring
    rw [hfactor] at hzero
    have hodd : Odd (2 ^ (n + 1) - 1) := by
      have h_even : Even (2 ^ (n + 1)) :=
        even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      exact Nat.Even.sub_odd Nat.one_le_two_pow h_even odd_one
    have hcop : Nat.Coprime (2 ^ (n + 1) - 1) (2 ^ (n + 3)) := by
      rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]
      exact hodd
    let u := ZMod.unitOfCoprime (2 ^ (n + 1) - 1) hcop
    have hu : (u : ZMod (2 ^ (n + 3))) =
        ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3))) :=
      ZMod.coe_unitOfCoprime _ _
    have hzero' : (u : ZMod (2 ^ (n + 3))) * ((2 : ZMod (2 ^ (n + 3))) * i) = 0 := by
      calc (u : ZMod (2 ^ (n + 3))) * ((2 : ZMod (2 ^ (n + 3))) * i)
          = ((2 : ZMod (2 ^ (n + 3))) *
              ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3)))) * i := by
            rw [hu]
            ring
        _ = 0 := hzero
    exact (Units.mul_right_eq_zero u).mp hzero'

private lemma sq_eq_one_of_mem_zpowers_fixed_by_twist
    {P : Type*} [Group P] [Finite P]
    (c a z y : P) {k : ℕ} (hk_three : 3 ≤ k)
    (h_order : orderOf c = 2 ^ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹)
    (hy_mem : y ∈ Subgroup.zpowers c)
    (hy_fixed : a * y * a⁻¹ = y) :
    y ^ 2 = 1 := by
  classical
  have hk_two : 2 ≤ k := by omega
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < 2 ^ k := by
    have := Finset.mem_range.mp hm_range
    rwa [h_order] at this
  let i : ZMod (2 ^ k) := m
  have hi_val : i.val = m := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hm_lt
  have hfix_pow : c ^ (SemiDihedralGroup.twist k * i).val = c ^ i.val := by
    calc c ^ (SemiDihedralGroup.twist k * i).val
        = a * c ^ i.val * a⁻¹ :=
          (twist_conj_zmod_pow c a z hk_two h_order h_z_pow h_conj i).symm
      _ = a * c ^ m * a⁻¹ := by rw [hi_val]
      _ = a * y * a⁻¹ := by rw [hm_eq]
      _ = y := hy_fixed
      _ = c ^ m := hm_eq.symm
      _ = c ^ i.val := by rw [hi_val]
  have hfix : SemiDihedralGroup.twist k * i = i := by
    have hmod : (SemiDihedralGroup.twist k * i).val ≡ i.val [MOD 2 ^ k] := by
      have hmod0 : (SemiDihedralGroup.twist k * i).val ≡ i.val [MOD orderOf c] :=
        (pow_eq_pow_iff_modEq).mp hfix_pow
      rwa [h_order] at hmod0
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at hmod
    exact ZMod.val_injective (2 ^ k) hmod
  have htwo : (2 : ZMod (2 ^ k)) * i = 0 :=
    two_mul_eq_zero_of_twist_fixed hk_three hfix
  have hii : i + i = 0 := by
    simpa [two_mul] using htwo
  have hc_addval : c ^ (i + i).val = c ^ i.val * c ^ i.val := by
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_order, ZMod.val_add, Nat.mod_mod]
  calc y ^ 2
      = c ^ i.val * c ^ i.val := by rw [← hm_eq, hi_val, pow_two]
    _ = c ^ (i + i).val := hc_addval.symm
    _ = 1 := by rw [hii, ZMod.val_zero, pow_zero]

private lemma zpowers_involution_eq_pow_pred_of_order_two_pow
    {P : Type*} [Group P] [Finite P] (c z : P) {k : ℕ}
    (hk_pos : 0 < k) (h_order : orderOf c = 2 ^ k)
    (h_z_mem : z ∈ Subgroup.zpowers c) (h_z_sq : z ^ 2 = 1) (h_z_ne : z ≠ 1) :
    z = c ^ (2 ^ (k - 1)) := by
  obtain ⟨h_z_half, _h_order_even, _h_half_pos⟩ :=
    eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c z h_z_mem h_z_sq h_z_ne
  have hhalf : 2 ^ k / 2 = 2 ^ (k - 1) := by
    rcases k with _ | k
    · omega
    · simp [pow_succ]
  rw [h_z_half, h_order, hhalf]

/-- In a finite cyclic `2`-group of order larger than `2`, the nontrivial involution is a
square.

This is the cyclic-quotient square-root step in Isaacs Thm 6.12: if the cyclic quotient
`P/C` has order larger than `2`, then its unique involution coset is a square. -/
theorem exists_sq_eq_of_isCyclic_two_group_involution_of_card_ne_two
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) [IsCyclic Q]
    {x : Q} (hx_ne : x ≠ 1) (hx_sq : x ^ 2 = 1) (hcard_ne_two : Nat.card Q ≠ 2) :
    ∃ y : Q, y ^ 2 = x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨k, hcard⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).mp hQ
  have hcard_ne_one : Nat.card Q ≠ 1 := by
    intro hcard_one
    haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hcard_one).1
    exact hx_ne (Subsingleton.elim x 1)
  have hk_pos : 0 < k := by
    by_contra hk_not
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk_not
    apply hcard_ne_one
    rw [hcard, hk_zero, pow_zero]
  have hk_ne_one : k ≠ 1 := by
    intro hk_one
    apply hcard_ne_two
    rw [hcard, hk_one, pow_one]
  have hk_two : 2 ≤ k := by omega
  have hg_order : orderOf g = 2 ^ k := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg_gen
  have hx_mem : x ∈ Subgroup.zpowers g := hg_gen x
  have hx_eq : x = g ^ (2 ^ (k - 1)) :=
    zpowers_involution_eq_pow_pred_of_order_two_pow g x hk_pos hg_order hx_mem hx_sq hx_ne
  refine ⟨g ^ (2 ^ (k - 2)), ?_⟩
  rw [hx_eq, ← pow_mul]
  congr 1
  rw [show k - 1 = k - 2 + 1 by omega, pow_succ]

private lemma square_eq_one_or_unique_involution_of_square_sq_one
    {P : Type*} [Group P] (c a z : P)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_z_unique : ∀ y ∈ Subgroup.zpowers c, y ^ 2 = 1 → y ≠ 1 → y = z)
    (h_a_sq_sq : (a ^ 2) ^ 2 = 1) :
    a ^ 2 = 1 ∨ a ^ 2 = z := by
  by_cases h_a_sq_one : a ^ 2 = 1
  · exact Or.inl h_a_sq_one
  · exact Or.inr (h_z_unique (a ^ 2)
      (Subgroup.sq_mem_of_index_two h_idx a) h_a_sq_sq h_a_sq_one)

private lemma two_le_exponent_of_nonabelian_index_two
    {P : Type*} [Group P] [Finite P] (c : P) {k : ℕ}
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_order : orderOf c = 2 ^ k)
    (hk_pos : 0 < k) :
    2 ≤ k := by
  by_contra hk_not
  have hk_eq : k = 1 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card P = 2 ^ 2 := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_order, hk_eq] at h
    omega
  obtain ⟨x, y, hxy⟩ := h_nonab
  exact hxy (IsPGroup.commutative_of_card_eq_prime_sq (p := 2) hcard x y)

private lemma commutative_of_index_two_zpowers_of_commute_generator
    {P : Type*} [Group P] (c a : P)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_comm : Commute a c) :
    ∀ x y : P, x * y = y * x := by
  let C := Subgroup.zpowers c
  have h_a_inv_notmem : a⁻¹ ∉ C := by
    intro ha
    exact h_a_notmem (C.inv_mem_iff.mp ha)
  have h_repr : ∀ x : P, (∃ m : ℤ, c ^ m = x) ∨ ∃ m : ℤ, x = a * c ^ m := by
    intro x
    by_cases hx : x ∈ C
    · left
      exact Subgroup.mem_zpowers_iff.mp hx
    · right
      have hax : a⁻¹ * x ∈ C := by
        rw [Subgroup.mul_mem_iff_of_index_two h_idx]
        exact iff_of_false h_a_inv_notmem hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hax
      exact ⟨m, by
        calc x = a * (a⁻¹ * x) := by group
          _ = a * c ^ m := by rw [← hm]⟩
  intro x y
  rcases h_repr x with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rcases h_repr y with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact (Commute.zpow_zpow_self c m n).eq
    · have hcm_a : Commute (c ^ m) a := h_comm.symm.zpow_left m
      calc c ^ m * (a * c ^ n)
          = a * (c ^ m * c ^ n) := hcm_a.left_comm (c ^ n)
        _ = a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = a * c ^ n * c ^ m := by group
  · rcases h_repr y with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have hcn_a : Commute (c ^ n) a := h_comm.symm.zpow_left n
      calc (a * c ^ m) * c ^ n
          = a * (c ^ m * c ^ n) := by group
        _ = a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = c ^ n * (a * c ^ m) := by rw [hcn_a.left_comm]
    · have ham : Commute a (c ^ m) := h_comm.zpow_right m
      have han : Commute a (c ^ n) := h_comm.zpow_right n
      calc (a * c ^ m) * (a * c ^ n)
          = a * a * (c ^ m * c ^ n) := by
            rw [mul_assoc, ham.symm.left_comm]
            group
        _ = a * a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = a * (a * c ^ n) * c ^ m := by group
        _ = a * (c ^ n * a) * c ^ m := by rw [han.eq]
        _ = (a * c ^ n) * (a * c ^ m) := by
            group

private lemma three_le_exponent_of_nonabelian_twist
    {P : Type*} [Group P] [Finite P] (c a z : P) {k : ℕ}
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (hk : 2 ≤ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    3 ≤ k := by
  by_contra hk_not
  have hk_eq : k = 2 := by omega
  have h_conj_c : a * c * a⁻¹ = c := by
    rw [h_conj, h_z_pow, hk_eq]
    norm_num
    group
  have h_comm : Commute a c := by
    change a * c = c * a
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [h_conj_c]
  obtain ⟨x, y, hxy⟩ := h_nonab
  exact hxy (commutative_of_index_two_zpowers_of_commute_generator c a
    h_idx h_a_notmem h_comm x y)

private noncomputable def semiDihedralIsoOfTwistInvolution
    {P : Type*} [Group P] [Finite P]
    (c a z : P) (k : ℕ) (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_a_sq : a ^ 2 = 1)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    P ≃* SemiDihedralGroup k := by
  refine semiDihedralIsoOfTwistNormalized c a k h_order h_idx h_a_notmem h_a_sq ?_
  rw [h_conj, h_z_pow, ← pow_twist_eq_pow_half_mul_inv c hk h_order]

private noncomputable def semiDihedralIsoOfTwistSquareInvolution
    {P : Type*} [Group P] [Finite P]
    (c a z : P) (k : ℕ) (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_mem : z ∈ Subgroup.zpowers c)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_z_sq : z ^ 2 = 1)
    (h_a_sq : a ^ 2 = z)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    P ≃* SemiDihedralGroup k := by
  classical
  have hz_comm : Commute z c := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h_z_mem
    rw [← hm]
    exact Commute.zpow_self c m
  have h_ca_notmem : c * a ∉ Subgroup.zpowers c := by
    intro hca
    apply h_a_notmem
    have ha : a = c⁻¹ * (c * a) := by group
    rw [ha]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
      hca
  have h_ca_sq : (c * a) ^ 2 = 1 := by
    calc (c * a) ^ 2
        = (c * a) * (c * a) := by rw [pow_two]
      _ = c * (a * c * a⁻¹) * a ^ 2 := by group
      _ = c * (z * c⁻¹) * z := by rw [h_conj, h_a_sq]
      _ = (c * z * c⁻¹) * z := by group
      _ = z * z := by rw [hz_comm.symm.mul_inv_cancel]
      _ = 1 := by rw [← pow_two, h_z_sq]
  have h_ca_conj : (c * a) * c * (c * a)⁻¹ = z * c⁻¹ := by
    calc (c * a) * c * (c * a)⁻¹
        = c * (a * c * a⁻¹) * c⁻¹ := by group
      _ = c * (z * c⁻¹) * c⁻¹ := by rw [h_conj]
      _ = (c * z * c⁻¹) * c⁻¹ := by group
      _ = z * c⁻¹ := by rw [hz_comm.symm.mul_inv_cancel]
  exact semiDihedralIsoOfTwistInvolution c (c * a) z k hk h_order h_idx
    h_ca_notmem h_z_pow h_ca_sq h_ca_conj

/-- **Isaacs Lemma 6.13 (twist case)**: Let `P` be a finite nonabelian 2-group with a cyclic
subgroup `C = ⟨c⟩` of index `2`, and `a ∈ P − C` with `a * c * a⁻¹ = z * c⁻¹` where `z` is
the unique involution in `C`. Then `P ≃* SemiDihedralGroup k` where `2 ^ k = orderOf c`. -/
theorem semiDihedral_of_twistConjugation
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (c a z : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_mem : z ∈ Subgroup.zpowers c) (h_z_sq : z ^ 2 = 1) (h_z_ne : z ≠ 1)
    (h_z_unique : ∀ y ∈ Subgroup.zpowers c, y ^ 2 = 1 → y ≠ 1 → y = z)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    ∃ k : ℕ, 2 ^ k = orderOf c ∧ Nonempty (P ≃* SemiDihedralGroup k) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, h_order⟩ := (IsPGroup.iff_orderOf.mp hP) c
  have hk_pos : 0 < k := by
    obtain ⟨_h_z_half, _h_order_even, h_half_pos⟩ :=
      eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c z h_z_mem h_z_sq h_z_ne
    by_contra hk_not
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk_not
    rw [h_order, hk0] at h_half_pos
    norm_num at h_half_pos
  have hk_two : 2 ≤ k :=
    two_le_exponent_of_nonabelian_index_two c h_nonab h_idx h_order hk_pos
  have h_z_pow : z = c ^ (2 ^ (k - 1)) :=
    zpowers_involution_eq_pow_pred_of_order_two_pow c z hk_pos h_order
      h_z_mem h_z_sq h_z_ne
  have hk_three : 3 ≤ k :=
    three_le_exponent_of_nonabelian_twist c a z h_nonab h_idx h_a_notmem
      hk_two h_z_pow h_conj
  have h_a_sq_sq : (a ^ 2) ^ 2 = 1 := by
    exact sq_eq_one_of_mem_zpowers_fixed_by_twist c a z (a ^ 2)
      hk_three h_order h_z_pow h_conj
      (Subgroup.sq_mem_of_index_two h_idx a)
      (by group)
  refine ⟨k, h_order.symm, ?_⟩
  rcases square_eq_one_or_unique_involution_of_square_sq_one c a z
      h_idx h_z_unique h_a_sq_sq with h_a_sq | h_a_sq
  · exact ⟨semiDihedralIsoOfTwistInvolution c a z k hk_two h_order h_idx
      h_a_notmem h_z_pow h_a_sq h_conj⟩
  · exact ⟨semiDihedralIsoOfTwistSquareInvolution c a z k hk_two h_order h_idx
      h_a_notmem h_z_mem h_z_pow h_z_sq h_a_sq h_conj⟩

private lemma exists_sq_ne_one_of_nonabelian
    {P : Type*} [Group P] (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    ∃ c : P, c ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨x, y, hxy⟩ := h_nonab
  have hx_inv : x⁻¹ = x := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h x])
  have hy_inv : y⁻¹ = y := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h y])
  have hxy_inv : (x * y)⁻¹ = x * y := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h (x * y)])
  apply hxy
  calc x * y
      = (x * y)⁻¹ := hxy_inv.symm
    _ = y⁻¹ * x⁻¹ := by rw [mul_inv_rev]
    _ = y * x := by rw [hy_inv, hx_inv]

private lemma exists_orderOf_eq_four_of_card_eight_nonabelian
    {P : Type*} [Group P] [Finite P]
    (h_card : Nat.card P = 8) (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    ∃ c : P, orderOf c = 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := IsPGroup.of_card (p := 2) (n := 3) (by
    rw [h_card]
    norm_num)
  obtain ⟨c, hc_sq_ne⟩ := exists_sq_ne_one_of_nonabelian h_nonab
  obtain ⟨k, h_order⟩ := (IsPGroup.iff_orderOf.mp hP) c
  have hk_le : k ≤ 3 := by
    have hdvd : 2 ^ k ∣ 2 ^ 3 := by
      have hdvd0 : orderOf c ∣ 8 := by
        rw [← h_card]
        exact orderOf_dvd_natCard c
      rw [h_order] at hdvd0
      simpa using hdvd0
    exact (Nat.pow_dvd_pow_iff_le_right one_lt_two).mp hdvd
  have hk_two : 2 ≤ k := by
    by_contra hk_not
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · rw [pow_zero] at h_order
      have hc_one : c = 1 := orderOf_eq_one_iff.mp h_order
      exact hc_sq_ne (by rw [hc_one, one_pow])
    · rw [pow_one] at h_order
      exact hc_sq_ne (orderOf_dvd_iff_pow_eq_one.mp (by rw [h_order]))
  have hk_ne_three : k ≠ 3 := by
    intro hk3
    have hcyc : IsCyclic P := isCyclic_of_orderOf_eq_card c (by
      rw [h_order, hk3, h_card]
      norm_num)
    obtain ⟨x, y, hxy⟩ := h_nonab
    haveI : IsCyclic P := hcyc
    exact hxy (Std.Commutative.comm x y)
  have hk_eq : k = 2 := by omega
  exact ⟨c, by rw [h_order, hk_eq]; norm_num⟩

private lemma mem_zpowers_orderOf_four_eq_self_or_inv
    {P : Type*} [Group P] [Finite P] {c y : P}
    (h_order : orderOf c = 4)
    (hy_mem : y ∈ Subgroup.zpowers c)
    (hy_order : orderOf y = 4) :
    y = c ∨ y = c⁻¹ := by
  classical
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < 4 := by
    have := Finset.mem_range.mp hm_range
    rwa [h_order] at this
  have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with rfl | rfl | rfl | rfl
  · rw [pow_zero] at hm_eq
    rw [← hm_eq, orderOf_one] at hy_order
    norm_num at hy_order
  · left
    simpa using hm_eq.symm
  · have hy_sq : y ^ 2 = 1 := by
      rw [← hm_eq, ← pow_mul]
      change c ^ 4 = 1
      rw [← h_order, pow_orderOf_eq_one]
    have hdvd : 4 ∣ 2 := by
      rw [← hy_order]
      exact orderOf_dvd_of_pow_eq_one hy_sq
    norm_num at hdvd
  · right
    rw [← hm_eq]
    have hmul : c ^ 3 * c = 1 := by
      rw [← pow_succ]
      change c ^ 4 = 1
      rw [← h_order, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left hmul

/-- **Isaacs Corollary 6.14**: A nonabelian group of order `8` is isomorphic to `D_8` or `Q_8`
(i.e., `DihedralGroup 4` or `QuaternionGroup 2` in mathlib indexing). -/
theorem dihedralOrQuaternion_of_card_eight
    {P : Type*} [Group P] [Finite P]
    (h_card : Nat.card P = 8) (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := IsPGroup.of_card (p := 2) (n := 3) (by
    rw [h_card]
    norm_num)
  obtain ⟨c, h_order4⟩ :=
    exists_orderOf_eq_four_of_card_eight_nonabelian h_card h_nonab
  have h_idx : (Subgroup.zpowers c).index = 2 := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [Nat.card_zpowers, h_order4, h_card] at h
    omega
  obtain ⟨a, h_a_notmem, _h_cover⟩ :=
    (Subgroup.index_eq_two_iff_exists_notMem_and.mp h_idx)
  have h_a_inv_notmem : a⁻¹ ∉ Subgroup.zpowers c := by
    intro ha
    exact h_a_notmem ((Subgroup.zpowers c).inv_mem_iff.mp ha)
  have h_ac_notmem : a * c ∉ Subgroup.zpowers c := by
    rw [Subgroup.mul_mem_iff_of_index_two h_idx]
    intro hiff
    exact h_a_notmem (hiff.mpr (Subgroup.mem_zpowers c))
  have hy_mem : a * c * a⁻¹ ∈ Subgroup.zpowers c := by
    rw [Subgroup.mul_mem_iff_of_index_two h_idx]
    exact iff_of_false h_ac_notmem h_a_inv_notmem
  have hy_order : orderOf (a * c * a⁻¹) = 4 := by
    have hsemi : SemiconjBy a c (a * c * a⁻¹) := by
      change a * c = (a * c * a⁻¹) * a
      group
    exact (SemiconjBy.orderOf_eq a hsemi).symm.trans h_order4
  rcases mem_zpowers_orderOf_four_eq_self_or_inv h_order4 hy_mem hy_order with h_conj_fixed | h_conj
  · exfalso
    have h_comm : Commute a c := by
      change a * c = c * a
      calc a * c = (a * c * a⁻¹) * a := by group
        _ = c * a := by rw [h_conj_fixed]
    obtain ⟨x, y, hxy⟩ := h_nonab
    exact hxy (commutative_of_index_two_zpowers_of_commute_generator c a
      h_idx h_a_notmem h_comm x y)
  · rcases dihedralOrQuaternion_of_invertingConjugation hP c a h_idx h_a_notmem h_conj
      with hD | hQ
    · left
      rw [h_order4] at hD
      exact hD
    · right
      have h_half : orderOf c / 2 = 2 := by
        rw [h_order4]
      rw [h_half] at hQ
      exact hQ

/-! ### Isaacs Lemma 6.15: characteristic elementary abelian `p²` subgroup

mmd L3533-3541. Statement: `T` is a `p`-group with `|T| ≠ 8`, `|T : Z(T)| = p²`, and there is a
cyclic subgroup `C` with `Z(T) < C < T`. Then `T` has a characteristic elementary abelian
subgroup of order `p²`.

The proof splits on `p`:
- `p ≠ 2`: take `K = {x | x^p = 1}` (subgroup since `T` has class ≤ 2 by Step 0,
  using `Ch04.setOfPowEqOne`). `K` is characteristic, and `|K| = p²` from the bounds
  `θ(T) ⊆ Z(T)` (since `T/Z(T)` order `p²` noncyclic = elementary abelian) and `K ∩ C`
  cyclic with `|K : K ∩ C| ≤ p`.
- `p = 2`: apply twice the sub-lemma "noncyclic abelian 2-group with cyclic subgroup of
  index 2 ⇒ `{a | a² = 1}` is characteristic elementary abelian of order 4". -/

/-- **Step 0 of Lem 6.15**: under the hypothesis `Z(T) ≤ C` and `|T : Z(T)| = p²` with
`Z(T) ≠ C`, we get `|T : C| = p`. -/
private lemma index_eq_prime_of_center_lt_of_center_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    C.index = p := by
  -- C.index ∣ Z.index = p^2
  have h_dvd : C.index ∣ (Subgroup.center T).index :=
    Subgroup.index_dvd_of_le hZ_lt_C.le
  rw [h_idx] at h_dvd
  -- C.index ∈ {1, p, p^2}
  rcases (Nat.dvd_prime_pow hp.out).mp h_dvd with ⟨k, hk, hkpow⟩
  interval_cases k
  · -- k = 0: C = ⊤
    rw [pow_zero] at hkpow
    have : C = ⊤ := Subgroup.index_eq_one.mp hkpow
    exact absurd this hC_lt_T.ne
  · rw [pow_one] at hkpow; exact hkpow
  · -- k = 2: C = Z(T)
    exfalso
    rw [← h_idx] at hkpow
    -- From C.index = (Z(T)).index = p^2 and index_mul_card, |C| = |Z(T)|.
    have h_card_eq : Nat.card C = Nat.card (Subgroup.center T) := by
      have h1 := C.index_mul_card
      have h2 := (Subgroup.center T).index_mul_card
      rw [hkpow, ← h2] at h1
      have hidx_pos : 0 < (Subgroup.center T).index := by
        rw [h_idx]; exact Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)
      exact Nat.eq_of_mul_eq_mul_left hidx_pos h1
    have hZ_eq_C : Subgroup.center T = C :=
      Subgroup.eq_of_le_of_card_ge hZ_lt_C.le (le_of_eq h_card_eq)
    exact hZ_lt_C.ne hZ_eq_C

/-- **Step 0 of Lem 6.15**: under the hypothesis of Lem 6.15, `commutator T ≤ Z(T)`
(i.e. `T` has nilpotence class ≤ 2). -/
private lemma commutator_le_center_of_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) :
    _root_.commutator T ≤ Subgroup.center T := by
  haveI hZnorm : (Subgroup.center T).Normal := inferInstance
  -- `T ⧸ Z(T)` of order p² is abelian.
  have h_card_quot : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  have h_quot_comm : ∀ a b : T ⧸ Subgroup.center T, a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := p) h_card_quot
  exact hZnorm.quotient_commutative_iff_commutator_le.mp ⟨h_quot_comm⟩

/-- **Step 0 of Lem 6.15**: under the hypothesis `Z(T) ≤ C` and `|T : Z(T)| = p²`, `C` is
normal in `T`. (Because `T/Z(T)` of order `p²` is abelian, so every subgroup of `T/Z(T)`
is normal, and `C/Z(T)` lifts back to `C` normal in `T`.) -/
private lemma normal_of_center_le_of_center_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hZ_le_C : Subgroup.center T ≤ C) : C.Normal := by
  haveI hZnorm : (Subgroup.center T).Normal := inferInstance
  -- T/Z(T) of order p² is abelian.
  have h_card_quot : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  have hQuot_comm : ∀ a b : T ⧸ Subgroup.center T, a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := p) h_card_quot
  -- Image of C under the quotient map: C/Z(T) ≤ T/Z(T).
  let C' : Subgroup (T ⧸ Subgroup.center T) := C.map (QuotientGroup.mk' (Subgroup.center T))
  haveI hC'Norm : C'.Normal := by
    -- Subgroups of an abelian quotient are normal: g*n*g⁻¹ = n via mul_comm.
    refine ⟨fun n hn g => ?_⟩
    have h_eq : g * n * g⁻¹ = n := by
      rw [hQuot_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [h_eq]; exact hn
  -- C = preimage of C' under mk' Z(T) (because Z(T) ≤ C).
  have h_comap_eq : C'.comap (QuotientGroup.mk' (Subgroup.center T)) = C := by
    show ((C.map (QuotientGroup.mk' (Subgroup.center T))).comap _) = C
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr hZ_le_C
  rw [← h_comap_eq]
  exact hC'Norm.comap _

/-- **Helper for Lem 6.15**: if `|T : Z(T)| = p²` then `T` is nonabelian. -/
private lemma exists_not_commute_of_center_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) :
    ∃ x y : T, x * y ≠ y * x := by
  by_contra h
  push_neg at h
  -- T abelian ⇒ Z(T) = ⊤ ⇒ index = 1.
  have hZ_top : Subgroup.center T = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    exact fun y => (h y x)
  rw [hZ_top, Subgroup.index_top] at h_idx
  have hp1 : 1 < p := hp.out.one_lt
  have hp_sq_lt : 1 < p ^ 2 := by
    calc 1 = 1 ^ 2 := (one_pow 2).symm
      _ < p ^ 2 := Nat.pow_lt_pow_left hp1 (by norm_num)
  omega

/-- **Lem 6.15 `p = 2` setup**: the quotient `T/T'` is abelian. -/
theorem quotient_commutator_commutative
    {T : Type*} [Group T] :
    ∀ a b : T ⧸ _root_.commutator T, a * b = b * a := by
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (le_rfl : _root_.commutator T ≤ _root_.commutator T)).comm

/-- **Lem 6.15 `p = 2` setup**: under the center-index hypothesis of Lemma 6.15,
the quotient `T/T'` is not cyclic.

This isolates Isaacs's observation that, once `T' ≤ Z(T)`, cyclicity of `T/T'` would make
`T` itself abelian by `commutative_of_cyclic_center_quotient`, contradicting
`|T : Z(T)| = p²`. -/
theorem quotient_commutator_not_isCyclic_of_center_index_prime_sq
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) :
    ¬ IsCyclic (T ⧸ _root_.commutator T) := by
  intro h_cyc
  obtain ⟨x, y, hxy⟩ := exists_not_commute_of_center_index_pow_two h_idx
  let f : T →* T ⧸ _root_.commutator T := QuotientGroup.mk' (_root_.commutator T)
  have hker : f.ker ≤ Subgroup.center T := by
    rw [QuotientGroup.ker_mk']
    exact commutator_le_center_of_index_pow_two h_idx
  haveI : IsCyclic (T ⧸ _root_.commutator T) := h_cyc
  exact hxy (commutative_of_cyclic_center_quotient f hker x y)

/-- **Lem 6.15 `p = 2` setup**: the image of Isaacs's cyclic subgroup `C` in `T/T'`
is cyclic of index `2`.

This supplies the `D ≤ T/T'` input for
`exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group`. -/
theorem quotient_commutator_image_cyclic_index_two_of_center_index_four
    {T : Type*} [Group T] [Finite T]
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    IsCyclic (C.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      (C.map (QuotientGroup.mk' (_root_.commutator T))).index = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · haveI : IsCyclic C := hC_cyclic
    exact isCyclic_of_surjective
      ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap C)
      ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap_surjective C)
  · have hcomm_le_C : _root_.commutator T ≤ C :=
      (commutator_le_center_of_index_pow_two (p := 2) h_idx).trans hZ_lt_C.le
    calc
      (C.map (QuotientGroup.mk' (_root_.commutator T))).index = C.index := by
        exact Subgroup.index_map_eq C
          (QuotientGroup.mk'_surjective (_root_.commutator T)) (by
            rw [QuotientGroup.ker_mk']
            exact hcomm_le_C)
      _ = 2 :=
        index_eq_prime_of_center_lt_of_center_index_pow_two
          (p := 2) h_idx hZ_lt_C hC_lt_T

/-- **Step 0 of Lem 6.15** (cardinality): under the hypothesis of Lem 6.15,
`|commutator T| = p`. -/
private lemma card_commutator_eq_prime_of_lem_6_15
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} [C.Normal] (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    Nat.card (_root_.commutator T) = p := by
  have hC_idx : C.index = p :=
    index_eq_prime_of_center_lt_of_center_index_pow_two h_idx hZ_lt_C hC_lt_T
  -- Cyclic quotient T/C.
  have hCT_card : Nat.card (T ⧸ C) = p := by rw [← Subgroup.index_eq_card]; exact hC_idx
  haveI : IsCyclic (T ⧸ C) := isCyclic_of_prime_card hCT_card
  -- Use Lem 4.6: |commutator T| · |C ⊓ Z(T)| = |C|.
  have h_lem46 :
      Nat.card (_root_.commutator T) * Nat.card (C ⊓ Subgroup.center T : Subgroup T)
        = Nat.card C := by
    refine
      OddOrder.Isaacs.Ch04.card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
      (A := C) ?_ ?_
    · -- C abelian (cyclic)
      intro a ha b hb
      haveI := hC_cyclic
      letI : CommGroup C := IsCyclic.commGroup
      have h_comm : ∀ x y : ↥C, x * y = y * x := mul_comm
      exact congrArg (fun (z : ↥C) => (z : T)) (h_comm ⟨a, ha⟩ ⟨b, hb⟩)
    · -- T/C cyclic
      infer_instance
  -- C ⊓ Z(T) = Z(T) since Z(T) ≤ C.
  have h_inf : C ⊓ Subgroup.center T = Subgroup.center T := inf_eq_right.mpr hZ_lt_C.le
  rw [h_inf] at h_lem46
  -- |C| / |Z(T)| = p. From |T| = p²·|Z(T)| = p·|C|, we get |C| = p·|Z(T)|.
  have h_card_T_Z : (Subgroup.center T).index * Nat.card (Subgroup.center T) = Nat.card T :=
    Subgroup.index_mul_card _
  have h_card_T_C : C.index * Nat.card C = Nat.card T := Subgroup.index_mul_card _
  rw [h_idx] at h_card_T_Z
  rw [hC_idx] at h_card_T_C
  have h_card_C : Nat.card C = p * Nat.card (Subgroup.center T) := by
    have hp_pos : 0 < p := hp.out.pos
    have hT_eq : p ^ 2 * Nat.card (Subgroup.center T) = p * Nat.card C := by
      rw [h_card_T_Z, h_card_T_C]
    have hT_eq' : p * (p * Nat.card (Subgroup.center T)) = p * Nat.card C := by
      have : p ^ 2 * Nat.card (Subgroup.center T) = p * (p * Nat.card (Subgroup.center T)) := by
        ring
      rw [← this]; exact hT_eq
    exact (Nat.eq_of_mul_eq_mul_left hp_pos hT_eq').symm
  rw [h_card_C] at h_lem46
  -- Now: |commutator T| · |Z(T)| = p · |Z(T)|, so |commutator T| = p (since |Z(T)| > 0).
  have hZ_pos : 0 < Nat.card (Subgroup.center T) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hZ_pos h_lem46

/-! ### Odd p case of Lem 6.15 -/

/-- **Lem 6.15 odd-p helper**: under the hypothesis of Lem 6.15 with `p` odd, the set
`{x : T | x^p = 1}` is characteristic, i.e., preserved by any automorphism. The same set
is also a subgroup (via `Ch04.setOfPowEqOne`); here we record characteristicity. -/
private lemma setOfPowEqOne_characteristic_of_class_le_two_odd
    {T : Type*} [Group T] {p : ℕ} (hp : Odd p)
    (hC : _root_.commutator T ≤ Subgroup.center T) :
    (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext x
  rw [Subgroup.mem_comap]
  show (φ x) ^ p = 1 ↔ x ^ p = 1
  refine ⟨fun hpx => ?_, fun hpx => ?_⟩
  · -- φ x ^ p = 1 ⇒ φ (x^p) = 1 ⇒ x^p = 1 by injectivity
    rw [← map_pow] at hpx
    have : φ (x ^ p) = φ 1 := by rw [hpx, map_one]
    exact φ.injective this
  · rw [← map_pow, hpx, map_one]

/-- **Lem 6.15 odd-p helper**: Under the hypothesis of Lem 6.15 with `p` odd,
the image of `θ : T → T, θ(x) = x^p` is contained in `Z(T)`. -/
private lemma pow_p_mem_center_of_index_pow_two_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) (x : T) :
    x ^ p ∈ Subgroup.center T := by
  -- T/Z(T) has order p² and is noncyclic (otherwise T abelian, contradiction).
  haveI hZnorm : (Subgroup.center T).Normal := inferInstance
  have h_card_quot : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  -- Get T is nonabelian:
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_center_index_pow_two h_idx
  -- The quotient T/Z(T) is not cyclic (because then T abelian).
  have h_quot_not_cyclic : ¬ IsCyclic (T ⧸ Subgroup.center T) := by
    intro h_cyc
    let f : T →* T ⧸ Subgroup.center T := QuotientGroup.mk' (Subgroup.center T)
    have hker : f.ker ≤ Subgroup.center T := by
      rw [QuotientGroup.ker_mk']
    have h_comm : ∀ a b : T, a * b = b * a :=
      @commutative_of_cyclic_center_quotient T _ _ _ h_cyc f hker
    exact hab (h_comm a b)
  -- T/Z(T) of order p² noncyclic ⇒ exponent = p.
  haveI hp_prime : Fact p.Prime := hp
  have h_quot_exp : Monoid.exponent (T ⧸ Subgroup.center T) = p :=
    (not_isCyclic_iff_exponent_eq_prime hp.out h_card_quot).mp h_quot_not_cyclic
  -- So every element x : T satisfies (x : T/Z(T))^p = 1, i.e., x^p ∈ Z(T).
  have h_pow_eq_one : (QuotientGroup.mk x : T ⧸ Subgroup.center T) ^ p = 1 := by
    rw [← h_quot_exp]; exact Monoid.pow_exponent_eq_one _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h_pow_eq_one
  exact h_pow_eq_one

/-- **Lem 6.15 odd-p helper**: the kernel of `θ : T → T, x ↦ x^p` has order ≥ p².
Given the commutator structure (class ≤ 2) with `|commutator T| = p` (Step 0)
and `|T : Z(T)| = p²`. -/
private lemma card_setOfPowEqOne_ge_pow_two_of_index_pow_two_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    (hC : _root_.commutator T ≤ Subgroup.center T)
    (h_commp : ∀ c ∈ _root_.commutator T, c ^ p = 1) :
    p ^ 2 ≤ Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) := by
  -- Define θ : T → T as a homomorphism (Ch04.powPHom). Use Lagrange: |K| · |im| = |T|.
  let θ := OddOrder.Isaacs.Ch04.powPHom hC hp_odd h_commp
  -- ker θ = setOfPowEqOne
  have h_ker_eq : θ.ker = OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd := by
    ext x
    constructor
    · intro hx
      change x ^ p = 1
      exact hx
    · intro hx
      change x ^ p = 1 at hx
      exact hx
  -- im θ ⊆ Z(T)
  have h_im_le_Z : θ.range ≤ Subgroup.center T := by
    rintro _ ⟨x, rfl⟩
    change x ^ p ∈ Subgroup.center T
    exact pow_p_mem_center_of_index_pow_two_odd h_idx x
  -- |ker| · |im| = |T| and |im| ≤ |Z(T)|, so |ker| ≥ |T| / |Z(T)| = p²
  have h_lag : Nat.card θ.ker * θ.ker.index = Nat.card T :=
    Subgroup.card_mul_index _
  rw [Subgroup.index_ker] at h_lag
  have h_im_card_le : Nat.card θ.range ≤ Nat.card (Subgroup.center T) :=
    Subgroup.card_le_of_le h_im_le_Z
  rw [h_ker_eq] at h_lag
  -- |T| = (Z(T)).index * |Z(T)| = p² * |Z(T)|
  have hT_card : Nat.card T = p ^ 2 * Nat.card (Subgroup.center T) := by
    have := (Subgroup.center T).index_mul_card
    rw [h_idx] at this
    exact this.symm
  rw [hT_card] at h_lag
  -- p² * |Z(T)| ≤ |K| * |Z(T)| (using h_im_card_le and h_lag)
  have hZ_pos : 0 < Nat.card (Subgroup.center T) := Nat.card_pos
  by_contra hKlt
  push_neg at hKlt
  -- |K| < p² ⇒ |K| * |Z(T)| < p² * |Z(T)|. But |K| * |im θ| = |T| = p² * |Z(T)|
  -- and |im θ| ≤ |Z(T)|.
  have h_lt : Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) * Nat.card θ.range
            < p ^ 2 * Nat.card (Subgroup.center T) := by
    calc Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) * Nat.card θ.range
        ≤ Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) * Nat.card (Subgroup.center T) :=
          Nat.mul_le_mul_left _ h_im_card_le
      _ < p ^ 2 * Nat.card (Subgroup.center T) := by
          exact (Nat.mul_lt_mul_right hZ_pos).mpr hKlt
  omega

/-- **Lem 6.15 odd-p helper**: `K ⊓ C` has order ≤ p, where `K = {x | x^p = 1}` and
`C` is cyclic. This uses: subgroup of cyclic is cyclic, and a cyclic group all of whose
elements have order dividing p has order ≤ p. -/
private lemma card_setOfPowEqOne_inf_le_prime
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (hC : _root_.commutator T ≤ Subgroup.center T)
    {C : Subgroup T} (hC_cyclic : IsCyclic C) :
    Nat.card ((OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) ⊓ C : Subgroup T) ≤ p := by
  -- The inf K ⊓ C is a subgroup of C (cyclic), hence cyclic.
  set K := OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd with hK_def
  -- Every element x ∈ K ⊓ C satisfies x^p = 1, so orderOf x ∣ p, i.e., orderOf x = 1 or p.
  -- A finite cyclic group all of whose elements have order dividing p has order ≤ p.
  -- Approach: take generator g of K ⊓ C (cyclic); g^p = 1; orderOf g ≤ p; |K ⊓ C| = orderOf g.
  haveI : IsCyclic ((K ⊓ C : Subgroup T).subgroupOf C) :=
    Subgroup.isCyclic_of_le (le_top : (K ⊓ C : Subgroup T).subgroupOf C ≤ ⊤)
  -- The subgroup K ⊓ C ↪ C is cyclic.
  haveI : IsCyclic (K ⊓ C : Subgroup T) := by
    -- Use isCyclic_of_le with K ⊓ C ≤ C: but this needs a coercion from Subgroup C, while
    -- here both K ⊓ C and C are subgroups of T. We use the equivalence via subgroupOf.
    refine isCyclic_of_injective ((K ⊓ C : Subgroup T).inclusion (inf_le_right : K ⊓ C ≤ C)) ?_
    exact Subgroup.inclusion_injective _
  -- Every element x ∈ K ⊓ C satisfies x^p = 1, so the exponent of K ⊓ C divides p.
  -- Since K ⊓ C is cyclic, its exponent equals its cardinality, hence |K ⊓ C| ≤ p.
  have h_exp_dvd : Monoid.exponent (K ⊓ C : Subgroup T) ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    show ((x : T) ^ p : T) = (1 : T)
    push_cast
    have h_mem : (x : T) ∈ K := (Subgroup.mem_inf.mp x.2).1
    exact h_mem
  have h_card_eq : Nat.card (K ⊓ C : Subgroup T) = Monoid.exponent (K ⊓ C : Subgroup T) :=
    (IsCyclic.exponent_eq_card (α := (K ⊓ C : Subgroup T))).symm
  rw [h_card_eq]
  exact Nat.le_of_dvd hp.out.pos h_exp_dvd

/-- **Lem 6.15 odd-p helper**: `|K| ≤ p²` where `K = {x | x^p = 1}`.
Use `|K| = |K : K ⊓ C| · |K ⊓ C|`, `|K : K ⊓ C| = C.relIndex K ≤ C.index = p`, and
`|K ⊓ C| ≤ p`. -/
private lemma card_setOfPowEqOne_le_pow_two_of_index_pow_two_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    (hC : _root_.commutator T ≤ Subgroup.center T)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) ≤ p ^ 2 := by
  set K := OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd with hK_def
  have hC_idx : C.index = p :=
    index_eq_prime_of_center_lt_of_center_index_pow_two h_idx hZ_lt_C hC_lt_T
  have h_int_le : Nat.card (K ⊓ C : Subgroup T) ≤ p :=
    card_setOfPowEqOne_inf_le_prime hp_odd hC hC_cyclic
  -- |K : K ⊓ C| · |K ⊓ C| = |K| in subgroup K. The standard fact is
  -- (K ⊓ C).relIndex K = C.relIndex K, and `relIndex_le_of_le_right` then bounds
  -- `C.relIndex K ≤ C.relIndex ⊤ = C.index = p`.
  have hC_idx_ne_zero : C.index ≠ 0 := by rw [hC_idx]; exact hp.out.ne_zero
  have hC_relIndex_le : C.relIndex K ≤ C.index := by
    have h := Subgroup.relIndex_le_of_le_right (H := C) (K := K) (L := ⊤) le_top ?_
    · simpa [Subgroup.relIndex_top_right] using h
    · simp [Subgroup.relIndex_top_right, hC_idx_ne_zero]
  -- (K ⊓ C).index_within_K equals C.relIndex K.
  -- Use the Lagrange relation in K. Lemma: H ⊆ K' with H.subgroupOf K' has
  -- (H.subgroupOf K').index = K'.relIndex (H ⊔ K') ... we'll just use:
  -- |K| = (C.subgroupOf K).index * Nat.card (C.subgroupOf K) (subgroup of K)
  -- But Nat.card (C.subgroupOf K) = Nat.card (K ⊓ C). Let's use directly.
  have h_lag_in_K :
      (C.subgroupOf K).index * Nat.card (C.subgroupOf K) = Nat.card K :=
    Subgroup.index_mul_card _
  -- (C.subgroupOf K).index = C.relIndex K by definition.
  have h_relIndex_def : C.relIndex K = (C.subgroupOf K).index := rfl
  -- Nat.card (C.subgroupOf K) = Nat.card (K ⊓ C : Subgroup T).
  have h_card_subgroupOf : Nat.card (C.subgroupOf K) = Nat.card (K ⊓ C : Subgroup T) := by
    refine Nat.card_congr ?_
    refine {
      toFun := fun x => ⟨((x : K) : T), ?_⟩
      invFun := fun y => ⟨⟨(y : T), (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
    }
    · -- ((x : K) : T) ∈ K ⊓ C
      refine Subgroup.mem_inf.mpr ⟨(x : K).2, ?_⟩
      have := x.2
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    · rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_inf.mp y.2).2
    · intro x; rfl
    · intro y; rfl
  rw [h_card_subgroupOf, ← h_relIndex_def] at h_lag_in_K
  -- |K| = C.relIndex K * |K ⊓ C| ≤ p * p = p².
  rw [← h_lag_in_K]
  calc C.relIndex K * Nat.card (K ⊓ C : Subgroup T)
      ≤ p * p := by
        have h1 : C.relIndex K ≤ p := by rw [← hC_idx]; exact hC_relIndex_le
        exact Nat.mul_le_mul h1 h_int_le
    _ = p ^ 2 := by ring

/-! ### Lem 6.15 — main theorem (odd case + dispatch). -/

/-- **Isaacs Lemma 6.15** (odd `p` case): Let `T` be a group with `|T : Z(T)| = p²` and a
cyclic subgroup `C` with `Z(T) < C < T`. If `p` is odd, then there is a characteristic
elementary abelian subgroup of `T` of order `p²` (specifically `K = {x | x^p = 1}`). -/
private theorem char_elementaryAbelian_p_sq_of_index_p_sq_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  have hC : _root_.commutator T ≤ Subgroup.center T :=
    commutator_le_center_of_index_pow_two h_idx
  haveI hC_normal : C.Normal :=
    normal_of_center_le_of_center_index_pow_two h_idx hZ_lt_C.le
  -- |commutator T| = p
  have h_card_comm : Nat.card (_root_.commutator T) = p :=
    card_commutator_eq_prime_of_lem_6_15 h_idx hC_cyclic hC_lt_T hZ_lt_C
  -- Every element of commutator T has order ∣ p (Lagrange), so c^p = 1.
  have h_commp : ∀ c ∈ _root_.commutator T, c ^ p = 1 := by
    intro c hc
    -- Work in the subgroup commutator T (as a group), use Nat.card.
    have h_pow_in : (⟨c, hc⟩ : _root_.commutator T) ^ Nat.card (_root_.commutator T) = 1 :=
      pow_card_eq_one'
    rw [h_card_comm] at h_pow_in
    have : ((⟨c, hc⟩ : _root_.commutator T) ^ p : _root_.commutator T) = (1 : _root_.commutator T) :=
      h_pow_in
    have h_pow' : (c : T) ^ p = 1 := by
      have h1 := congrArg Subtype.val this
      simpa using h1
    exact h_pow'
  -- K = ker (x ↦ x^p), realized as setOfPowEqOne.
  set K := OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd with hK_def
  refine ⟨K, ?_, ?_, ?_⟩
  · exact setOfPowEqOne_characteristic_of_class_le_two_odd hp_odd hC
  · -- K is elementary abelian: K commutes pointwise (subset of abelian T? No, T might be
    -- nonabelian. But K ⊆ ... wait, the def of IsElementaryAbelian is commutativity in K,
    -- and every element to the p is 1.)
    -- We need: ∀ x y ∈ K, xy = yx; and ∀ x ∈ K, x^p = 1.
    -- The second is by definition of K. The first: K ⊆ Z(T)? No, that's stronger than needed.
    -- Actually: K has order p², so K of prime-square order is abelian (by mathlib
    -- `IsPGroup.commutative_of_card_eq_prime_sq`).
    -- But we need K's order. We have |K| ≥ p² and |K| ≤ p², so |K| = p².
    have h_card_ge : p ^ 2 ≤ Nat.card K :=
      card_setOfPowEqOne_ge_pow_two_of_index_pow_two_odd hp_odd h_idx hC h_commp
    have h_card_le : Nat.card K ≤ p ^ 2 :=
      card_setOfPowEqOne_le_pow_two_of_index_pow_two_odd hp_odd h_idx hC hC_cyclic hZ_lt_C hC_lt_T
    have h_card : Nat.card K = p ^ 2 := le_antisymm h_card_le h_card_ge
    refine ⟨?_, ?_⟩
    · -- commute
      exact IsPGroup.commutative_of_card_eq_prime_sq (p := p) (G := K) h_card
    · -- ∀ x : K, x^p = 1
      intro x
      apply Subtype.ext
      show ((x : T) ^ p : T) = (1 : T)
      push_cast
      have h_mem : (x : T) ∈ K := x.2
      change (x : T) ^ p = 1 at h_mem
      exact h_mem
  · -- |K| = p²
    have h_card_ge : p ^ 2 ≤ Nat.card K :=
      card_setOfPowEqOne_ge_pow_two_of_index_pow_two_odd hp_odd h_idx hC h_commp
    have h_card_le : Nat.card K ≤ p ^ 2 :=
      card_setOfPowEqOne_le_pow_two_of_index_pow_two_odd hp_odd h_idx hC hC_cyclic hZ_lt_C hC_lt_T
    exact le_antisymm h_card_le h_card_ge

/-- **Isaacs Lemma 6.15** (odd prime case).

Let `T` be a finite group with `|T : Z(T)| = p^2` and a cyclic subgroup `C` with
`Z(T) < C < T`. If `p` is odd, then `T` has a characteristic elementary abelian subgroup
of order `p^2`.

The full `p = 2` branch is handled separately below; this theorem exposes the completed
odd-`p` half for later Ch.6/Ch.7 use. -/
theorem exists_characteristic_isElementaryAbelian_of_center_index_prime_sq_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 :=
  char_elementaryAbelian_p_sq_of_index_p_sq_odd
    hp_odd h_idx hC_cyclic hZ_lt_C hC_lt_T

/-! ### `p = 2` case of Lem 6.15 -/

/-- **Lem 6.15 `p = 2` sub-lemma**: a finite abelian 2-group with a cyclic subgroup of
index 2 that is itself not cyclic has a characteristic elementary abelian subgroup of order 4
(namely `{x | x² = 1}`).

mmd L3535-3536: "If A is abelian noncyclic and B ⊆ A is cyclic of index 2, then {a | a² = 1}
is characteristic elementary abelian of order 4 in A." -/
private theorem char_elementaryAbelian_4_of_noncyclic_abelian_2group
    {A : Type*} [Group A] [Finite A] (hAb : ∀ x y : A, x * y = y * x)
    (h_two : IsPGroup 2 A)
    {D : Subgroup A} (hD_cyc : IsCyclic D) (hD_idx : D.index = 2)
    (h_not_cyclic : ¬ IsCyclic A) :
    ∃ K : Subgroup A, K.Characteristic ∧
      IsElementaryAbelian 2 K ∧ Nat.card K = 4 := by
  classical
  -- Define K = {x : A | x^2 = 1} as a subgroup (uses abelianness).
  let K : Subgroup A := {
    carrier := {x : A | x ^ 2 = 1}
    one_mem' := by show (1 : A) ^ 2 = 1; exact one_pow 2
    inv_mem' := by
      intro x (hx : x ^ 2 = 1)
      show (x⁻¹) ^ 2 = 1
      rw [inv_pow, hx, inv_one]
    mul_mem' := by
      intro x y (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
      show (x * y) ^ 2 = 1
      have h : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        rw [mul_assoc, ← mul_assoc y x y, hAb y x, mul_assoc, ← mul_assoc]
      rw [h, hx, hy, mul_one]
  }
  refine ⟨K, ?_, ?_, ?_⟩
  · -- K is characteristic
    refine ⟨fun φ => ?_⟩
    ext x
    rw [Subgroup.mem_comap]
    show (φ x) ^ 2 = 1 ↔ x ^ 2 = 1
    refine ⟨fun hpx => ?_, fun hpx => ?_⟩
    · rw [← map_pow] at hpx
      have : φ (x ^ 2) = φ 1 := by rw [hpx, map_one]
      exact φ.injective this
    · rw [← map_pow, hpx, map_one]
  · -- K is elementary abelian
    refine ⟨?_, ?_⟩
    · -- commute
      intro x y
      apply Subtype.ext
      show (x : A) * (y : A) = (y : A) * (x : A)
      exact hAb _ _
    · -- ∀ x : K, x^2 = 1
      intro x
      apply Subtype.ext
      show ((x : A) ^ 2 : A) = (1 : A)
      have h_mem : (x : A) ∈ K := x.2
      change (x : A) ^ 2 = 1 at h_mem
      exact h_mem
  · -- |K| = 4. Strategy:
    -- (a) D is normal in A (A abelian).
    -- (b) |D| is a 2-power ≥ 2.
    -- (c) |K ⊓ D| = 2: lower from involution z = d^(|D|/2); upper from cyclic K∩D / exponent 2.
    -- (d) D.relIndex K ∣ D.index = 2 (D normal).
    -- (e) For |K| ≥ 4: construct a' ∈ K \ D, then (K ⊓ D as sub of K) has index ≥ 2 in K.
    haveI hD_norm : D.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h_eq : g * n * g⁻¹ = n := by
        rw [hAb g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [h_eq]; exact hn
    -- |D| is a 2-power.
    haveI hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hD_two : IsPGroup 2 (D : Subgroup A) := h_two.to_subgroup D
    obtain ⟨kD, hD_pow⟩ := (IsPGroup.iff_card (p := 2) (G := (D : Subgroup A))).mp hD_two
    -- |D| ≠ 1 (else |A| = 2 ⇒ cyclic).
    have hD_card_ne_one : Nat.card (D : Subgroup A) ≠ 1 := by
      intro h1
      have hA_card : Nat.card A = 2 := by
        have := D.card_mul_index
        rw [hD_idx, h1] at this; omega
      exact h_not_cyclic (isCyclic_of_prime_card hA_card)
    have hkD_pos : 1 ≤ kD := by
      by_contra hlt
      push_neg at hlt
      interval_cases kD
      rw [pow_zero] at hD_pow
      exact hD_card_ne_one hD_pow
    -- |D| ≥ 2, |D| even.
    have hD_card_ge_two : 2 ≤ Nat.card (D : Subgroup A) := by
      rw [hD_pow]
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ kD := Nat.pow_le_pow_right (by norm_num) hkD_pos
    have hD_card_even : 2 ∣ Nat.card (D : Subgroup A) := by
      rw [hD_pow]; exact dvd_pow_self _ (by omega : kD ≠ 0)
    have hA_card_eq : Nat.card A = 2 * Nat.card (D : Subgroup A) := by
      have := D.index_mul_card
      rw [hD_idx] at this; omega
    set n := Nat.card (D : Subgroup A) with hn_def
    -- Generator of D (in ↥D).
    obtain ⟨d, hd_gen⟩ := IsCyclic.exists_generator (α := (D : Subgroup A))
    have hd_order : orderOf d = n := by
      rw [hn_def]; exact orderOf_eq_card_of_forall_mem_zpowers hd_gen
    -- Involution z := d^(n/2) (in A; via the coercion).
    set z : A := (d : A) ^ (n / 2) with hz_def
    have hz_in_D : z ∈ D := pow_mem d.2 _
    -- (d : A) ^ n = 1.
    have hd_pow_n_amb : (d : A) ^ n = 1 := by
      have h_in_D : (d : (D : Subgroup A)) ^ n = 1 := by
        rw [← hd_order]; exact pow_orderOf_eq_one d
      have : (((d : (D : Subgroup A)) ^ n : (D : Subgroup A)) : A) =
          ((1 : (D : Subgroup A)) : A) := by
        rw [h_in_D]
      simpa [SubmonoidClass.coe_pow] using this
    have hz_sq : z ^ 2 = 1 := by
      rw [hz_def, ← pow_mul]
      have h_mul : (n / 2) * 2 = n := by
        have := Nat.mul_div_cancel' hD_card_even
        omega
      rw [h_mul]; exact hd_pow_n_amb
    have hn_half_pos : 0 < n / 2 := by
      have : 2 ≤ n := hD_card_ge_two; omega
    have hn_half_lt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    have hz_ne_one : z ≠ 1 := by
      intro h
      have hd_pow_half : (d : (D : Subgroup A)) ^ (n / 2) = 1 := by
        apply Subtype.ext
        show (((d : (D : Subgroup A)) ^ (n / 2) : (D : Subgroup A)) : A) = (1 : A)
        rw [SubmonoidClass.coe_pow]; exact h
      have hdvd : orderOf d ∣ (n / 2) := orderOf_dvd_of_pow_eq_one hd_pow_half
      rw [hd_order] at hdvd
      have := Nat.le_of_dvd hn_half_pos hdvd
      omega
    have hz_in_K : z ∈ K := hz_sq
    -- |K ⊓ D| ≥ 2.
    have h_inf_ge_two : 2 ≤ Nat.card (K ⊓ D : Subgroup A) := by
      have h1_in : (1 : A) ∈ (K ⊓ D : Subgroup A) := Subgroup.one_mem _
      have hz_in : z ∈ (K ⊓ D : Subgroup A) := Subgroup.mem_inf.mpr ⟨hz_in_K, hz_in_D⟩
      have h_ne : (⟨z, hz_in⟩ : (K ⊓ D : Subgroup A)) ≠ ⟨1, h1_in⟩ := by
        intro heq
        exact hz_ne_one (Subtype.mk_eq_mk.mp heq)
      have h_finset_card :
          ({⟨1, h1_in⟩, ⟨z, hz_in⟩} : Finset (K ⊓ D : Subgroup A)).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        intro hmem
        rw [Finset.mem_singleton] at hmem
        exact h_ne hmem.symm
      haveI : Fintype (K ⊓ D : Subgroup A) := Fintype.ofFinite _
      have h_le_card : ({⟨1, h1_in⟩, ⟨z, hz_in⟩} : Finset (K ⊓ D : Subgroup A)).card
          ≤ Fintype.card (K ⊓ D : Subgroup A) := Finset.card_le_univ _
      rw [Nat.card_eq_fintype_card]
      omega
    -- |K ⊓ D| ≤ 2: K ⊓ D ≤ D cyclic, exponent dvd 2.
    have h_inf_le_two : Nat.card (K ⊓ D : Subgroup A) ≤ 2 := by
      haveI : IsCyclic ((K ⊓ D : Subgroup A) : Subgroup A) := by
        refine isCyclic_of_injective ((K ⊓ D : Subgroup A).inclusion
          (inf_le_right : K ⊓ D ≤ D)) ?_
        exact Subgroup.inclusion_injective _
      have h_exp_dvd : Monoid.exponent (K ⊓ D : Subgroup A) ∣ 2 := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        apply Subtype.ext
        show ((x : (K ⊓ D : Subgroup A)) : A) ^ 2 = (1 : A)
        have h_mem : (x : A) ∈ K := (Subgroup.mem_inf.mp x.2).1
        change (x : A) ^ 2 = 1 at h_mem
        exact h_mem
      have h_card_eq : Nat.card (K ⊓ D : Subgroup A) =
          Monoid.exponent (K ⊓ D : Subgroup A) :=
        (IsCyclic.exponent_eq_card (α := (K ⊓ D : Subgroup A))).symm
      rw [h_card_eq]
      exact Nat.le_of_dvd (by norm_num) h_exp_dvd
    have h_inf_eq_two : Nat.card (K ⊓ D : Subgroup A) = 2 :=
      le_antisymm h_inf_le_two h_inf_ge_two
    -- D.relIndex K ∣ 2 (D normal).
    have h_relIndex_dvd : D.relIndex K ∣ 2 := by
      rw [← hD_idx]
      exact Subgroup.relIndex_dvd_index_of_normal D K
    have h_card_subgroupOf : Nat.card (D.subgroupOf K) = Nat.card (K ⊓ D : Subgroup A) := by
      refine Nat.card_congr ?_
      refine {
        toFun := fun x => ⟨((x : K) : A), ?_⟩
        invFun := fun y => ⟨⟨(y : A), (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_
      }
      · refine Subgroup.mem_inf.mpr ⟨(x : K).2, ?_⟩
        have := x.2
        rw [Subgroup.mem_subgroupOf] at this
        exact this
      · rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.mp y.2).2
      · intro x; rfl
      · intro y; rfl
    have h_lag :
        (D.subgroupOf K).index * Nat.card (D.subgroupOf K) = Nat.card K :=
      Subgroup.index_mul_card _
    have h_relIndex_eq : D.relIndex K = (D.subgroupOf K).index := rfl
    rw [h_card_subgroupOf, h_inf_eq_two] at h_lag
    -- |K| ≤ 4 from D.relIndex K ≤ 2.
    have h_relIndex_le : D.relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) h_relIndex_dvd
    have h_K_le_4 : Nat.card K ≤ 4 := by
      rw [h_relIndex_eq] at h_relIndex_le
      have h_mul : (D.subgroupOf K).index * 2 ≤ 2 * 2 :=
        Nat.mul_le_mul_right 2 (by rw [← h_relIndex_eq]; exact h_relIndex_le)
      omega
    -- |K| ≥ 4. Use existence of a' ∈ K \ D.
    -- First, pick a ∈ A with a ∉ D.
    obtain ⟨a, ha_notmem, _ha_or⟩ :=
      (Subgroup.index_eq_two_iff_exists_notMem_and (H := D)).mp hD_idx
    have ha_sq : a ^ 2 ∈ D := Subgroup.sq_mem_of_index_two hD_idx a
    -- orderOf a < |A| (otherwise A cyclic).
    have ha_order_lt : orderOf a < Nat.card A := by
      by_contra hge
      push_neg at hge
      have h_le : orderOf a ≤ Nat.card A := orderOf_le_card
      have ha_order_eq : orderOf a = Nat.card A := le_antisymm h_le hge
      apply h_not_cyclic
      refine ⟨⟨a, ?_⟩⟩
      intro x
      have hz_card : Nat.card (Subgroup.zpowers a) = Nat.card A := by
        rw [Nat.card_zpowers, ha_order_eq]
      have hz_top : Subgroup.zpowers a = ⊤ :=
        (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers a)).mp hz_card
      have hxin : x ∈ Subgroup.zpowers a := by rw [hz_top]; trivial
      rw [Subgroup.mem_zpowers_iff] at hxin
      obtain ⟨k, hk⟩ := hxin
      exact ⟨k, hk⟩
    -- orderOf a is a 2-power.
    obtain ⟨ka, ha_order_pow_eq⟩ := (IsPGroup.iff_orderOf.mp h_two) a
    have hA_card_pow : Nat.card A = 2 ^ (kD + 1) := by
      rw [hA_card_eq, hD_pow, pow_succ]; ring
    have hka_le : ka ≤ kD := by
      have h1 : 2 ^ ka < 2 ^ (kD + 1) := by
        rw [← ha_order_pow_eq, ← hA_card_pow]; exact ha_order_lt
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
      omega
    have ha_order_dvd : orderOf a ∣ n := by
      rw [ha_order_pow_eq]
      have hn_pow : n = 2 ^ kD := by
        simpa [hn_def] using hD_pow
      rw [hn_pow]
      exact pow_dvd_pow _ hka_le
    have ha_pow_n : a ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp ha_order_dvd
    -- (a^2)^(n/2) = a^n = 1.
    have ha_sq_pow_half : (a ^ 2) ^ (n / 2) = 1 := by
      rw [← pow_mul]
      have h_mul : 2 * (n / 2) = n := Nat.mul_div_cancel' hD_card_even
      rw [h_mul]; exact ha_pow_n
    -- a^2 viewed in ↥D.
    let a2D : (D : Subgroup A) := ⟨a ^ 2, ha_sq⟩
    have ha2D_in_zpowers : a2D ∈ Subgroup.zpowers d := hd_gen a2D
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha2D_in_zpowers
    -- (a2D)^(n/2) = 1 in ↥D.
    have ha2D_pow_half : a2D ^ (n / 2) = 1 := by
      apply Subtype.ext
      show ((a2D ^ (n / 2) : (D : Subgroup A)) : A) = (1 : A)
      rw [SubmonoidClass.coe_pow]
      show (a ^ 2) ^ (n / 2) = 1
      exact ha_sq_pow_half
    -- d^(m * (n/2)) = (d^m)^(n/2) = (a2D)^(n/2) = 1, so orderOf d ∣ m * (n/2), i.e. n ∣ m*(n/2).
    have hm_two_dvd : (2 : ℤ) ∣ m := by
      have h1 : d ^ (m * ((n / 2 : ℕ) : ℤ)) = 1 := by
        rw [zpow_mul, hm, zpow_natCast]; exact ha2D_pow_half
      have h2 : (orderOf d : ℤ) ∣ m * ((n / 2 : ℕ) : ℤ) :=
        (orderOf_dvd_iff_zpow_eq_one (x := d)
          (i := m * ((n / 2 : ℕ) : ℤ))).mpr h1
      rw [hd_order] at h2
      have hn_eq_int : (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) := by
        have hh := Nat.mul_div_cancel' hD_card_even
        have : (2 * (n / 2) : ℕ) = n := hh
        push_cast at this ⊢
        omega
      rw [hn_eq_int] at h2
      have h2' : 2 * ((n / 2 : ℕ) : ℤ) ∣ m * ((n / 2 : ℕ) : ℤ) := h2
      have hn_half_pos_int : (0 : ℤ) < ((n / 2 : ℕ) : ℤ) := by exact_mod_cast hn_half_pos
      -- 2 * (n/2) ∣ m * (n/2)
      obtain ⟨q, hq⟩ := h2'
      -- 2 * (n/2) * q = m * (n/2)
      have h_q : ((n / 2 : ℕ) : ℤ) * (2 * q) =
          ((n / 2 : ℕ) : ℤ) * m := by
        calc
          ((n / 2 : ℕ) : ℤ) * (2 * q) = (2 * ((n / 2 : ℕ) : ℤ)) * q := by ring
          _ = m * ((n / 2 : ℕ) : ℤ) := hq.symm
          _ = ((n / 2 : ℕ) : ℤ) * m := by ring
      have h_can : 2 * q = m := mul_left_cancel₀ hn_half_pos_int.ne' h_q
      exact ⟨q, h_can.symm⟩
    obtain ⟨m', hm'⟩ := hm_two_dvd
    -- Define a' := a * d^(-m').
    set a' : A := a * (d : A) ^ (-m') with ha'_def
    -- (a')^2 = a^2 · d^(-2m') = d^m · d^(-2m') = 1 (using abelianness).
    have ha2_eq_zpow : a ^ 2 = (d : A) ^ m := by
      have h := congrArg (fun (x : (D : Subgroup A)) => (x : A)) hm
      simp only [SubgroupClass.coe_zpow] at h
      exact h.symm
    have ha'_sq : a' ^ 2 = 1 := by
      have hab : ∀ u v : A, u * v = v * u := hAb
      have h_expand : a' * a' = a * a * ((d : A) ^ (-m') * (d : A) ^ (-m')) := by
        rw [ha'_def]
        rw [mul_assoc, ← mul_assoc ((d : A) ^ (-m')) a, hab ((d : A) ^ (-m')) a]
        rw [mul_assoc, ← mul_assoc]
      rw [pow_two, h_expand, ← pow_two, ← pow_two, ha2_eq_zpow]
      have h_neg_sq : ((d : A) ^ (-m')) ^ 2 =
          (d : A) ^ ((-m') * 2 : ℤ) := by
        rw [← zpow_natCast ((d : A) ^ (-m')) 2, ← zpow_mul]
        ring_nf
      rw [h_neg_sq]
      rw [← zpow_add]
      have h_exp : m + (-m') * 2 = 0 := by rw [hm']; ring
      rw [h_exp, zpow_zero]
    -- a' ∉ D.
    have ha'_notmem : a' ∉ D := by
      intro hin
      have h_d_inv : (d : A) ^ (-m') ∈ D := zpow_mem d.2 _
      have h_a : a ∈ D := by
        have : a = a' * ((d : A) ^ (-m'))⁻¹ := by
          rw [ha'_def, mul_assoc, mul_inv_cancel, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ hin (Subgroup.inv_mem _ h_d_inv)
      exact ha_notmem h_a
    have ha'_in_K : a' ∈ K := ha'_sq
    -- K has at least 4 elements: 1, z, a', a'*z. Need them all distinct.
    -- 1 ≠ z ✓ (hz_ne_one). 1 ∈ D, z ∈ D, a' ∉ D, a'*z ∉ D (else a' = (a'*z)*z⁻¹ ∈ D).
    -- Also a' ≠ a'*z (else z = 1).
    have hz_K_in : z ∈ K := hz_in_K
    have ha'z_in_K : a' * z ∈ K := K.mul_mem ha'_in_K hz_K_in
    have ha'z_notmem : a' * z ∉ D := by
      intro hin
      have hz_in_D' : z ∈ D := hz_in_D
      have : a' ∈ D := by
        have heq : a' = (a' * z) * z⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
        rw [heq]
        exact Subgroup.mul_mem _ hin (Subgroup.inv_mem _ hz_in_D')
      exact ha'_notmem this
    -- Define the four elements as a Finset in K.
    have h_one_in_K : (1 : A) ∈ K := K.one_mem
    -- Now build the cardinality.
    haveI : Fintype K := Fintype.ofFinite _
    let S : Finset K :=
      {⟨1, h_one_in_K⟩, ⟨z, hz_K_in⟩, ⟨a', ha'_in_K⟩, ⟨a' * z, ha'z_in_K⟩}
    have hS_card : S.card = 4 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · -- ⟨a', ..⟩ ∉ {⟨a'*z, ..⟩}
        intro h
        rw [Finset.mem_singleton] at h
        have heq : a' = a' * z := congrArg Subtype.val h
        have hz_eq : z = 1 := by
          have : a' * 1 = a' * z := by rw [mul_one]; exact heq
          exact (mul_left_cancel this).symm
        exact hz_ne_one hz_eq
      · -- ⟨z, ..⟩ ∉ {⟨a', ..⟩, ⟨a'*z, ..⟩}
        intro h
        rw [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · have heq : z = a' := congrArg Subtype.val h
          have : a' ∈ D := heq ▸ hz_in_D
          exact ha'_notmem this
        · have heq : z = a' * z := congrArg Subtype.val h
          have : a' * z ∈ D := heq ▸ hz_in_D
          exact ha'z_notmem this
      · -- ⟨1, ..⟩ ∉ {⟨z, ..⟩, ⟨a', ..⟩, ⟨a'*z, ..⟩}
        intro h
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · have heq : (1 : A) = z := congrArg Subtype.val h
          exact hz_ne_one heq.symm
        · have heq : (1 : A) = a' := congrArg Subtype.val h
          have : a' ∈ D := heq ▸ D.one_mem
          exact ha'_notmem this
        · have heq : (1 : A) = a' * z := congrArg Subtype.val h
          have : a' * z ∈ D := heq ▸ D.one_mem
          exact ha'z_notmem this
    have h_K_ge_4 : 4 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      have := Finset.card_le_univ S
      omega
    omega

/-- **Isaacs Lemma 6.15** (`p = 2` abelian index-two branch).

If `A` is a finite abelian `2`-group with a cyclic subgroup of index `2`, and `A` is
not cyclic, then `A` contains a characteristic elementary abelian subgroup of order `4`.

This is the standalone `p = 2` sub-lemma used in the full Lemma 6.15 proof and in the
later `p`-group classification route toward Isaacs 6.11. -/
theorem exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group
    {A : Type*} [Group A] [Finite A] (hAb : ∀ x y : A, x * y = y * x)
    (h_two : IsPGroup 2 A)
    {D : Subgroup A} (hD_cyc : IsCyclic D) (hD_idx : D.index = 2)
    (h_not_cyclic : ¬ IsCyclic A) :
    ∃ K : Subgroup A, K.Characteristic ∧
      IsElementaryAbelian 2 K ∧ Nat.card K = 4 :=
  char_elementaryAbelian_4_of_noncyclic_abelian_2group
    hAb h_two hD_cyc hD_idx h_not_cyclic

/-- **Isaacs Lemma 6.15** (`p = 2` quotient lift setup).

Under the `p = 2` hypotheses through the first quotient step, applying the abelian index-two
branch to `T/T'` produces a characteristic subgroup upstairs whose image in `T/T'` is elementary
abelian of order `4`. -/
theorem exists_characteristic_lift_quotient_commutator_four_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 := by
  let D : Subgroup (T ⧸ _root_.commutator T) :=
    C.map (QuotientGroup.mk' (_root_.commutator T))
  have hD : IsCyclic D ∧ D.index = 2 := by
    simpa [D] using
      quotient_commutator_image_cyclic_index_two_of_center_index_four
        h_idx hC_cyclic hC_lt_T hZ_lt_C
  have hQ_ab : ∀ x y : T ⧸ _root_.commutator T, x * y = y * x :=
    quotient_commutator_commutative
  have hQ_two : IsPGroup 2 (T ⧸ _root_.commutator T) :=
    hT_two.to_quotient (_root_.commutator T)
  have hQ_not_cyclic : ¬ IsCyclic (T ⧸ _root_.commutator T) :=
    quotient_commutator_not_isCyclic_of_center_index_prime_sq h_idx
  obtain ⟨K, hK_char, hK_elem, hK_card⟩ :=
    exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group
      (A := T ⧸ _root_.commutator T) hQ_ab hQ_two
      (D := D) hD.1 hD.2 hQ_not_cyclic
  let E : Subgroup T := K.comap (QuotientGroup.mk' (_root_.commutator T))
  have hE_map :
      E.map (QuotientGroup.mk' (_root_.commutator T)) = K := by
    dsimp [E]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (_root_.commutator T)) K
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · dsimp [E]
    exact Subgroup.Characteristic.comap_quotient_mk hK_char
  · intro x hx
    dsimp [E]
    change (x : T ⧸ _root_.commutator T) ∈ K
    rw [show (x : T ⧸ _root_.commutator T) = 1 from
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact K.one_mem
  · rwa [hE_map]
  · rwa [hE_map]

/-- **Isaacs Lemma 6.15** (`p = 2` lift cardinality).

If a subgroup `E` contains `T'` and its image in `T/T'` has order `4`, then in the
Lemma 6.15 `p = 2` setup `E` has order `8`. -/
theorem card_lift_quotient_commutator_eq_eight_of_center_index_four
    {T : Type*} [Group T] [Finite T]
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C E : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C)
    (hcomm_le_E : _root_.commutator T ≤ E)
    (hE_image_card :
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4) :
    Nat.card E = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : C.Normal :=
    normal_of_center_le_of_center_index_pow_two (p := 2) h_idx hZ_lt_C.le
  have hcomm_card : Nat.card (_root_.commutator T) = 2 :=
    card_commutator_eq_prime_of_lem_6_15
      (p := 2) h_idx hC_cyclic hC_lt_T hZ_lt_C
  have hquot_card :
      Nat.card (E ⧸ (_root_.commutator T).subgroupOf E) = 4 := by
    rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map
      (_root_.commutator T) E]
    exact hE_image_card
  have hsub_card :
      Nat.card ((_root_.commutator T).subgroupOf E) = 2 := by
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hcomm_le_E).toEquiv).trans hcomm_card
  have hsplit :
      Nat.card E =
        Nat.card (E ⧸ (_root_.commutator T).subgroupOf E) *
          Nat.card ((_root_.commutator T).subgroupOf E) :=
    ((_root_.commutator T).subgroupOf E).card_eq_card_quotient_mul_card_subgroup
  rw [hquot_card, hsub_card] at hsplit
  norm_num at hsplit
  exact hsplit

/-- **Isaacs Lemma 6.15** (`p = 2` first lifted subgroup).

The first application of the abelian index-two branch to `T/T'` yields a characteristic
subgroup `E ≤ T` whose quotient image is elementary abelian of order `4`, and whose own
order is `8`. -/
theorem exists_lift_quotient_commutator_order_eight_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 ∧
      Nat.card E = 8 := by
  obtain ⟨E, hE_char, hcomm_le_E, hE_elem, hE_image_card⟩ :=
    exists_characteristic_lift_quotient_commutator_four_of_center_index_four
      hT_two h_idx hC_cyclic hC_lt_T hZ_lt_C
  exact ⟨E, hE_char, hcomm_le_E, hE_elem, hE_image_card,
    card_lift_quotient_commutator_eq_eight_of_center_index_four
      h_idx hC_cyclic hC_lt_T hZ_lt_C hcomm_le_E hE_image_card⟩

/-- A finite elementary abelian `2`-group of order `4` is not cyclic. -/
private lemma not_isCyclic_of_isElementaryAbelian_two_card_four
    {A : Type*} [Group A] [Finite A]
    (hElem : IsElementaryAbelian 2 A) (hCard : Nat.card A = 4) :
    ¬ IsCyclic A := by
  exact hElem.not_isCyclic_of_card_prime_sq Nat.prime_two (by simpa using hCard)

/-- If a quotient image of `E` is elementary abelian of order `4`, then `E` is not cyclic. -/
private lemma not_isCyclic_of_quotient_commutator_image_four
    {T : Type*} [Group T] [Finite T] {E : Subgroup T}
    (hE_image_elem :
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))))
    (hE_image_card :
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4) :
    ¬ IsCyclic E := by
  have hImage_not :
      ¬ IsCyclic (E.map (QuotientGroup.mk' (_root_.commutator T))) :=
    not_isCyclic_of_isElementaryAbelian_two_card_four
      hE_image_elem hE_image_card
  intro hE_cyclic
  haveI : IsCyclic E := hE_cyclic
  exact hImage_not (isCyclic_of_surjective
    ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap E)
    ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap_surjective E))

/-- The intersection of a subgroup with a cyclic subgroup, viewed inside the former, is cyclic. -/
private lemma subgroupOf_isCyclic_of_isCyclic
    {T : Type*} [Group T] {C E : Subgroup T} (hC_cyclic : IsCyclic C) :
    IsCyclic (C.subgroupOf E) := by
  haveI : IsCyclic C := hC_cyclic
  let f : C.subgroupOf E →* C := {
    toFun := fun x => ⟨((x : C.subgroupOf E) : E), by
      have hx : ((x : C.subgroupOf E) : E) ∈ C.subgroupOf E := x.2
      rwa [Subgroup.mem_subgroupOf] at hx⟩
    map_one' := by ext; rfl
    map_mul' := by intro x y; ext; rfl
  }
  exact isCyclic_of_injective f (by
    intro x y hxy
    apply Subtype.ext
    have hT :
        (((x : C.subgroupOf E) : E) : T) =
          (((y : C.subgroupOf E) : E) : T) := by
      simpa [f] using congrArg Subtype.val hxy
    exact Subtype.ext hT)

/-- If `C` has index `2` in `T` and `E` is not contained in `C`, then `C ∩ E` has
index `2` in `E`. -/
private lemma relIndex_eq_two_of_index_two_of_not_le
    {T : Type*} [Group T] {C E : Subgroup T}
    (hC_idx : C.index = 2) (hE_not_le_C : ¬ E ≤ C) :
    C.relIndex E = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  rw [SetLike.le_def] at hE_not_le_C
  push Not at hE_not_le_C
  obtain ⟨a, haE, haC⟩ := hE_not_le_C
  refine ⟨a, haE, haC, ?_⟩
  intro b _hbE
  by_cases hbC : b ∈ C
  · exact Or.inr hbC
  · left
    rw [Subgroup.mul_mem_iff_of_index_two hC_idx]
    exact iff_of_false hbC haC

/-- If `C` has index `2`, then any subgroup properly between `C` and `⊤` is impossible. -/
private lemma not_ge_of_ne_of_ne_top_of_index_two
    {T : Type*} [Group T] [Finite T] {C E : Subgroup T}
    (hC_idx : C.index = 2) (hE_ne_C : E ≠ C) (hE_ne_top : E ≠ ⊤) :
    ¬ C ≤ E := by
  intro hC_le_E
  have hmul : C.relIndex E * E.index = 2 := by
    rw [Subgroup.relIndex_mul_index hC_le_E, hC_idx]
  have hrel_pos : 0 < C.relIndex E := by
    exact Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
  have hidx_pos : 0 < E.index := by
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := E))
  have hcases : C.relIndex E = 1 ∨ E.index = 1 := by
    by_contra h
    push Not at h
    have hrel_ge_two : 2 ≤ C.relIndex E := by omega
    have hidx_ge_two : 2 ≤ E.index := by omega
    have hprod_ge : 4 ≤ C.relIndex E * E.index :=
      Nat.mul_le_mul hrel_ge_two hidx_ge_two
    omega
  rcases hcases with hrel | hidx
  · have hE_le_C : E ≤ C := Subgroup.relIndex_eq_one.mp hrel
    exact hE_ne_C (le_antisymm hE_le_C hC_le_E)
  · exact hE_ne_top (Subgroup.index_eq_one.mp hidx)

/-- Finite subgroup cardinality strictly drops for a proper subgroup. -/
private lemma subgroup_card_lt_of_lt_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H < ⊤) :
    Nat.card H < Nat.card G := by
  have h_dvd : Nat.card H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le : Nat.card H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne : Nat.card H ≠ Nat.card G := fun heq =>
    hH.ne (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le h_ne

/-- In a finite cyclic group, the subgroup cut out by `x ^ |K| = 1` is exactly `K`. -/
private lemma mem_of_pow_card_eq_one_of_isCyclic_subgroup
    {A : Type*} [Group A] [Finite A] (hA_cyclic : IsCyclic A)
    (K : Subgroup A) {x : A} (hx : x ^ Nat.card K = 1) :
    x ∈ K := by
  classical
  haveI : IsCyclic A := hA_cyclic
  haveI : Fintype A := Fintype.ofFinite A
  letI : CommGroup A := IsCyclic.commGroup
  let P : Subgroup A := {
    carrier := {x | x ^ Nat.card K = 1}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      change (x * y) ^ Nat.card K = 1
      rw [mul_pow, hx, hy, mul_one]
    inv_mem' := by
      intro x hx
      change x⁻¹ ^ Nat.card K = 1
      rw [inv_pow, hx, inv_one]
  }
  have hK_le_P : K ≤ P := by
    intro y hy
    dsimp [P]
    have h_sub :
        (⟨y, hy⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h_sub
  have hP_card_le : Nat.card P ≤ Nat.card K := by
    haveI : Fintype P := Fintype.ofFinite P
    have hroot :=
      (IsCyclic.card_pow_eq_one_le (α := A) (n := Nat.card K) Nat.card_pos)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    dsimp [P]
    rw [Fintype.card_subtype]
    simpa [Nat.card_eq_fintype_card] using hroot
  have hKP : K = P := Subgroup.eq_of_le_of_card_ge hK_le_P hP_card_le
  rw [hKP]
  exact hx

/-- In a finite cyclic `2`-group, every proper subgroup lies in any subgroup of index `2`. -/
private lemma le_index_two_subgroup_of_lt_top_of_cyclic_two_group
    {A : Type*} [Group A] [Finite A] (hA_two : IsPGroup 2 A) (hA_cyclic : IsCyclic A)
    {Z H : Subgroup A} (hZ_idx : Z.index = 2) (hH_lt_top : H < ⊤) :
    H ≤ Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨kA, hA_card⟩ := (IsPGroup.iff_card (p := 2) (G := A)).mp hA_two
  obtain ⟨kH, hH_card⟩ := (IsPGroup.iff_card (p := 2) (G := H)).mp
    (hA_two.to_subgroup H)
  obtain ⟨kZ, hZ_card⟩ := (IsPGroup.iff_card (p := 2) (G := Z)).mp
    (hA_two.to_subgroup Z)
  have hZ_mul : 2 * Nat.card Z = Nat.card A := by
    simpa [hZ_idx] using Z.index_mul_card
  have hkA_eq : kA = kZ + 1 := by
    have hpow : 2 ^ (kZ + 1) = 2 ^ kA := by
      calc
        2 ^ (kZ + 1) = 2 * 2 ^ kZ := by
          rw [pow_succ']
        _ = 2 * Nat.card Z := by rw [hZ_card]
        _ = Nat.card A := hZ_mul
        _ = 2 ^ kA := hA_card
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow.symm
  have hH_card_lt : Nat.card H < Nat.card A :=
    subgroup_card_lt_of_lt_top hH_lt_top
  have hkH_lt_A : kH < kA := by
    have hpow : 2 ^ kH < 2 ^ kA := by
      rw [← hH_card, ← hA_card]
      exact hH_card_lt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have hkH_le_Z : kH ≤ kZ := by omega
  have hH_dvd_Z : Nat.card H ∣ Nat.card Z := by
    rw [hH_card, hZ_card]
    exact pow_dvd_pow 2 hkH_le_Z
  intro x hx
  have hx_order_dvd_H : orderOf x ∣ Nat.card H :=
    H.orderOf_dvd_natCard hx
  have hx_order_dvd_Z : orderOf x ∣ Nat.card Z :=
    dvd_trans hx_order_dvd_H hH_dvd_Z
  exact mem_of_pow_card_eq_one_of_isCyclic_subgroup hA_cyclic Z
    (orderOf_dvd_iff_pow_eq_one.mp hx_order_dvd_Z)

/-- If a central subgroup has index `2`, then the ambient group is abelian. -/
private lemma commutative_of_central_index_two_subgroup
    {A : Type*} [Group A] {D : Subgroup A}
    (hD_le_center : D ≤ Subgroup.center A) (hD_idx : D.index = 2) :
    ∀ x y : A, x * y = y * x := by
  intro x y
  by_cases hxD : x ∈ D
  · have hx_center : x ∈ Subgroup.center A := hD_le_center hxD
    exact (Subgroup.mem_center_iff.mp hx_center y).symm
  by_cases hyD : y ∈ D
  · have hy_center : y ∈ Subgroup.center A := hD_le_center hyD
    exact Subgroup.mem_center_iff.mp hy_center x
  have hxyD : x * y ∈ D := by
    rw [Subgroup.mul_mem_iff_of_index_two hD_idx]
    exact iff_of_false hxD hyD
  have hxy_center : x * y ∈ Subgroup.center A := hD_le_center hxyD
  have hcomm := Subgroup.mem_center_iff.mp hxy_center x
  exact mul_left_cancel (a := x) (by
    calc
      x * (x * y) = x * y * x := hcomm
      _ = x * (y * x) := by rw [mul_assoc])

/-- Restrict an automorphism of `G` to a characteristic subgroup. -/
private def characteristicRestrictMulEquiv
    {G : Type*} [Group G] {H : Subgroup G} (hH : H.Characteristic)
    (φ : G ≃* G) : H ≃* H where
  toFun x := ⟨φ x, by
    have hx : (x : G) ∈ H.comap φ.toMonoidHom := by
      rw [hH.fixed φ]
      exact x.2
    exact hx⟩
  invFun x := ⟨φ.symm x, by
    have hx : (x : G) ∈ H.comap φ.symm.toMonoidHom := by
      rw [hH.fixed φ.symm]
      exact x.2
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    exact φ.symm_apply_apply (x : G)
  right_inv x := by
    apply Subtype.ext
    exact φ.apply_symm_apply (x : G)
  map_mul' x y := by
    apply Subtype.ext
    exact φ.map_mul (x : G) (y : G)

/-- A characteristic subgroup of a characteristic subgroup is characteristic upstairs. -/
private lemma characteristic_map_subtype_of_characteristic
    {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup H}
    (hH : H.Characteristic) (hK : K.Characteristic) :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨x, hxL, rfl⟩ := hy
  rw [Subgroup.mem_map] at hxL
  obtain ⟨k, hkK, rfl⟩ := hxL
  let φH : H ≃* H := characteristicRestrictMulEquiv hH φ
  have hk_image : φH k ∈ K := by
    have hmem_map : φH k ∈ K.map φH.toMonoidHom :=
      Subgroup.mem_map_of_mem φH.toMonoidHom hkK
    exact (Subgroup.characteristic_iff_map_le.mp hK φH) hmem_map
  refine ⟨φH k, hk_image, ?_⟩
  rfl

/-- Elementary abelian structure is transported across a multiplicative equivalence. -/
private lemma isElementaryAbelian_of_mulEquiv
    {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsElementaryAbelian p A) :
    IsElementaryAbelian p B := by
  constructor
  · intro x y
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    simpa using congrArg e (h.1 x' y')
  · intro x
    obtain ⟨x', rfl⟩ := e.surjective x
    simpa using congrArg e (h.2 x')

/-- **Isaacs Lemma 6.15** (`p = 2`, second-step setup).

The lifted subgroup `E` from `T/T'` is noncyclic and has order `8`; moreover
`C ∩ E`, viewed as a subgroup of `E`, is cyclic of index `2`. -/
theorem exists_lift_order_eight_noncyclic_cyclic_index_two_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 ∧
      Nat.card E = 8 ∧
      ¬ IsCyclic E ∧
      IsCyclic (C.subgroupOf E) ∧
      (C.subgroupOf E).index = 2 := by
  obtain ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card⟩ :=
    exists_lift_quotient_commutator_order_eight_of_center_index_four
      hT_two h_idx hC_cyclic hC_lt_T hZ_lt_C
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC_idx : C.index = 2 :=
    index_eq_prime_of_center_lt_of_center_index_pow_two
      (p := 2) h_idx hZ_lt_C hC_lt_T
  have hE_not_cyclic : ¬ IsCyclic E :=
    not_isCyclic_of_quotient_commutator_image_four
      hE_image_elem hE_image_card
  have hE_ne_C : E ≠ C := by
    intro hEq
    apply hE_not_cyclic
    rw [hEq]
    exact hC_cyclic
  have hE_ne_top : E ≠ ⊤ := by
    intro hEq
    apply hT_card_ne
    simpa [hEq] using hE_card
  have hC_not_le_E : ¬ C ≤ E :=
    not_ge_of_ne_of_ne_top_of_index_two hC_idx hE_ne_C hE_ne_top
  have hE_not_le_C : ¬ E ≤ C := by
    intro hE_le_C
    haveI : IsCyclic C := hC_cyclic
    exact hE_not_cyclic (Subgroup.isCyclic_of_le hE_le_C)
  have hCE_idx : (C.subgroupOf E).index = 2 := by
    simpa [Subgroup.relIndex] using
      relIndex_eq_two_of_index_two_of_not_le hC_idx hE_not_le_C
  exact ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card,
    hE_not_cyclic, subgroupOf_isCyclic_of_isCyclic hC_cyclic, hCE_idx⟩

/-- **Isaacs Lemma 6.15** (`p = 2`, lifted subgroup is abelian).

In the second `p = 2` step, the lifted subgroup `E` is noncyclic of order `8`, `C ∩ E`
has index `2` in `E`, and the cyclic `2`-group maximality argument forces `C ∩ E ≤ Z(E)`.
Thus `E` is abelian, matching the corresponding sentence in Isaacs Lemma 6.15. -/
theorem exists_lift_order_eight_noncyclic_abelian_cyclic_index_two_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 ∧
      Nat.card E = 8 ∧
      ¬ IsCyclic E ∧
      (∀ x y : E, x * y = y * x) ∧
      IsCyclic (C.subgroupOf E) ∧
      (C.subgroupOf E).index = 2 := by
  obtain ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card,
    hE_not_cyclic, hCE_cyclic, hCE_idx⟩ :=
    exists_lift_order_eight_noncyclic_cyclic_index_two_of_center_index_four
      hT_two hT_card_ne h_idx hC_cyclic hC_lt_T hZ_lt_C
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC_idx : C.index = 2 :=
    index_eq_prime_of_center_lt_of_center_index_pow_two
      (p := 2) h_idx hZ_lt_C hC_lt_T
  have hE_ne_C : E ≠ C := by
    intro hEq
    apply hE_not_cyclic
    rw [hEq]
    exact hC_cyclic
  have hE_ne_top : E ≠ ⊤ := by
    intro hEq
    apply hT_card_ne
    simpa [hEq] using hE_card
  have hC_not_le_E : ¬ C ≤ E :=
    not_ge_of_ne_of_ne_top_of_index_two hC_idx hE_ne_C hE_ne_top
  have hZ_rel : (Subgroup.center T).relIndex C = 2 := by
    have hmul :
        (Subgroup.center T).relIndex C * C.index = (Subgroup.center T).index := by
      rw [Subgroup.relIndex_mul_index hZ_lt_C.le]
    rw [hC_idx, h_idx] at hmul
    norm_num at hmul
    omega
  have hZC_idx : ((Subgroup.center T).subgroupOf C).index = 2 := by
    simpa [Subgroup.relIndex] using hZ_rel
  have hEC_lt_top : E.subgroupOf C < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    apply hC_not_le_E
    intro x hxC
    have hx_sub : (⟨x, hxC⟩ : C) ∈ E.subgroupOf C := by
      rw [htop]
      trivial
    rwa [Subgroup.mem_subgroupOf] at hx_sub
  have hEC_le_ZC : E.subgroupOf C ≤ (Subgroup.center T).subgroupOf C :=
    le_index_two_subgroup_of_lt_top_of_cyclic_two_group
      (A := C) (hT_two.to_subgroup C) hC_cyclic hZC_idx hEC_lt_top
  have hCE_le_centerE : C.subgroupOf E ≤ Subgroup.center E := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro y
    have heC : ((e : E) : T) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using he
    let eC : C := ⟨((e : E) : T), heC⟩
    have heC_in_EC : eC ∈ E.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact e.2
    have heC_in_ZC : eC ∈ (Subgroup.center T).subgroupOf C :=
      hEC_le_ZC heC_in_EC
    have he_center_T : ((e : E) : T) ∈ Subgroup.center T := by
      simpa [Subgroup.mem_subgroupOf, eC] using heC_in_ZC
    exact Subtype.ext (Subgroup.mem_center_iff.mp he_center_T ((y : E) : T))
  have hE_ab : ∀ x y : E, x * y = y * x :=
    commutative_of_central_index_two_subgroup hCE_le_centerE hCE_idx
  exact ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card,
    hE_not_cyclic, hE_ab, hCE_cyclic, hCE_idx⟩

/-- **Isaacs Lemma 6.15** (`p = 2` branch).

Let `T` be a finite `2`-group with `|T : Z(T)| = 4`, `|T| ≠ 8`, and a cyclic subgroup
`C` with `Z(T) < C < T`. Then `T` contains a characteristic elementary abelian subgroup
of order `4`. -/
theorem exists_characteristic_isElementaryAbelian_four_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian 2 K ∧ Nat.card K = 4 := by
  obtain ⟨E, hE_char, _hcomm_le_E, _hE_image_elem, _hE_image_card, _hE_card,
    hE_not_cyclic, hE_ab, hCE_cyclic, hCE_idx⟩ :=
    exists_lift_order_eight_noncyclic_abelian_cyclic_index_two_of_center_index_four
      hT_two hT_card_ne h_idx hC_cyclic hC_lt_T hZ_lt_C
  obtain ⟨K, hK_char, hK_elem, hK_card⟩ :=
    exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group
      (A := E) hE_ab (hT_two.to_subgroup E)
      (D := C.subgroupOf E) hCE_cyclic hCE_idx hE_not_cyclic
  let L : Subgroup T := K.map E.subtype
  refine ⟨L, ?_, ?_, ?_⟩
  · dsimp [L]
    exact characteristic_map_subtype_of_characteristic hE_char hK_char
  · dsimp [L]
    exact isElementaryAbelian_of_mulEquiv
      (Subgroup.equivMapOfInjective K E.subtype E.subtype_injective) hK_elem
  · dsimp [L]
    rw [Subgroup.card_subtype, hK_card]

/-! ### Lem 6.15 — main dispatch -/

/-- **Isaacs Lemma 6.15**.

Let `T` be a finite `p`-group with order different from `8`, and suppose
`|T : Z(T)| = p²`. If `C` is cyclic and `Z(T) < C < T`, then `T` contains a
characteristic elementary abelian subgroup of order `p²`.

The proof dispatches to the already-formalized odd-prime branch and the separate `p = 2`
center-index-four branch. -/
theorem exists_characteristic_isElementaryAbelian_of_center_index_prime_sq
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  rcases (Fact.out : p.Prime).eq_two_or_odd' with hp_two | hp_odd
  · subst p
    simpa using
      exists_characteristic_isElementaryAbelian_four_of_center_index_four
        hT hT_card_ne h_idx hC_cyclic hC_lt_T hZ_lt_C
  · exact exists_characteristic_isElementaryAbelian_of_center_index_prime_sq_odd
      hp_odd h_idx hC_cyclic hZ_lt_C hC_lt_T

/-- **Isaacs Thm 6.12 setup**: Lemma 6.15 applied to an ambient self-centralizing
subgroup `C ≤ T ≤ P`.

In the proof of Thm 6.12, after choosing `T/C` of order `p`, this packages the
translation from the ambient cyclic self-centralizing subgroup `C : Subgroup P` to the
subgroup `C.subgroupOf T` required by Lemma 6.15. -/
theorem exists_characteristic_isElementaryAbelian_of_self_centralizing_relIndex_prime
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal]
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = p ^ 2)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hC_cyclic : IsCyclic C)
    (hT_not_comm : ¬ IsMulCommutative T) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  have hZ_lt_C : Subgroup.center T < C.subgroupOf T :=
    center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
      hC_le_T hCent hC_rel hT_not_comm
  have hCsub_index : (C.subgroupOf T).index = p := by
    simpa [Subgroup.relIndex] using hC_rel
  have hCsub_lt_top : C.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    have hidx_one : (C.subgroupOf T).index = 1 := by
      rw [htop, Subgroup.index_top]
    exact (Fact.out : p.Prime).ne_one (hCsub_index.symm.trans hidx_one)
  have hCsub_cyclic : IsCyclic (C.subgroupOf T) :=
    subgroupOf_isCyclic_of_isCyclic hC_cyclic
  exact exists_characteristic_isElementaryAbelian_of_center_index_prime_sq
    hT hT_card_ne h_idx hCsub_cyclic hZ_lt_C hCsub_lt_top

/-- **Isaacs Thm 6.12 setup**: Lemma 6.15 applied after the `c^p ∈ Z(T)` index
calculation.

This packages the proof step where `C = ⟨c⟩`, `|T : C| = p`, and `c^p ∈ Z(T)` give
`|T : Z(T)| = p²`, so the characteristic elementary abelian subgroup supplied by
Lemma 6.15 can be invoked. -/
theorem exists_characteristic_isElementaryAbelian_of_zpowers_relIndex_pow_mem_center
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal] {c : P}
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (hC_eq : C = Subgroup.zpowers c) (hcT : c ∈ T)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T)
    (hcp : (⟨c, hcT⟩ : T) ^ p ∈ Subgroup.center T) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  let cT : T := ⟨c, hcT⟩
  have hCsub_eq : C.subgroupOf T = Subgroup.zpowers cT := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [hC_eq] at hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simpa [cT] using hk
    · intro hx
      rw [Subgroup.mem_subgroupOf, hC_eq]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have hk_val := congrArg Subtype.val hk
      simpa [cT] using hk_val
  have hZ_lt_C : Subgroup.center T < C.subgroupOf T :=
    center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
      hC_le_T hCent hC_rel hT_not_comm
  have hZ_lt_zpowers : Subgroup.center T < Subgroup.zpowers cT := by
    simpa [hCsub_eq] using hZ_lt_C
  have hZ_rel_zpowers : (Subgroup.center T).relIndex (Subgroup.zpowers cT) = p :=
    center_relIndex_zpowers_eq_prime_of_pow_mem_center hT hZ_lt_zpowers hcp
  have hZ_rel_C : (Subgroup.center T).relIndex (C.subgroupOf T) = p := by
    simpa [hCsub_eq] using hZ_rel_zpowers
  have h_idx : (Subgroup.center T).index = p ^ 2 :=
    center_index_eq_prime_sq_of_subgroupOf_relIndex_prime hC_rel hZ_lt_C.le hZ_rel_C
  have hC_cyclic : IsCyclic C := by
    rw [hC_eq]
    exact Subgroup.isCyclic_zpowers c
  exact exists_characteristic_isElementaryAbelian_of_self_centralizing_relIndex_prime
    hT hT_card_ne h_idx hC_le_T hCent hC_rel hC_cyclic hT_not_comm

/-- **Isaacs Thm 6.12 setup**: if every normal abelian subgroup of `P` is cyclic, then a
normal subgroup `T` has no characteristic elementary abelian subgroup of order `p²`.

Indeed, such a subgroup is normal in `P` because it is characteristic in `T` and `T ⊴ P`;
as an elementary abelian group of order `p²`, it is not cyclic. -/
theorem not_exists_characteristic_isElementaryAbelian_card_prime_sq_of_normal_abelian_cyclic
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] {T : Subgroup P}
    (hT_normal : T.Normal)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B) :
    ¬ ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  rintro ⟨K, hK_char, hK_elem, hK_card⟩
  let B : Subgroup P := K.map T.subtype
  haveI : T.Normal := hT_normal
  haveI : K.Characteristic := hK_char
  have hB_normal : B.Normal := by
    dsimp [B]
    infer_instance
  have hB_elem : IsElementaryAbelian p B := by
    dsimp [B]
    exact isElementaryAbelian_of_mulEquiv
      (Subgroup.equivMapOfInjective K T.subtype T.subtype_injective) hK_elem
  have hB_comm : IsMulCommutative B := ⟨⟨fun x y => hB_elem.comm x y⟩⟩
  have hB_card : Nat.card B = p ^ 2 := by
    dsimp [B]
    rw [Subgroup.card_subtype, hK_card]
  exact (hB_elem.not_isCyclic_of_card_prime_sq (Fact.out : p.Prime) hB_card)
    (hcyc B hB_normal hB_comm)

/-- **Isaacs Thm 6.12 setup**: under the normal-abelian-cyclic hypothesis, the element
`c^p` is not central in `T` in the main 6.12 configuration.

This is the sentence in the proof of Theorem 6.12 where Lemma 6.15 is applied by
contradiction: if `c^p ∈ Z(T)`, the preceding bridge produces a characteristic elementary
abelian subgroup of `T` of order `p²`, contradicting the ambient hypothesis. -/
theorem pow_not_mem_center_of_zpowers_relIndex_of_normal_abelian_cyclic
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal] {c : P}
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (hT_normal : T.Normal)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (hC_eq : C = Subgroup.zpowers c) (hcT : c ∈ T)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T) :
    (⟨c, hcT⟩ : T) ^ p ∉ Subgroup.center T := by
  intro hcp
  have h_exists :
      ∃ K : Subgroup T, K.Characteristic ∧
        IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 :=
    exists_characteristic_isElementaryAbelian_of_zpowers_relIndex_pow_mem_center
      hT hT_card_ne hC_eq hcT hC_le_T hCent hC_rel hT_not_comm hcp
  exact
    (not_exists_characteristic_isElementaryAbelian_card_prime_sq_of_normal_abelian_cyclic
      hT_normal hcyc) h_exists

/-! ### The conjugation congruence step in Theorem 6.12 -/

/-- **Isaacs Thm 6.12 setup**: if conjugation by `a` sends `c` to `c^i`, then it sends
`c^k` to `c^(i*k)`. -/
private lemma conj_zpow_eq_zpow_mul_of_conj_eq_zpow
    {G : Type*} [Group G] {a c : G} {i k : ℤ}
    (h_conj : a * c * a⁻¹ = c ^ i) :
    a * c ^ k * a⁻¹ = c ^ (i * k) := by
  have hmap : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
    simp
  rw [hmap, h_conj, zpow_mul]

/-- **Isaacs Thm 6.12 setup**: iterating the conjugation exponent. -/
private lemma conj_pow_eq_zpow_pow_of_conj_eq_zpow
    {G : Type*} [Group G] {a c : G} {i : ℤ}
    (h_conj : a * c * a⁻¹ = c ^ i) (n : ℕ) :
    a ^ n * c * (a ^ n)⁻¹ = c ^ (i ^ n : ℤ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        a ^ (n + 1) * c * (a ^ (n + 1))⁻¹ =
            a * (a ^ n * c * (a ^ n)⁻¹) * a⁻¹ := by
          rw [pow_succ']
          group
        _ = a * c ^ (i ^ n : ℤ) * a⁻¹ := by rw [ih]
        _ = c ^ (i * (i ^ n : ℤ)) :=
          conj_zpow_eq_zpow_mul_of_conj_eq_zpow h_conj
        _ = c ^ (i ^ (n + 1) : ℤ) := by
          congr 1
          rw [pow_succ']

/-- **Isaacs Thm 6.12 setup**: if `aC = (bC)^2` in `P/C`, and conjugation by
`a` and `b` sends `c` to `c^i` and `c^j`, respectively, then `i ≡ j² (mod |c|)`.

This is the square-root bridge used after the cyclic quotient step: an element of `C = ⟨c⟩`
commutes with every power of `c`, so replacing `a` by a representative `c^m * b²` makes
conjugation by `a` agree with conjugation by `b²` on `c`. -/
theorem conj_exponent_modEq_sq_of_quotient_sq_eq
    {P : Type*} [Group P] {C : Subgroup P} [C.Normal] {a b c : P} {i j : ℤ}
    (hC_eq : C = Subgroup.zpowers c)
    (hquot : QuotientGroup.mk' C a = (QuotientGroup.mk' C b) ^ 2)
    (h_conj_a : a * c * a⁻¹ = c ^ i)
    (h_conj_b : b * c * b⁻¹ = c ^ j) :
    i ≡ j ^ 2 [ZMOD orderOf c] := by
  classical
  have hquot' : QuotientGroup.mk' C a = QuotientGroup.mk' C (b ^ 2) := by
    simpa [QuotientGroup.mk_pow] using hquot
  have hdiv : a / b ^ 2 ∈ C :=
    (QuotientGroup.eq_iff_div_mem (N := C)).mp hquot'
  have hz_mem : a / b ^ 2 ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using hdiv
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz_mem
  have ha_eq : a = c ^ m * b ^ 2 := by
    calc
      a = (a / b ^ 2) * b ^ 2 := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
      _ = c ^ m * b ^ 2 := by rw [← hm]
  have hb2_conj : b ^ 2 * c * (b ^ 2)⁻¹ = c ^ (j ^ 2 : ℤ) :=
    conj_pow_eq_zpow_pow_of_conj_eq_zpow h_conj_b 2
  have hsame : a * c * a⁻¹ = b ^ 2 * c * (b ^ 2)⁻¹ := by
    rw [ha_eq]
    calc
      (c ^ m * b ^ 2) * c * (c ^ m * b ^ 2)⁻¹ =
          c ^ m * (b ^ 2 * c * (b ^ 2)⁻¹) * (c ^ m)⁻¹ := by
        group
      _ = c ^ m * c ^ (j ^ 2 : ℤ) * (c ^ m)⁻¹ := by rw [hb2_conj]
      _ = c ^ (j ^ 2 : ℤ) := by
        have hcomm : Commute (c ^ m) (c ^ (j ^ 2 : ℤ)) :=
          (Commute.zpow_self c m).zpow_right (j ^ 2 : ℤ)
        rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
      _ = b ^ 2 * c * (b ^ 2)⁻¹ := hb2_conj.symm
  have hpow_eq : c ^ i = c ^ (j ^ 2 : ℤ) := by
    rw [← h_conj_a, hsame, hb2_conj]
  rw [← zpow_eq_zpow_iff_modEq]
  exact hpow_eq

/-- **Isaacs Thm 6.12 setup**: if `a^p ∈ ⟨c⟩` and conjugation by `a` sends `c` to
`c^i`, then `i^p ≡ 1 (mod |c|)`.

In the proof of Theorem 6.12 this is the line `c = c^{a^p} = c^{i^p}`. -/
theorem conj_exponent_pow_modEq_one_of_pow_mem_zpowers
    {G : Type*} [Group G] {p e : ℕ} {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (ha_pow : a ^ p ∈ Subgroup.zpowers c) :
    i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)] := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha_pow
  have hcomm : a ^ p * c * (a ^ p)⁻¹ = c := by
    rw [← hm]
    have hzc : c ^ m * c = c * c ^ m := (Commute.zpow_self c m).eq
    calc
      c ^ m * c * (c ^ m)⁻¹ = c * c ^ m * (c ^ m)⁻¹ := by rw [hzc]
      _ = c := by simp [mul_assoc]
  have hiter : a ^ p * c * (a ^ p)⁻¹ = c ^ (i ^ p : ℤ) :=
    conj_pow_eq_zpow_pow_of_conj_eq_zpow h_conj p
  have hpow_eq : c ^ (i ^ p : ℤ) = c := hiter.symm.trans hcomm
  have hmod : i ^ p ≡ (1 : ℤ) [ZMOD orderOf c] := by
    rw [← zpow_eq_zpow_iff_modEq]
    simpa using hpow_eq
  simpa [h_order] using hmod

/-- **Isaacs Thm 6.12 setup**: if conjugation by `a` does not fix `c^p`, the exponent `i`
cannot be `1` modulo `p^(e-1)`. -/
theorem conj_exponent_not_modEq_one_of_pow_conj_ne
    {G : Type*} [Group G] {p e : ℕ} (he : 0 < e)
    {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p) :
    ¬ i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] := by
  intro hmod
  have hmod_mul : i * (p : ℤ) ≡ (p : ℤ) [ZMOD ((p : ℤ) ^ e)] := by
    obtain ⟨m, hm⟩ := hmod.symm.dvd
    refine Int.modEq_iff_dvd.mpr ?_
    refine ⟨-m, ?_⟩
    have hpow : (p : ℤ) ^ e = (p : ℤ) ^ (e - 1) * (p : ℤ) := by
      rw [← pow_succ, Nat.sub_add_cancel he]
    calc
      (p : ℤ) - i * (p : ℤ)
          = -((i - 1) * (p : ℤ)) := by ring
      _ = -(((p : ℤ) ^ (e - 1) * m) * (p : ℤ)) := by rw [hm]
      _ = ((p : ℤ) ^ e) * -m := by
        rw [hpow]
        ring
  have hmod_order : i * (p : ℤ) ≡ (p : ℤ) [ZMOD orderOf c] := by
    simpa [h_order] using hmod_mul
  have hfix : a * c ^ p * a⁻¹ = c ^ p := by
    calc
      a * c ^ p * a⁻¹ = a * c ^ (p : ℤ) * a⁻¹ := by rw [zpow_natCast]
      _ = c ^ (i * (p : ℤ)) :=
        conj_zpow_eq_zpow_mul_of_conj_eq_zpow h_conj
      _ = c ^ (p : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq]
        exact hmod_order
      _ = c ^ p := by rw [zpow_natCast]
  exact hpow_ne hfix

/-- **Isaacs Thm 6.12 setup**: the Lemma 6.16 dispatch for the conjugation exponent.

From `a^p ∈ ⟨c⟩`, conjugation by `a` as `c ↦ c^i`, and non-fixity of `c^p`, Lemma 6.16
forces `p = 2` and leaves only the two `2`-adic alternatives for `i`. -/
theorem conj_exponent_two_cases_of_pow_mem_zpowers_of_pow_conj_ne
    {G : Type*} [Group G] {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (ha_pow : a ^ p ∈ Subgroup.zpowers c)
    (hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p) :
    p = 2 ∧
      (i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) := by
  have hpow_mod : i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)] :=
    conj_exponent_pow_modEq_one_of_pow_mem_zpowers h_order h_conj ha_pow
  have hnot_mod :
      ¬ i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] :=
    conj_exponent_not_modEq_one_of_pow_conj_ne he h_order h_conj hpow_ne
  rcases pow_prime_modEq_one_cases hp he hpow_mod with hmod_one | htwo | htwo
  · exact (hnot_mod hmod_one).elim
  · exact ⟨htwo.1, Or.inl htwo.2⟩
  · exact ⟨htwo.1, Or.inr htwo.2⟩

/-- **Isaacs Thm 6.12 setup**: both `2`-adic alternatives from Lemma 6.16 make
`i * 2 ≡ -2 (mod 2^e)`. -/
private lemma mul_two_modEq_neg_two_of_two_adic_conj_cases
    {e : ℕ} (he : 0 < e) {i : ℤ}
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    i * (2 : ℤ) ≡ (-2 : ℤ) [ZMOD ((2 : ℤ) ^ e)] := by
  rcases hcases with hi | hi
  · simpa using hi.mul_right (2 : ℤ)
  · have hrhs :
        ((2 : ℤ) ^ (e - 1) - 1) * (2 : ℤ) ≡
          (-2 : ℤ) [ZMOD ((2 : ℤ) ^ e)] := by
      refine Int.modEq_iff_dvd.mpr ?_
      refine ⟨-1, ?_⟩
      have hpow : (2 : ℤ) ^ e = (2 : ℤ) ^ (e - 1) * (2 : ℤ) := by
        rw [← pow_succ, Nat.sub_add_cancel he]
      rw [hpow]
      ring
    exact (hi.mul_right (2 : ℤ)).trans hrhs

/-- **Isaacs Thm 6.12 setup**: after the Lemma 6.16 dispatch, conjugation by `a`
inverts `c^2`.

This formalizes the sentence following the congruence computation in the proof of Theorem 6.12:
`i ≡ -1 (mod 2^(e-1))`, hence `(c^2)^a = (c^2)⁻¹`. -/
theorem conj_square_eq_inv_of_pow_mem_zpowers_of_pow_conj_ne
    {G : Type*} [Group G] {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (ha_pow : a ^ p ∈ Subgroup.zpowers c)
    (hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p) :
    p = 2 ∧ a * c ^ 2 * a⁻¹ = (c ^ 2)⁻¹ := by
  obtain ⟨hp_eq_two, hcases⟩ :=
    conj_exponent_two_cases_of_pow_mem_zpowers_of_pow_conj_ne
      hp he h_order h_conj ha_pow hpow_ne
  refine ⟨hp_eq_two, ?_⟩
  have hmod_two :
      i * (2 : ℤ) ≡ (-2 : ℤ) [ZMOD ((2 : ℤ) ^ e)] :=
    mul_two_modEq_neg_two_of_two_adic_conj_cases he hcases
  have hmod_order : i * (2 : ℤ) ≡ (-2 : ℤ) [ZMOD orderOf c] := by
    simpa [h_order, hp_eq_two] using hmod_two
  have hzpow : a * c ^ (2 : ℤ) * a⁻¹ = (c ^ (2 : ℤ))⁻¹ := by
    calc
      a * c ^ (2 : ℤ) * a⁻¹ = c ^ (i * (2 : ℤ)) :=
        conj_zpow_eq_zpow_mul_of_conj_eq_zpow h_conj
      _ = c ^ (-2 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq]
        exact hmod_order
      _ = (c ^ (2 : ℤ))⁻¹ := by rw [zpow_neg]
  simpa [zpow_ofNat] using hzpow

/-- **Isaacs Thm 6.12 setup**: the two `2`-adic alternatives from Lemma 6.16 are
exactly the inversion and semidihedral-twist conjugation alternatives used by Lemma 6.13. -/
theorem conj_eq_inv_or_twist_of_two_adic_cases
    {G : Type*} [Group G] {c a : G} {e : ℕ} {i : ℤ}
    (h_order : orderOf c = 2 ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    a * c * a⁻¹ = c⁻¹ ∨
      a * c * a⁻¹ = c ^ (2 ^ (e - 1)) * c⁻¹ := by
  rcases hcases with hi | hi
  · left
    have hpow : c ^ i = c ^ (-1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq]
      simpa [h_order] using hi
    calc
      a * c * a⁻¹ = c ^ i := h_conj
      _ = c ^ (-1 : ℤ) := hpow
      _ = c⁻¹ := by rw [zpow_neg_one]
  · right
    have hpow : c ^ i = c ^ ((2 : ℤ) ^ (e - 1) - 1) := by
      rw [zpow_eq_zpow_iff_modEq]
      simpa [h_order] using hi
    have hpow_cast : ((2 : ℤ) ^ (e - 1)) = ((2 ^ (e - 1) : ℕ) : ℤ) := by
      norm_num
    calc
      a * c * a⁻¹ = c ^ i := h_conj
      _ = c ^ ((2 : ℤ) ^ (e - 1) - 1) := hpow
      _ = c ^ ((2 : ℤ) ^ (e - 1)) * c⁻¹ := by
        rw [zpow_sub, zpow_one]
      _ = c ^ (2 ^ (e - 1)) * c⁻¹ := by
        rw [hpow_cast, zpow_natCast]

/-- The two 2-adic alternatives in Isaacs Lemma 6.16 cannot be a square modulo `2^e`
when `e ≥ 3`.

The proof reduces modulo `4`: both alternatives are `-1 mod 4`, but no square in
`ZMod 4` is `-1`. -/
private lemma square_root_two_adic_cases_false
    {e : ℕ} (he : 3 ≤ e) {i j : ℤ}
    (hij : i ≡ j ^ 2 [ZMOD ((2 : ℤ) ^ e)])
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    False := by
  have h4_dvd : (4 : ℤ) ∣ (2 : ℤ) ^ e := by
    have hle : 2 ≤ e := le_trans (by norm_num) he
    simpa [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num] using
      pow_dvd_pow (2 : ℤ) hle
  have hij4 : i ≡ j ^ 2 [ZMOD (4 : ℤ)] := hij.of_dvd h4_dvd
  have hi4 : i ≡ -1 [ZMOD (4 : ℤ)] := by
    rcases hcases with hi | hi
    · exact hi.of_dvd h4_dvd
    · have hsemi :
          ((2 : ℤ) ^ (e - 1) - 1) ≡ (-1 : ℤ) [ZMOD (4 : ℤ)] := by
        refine Int.modEq_iff_dvd.mpr ?_
        have hle : 2 ≤ e - 1 := Nat.le_sub_of_add_le he
        have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ (e - 1) := by
          simpa [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num] using
            pow_dvd_pow (2 : ℤ) hle
        convert dvd_neg.mpr h4 using 1
        ring
      exact (hi.of_dvd h4_dvd).trans hsemi
  have hsq : (j ^ 2 : ℤ) ≡ (-1 : ℤ) [ZMOD (4 : ℤ)] :=
    hij4.symm.trans hi4
  have hZcast : ((j ^ 2 : ℤ) : ZMod 4) = (-1 : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff (j ^ 2) (-1) 4).mpr hsq
  have hZ : ((j : ZMod 4) ^ 2) = (-1 : ZMod 4) := by
    simpa using hZcast
  have hbad : ∀ x : ZMod 4, x ^ 2 ≠ (-1 : ZMod 4) := by
    decide
  exact hbad (j : ZMod 4) hZ

/-- **Isaacs Thm 6.12 setup**: in the cyclic quotient branch, the 2-adic conjugation
alternatives force `|P/C| = 2`.

If `P/C` had order larger than `2`, the nontrivial involution `aC` would be a square
`(bC)^2`. Conjugation by `b` on `C = ⟨c⟩` has some exponent `j`, so
`conj_exponent_modEq_sq_of_quotient_sq_eq` gives `i ≡ j² (mod |c|)`. Since the two
2-adic alternatives both reduce to `-1 mod 4`, this is impossible. -/
theorem index_eq_two_of_cyclic_quotient_of_two_adic_conj_cases
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} [C.Normal] {c a : P} {e : ℕ} {i : ℤ}
    (hC_eq : C = Subgroup.zpowers c)
    (hquot_cyclic : IsCyclic (P ⧸ C))
    (h_order : orderOf c = 2 ^ e) (he : 3 ≤ e)
    (ha_notmem : a ∉ C) (ha_sq_mem : a ^ 2 ∈ C)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    C.index = 2 := by
  classical
  rw [Subgroup.index_eq_card]
  by_contra hcard_ne_two
  let q : P ⧸ C := QuotientGroup.mk' C a
  have hq_ne : q ≠ 1 := by
    intro hq_one
    exact ha_notmem ((QuotientGroup.eq_one_iff a).mp hq_one)
  have hq_sq : q ^ 2 = 1 := by
    change ((a : P ⧸ C) ^ 2 = 1)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha_sq_mem
  have hQ : IsPGroup 2 (P ⧸ C) := hP.to_quotient C
  haveI : IsCyclic (P ⧸ C) := hquot_cyclic
  obtain ⟨r, hr_sq⟩ :=
    exists_sq_eq_of_isCyclic_two_group_involution_of_card_ne_two
      (Q := P ⧸ C) hQ hq_ne hq_sq hcard_ne_two
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective C r
  have hquot : QuotientGroup.mk' C a = (QuotientGroup.mk' C b) ^ 2 := by
    rw [hb]
    exact hr_sq.symm
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have hb_conj_mem_C : b * c * b⁻¹ ∈ C := by
    exact (inferInstance : C.Normal).conj_mem c hcC b
  have hb_conj_mem_z : b * c * b⁻¹ ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using hb_conj_mem_C
  obtain ⟨j, h_conj_b_symm⟩ := Subgroup.mem_zpowers_iff.mp hb_conj_mem_z
  have h_conj_b : b * c * b⁻¹ = c ^ j := h_conj_b_symm.symm
  have hij_order : i ≡ j ^ 2 [ZMOD orderOf c] :=
    conj_exponent_modEq_sq_of_quotient_sq_eq hC_eq hquot h_conj h_conj_b
  have hij : i ≡ j ^ 2 [ZMOD ((2 : ℤ) ^ e)] := by
    simpa [h_order] using hij_order
  exact square_root_two_adic_cases_false he hij hcases

/-! ### Lem 6.15 — contradiction forms for the 6.11 route -/

/-- **Isaacs Lemma 6.15**, odd-prime contradiction form.

If a finite `p`-group has a unique subgroup of order `p`, then the odd-prime case of Lemma 6.15
cannot occur: the characteristic elementary abelian subgroup of order `p²` would contain two
distinct subgroups of order `p`. This is one of the exclusion steps in the route from Thm 6.12
to Thm 6.11. -/
theorem false_of_unique_subgroups_card_prime_of_center_index_prime_sq_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (hUnique :
      ∀ K L : Subgroup T, Nat.card K = p → Nat.card L = p → K = L)
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    False := by
  obtain ⟨K, _hK_char, hK_elem, hK_card⟩ :=
    exists_characteristic_isElementaryAbelian_of_center_index_prime_sq_odd
      hp_odd h_idx hC_cyclic hZ_lt_C hC_lt_T
  exact Subgroup.not_exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_unique
    (G := T) (p := p) (Fact.out : p.Prime) hUnique ⟨K, hK_elem, hK_card⟩

/-- **Isaacs Lemma 6.15**, `p = 2` contradiction form.

Under the unique order-`2` subgroup hypothesis, the `p = 2`, `|T| ≠ 8` branch of Lemma 6.15
cannot occur. This packages the part of Isaacs' 6.11 route that rules out the elementary
abelian obstruction produced by the center-index-four argument. -/
theorem false_of_unique_subgroups_card_two_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (hUnique : ∀ K L : Subgroup T, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    False := by
  obtain ⟨K, _hK_char, hK_elem, hK_card⟩ :=
    exists_characteristic_isElementaryAbelian_four_of_center_index_four
      hT_two hT_card_ne h_idx hC_cyclic hC_lt_T hZ_lt_C
  exact Subgroup.not_exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_unique
    (G := T) (p := 2) Nat.prime_two hUnique ⟨K, hK_elem, by
      simpa using hK_card⟩

/-- **Isaacs Lemma 6.15**, contradiction form used in the route to Thm 6.11.

Under the unique order-`p` subgroup hypothesis, the full Lemma 6.15 configuration cannot occur,
because the characteristic elementary abelian subgroup of order `p²` would contain two distinct
subgroups of order `p`. -/
theorem false_of_unique_subgroups_card_prime_of_center_index_prime_sq
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hT : IsPGroup p T)
    (hUnique : ∀ K L : Subgroup T, Nat.card K = p → Nat.card L = p → K = L)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    False := by
  obtain ⟨K, _hK_char, hK_elem, hK_card⟩ :=
    exists_characteristic_isElementaryAbelian_of_center_index_prime_sq
      hT hT_card_ne h_idx hC_cyclic hZ_lt_C hC_lt_T
  exact Subgroup.not_exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_unique
    (G := T) (p := p) (Fact.out : p.Prime) hUnique ⟨K, hK_elem, hK_card⟩

end

end OddOrder.Isaacs.Ch06
