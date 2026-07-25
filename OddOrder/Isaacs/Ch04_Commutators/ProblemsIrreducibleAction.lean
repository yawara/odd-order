/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch04_Commutators.Main.BaerTrick

/-!
# Isaacs Chapter 4 — Problem 4D.3 (真の `A`-不変部分群に自明な coprime 作用)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4D.3 (書籍 p. 145)。

`A` が `G` に coprime に作用し (`A` か `G` の一方は可解), **すべての真の `A`-不変部分群には
自明に作用するが `G` 全体には非自明に作用する**とき (`IsIrreducibleCoprimeAction`),
`G` の構造は強く制限される:

* **(a)** `G` は `p`-群 (`exists_isPGroup`)
* **(b)** `G' ⊆ Z(G)` (`commutator_le_center`)
* (c)–(g) は後続。

## 基本構造

仮説から直ちに `⁅G, A⁆ = G` (`actionCommutator_eq_top`) と,
**`C_G(A)` が唯一の極大 `A`-不変部分群** (`le_fixedPoints_of_ne_top` +
`fixedPoints_ne_top`) が従う。(a) は各素数の `A`-不変 Sylow (Isaacs Thm 3.23(a),
`exists_aInvariant_sylow`) がすべて真部分群だとすると `|G|` が `|C_G(A)|` を割って
しまうことから, (b) は Problem 4C.3 の作用版
(`actionCommutator_le_centralizer_of_trivial_on_normal`) から従う。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4D.3 (p. 145) -/

variable {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}

/-! ### Problem 4C.3 の作用版 -/

/-- **Problem 4C.3 (作用版)**: `A` が `N ⊴ G` に自明に作用するなら `⁅G, A⁆` は `N` を中心化する。

`u := g⁻¹ · (φ a) g` に対し, `g n g⁻¹ ∈ N` の `A`-不変性から
`(φ a) g · n · ((φ a) g)⁻¹ = g n g⁻¹`, すなわち `u n u⁻¹ = n`。`⁅G, A⁆` はこの形の元で
生成される (`actionCommutator_le_iff_left`)。 -/
theorem actionCommutator_le_centralizer_of_trivial_on_normal
    {N : Subgroup G} [N.Normal]
    (htriv : ∀ a : A, ∀ n ∈ N, (φ a) n = n) :
    actionCommutator φ ≤ Subgroup.centralizer (N : Set G) := by
  rw [actionCommutator_le_iff_left]
  intro a g
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hgn : g * n * g⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn g
  have h1 : (φ a) g * n * ((φ a) g)⁻¹ = g * n * g⁻¹ := by
    have h := htriv a _ hgn
    rwa [map_mul, map_mul, map_inv, htriv a n hn] at h
  have hconj : (g⁻¹ * (φ a) g) * n * (g⁻¹ * (φ a) g)⁻¹ = n := by
    rw [mul_inv_rev, inv_inv]
    calc g⁻¹ * (φ a) g * n * (((φ a) g)⁻¹ * g)
        = g⁻¹ * ((φ a) g * n * ((φ a) g)⁻¹) * g := by group
      _ = g⁻¹ * (g * n * g⁻¹) * g := by rw [h1]
      _ = n := by group
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

/-! ### 仮説束 -/

/-- **Problem 4D.3 の仮説**: coprime 作用で「すべての真の `A`-不変部分群には自明に作用するが
`G` 全体には非自明に作用する」。 -/
structure IsIrreducibleCoprimeAction {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) : Prop where
  /-- `(|A|, |G|) = 1`. -/
  coprime : Nat.Coprime (Nat.card A) (Nat.card G)
  /-- `A` か `G` の一方は可解 (Glauberman の補題を使うため). -/
  solvable : IsSolvable A ∨ IsSolvable G
  /-- 真の `A`-不変部分群には自明に作用する. -/
  trivial_on_proper : ∀ H : Subgroup G, Ch03.IsAInvariant φ H → H ≠ ⊤ →
    ∀ a : A, ∀ h ∈ H, (φ a) h = h
  /-- `G` 全体への作用は非自明. -/
  nontrivial : actionCommutator φ ≠ ⊥

namespace IsIrreducibleCoprimeAction

/-- 真の `A`-不変部分群はすべて `C_G(A)` に含まれる. -/
theorem le_fixedPoints_of_ne_top (h : IsIrreducibleCoprimeAction φ) {H : Subgroup G}
    (hinv : Ch03.IsAInvariant φ H) (hne : H ≠ ⊤) :
    H ≤ Subgroup.fixedPointsOfMulAut φ := fun _ hx =>
  Subgroup.mem_fixedPointsOfMulAut.mpr fun a => h.trivial_on_proper H hinv hne a _ hx

/-- `C_G(A) ≠ G` (さもなくば作用が自明になる). -/
theorem fixedPoints_ne_top (h : IsIrreducibleCoprimeAction φ) :
    Subgroup.fixedPointsOfMulAut φ ≠ ⊤ := by
  intro htop
  refine h.nontrivial ((actionCommutator_eq_bot_iff_acts_trivially φ).mpr fun a g => ?_)
  have hg : g ∈ Subgroup.fixedPointsOfMulAut φ := htop ▸ Subgroup.mem_top g
  exact Subgroup.mem_fixedPointsOfMulAut.mp hg a

/-- `G` は非自明 (自明なら作用も自明). -/
theorem nontrivial_group (h : IsIrreducibleCoprimeAction φ) : Nontrivial G := by
  by_contra hcon
  haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hcon
  exact h.nontrivial ((actionCommutator_eq_bot_iff_acts_trivially φ).mpr fun _ _ =>
    Subsingleton.elim _ _)

variable [Finite A] [Finite G]

/-- **`⁅G, A⁆ = G`**: `⁅G, A⁆` は `A`-不変なので, 真部分群なら `A` はその上で自明に作用し,
Lemma 4.28 の系から `⁅G, A⁆ = 1` となって仮定に反する。 -/
theorem actionCommutator_eq_top (h : IsIrreducibleCoprimeAction φ) :
    actionCommutator φ = ⊤ := by
  by_contra hne
  refine h.nontrivial ?_
  refine actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime h.coprime h.solvable ?_
  exact h.trivial_on_proper _ (Ch03.IsAInvariant.actionCommutator φ) hne

/-- **Isaacs Problem 4D.3(a)**: `G` は `p`-群。

各素数 `p` の `A`-不変 Sylow `p`-部分群 (Thm 3.23(a)) が真部分群なら `C_G(A)` に含まれるので,
すべての素数でそうだとすると `|G|` の各素数冪が `|C_G(A)|` を割り `C_G(A) = G` となって
`fixedPoints_ne_top` に反する。 -/
theorem exists_isPGroup (h : IsIrreducibleCoprimeAction φ) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p G := by
  by_contra hcon
  push Not at hcon
  set F : Subgroup G := Subgroup.fixedPointsOfMulAut φ with hF
  have hpow : ∀ p : ℕ, p.Prime → p ^ (Nat.card G).factorization p ∣ Nat.card ↥F := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hPinv⟩ := exists_aInvariant_sylow (φ := φ) h.coprime h.solvable p
    have hPne : (P : Subgroup G) ≠ ⊤ := by
      intro htop
      refine hcon p hp fun g => ?_
      have hg : g ∈ (P : Subgroup G) := htop ▸ Subgroup.mem_top g
      obtain ⟨k, hk⟩ := P.2 (⟨g, hg⟩ : ↥(P : Subgroup G))
      exact ⟨k, congrArg Subtype.val hk⟩
    have hcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
      P.card_eq_multiplicity
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (h.le_fixedPoints_of_ne_top hPinv hPne)
  have hdvd : Nat.card G ∣ Nat.card ↥F := by
    refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr fun p k hp hpk => ?_
    refine dvd_trans (pow_dvd_pow p ?_) (hpow p hp)
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hpk
  have heq : Nat.card ↥F = Nat.card G :=
    Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card F) hdvd
  exact h.fixedPoints_ne_top (Subgroup.eq_top_of_card_eq F heq)

/-- **Isaacs Problem 4D.3(b)**: `G' ⊆ Z(G)`, すなわち `G` の冪零類は `2` 以下。

`G` は (a) より `p`-群なので冪零, したがって `G' ≠ G`。`G'` は特性部分群ゆえ `A`-不変で,
真部分群なので `A` は `G'` 上で自明に作用する。Problem 4C.3 の作用版より
`⁅G, A⁆ ≤ C_G(G')` で, `⁅G, A⁆ = G` (`actionCommutator_eq_top`) だから `G' ≤ Z(G)`。 -/
theorem commutator_le_center (h : IsIrreducibleCoprimeAction φ) :
    _root_.commutator G ≤ Subgroup.center G := by
  haveI := h.nontrivial_group
  obtain ⟨p, hp, hpG⟩ := h.exists_isPGroup
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent G := hpG.isNilpotent
  -- `G' ≠ ⊤` (冪零 + 非自明)
  have hGne : _root_.commutator G ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent G›
    have hall : ∀ m : ℕ, (⊤ : Subgroup G).lowerCentralSeries m = ⊤ := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Subgroup.lowerCentralSeries_succ, ih]; exact htop
    exact (top_ne_bot : (⊤ : Subgroup G) ≠ ⊥) (by rw [← hall n, hn])
  -- `A` は `G'` 上で自明に作用する
  have hinv : Ch03.IsAInvariant φ (_root_.commutator G) :=
    Ch03.IsAInvariant.of_characteristic φ
  have htriv := h.trivial_on_proper _ hinv hGne
  have hle := actionCommutator_le_centralizer_of_trivial_on_normal (φ := φ)
    (N := _root_.commutator G) htriv
  rw [h.actionCommutator_eq_top, top_le_iff] at hle
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer ((_root_.commutator G : Subgroup G) : Set G) := by
    rw [hle]; exact Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm

end IsIrreducibleCoprimeAction

end

end OddOrder.Isaacs.Ch04
