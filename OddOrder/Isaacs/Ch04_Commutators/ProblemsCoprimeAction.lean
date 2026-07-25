/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ProblemsStabilityGroup

/-!
# Isaacs Chapter 4 — Problems 4D (coprime action)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 4D (書籍 p. 145)。

§4C と同様, `A` が `G` に自己同型で作用する状況を **周囲群 `Γ`** (典型的には半直積
`Γ = G ⋊ A`) の部分群 `G`, `A` として述べる。

## 主結果

* **4D.1(a)** `commutator_eq_bot_of_centralizer_le_of_coprime` — `N ⊴ G` が `A`-不変で
  `C_G(N) ⊆ N`, `(|N|, |A|) = 1` のとき, `A` が `N` に自明に作用すれば `G` にも自明に作用する。
* **4D.1(b)** `inf_centralizer_eq_bot_of_centralizer_le_of_coprime` — 同じ状況で `A` が `G` に
  忠実に作用すれば `N` にも忠実に作用する。

⚠ 有限性は仮定していない: 証明は `Nat.card` の規約 (無限群では `0`) のままで通り, `Γ` が
有限の場合が Isaacs の設定になる。

Isaacs の Note: `G` が可解で `N = F(G)`, あるいは `G` が `p`-可解で `O_{p'}(G) = 1`,
`N = O_p(G)` のとき `C_G(N) ⊆ N` が成り立つので, これらの場合には「`A` が `G` に忠実かつ
coprime に作用すれば `N` にも忠実に作用する」が従う。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement Pointwise

section /- Problems 4D: coprime action (p. 145) -/

variable {Γ : Type*} [Group Γ] {G A N : Subgroup Γ}

/-! ### Problem 4D.1 -/

/-- 4D.1 の鍵補題: `N` を中心化する `G ⊔ A` の元で `|A|` 乗が `1` になるものは `A` に入る。

`x = a * g` (`a ∈ A`, `g ∈ G`) と分解すると `a ∈ C_Γ(N)` から `g ∈ C_Γ(N) ⊓ G ≤ N`。
`a` は `N ∋ g` を中心化するので `x ^ |A| = a ^ |A| * g ^ |A| = g ^ |A|`, よって `g` の位数は
`|N|` と `|A|` の両方を割り, 互いに素性から `g = 1`。 -/
theorem mem_of_pow_card_eq_one_of_mem_centralizer [G.Normal]
    (hCG : Subgroup.centralizer (N : Set Γ) ⊓ G ≤ N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥A))
    (hAC : A ≤ Subgroup.centralizer (N : Set Γ))
    {x : Γ} (hxC : x ∈ Subgroup.centralizer (N : Set Γ)) (hxGA : x ∈ G ⊔ A)
    (hxpow : x ^ Nat.card ↥A = 1) : x ∈ A := by
  -- `x = a * g` with `a ∈ A`, `g ∈ G`
  obtain ⟨a, ha, g, hg, rfl⟩ : ∃ a ∈ A, ∃ g ∈ G, a * g = x := by
    have hmem : x ∈ ((A : Set Γ) * (G : Set Γ)) := by
      rw [← Subgroup.mul_normal]
      simpa [sup_comm] using hxGA
    obtain ⟨a, ha, g, hg, hx⟩ := hmem
    exact ⟨a, ha, g, hg, hx⟩
  -- `g` centralizes `N`, hence lies in `N`
  have hgC : g ∈ Subgroup.centralizer (N : Set Γ) := by
    have hrw : g = a⁻¹ * (a * g) := by group
    rw [hrw]
    exact mul_mem (inv_mem (hAC ha)) hxC
  have hgN : g ∈ N := hCG ⟨hgC, hg⟩
  -- `a` and `g` commute (`a` centralizes `N ∋ g`)
  have hcomm : Commute a g := (Subgroup.mem_centralizer_iff.mp (hAC ha) g hgN).symm
  -- `a ^ |A| = 1`, hence `g ^ |A| = 1`
  have hapow : a ^ Nat.card ↥A = 1 := by
    have := pow_card_eq_one' (G := ↥A) (x := (⟨a, ha⟩ : ↥A))
    exact congrArg Subtype.val this
  have hgpow : g ^ Nat.card ↥A = 1 := by
    rw [hcomm.mul_pow, hapow, one_mul] at hxpow
    exact hxpow
  -- the order of `g` divides both `|N|` and `|A|`
  have hdvdN : orderOf g ∣ Nat.card ↥N := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have := pow_card_eq_one' (G := ↥N) (x := (⟨g, hgN⟩ : ↥N))
    exact congrArg Subtype.val this
  have hdvdA : orderOf g ∣ Nat.card ↥A := orderOf_dvd_of_pow_eq_one hgpow
  have hone : orderOf g = 1 :=
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hdvdN hdvdA)
  have hg1 : g = 1 := orderOf_eq_one_iff.mp hone
  simpa [hg1] using ha

/-- 4D.1(a) の核: 上の状況で `G` は `A` を正規化する。

`g ∈ G`, `a ∈ A` に対し `g a g⁻¹` は `C_Γ(N)` (正規) に入り, `G ⊔ A` に入り,
`|A|` 乗が `1` なので鍵補題から `A` に入る。 -/
theorem le_normalizer_of_centralizer_le_of_coprime [G.Normal] [N.Normal]
    (hCG : Subgroup.centralizer (N : Set Γ) ⊓ G ≤ N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥A))
    (hAC : A ≤ Subgroup.centralizer (N : Set Γ)) :
    G ≤ Subgroup.normalizer (A : Set Γ) := by
  refine le_normalizer_of_forall_conj_mem fun g hg a ha => ?_
  refine mem_of_pow_card_eq_one_of_mem_centralizer hCG hcop hAC ?_ ?_ ?_
  · exact (Subgroup.normal_centralizer (H := N)).conj_mem a (hAC ha) g
  · have hgS : g ∈ G ⊔ A := (le_sup_left : G ≤ G ⊔ A) hg
    have haS : a ∈ G ⊔ A := (le_sup_right : A ≤ G ⊔ A) ha
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgS haS) (Subgroup.inv_mem _ hgS)
  · have hpow : (g * a * g⁻¹) ^ Nat.card ↥A = g * a ^ Nat.card ↥A * g⁻¹ := by
      simp [conj_pow]
    rw [hpow]
    have hapow : a ^ Nat.card ↥A = 1 := by
      have := pow_card_eq_one' (G := ↥A) (x := (⟨a, ha⟩ : ↥A))
      exact congrArg Subtype.val this
    simp [hapow]

/-- **Isaacs Problem 4D.1(a)**: `N ⊴ G` が `A`-不変で `C_G(N) ⊆ N`, `(|N|, |A|) = 1` のとき,
`A` が `N` に自明に作用すれば (`⁅N, A⁆ = 1`), `G` にも自明に作用する (`⁅G, A⁆ = 1`)。

`C := C_Γ(N)` を考えると `A ≤ C` で, `C ⊓ G ≤ N` と互いに素性から `G` は `A` を正規化する
(`le_normalizer_of_centralizer_le_of_coprime`)。よって `⁅G, A⁆ ≤ G ⊓ A = 1`。 -/
theorem commutator_eq_bot_of_centralizer_le_of_coprime [G.Normal] [N.Normal]
    (hCG : Subgroup.centralizer (N : Set Γ) ⊓ G ≤ N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥A))
    (hdisj : G ⊓ A = ⊥) (htriv : ⁅N, A⁆ = ⊥) :
    ⁅G, A⁆ = ⊥ := by
  have hAC : A ≤ Subgroup.centralizer (N : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact htriv
  have hnorm := le_normalizer_of_centralizer_le_of_coprime hCG hcop hAC
  have hGA : ⁅G, A⁆ ≤ G ⊓ A := by
    refine le_inf (Subgroup.commutator_le_left G A) ?_
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer hnorm
  rw [hdisj] at hGA
  exact le_bot_iff.mp hGA

/-- **Isaacs Problem 4D.1(b)**: 同じ状況で `A` が `G` に忠実に作用すれば
(`A ⊓ C_Γ(G) = 1`), `N` にも忠実に作用する (`A ⊓ C_Γ(N) = 1`)。

`A₀ := A ⊓ C_Γ(N)` は `N` に自明に作用するので (a) を `A₀` に適用すると `⁅G, A₀⁆ = 1`,
すなわち `A₀ ≤ C_Γ(G)`。忠実性から `A₀ ≤ A ⊓ C_Γ(G) = 1`。 -/
theorem inf_centralizer_eq_bot_of_centralizer_le_of_coprime [G.Normal] [N.Normal]
    (hCG : Subgroup.centralizer (N : Set Γ) ⊓ G ≤ N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥A))
    (hdisj : G ⊓ A = ⊥)
    (hfaithful : A ⊓ Subgroup.centralizer (G : Set Γ) = ⊥) :
    A ⊓ Subgroup.centralizer (N : Set Γ) = ⊥ := by
  set A₀ : Subgroup Γ := A ⊓ Subgroup.centralizer (N : Set Γ) with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hcop₀ : Nat.Coprime (Nat.card ↥N) (Nat.card ↥A₀) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hA₀A) hcop
  have hdisj₀ : G ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff, ← hdisj]
    exact inf_le_inf_left G hA₀A
  have htriv₀ : ⁅N, A₀⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right
  have hbot := commutator_eq_bot_of_centralizer_le_of_coprime (A := A₀) hCG hcop₀ hdisj₀ htriv₀
  have hA₀C : A₀ ≤ Subgroup.centralizer (G : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hbot
  rw [eq_bot_iff, ← hfaithful]
  exact le_inf hA₀A hA₀C

end

end OddOrder.Isaacs.Ch04
