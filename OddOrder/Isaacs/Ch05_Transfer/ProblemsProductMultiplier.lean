/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralCommutatorPower
import OddOrder.GroupTheory.CentralProduct
import OddOrder.Isaacs.Ch05_Transfer.ProblemsSchurMultiplier

/-!
# Isaacs Problem 5A.8(b) — 互いに素な直積の Schur 乗数

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 5A.8(b) (書籍 p. 153):
`|A|` と `|B|` が互いに素なら `M(A × B) ≅ M(A) × M(B)`。

`M(G)` の universal object は未実装 (issue 9206) なので, 上界側は
`ProblemsSchurMultiplier.lean` と同じく **stem extension の ∀-形**で述べる:

> `h : Γ →* A × B` が stem extension で `|A|`, `|B|` が互いに素なら, `A` の stem extension
> `f` と `B` の stem extension `g` が存在して `|ker h| = |ker f| · |ker g|`。

5A.8(a) (`isStemExtension_prodMap` / `card_ker_prodMap`) と合わせて位数版の等式になる。

## 分解の骨格

`Z := ker h`, `Γ_A := h⁻¹(A × 1) = ker (snd ∘ h)`, `Γ_B := h⁻¹(1 × B) = ker (fst ∘ h)`。

1. `Γ_A ⊓ Γ_B = Z` (`inf_ker_snd_ker_fst`)。
2. `Γ = Γ_A · Γ_B` (`exists_mem_ker_snd_mul_mem_ker_fst`)。
3. ⭐ **`⁅Γ_A, Γ_B⁆ = ⊥`** (`commutator_ker_snd_ker_fst_eq_bot`) — ここが coprime を使う要。

4. `Γ` は `Γ_A` と `Γ_B` の**中心積** (`isCentralProduct_top`) なので
   `Γ' = ⁅Γ_A,Γ_A⁆ ⊔ ⁅Γ_B,Γ_B⁆` (`commutator_eq_sup`)。
5. `Z = Z_A · Z_B` (`exists_mul_mem_inf_commutator`), ここで
   `Z_A := Z ⊓ ⁅Γ_A,Γ_A⁆`, `Z_B := Z ⊓ ⁅Γ_B,Γ_B⁆`。

本ファイルは 1-5 の前半を提供する。残り (`Z_A ⊓ Z_B = ⊥`, 商への降下) は
issue 1055 の設計に従って続きを実装する。

## `⁅Γ_A, Γ_B⁆ = ⊥` の証明 (書籍の行間)

`x ∈ Γ_A`, `y ∈ Γ_B` なら `⁅x, y⁆ ∈ Γ_A ⊓ Γ_B = Z ≤ Z(Γ)`。
`h (x ^ |A|) = (h x) ^ |A| = ((h x).1 ^ |A|, 1) = 1` なので **`x ^ |A| ∈ Z`**
— 剰余群 `Γ_A/Z` を作らずに済むのがポイント。`⁅x,y⁆` が中心的なので
`⁅x,y⁆ ^ |A| = ⁅x ^ |A|, y⁆ = 1` (中心元との交換子は自明)。同様に `⁅x,y⁆ ^ |B| = 1`。
位数が `|A|` と `|B|` の両方を割るので coprime から `⁅x,y⁆ = 1`。
-/

open scoped commutatorElement

namespace OddOrder.Isaacs.Ch05

section /- 5A.8(b): coprime direct product (p. 153) -/

variable {Γ A B : Type*} [Group Γ] [Group A] [Group B]

/-- `Γ_A ⊓ Γ_B = Z`: 両成分が自明 ⟺ `h` の核。 -/
theorem inf_ker_snd_ker_fst (h : Γ →* A × B) :
    ((MonoidHom.snd A B).comp h).ker ⊓ ((MonoidHom.fst A B).comp h).ker = h.ker := by
  ext x
  simp [MonoidHom.mem_ker, Prod.ext_iff, and_comm]

/-- `Γ = Γ_A · Γ_B`: `h` が全射なら任意の `γ` は `Γ_A` の元と `Γ_B` の元の積。 -/
theorem exists_mem_ker_snd_mul_mem_ker_fst {h : Γ →* A × B} (hsurj : Function.Surjective h)
    (γ : Γ) :
    ∃ x ∈ ((MonoidHom.snd A B).comp h).ker, ∃ y ∈ ((MonoidHom.fst A B).comp h).ker,
      γ = x * y := by
  obtain ⟨x, hx⟩ := hsurj ((h γ).1, 1)
  refine ⟨x, ?_, x⁻¹ * γ, ?_, by group⟩
  · simp [MonoidHom.mem_ker, hx]
  · simp [MonoidHom.mem_ker, hx]

/-- ⭐ **`⁅Γ_A, Γ_B⁆ = ⊥`** (Problem 5A.8(b) の要): `ker h ≤ Z(Γ)` で `|A|`, `|B|` が
互いに素なら, `h⁻¹(A × 1)` と `h⁻¹(1 × B)` は元ごとに可換。

⚠ `h` の全射性は不要。 -/
theorem commutator_ker_snd_ker_fst_eq_bot [Finite A] [Finite B] {h : Γ →* A × B}
    (hker : h.ker ≤ Subgroup.center Γ)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    ⁅((MonoidHom.snd A B).comp h).ker, ((MonoidHom.fst A B).comp h).ker⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [MonoidHom.mem_ker] at hx hy
  have hx2 : (h x).2 = 1 := hx
  have hy1 : (h y).1 = 1 := hy
  rw [Subgroup.mem_bot]
  -- `⁅x, y⁆ ∈ ker h ≤ Z(Γ)`
  have hcxy : ⁅x, y⁆ ∈ h.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    simp [commutatorElement_def, Prod.ext_iff, hx2, hy1]
  have hcen : ⁅x, y⁆ ∈ Subgroup.center Γ := hker hcxy
  -- 中心元との交換子は自明
  have hkey : ∀ z : Γ, z ∈ h.ker → ⁅z, y⁆ = 1 ∧ ⁅x, z⁆ = 1 := by
    intro z hz
    have hzc := Subgroup.mem_center_iff.mp (hker hz)
    exact ⟨commutatorElement_eq_one_iff_mul_comm.mpr (hzc y).symm,
      commutatorElement_eq_one_iff_mul_comm.mpr (hzc x)⟩
  -- `x ^ |A| ∈ ker h` (剰余群を経由しない)
  have hxA : x ^ Nat.card A ∈ h.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    refine Prod.ext ?_ ?_
    · simp
    · simp [hx2]
  have hyB : y ^ Nat.card B ∈ h.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    refine Prod.ext ?_ ?_
    · simp [hy1]
    · simp
  -- 双線形性で位数を潰す
  have hpowA : ⁅x, y⁆ ^ Nat.card A = 1 := by
    rw [← OddOrder.GroupTheory.commutatorElement_pow_left_of_central hcen]
    exact (hkey _ hxA).1
  have hpowB : ⁅x, y⁆ ^ Nat.card B = 1 := by
    rw [← OddOrder.GroupTheory.commutatorElement_pow_right_of_central hcen]
    exact (hkey _ hyB).2
  have hone : orderOf ⁅x, y⁆ = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpowA)
      (orderOf_dvd_of_pow_eq_one hpowB))
  exact orderOf_eq_one_iff.mp hone

/-! ### ステップ 4: `Γ` は `Γ_A` と `Γ_B` の中心積 -/

/-- `h` が全射で `ker h ≤ Z(Γ)`, `|A|`, `|B|` 互いに素なら, `Γ` は `Γ_A` と `Γ_B` の中心積。 -/
theorem isCentralProduct_top [Finite A] [Finite B] {h : Γ →* A × B}
    (hsurj : Function.Surjective h) (hker : h.ker ≤ Subgroup.center Γ)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    OddOrder.GroupTheory.IsCentralProduct (⊤ : Subgroup Γ)
      ((MonoidHom.snd A B).comp h).ker ((MonoidHom.fst A B).comp h).ker where
  sup_eq := by
    refine (eq_top_iff.mpr fun γ _ => ?_).symm
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mem_ker_snd_mul_mem_ker_fst hsurj γ
    exact Subgroup.mul_mem_sup hx hy
  commutator_eq_bot := commutator_ker_snd_ker_fst_eq_bot hker hcop

/-- **ステップ 4**: `Γ' = ⁅Γ_A, Γ_A⁆ ⊔ ⁅Γ_B, Γ_B⁆`。 -/
theorem commutator_eq_sup [Finite A] [Finite B] {h : Γ →* A × B}
    (hsurj : Function.Surjective h) (hker : h.ker ≤ Subgroup.center Γ)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    _root_.commutator Γ =
      ⁅((MonoidHom.snd A B).comp h).ker, ((MonoidHom.snd A B).comp h).ker⁆ ⊔
        ⁅((MonoidHom.fst A B).comp h).ker, ((MonoidHom.fst A B).comp h).ker⁆ := by
  rw [_root_.commutator_def]
  exact (isCentralProduct_top hsurj hker hcop).commutator_self

/-! ### ステップ 5 前半: `Z = Z_A · Z_B` -/

/-- **ステップ 5 前半**: `Z := ker h` の各元は `Z ⊓ ⁅Γ_A,Γ_A⁆` の元と `Z ⊓ ⁅Γ_B,Γ_B⁆` の元の積。

`Z ≤ Γ' = ⁅Γ_A,Γ_A⁆ ⊔ ⁅Γ_B,Γ_B⁆` で, この join もまた中心積なので `z = u · v` と分解できる。
`u ∈ ⁅Γ_A,Γ_A⁆ ≤ Γ_A` と `z ∈ Z ≤ Γ_A` から `v = u⁻¹ z ∈ Γ_A ⊓ Γ_B = Z`, 対称に `u ∈ Z`。 -/
theorem exists_mul_mem_inf_commutator [Finite A] [Finite B] {h : Γ →* A × B}
    (hsurj : Function.Surjective h) (hst : IsStemExtension h)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) {z : Γ} (hz : z ∈ h.ker) :
    ∃ u ∈ h.ker ⊓ ⁅((MonoidHom.snd A B).comp h).ker, ((MonoidHom.snd A B).comp h).ker⁆,
      ∃ v ∈ h.ker ⊓ ⁅((MonoidHom.fst A B).comp h).ker, ((MonoidHom.fst A B).comp h).ker⁆,
        z = u * v := by
  set ΓA := ((MonoidHom.snd A B).comp h).ker with hΓA
  set ΓB := ((MonoidHom.fst A B).comp h).ker with hΓB
  have hbot : ⁅ΓA, ΓB⁆ = ⊥ := commutator_ker_snd_ker_fst_eq_bot hst.ker_le_center hcop
  -- `⁅ΓA,ΓA⁆ ⊔ ⁅ΓB,ΓB⁆` もまた中心積
  have hsub : OddOrder.GroupTheory.IsCentralProduct (⁅ΓA, ΓA⁆ ⊔ ⁅ΓB, ΓB⁆) ⁅ΓA, ΓA⁆ ⁅ΓB, ΓB⁆ :=
    ⟨rfl, le_bot_iff.mp ((Subgroup.commutator_mono
      (Subgroup.commutator_le_self _) (Subgroup.commutator_le_self _)).trans hbot.le)⟩
  have hzsup : z ∈ ⁅ΓA, ΓA⁆ ⊔ ⁅ΓB, ΓB⁆ := by
    rw [← commutator_eq_sup hsurj hst.ker_le_center hcop]
    exact hst.ker_le_commutator hz
  obtain ⟨u, hu, v, hv, rfl⟩ := hsub.exists_mul hzsup
  -- `Γ_A ⊓ Γ_B = ker h`
  have hinf := inf_ker_snd_ker_fst h
  have huA : u ∈ ΓA := Subgroup.commutator_le_self _ hu
  have hvB : v ∈ ΓB := Subgroup.commutator_le_self _ hv
  have hzA : u * v ∈ ΓA := (inf_ker_snd_ker_fst h ▸ hz : _ ∈ ΓA ⊓ ΓB).1
  have hvA : v ∈ ΓA := by
    have hvu : v = u⁻¹ * (u * v) := by group
    rw [hvu]
    exact ΓA.mul_mem (ΓA.inv_mem huA) hzA
  have hvZ : v ∈ h.ker := by
    rw [← hinf]
    exact ⟨hvA, hvB⟩
  have huZ : u ∈ h.ker := by
    have : u = (u * v) * v⁻¹ := by group
    rw [this]
    exact h.ker.mul_mem hz (h.ker.inv_mem hvZ)
  exact ⟨u, ⟨huZ, hu⟩, v, ⟨hvZ, hv⟩, rfl⟩

/-! ### ステップ 5 後半: `Z_A ⊓ Z_B = ⊥` -/

/-- 中心的な核をもつ準同型 `ψ : K →* A'` があり `p ∤ |A'|` なら `p ∤ |K'|`。

`Syl_p(K)` の元は位数が `p` 冪で, その `ψ` 像は位数が `|A'|` を割る。互いに素なので像は `1`,
すなわち `Syl_p(K) ≤ ker ψ ≤ Z(K)`。あとは `not_dvd_card_commutator_of_sylow_le_center`。 -/
theorem not_dvd_card_commutator_of_ker_le_center {K : Type*} [Group K] [Finite K]
    {A' : Type*} [Group A'] [Finite A'] {ψ : K →* A'} (hψ : ψ.ker ≤ Subgroup.center K)
    {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card A') :
    ¬ p ∣ Nat.card (_root_.commutator K) := by
  obtain ⟨P⟩ : Nonempty (Sylow p K) := inferInstance
  refine not_dvd_card_commutator_of_sylow_le_center P ?_
  intro x hx
  obtain ⟨k, hk⟩ := P.2 (⟨x, hx⟩ : ↥(P : Subgroup K))
  have hxpow : x ^ p ^ k = 1 := by
    have hv := congrArg Subtype.val hk
    simpa using hv
  have h1 : ψ x = 1 := by
    have hA : ψ x ^ p ^ k = 1 := by rw [← map_pow, hxpow, map_one]
    have hcard : ψ x ^ Nat.card A' = 1 := pow_card_eq_one'
    have hcop : Nat.Coprime (p ^ k) (Nat.card A') :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
      (orderOf_dvd_of_pow_eq_one hA) (orderOf_dvd_of_pow_eq_one hcard)))
  exact hψ (MonoidHom.mem_ker.mpr h1)

/-- `⁅H, H⁆` (周囲群の中) と `commutator ↥H` は位数が等しい。 -/
theorem card_commutator_subgroup (H : Subgroup Γ) :
    Nat.card (⁅H, H⁆ : Subgroup Γ) = Nat.card (_root_.commutator ↥H) := by
  rw [← H.map_subtype_commutator]
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv).symm

/-- `p ∤ |A|` なら `p ∤ |⁅Γ_A, Γ_A⁆|`。 -/
theorem not_dvd_card_commutator_ker_snd [Finite Γ] [Finite A] {h : Γ →* A × B}
    (hker : h.ker ≤ Subgroup.center Γ) {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card A) :
    ¬ p ∣ Nat.card
      ((⁅((MonoidHom.snd A B).comp h).ker, ((MonoidHom.snd A B).comp h).ker⁆) :
        Subgroup Γ) := by
  set ΓA := ((MonoidHom.snd A B).comp h).ker with hΓA
  rw [card_commutator_subgroup]
  refine not_dvd_card_commutator_of_ker_le_center
    (ψ := ((MonoidHom.fst A B).comp h).restrict ΓA) ?_ hp
  intro x hx
  have h1 : (h (x : Γ)).1 = 1 := MonoidHom.mem_ker.mp hx
  have h2 : (h (x : Γ)).2 = 1 := (x : ↥ΓA).2
  have hxker : (x : Γ) ∈ h.ker := MonoidHom.mem_ker.mpr (Prod.ext h1 h2)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hxker)) (g : Γ))

/-- `p ∤ |B|` なら `p ∤ |⁅Γ_B, Γ_B⁆|`。 -/
theorem not_dvd_card_commutator_ker_fst [Finite Γ] [Finite B] {h : Γ →* A × B}
    (hker : h.ker ≤ Subgroup.center Γ) {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card B) :
    ¬ p ∣ Nat.card
      ((⁅((MonoidHom.fst A B).comp h).ker, ((MonoidHom.fst A B).comp h).ker⁆) :
        Subgroup Γ) := by
  set ΓB := ((MonoidHom.fst A B).comp h).ker with hΓB
  rw [card_commutator_subgroup]
  refine not_dvd_card_commutator_of_ker_le_center
    (ψ := ((MonoidHom.snd A B).comp h).restrict ΓB) ?_ hp
  intro x hx
  have h2 : (h (x : Γ)).2 = 1 := MonoidHom.mem_ker.mp hx
  have h1 : (h (x : Γ)).1 = 1 := (x : ↥ΓB).2
  have hxker : (x : Γ) ∈ h.ker := MonoidHom.mem_ker.mpr (Prod.ext h1 h2)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hxker)) (g : Γ))

/-- **ステップ 5 後半**: `Z_A ⊓ Z_B = ⊥`。

`|Z_A|` の素因数は `|A|` を割り, `|Z_B|` の素因数は `|B|` を割る (上 2 補題の対偶)。
`|A|`, `|B|` は互いに素なので位数が互いに素になり交わりは自明。 -/
theorem inf_inf_commutator_eq_bot [Finite Γ] [Finite A] [Finite B] {h : Γ →* A × B}
    (hker : h.ker ≤ Subgroup.center Γ) (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    (h.ker ⊓ ⁅((MonoidHom.snd A B).comp h).ker, ((MonoidHom.snd A B).comp h).ker⁆) ⊓
      (h.ker ⊓ ⁅((MonoidHom.fst A B).comp h).ker, ((MonoidHom.fst A B).comp h).ker⁆) = ⊥ := by
  rw [← disjoint_iff]
  refine Subgroup.disjoint_of_coprime_natCard ?_
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpA : p ∣ Nat.card
      ((h.ker ⊓ ⁅((MonoidHom.snd A B).comp h).ker,
        ((MonoidHom.snd A B).comp h).ker⁆ : Subgroup Γ)) :=
    hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpB : p ∣ Nat.card
      ((h.ker ⊓ ⁅((MonoidHom.fst A B).comp h).ker,
        ((MonoidHom.fst A B).comp h).ker⁆ : Subgroup Γ)) :=
    hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hdA : p ∣ Nat.card A := by
    by_contra hcon
    exact not_dvd_card_commutator_ker_snd hker hcon
      (hpA.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hdB : p ∣ Nat.card B := by
    by_contra hcon
    exact not_dvd_card_commutator_ker_fst hker hcon
      (hpB.trans (Subgroup.card_dvd_of_le inf_le_right))
  exact hp.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdA hdB))

end

end OddOrder.Isaacs.Ch05
