/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# Isaacs §3E の演習 (書籍 pp. 106-107)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 3E (coprime action)。

⚠ **置き場が Ch.4 なのは意図的**: §3E の主定理群 (Thm 3.23 A-不変 Sylow, Thm 3.24
Glauberman, Thm 3.27-3.30) は Ch.4 の交換子機構を要するため
`Ch04_Commutators/ForwardFromCh03.lean` に置かれている。演習も同じ層に置く。

* **3E.1 の Hint 前半** `exists_ne_one_fixed_of_isPGroup_of_dvd` —
  `p`-群 `P` が `G` に作用し `p ∣ |G|` なら `C_G(P) ≠ 1`。
  (対偶が書籍の Hint「`C_G(P) = 1` なら `p ∤ |G|`」。)
* **3E.3** `smul_eq_self_of_trivial_on_normal_and_quotient` —
  `N ⊴ G` が `A`-不変, `(|A|,|N|) = 1`, `A` が `N` にも `G/N` にも自明に作用するなら
  `G` に自明に作用する。
-/

namespace OddOrder.Isaacs.Ch04

open Subgroup Pointwise

variable {G : Type*} [Group G]

section /- 3E: coprime action の演習 -/

variable {A : Type*} [Group A] [Finite A] [Finite G]

omit [Finite A] in
/-- **Isaacs Problem 3E.1 の Hint (対偶)**: `p`-群 `A` が `G` に自己同型で作用し
`p ∣ |G|` なら, `A` に固定される非自明な元がある (`C_G(A) ≠ 1`)。

`A` の `G` への作用について `|G| ≡ |C_G(A)| (mod p)`
(`IsPGroup.card_modEq_card_fixedPoints`)。`p ∣ |G|` なら `p ∣ |C_G(A)|` で
`C_G(A)` は `1` を含むから位数 `≥ p ≥ 2`。 -/
theorem exists_ne_one_fixed_of_isPGroup_of_dvd {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    (φ : A →* MulAut G) (hdvd : p ∣ Nat.card G) :
    ∃ g : G, g ≠ 1 ∧ ∀ a : A, (φ a) g = g := by
  letI : MulDistribMulAction A G := MulDistribMulAction.compHom G φ
  have hmod := hA.card_modEq_card_fixedPoints (α := G)
  have hdvdF : p ∣ Nat.card (MulAction.fixedPoints A G) := by
    have h0 : Nat.card G ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvd
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans h0)
  have h1 : (1 : G) ∈ MulAction.fixedPoints A G := fun a => smul_one a
  have hpos : 0 < Nat.card (MulAction.fixedPoints A G) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
  have hlt : 1 < Nat.card (MulAction.fixedPoints A G) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hdvdF)
  haveI : Nontrivial (MulAction.fixedPoints A G) := Finite.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨y, hy⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints A G)
  refine ⟨(y : G), fun hy1 => hy (Subtype.ext hy1), fun a => ?_⟩
  exact y.2 a

omit [Finite A] [Finite G] in
/-- **Isaacs Problem 3E.3** (書籍 p. 106): `N ⊴ G` が `A`-不変で `(|A|, |N|) = 1`,
`A` が `N` にも `G/N` にも自明に作用するなら, `A` は `G` に自明に作用する。

`g` を固定すると `a ↦ g⁻¹ (φ a g)` は `A → ↥N` の**準同型**になる
(`A` が `N` に自明に作用するので cocycle 条件が積の条件になる)。像は `|A|` と `|N|` の
両方を割る位数を持つので自明。⚠ 書籍 Hint の「`A` が巡回群としてよい」は不要。 -/
theorem smul_eq_self_of_trivial_on_normal_and_quotient (φ : A →* MulAut G) {N : Subgroup G}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card ↥N))
    (htrivN : ∀ (a : A), ∀ n ∈ N, (φ a) n = n)
    (htrivQ : ∀ (a : A) (g : G), g⁻¹ * (φ a) g ∈ N) :
    ∀ (a : A) (g : G), (φ a) g = g := by
  intro a g
  -- `ψ : A →* ↥N`, `ψ a = g⁻¹ * (φ a) g`
  let ψ : A →* ↥N :=
    { toFun := fun b => ⟨g⁻¹ * (φ b) g, htrivQ b g⟩
      map_one' := by
        refine Subtype.ext ?_
        simp
      map_mul' := by
        intro b₁ b₂
        refine Subtype.ext ?_
        have hmem : g⁻¹ * (φ b₂) g ∈ N := htrivQ b₂ g
        have hfix : (φ b₁) (g⁻¹ * (φ b₂) g) = g⁻¹ * (φ b₂) g := htrivN b₁ _ hmem
        have hexp : (φ (b₁ * b₂)) g = ((φ b₁) g) * ((φ b₁) (g⁻¹ * (φ b₂) g)) := by
          rw [map_mul (φ) b₁ b₂]
          rw [show ((φ b₁) * (φ b₂) : MulAut G) g = (φ b₁) ((φ b₂) g) from rfl]
          rw [map_mul (φ b₁), map_inv (φ b₁)]
          group
        change g⁻¹ * (φ (b₁ * b₂)) g = (g⁻¹ * (φ b₁) g) * (g⁻¹ * (φ b₂) g)
        rw [hexp, hfix]
        group }
  -- 像は自明
  have hrange : Nat.card ↥(ψ.range) = 1 := by
    have hdvdA : Nat.card ↥(ψ.range) ∣ Nat.card A := by
      rw [MonoidHom.range_eq_map]
      have h := Subgroup.card_map_dvd (⊤ : Subgroup A) ψ
      rwa [Nat.card_congr (Subgroup.topEquiv (G := A)).toEquiv] at h
    have hdvdN : Nat.card ↥(ψ.range) ∣ Nat.card ↥N := Subgroup.card_subgroup_dvd_card _
    have := Nat.dvd_gcd hdvdA hdvdN
    rwa [hcop, Nat.dvd_one] at this
  have hbot : ψ.range = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hrange
  have hψa : ψ a = 1 := by
    have : ψ a ∈ ψ.range := ⟨a, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have : g⁻¹ * (φ a) g = 1 := congrArg (Subtype.val : ↥N → G) hψa
  have h2 := mul_eq_one_iff_eq_inv.mp this
  simpa using h2.symm

end -- 3E

end OddOrder.Isaacs.Ch04
