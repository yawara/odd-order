/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.Conjugacy

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

omit [Finite A] in
/-- **Isaacs Problem 3E.1** (`G` が可解な場合, 書籍 p. 106): `A` が `G` に自己同型で作用し
`G` が非自明な可解群なら, ある素数 `p` について非自明な `A`-不変 `p`-部分群がある。

導来列の最後の非自明な項 `K` は可換で `A`-不変 (`IsAInvariant.derivedSeries`)。
`p ∣ |K|` を取ると `K` の Sylow `p`-部分群 (`nilPiPart K {p}`) は一意なので
`A`-不変 (`nilPiPart_map_mulAut`)。⚠ 半直積 `G ⋊ A` を作る必要はない。 -/
theorem exists_isAInvariant_isPGroup_of_isSolvable [IsSolvable G] [Nontrivial G]
    (φ : A →* MulAut G) :
    ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ H ≠ ⊥ ∧ IsPGroup p ↥H ∧
      OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
  classical
  -- 導来列の最後の非自明な項 `K`
  have hex : ∃ n, derivedSeries G n = ⊥ := IsSolvable.solvable
  have hn : derivedSeries G (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hn
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have hxtop : x ∈ (⊤ : Subgroup G) := trivial
    rw [hn, Subgroup.mem_bot] at hxtop
    exact hx hxtop
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  set K : Subgroup G := derivedSeries G m with hKdef
  have hKne : K ≠ ⊥ := Nat.find_min hex (by omega)
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    have hbot : ⁅K, K⁆ = ⊥ := by
      rw [hKdef, ← derivedSeries_succ, ← hm]
      exact hn
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) x hx)
  haveI hKnil : Group.IsNilpotent ↥K := by
    refine ⟨⟨1, ?_⟩⟩
    rw [Subgroup.upperCentralSeries_one, eq_top_iff]
    intro a _
    refine Subgroup.mem_center_iff.mpr fun b => ?_
    exact Subtype.ext (hKcomm b b.2 a a.2)
  -- `p ∣ |K|`
  have hKcard : 1 < Nat.card ↥K := by
    haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    exact Finite.one_lt_card
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hKcard.ne'
  haveI : Fact p.Prime := ⟨hp⟩
  have hpart := OddOrder.Isaacs.Ch03.isHallPart_nilPiPart (N := K) ({p} : Set ℕ) hKnil
  refine ⟨p, OddOrder.Isaacs.Ch03.nilPiPart K ({p} : Set ℕ), hp, ?_, ?_, ?_⟩
  · -- 非自明
    intro hbot
    have hcard := OddOrder.Isaacs.Ch03.card_isHallPart_singleton hpart
    rw [hbot] at hcard
    have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
    rw [h1] at hcard
    have hfac : 0 < (Nat.card ↥K).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpdvd
    have hlt : 1 < p ^ (Nat.card ↥K).factorization p :=
      Nat.one_lt_pow hfac.ne' hp.one_lt
    omega
  · exact OddOrder.Isaacs.Ch03.isPGroup_of_isPiGroup_singleton hpart.isPiGroup
  · -- `A`-不変
    intro a
    have hKinv : K.map (φ a).toMonoidHom = K := by
      have h := OddOrder.Isaacs.Ch03.IsAInvariant.derivedSeries φ m a
      rw [Subgroup.pointwise_smul_def] at h
      exact h
    have hmap := OddOrder.Isaacs.Ch03.nilPiPart_map_mulAut (N := K) ({p} : Set ℕ) hKnil (φ a)
    rw [hKinv] at hmap
    rw [Subgroup.pointwise_smul_def]
    exact hmap.symm

/-! ### 3E.1 (`A` 可解の場合) の部品 -/

/-- 作用の固定部分群 `C_G(A)`。 -/
def actionFixedSubgroup (φ : A →* MulAut G) : Subgroup G where
  carrier := {g : G | ∀ a : A, (φ a) g = g}
  one_mem' := fun a => map_one (φ a)
  mul_mem' := fun {x y} hx hy a => by rw [map_mul, hx a, hy a]
  inv_mem' := fun {x} hx a => by rw [map_inv, hx a]

omit [Finite A] [Finite G] in
theorem mem_actionFixedSubgroup {φ : A →* MulAut G} {g : G} :
    g ∈ actionFixedSubgroup φ ↔ ∀ a : A, (φ a) g = g := Iff.rfl

/-- **3E.1 (`A` 可解) の case (iii)**: `B ⊴ A` が `G` に互いに素に作用し
`C_G(B) = 1` なら, 各素数 `q` について `A`-不変な Sylow `q`-部分群がある。

Thm 3.23(a) で `B`-不変 Sylow `S` を取る。`a ∈ A` について `(φ a) • S` も `B`-不変
(`B ⊴ A`) な Sylow なので, Thm 3.23(b) より `C_G(B) = 1` の元で共役, すなわち一致する。 -/
theorem exists_isAInvariant_sylow_of_normal_of_trivial_fixed (φ : A →* MulAut G)
    {B : Subgroup A} [B.Normal]
    (hcop : Nat.Coprime (Nat.card ↥B) (Nat.card G))
    (hsolv : IsSolvable ↥B ∨ IsSolvable G)
    (hfix : ∀ g : G, (∀ b : ↥B, (φ (b : A)) g = g) → g = 1)
    (q : ℕ) [Fact q.Prime] :
    ∃ S : Sylow q G, OddOrder.Isaacs.Ch03.IsAInvariant φ (S : Subgroup G) := by
  set ψ : ↥B →* MulAut G := φ.comp B.subtype with hψ
  obtain ⟨S, hS⟩ := exists_aInvariant_sylow (φ := ψ) hcop hsolv q
  refine ⟨S, fun a => ?_⟩
  have hcoe : (((φ a : MulAut G) • S : Sylow q G) : Subgroup G)
      = (φ a : MulAut G) • (S : Subgroup G) := rfl
  -- `(φ a) • S` も `B`-不変
  have hconj : OddOrder.Isaacs.Ch03.IsAInvariant ψ
      ((((φ a : MulAut G) • S : Sylow q G)) : Subgroup G) := by
    rw [hcoe]
    intro b
    have hb : (b : A) ∈ B := b.2
    have hmem : a⁻¹ * (b : A) * a ∈ B := by
      simpa using (‹B.Normal›.conj_mem (b : A) hb a⁻¹)
    have hkey : ψ b • ((φ a : MulAut G) • (S : Subgroup G))
        = (φ a : MulAut G) • (ψ ⟨a⁻¹ * (b : A) * a, hmem⟩ • (S : Subgroup G)) := by
      rw [smul_smul, smul_smul]
      congr 1
      change φ (b : A) * φ a = φ a * φ (a⁻¹ * (b : A) * a)
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [hkey, hS _]
  -- Thm 3.23(b) で共役, しかし `C_G(B) = 1`
  obtain ⟨c, hcfix, hceq⟩ := aInvariant_sylow_conj (φ := ψ) hcop hsolv hS hconj
  have h1 : MulAut.conj (1 : G) • (S : Subgroup G) = (S : Subgroup G) := by simp
  rw [hfix c hcfix, h1, hcoe] at hceq
  exact hceq.symm

end -- 3E

end OddOrder.Isaacs.Ch04
