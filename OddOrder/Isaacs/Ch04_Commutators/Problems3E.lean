/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.Conjugacy
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems3D
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups
import OddOrder.Isaacs.Ch04_Commutators.ProblemsCyclicSylow

/-!
# Isaacs §3E の演習 (書籍 pp. 106-107)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 3E (coprime action)。

⚠ **置き場が Ch.4 なのは意図的**: §3E の主定理群 (Thm 3.23 A-不変 Sylow, Thm 3.24
Glauberman, Thm 3.27-3.30) は Ch.4 の交換子機構を要するため
`Ch04_Commutators/ForwardFromCh03.lean` に置かれている。演習も同じ層に置く。

⚠ 固定部分群は既存の `OddOrder.GroupTheory.fixedSubgroup φ K` を使う (重複定義しない)。

* **3E.1 の Hint 前半** `exists_ne_one_fixed_of_isPGroup_of_dvd` —
  `p`-群 `P` が `G` に作用し `p ∣ |G|` なら `C_G(P) ≠ 1`。
  (対偶が書籍の Hint「`C_G(P) = 1` なら `p ∤ |G|`」。)
* **3E.3** `smul_eq_self_of_trivial_on_normal_and_quotient` —
  `N ⊴ G` が `A`-不変, `(|A|,|N|) = 1`, `A` が `N` にも `G/N` にも自明に作用するなら
  `G` に自明に作用する。
-/

namespace OddOrder.Isaacs.Ch04

open Subgroup Pointwise

open scoped commutatorElement

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
  let : MulDistribMulAction A G := MulDistribMulAction.compHom G φ
  have hmod := hA.card_modEq_card_fixedPoints (α := G)
  have hdvdF : p ∣ Nat.card (MulAction.fixedPoints A G) := by
    have h0 : Nat.card G ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvd
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans h0)
  have h1 : (1 : G) ∈ MulAction.fixedPoints A G := fun a => smul_one a
  have hpos : 0 < Nat.card (MulAction.fixedPoints A G) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
  have hlt : 1 < Nat.card (MulAction.fixedPoints A G) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hdvdF)
  have : Nontrivial (MulAction.fixedPoints A G) := Finite.one_lt_card_iff_nontrivial.mp hlt
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
theorem exists_isAInvariant_isPGroup_of_isSolvable [Group.IsSolvable G] [Nontrivial G]
    (φ : A →* MulAut G) :
    ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ H ≠ ⊥ ∧ IsPGroup p ↥H ∧
      OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
  classical
  -- 導来列の最後の非自明な項 `K`
  have hex : ∃ n, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
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
  have hKnil : Group.IsNilpotent ↥K := by
    refine ⟨⟨1, ?_⟩⟩
    rw [Subgroup.upperCentralSeries_one, eq_top_iff]
    intro a _
    refine Subgroup.mem_center_iff.mpr fun b => ?_
    exact Subtype.ext (hKcomm b b.2 a a.2)
  -- `p ∣ |K|`
  have hKcard : 1 < Nat.card ↥K := by
    have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    exact Finite.one_lt_card
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hKcard.ne'
  have : Fact p.Prime := ⟨hp⟩
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

/-- **3E.1 (`A` 可解) の case (iii)**: `B ⊴ A` が `G` に互いに素に作用し
`C_G(B) = 1` なら, 各素数 `q` について `A`-不変な Sylow `q`-部分群がある。

Thm 3.23(a) で `B`-不変 Sylow `S` を取る。`a ∈ A` について `(φ a) • S` も `B`-不変
(`B ⊴ A`) な Sylow なので, Thm 3.23(b) より `C_G(B) = 1` の元で共役, すなわち一致する。 -/
theorem exists_isAInvariant_sylow_of_normal_of_trivial_fixed (φ : A →* MulAut G)
    {B : Subgroup A} [B.Normal]
    (hcop : Nat.Coprime (Nat.card ↥B) (Nat.card G))
    (hsolv : Group.IsSolvable ↥B ∨ Group.IsSolvable G)
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

omit [Finite A] [Finite G] in
/-- 固定部分群は `B ⊴ A` について `A`-不変。 -/
theorem isAInvariant_fixedSubgroup_normal (φ : A →* MulAut G) {B : Subgroup A} [B.Normal] :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (OddOrder.GroupTheory.fixedSubgroup φ B) := by
  refine OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mpr fun a g hg b hb => ?_
  have hmem : a⁻¹ * b * a ∈ B := by
    simpa using (‹B.Normal›.conj_mem b hb a⁻¹)
  have hfix : (φ (a⁻¹ * b * a)) g = g := hg _ hmem
  have hstep : (φ b) ((φ a) g) = (φ a) ((φ (a⁻¹ * b * a)) g) := by
    have h1 : (φ b) * (φ a) = (φ a) * (φ (a⁻¹ * b * a)) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    calc (φ b) ((φ a) g) = ((φ b) * (φ a)) g := rfl
      _ = ((φ a) * (φ (a⁻¹ * b * a))) g := by rw [h1]
      _ = (φ a) ((φ (a⁻¹ * b * a)) g) := rfl
  rw [hstep, hfix]

universe u

/-- 3E.1 (`A` 可解の場合) の帰納本体 (`|G|` に関する帰納)。 -/
private theorem exists_isAInvariant_isPGroup_solvableA_aux :
    ∀ (n : ℕ) {G : Type u} [Group G] [Finite G] [Nontrivial G]
      {A : Type*} [Group A] [Finite A] [Group.IsSolvable A] (φ : A →* MulAut G),
      Nat.card G ≤ n →
      ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ H ≠ ⊥ ∧ IsPGroup p ↥H ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ A _ _ _ φ hcard
  classical
  -- `p ∣ |G|` を取れる
  have hGcard : 1 < Nat.card G := Finite.one_lt_card
  -- 作用を単射にする
  set Abar := A ⧸ φ.ker with hAbar
  set ψ : Abar →* MulAut G := QuotientGroup.kerLift φ with hψ
  have hψinj : Function.Injective ψ := QuotientGroup.kerLift_injective φ
  have hψφ : ∀ a : A, ψ (QuotientGroup.mk' φ.ker a) = φ a := fun a => rfl
  have htransfer : ∀ H : Subgroup G, OddOrder.Isaacs.Ch03.IsAInvariant ψ H →
      OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
    intro H hH a
    have := hH (QuotientGroup.mk' φ.ker a)
    rwa [hψφ a] at this
  by_cases hAtriv : Subsingleton Abar
  · -- 作用は自明: 任意の Sylow でよい
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hGcard.ne'
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨S⟩ : Nonempty (Sylow q G) := inferInstance
    refine ⟨q, (S : Subgroup G), hq, ?_, S.isPGroup', ?_⟩
    · intro hbot
      have hcardS := S.card_eq_multiplicity
      rw [hbot] at hcardS
      have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
      rw [h1] at hcardS
      have hfac : 0 < (Nat.card G).factorization q :=
        Nat.Prime.factorization_pos_of_dvd hq (by omega) hqdvd
      have hlt : 1 < q ^ (Nat.card G).factorization q := Nat.one_lt_pow hfac.ne' hq.one_lt
      omega
    · refine htransfer _ fun a => ?_
      rw [Subsingleton.elim a 1, map_one]
      exact one_smul _ _
  · -- `Ā` は非自明: 極小正規部分群 `B` を取る
    have : Nontrivial Abar := not_subsingleton_iff_nontrivial.mp hAtriv
    have hBtop : (⊤ : Subgroup Abar) ≠ ⊥ := by
      intro h
      obtain ⟨x, hx⟩ := exists_ne (1 : Abar)
      have hxt : x ∈ (⊤ : Subgroup Abar) := trivial
      rw [h, Subgroup.mem_bot] at hxt
      exact hx hxt
    obtain ⟨B, hB, -⟩ := OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal
      (⊤ : Subgroup Abar) hBtop
    have hBnormal : B.Normal := hB.1
    obtain ⟨p₀, hp₀, hBel⟩ :=
      OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hB
    have : Fact p₀.Prime := ⟨hp₀⟩
    have hBp : IsPGroup p₀ ↥B := fun g => ⟨1, by simpa using hBel.2 g⟩
    set C : Subgroup G := OddOrder.GroupTheory.fixedSubgroup ψ B with hC
    have hCinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ C :=
      isAInvariant_fixedSubgroup_normal ψ
    -- `C ≠ ⊤` (`ψ` 単射 + `B ≠ ⊥`)
    have hCne : C ≠ ⊤ := by
      intro htop
      have : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB.2.1
      obtain ⟨b, hb⟩ := exists_ne (1 : ↥B)
      refine hb ?_
      have hfix : ∀ g : G, (ψ (b : Abar)) g = g := by
        intro g
        have hgC : g ∈ C := by rw [htop]; trivial
        exact hgC (b : Abar) b.2
      have : ψ (b : Abar) = 1 := MulEquiv.ext hfix
      have hb1 : (b : Abar) = 1 := hψinj (by rw [this, map_one])
      exact Subtype.ext hb1
    by_cases hCbot : C = ⊥
    · -- case (iii)
      have hnotdvd : ¬ p₀ ∣ Nat.card G := by
        intro hdvd
        obtain ⟨g, hg1, hgfix⟩ :=
          exists_ne_one_fixed_of_isPGroup_of_dvd hBp (ψ.comp B.subtype) hdvd
        have hgC : g ∈ C := fun l hl => hgfix ⟨l, hl⟩
        rw [hCbot, Subgroup.mem_bot] at hgC
        exact hg1 hgC
      have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card G) := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
        rw [hk]
        exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp₀).mpr hnotdvd)
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hGcard.ne'
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨S, hS⟩ := exists_isAInvariant_sylow_of_normal_of_trivial_fixed ψ hcop
        (Or.inl inferInstance) (fun g hg => by
          have hgC : g ∈ C := fun l hl => hg ⟨l, hl⟩
          rwa [hCbot, Subgroup.mem_bot] at hgC) q
      refine ⟨q, (S : Subgroup G), hq, ?_, S.isPGroup', htransfer _ hS⟩
      intro hbot
      have hcardS := S.card_eq_multiplicity
      rw [hbot] at hcardS
      have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
      rw [h1] at hcardS
      have hfac : 0 < (Nat.card G).factorization q :=
        Nat.Prime.factorization_pos_of_dvd hq (by omega) hqdvd
      have hlt : 1 < q ^ (Nat.card G).factorization q := Nat.one_lt_pow hfac.ne' hq.one_lt
      omega
    · -- case (ii): `↥C` に降りる
      have : Nontrivial ↥C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCbot
      have hClt : Nat.card ↥C < Nat.card G := by
        obtain ⟨x, hx⟩ : ∃ x : G, x ∉ C := by
          simpa [Subgroup.eq_top_iff'] using hCne
        exact Finite.card_subtype_lt (x := x) hx
      obtain ⟨p, H', hp, hH'ne, hH'p, hH'inv⟩ :=
        ih (Nat.card ↥C) (lt_of_lt_of_le hClt hcard) (G := ↥C)
          (A := Abar) (OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hCinv) le_rfl
      refine ⟨p, H'.map C.subtype, hp, ?_, ?_, htransfer _ ?_⟩
      · intro hbot
        refine hH'ne ?_
        rw [← Subgroup.comap_map_eq_self_of_injective C.subtype_injective H', hbot]
        simp
      · exact hH'p.of_injective (Subgroup.equivMapOfInjective H' C.subtype
          C.subtype_injective).symm.toMonoidHom
          (Subgroup.equivMapOfInjective H' C.subtype C.subtype_injective).symm.injective
      · refine OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mpr ?_
        rintro a - ⟨y, hy, rfl⟩
        exact ⟨(OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hCinv a) y,
          hH'inv.smul_mem a hy, rfl⟩

/-- **Isaacs Problem 3E.1** (`A` が可解な場合, 書籍 p. 106)。 -/
theorem exists_isAInvariant_isPGroup_of_isSolvable_aut {G : Type u} [Group G] [Finite G]
    [Nontrivial G] {A : Type*} [Group A] [Finite A] [Group.IsSolvable A] (φ : A →* MulAut G) :
    ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ H ≠ ⊥ ∧ IsPGroup p ↥H ∧
      OddOrder.Isaacs.Ch03.IsAInvariant φ H :=
  exists_isAInvariant_isPGroup_solvableA_aux (Nat.card G) φ le_rfl

/-- **Isaacs Problem 3E.2** (書籍 p. 106): 互いに素な作用で `G = HK` (`H`, `K` は `A`-不変)
なら `C_G(A) = (C_G(A) ∩ H)(C_G(A) ∩ K)`。

`c ∈ C_G(A)` を `c = h₀k₀` と書くと `H ∩ c K` は `A`-不変な `H ∩ K` の剰余類なので,
Thm 3.27 (`aInvariant_coset_mem_centralizer`) により `A`-固定点 `c'` を含む。
`c'` は `C ∩ H` に入り `c'⁻¹c ∈ C ∩ K`。 -/
theorem fixedSubgroup_top_eq_mul (φ : A →* MulAut G)
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    {H K : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    (hK : OddOrder.Isaacs.Ch03.IsAInvariant φ K)
    (hHK : ∀ g : G, ∃ h ∈ H, ∃ k ∈ K, g = h * k) :
    ((OddOrder.GroupTheory.fixedSubgroup φ ⊤ : Subgroup G) : Set G)
      = ((OddOrder.GroupTheory.fixedSubgroup φ ⊤ ⊓ H : Subgroup G) : Set G) *
        ((OddOrder.GroupTheory.fixedSubgroup φ ⊤ ⊓ K : Subgroup G) : Set G) := by
  ext c
  constructor
  · intro hc
    have hcfix : ∀ a : A, (φ a) c = c := fun a => hc a trivial
    obtain ⟨h₀, hh₀, k₀, hk₀, hceq⟩ := hHK c
    have hcoset : ∀ a : A, ∃ n ∈ H ⊓ K, (φ a) h₀ = h₀ * n := by
      intro a
      refine ⟨h₀⁻¹ * (φ a) h₀,
        Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hh₀) (hH.smul_mem a hh₀), ?_⟩, by group⟩
      have hsplit : (φ a) h₀ * (φ a) k₀ = c := by
        rw [← map_mul, ← hceq, hcfix a]
      have hval : h₀⁻¹ * (φ a) h₀ = k₀ * ((φ a) k₀)⁻¹ := by
        have h1 : (φ a) h₀ = c * ((φ a) k₀)⁻¹ := by
          rw [← hsplit]
          group
        rw [h1, hceq]
        group
      rw [hval]
      exact mul_mem hk₀ (inv_mem (hK.smul_mem a hk₀))
    obtain ⟨c', ⟨n, hn, hc'eq⟩, hc'fix⟩ :=
      aInvariant_coset_mem_centralizer hCop hSolv (hH.inf hK) hcoset
    have hnH : n ∈ H := (Subgroup.mem_inf.mp hn).1
    have hnK : n ∈ K := (Subgroup.mem_inf.mp hn).2
    refine ⟨c', Subgroup.mem_inf.mpr ⟨fun a _ => hc'fix a,
        by rw [hc'eq]; exact mul_mem hh₀ hnH⟩,
      c'⁻¹ * c, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by group⟩
    · intro a _
      rw [map_mul, map_inv, hc'fix a, hcfix a]
    · have : c'⁻¹ * c = n⁻¹ * k₀ := by
        rw [hc'eq, hceq]
        group
      rw [this]
      exact mul_mem (inv_mem hnK) hk₀
  · rintro ⟨x, hx, y, hy, rfl⟩
    intro a ha
    rw [map_mul, (Subgroup.mem_inf.mp hx).1 a ha, (Subgroup.mem_inf.mp hy).1 a ha]

/-! ### 3E.4 の核となる不等式 -/

omit [Finite A] in
/-- **`P ≤ Q` なら `[P : P ⊓ C] ≤ [Q : Q ⊓ C]`** (積の形): `P·(Q ⊓ C) ⊆ Q` と
`|P·(Q ⊓ C)|·|P ⊓ C| = |P|·|Q ⊓ C|` から。

3E.4 の `p`-部分比較の核 (`P`, `Q` を `A`-不変 Sylow に取る)。 -/
theorem card_mul_card_inf_le_of_le {P Q C : Subgroup G} (hPQ : P ≤ Q) :
    Nat.card ↥P * Nat.card ↥(Q ⊓ C) ≤ Nat.card ↥Q * Nat.card ↥(P ⊓ C) := by
  have hkey := Subgroup.card_HK_mul_card_inf_eq_card_mul_card P (Q ⊓ C)
  have hinf : P ⊓ (Q ⊓ C) = P ⊓ C := by
    rw [← inf_assoc, inf_eq_left.mpr hPQ]
  rw [hinf] at hkey
  have hsub : ((P : Set G) * ((Q ⊓ C : Subgroup G) : Set G)) ⊆ (Q : Set G) := by
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact Q.mul_mem (hPQ ha) (Subgroup.mem_inf.mp hb).1
  have hle : Nat.card ((P : Set G) * ((Q ⊓ C : Subgroup G) : Set G)) ≤ Nat.card ↥Q :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  calc Nat.card ↥P * Nat.card ↥(Q ⊓ C)
      = Nat.card ((P : Set G) * ((Q ⊓ C : Subgroup G) : Set G)) * Nat.card ↥(P ⊓ C) := hkey.symm
    _ ≤ Nat.card ↥Q * Nat.card ↥(P ⊓ C) := Nat.mul_le_mul_right _ hle

omit [Finite A] [Finite G] in
/-- `A`-不変部分群 `H` への作用制限の固定部分群は `C_G(A) ⊓ H` (を `↥H` で見たもの)。 -/
theorem fixedSubgroup_toMulAutHom_top {φ : A →* MulAut G} {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.GroupTheory.fixedSubgroup
        (OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH) (⊤ : Subgroup A)
      = (OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)).subgroupOf H := by
  ext x
  simp only [OddOrder.GroupTheory.mem_fixedSubgroup, Subgroup.mem_subgroupOf]
  constructor
  · exact fun h a ha => congrArg (Subtype.val : ↥H → G) (h a ha)
  · exact fun h a ha => Subtype.ext (h a ha)

/-- **3E.4 の `p`-部分**: `A`-不変部分群 `H` に対し, `H` の `A`-不変 Sylow `p`-部分群 `P`
(を `G` の部分群として見たもの) が取れて, `|P|` は `|H|` の `p`-部分,
`|P ⊓ C_G(A)|` は `|H ⊓ C_G(A)|` の `p`-部分になる (Lemma 3.32 を `↥H` に適用)。 -/
theorem exists_aInvariant_sylow_card_inf {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) {p : ℕ} [Fact p.Prime] :
    ∃ P : Subgroup G, P ≤ H ∧ OddOrder.Isaacs.Ch03.IsAInvariant φ P ∧
      Nat.card ↥P = p ^ (Nat.card ↥H).factorization p ∧
      Nat.card ↥(P ⊓ OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A))
        = p ^ (Nat.card ↥(H ⊓ OddOrder.GroupTheory.fixedSubgroup φ
            (⊤ : Subgroup A))).factorization p := by
  set ρ := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH with hρ
  have hCopH : Nat.Coprime (Nat.card A) (Nat.card ↥H) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card H)
  have hSolvH : Group.IsSolvable A ∨ Group.IsSolvable ↥H := by
    rcases hSolv with h | h
    · exact Or.inl h
    · have := h; exact Or.inr inferInstance
  obtain ⟨P', hP'inv⟩ := exists_aInvariant_sylow (φ := ρ) hCopH hSolvH p
  have h32 := card_inf_fixedSubgroup_of_aInvariant_sylow (φ := ρ) hCopH hSolvH hP'inv
  rw [fixedSubgroup_toMulAutHom_top hH] at h32
  refine ⟨(P' : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · refine OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mpr ?_
    rintro a - ⟨y, hy, rfl⟩
    exact ⟨ρ a y, hP'inv.smul_mem a hy, rfl⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact P'.card_eq_multiplicity
  · have hmap : ((P' : Subgroup ↥H).map H.subtype)
        ⊓ OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)
        = (((P' : Subgroup ↥H) ⊓ (OddOrder.GroupTheory.fixedSubgroup φ
            (⊤ : Subgroup A)).subgroupOf H)).map H.subtype := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
        obtain ⟨y, hy, rfl⟩ := hz1
        exact ⟨y, Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_subgroupOf.mpr hz2⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_inf.mpr ⟨⟨y, (Subgroup.mem_inf.mp hy).1, rfl⟩,
          Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hy).2⟩
    have hcard : Nat.card ↥((OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)).subgroupOf H)
        = Nat.card ↥(H ⊓ OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)) := by
      rw [← Subgroup.inf_subgroupOf_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        H ⊓ OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A) ≤ H)).toEquiv
    rw [hmap, Subgroup.card_map_of_injective H.subtype_injective, h32, hcard]

/-- **Isaacs Problem 3E.4** (書籍 p. 106): 互いに素な作用で `C := C_G(A)` とし `H` が
`A`-不変なら `[H : H ⊓ C] ∣ [G : C]` かつ `[C : H ⊓ C] ∣ [G : H]`。

素数ごとに `p`-部分を比べる。`H` の `A`-不変 Sylow `p` `P` を `G` の `A`-不変 Sylow `p` `Q`
に埋め込む (`Cor 3.25`) と, Lemma 3.32 が `|P ⊓ C| = |H ⊓ C|_p`, `|Q ⊓ C| = |C|_p` を与え,
核の不等式 `card_mul_card_inf_le_of_le` が
`|H|_p + |C|_p ≤ |G|_p + |H ⊓ C|_p` を与える。 -/
theorem relIndex_dvd_index_of_aInvariant {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    (H ⊓ OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)).relIndex H
        ∣ (OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)).index ∧
      (H ⊓ OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)).relIndex
        (OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A)) ∣ H.index := by
  set C : Subgroup G := OddOrder.GroupTheory.fixedSubgroup φ (⊤ : Subgroup A) with hCdef
  -- 素数ごとの鍵不等式
  have hkey : ∀ p : ℕ, p.Prime →
      (Nat.card ↥H).factorization p + (Nat.card ↥C).factorization p
        ≤ (Nat.card G).factorization p + (Nat.card ↥(H ⊓ C)).factorization p := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hPH, hPinv, hPcard, hPCcard⟩ :=
      exists_aInvariant_sylow_card_inf hCop hSolv hH (p := p)
    have hPp : IsPGroup p ↥P := IsPGroup.of_card hPcard
    obtain ⟨Q, hQinv, hPQ⟩ := aInvariant_pSubgroup_le_aInvariant_sylow hCop hSolv hPp hPinv
    have hQcard : Nat.card ↥(Q : Subgroup G) = p ^ (Nat.card G).factorization p :=
      Q.card_eq_multiplicity
    have hQCcard : Nat.card ↥((Q : Subgroup G) ⊓ C) = p ^ (Nat.card ↥C).factorization p :=
      card_inf_fixedSubgroup_of_aInvariant_sylow hCop hSolv hQinv
    have hineq := card_mul_card_inf_le_of_le (C := C) hPQ
    rw [hPcard, hQcard, hQCcard, hPCcard, ← pow_add, ← pow_add] at hineq
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hineq
  -- 位数の積の関係
  have hrel1 : Nat.card ↥(H ⊓ C) * (H ⊓ C).relIndex H = Nat.card ↥H := by
    have h := Subgroup.card_mul_index ((H ⊓ C).subgroupOf H)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ C ≤ H)).toEquiv] at h
  have hrel2 : Nat.card ↥(H ⊓ C) * (H ⊓ C).relIndex C = Nat.card ↥C := by
    have h := Subgroup.card_mul_index ((H ⊓ C).subgroupOf C)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ C ≤ C)).toEquiv] at h
  have hC : Nat.card ↥C * C.index = Nat.card G := Subgroup.card_mul_index C
  have hHidx : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
  have hne : ∀ K : Subgroup G, Nat.card ↥K ≠ 0 := fun K => Nat.card_pos.ne'
  have hrel1ne : (H ⊓ C).relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel2ne : (H ⊓ C).relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : ∀ (m n : ℕ), m ≠ 0 → n ≠ 0 → ∀ p : ℕ,
      (m * n).factorization p = m.factorization p + n.factorization p := by
    intro m n hm hn p
    rw [Nat.factorization_mul hm hn]
    rfl
  constructor
  · rw [← Nat.factorization_le_iff_dvd hrel1ne Subgroup.index_ne_zero_of_finite, Finsupp.le_def]
    intro p
    by_cases hp : p.Prime
    · have e1 := congrArg (fun m => m.factorization p) hrel1
      have e2 := congrArg (fun m => m.factorization p) hC
      simp only [hfac _ _ (hne _) hrel1ne,
        hfac _ _ (hne _) Subgroup.index_ne_zero_of_finite] at e1 e2
      have := hkey p hp
      omega
    · simp [hp]
  · rw [← Nat.factorization_le_iff_dvd hrel2ne Subgroup.index_ne_zero_of_finite, Finsupp.le_def]
    intro p
    by_cases hp : p.Prime
    · have e1 := congrArg (fun m => m.factorization p) hrel2
      have e2 := congrArg (fun m => m.factorization p) hHidx
      simp only [hfac _ _ (hne _) hrel2ne,
        hfac _ _ (hne _) Subgroup.index_ne_zero_of_finite] at e1 e2
      have := hkey p hp
      omega
    · simp [hp]

/-! ### Problem 3E.5 — `O_p(G)` は `O_p(G)/Φ(O_p(G))` への作用の核

`G` を `p`-可解, `O_{p'}(G) = 1` とし `P = O_p(G)`, `F = Φ(P)` とおく。`F` は `P` の
特性部分群なので `F ⊴ G` で, `G` は `P/F` に共役で作用する。`P/F` は可換なので `P` は
その核に入る (書籍の "observe")。逆に核が `P` に収まることを示すのが本問。
-/

/-- **3E.5 の作用の核**: `P ⊴ G` に対する, `G` の `P/Φ(P)` への共役作用の核。

`Φ(P)` は `P` の特性部分群なので `G` で正規 (`Subgroup.normal_of_characteristic_of_normal`)。
`G` の `P/Φ(P)` への共役作用は `G ⧸ Φ(P)` の中で `P/Φ(P)` に共役で作用することと同じなので,
核は `C_{G/Φ(P)}(P/Φ(P))` の引き戻し。元による特徴付け (`g` が `P/Φ(P)` に自明に作用する
⟺ `∀ y ∈ P, ⁅g, y⁆ ∈ Φ(P)`) は `mem_frattiniQuotientKernel_iff`。 -/
def frattiniQuotientKernel {G : Type*} [Group G] (P : Subgroup G) [P.Normal] : Subgroup G :=
  Subgroup.comap (QuotientGroup.mk' ((frattini ↥P).map P.subtype))
    (Subgroup.centralizer
      ((P.map (QuotientGroup.mk' ((frattini ↥P).map P.subtype)) :
          Subgroup (G ⧸ (frattini ↥P).map P.subtype)) :
        Set (G ⧸ (frattini ↥P).map P.subtype)))

/-- `frattiniQuotientKernel P` は文字どおり `G` の `P/Φ(P)` への共役作用
`MulAut.conjNormal ∘ (G ↠ G ⧸ Φ(P)) : G →* MulAut (P/Φ(P))` の核。

`MonoidHom.comap_ker` + `ker_conjNormal_eq_centralizer`。 -/
theorem frattiniQuotientKernel_eq_ker {G : Type*} [Group G] (P : Subgroup G) [P.Normal] :
    frattiniQuotientKernel P =
      ((MulAut.conjNormal (H := P.map (QuotientGroup.mk' ((frattini ↥P).map P.subtype)))).comp
        (QuotientGroup.mk' ((frattini ↥P).map P.subtype))).ker := by
  rw [← MonoidHom.comap_ker, ker_conjNormal_eq_centralizer]
  rfl

/-- **核の元による特徴付け**: `g` が `P/Φ(P)` に自明に作用する ⟺ `∀ y ∈ P, ⁅g, y⁆ ∈ Φ(P)`。

`⁅g, y⁆ ∈ Φ(P)` は `G ⧸ Φ(P)` で `ḡ` と `ȳ` が可換であることに他ならない。 -/
theorem mem_frattiniQuotientKernel_iff {G : Type*} [Group G] {P : Subgroup G} [P.Normal]
    {g : G} :
    g ∈ frattiniQuotientKernel P ↔ ∀ y ∈ P, ⁅g, y⁆ ∈ (frattini ↥P).map P.subtype := by
  simp only [frattiniQuotientKernel, Subgroup.mem_comap, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · intro h y hy
    have hc : Commute ((QuotientGroup.mk' ((frattini ↥P).map P.subtype)) y)
        ((QuotientGroup.mk' ((frattini ↥P).map P.subtype)) g) :=
      h _ (Subgroup.mem_map_of_mem _ hy)
    rw [← QuotientGroup.ker_mk' ((frattini ↥P).map P.subtype), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hc.symm
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hy' := h y hy
    rw [← QuotientGroup.ker_mk' ((frattini ↥P).map P.subtype), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_commute] at hy'
    exact hy'.symm

/-- `↥P` の元が `Φ(P)` の `G` への像に入るなら, もとの `Φ(↥P)` に入る。 -/
theorem mem_frattini_of_coe_mem_map {G : Type*} [Group G] {P : Subgroup G} {z : ↥P}
    (hz : (z : G) ∈ (frattini ↥P).map P.subtype) : z ∈ frattini ↥P := by
  obtain ⟨w, hw, hwz⟩ := hz
  exact (Subtype.ext hwz : w = z) ▸ hw

/-- **書籍の "observe"**: `P` が `p`-群なら `P/Φ(P)` は可換なので `P` は作用の核に入る。

`⁅x, y⁆ ∈ P' ≤ Φ(P)` (`commutator_le_frattini_of_pgroup`)。 -/
theorem le_frattiniQuotientKernel {G : Type*} [Group G] [Finite G] {P : Subgroup G} [P.Normal]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p ↥P) : P ≤ frattiniQuotientKernel P := by
  intro g hg
  rw [mem_frattiniQuotientKernel_iff]
  intro y hy
  refine ⟨⁅(⟨g, hg⟩ : ↥P), (⟨y, hy⟩ : ↥P)⁆, ?_, rfl⟩
  refine commutator_le_frattini_of_pgroup hP ?_
  rw [commutator_def]
  exact commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **3E.5 の核心**: `P ⊴ G` が `p`-群で, `x` の位数が `p` で割れず `x` が `P/Φ(P)` に
自明に作用するなら, `x` は `P` を中心化する。

`⟨x⟩` を `P` に共役で作用させると `(|⟨x⟩|, |Φ(P)|) = 1` かつ `P/Φ(P)` 上自明なので,
**3D.4** (`smul_eq_self_of_trivial_mod_frattini`) がそのまま適用できる。 -/
theorem mem_centralizer_of_mem_frattiniQuotientKernel {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} [P.Normal] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p ↥P) {x : G}
    (hx : x ∈ frattiniQuotientKernel P) (hord : ¬ p ∣ orderOf x) :
    x ∈ Subgroup.centralizer (P : Set G) := by
  classical
  set Z : Subgroup G := Subgroup.zpowers x with hZ
  let : MulDistribMulAction ↥Z ↥P :=
    MulDistribMulAction.compHom ↥P ((MulAut.conjNormal (H := P)).comp Z.subtype)
  have hZK : Z ≤ frattiniQuotientKernel P := Subgroup.zpowers_le.mpr hx
  have hcop : Nat.Coprime (Nat.card ↥Z) (Nat.card ↥(frattini ↥P)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    have hdvd : Nat.card ↥(frattini ↥P) ∣ Nat.card ↥P := Subgroup.card_subgroup_dvd_card _
    have hcard : Nat.card ↥Z = orderOf x := by rw [hZ]; exact Nat.card_zpowers x
    rw [hcard]
    refine Nat.Coprime.coprime_dvd_right (hn ▸ hdvd) ?_
    exact Nat.Coprime.pow_right n
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hord).symm
  have htriv : ∀ (h : ↥Z) (g : ↥P), g⁻¹ * (h • g) ∈ frattini ↥P := by
    intro h g
    have hmem : ⁅(h : G), ((g : G))⁻¹⁆ ∈ (frattini ↥P).map P.subtype :=
      mem_frattiniQuotientKernel_iff.mp (hZK h.2) _ (inv_mem g.2)
    refine mem_frattini_of_coe_mem_map ?_
    have hsmul : ((h • g : ↥P) : G) = (h : G) * (g : G) * (h : G)⁻¹ := rfl
    have hcoe : ((g⁻¹ * (h • g) : ↥P) : G) = ⁅((g : G))⁻¹, (h : G)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, commutatorElement_def]
      group
    rw [hcoe, ← commutatorElement_inv]
    exact inv_mem hmem
  have hfix := OddOrder.Isaacs.Ch03.smul_eq_self_of_trivial_mod_frattini hcop htriv
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxy : x * y * x⁻¹ = y :=
    congrArg (Subtype.val : ↥P → G) (hfix ⟨x, Subgroup.mem_zpowers x⟩ ⟨y, hy⟩)
  calc y * x = x * y * x⁻¹ * x := by rw [hxy]
    _ = x * y := by group

/-- **Isaacs Problem 3E.5** (書籍 p. 107): `G` を `p`-可解, `O_{p'}(G) = 1` とし
`P = O_p(G)`, `F = Φ(P)` とおくと, `G` の `P/F` への自然な共役作用の核はちょうど `P`。

(書籍の Note: したがって `G/P` は `Aut(P/F)` の部分群と同型で, `P/F` が位数 `pⁿ` の
初等可換 `p`-群であることから `G/P` は `GL(n, p)` の部分群と同型になる。)

**証明**: `P ≤ K` は `P/F` が可換だから (`le_frattiniQuotientKernel`)。逆向きは `K` が
`p`-群であることを示す: `q ≠ p` が `|K|` を割るとして Cauchy で位数 `q` の元 `x ∈ K` を
取ると, `x` は `P` に互いに素に作用し `P/F` 上自明なので **3D.4** で `P` に自明に作用し
(`mem_centralizer_of_mem_frattiniQuotientKernel`), **Hall-Higman 1.2.3**
(`hall_higman_1_2_3`, ここで `O_{p'}(G) = 1` を使う) より
`x ∈ C_G(O_p(G)) ≤ O_p(G) = P`。すると `q ∣ |P| = p^n` で矛盾。
`K ⊴ G` は `p`-群なので `K ≤ O_p(G) = P`。 -/
theorem frattiniQuotientKernel_oPiCore_eq {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    frattiniQuotientKernel (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)
      = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := by
  classical
  set P : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G with hPdef
  have hPp : IsPGroup p ↥P :=
    OddOrder.Isaacs.Ch03.Subgroup.isPiGroup_singleton_iff_isPGroup.mp
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup _)
  refine le_antisymm ?_ (le_frattiniQuotientKernel hPp)
  have hKnormal : (frattiniQuotientKernel P).Normal :=
    (Subgroup.normal_centralizer).comap _
  refine OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
  intro q hq
  rw [Set.mem_singleton_iff]
  by_contra hqp
  obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
  have : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(frattiniQuotientKernel P)) q hqdvd
  have hzord : orderOf ((z : G)) = q := by rw [Subgroup.orderOf_coe]; exact hz
  have hnotdvd : ¬ p ∣ orderOf ((z : G)) := by
    rw [hzord]
    exact fun hdvd =>
      hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqprime).mp hdvd).symm
  have hzP : (z : G) ∈ P :=
    OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({p} : Set ℕ) hp'
      (mem_centralizer_of_mem_frattiniQuotientKernel hPp z.2 hnotdvd)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
  have hdvd : orderOf ((⟨(z : G), hzP⟩ : ↥P)) ∣ Nat.card ↥P := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hzord, hn] at hdvd
  exact hqp ((Nat.prime_dvd_prime_iff_eq hqprime (Fact.out : p.Prime)).mp
    (hqprime.dvd_of_dvd_pow hdvd))

end -- 3E

end OddOrder.Isaacs.Ch04
