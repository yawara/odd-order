/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups

/-!
# Isaacs §3E: Hartley–Turull cluster (Lemmas 3.31–3.34, pp. 105-108)

この leaf は Hartley–Turull 定理 (Thm 3.31) とその支持補題群を実装する:

* **Lemma 3.33** (equivariant bijection lemma): 全部分群 `B ≤ A` の固定点数が一致する
  2 つの有限 `A`-集合の間には `A`-equivariant 全単射が存在する (純組合せ).
* **Theorem 3.31** (Hartley–Turull): `A` が `G` に coprime に作用する
  (どちらかが solvable) とき, **abelian** な群 `H` への `A`-作用で全部分群 `B ≤ A`
  の固定点数が `G` と一致するものが存在する (しかも `|H| = |G|`).

## 主要結果

| Isaacs # | Lean | 状態 |
|---|---|---|
| Thm 3.31 | `exists_abelian_fixedPoint_replacement` | ✅ |
| Thm 3.31 step 1 | `exists_solvable_fixedPoint_replacement` | ✅ |
| Lem 3.33 | `exists_equivariant_equiv_of_card_fixedPoints_eq` | ✅ |

## Thm 3.31 の証明構造 (Isaacs pp. 105-107)

2 段構成. **Step 1** (`exists_solvable_fixedPoint_replacement`): `|G|` の各素因子 `p` に
A-不変 Sylow `P_p` を選び (Thm 3.23(a)), `N := Π_p P_p` に成分ごとの `A`-作用を入れる.
Lemma 3.32 を各 `B ≤ A` の制限作用に適用すると `|C_{P_p}(B)| = |P_p ∩ C_G(B)|` は
`|C_G(B)|` の full `p`-part であり, 全素因子にわたる積で `|C_N(B)| = |C_G(B)|`.
`N` は p-群の積ゆえ nilpotent (特に solvable). **Step 2**
(`exists_abelian_replacement_aux`): solvable `N` に対し `|N|` の強帰納法.
`N` 非可換なら `K := N' × (N/N')` に成分ごと作用を入れる. Cor 3.28 (coprime 固定点の
商への全射性) から `|C_N(B)| = |N' ∩ C_N(B)| · |C_{N/N'}(B)|`
(`card_fixedSubgroup_eq_mul_of_normal`) なので, `N'` と `N/N'` (いずれも位数減) の
abelian 置換の積が `N` の abelian 置換になる.

## Lem 3.33 の証明構造 (Isaacs pp. 105-106)

`|Ω|` の強帰納法 (`exists_equivariant_equiv_aux`, motive は `ℕ` 上に取り
`Ω`, `Λ` を型ごと一般化する).

1. `Ω = ∅` なら `B = ⊥` の固定点数比較で `|Λ| = 0`, 空の equiv で終了.
2. 軌道サイズ最小の点 `μ ∈ Ω` を取り `S := stab_A(μ)` とおく. 最小性から
   「`S ≤ H` かつ `H` が `Ω` に固定点をもつ ⇒ `H = S`」
   (`eq_stabilizer_of_le_of_orbit_card_min`).
3. `μ` は `S`-固定なので固定点数の仮定から `S`-固定点 `ν ∈ Λ` が存在.
   `T := stab_A(ν) ≥ S` は `ν` を固定するので再び仮定から `T` は `Ω` にも固定点を
   もち, step 2 より `T = S`.
4. orbit-stabilizer 定理を両側で使い equivariant 全単射
   `A•μ ≃ A ⧸ S ≃ A•ν` を得る (`c • μ ↦ c • ν`; well-defined は `stab` の一致から).
5. 各 `B ≤ A` の固定点数は軌道とその補集合に分割して数えられ, step 4 の全単射が
   `B`-固定点を保つ (`b • (c•μ) = c•μ ⟺ c⁻¹bc ∈ S ⟺ b • (c•ν) = c•ν`) ので,
   補集合対も固定点数の仮定を満たす. `|Ω ∖ A•μ| < |Ω|` で帰納法の仮定を適用し,
   軌道上と補集合上の equivariant 全単射を貼り合わせて完成.
-/

namespace OddOrder.Isaacs.Ch04

universe u v

variable {A : Type*} [Group A]

section /- 3E: Lemma 3.33 equivariant bijection (pp. 105-106) -/

/-- 補助: `b • (c • x) = c • x` ⟺ 共役 `c⁻¹ * b * c` が `stabilizer A x` に属する.
Lemma 3.33 の step 5 (軌道上の固定点対応) で両側の集合に対して使う. -/
theorem smul_smul_eq_self_iff_conj_mem_stabilizer {Ω : Type*} [MulAction A Ω]
    (b c : A) (x : Ω) :
    b • c • x = c • x ↔ c⁻¹ * b * c ∈ MulAction.stabilizer A x := by
  rw [MulAction.mem_stabilizer_iff, mul_assoc, mul_smul, mul_smul, inv_smul_eq_iff]

/-- **Isaacs Lemma 3.33, Step 1** (p. 105): `μ ∈ Ω` の軌道サイズが最小のとき,
`stab_A(μ) ≤ H` なる部分群 `H` が `Ω` のどこかの点 `ω` を固定するならば
`H = stab_A(μ)`.

**証明**: `H ≤ stab_A(ω)` で, orbit-stabilizer から
`|A•μ| = [A : stab_A(μ)] ≥ [A : H] ≥ [A : stab_A(ω)] = |A•ω|` (index の整除 + 有限性).
軌道サイズ最小性から全て等号, 特に `[A : H] = [A : stab_A(μ)]` で
`relIndex = 1` から `H ≤ stab_A(μ)`. -/
theorem eq_stabilizer_of_le_of_orbit_card_min {Ω : Type*} [Finite Ω] [MulAction A Ω]
    {μ : Ω} (hmin : ∀ ω : Ω, Nat.card (MulAction.orbit A μ) ≤ Nat.card (MulAction.orbit A ω))
    {H : Subgroup A} (hle : MulAction.stabilizer A μ ≤ H)
    {ω : Ω} (hfix : ∀ b ∈ H, b • ω = ω) :
    H = MulAction.stabilizer A μ := by
  have hHle : H ≤ MulAction.stabilizer A ω := fun b hb =>
    MulAction.mem_stabilizer_iff.mpr (hfix b hb)
  -- orbit-stabilizer: index = orbit cardinality.
  have hidx : ∀ x : Ω, (MulAction.stabilizer A x).index = Nat.card (MulAction.orbit A x) := by
    intro x
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A x)).symm
  have hpos : ∀ x : Ω, 0 < Nat.card (MulAction.orbit A x) := by
    intro x
    haveI : Nonempty (MulAction.orbit A x) := ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
    exact Nat.card_pos
  have h1 : (MulAction.stabilizer A ω).index ∣ H.index := Subgroup.index_dvd_of_le hHle
  have h2 : H.index ∣ (MulAction.stabilizer A μ).index := Subgroup.index_dvd_of_le hle
  have hμpos : 0 < (MulAction.stabilizer A μ).index := by rw [hidx]; exact hpos μ
  have hHpos : 0 < H.index := by
    rcases Nat.eq_zero_or_pos H.index with h0 | h
    · rw [h0, zero_dvd_iff] at h2
      omega
    · exact h
  have hle1 : (MulAction.stabilizer A ω).index ≤ H.index := Nat.le_of_dvd hHpos h1
  have hle2 : H.index ≤ (MulAction.stabilizer A μ).index := Nat.le_of_dvd hμpos h2
  have hminω : (MulAction.stabilizer A μ).index ≤ (MulAction.stabilizer A ω).index := by
    rw [hidx, hidx]
    exact hmin ω
  -- All the indices are equal; conclude via relIndex = 1.
  have heq : H.index = (MulAction.stabilizer A μ).index :=
    le_antisymm hle2 (hminω.trans hle1)
  have hrel : (MulAction.stabilizer A μ).relIndex H * H.index = H.index := by
    rw [Subgroup.relIndex_mul_index hle, heq]
  have hrel1 : (MulAction.stabilizer A μ).relIndex H = 1 :=
    Nat.eq_of_mul_eq_mul_right hHpos (by rw [hrel, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) hle

/-- 補助 (カウント分割): 有限型 `X` 上の述語 `p` を満たす元の個数は, `q` を満たす部分と
満たさない部分に分割して数えられる. Lemma 3.33 の step 5 で `p` = `B`-固定,
`q` = 軌道所属として使う. -/
private theorem nat_card_subtype_split {X : Type*} [Finite X] (p q : X → Prop) :
    Nat.card {x : X // p x} =
      Nat.card {y : {x : X // q x} // p y.1} + Nat.card {y : {x : X // ¬q x} // p y.1} := by
  classical
  have k1 : Nat.card {y : {x : X // p x} // q y.1} = Nat.card {y : {x : X // q x} // p y.1} :=
    Nat.card_congr
      { toFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
        invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  have k2 : Nat.card {y : {x : X // p x} // ¬q y.1} = Nat.card {y : {x : X // ¬q x} // p y.1} :=
    Nat.card_congr
      { toFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
        invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  calc Nat.card {x : X // p x}
      = Nat.card ({y : {x : X // p x} // q y.1} ⊕ {y : {x : X // p x} // ¬q y.1}) :=
        (Nat.card_congr (Equiv.sumCompl fun y : {x : X // p x} => q y.1)).symm
    _ = Nat.card {y : {x : X // p x} // q y.1} + Nat.card {y : {x : X // p x} // ¬q y.1} :=
        Nat.card_sum
    _ = Nat.card {y : {x : X // q x} // p y.1} + Nat.card {y : {x : X // ¬q x} // p y.1} := by
        rw [k1, k2]

/-- Lemma 3.33 の帰納法エンジン: `n = |Ω|` 上の強帰納法で, `Ω`, `Λ` を型ごと一般化する.
固定点数の仮定は部分群 `B` ごとに `{ω // ∀ b ∈ B, b • ω = ω}` の `Nat.card` 一致で表す
(集合 `MulAction.fixedPoints` 形への変換は wrapper 側で行う). -/
private theorem exists_equivariant_equiv_aux (n : ℕ) :
    ∀ (Ω : Type u) (Λ : Type v) [Finite Ω] [Finite Λ] [MulAction A Ω] [MulAction A Λ],
      Nat.card Ω = n →
      (∀ B : Subgroup A,
        Nat.card {ω : Ω // ∀ b ∈ B, b • ω = ω} = Nat.card {l : Λ // ∀ b ∈ B, b • l = l}) →
      ∃ f : Ω ≃ Λ, ∀ (a : A) (ω : Ω), f (a • ω) = a • f ω := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Ω Λ _ _ _ _ hn hcount
    classical
    cases isEmpty_or_nonempty Ω with
    | inl hΩempty =>
      -- Base case: Ω = ∅. Comparing fixed points of ⊥ gives |Λ| = |Ω| = 0.
      haveI := hΩempty
      have hΛ0 : Nat.card Λ = 0 := by
        have h1 : Nat.card {ω : Ω // ∀ b ∈ (⊥ : Subgroup A), b • ω = ω} = Nat.card Ω :=
          Nat.card_congr (Equiv.subtypeUnivEquiv fun ω b hb => by
            rw [Subgroup.mem_bot.mp hb, one_smul])
        have h2 : Nat.card {l : Λ // ∀ b ∈ (⊥ : Subgroup A), b • l = l} = Nat.card Λ :=
          Nat.card_congr (Equiv.subtypeUnivEquiv fun l b hb => by
            rw [Subgroup.mem_bot.mp hb, one_smul])
        have h3 := hcount ⊥
        have h4 : Nat.card Ω = 0 := Nat.card_eq_zero.mpr (Or.inl hΩempty)
        omega
      haveI hΛempty : IsEmpty Λ := by
        by_contra hne
        haveI := not_isEmpty_iff.mp hne
        have := Nat.card_pos (α := Λ)
        omega
      exact ⟨Equiv.equivOfIsEmpty Ω Λ, fun a ω => isEmptyElim ω⟩
    | inr hΩne =>
      haveI := hΩne
      -- Step 2: pick μ with orbit of minimal size; S := stabilizer A μ.
      obtain ⟨μ, hmin⟩ := Finite.exists_min fun ω : Ω => Nat.card (MulAction.orbit A ω)
      have hμfix : ∀ b ∈ MulAction.stabilizer A μ, b • μ = μ := fun b hb =>
        MulAction.mem_stabilizer_iff.mp hb
      -- Step 3: obtain an S-fixed point ν ∈ Λ, and show stabilizer A ν = stabilizer A μ.
      obtain ⟨⟨ν, hν⟩⟩ : Nonempty {l : Λ // ∀ b ∈ MulAction.stabilizer A μ, b • l = l} := by
        have hSpos : 0 < Nat.card {ω' : Ω // ∀ b ∈ MulAction.stabilizer A μ, b • ω' = ω'} := by
          haveI : Nonempty {ω' : Ω // ∀ b ∈ MulAction.stabilizer A μ, b • ω' = ω'} :=
            ⟨⟨μ, hμfix⟩⟩
          exact Nat.card_pos
        rw [hcount (MulAction.stabilizer A μ)] at hSpos
        exact (Nat.card_pos_iff.mp hSpos).1
      have hSle : MulAction.stabilizer A μ ≤ MulAction.stabilizer A ν := fun b hb =>
        MulAction.mem_stabilizer_iff.mpr (hν b hb)
      obtain ⟨⟨ω₀, hω₀⟩⟩ :
          Nonempty {ω' : Ω // ∀ b ∈ MulAction.stabilizer A ν, b • ω' = ω'} := by
        have hTpos : 0 < Nat.card {l : Λ // ∀ b ∈ MulAction.stabilizer A ν, b • l = l} := by
          haveI : Nonempty {l : Λ // ∀ b ∈ MulAction.stabilizer A ν, b • l = l} :=
            ⟨⟨ν, fun b hb => MulAction.mem_stabilizer_iff.mp hb⟩⟩
          exact Nat.card_pos
        rw [← hcount (MulAction.stabilizer A ν)] at hTpos
        exact (Nat.card_pos_iff.mp hTpos).1
      have hstab : MulAction.stabilizer A ν = MulAction.stabilizer A μ :=
        eq_stabilizer_of_le_of_orbit_card_min hmin hSle hω₀
      have hstab' : MulAction.stabilizer A μ = MulAction.stabilizer A ν := hstab.symm
      -- Orbit complements are A-invariant.
      have hUinv : ∀ (a : A) (ω' : Ω),
          ω' ∉ MulAction.orbit A μ → a • ω' ∉ MulAction.orbit A μ := by
        intro a ω' hω' hmem
        exact hω' (by simpa using MulAction.mem_orbit_of_mem_orbit a⁻¹ hmem)
      have hVinv : ∀ (a : A) (l : Λ),
          l ∉ MulAction.orbit A ν → a • l ∉ MulAction.orbit A ν := by
        intro a l hl hmem
        exact hl (by simpa using MulAction.mem_orbit_of_mem_orbit a⁻¹ hmem)
      letI actΩ' : MulAction A {ω' : Ω // ω' ∉ MulAction.orbit A μ} :=
        { smul := fun a x => ⟨a • x.1, hUinv a x.1 x.2⟩
          one_smul := fun x => Subtype.ext (one_smul A x.1)
          mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1) }
      letI actΛ' : MulAction A {l : Λ // l ∉ MulAction.orbit A ν} :=
        { smul := fun a x => ⟨a • x.1, hVinv a x.1 x.2⟩
          one_smul := fun x => Subtype.ext (one_smul A x.1)
          mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1) }
      -- Step 4: the equivariant bijection A•μ ≃ A ⧸ S ≃ A•ν, characterized by c•μ ↦ c•ν.
      let e : {ω' : Ω // ω' ∈ MulAction.orbit A μ} ≃ {l : Λ // l ∈ MulAction.orbit A ν} :=
        (MulAction.orbitEquivQuotientStabilizer A μ).trans
          ((Subgroup.quotientEquivOfEq hstab').trans
            (MulAction.orbitEquivQuotientStabilizer A ν).symm)
      have he : ∀ (c : A) (h : c • μ ∈ MulAction.orbit A μ),
          e ⟨c • μ, h⟩ = ⟨c • ν, MulAction.mem_orbit ν c⟩ := by
        intro c h
        have h0 : (⟨c • μ, h⟩ : {ω' : Ω // ω' ∈ MulAction.orbit A μ}) =
            (MulAction.orbitEquivQuotientStabilizer A μ).symm (QuotientGroup.mk c) :=
          Subtype.ext (MulAction.orbitEquivQuotientStabilizer_symm_apply A μ c).symm
        change (MulAction.orbitEquivQuotientStabilizer A ν).symm
            ((Subgroup.quotientEquivOfEq hstab')
              ((MulAction.orbitEquivQuotientStabilizer A μ) ⟨c • μ, h⟩)) =
            ⟨c • ν, MulAction.mem_orbit ν c⟩
        rw [h0, Equiv.apply_symm_apply, Subgroup.quotientEquivOfEq_mk]
        exact Subtype.ext (MulAction.orbitEquivQuotientStabilizer_symm_apply A ν c)
      -- Step 5a: e preserves B-fixedness (via conjugates in the common stabilizer).
      have htransfer : ∀ (B : Subgroup A) (x : {ω' : Ω // ω' ∈ MulAction.orbit A μ}),
          (∀ b ∈ B, b • x.1 = x.1) ↔ ∀ b ∈ B, b • (e x).1 = (e x).1 := by
        intro B x
        obtain ⟨x, hx⟩ := x
        obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.mp hx
        rw [he c hx]
        change (∀ b ∈ B, b • c • μ = c • μ) ↔ ∀ b ∈ B, b • c • ν = c • ν
        constructor <;> intro H b hb
        · have h1 := (smul_smul_eq_self_iff_conj_mem_stabilizer b c μ).mp (H b hb)
          rw [← hstab] at h1
          exact (smul_smul_eq_self_iff_conj_mem_stabilizer b c ν).mpr h1
        · have h1 := (smul_smul_eq_self_iff_conj_mem_stabilizer b c ν).mp (H b hb)
          rw [hstab] at h1
          exact (smul_smul_eq_self_iff_conj_mem_stabilizer b c μ).mpr h1
      -- Step 5b: fixed-point counts agree on the orbit complements.
      have hcomplement : ∀ B : Subgroup A,
          Nat.card {y : {ω' : Ω // ω' ∉ MulAction.orbit A μ} // ∀ b ∈ B, b • y = y} =
            Nat.card {z : {l : Λ // l ∉ MulAction.orbit A ν} // ∀ b ∈ B, b • z = z} := by
        intro B
        have h1 : Nat.card {ω' : Ω // ∀ b ∈ B, b • ω' = ω'} =
            Nat.card {y : {ω' : Ω // ω' ∈ MulAction.orbit A μ} // ∀ b ∈ B, b • y.1 = y.1} +
              Nat.card {y : {ω' : Ω // ω' ∉ MulAction.orbit A μ} // ∀ b ∈ B, b • y.1 = y.1} :=
          nat_card_subtype_split _ _
        have h2 : Nat.card {l : Λ // ∀ b ∈ B, b • l = l} =
            Nat.card {z : {l : Λ // l ∈ MulAction.orbit A ν} // ∀ b ∈ B, b • z.1 = z.1} +
              Nat.card {z : {l : Λ // l ∉ MulAction.orbit A ν} // ∀ b ∈ B, b • z.1 = z.1} :=
          nat_card_subtype_split _ _
        have h3 : Nat.card
              {y : {ω' : Ω // ω' ∈ MulAction.orbit A μ} // ∀ b ∈ B, b • y.1 = y.1} =
            Nat.card {z : {l : Λ // l ∈ MulAction.orbit A ν} // ∀ b ∈ B, b • z.1 = z.1} :=
          Nat.card_congr (Equiv.subtypeEquiv e (htransfer B))
        have h4 := hcount B
        have h5 : Nat.card
              {y : {ω' : Ω // ω' ∉ MulAction.orbit A μ} // ∀ b ∈ B, b • y = y} =
            Nat.card {y : {ω' : Ω // ω' ∉ MulAction.orbit A μ} // ∀ b ∈ B, b • y.1 = y.1} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun y =>
            ⟨fun H b hb => Subtype.ext_iff.mp (H b hb), fun H b hb => Subtype.ext (H b hb)⟩)
        have h6 : Nat.card
              {z : {l : Λ // l ∉ MulAction.orbit A ν} // ∀ b ∈ B, b • z = z} =
            Nat.card {z : {l : Λ // l ∉ MulAction.orbit A ν} // ∀ b ∈ B, b • z.1 = z.1} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun z =>
            ⟨fun H b hb => Subtype.ext_iff.mp (H b hb), fun H b hb => Subtype.ext (H b hb)⟩)
        omega
      -- Step 6: the complement is strictly smaller; apply the induction hypothesis.
      have hsplitΩ : Nat.card Ω =
          Nat.card {ω' : Ω // ω' ∈ MulAction.orbit A μ} +
            Nat.card {ω' : Ω // ω' ∉ MulAction.orbit A μ} := by
        rw [← Nat.card_sum]
        exact (Nat.card_congr (Equiv.sumCompl fun ω' : Ω => ω' ∈ MulAction.orbit A μ)).symm
      have hUpos : 0 < Nat.card {ω' : Ω // ω' ∈ MulAction.orbit A μ} := by
        haveI : Nonempty {ω' : Ω // ω' ∈ MulAction.orbit A μ} :=
          ⟨⟨μ, MulAction.mem_orbit_self μ⟩⟩
        exact Nat.card_pos
      have hlt : Nat.card {ω' : Ω // ω' ∉ MulAction.orbit A μ} < n := by omega
      obtain ⟨f', hf'⟩ := ih (Nat.card {ω' : Ω // ω' ∉ MulAction.orbit A μ}) hlt
        {ω' : Ω // ω' ∉ MulAction.orbit A μ} {l : Λ // l ∉ MulAction.orbit A ν}
        rfl hcomplement
      -- Step 7: glue e (on the orbit) and f' (on the complement).
      let fglue : Ω ≃ Λ :=
        (Equiv.sumCompl fun ω' : Ω => ω' ∈ MulAction.orbit A μ).symm.trans
          ((e.sumCongr f').trans (Equiv.sumCompl fun l : Λ => l ∈ MulAction.orbit A ν))
      have fpos : ∀ d : A, fglue (d • μ) = d • ν := by
        intro d
        change (Equiv.sumCompl fun l : Λ => l ∈ MulAction.orbit A ν)
            ((e.sumCongr f')
              ((Equiv.sumCompl fun ω' : Ω => ω' ∈ MulAction.orbit A μ).symm (d • μ))) =
            d • ν
        rw [Equiv.sumCompl_symm_apply_of_pos (p := fun ω' : Ω => ω' ∈ MulAction.orbit A μ)
            (MulAction.mem_orbit μ d),
          Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl,
          he d (MulAction.mem_orbit μ d)]
      have fneg : ∀ x : {ω' : Ω // ω' ∉ MulAction.orbit A μ}, fglue x.1 = (f' x).1 := by
        intro x
        change (Equiv.sumCompl fun l : Λ => l ∈ MulAction.orbit A ν)
            ((e.sumCongr f')
              ((Equiv.sumCompl fun ω' : Ω => ω' ∈ MulAction.orbit A μ).symm x.1)) =
            (f' x).1
        rw [Equiv.sumCompl_symm_apply_of_neg (p := fun ω' : Ω => ω' ∈ MulAction.orbit A μ) x.2,
          Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
      refine ⟨fglue, fun a ω => ?_⟩
      by_cases h : ω ∈ MulAction.orbit A μ
      · obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.mp h
        calc fglue (a • c • μ) = fglue ((a * c) • μ) := by rw [mul_smul]
          _ = (a * c) • ν := fpos (a * c)
          _ = a • c • ν := mul_smul a c ν
          _ = a • fglue (c • μ) := by rw [fpos c]
      · have h1 : fglue (a • ω) =
            (f' (a • (⟨ω, h⟩ : {ω' : Ω // ω' ∉ MulAction.orbit A μ}))).1 :=
          fneg (a • ⟨ω, h⟩)
        have h2 : f' (a • (⟨ω, h⟩ : {ω' : Ω // ω' ∉ MulAction.orbit A μ})) =
            a • f' ⟨ω, h⟩ := hf' a ⟨ω, h⟩
        have h3 : fglue ω = (f' ⟨ω, h⟩).1 := fneg ⟨ω, h⟩
        rw [h1, h2, h3]
        rfl

/-- **Isaacs Lemma 3.33** (equivariant bijection lemma; Hartley–Turull cluster, p. 105).
群 `A` が有限集合 `Ω`, `Λ` に作用し, **任意の**部分群 `B ≤ A` について `B` の固定点数が
`Ω` と `Λ` で一致するならば, `A`-equivariant な全単射 `f : Ω ≃ Λ` が存在する.

**証明** (Isaacs pp. 105-106): `|Ω|` の強帰納法 (`exists_equivariant_equiv_aux`).
軌道サイズ最小の `μ ∈ Ω`, `S := stab_A(μ)` を取ると, 最小性から「`S ≤ H` が固定点を
もてば `H = S`」. 固定点数の仮定で `S`-固定点 `ν ∈ Λ` を取れば `stab_A(ν) = S` となり,
orbit-stabilizer 定理で `A•μ ≃ A ⧸ S ≃ A•ν` が equivariant 全単射. 固定点数を軌道と
補集合に分割すれば補集合対も仮定を満たし (軌道上の `B`-固定点対応は
`c⁻¹bc ∈ S` への言い換えで両側一致), 帰納法で得た補集合上の全単射と貼り合わせる. -/
theorem exists_equivariant_equiv_of_card_fixedPoints_eq
    {Ω : Type u} {Λ : Type v} [Finite Ω] [Finite Λ] [MulAction A Ω] [MulAction A Λ]
    (hcount : ∀ B : Subgroup A,
      Nat.card (MulAction.fixedPoints B Ω) = Nat.card (MulAction.fixedPoints B Λ)) :
    ∃ f : Ω ≃ Λ, ∀ (a : A) (ω : Ω), f (a • ω) = a • f ω := by
  apply exists_equivariant_equiv_aux (Nat.card Ω) Ω Λ rfl
  intro B
  have hΩ : Nat.card (MulAction.fixedPoints B Ω) =
      Nat.card {ω : Ω // ∀ b ∈ B, b • ω = ω} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun ω => by
      rw [MulAction.mem_fixedPoints]
      exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b.1 b.2⟩)
  have hΛ : Nat.card (MulAction.fixedPoints B Λ) =
      Nat.card {l : Λ // ∀ b ∈ B, b • l = l} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun l => by
      rw [MulAction.mem_fixedPoints]
      exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b.1 b.2⟩)
  rw [← hΩ, ← hΛ]
  exact hcount B

end

section /- 3E: Theorem 3.31 Hartley–Turull (pp. 105-107) -/

open OddOrder.GroupTheory (fixedSubgroup)
open _root_.OddOrder.Isaacs.Ch03 (IsAInvariant)
open scoped commutatorElement

/-! ### 支持補題: 制限作用・積作用の固定点 -/

/-- `A`-不変部分群は制限作用 `φ ∘ B.subtype` でも不変. -/
private theorem isAInvariant_comp_subtype {G : Type*} [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} (hN : IsAInvariant φ N) (B : Subgroup A) :
    IsAInvariant (φ.comp B.subtype) N :=
  fun b => hN (B.subtype b)

/-- 橋渡し: 制限作用 `φ ∘ B.subtype` の全体固定部分群は `fixedSubgroup φ B`. -/
private theorem fixedSubgroup_comp_subtype_top {G : Type*} [Group G] (φ : A →* MulAut G)
    (B : Subgroup A) :
    fixedSubgroup (φ.comp B.subtype) (⊤ : Subgroup ↥B) = fixedSubgroup φ B := by
  ext g
  constructor
  · intro h l hl
    exact h ⟨l, hl⟩ trivial
  · intro h b _
    exact h b.1 b.2

/-- `A`-不変部分群 `N` への制限作用の `B`-固定点は `N ⊓ C_G(B)` と同数
(実際には部分群として一致する; カード形で使う). -/
theorem card_fixedSubgroup_restrict {G : Type*} [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} (hN : IsAInvariant φ N) (B : Subgroup A) :
    Nat.card ↥(fixedSubgroup hN.restrict B) = Nat.card ↥(N ⊓ fixedSubgroup φ B) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1,
        Subgroup.mem_inf.mpr ⟨x.1.2, fun l hl => congrArg Subtype.val (x.2 l hl)⟩⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩,
        fun l hl => Subtype.ext ((Subgroup.mem_inf.mp y.2).2 l hl)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- 成分ごとの `MulAut` 作用の binary 積. -/
private def prodMulAutHom {H₁ H₂ : Type*} [Group H₁] [Group H₂]
    (ψ₁ : A →* MulAut H₁) (ψ₂ : A →* MulAut H₂) : A →* MulAut (H₁ × H₂) where
  toFun a := (ψ₁ a).prodCongr (ψ₂ a)
  map_one' := MulEquiv.ext fun x => by
    change ((ψ₁ 1) x.1, (ψ₂ 1) x.2) = x
    rw [map_one, map_one]
    rfl
  map_mul' a b := MulEquiv.ext fun x => by
    change ((ψ₁ (a * b)) x.1, (ψ₂ (a * b)) x.2) =
      ((ψ₁ a) ((ψ₁ b) x.1), (ψ₂ a) ((ψ₂ b) x.2))
    rw [map_mul, map_mul]
    rfl

/-- Binary 積作用の固定点数は成分の固定点数の積. -/
private theorem card_fixedSubgroup_prodMulAutHom {H₁ H₂ : Type*} [Group H₁] [Group H₂]
    (ψ₁ : A →* MulAut H₁) (ψ₂ : A →* MulAut H₂) (B : Subgroup A) :
    Nat.card ↥(fixedSubgroup (prodMulAutHom ψ₁ ψ₂) B) =
      Nat.card ↥(fixedSubgroup ψ₁ B) * Nat.card ↥(fixedSubgroup ψ₂ B) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => (⟨x.1.1, fun l hl => congrArg Prod.fst (x.2 l hl)⟩,
        ⟨x.1.2, fun l hl => congrArg Prod.snd (x.2 l hl)⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1),
        fun l hl => Prod.ext (y.1.2 l hl) (y.2.2 l hl)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

/-- 成分ごとの `MulAut` 作用の (依存) 有限積. -/
private def piMulAutHom {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
    (ψ : ∀ i, A →* MulAut (M i)) : A →* MulAut (∀ i, M i) where
  toFun a := MulEquiv.piCongrRight fun i => ψ i a
  map_one' := MulEquiv.ext fun x => funext fun i => by
    change (ψ i 1) (x i) = x i
    rw [map_one]
    rfl
  map_mul' a b := MulEquiv.ext fun x => funext fun i => by
    change (ψ i (a * b)) (x i) = (ψ i a) ((ψ i b) (x i))
    rw [map_mul]
    rfl

/-- 積作用の固定点数は成分の固定点数の積 (依存 Pi 版). -/
private theorem card_fixedSubgroup_piMulAutHom {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, Group (M i)] (ψ : ∀ i, A →* MulAut (M i)) (B : Subgroup A) :
    Nat.card ↥(fixedSubgroup (piMulAutHom ψ) B) =
      ∏ i, Nat.card ↥(fixedSubgroup (ψ i) B) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, fun l hl => congrFun (x.2 l hl) i⟩
      invFun := fun y => ⟨fun i => (y i).1, fun l hl => funext fun i => (y i).2 l hl⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

/-- 数値補助: `m ∣ n`, `n ≠ 0` なら `n` の全素因子にわたる `m` の p-part の積は `m`.
(`m` の素因子は全て `n` の素因子で, 残りは `p^0 = 1`.) -/
private theorem prod_primeFactors_pow_factorization_eq {n : ℕ} (hn : n ≠ 0) {m : ℕ}
    (hm : m ∣ n) : ∏ p ∈ n.primeFactors, p ^ m.factorization p = m := by
  have hm0 : m ≠ 0 := fun h => hn (zero_dvd_iff.mp (h ▸ hm))
  have hsub : m.factorization.support ⊆ n.primeFactors := by
    rw [Nat.support_factorization]
    exact Nat.primeFactors_mono hm hn
  have h : m.factorization.prod (fun p k => p ^ k) =
      ∏ p ∈ n.primeFactors, p ^ m.factorization p :=
    Finsupp.prod_of_support_subset m.factorization hsub (fun p k => p ^ k)
      fun p _ => pow_zero p
  rw [← h]
  exact Nat.prod_factorization_pow_eq_self hm0

/-! ### Step 1: nilpotent 化 (A-不変 Sylow の直積) -/

/-- **Isaacs Thm 3.31, Step 1** (p. 106): coprime + solvable 作用 `φ : A →* MulAut G`
に対し, **solvable** (実際には nilpotent) な群 `H` への作用 `ψ` で全部分群 `B ≤ A` の
固定点数が `G` と一致し `|H| = |G|` となるものが存在する.

**証明**: `|G|` の各素因子 `p` に A-不変 Sylow `P_p` を選び (Thm 3.23(a)),
`H := Π_p P_p` に成分ごとの作用を入れる. Lemma 3.32 より各 `B` で
`|C_{P_p}(B)| = |P_p ∩ C_G(B)|` は `|C_G(B)|` の full `p`-part なので, 積は
`|C_G(B)|` に一致する. -/
theorem exists_solvable_fixedPoint_replacement [Finite A]
    {G : Type u} [Group G] [Finite G] (φ : A →* MulAut G)
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    ∃ (H : Type u) (_ : Group H) (_ : Finite H) (ψ : A →* MulAut H),
      IsSolvable H ∧ Nat.card H = Nat.card G ∧
      ∀ B : Subgroup A,
        Nat.card ↥(fixedSubgroup φ B) = Nat.card ↥(fixedSubgroup ψ B) := by
  classical
  have hPP : ∀ p : (Nat.card G).primeFactors,
      ∃ P : Sylow (p : ℕ) G, IsAInvariant φ (P : Subgroup G) := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact exists_aInvariant_sylow hCop hSolv p
  choose P hP using hPP
  refine ⟨∀ p : (Nat.card G).primeFactors, ↥(P p : Subgroup G), inferInstance, inferInstance,
    piMulAutHom fun p => (hP p).restrict, ?_, ?_, ?_⟩
  · -- solvability: each factor is a p-group, hence nilpotent; a finite product of
    -- nilpotent groups is nilpotent, hence solvable.
    haveI : ∀ p : (Nat.card G).primeFactors, Group.IsNilpotent ↥(P p : Subgroup G) := by
      intro p
      haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      exact (P p).isPGroup'.isNilpotent
    infer_instance
  · -- cardinality: ∏_p |P_p| = ∏_p p-part of |G| = |G|.
    calc Nat.card (∀ p : (Nat.card G).primeFactors, ↥(P p : Subgroup G))
        = ∏ p : (Nat.card G).primeFactors, Nat.card ↥(P p : Subgroup G) := Nat.card_pi
      _ = ∏ p : (Nat.card G).primeFactors, (p : ℕ) ^ (Nat.card G).factorization (p : ℕ) := by
          refine Finset.prod_congr rfl fun p _ => ?_
          haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
          exact (P p).card_eq_multiplicity
      _ = ∏ p ∈ (Nat.card G).primeFactors, p ^ (Nat.card G).factorization p :=
          Finset.prod_finset_coe (fun p => p ^ (Nat.card G).factorization p) _
      _ = Nat.card G := prod_primeFactors_pow_factorization_eq Nat.card_pos.ne' dvd_rfl
  · -- fixed-point counts: Lemma 3.32 applied to the restricted B-action, prime by prime.
    intro B
    have hCopB : Nat.Coprime (Nat.card ↥B) (Nat.card G) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B)
    have hSolvB : IsSolvable ↥B ∨ IsSolvable G := by
      rcases hSolv with hA | hG
      · exact Or.inl (by haveI := hA; infer_instance)
      · exact Or.inr hG
    have hdvdC : Nat.card ↥(fixedSubgroup φ B) ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card _
    calc Nat.card ↥(fixedSubgroup φ B)
        = ∏ p ∈ (Nat.card G).primeFactors,
            p ^ (Nat.card ↥(fixedSubgroup φ B)).factorization p :=
          (prod_primeFactors_pow_factorization_eq Nat.card_pos.ne' hdvdC).symm
      _ = ∏ p : (Nat.card G).primeFactors,
            (p : ℕ) ^ (Nat.card ↥(fixedSubgroup φ B)).factorization (p : ℕ) :=
          (Finset.prod_finset_coe
            (fun p => p ^ (Nat.card ↥(fixedSubgroup φ B)).factorization p) _).symm
      _ = ∏ p : (Nat.card G).primeFactors,
            Nat.card ↥(fixedSubgroup ((hP p).restrict) B) := by
          refine Finset.prod_congr rfl fun p _ => ?_
          haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
          have h332 := card_inf_fixedSubgroup_of_aInvariant_sylow
            (φ := φ.comp B.subtype) hCopB hSolvB (isAInvariant_comp_subtype (hP p) B)
          rw [fixedSubgroup_comp_subtype_top] at h332
          rw [card_fixedSubgroup_restrict (hP p) B, h332]
      _ = Nat.card ↥(fixedSubgroup (piMulAutHom fun p => (hP p).restrict) B) :=
          (card_fixedSubgroup_piMulAutHom _ B).symm

/-! ### Step 2: abelian 化 (導来部分群と商の積, 位数の強帰納法) -/

/-- **固定点数の積公式** (Isaacs p. 107 の核; Cor 3.28 の帰結): coprime + solvable 作用と
`A`-不変正規部分群 `N ⊴ G` に対し `|C_G(B)| = |N ∩ C_G(B)| · |C_{G/N}(B)|`.

**証明**: 制限 `C_G(B) → G/N` の核は `N ∩ C_G(B)`, 像は `C_{G/N}(B)` (像 ⊇ は
Cor 3.28 = `coprime_fixedPoints_quotient` の `B`-制限作用への適用) で第一同型定理. -/
theorem card_fixedSubgroup_eq_mul_of_normal [Finite A]
    {G : Type u} [Group G] [Finite G] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN : IsAInvariant φ N) (B : Subgroup A) :
    Nat.card ↥(fixedSubgroup φ B) =
      Nat.card ↥(N ⊓ fixedSubgroup φ B) *
        Nat.card ↥(fixedSubgroup hN.quotientMulAutHom B) := by
  classical
  have hCopB : Nat.Coprime (Nat.card ↥B) (Nat.card G) :=
    hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B)
  have hSolvB : IsSolvable ↥B ∨ IsSolvable G := by
    rcases hSolv with hA | hG
    · exact Or.inl (by haveI := hA; infer_instance)
    · exact Or.inr hG
  let f : ↥(fixedSubgroup φ B) →* G ⧸ N :=
    (QuotientGroup.mk' N).comp (fixedSubgroup φ B).subtype
  -- range f = C_{G/N}(B); the ⊇ inclusion is Cor 3.28 for the restricted B-action.
  have hrange : f.range = fixedSubgroup hN.quotientMulAutHom B := by
    ext q
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      intro l hl
      change hN.quotientMulAutHom l (QuotientGroup.mk' N c) = QuotientGroup.mk' N c
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk', hc l hl]
    · intro hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      have hg_fix : ∀ b : ↥B, ∃ n ∈ N, (φ b.1) g = g * n := by
        intro b
        have hb := hq b.1 b.2
        rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk',
          QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
        exact ⟨g⁻¹ * (φ b.1) g, by simpa using N.inv_mem hb, by group⟩
      obtain ⟨c, hc_fix, n, hn_mem, hcn⟩ :=
        coprime_fixedPoints_quotient (φ := φ.comp B.subtype) hCopB hSolvB
          (isAInvariant_comp_subtype hN B) hg_fix
      refine ⟨⟨c, fun l hl => hc_fix ⟨l, hl⟩⟩, ?_⟩
      change QuotientGroup.mk' N c = QuotientGroup.mk' N g
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcn]
      simpa using N.inv_mem hn_mem
  -- ker f ≃ N ⊓ C_G(B).
  have hker_card : Nat.card ↥f.ker = Nat.card ↥(N ⊓ fixedSubgroup φ B) := by
    have hmem : ∀ x : ↥(fixedSubgroup φ B), x ∈ f.ker ↔ (x : G) ∈ N := by
      intro x
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' N (x : G) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨(hmem x.1).mp x.2, x.1.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).2⟩,
          (hmem ⟨y.1, (Subgroup.mem_inf.mp y.2).2⟩).mpr (Subgroup.mem_inf.mp y.2).1⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hquot_card : Nat.card (↥(fixedSubgroup φ B) ⧸ f.ker) =
      Nat.card ↥(fixedSubgroup hN.quotientMulAutHom B) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  calc Nat.card ↥(fixedSubgroup φ B)
      = Nat.card (↥(fixedSubgroup φ B) ⧸ f.ker) * Nat.card ↥f.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    _ = Nat.card ↥(fixedSubgroup hN.quotientMulAutHom B) *
          Nat.card ↥(N ⊓ fixedSubgroup φ B) := by rw [hquot_card, hker_card]
    _ = Nat.card ↥(N ⊓ fixedSubgroup φ B) *
          Nat.card ↥(fixedSubgroup hN.quotientMulAutHom B) := Nat.mul_comm _ _

/-- Thm 3.31, Step 2 の帰納法エンジン: solvable な `G` は位数の強帰納法で abelian 置換
をもつ. 非可換なら `G' × (G/G')` (成分位数はいずれも真に減る) に帰着し, 固定点数は
`card_fixedSubgroup_eq_mul_of_normal` で分解する. -/
private theorem exists_abelian_replacement_aux [Finite A] (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [IsSolvable G] (φ : A →* MulAut G),
      Nat.card G = n →
      Nat.Coprime (Nat.card A) (Nat.card G) →
      ∃ (H : Type u) (_ : CommGroup H) (_ : Finite H) (ψ : A →* MulAut H),
        Nat.card H = Nat.card G ∧
        ∀ B : Subgroup A,
          Nat.card ↥(fixedSubgroup φ B) = Nat.card ↥(fixedSubgroup ψ B) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ φ hn hCop
    by_cases habel : commutator G = ⊥
    · -- G is abelian: take H := G itself.
      have hcomm : ∀ x y : G, x * y = y * x := by
        intro x y
        have hxy : ⁅x, y⁆ ∈ commutator G :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [habel, Subgroup.mem_bot] at hxy
        exact commutatorElement_eq_one_iff_mul_comm.mp hxy
      refine ⟨G, { ‹Group G› with mul_comm := hcomm }, ‹Finite G›, φ, rfl, ?_⟩
      intro B
      rfl
    · -- G is nonabelian: recurse on G' and G/G'.
      have hN_inv : IsAInvariant φ (commutator G) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.commutator_self φ
      -- commutator G ≠ ⊤ (else the derived series never reaches ⊥).
      have hN_ne_top : commutator G ≠ ⊤ := by
        intro htop
        have hall : ∀ k, derivedSeries G k = ⊤ := by
          intro k
          induction k with
          | zero => exact derivedSeries_zero G
          | succ k ihk => rw [derivedSeries_succ, ihk]; exact htop
        obtain ⟨k, hk⟩ := IsSolvable.solvable (G := G)
        rw [hall k] at hk
        exact habel (le_bot_iff.mp (hk ▸ le_top))
      -- both components have strictly smaller order.
      have hlt₁ : Nat.card ↥(commutator G) < n := by
        rcases lt_or_eq_of_le (Subgroup.card_le_card_group (commutator G)) with h | h
        · omega
        · exact absurd (Subgroup.eq_top_of_card_eq _ h) hN_ne_top
      have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator G)
      have hlt₂ : Nat.card (G ⧸ commutator G) < n := by
        have h1 : 1 < Nat.card ↥(commutator G) :=
          (Subgroup.one_lt_card_iff_ne_bot (commutator G)).mpr habel
        have hq_pos : 0 < Nat.card (G ⧸ commutator G) := Nat.card_pos
        calc Nat.card (G ⧸ commutator G)
            < Nat.card (G ⧸ commutator G) * Nat.card ↥(commutator G) :=
              (lt_mul_iff_one_lt_right hq_pos).mpr h1
          _ = Nat.card G := hprod.symm
          _ = n := hn
      -- coprimality descends to both components.
      have hCop_sub : Nat.Coprime (Nat.card A) (Nat.card ↥(commutator G)) :=
        hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
      have hCop_quot : Nat.Coprime (Nat.card A) (Nat.card (G ⧸ commutator G)) :=
        hCop.coprime_dvd_right (Subgroup.card_quotient_dvd_card _)
      -- recursive calls.
      obtain ⟨H₁, instH₁, instF₁, ψ₁, hcard₁, hfix₁⟩ :=
        ih (Nat.card ↥(commutator G)) hlt₁ ↥(commutator G) hN_inv.restrict rfl hCop_sub
      obtain ⟨H₂, instF₂', instF₂, ψ₂, hcard₂, hfix₂⟩ :=
        ih (Nat.card (G ⧸ commutator G)) hlt₂ (G ⧸ commutator G)
          hN_inv.quotientMulAutHom rfl hCop_quot
      letI := instH₁
      letI := instF₁
      letI := instF₂'
      letI := instF₂
      refine ⟨H₁ × H₂, inferInstance, inferInstance, prodMulAutHom ψ₁ ψ₂, ?_, ?_⟩
      · rw [Nat.card_prod, hcard₁, hcard₂, mul_comm]
        exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator G)).symm
      · intro B
        rw [card_fixedSubgroup_prodMulAutHom ψ₁ ψ₂ B, ← hfix₁ B, ← hfix₂ B,
          card_fixedSubgroup_restrict hN_inv B]
        exact card_fixedSubgroup_eq_mul_of_normal hCop (Or.inr ‹IsSolvable G›) hN_inv B

/-- **Isaacs Thm 3.31** (Hartley–Turull, pp. 105-107): `A` が有限群 `G` に coprime に
自己同型作用し (`(|A|, |G|) = 1`), `A` か `G` の一方が solvable なら, **abelian** な
有限群 `H` への作用 `ψ : A →* MulAut H` で

* `|H| = |G|`, かつ
* 全ての部分群 `B ≤ A` について `|C_G(B)| = |C_H(B)|`

を満たすものが存在する.

**証明** (Isaacs pp. 106-107): 2 段. Step 1 (`exists_solvable_fixedPoint_replacement`)
で `G` を A-不変 Sylow の直積 (nilpotent, 特に solvable) に置換し (Lemma 3.32 で
固定点数保存), Step 2 (`exists_abelian_replacement_aux`) で solvable 群を位数の
強帰納法により `G' × (G/G')` を経て abelian 群に置換する (Cor 3.28 由来の積公式
`card_fixedSubgroup_eq_mul_of_normal` で固定点数保存). -/
theorem exists_abelian_fixedPoint_replacement [Finite A]
    {G : Type u} [Group G] [Finite G] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    ∃ (H : Type u) (_ : CommGroup H) (_ : Finite H) (ψ : A →* MulAut H),
      Nat.card H = Nat.card G ∧
      ∀ B : Subgroup A,
        Nat.card ↥(fixedSubgroup φ B) = Nat.card ↥(fixedSubgroup ψ B) := by
  obtain ⟨N, instN, instNF, ψN, hsolvN, hcardN, hfixN⟩ :=
    exists_solvable_fixedPoint_replacement φ hCop hSolv
  letI := instN
  letI := instNF
  haveI := hsolvN
  obtain ⟨H, instH, instHF, ψH, hcardH, hfixH⟩ :=
    exists_abelian_replacement_aux (Nat.card N) N ψN rfl (by rw [hcardN]; exact hCop)
  exact ⟨H, instH, instHF, ψH, by rw [hcardH, hcardN],
    fun B => (hfixN B).trans (hfixH B)⟩

end

end OddOrder.Isaacs.Ch04
