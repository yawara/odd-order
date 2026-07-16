/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# Isaacs §3E: Hartley–Turull cluster (Lemmas 3.31–3.34, pp. 105-108)

この leaf は Hartley–Turull 定理 (Thm 3.31) とその支持補題群のうち,
まず **Lemma 3.33** (equivariant bijection lemma) を実装する:
全部分群 `B ≤ A` の固定点数が一致する 2 つの有限 `A`-集合の間には
`A`-equivariant 全単射が存在する (純組合せ; 群論的前提なし).

## 主要結果

| Isaacs # | Lean | 状態 |
|---|---|---|
| Lem 3.33 | `exists_equivariant_equiv_of_card_fixedPoints_eq` | ✅ |

## 証明構造 (Isaacs pp. 105-106)

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

end OddOrder.Isaacs.Ch04
