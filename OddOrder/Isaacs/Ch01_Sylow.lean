/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Sylow

/-!
# OddOrder.Isaacs.Ch01 — Sylow Theory

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 1
"Sylow Theory" (pp. 1-44) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 1A | 群作用と Fundamental Counting Principle | 1.1 – 1.6 | 着手中 |
| 1B | Sylow の存在定理 (Sylow E), Cauchy | 1.7 – 1.10 | TODO |
| 1C | Sylow の共役 (Sylow C / D), Frattini argument | 1.11 – 1.18 | TODO |
| 1D | 冪零群, Fitting 部分群 `F(G)` | 1.19 – 1.29 | TODO |
| 1E | 位数 \|G\|=2n (n 奇) の指数 2 正規部分群 など | 1.30 – 1.36 | TODO |
| 1F | Brodkey の定理 (Sylow が abelian の場合) | 1.37 – 1.40 | 完了 |
| 1G | Chermak–Delgado | 1.41 – 1.46 | TODO |

## 方針

mathlib 既存資産 (`Sylow`, `MulAction.orbitEquivQuotientStabilizer`,
`Subgroup.normalCore`, `Subgroup.normalCore_eq_ker`) を最大限再利用し、
Isaacs の流儀で主張を再述する薄いラッパーを与える。

主要な新規実装ターゲット (mathlib 未収載):

* **§1D Thm 1.28**: Fitting 部分群 `Fit(G)` の定義 + 「最大冪零正規部分群である」
  ことの証明 (Phase 1 の最初の本格的な新規実装)

ノート: [notes/isaacs/ch01_sylow.md](../../notes/isaacs/ch01_sylow.md)
-/

namespace OddOrder.Isaacs.Ch01

section /- 1A: Group actions and the Fundamental Counting Principle (pp. 1-10) -/

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 1.1**.  部分群 `H ≤ G` の coset 集合 `G ⧸ H` への右乗法作用の
permutation 表現 `G → Sym(G ⧸ H)` の核は `core_G(H) = H.normalCore` に一致する。
従って `G / core_G(H)` は `Sym(G ⧸ H)` の部分群と同型 (第一同型定理).

mathlib `Subgroup.normalCore_eq_ker` の再述. -/
theorem normalCore_eq_perm_ker (H : Subgroup G) :
    H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker :=
  H.normalCore_eq_ker

/-- **Isaacs Thm 1.4** (Fundamental Counting Principle).  `G` が `Ω` に作用し
`α ∈ Ω` の軌道 `O` と固定部分群 `H = G_α` を取ると, `O ≃ G ⧸ H`
(orbit-stabilizer theorem の "全単射" 部分).

mathlib `MulAction.orbitEquivQuotientStabilizer` の Isaacs 流再述. -/
noncomputable def fundamentalCountingEquiv
    {Ω : Type*} [MulAction G Ω] (α : Ω) :
    MulAction.orbit G α ≃ G ⧸ MulAction.stabilizer G α :=
  MulAction.orbitEquivQuotientStabilizer G α

/-- **Isaacs Cor 1.2**.  `H ≤ G` で `[G:H] = n` なら，`N := core_G(H) = H.normalCore` は
`N ◁ G`, `N ≤ H` であり，`[G:N] ∣ n!`.

証明: Thm 1.1 より `G/N ↪ Sym(G/H) ≅ S_n`，よって `|G/N| ∣ |S_n| = n!`．
mathlib では `H.normalCore_eq_ker` → `index_ker` → `card_subgroup_dvd_card` + `Nat.card_perm`
を組み合わせる. -/
theorem normalCore_index_dvd_factorial (H : Subgroup G) [Finite (G ⧸ H)] :
    H.normalCore.Normal ∧ H.normalCore ≤ H ∧
      H.normalCore.index ∣ Nat.factorial H.index := by
  refine ⟨inferInstance, H.normalCore_le, ?_⟩
  rw [H.normalCore_eq_ker, Subgroup.index_ker]
  calc Nat.card (MulAction.toPermHom G (G ⧸ H)).range
      ∣ Nat.card (Equiv.Perm (G ⧸ H)) := Subgroup.card_subgroup_dvd_card _
    _ = Nat.factorial (Nat.card (G ⧸ H)) := Nat.card_perm
    _ = Nat.factorial H.index := by rw [← Subgroup.index_eq_card]

/-- **Isaacs Cor 1.3**.  `G` が単純群で `∃ H ≤ G` with `[G:H] = n > 1` なら `|G| ∣ n!`.

証明: Cor 1.2 の `N := core_G(H)` は `G` で正規．`G` 単純なので `N = ⊥` か `N = ⊤`．
`n > 1` より `H ⊊ G`，よって `N ≤ H ⊊ G`，つまり `N ≠ ⊤`．
ゆえに `N = ⊥`，`[G:⊥] = |G|`，`|G| ∣ n!`. -/
theorem card_dvd_factorial_of_simple_subgroup_index [IsSimpleGroup G] [Finite G]
    (H : Subgroup G) (hn1 : 1 < H.index) :
    Nat.card G ∣ Nat.factorial H.index := by
  have hn : H.index ≠ 0 := by omega
  haveI : Finite (G ⧸ H) := Subgroup.index_ne_zero_iff_finite.mp hn
  obtain ⟨_, hNH, hdvd⟩ := normalCore_index_dvd_factorial H
  rcases Subgroup.Normal.eq_bot_or_eq_top (inferInstance : H.normalCore.Normal)
      with hN | hN
  · rw [hN, Subgroup.index_bot] at hdvd
    exact hdvd
  · -- N = ⊤ なら H = ⊤ つまり [G:H] = 1, hn1 と矛盾
    exfalso
    have hHtop : H = ⊤ := le_antisymm le_top (hN ▸ hNH)
    rw [hHtop, Subgroup.index_top] at hn1
    exact Nat.lt_irrefl 1 hn1

/-- **Isaacs Cor 1.5**.  有限群 `G` と `x ∈ G` について，`x` の共役類のサイズは
`[G : C_G(x)]` に等しい.

証明: `ConjAct G` の `G` への共役作用で
`x` の軌道 = 共役類 (`ConjAct.orbit_eq_carrier_conjClasses`)，
orbit-stabilizer 定理 (`MulAction.index_stabilizer`) より
orbit サイズ = `(stabilizer (ConjAct G) x).index`，
`Subgroup.centralizer_eq_comap_stabilizer` + `index_comap_of_surjective`
で centralizer の指数に書き換える. -/
theorem card_conjClass_eq_index_centralizer [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (Subgroup.centralizer {x}).index := by
  have horb : MulAction.orbit (ConjAct G) x = (ConjClasses.mk x).carrier :=
    ConjAct.orbit_eq_carrier_conjClasses x
  -- Nat.card ↑carrier = carrier.ncard (forward), then rewrite using orbit
  rw [Nat.card_coe_set_eq, ← horb,
      ← MulAction.index_stabilizer (G := ConjAct G) (X := G)]
  -- (centralizer {x}).index = (comap toConjAct stab).index = stab.index
  rw [Subgroup.centralizer_eq_comap_stabilizer]
  exact ((MulAction.stabilizer (ConjAct G) x).index_comap_of_surjective
           ConjAct.toConjAct.surjective).symm

open scoped Pointwise in
/-- **Isaacs Cor 1.6**.  有限群 `G` の部分群 `H` の `G` 内の共役の総数は
`[G : N_G(H)]` に等しい.

証明: `ConjAct G` の `Subgroup G` への点別共役作用 (`Pointwise` locale) で，
`H` の軌道サイズ = `[ConjAct G : stabilizer (ConjAct G) H]` (orbit-stabilizer)，
`ofConjAct` が等長写像なので `stabilizer` と `normalizer H` の指数が一致する
(`Subgroup.index_map_equiv` + `Subgroup.conjAct_pointwise_smul_iff`). -/
theorem card_subgroup_conjugates_eq_index_normalizer [Finite G] (H : Subgroup G) :
    (MulAction.orbit (ConjAct G) H).ncard = (Subgroup.normalizer (H : Set G)).index := by
  rw [← MulAction.index_stabilizer (G := ConjAct G) (X := Subgroup G)]
  -- (stab).index = (stab.map ofConjAct).index (isomorphism preserves index)
  rw [← (MulAction.stabilizer (ConjAct G) H).index_map_equiv ConjAct.ofConjAct]
  congr 1
  -- (stabilizer (ConjAct G) H).map ofConjAct = normalizer (H : Set G)
  ext h
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    -- hg : g • H = H, g : ConjAct G; rewrite as toConjAct (ofConjAct g) • H = H
    rw [← ConjAct.toConjAct_ofConjAct g] at hg
    exact Subgroup.conjAct_pointwise_smul_iff.mp hg
  · intro hh
    exact ⟨ConjAct.toConjAct h, Subgroup.conjAct_pointwise_smul_iff.mpr hh,
           ConjAct.ofConjAct_toConjAct h⟩

end -- 1A

section /- 1B: Sylow's existence theorem and Cauchy (pp. 10-17) -/

variable {G : Type*} [Group G]

/-- **Isaacs Thm 1.7** (Sylow E).  任意の群 `G` と素数 `p` について `G` は
Sylow `p`-部分群を持つ.

mathlib `Sylow.nonempty` の再述.  mathlib では `Sylow p G` 型自体が
"`G` の極大 `p`-部分群" を表し, `[Fact p.Prime]` のみで非空 (有限性不要; Zorn).
有限 `G` ではさらに `Sylow.card_eq_multiplicity` で `|S| = p^{v_p(|G|)}` が成り立つ. -/
theorem sylow_nonempty (p : ℕ) [Fact p.Prime] : Nonempty (Sylow p G) :=
  Sylow.nonempty

/-- **Isaacs Lemma 1.8** (Sylow E の補題).  素数 `p`, `a ≥ 0`, `m ≥ 1` で
`Nat.choose (p^a · m) (p^a) ≡ m (mod p)`.  Wielandt 流 Sylow E 証明で
`Ω = {S ⊆ G : |S| = p^a}` への右乗法作用の濃度を見るときに使う.

mathlib `Choose.choose_pow_mul_pow_mul_modEq_choose_nat` の `b := 1` 特殊化. -/
theorem choose_pow_mul_modEq_self {p : ℕ} [Fact p.Prime] (a m : ℕ) :
    (p ^ a * m).choose (p ^ a) ≡ m [MOD p] := by
  simpa using
    Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := a) (a := m) (b := 1)

/-- **Isaacs Cor 1.9** (Cauchy).  有限群 `G` で素数 `p ∣ |G|` ⇒ `G` は位数 `p`
の元を持つ.

mathlib `exists_prime_orderOf_dvd_card'` の再述. -/
theorem cauchy [Finite G] {p : ℕ} [Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    ∃ x : G, orderOf x = p :=
  exists_prime_orderOf_dvd_card' p hdvd

/-- **Isaacs Lemma 1.10**.  `K ≤ N ≤ G`, `N ◁ G` で `K` が `N` の特性部分群なら
`K ◁ G`.  ここでは `K : Subgroup N`, 結論は `K.map N.subtype` の `G` における
正規性, という mathlib 寄りの形.

mathlib `Subgroup.normal_of_characteristic_of_normal` がインスタンスとして
提供しているため typeclass で自動推論される; 以下は再述. -/
theorem normal_of_characteristic_in_normal
    {N : Subgroup G} [N.Normal] {K : Subgroup N} [K.Characteristic] :
    (K.map N.subtype).Normal :=
  inferInstance

-- TODO  Isaacs 流に `K N : Subgroup G, K ≤ N, (K.subgroupOf N).Characteristic`
--   ⇒ `K.Normal` の "G 内 K" 形ラッパーも欲しい (低優先度).

end -- 1B

section /- 1C: Sylow C / D, Frattini argument (pp. 13-17) -/

open Pointwise Subgroup MulAction

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- **Isaacs Thm 1.11**.  `G` の任意の `p`-部分群 `P` は, ある Sylow `p`-部分群 `S` と
ある `g ∈ G` が存在して `P ≤ g • S` (= `S` の共役) に含まれる.

証明の方針: `IsPGroup.exists_le_sylow` で `P ≤ Q` となる Sylow 部分群 `Q` を取り,
`orbit_eq_top` を使って `Q` と任意の Sylow を結ぶ共役元を取る.

mathlib `IsPGroup.exists_le_sylow` + `Sylow.orbit_eq_top` の組み合わせ. -/
theorem sylow_pgroup_le_conjugate [Finite (Sylow p G)]
    {P : Subgroup G} (hP : IsPGroup p P) (S : Sylow p G) :
    ∃ g : G, P ≤ ↑(g • S) := by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := (S.orbit_eq_top ▸ Set.mem_univ Q :
      Q ∈ MulAction.orbit G S)
  exact ⟨g, hQ.trans (by rfl)⟩

/-- **Isaacs Thm 1.12** (Sylow C).  有限群 `G` の任意の 2 つの Sylow `p`-部分群は
`G` の元による共役で移り合う.

mathlib `MulAction.exists_smul_eq` (from `Sylow.isPretransitive_of_finite`) の再述. -/
theorem sylow_conjugate [Finite (Sylow p G)] (P Q : Sylow p G) :
    ∃ g : G, g • P = Q :=
  exists_smul_eq G P Q

/-- **Isaacs Lemma 1.13** (Frattini argument).  `N ◁ G` 有限, `P ∈ Syl_p(N)` ならば
`G = N_G(P) · N`, すなわち `normalizer (↑P) ⊔ N = ⊤`.

mathlib `Sylow.normalizer_sup_eq_top'` の再述 (P を G の Sylow として N に含まれる形). -/
theorem frattini_argument [Finite (Sylow p G)]
    {N : Subgroup G} [N.Normal] (P : Sylow p G) (hPN : ↑P ≤ N) :
    normalizer (P : Subgroup G) ⊔ N = ⊤ :=
  P.normalizer_sup_eq_top' hPN

omit [Fact p.Prime] in
/-- **Isaacs Thm 1.14** (Sylow D).  `G` の任意の `p`-部分群は何らかの Sylow `p`-部分群に
含まれる.

mathlib `IsPGroup.exists_le_sylow` の直接再述. -/
theorem pgroup_le_sylow
    {P : Subgroup G} (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q :=
  hP.exists_le_sylow

/-- **Isaacs Cor 1.15**.  `S ∈ Syl_p(G)` について Sylow `p`-部分群の個数は
`n_p(G) = [G : N_G(S)]`.

mathlib `Sylow.card_eq_index_normalizer` の再述. -/
theorem card_sylow_eq_index_normalizer [Finite (Sylow p G)] (S : Sylow p G) :
    Nat.card (Sylow p G) = (normalizer ((S : Subgroup G) : Set G)).index :=
  S.card_eq_index_normalizer

-- TODO **Isaacs Thm 1.16** (n_p の精密な合同).  `n_p(G) > 1` のとき, distinct な
--   `S, T ∈ Syl_p(G)` で `|S ∩ T|` が最大となるものをとると
--     `n_p(G) ≡ 1 (mod |S : S ∩ T|)`.
--   (Cor 1.17 `n_p ≡ 1 (mod p)` の strengthen.)
--
--   ## 証明骨子 (Isaacs p.15, "Proof of Theorem 1.16"):
--   1. `S` を部分群とみなして `Sylow p G` 上に共役で作用させる
--      (`Subgroup.instMulAction` で自動).
--   2. `S` 軌道は `{S}` (固定点 1 個) + その他で分解. 残り軌道の合計が
--      `n_p - 1`. 残り軌道の各サイズが `|S : S ∩ T|` で割れることを示せばよい.
--   3. 任意の軌道 `O ∋ P (P ≠ S)` について `Stab_S(P) = S ⊓ N_G(P)`.
--      `Sylow.smul_eq_iff_mem_normalizer` から.
--   4. `IsPGroup.inf_normalizer_sylow` で `S ⊓ N_G(P) = S ⊓ P`.
--      よって `|O| = |S : S ⊓ P|`.
--   5. `|S ⊓ P| ≤ |S ⊓ T|` (|S ∩ T| 最大性). したがって
--      `|S : S ⊓ T| ≤ |S : S ⊓ P| = |O|`.
--   6. `|O|, |S : S ⊓ T|` 共に `p`-冪 (`IsPGroup.card_orbit` + S が p-群).
--      `p`-冪同士で大小関係から整除関係 `|S : S ⊓ T| ∣ |O|` が出る.
--   7. 全軌道の和が `n_p`, 固定点軌道 `{S}` の寄与が `1`, 残りはすべて
--      `|S : S ⊓ T|` の倍数. よって `n_p ≡ 1 (mod |S : S ⊓ T|)`.
--
--   ## 必要となる mathlib 補題 (偵察済 2026-05-21):
--   - `Sylow.smul_eq_iff_mem_normalizer` (Sylow.lean:258): `g • P = P ↔ g ∈ N_G(P)`.
--   - `IsPGroup.inf_normalizer_sylow` (Sylow.lean:277): p-群 Q, Sylow P で
--     `Q ⊓ N_G(P) = Q ⊓ P`.
--   - `IsPGroup.card_orbit` (PGroup.lean:147): p-群作用の軌道は p-冪サイズ.
--   - `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` (Quotient.lean:182):
--     orbit-stabilizer.
--   - `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'` (Quotient.lean:214):
--     class formula `β ≃ Σ ω : Ω, α ⧸ stabilizer α (φ ω)`.
--   - `Subgroup.instMulAction` (GroupAction/Defs.lean:246): H ≤ G → MulAction H α.
--
--   ## 詰まりどころ (blocker):
--   class formula で `Nat.card (Sylow p G) = Σ orbit_sizes` の和への変換は
--   できるが, 「固定点軌道 `{S}` を分離し残りを mod 計算」を Lean で書き下すと
--   軌道の代表元の扱い (`Quotient.out`) と `Finset.sum_eq_card_add_sum_of_eq_one`
--   的な分解補題の組み合わせが必要. 60-80 行が見込まれ, さらに
--   `(stabilizer S P : Subgroup S)` を `(S ⊓ P : Subgroup G)` と同型に持ち上げる
--   `subgroupOf` 周りの計算がトリッキー (Nat.card 等式チェーンが長い).
--
--   現状の判断: Phase 1 で Cor 1.17 が使えれば FT 局所解析の入り口は十分カバーされる
--   ので, Thm 1.16 は backlog として明確化 + 詳細プルーフスケッチ済の状態で保留.
--   再着手者は上の 7 ステップに沿って書き下せば原理的に閉じる. 参考実装は
--   mathlib 内 `Sylow.card_modEq_card_normalizer` 系 (Sylow.lean:540-610) の
--   類似パターン.

/-- **Isaacs Cor 1.17**.  `n_p(G) ≡ 1 (mod p)`.

mathlib `card_sylow_modEq_one` の再述. -/
theorem card_sylow_modEq_one_prime [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] :=
  card_sylow_modEq_one p G

omit [Fact p.Prime] in
/-- **Isaacs Lemma 1.18**.  `P ∈ Syl_p(G)`, `Q` が `N_G(P)` に含まれる `p`-部分群ならば
`Q ≤ P`.

証明: `IsPGroup.inf_normalizer_sylow` より `Q ⊓ N_G(P) = Q ⊓ P`, そして `Q ≤ N_G(P)` から
`Q = Q ⊓ N_G(P) = Q ⊓ P ≤ P`.

mathlib `IsPGroup.inf_normalizer_sylow` の系. -/
theorem pgroup_in_normalizer_le_sylow
    {Q : Subgroup G} (hQ : IsPGroup p Q) (P : Sylow p G)
    (hQN : Q ≤ normalizer (P : Subgroup G)) : Q ≤ P := by
  have h := hQ.inf_normalizer_sylow P
  -- h : Q ⊓ N_G(P) = Q ⊓ P
  rw [inf_of_le_left hQN] at h
  -- h : Q = Q ⊓ P
  exact inf_eq_left.mp h.symm

end -- 1C

section /- 1D: Nilpotent groups, Fitting subgroup F(G) (pp. 21-29) -/

open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Isaacs Thm 1.19–1.25: 冪零群と p-群の基本構造 -/

/-- **Isaacs Thm 1.19**.  `P` を有限 `p`-群, `N` をその非自明な正規部分群とすると,
`N ∩ Z(P)` は非自明.

証明骨子: `ConjAct P` の作用を `N` (正規部分群) に制限して考える
(`Subgroup.conjMulDistribMulAction`).  `IsPGroup p P` から `IsPGroup p (ConjAct P)`,
`IsPGroup.card_modEq_card_fixedPoints` で `|N| ≡ |fixedPoints| (mod p)`.
`N` 非自明 p-群より `p ∣ |N|`, ゆえ `p ∣ |fixedPoints|`. `1 ∈ fixedPoints` なので
`|fixedPoints| ≥ 1`, よって `≥ p ≥ 2`, 非自明. fixed point は `N ∩ Z(P)` の元. -/
theorem IsPGroup.normal_inf_center_nontrivial {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal] (hN : Nontrivial N) :
    Nontrivial ((N ⊓ Subgroup.center P : Subgroup P)) := by
  -- ConjAct P acts on N (since N is normal), IsPGroup p (ConjAct P).
  haveI hCA : IsPGroup p (ConjAct P) := hP.of_equiv ConjAct.toConjAct
  -- p divides |N| since N is a nontrivial p-group.
  have hpN : p ∣ Nat.card N := by
    obtain ⟨n, hn0, hn⟩ := (hP.to_subgroup N).nontrivial_iff_card.mp hN
    exact hn.symm ▸ dvd_pow_self _ hn0.ne'
  -- 1 is fixed under the ConjAct P action on N.
  have h1 : (1 : N) ∈ MulAction.fixedPoints (ConjAct P) N := by
    intro g
    apply Subtype.ext
    change (g : ConjAct P) • ((1 : N) : P) = ((1 : N) : P)
    rw [ConjAct.smul_def]
    simp
  -- p ∣ |N| and ∃ fixed point ⇒ ∃ another fixed point ≠ 1.
  obtain ⟨g, hgFix, hg1⟩ :=
    hCA.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := N) hpN h1
  -- (g : P) is central, and g ∈ N, hence ≠ 1 gives nontriviality of N ⊓ center P.
  have hg_center : (g : P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro h
    have heq : ConjAct.toConjAct h • g = g := hgFix _
    have hcoe : (((ConjAct.toConjAct h) • g : N) : P) = (g : P) := by rw [heq]
    rw [ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul_eq_mulAut_conj,
      MulAut.conj_apply] at hcoe
    -- hcoe : h * (g : P) * h⁻¹ = (g : P)
    rw [mul_inv_eq_iff_eq_mul] at hcoe
    exact hcoe
  refine ⟨⟨1, ⟨((g : N) : P), Subgroup.mem_inf.mpr ⟨g.2, hg_center⟩⟩, ?_⟩⟩
  intro heq
  apply hg1
  -- heq : (1 : (N ⊓ center P)) = ⟨(g : P), ...⟩ at the inf level
  -- goal: 1 = g at the N level
  apply Subtype.ext  -- to P level
  have := congrArg (fun x : (N ⊓ Subgroup.center P : Subgroup P) => (x : P)) heq
  simpa using this

/-- **Isaacs Lemma 1.20** (nilpotent 群の特性化, 部分結果).  有限群 `G` が冪零であることと
全 Sylow が正規であることは同値.

Isaacs Lemma 1.20 は冪零性のいくつかの特性化を主張するが (1)-(2) 部分は `IsNilpotent` の
定義そのもの, 残りの (3) 「全 Sylow 正規」は mathlib `isNilpotent_of_finite_tfae` で完備.
ここではすでに後段の Thm 1.26 で同じ TFAE をラップ済 (`isNilpotent_iff_forall_sylow_normal`).
独立の名前空間にエイリアスを置く. -/
theorem isNilpotent_iff_normalizerCondition [Finite G] :
    Group.IsNilpotent G ↔ NormalizerCondition G :=
  isNilpotent_of_finite_tfae.out 0 1

/-- **Isaacs Thm 1.21**.  冪零群は中心列 `1 = Z_0 ≤ Z_1 ≤ ... ≤ Z_n = G` を持ち,
各 `Z_{i+1}/Z_i ≤ Z(G/Z_i)`. 逆も成り立つ.

mathlib `Group.upperCentralSeries_nilpotencyClass : upperCentralSeries G (nilpotencyClass G) = ⊤`
の再述. `upperCentralSeries` が中心列で, `nilpotencyClass` ステップで `⊤` に到達する. -/
theorem upperCentralSeries_eq_top_of_isNilpotent [Group.IsNilpotent G] :
    upperCentralSeries G (Group.nilpotencyClass G) = ⊤ :=
  upperCentralSeries_nilpotencyClass

/-- **Isaacs Thm 1.22** (Normalizer Condition).  有限冪零群 `G` で真部分群 `H < G` ならば
`H < N_G(H)`.

mathlib `normalizerCondition_of_isNilpotent` の再述. -/
theorem lt_normalizer_of_isNilpotent_of_lt_top [Group.IsNilpotent G]
    {H : Subgroup G} (hH : H < ⊤) :
    H < Subgroup.normalizer H :=
  normalizerCondition_of_isNilpotent H hH

-- TODO Isaacs Lemma 1.23. P p-群, N ◁ P, M ◁ P with N < M ⇒ ∃ L ◁ P, N ≤ L ≤ M, |L:N|=p.
--   Strategy: P/N の正規部分群 M/N に Thm 1.19 (上記の `IsPGroup.normal_inf_center_nontrivial`)
--   を適用. (M/N) ∩ Z(P/N) ≠ {1} から位数 p の中心元を取り pull back. 中継部分が30行超.

/-- **Isaacs Cor 1.24** (弱形).  位数 `p^n` の有限 `p`-群 `G` は, 各 `m ≤ n` に対して
位数 `p^m` の部分群を持つ.

`Sylow.exists_subgroup_card_pow_prime_of_le_card` の再述. (mathlib 直.)  Isaacs 厳密形は
さらに「これらの部分群が正規」も主張するが, Lemma 1.23 強形が必要なので一旦弱形. -/
theorem IsPGroup.exists_subgroup_card_pow_le {G : Type*} [Group G]
    {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G) {m : ℕ}
    (hm : p ^ m ≤ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ m :=
  Sylow.exists_subgroup_card_pow_prime_of_le_card hp hG hm

/-- **Isaacs Cor 1.25**.  有限群 `G` で素数 `p`, `p^m ∣ |G|` ならば, 位数 `p^m` の
部分群が存在する (Sylow E の一般化).

mathlib `Sylow.exists_subgroup_card_pow_prime` の再述. -/
theorem Sylow.exists_subgroup_card_pow_dvd [Finite G] (p : ℕ) {m : ℕ} [Fact p.Prime]
    (hdvd : p ^ m ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ m :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

/-! ### O_p(G) と Fitting 部分群 F(G)

Isaacs §1D 後半の主要新規実装。詳細設計は
[notes/isaacs/ch01_sylow_d_fitting.md](../../notes/isaacs/ch01_sylow_d_fitting.md)。

`opCore p G` (= `O_p(G)`) は全 Sylow `p`-部分群の共通部分として定義し,
最大の正規 `p`-部分群であることを示す (Isaacs Problem 1B.2). この上に
`fitting G` (= `F(G)`) を `⨆_{p prime} opCore p G` として乗せる. -/

/-- `O_p(G)`: `G` の全 Sylow `p`-部分群の共通部分.  Isaacs Problem 1B.2 で示される
ように, これは `G` の最大の正規 `p`-部分群と一致する.

mathlib 未収載のため新規定義 (将来 mathlib に `Subgroup.opCore` として PR したい形). -/
def opCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ P : Sylow p G, (P : Subgroup G)

@[simp]
theorem mem_opCore {p : ℕ} {x : G} :
    x ∈ opCore p G ↔ ∀ P : Sylow p G, x ∈ (P : Subgroup G) := by
  simp [opCore, Subgroup.mem_iInf]

theorem opCore_le {p : ℕ} (P : Sylow p G) : opCore p G ≤ (P : Subgroup G) :=
  iInf_le _ P

/-- `O_p(G)` は `p`-部分群 (Sylow に含まれるから).

`[Fact p.Prime]` 必須 (`Sylow.nonempty` から少なくとも 1 つの Sylow を取るため). -/
theorem opCore_isPGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] :
    IsPGroup p (opCore p G) := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  exact P.2.of_injective (Subgroup.inclusion (opCore_le P))
    (Subgroup.inclusion_injective _)

/-- `O_p(G)` は `G` で正規.
証明: `Subgroup.Normal.of_conjugate_fixed` を使い,
`∀ g : G, MulAut.conj g • opCore p G = opCore p G` を示す.
各 `g` について `MulAut.conj g` は Sylow 部分群を Sylow 部分群に写す (`g • P ∈ Sylow p G`)
ので, 全 Sylow の共通部分 `opCore p G` も共役不変. -/
instance opCore.normal (p : ℕ) (G : Type*) [Group G] : (opCore p G).Normal := by
  apply Subgroup.Normal.of_conjugate_fixed
  intro g
  ext x
  simp only [mem_opCore, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  -- After simp: ∀ P, (MulAut.conj g)⁻¹ x ∈ ↑P  ↔  ∀ P, x ∈ ↑P
  -- Here ↑P is the Subgroup G coercion via CoeOut (Sylow p G) (Subgroup G)
  constructor
  · intro h P
    -- Apply h to (g⁻¹ • P : Sylow p G); then unfold the smul at Subgroup level
    have hQ : (MulAut.conj g)⁻¹ x ∈ (↑(g⁻¹ • P) : Subgroup G) := h (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, ← map_inv,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    simp only [map_inv, inv_inv, MulAut.smul_def] at hQ
    rwa [MulAut.apply_inv_self] at hQ
  · intro h P
    -- Apply h to (g • P : Sylow p G); then unfold the smul at Subgroup level
    have hQ : x ∈ (↑(g • P) : Subgroup G) := h (g • P)
    rw [Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    exact hQ

/-- **Isaacs Problem 1B.2**. 任意の正規 `p`-部分群 `N` は `opCore p G` に含まれる.
これにより `opCore p G` は `G` の最大正規 `p`-部分群である.

証明: Sylow D (`IsPGroup.exists_le_sylow`) で `N ≤ Q` となる Sylow `Q` を取り,
任意の Sylow `P` に対して Sylow C (`[Finite (Sylow p G)]`) で `∃ g, P = g • Q` を取る.
`N` の正規性から `N = MulAut.conj g • N ≤ MulAut.conj g • Q = ↑(g • Q) = ↑P`. -/
theorem normal_pgroup_le_opCore {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite (Sylow p G)]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p N) :
    N ≤ opCore p G := by
  rw [opCore, le_iInf_iff]
  intro P
  obtain ⟨Q, hNQ⟩ := hN.exists_le_sylow
  obtain ⟨g, hgQ⟩ := MulAction.exists_smul_eq G Q P
  calc (N : Subgroup G)
      = MulAut.conj g • N := (Subgroup.Normal.conj_smul_eq_self g N).symm
    _ ≤ MulAut.conj g • (Q : Subgroup G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNQ
    _ = ↑(g • Q) := Sylow.coe_subgroup_smul.symm
    _ = ↑P := by rw [hgQ]

/-! ### Isaacs Thm 1.26 (冪零 ⇔ Sylow 全正規) -/

/-- **Isaacs Thm 1.26 (1) ⇔ (4)**.  有限群 `G` について「`G` が冪零」と
「`G` の任意の Sylow 部分群が正規」は同値.

mathlib `isNilpotent_of_finite_tfae` の (0) ⇔ (3) の抽出ラッパー.  Isaacs 流 5 条件
((1)冪零, (2)`H<G ⇒ N_G(H)>H`, (3) 全極大正規, (4) 全 Sylow 正規, (5) Sylow 内部直積)
は TFAE 全体 (`isNilpotent_of_finite_tfae`) で確保される. -/
theorem isNilpotent_iff_forall_sylow_normal [Finite G] :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal :=
  isNilpotent_of_finite_tfae.out 0 3

/-- **Isaacs Thm 1.26 (4) ⇒ (1)** (片向き取り出し).
全 Sylow が正規ならば G は冪零. -/
theorem isNilpotent_of_forall_sylow_normal [Finite G]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal) :
    Group.IsNilpotent G :=
  isNilpotent_iff_forall_sylow_normal.mpr h

/-- **Isaacs Thm 1.26 (1) ⇒ (4)** (片向き取り出し).
冪零ならば任意の Sylow は正規. -/
theorem Sylow.normal_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  isNilpotent_iff_forall_sylow_normal.mp ‹_› p P

/-- **Isaacs Lemma 1.27**.  `H i : ι → Subgroup G` が有限族で各 `H i` が正規部分群,
かつ位数 (`Nat.card`) が対ごとに互いに素ならば, 族 `H` は `iSupIndep` (内部直積構造).

証明: 互いに素 ⇒ `Subgroup.inf_eq_bot_of_coprime` で `Disjoint`,
正規 + Disjoint ⇒ `commute_of_normal_of_disjoint` で `Pairwise Commute`,
最後に mathlib `Subgroup.independent_of_coprime_order` を適用. -/
theorem iSupIndep_of_coprime_card_of_normal {ι : Type*} [Finite ι]
    (H : ι → Subgroup G) [∀ i, (H i).Normal] [∀ i, Finite (H i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    iSupIndep H := by
  -- Step 1: Disjoint from coprime cards.
  have hdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j) := fun i j hij =>
    disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime (hcoprime hij))
  -- Step 2: Pairwise commute from disjoint + normal.
  have hcomm : Pairwise fun i j : ι =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact Subgroup.commute_of_normal_of_disjoint (H i) (H j)
      inferInstance inferInstance (hdisj i j hij) x y hx hy
  -- Step 3: Apply mathlib's independent_of_coprime_order.
  classical
  haveI : ∀ i, Fintype (H i) := fun i => Fintype.ofFinite _
  have hcoprime' : Pairwise fun i j =>
      Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j)) := by
    intro i j hij
    have := hcoprime hij
    simpa [Nat.card_eq_fintype_card] using this
  exact Subgroup.independent_of_coprime_order hcomm hcoprime'

/-! ### Fitting 部分群 F(G) -/

/-- **Fitting subgroup** `F(G)`: 全ての素数 `p` についての `opCore p G` (= `O_p(G)`)
の supremum.  これは `G` の最大の正規冪零部分群となる (Isaacs Cor 1.28).

mathlib 未収載のため新規定義. `Subgroup.fitting` として将来 mathlib に PR したい形.

Isaacs 流の定義「`|G|` の各素因子 `p` について `O_p(G)` の積」と等価. 非素数 `p` や
`|G|` に分割しない素数 `p` に対しては `opCore p G ⊆` 既存の sup なので, 範囲を
広げても結果は変わらない (実際 `opCore p G = ⊥` for primes p ∤ |G|, 有限 G で). -/
def fitting (G : Type*) [Group G] : Subgroup G :=
  ⨆ p : Nat.Primes, opCore (p : ℕ) G

theorem opCore_le_fitting (p : Nat.Primes) (G : Type*) [Group G] :
    opCore (p : ℕ) G ≤ fitting G :=
  le_iSup (fun q : Nat.Primes => opCore (q : ℕ) G) p

/-- `F(G)` は `G` の正規部分群. 各 `opCore p G` の正規性を `iSup_induction` で全体に持ち上げる. -/
instance fitting.normal (G : Type*) [Group G] : (fitting G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ fitting G) hn
    ?mem ?one ?mul
  case mem =>
    intro p x hx
    -- x ∈ opCore p G が正規だから g * x * g⁻¹ ∈ opCore p G ≤ fitting
    exact (opCore_le_fitting p G) ((opCore.normal (p : ℕ) G).conj_mem x hx g)
  case one =>
    simp
  case mul =>
    intro x y hx hy
    -- g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (fitting G).mul_mem hx hy

/-- 補助補題: 有限冪零群 `N` では, 各素因数 `p` に対する代表 Sylow 部分群
`default : Sylow p N` の supremum は `⊤_N` に等しい.

証明骨子: Thm 1.26 で全 Sylow が正規, よって `unique_of_normal` で各素因数につき
Sylow が 1 つ. `noncommPiCoprod` 経由で `(∀ p ∈ pf(|N|), Sylow p N) →* N` を作り,
互いに素な p-群より単射 (`independent_of_coprime_order`), 濃度比較で全射 ⇒ range = ⊤.
range = `⨆ p, ↑(default Sylow)` (by `noncommPiCoprod_range`). -/
private theorem iSup_default_sylow_eq_top_of_nilpotent
    (N : Type*) [Group N] [Finite N] [Group.IsNilpotent N] :
    ⨆ p : (Nat.card N).primeFactors,
        ((default : Sylow (p : ℕ) N) : Subgroup N) = ⊤ := by
  classical
  have hnormal : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p N), P.Normal := fun P =>
    Sylow.normal_of_isNilpotent P
  have _ := Fintype.ofFinite N
  set ps := (Nat.card N).primeFactors with hps
  let P : ∀ p, Sylow p N := default
  have hPfin : ∀ p, Fintype (P p) := fun p ↦ Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : N, x ∈ (P p₁ : Subgroup N) → y ∈ (P p₂ : Subgroup N) → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hnormal (P p₁)) (hnormal (P p₂))
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  -- noncommPiCoprod : (∀ p : ps, P p) →* N
  set f := Subgroup.noncommPiCoprod (G := N) (H := fun p : ps => (P p : Subgroup N)) hcomm
    with hf
  -- f is injective by independent_of_coprime_order
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  -- |∀ p : ps, P p| = |N|
  have hcard : Fintype.card (∀ p : ps, P p) = Fintype.card N := by
    simp only [← Nat.card_eq_fintype_card]
    calc Nat.card (∀ p : ps, P p)
        = ∏ p : ps, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : ps, p.1 ^ (Nat.card N).factorization p.1 := by
          refine Finset.prod_congr rfl ?_
          rintro ⟨p, hp⟩ _
          exact @Sylow.card_eq_multiplicity _ _ _ p
            ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p ∈ ps, p ^ (Nat.card N).factorization p :=
          Finset.prod_finset_coe (fun p => p ^ (Nat.card N).factorization p) _
      _ = (Nat.card N).factorization.prod (· ^ ·) := rfl
      _ = Nat.card N := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'
  -- bijective
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  -- range = ⊤
  have hrange : f.range = (⊤ : Subgroup N) :=
    MonoidHom.range_eq_top.mpr hbij.surjective
  -- but noncommPiCoprod_range says range = ⨆ i, H i
  have hrange' : f.range = ⨆ p : ps, (P p : Subgroup N) :=
    Subgroup.noncommPiCoprod_range
  rw [hrange'] at hrange
  exact hrange

/-- **Isaacs Cor 1.28(b)** (Fitting subgroup の最大性).
任意の正規冪零部分群 `N` は `fitting G` に含まれる.

証明骨子: `N` が冪零 ⇒ `N` の各 Sylow `Q` は `N` で正規 (Thm 1.26) ⇒ `Q` は `N` で
特性的 (`Sylow.characteristic_of_normal`) ⇒ `N ◁ G` で `Q.map N.subtype ◁ G` (Lemma 1.10).
これが `p`-部分群なので Problem 1B.2 で `Q.map N.subtype ≤ opCore p G ≤ fitting G`.
`N` 全体が unique Sylow 達の sup に等しい (`iSup_default_sylow_eq_top_of_nilpotent`) ことから
`N ≤ fitting G`. -/
theorem nilpotent_normal_le_fitting [Finite G] {N : Subgroup G} [N.Normal]
    [Group.IsNilpotent N] : N ≤ fitting G := by
  -- N 全体 (= ⊤ within Subgroup N, mapped through N.subtype = N) ≤ fitting G
  have hsup : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hsup, ← iSup_default_sylow_eq_top_of_nilpotent N, Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  haveI hp' : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- default : Sylow p N is normal in N
  have hPN : (default : Sylow p N).Normal := Sylow.normal_of_isNilpotent _
  -- default Sylow is characteristic in N (unique Sylow ⇒ characteristic)
  haveI : ((default : Sylow p N) : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal _ hPN
  -- so its image in G is normal (Lemma 1.10)
  haveI : (((default : Sylow p N) : Subgroup N).map N.subtype).Normal :=
    normal_of_characteristic_in_normal
  -- it's a p-subgroup of G
  have hpGroup : IsPGroup p (((default : Sylow p N) : Subgroup N).map N.subtype) :=
    (default : Sylow p N).2.map N.subtype
  -- Problem 1B.2 + opCore ≤ fitting
  calc ((default : Sylow p N) : Subgroup N).map N.subtype
      ≤ opCore p G := normal_pgroup_le_opCore hpGroup
    _ ≤ fitting G := opCore_le_fitting ⟨p, hp'.out⟩ G

/-- 有限 `G` で `p ∤ |G|` (より一般に `p` が `|G|` の素因子でない) なら, 任意の
Sylow `p`-部分群は自明 `⊥`, 従って `opCore p G = ⊥`.

`Sylow.card_eq_multiplicity` で各 Sylow の濃度は `p ^ v_p(|G|)`. `p ∉ pf(|G|)` なら
`v_p(|G|) = 0` で濃度 1, ゆえ `⊥`. -/
theorem opCore_eq_bot_of_not_mem_primeFactors [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ∉ (Nat.card G).primeFactors) :
    opCore p G = ⊥ := by
  -- Pick any Sylow P; it's ⊥ since its card is p^0 = 1.
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hcard : Nat.card (P : Subgroup G) = 1 := by
    rw [Sylow.card_eq_multiplicity P]
    have hfact : (Nat.card G).factorization p = 0 := by
      by_cases hdvd : p ∣ Nat.card G
      · -- p divides but is not in primeFactors → contradiction since Nat.card G ≠ 0
        exfalso
        exact hp (Nat.mem_primeFactors.mpr
          ⟨(Fact.out : p.Prime), hdvd, Nat.card_pos.ne'⟩)
      · exact Nat.factorization_eq_zero_of_not_dvd hdvd
    rw [hfact, pow_zero]
  have hPbot : (P : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  exact le_bot_iff.mp (le_of_le_of_eq (opCore_le P) hPbot)

/-- 有限 `G` について `fitting G` は `|G|` の素因子だけに渡る `opCore` の sup と等しい.
非素因子 `p` に対しては `opCore p G = ⊥` で寄与しないため. -/
theorem fitting_eq_iSup_primeFactors [Finite G] :
    fitting G = ⨆ p : (Nat.card G).primeFactors, opCore (p : ℕ) G := by
  apply le_antisymm
  · -- fitting = ⨆ p : Primes ≤ ⨆ p : pf
    refine iSup_le (fun p => ?_)
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    by_cases hmem : (p : ℕ) ∈ (Nat.card G).primeFactors
    · -- p is in primeFactors, contribute via the indexed sup
      exact le_iSup (fun q : (Nat.card G).primeFactors => opCore (q : ℕ) G) ⟨p, hmem⟩
    · -- p not in primeFactors: opCore p G = ⊥
      rw [opCore_eq_bot_of_not_mem_primeFactors hmem]
      exact bot_le
  · -- ⨆ p : pf ≤ ⨆ p : Primes (= fitting)
    refine iSup_le (fun p => ?_)
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    exact opCore_le_fitting ⟨(p : ℕ), hp⟩ G

/-- **Isaacs Cor 1.28(a)** (Fitting subgroup の冪零性).
有限群 `G` について `fitting G` は冪零.

証明骨子: `(Nat.card G).primeFactors` 上の積 `∀ p, opCore p G` から `G` への
`noncommPiCoprod` を考える. (i) 異なる素数 `p ≠ q` で `opCore p G, opCore q G` は
互いに素な p-群 (`IsPGroup.disjoint_of_ne`) ゆえ可換 (`commute_of_normal_of_disjoint`,
両者は正規), (ii) `independent_of_coprime_order` で `iSupIndep`, よって
`noncommPiCoprod` は単射 (`injective_noncommPiCoprod_of_iSupIndep`).
range は `⨆ p, opCore p G = fitting G` (`fitting_eq_iSup_primeFactors`).
従って `(∀ p, opCore p G) ≃* fitting G` (`MulEquiv.ofInjective` + `subgroupCongr`).
各 `opCore p G` は有限 p-群ゆえ冪零 (`IsPGroup.isNilpotent`), 有限積も冪零
(`isNilpotent_pi`), `MulEquiv` で `fitting G` も冪零.

`instance` 指定で `[Group.IsNilpotent (fitting G)]` が下流で自動推論される. -/
instance fitting.isNilpotent [Finite G] : Group.IsNilpotent (fitting G) := by
  classical
  have _ := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors with hps
  -- For each p ∈ pf, opCore p G is a p-group and normal in G
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : G, x ∈ opCore (p₁ : ℕ) G → y ∈ opCore (p₂ : ℕ) G → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    haveI hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (opCore.normal p₁ G)
      (opCore.normal p₂ G)
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  set f := Subgroup.noncommPiCoprod (G := G)
    (H := fun p : ps => opCore (p : ℕ) G) hcomm with hf
  -- f is injective by iSupIndep (coprime orders)
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    haveI hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  -- range f = ⨆ p, opCore p G = fitting G
  have hrange : f.range = fitting G := by
    rw [hf, Subgroup.noncommPiCoprod_range, ← fitting_eq_iSup_primeFactors]
  -- Build MulEquiv (∀ p, opCore p G) ≃* fitting G
  let e : (∀ p : ps, opCore (p : ℕ) G) ≃* fitting G :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  -- Each opCore p G (as a group) is finite + p-group ⇒ nilpotent
  have hnilp : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := by
    rintro ⟨p, hp⟩
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact (opCore_isPGroup p G).isNilpotent
  -- Finite product of nilpotent is nilpotent
  haveI : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := hnilp
  haveI : Group.IsNilpotent (∀ p : ps, opCore (p : ℕ) G) := isNilpotent_pi
  -- Transport across the MulEquiv
  exact nilpotent_of_mulEquiv e

/-- **Isaacs Cor 1.29** (冪零正規部分群の積も冪零).
`K, L` が `G` の正規冪零部分群ならば `K ⊔ L` (= `KL`) も冪零.

証明: Cor 1.28(b) で `K, L ≤ fitting G` ⇒ `K ⊔ L ≤ fitting G`.
`(K ⊔ L).subgroupOf (fitting G)` は冪零 (Cor 1.28(a) + `Subgroup.isNilpotent` instance),
`subgroupOfEquivOfLe` の同型で `K ⊔ L` も冪零. -/
instance sup_isNilpotent_of_normal_nilpotent [Finite G]
    (K L : Subgroup G) [K.Normal] [L.Normal]
    [Group.IsNilpotent K] [Group.IsNilpotent L] :
    Group.IsNilpotent (↥(K ⊔ L)) := by
  have hKLfit : K ⊔ L ≤ fitting G :=
    sup_le nilpotent_normal_le_fitting nilpotent_normal_le_fitting
  exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKLfit)

end -- 1D

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. 31-34) -/

variable {G : Type*} [Group G]

/-- **Isaacs Thm 1.30** (前半).  `|G| = p · q` で `q < p` がともに素数ならば,
`G` の Sylow `p`-部分群は正規 (一意).

証明: Sylow C / III により `n_p := |Syl_p(G)| ∣ q` かつ `n_p ≡ 1 (mod p)`.
`q` は素数なので `n_p ∈ {1, q}`. `n_p = q` ならば `q ≡ 1 (mod p)`,
すなわち `p ∣ q − 1`. しかし `q < p` より `q − 1 < p`, 唯一 `q − 1 = 0`
すなわち `q = 1` だが `q` は素数で矛盾. ゆえに `n_p = 1`, Sylow `p` 一意. -/
theorem sylow_normal_of_card_eq_mul_prime_lt
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q < p) (hcard : Nat.card G = p * q) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow p G) := by
    -- まず Finite (Sylow p G) を確保
    haveI : Finite (Sylow p G) := inferInstance
    -- P.index = q を取り出す
    have hPcard : Nat.card P = p := by
      have hmul := P.card_eq_multiplicity (G := G)
      rw [hcard, Nat.factorization_mul (Fact.out (p := p.Prime)).ne_zero
          (Fact.out (p := q.Prime)).ne_zero] at hmul
      simp only [Finsupp.coe_add, Pi.add_apply,
                 Nat.Prime.factorization_self (Fact.out (p := p.Prime)),
                 (Fact.out (p := q.Prime)).factorization,
                 Finsupp.single_apply, if_neg hqp.ne] at hmul
      simpa using hmul
    have hPindex : (P : Subgroup G).index = q := by
      have h1 : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
        Subgroup.card_mul_index _
      rw [hcard, hPcard] at h1
      exact Nat.eq_of_mul_eq_mul_left (Fact.out (p := p.Prime)).pos h1
    have hdvd : Nat.card (Sylow p G) ∣ q := hPindex ▸ P.card_dvd_index
    have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
    rcases (Nat.dvd_prime (Fact.out (p := q.Prime))).mp hdvd with hn1 | hnq
    · -- n = 1 ⇒ Subsingleton (Sylow p G は非空なので)
      exact (Nat.card_eq_one_iff_unique.mp hn1).1
    · -- n = q ⇒ q ≡ 1 [MOD p] ⇒ 矛盾
      exfalso
      rw [hnq] at hmod
      have hge : 1 ≤ q := (Fact.out (p := q.Prime)).pos
      have hdvd' : p ∣ q - 1 := (Nat.modEq_iff_dvd' hge).mp hmod.symm
      have hlt : q - 1 < p := by omega
      have hq1 : q - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' hlt
      have hq_eq : q = 1 := by omega
      exact (Fact.out (p := q.Prime)).one_lt.ne' hq_eq
  exact Sylow.normal_of_subsingleton P

-- TODO Thm 1.30 (後半): q ∤ p−1 ならば `G` は巡回群.
--   方針: `Aut(Sylow_p) ≅ (ℤ/p)ˣ = ℤ/(p-1)` への Sylow `q` 共役作用が自明,
--   よって Sylow `p`, `q` 互いに centralize で `G ≃ ℤ/p × ℤ/q ≅ ℤ/pq`.

/-- **Isaacs Thm 1.31** (`p > q` のとき).  `|G| = p² · q` で `q < p` がともに素数なら,
Sylow `p`-部分群は正規.

証明: Sylow C / III で `n_p ∣ q` かつ `n_p ≡ 1 (mod p)`. `q` 素数なので `n_p ∈ {1, q}`.
`n_p = q` ならば `q ≡ 1 (mod p)`, つまり `p ∣ q-1`. `q < p` より `q-1 < p`, 唯一
`q-1 = 0` で `q = 1` (素数で矛盾). ゆえ `n_p = 1`. 一般版 (`p < q`) は別途. -/
theorem sylow_normal_of_card_eq_sq_mul_prime_lt
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q < p) (hcard : Nat.card G = p ^ 2 * q) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow p G) := by
    haveI : Finite (Sylow p G) := inferInstance
    -- |P| = p²
    have hPcard : Nat.card P = p ^ 2 := by
      have hmul := P.card_eq_multiplicity (G := G)
      rw [hcard, Nat.factorization_mul (pow_ne_zero 2 (Fact.out (p := p.Prime)).ne_zero)
          (Fact.out (p := q.Prime)).ne_zero,
          Nat.Prime.factorization_pow (Fact.out (p := p.Prime))] at hmul
      simp only [Finsupp.coe_add, Pi.add_apply,
                 (Fact.out (p := q.Prime)).factorization, Finsupp.single_apply,
                 if_neg hqp.ne] at hmul
      simpa using hmul
    -- P.index = q
    have hPindex : (P : Subgroup G).index = q := by
      have h1 : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
        Subgroup.card_mul_index _
      rw [hcard, hPcard] at h1
      have hpos : 0 < p ^ 2 := pow_pos (Fact.out (p := p.Prime)).pos 2
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    have hdvd : Nat.card (Sylow p G) ∣ q := hPindex ▸ P.card_dvd_index
    have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
    rcases (Nat.dvd_prime (Fact.out (p := q.Prime))).mp hdvd with hn1 | hnq
    · exact (Nat.card_eq_one_iff_unique.mp hn1).1
    · exfalso
      rw [hnq] at hmod
      have hge : 1 ≤ q := (Fact.out (p := q.Prime)).pos
      have hdvd' : p ∣ q - 1 := (Nat.modEq_iff_dvd' hge).mp hmod.symm
      have hlt : q - 1 < p := by omega
      have hq1 : q - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' hlt
      exact (Fact.out (p := q.Prime)).one_lt.ne' (by omega : q = 1)
  exact Sylow.normal_of_subsingleton P

-- TODO Thm 1.31 (一般): `p < q` の場合は別ステップ.
--   `n_q ∣ p²`, `n_q ≡ 1 (mod q)` ⇒ `n_q ∈ {1, p, p²}`.
--   `n_q = p`: `q ∣ p-1` ⇒ `q ≤ p-1 < p < q`, 矛盾.
--   `n_q = p²`: `q ∣ p²-1 = (p-1)(p+1)`. `q ∤ p-1`, ゆえ `q ∣ p+1`, `q ≤ p+1`.
--     `p < q ≤ p+1` ⇒ `q = p+1`. 連続整数で素数のペアは `(p,q)=(2,3)` のみ → `|G|=12`.
--     `|G|=12` で `n_3=4` の場合は別途 Sylow 2 正規 (n_2=1) を示す必要.

-- TODO Thm 1.32  : |G|=p³q ⇒ 同上 (例外 |G|=24).
--   Thm 1.31 同様の Sylow 数の場合分け; 例外 `|G|=24` は Thm 1.33 に渡す.

-- TODO Thm 1.33  : |G|=24 ∧ n_2,n_3>1 ⇒ G ≅ S_4.
--   方針: G が n_3 = 4 個の Sylow 3 に共役で作用 ⇒ G →* S_4.
--   核 = ⋂ N_G(P_3) over P_3 ∈ Syl_3. 核 = ⊥ を示す必要 (難所).
--   |G|=|S_4|=24 ⇒ 全射, 同型.

-- TODO Thm 1.36 : `|G| = p^a q` (p, q 異素数, a ≥ 1) ⇒ G 単純でない.
--   Isaacs p.34 完全証明:
--   WLOG `n_p > 1` (これでないと Sylow p 正規で済む). `n_p = q`.
--   distinct `S, T ∈ Syl_p` で `D := S ∩ T` 最大を取る.
--   * D = 1 の場合: 全 Sylow p 対が trivial 交差で非単位元 p-元素計 `q(p^a-1)` 個.
--     残り `p^a q - q(p^a-1) = q` 元のうち単位元以外は q-元素. これらは Sylow q を成し,
--     一意 (cardinality 一致) ⇒ Sylow q 正規 ⇒ G 単純でない.
--   * D > 1 の場合: `N := N_G(D)`. p-群中で normalizer grow ⇒ N ∩ S > D, N ∩ T > D.
--     N が p-群でないことを示し, q ∣ |N|, Q ∈ Syl_q(N), |Q|=q, SQ = G.
--     D は全 Sylow p に含まれる ⇒ 1 < D ⊆ O_p(G), proper normal 部分群.
--   60-100 行 + 元素数の inclusion-exclusion 計算が必要で次セッション持ち越し.

/-- **Isaacs Lemma 1.34**.  `G` が有限集合 `Ω` に作用し, ある元 `x ∈ G` が
`Ω` 上で奇置換 (`Equiv.Perm.sign = -1`) を引き起こすなら, `G` は指数 2 の
正規部分群を持つ.

形式化方針: 符号写像 `Equiv.Perm.sign : Perm Ω →* ℤˣ` と作用準同型
`MulAction.toPermHom G Ω : G →* Perm Ω` の合成の核を取る.  核は常に正規,
range は `1` (= 単位) と `-1` (= `x` の像) を含むので `ℤˣ = ⊤` 全体,
よって `MonoidHom.index_ker` から index = `|ℤˣ| = 2`. -/
theorem normalSubgroup_index_two_of_actsOddly
    {Ω : Type*} [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    {x : G} (hx : Equiv.Perm.sign (MulAction.toPermHom G Ω x) = -1) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  set signHom : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G Ω) with hdef
  refine ⟨signHom.ker, inferInstance, ?_⟩
  have hxsign : signHom x = -1 := hx
  have hrange : signHom.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rcases Int.units_eq_one_or y with rfl | rfl
    · exact ⟨1, map_one signHom⟩
    · exact ⟨x, hxsign⟩
  rw [Subgroup.index_ker, hrange]
  simp [Nat.card_eq_fintype_card]

/-- **Isaacs Thm 1.35**.  有限群 `G` で `|G| = 2n`, `n` が奇数なら `G` は指数 2 の
正規部分群を持つ.

証明 (Isaacs 1.35): Cauchy の定理で `t ∈ G`, `orderOf t = 2` を取り,
正則作用 (左乗法) で `σ_t : g ↦ t * g` を考える.  `t ≠ 1` だから `σ_t` は固定点無し,
`t² = 1` だから involution.  mathlib `Equiv.Perm.sign_of_pow_two_eq_one` より
`sign σ_t = (-1)^(|G|/2) = (-1)^n = -1` (n 奇).  Lemma 1.34 で完了.

Feit-Thompson 「奇数位数群は可解」の "p = 2 の最易特殊 case" にあたる. -/
theorem normalSubgroup_index_two_of_card_two_mul_odd
    [Fintype G] {n : ℕ}
    (hn : Odd n) (hcard : Fintype.card G = 2 * n) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card G := by
    rw [Nat.card_eq_fintype_card, hcard]; exact ⟨n, rfl⟩
  obtain ⟨t, ht⟩ := cauchy (G := G) hdvd
  refine normalSubgroup_index_two_of_actsOddly (Ω := G) (x := t) ?_
  -- σ_t は involution: t² = 1
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hσ2 : (MulAction.toPermHom G G t) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  -- σ_t は固定点無し: t * g = g ⇒ t = 1, しかし orderOf t = 2 で矛盾
  have ht_ne_one : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact (by norm_num : (1 : ℕ) ≠ 2) ht
  have hfix : Fintype.card (Function.fixedPoints (MulAction.toPermHom G G t)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨g, hg⟩ => ?_⟩
    simp only [Function.mem_fixedPoints_iff, MulAction.toPermHom_apply,
               MulAction.toPerm_apply, smul_eq_mul] at hg
    -- hg : t * g = g  ⇒  t = 1
    exact ht_ne_one (mul_right_cancel (hg.trans (one_mul g).symm))
  rw [Equiv.Perm.sign_of_pow_two_eq_one hσ2, hfix, Nat.sub_zero, hcard,
      Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 2)]
  exact hn.neg_one_pow

-- TODO Thm 1.36  : |G|=p^a q ⇒ 単純でない.

end -- 1E

section /- 1F: Brodkey's theorem on abelian Sylow (pp. 37-38) -/

open Pointwise Subgroup MulAction

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- **Isaacs Thm 1.38** (Generalized Brodkey).  有限群 `G` で `S, T ∈ Syl_p(G)` が
`Nat.card (↑S ⊓ ↑T)` を最小化するならば, `D = S ∩ T` の `S` と `T` 両方で正規な
任意の部分群 `K` は `opCore p G = O_p(G)` に含まれる.

正規性は「`S, T` が `K` を正規化する」(`↑S ≤ N_G(K)`, `↑T ≤ N_G(K)`) という形で
与える.  これにより `O_p(G)` が `D` 内の「`S` でも `T` でも正規な最大部分群」
であることを示せる (`opCore_le` で逆向きは自明).

証明 (Isaacs p.38): 任意の Sylow `P : Sylow p G` に対し `K ≤ ↑P` を示せば
`mem_opCore` で結論.  `N := normalizer K` とおくと `S, T ≤ N`.
`(P ⊓ N).subgroupOf N` は `N` の `p`-部分群なので Sylow D で
`(P ⊓ N).subgroupOf N ≤ Q` となる `Q : Sylow p N` 取り, Sylow C in N で
`n : N` あって `n • S.subtype = Q`.  これを `G` に戻すと
`P ⊓ N ≤ (n : G) • ↑S`.  `T ≤ N`, `n ∈ N` から `(n : G) • T ≤ N`, よって
`P ⊓ (n • T) ⊆ P ⊓ N ⊆ n • ↑S`, 一方 `P ⊓ (n • T) ⊆ n • T` 自明,
合わせて `P ⊓ (n • T) ⊆ n • D`.  `n⁻¹ • ` で `n⁻¹ • P ⊓ T ⊆ D`.
最小性で等号: `n⁻¹ • P ⊓ T = D`, 特に `D ≤ n⁻¹ • P`, つまり `n • D ≤ P`.
`n ∈ N = N_G(K)`, `K ≤ D` から `K = n • K ≤ n • D ≤ P`. -/
theorem opCore_eq_inf_of_minimal_sylow_inter
    [Finite G]
    (S T : Sylow p G)
    (hmin : ∀ S' T' : Sylow p G,
        Nat.card ((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) ≤
        Nat.card ((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G))
    {K : Subgroup G} (hKD : K ≤ (S : Subgroup G) ⊓ (T : Subgroup G))
    (hSN : (S : Subgroup G) ≤ normalizer K) (hTN : (T : Subgroup G) ≤ normalizer K) :
    K ≤ opCore p G := by
  classical
  set N : Subgroup G := normalizer K with hNdef
  set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
  have hD_le_N : D ≤ N := inf_le_left.trans hSN
  intro k hk
  refine (mem_opCore (G := G)).mpr (fun P => ?_)
  -- Step 1: ((↑P ⊓ N).subgroupOf N) is a p-subgroup of N.
  -- Via the iso (↑P ⊓ N).subgroupOf N ≃* (↑P ⊓ N), and (↑P ⊓ N) is a p-group (sub of ↑P).
  have hPN_pgroup : IsPGroup p (((P : Subgroup G) ⊓ N).subgroupOf N) := by
    have hPN_pgroup_G : IsPGroup p ((P : Subgroup G) ⊓ N : Subgroup G) := P.2.to_inf_left
    exact hPN_pgroup_G.of_injective
      (Subgroup.subgroupOfEquivOfLe (G := G) (H := (P : Subgroup G) ⊓ N) (K := N)
        inf_le_right).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (G := G) (H := (P : Subgroup G) ⊓ N) (K := N)
        inf_le_right).injective
  -- Step 2: Sylow D in N.
  obtain ⟨Q, hPNQ⟩ := hPN_pgroup.exists_le_sylow
  -- Step 3: Sylow C in N: n • S.subtype hSN = Q.
  haveI : Finite (Sylow p N) := inferInstance
  obtain ⟨n, hnSQ⟩ := MulAction.exists_smul_eq N (S.subtype hSN) Q
  -- Step 4: pull back: P ⊓ N ≤ MulAut.conj (n : G) • ↑S.
  have hPN_in_nS : (P : Subgroup G) ⊓ N ≤ MulAut.conj (n : G) • (S : Subgroup G) := by
    intro g hg
    obtain ⟨hgP, hgN⟩ := hg
    have hg_inSub : (⟨g, hgN⟩ : N) ∈ ((P : Subgroup G) ⊓ N).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]; exact ⟨hgP, hgN⟩
    have hg_inQ : (⟨g, hgN⟩ : N) ∈ Q := hPNQ hg_inSub
    rw [← hnSQ] at hg_inQ
    -- hg_inQ : ⟨g, hgN⟩ ∈ (n • S.subtype hSN : Sylow p N).
    -- Membership in a Sylow ≡ membership in its underlying Subgroup; unfold then.
    have hg_inQ' : (⟨g, hgN⟩ : N) ∈
        (((n : N) • S.subtype hSN : Sylow p N) : Subgroup N) := hg_inQ
    rw [show (((n : N) • S.subtype hSN : Sylow p N) : Subgroup N) =
        MulAut.conj (n : N) • (S.subtype hSN : Subgroup N) from
        Sylow.coe_subgroup_smul] at hg_inQ'
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hg_inQ'
    -- hg_inQ : (MulAut.conj (n : N))⁻¹ • ⟨g, hgN⟩ ∈ S.subtype hSN
    -- This means ((n : N)⁻¹ * ⟨g, hgN⟩ * (n : N)) ∈ S.subtype hSN.
    -- Project to G: (n : G)⁻¹ * g * (n : G) ∈ S.
    have hgS : ((n : G)⁻¹ * g * (n : G)) ∈ (S : Subgroup G) := by
      have hN_val : (((MulAut.conj (n : N))⁻¹ • ⟨g, hgN⟩ : N) : G) =
          (n : G)⁻¹ * g * (n : G) := by
        simp [MulAut.smul_def]
      -- hg_inQ as membership in subtype: (... : N) ∈ S.subtype hSN.
      -- Use Sylow.coe_subtype: S.subtype hSN.toSubgroup = (↑S).subgroupOf N
      have hin_subOf : ((MulAut.conj (n : N))⁻¹ • ⟨g, hgN⟩ : N) ∈
          (S : Subgroup G).subgroupOf N := by
        rw [← Sylow.coe_subtype]
        exact hg_inQ'
      rw [Subgroup.mem_subgroupOf] at hin_subOf
      rwa [hN_val] at hin_subOf
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    exact hgS
  -- Step 5: T ≤ N and (n : G) ∈ N, so MulAut.conj (n : G) • ↑T ≤ N.
  have hnT_le_N : MulAut.conj (n : G) • (T : Subgroup G) ≤ N := by
    have hn_in_N : (n : G) ∈ N := n.2
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hx
    have hConjN : (n : G)⁻¹ * x * (n : G) ∈ N := hTN hx
    have hx_eq : x = (n : G) * ((n : G)⁻¹ * x * (n : G)) * (n : G)⁻¹ := by group
    rw [hx_eq]
    exact N.mul_mem (N.mul_mem hn_in_N hConjN) (N.inv_mem hn_in_N)
  -- Step 6: P ⊓ (MulAut.conj n • T) ≤ MulAut.conj n • D.
  have hPnT_le_nD : (P : Subgroup G) ⊓ (MulAut.conj (n : G) • (T : Subgroup G)) ≤
      MulAut.conj (n : G) • D := by
    rw [hDdef, Subgroup.smul_inf]
    refine le_inf ?_ inf_le_right
    exact (inf_le_inf_left _ hnT_le_N).trans hPN_in_nS
  -- Step 7: conjugate by n⁻¹: (n⁻¹ • P) ⊓ T ≤ D.
  have hnInvP_T_le_D :
      MulAut.conj ((n : G)⁻¹) • (P : Subgroup G) ⊓ (T : Subgroup G) ≤ D := by
    have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := MulAut.conj ((n : G)⁻¹)) |>.mpr hPnT_le_nD
    rw [Subgroup.smul_inf] at h1
    have he1 : MulAut.conj ((n : G)⁻¹) • (MulAut.conj (n : G) • (T : Subgroup G)) =
        (T : Subgroup G) := by
      rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have he2 : MulAut.conj ((n : G)⁻¹) • (MulAut.conj (n : G) • D) = D := by
      rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [he1, he2] at h1
    exact h1
  -- Step 8: define P' := n⁻¹ • P, use minimality of D.
  set P' : Sylow p G := (n : G)⁻¹ • P with hP'def
  have hP'_coe : (P' : Subgroup G) = MulAut.conj ((n : G)⁻¹) • (P : Subgroup G) := by
    rw [hP'def]; exact Sylow.coe_subgroup_smul
  have hP'T_le_D : (P' : Subgroup G) ⊓ (T : Subgroup G) ≤ D := by
    rw [hP'_coe]; exact hnInvP_T_le_D
  have hcard_ge : Nat.card D ≤
      Nat.card ((P' : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) := by
    have := hmin P' T
    simpa [hDdef] using this
  haveI : Finite D := inferInstance
  have hP'T_eq_D : (P' : Subgroup G) ⊓ (T : Subgroup G) = D :=
    Subgroup.eq_of_le_of_card_ge hP'T_le_D hcard_ge
  -- Step 9: D ≤ ↑P', so MulAut.conj n • D ≤ ↑P (re-conjugating).
  have hD_le_P' : D ≤ (P' : Subgroup G) := hP'T_eq_D ▸ inf_le_left
  have hnD_le_P : MulAut.conj (n : G) • D ≤ (P : Subgroup G) := by
    have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := MulAut.conj (n : G)) |>.mpr hD_le_P'
    rw [hP'_coe] at h1
    have he : MulAut.conj (n : G) • (MulAut.conj ((n : G)⁻¹) • (P : Subgroup G)) =
        (P : Subgroup G) := by
      rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    rw [he] at h1
    exact h1
  -- Step 10: K = MulAut.conj n • K (n ∈ N_G(K)), K ≤ D, so K ≤ n • D ≤ ↑P.
  have hnK_eq_K : MulAut.conj (n : G) • K = K := by
    have hn_in_N : (n : G) ∈ normalizer (K : Set G) := by
      change (n : G) ∈ N
      exact n.2
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hx
      rw [mem_normalizer_iff''] at hn_in_N
      exact (hn_in_N x).mpr hx
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
      rw [mem_normalizer_iff''] at hn_in_N
      exact (hn_in_N x).mp hx
  have hK_le_P : K ≤ (P : Subgroup G) := by
    rw [← hnK_eq_K]
    intro x hx
    exact hnD_le_P (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKD hx)
  exact hK_le_P hk

/-- **Isaacs Thm 1.37** (Brodkey).  有限群 `G` の各 Sylow `p`-部分群が abelian ならば,
ある `S, T ∈ Syl_p(G)` で `↑S ⊓ ↑T = opCore p G`.

`hAbel` は「各 Sylow `p`-部分群の任意の 2 元が可換」という形.
Sylow C で全 Sylow は同型なので 1 つ abelian なら全 abelian.

証明: `Nat.card (↑S ⊓ ↑T)` を最小化するペア `(S, T)` を取り Thm 1.38
(`opCore_eq_inf_of_minimal_sylow_inter`) を `K := ↑S ⊓ ↑T` に適用.
`S, T` が abelian なので `↑S ⊓ ↑T ≤ ↑S` の任意要素は `↑S` (`↑T`) の元と可換,
すなわち `↑S ≤ N_G(↑S ⊓ ↑T)`, `↑T ≤ N_G(↑S ⊓ ↑T)`.  Thm 1.38 で
`↑S ⊓ ↑T ≤ opCore p G`.  逆方向 `opCore p G ≤ ↑S ⊓ ↑T` は `opCore_le`. -/
theorem exists_pair_inf_eq_opCore_of_abelian
    [Finite G]
    (hAbel : ∀ (S : Sylow p G) (x y : G), x ∈ (S : Subgroup G) → y ∈ (S : Subgroup G) →
      Commute x y) :
    ∃ S T : Sylow p G, (S : Subgroup G) ⊓ (T : Subgroup G) = opCore p G := by
  classical
  haveI := Fintype.ofFinite (Sylow p G)
  obtain ⟨ST, _, hmin⟩ :=
    (Finset.univ : Finset (Sylow p G × Sylow p G)).exists_min_image
      (fun ST => Nat.card ((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G) : Subgroup G))
      ⟨(default : Sylow p G × Sylow p G), Finset.mem_univ _⟩
  obtain ⟨S, T⟩ := ST
  refine ⟨S, T, ?_⟩
  have hmin' : ∀ S' T' : Sylow p G,
      Nat.card ((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) ≤
      Nat.card ((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G) :=
    fun S' T' => hmin (S', T') (Finset.mem_univ _)
  refine le_antisymm ?_ (le_inf (opCore_le S) (opCore_le T))
  -- For abelian Sylow R containing D ≤ R: r ∈ R commutes with d ∈ D ≤ R,
  -- so MulAut.conj r fixes D pointwise ⇒ R ≤ N_G(D).
  have hD_normal_in (R : Sylow p G) (hDR : (S : Subgroup G) ⊓ (T : Subgroup G) ≤ R) :
      (R : Subgroup G) ≤
        normalizer (((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
    intro r hr
    change ∀ d, d ∈ ((S : Subgroup G) ⊓ (T : Subgroup G)) ↔
        r * d * r⁻¹ ∈ ((S : Subgroup G) ⊓ (T : Subgroup G))
    intro d
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · -- d ∈ D, r ∈ R, both in abelian R (d ∈ D ≤ R): r d r⁻¹ = d ∈ D.
      have hd_in_R : d ∈ (R : Subgroup G) := hDR hd
      have hcomm : Commute r d := hAbel R r d hr hd_in_R
      have heq : r * d * r⁻¹ = d := by
        rw [Commute, SemiconjBy] at hcomm
        -- hcomm : r * d = d * r
        calc r * d * r⁻¹ = d * r * r⁻¹ := by rw [hcomm]
          _ = d := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact hd
    · -- r d r⁻¹ ∈ D ≤ R, so r and (r d r⁻¹) ∈ R commute (R abelian),
      -- so r⁻¹ * (r d r⁻¹) * r = (r d r⁻¹), hence d = r d r⁻¹ ∈ D.
      have hcomm : Commute r (r * d * r⁻¹) := hAbel R r (r * d * r⁻¹) hr (hDR hd)
      have heq : r⁻¹ * (r * d * r⁻¹) * r = r * d * r⁻¹ := by
        rw [Commute, SemiconjBy] at hcomm
        -- hcomm : r * (rdr⁻¹) = (rdr⁻¹) * r
        calc r⁻¹ * (r * d * r⁻¹) * r
            = r⁻¹ * ((r * d * r⁻¹) * r) := by rw [mul_assoc]
          _ = r⁻¹ * (r * (r * d * r⁻¹)) := by rw [hcomm]
          _ = r * d * r⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      have hd_eq : d = r⁻¹ * (r * d * r⁻¹) * r := by group
      rw [hd_eq, heq]; exact hd
  refine opCore_eq_inf_of_minimal_sylow_inter S T hmin' (le_refl _)
    (hD_normal_in S inf_le_left) (hD_normal_in T inf_le_right)

/-- **Isaacs Cor 1.39**.  有限群 `G` で各 Sylow `p`-部分群が abelian な場合,
任意の Sylow `P` について `[G : opCore p G] ≤ [G : P]²`.

証明: Brodkey (Thm 1.37) で `S, T` を `↑S ⊓ ↑T = opCore p G` となるよう取る.
`Subgroup.index_inf_le` で `(↑S ⊓ ↑T).index ≤ ↑S.index * ↑T.index`.
Sylow 部分群は全て同型なので `↑S.index = ↑T.index = ↑P.index`. -/
theorem index_opCore_le_index_sylow_sq
    [Finite G]
    (hAbel : ∀ (S : Sylow p G) (x y : G), x ∈ (S : Subgroup G) → y ∈ (S : Subgroup G) →
      Commute x y) (P : Sylow p G) :
    (opCore p G).index ≤ (P : Subgroup G).index ^ 2 := by
  obtain ⟨S, T, hST⟩ := exists_pair_inf_eq_opCore_of_abelian (G := G) (p := p) hAbel
  have hSidx : (S : Subgroup G).index = (P : Subgroup G).index := by
    have h1 : Nat.card (S : Subgroup G) = Nat.card (P : Subgroup G) :=
      Nat.card_congr (Sylow.equiv (G := G) (p := p) S P).toEquiv
    have hS := (S : Subgroup G).card_mul_index
    have hP := (P : Subgroup G).card_mul_index
    have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
    rw [← hS, h1] at hP
    exact (Nat.eq_of_mul_eq_mul_left hPpos hP).symm
  have hTidx : (T : Subgroup G).index = (P : Subgroup G).index := by
    have h1 : Nat.card (T : Subgroup G) = Nat.card (P : Subgroup G) :=
      Nat.card_congr (Sylow.equiv (G := G) (p := p) T P).toEquiv
    have hT := (T : Subgroup G).card_mul_index
    have hP := (P : Subgroup G).card_mul_index
    have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
    rw [← hT, h1] at hP
    exact (Nat.eq_of_mul_eq_mul_left hPpos hP).symm
  calc (opCore p G).index
      = ((S : Subgroup G) ⊓ (T : Subgroup G)).index := by rw [hST]
    _ ≤ (S : Subgroup G).index * (T : Subgroup G).index := Subgroup.index_inf_le
    _ = (P : Subgroup G).index ^ 2 := by rw [hSidx, hTidx, sq]

/-- **Isaacs Cor 1.40**.  有限群 `G` で各 Sylow `p`-部分群が abelian かつ
`|G| < |P|²` (= `|P| > |G|^{1/2}`) ならば `opCore p G ≠ ⊥`.

証明: Cor 1.39 で `[G : opCore p G] ≤ [G : P]²`. `|G| < |P|²` から
`[G : P]² < |G|`, 一方 `[G : ⊥] = |G|`. もし `opCore p G = ⊥` なら
`|G| = [G : ⊥] ≤ [G : P]² < |G|`, 矛盾. -/
theorem opCore_ne_bot_of_card_sylow_sq_gt
    [Finite G]
    (hAbel : ∀ (S : Sylow p G) (x y : G), x ∈ (S : Subgroup G) → y ∈ (S : Subgroup G) →
      Commute x y) (P : Sylow p G)
    (hcard : Nat.card G < Nat.card (P : Subgroup G) ^ 2) :
    opCore p G ≠ ⊥ := by
  intro h
  have hidx_le := index_opCore_le_index_sylow_sq (G := G) (p := p) hAbel P
  have hP := (P : Subgroup G).card_mul_index
  have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
  have hG_pos : 0 < Nat.card G := Nat.card_pos
  have hsq : Nat.card (P : Subgroup G) ^ 2 * (P : Subgroup G).index ^ 2 = Nat.card G ^ 2 := by
    rw [← mul_pow, hP]
  have hPidx_sq : (P : Subgroup G).index ^ 2 < Nat.card G := by
    by_contra hne
    push Not at hne
    have h_mul : Nat.card (P : Subgroup G) ^ 2 * Nat.card G ≤ Nat.card G ^ 2 :=
      calc Nat.card (P : Subgroup G) ^ 2 * Nat.card G
          ≤ Nat.card (P : Subgroup G) ^ 2 * (P : Subgroup G).index ^ 2 :=
            Nat.mul_le_mul_left _ hne
        _ = Nat.card G ^ 2 := hsq
    have hGmul : Nat.card G ^ 2 < Nat.card (P : Subgroup G) ^ 2 * Nat.card G := by
      rw [sq (Nat.card G)]
      rw [show Nat.card (P : Subgroup G) ^ 2 * Nat.card G =
          Nat.card G * Nat.card (P : Subgroup G) ^ 2 from mul_comm _ _]
      exact (Nat.mul_lt_mul_left hG_pos).mpr hcard
    exact (hGmul.trans_le h_mul).false
  rw [h, Subgroup.index_bot] at hidx_le
  exact (hidx_le.trans_lt hPidx_sq).false

end -- 1F

section /- 1G: Chermak–Delgado (pp. 41-44) — Phase 1 では省略 -/

/-! ### §1G (Chermak–Delgado measure) は本プロジェクトでは省略

**省略理由 (2026-05-21 決定)**: Isaacs §1G は Chermak–Delgado measure
`m_G(H) := |H|·|C_G(H)|` と最大値部分群族 `L(G)` の理論 (Thm 1.41–1.46).
本プロジェクトの目標である Feit-Thompson 形式化 (Phase 2a/2b: BG + Peterfalvi)
において Chermak / Delgado への引用は `references/bg/*.mmd` および
`references/peterfalvi/*.mmd` の grep 検索で **0 件** (2026-05-21 確認).
従って本プロジェクトのスコープ外として正式に省略する.

将来 mathlib 本体への寄与時等に必要となれば Isaacs Thm 1.41–1.46 を本節に
追加する; その際の起点は本書 pp.41-44 の議論で, 特に Lemma 1.43
(m の不等式) が技術的中核.

関連項目: §1F Brodkey (Thm 1.37) は Chermak–Delgado から派生する Cor 1.39 の
abelian Sylow 版で, こちらは本ファイル §1F に実装済 (`exists_pair_inf_eq_opCore_of_abelian`,
`index_opCore_le_index_sylow_sq`). -/

end -- 1G

end OddOrder.Isaacs.Ch01
