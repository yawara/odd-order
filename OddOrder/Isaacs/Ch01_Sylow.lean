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
| 1F | Brodkey の定理 (Sylow が abelian の場合) | 1.37 – 1.40 | TODO |
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

-- TODO **Isaacs Thm 1.16**.  S, T ∈ Syl_p(G) で |S∩T| が最大のとき
--   n_p(G) ≡ 1 (mod |S : S∩T|), すなわち S での S∩T からの相対指数.
--   S 上の共役作用で固定点を数える精密な mod 計算が必要.
--   mathlib に直接対応する補題がなく 40 行超の実装が見込まれるため TODO に留める.

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

-- TODO Thm 1.19    : N ◁ P (P p-群) 非自明 ⇒ N ∩ Z(P) > 1.
-- TODO Lemma 1.20  : 有限 G が冪零であることの諸特性化.
-- TODO Thm 1.21    : 冪零群の中心列の存在/性質.   `Group.IsNilpotent`.
-- TODO Thm 1.22    : 冪零で H < G ⇒ N_G(H) > H.
-- TODO Lemma 1.23  : p-群 P, N < M ◁ P ⇒ ∃ L ◁ P, N ⊆ L ⊆ M, |L:N|=p.
-- TODO Cor 1.24    : 位数 p^a の p-群は各 b ≤ a で正規部分群 |L|=p^b を持つ.
-- TODO Cor 1.25    : 有限 G, p^b ∣ |G| ⇒ 位数 p^b の部分群存在.

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

-- TODO **Isaacs Lemma 1.27**. 互いに素な位数を持つ有限正規部分群族の和は `iSupIndep`.
--   mathlib `Subgroup.independent_of_coprime_order` を呼ぶラッパー. ただし
--   その関数は `Pairwise commute` を要求し, 正規部分群 + coprime cards から
--   `Disjoint` ⇒ `commute_of_normal_of_disjoint` への中継補題が必要 (要 Lagrange
--   による `orderOf` の分割整除).

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

-- TODO **Isaacs Cor 1.29** (冪零正規部分群の積も冪零).  Cor 1.28 (b) から直結:
--   K, L 冪零正規 ⇒ K, L ≤ fitting ⇒ KL ≤ fitting (冪零) ⇒ KL 冪零.

end -- 1D

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. 31-34) -/

variable {G : Type*} [Group G]

-- TODO Thm 1.30  : |G|=pq (q<p 素) ⇒ Sylow p 正規; q ∤ p−1 なら G 巡回.
-- TODO Thm 1.31  : |G|=p²q ⇒ Sylow p または q が正規.
-- TODO Thm 1.32  : |G|=p³q ⇒ 同上 (例外 |G|=24).
-- TODO Thm 1.33  : |G|=24 ∧ n_2,n_3>1 ⇒ G ≅ S_4.

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

section /- 1F: Brodkey's theorem on abelian Sylow (pp. ?–?) -/

-- TODO Thm 1.37 (Brodkey): G の Sylow p abelian ⇒ ∃ S, T ∈ Syl_p, S∩T = O_p(G).
-- TODO Thm 1.38  : 任意有限 G で S∩T 最小化を取ると O_p(G) 最大.
-- TODO Cor 1.39  : abelian Sylow ⇒ [G : O_p(G)] ≤ [G : P]².
-- TODO Cor 1.40  : abelian Sylow, |P| > |G|^{1/2} ⇒ O_p(G)>1.

end -- 1F

section /- 1G: Chermak–Delgado (pp. ?–?) -/

-- TODO Thm 1.41 (Chermak–Delgado):
--   G 有限 ⇒ 特性的 abelian N, [G:N] ≤ [G:A]² for all abelian A.
-- TODO Lemma 1.42 : m_G(H) ≤ m_G(C_G(H)); 等号 ⇔ H = C_G(C_G(H)).
-- TODO Lemma 1.43 : H, K ⊆ G, D = H∩K, J = ⟨H,K⟩ で m の不等式.
-- TODO Thm 1.44   : Chermak-Delgado measure 最大の部分群族 L(G) の格子構造.
-- TODO Cor 1.45   : L(G) には最小元 M (abelian, M ⊇ Z(G)).
-- TODO Cor 1.46   : |H|·|C_G(H)| > |G| ⇒ G は非可換単純群でない.

end -- 1G

end OddOrder.Isaacs.Ch01
