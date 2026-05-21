/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
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

-- TODO `opCore.normal` (`O_p(G)` は `G` で正規).
--   共役で全 Sylow が permute されることから `⨅ Sylow` が共役不変であることを示す.
--   `Sylow.coe_subgroup_smul` + `Subgroup.mem_pointwise_smul_iff_inv_smul_mem` の
--   組み合わせで membership 計算する必要があり、`MulAut.conj` の inverse 周りで
--   simp 補題が要安定化のため次の iteration へ.

-- TODO **Isaacs Problem 1B.2** (`opCore` の最大性): 任意の正規 `p`-部分群 ⊆ `opCore p G`.
--   証明骨子: 正規 `p`-部分群 N について N ≤ Q ∈ Sylow (Sylow D), 任意の P ∈ Sylow に対し
--   N = g • N ⊆ g • Q = P (Sylow C による共役). 上の `opCore.normal` 同様,
--   pointwise smul の membership 計算が必要.

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
