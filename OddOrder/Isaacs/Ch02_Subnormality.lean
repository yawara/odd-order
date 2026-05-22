/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch01_Sylow

open OddOrder.Isaacs.Ch01

/-!
# OddOrder.Isaacs.Ch02 — Subnormality

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 2
"Subnormality" (pp. 45-64) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 2A | 部分正規性の基本・join 定理・Wielandt の F(G) | 2.1 – 2.11 | 着手中 (基礎ラッパー済) |
| 2B | Baer の定理と Matsuyama の involution 定理 | 2.12 – 2.14 | TODO |
| 2C | p-local 部分群 | 2.15 – 2.17 | TODO |
| 2D | Zenkov と Lucchini | 2.18 – 2.20 | TODO (FT 経路で必要なし) |

## 方針

mathlib `Subgroup.IsSubnormal` (inductive predicate + `isSubnormal_iff` chain 表現 +
`subgroupOf` / `inf` / `trans` / `map` / `comap` ら) を全面利用。Ch.1 の `Subgroup.fitting`
(= F(G)) と Thm 1.26 (`isNilpotent_of_finite_tfae` 経由の NormalizerCondition) を
橋渡しに使う。

新規定義は `IsMinimalNormal` (mathlib 未収載). Thm 2.6 や 2.18 で必須。

ノート: [notes/isaacs/ch02_subnormality.md](../../notes/isaacs/ch02_subnormality.md)
-/

namespace OddOrder.Isaacs.Ch02

section /- 2A: Subnormality basics, joins, Wielandt's F(G) (pp. 45-54) -/

/-! ### mathlib 直接利用 (本ファイル内に wrapper を置かない)

CLAUDE.md `## 開発規約 ### mathlib ラッパー方針` に従い, 以下の Isaacs 結果は
mathlib に直接対応があり, 純粋なリネームラッパーは書かない. 呼び出し側で
直接 mathlib 名を使う:

* **Isaacs Cor 2.4** (`S ∩ T subnormal`): `Subgroup.IsSubnormal.inf`
* (`H ⊴ G ⇒ H ⊴⊴ G`): `Subgroup.Normal.isSubnormal`
* (subnormal の推移律): `Subgroup.IsSubnormal.trans`
* (subnormal の準同型像/逆像/quotient/smul): `.map`, `.comap`, `.quotient`, `.smul`
* (単純群の subnormal は normal): `.normal_of_isSimpleGroup`, `.eq_bot_or_top_of_isSimpleGroup`

下記の wrapper は **適応** または **2 回以上の使用予定** で書く:
* `inf_isSubnormal_subgroupOf` (Thm 2.3): `S ⊓ K |_K = S |_K` への書換を含む
* `commute_of_disjoint_normal` (Lemma 2.7): `Normal` を instance, `M N` を implicit
  に取り直した適応版 (Thm 2.6 等で複数回使う)
-/

variable {G : Type*} [Group G]

/-- **Minimal normal subgroup**: `M` が `G` の非自明正規部分群で、`M` に真に含まれる
`G`-正規部分群は `⊥` のみ。

mathlib 未収載 (`IsAtom` は subgroup lattice 全体に対するもので normal lattice
には対応しない). Isaacs Thm 2.6, 2.18 (Zenkov) で必須。 -/
def IsMinimalNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M

/-- **Isaacs Lemma 2.1, easy direction** (every subgroup subnormal ⇒ nilpotent).

「全ての部分群が部分正規」ならば NormalizerCondition が成立し，Thm 1.26 経由で冪零。
キーは mathlib `Subgroup.IsSubnormal.iff_eq_top_or_exists`: `H` が部分正規かつ `H ≠ ⊤`
ならば `H < K` で `H ⊴ K` となる `K` が存在する。すると `K ≤ N_G(H)` で `H < N_G(H)`。 -/
theorem isNilpotent_of_all_isSubnormal [Finite G]
    (h : ∀ H : Subgroup G, H.IsSubnormal) : Group.IsNilpotent G := by
  refine ((isNilpotent_of_finite_tfae (G := G)).out 1 0).mp ?_
  intro H hHlt
  rcases Subgroup.IsSubnormal.iff_eq_top_or_exists.mp (h H) with hHtop | ⟨K, hHK, _, hKnorm⟩
  · exact absurd hHtop hHlt.ne
  · have hKle : K ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHK.le).mp hKnorm
    exact lt_of_lt_of_le hHK hKle

/-- **Isaacs Lemma 2.1, hard direction** (nilpotent ⇒ every subgroup subnormal).

`H.index` についての強induction。`H = ⊤` ならば trivially top。さもなくば
NormalizerCondition (Thm 1.26) で `H < N_G(H)`，`N_G(H).index < H.index` なので
帰納仮定 → `N_G(H).IsSubnormal` → `IsSubnormal.step` で `H.IsSubnormal`。

`H` のなかで `H ⊴ N_G(H)` は `Subgroup.normal_subgroupOf_iff_le_normalizer le_normalizer`
で，K = N_G(H) のときは `K = normalizer K` ではないが `H ≤ normalizer H` から
`(H.subgroupOf normalizer H).Normal` が出る。 -/
theorem isSubnormal_of_isNilpotent_finite [Finite G] [Group.IsNilpotent G]
    (H : Subgroup G) : H.IsSubnormal := by
  classical
  -- Strong induction on H.index.
  induction hN : H.index using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hHt : H = ⊤
    · rw [hHt]; exact Subgroup.IsSubnormal.top
    · -- H < ⊤ via hHt; NormalizerCondition gives H < N_G(H).
      have hNC : NormalizerCondition G :=
        ((isNilpotent_of_finite_tfae (G := G)).out 0 1).mp ‹_›
      have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHt
      have hH_lt_N : H < Subgroup.normalizer (H : Set G) := hNC H hHlt
      -- (normalizer H).index < H.index
      have hidx : (Subgroup.normalizer (H : Set G)).index < n := by
        rw [← hN]
        exact Subgroup.index_strictAnti hH_lt_N
      -- Apply induction hypothesis to normalizer H.
      have hSubnN : (Subgroup.normalizer (H : Set G)).IsSubnormal :=
        ih _ hidx _ rfl
      -- H ⊴ normalizer H, i.e., (H.subgroupOf normalizer H).Normal.
      have hNorm : (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.le_normalizer)).mpr le_rfl
      exact Subgroup.IsSubnormal.step _ _ Subgroup.le_normalizer hSubnN hNorm

/-- **Isaacs Lemma 2.1** (full iff). 有限群 `G` について「`G` が冪零」と
「`G` の全ての部分群が部分正規」は同値. -/
theorem isNilpotent_iff_all_isSubnormal [Finite G] :
    Group.IsNilpotent G ↔ ∀ H : Subgroup G, H.IsSubnormal :=
  ⟨fun _ H => isSubnormal_of_isNilpotent_finite H, isNilpotent_of_all_isSubnormal⟩

/-- **Isaacs Lemma 2.3**: `S ⊴⊴ G`, `K ≤ G` ならば `S ∩ K ⊴⊴ K`.

mathlib では `S ∩ K` を `K` の部分群として扱うのに `(S ⊓ K).subgroupOf K` を使う.
`inf_subgroupOf_right` で `(S ⊓ K).subgroupOf K = S.subgroupOf K` に書き換えて
`IsSubnormal.subgroupOf` を適用. -/
theorem inf_isSubnormal_subgroupOf {S : Subgroup G} (hS : S.IsSubnormal) (K : Subgroup G) :
    ((S ⊓ K).subgroupOf K).IsSubnormal := by
  rw [Subgroup.inf_subgroupOf_right]
  exact hS.subgroupOf

/-- **Isaacs Lemma 2.7**: `M, N ◁ G` で `M ∩ N = 1` ならば `M` の元と `N` の元は可換.

mathlib `Subgroup.commute_of_normal_of_disjoint` の **適応版** —
`Normal` を instance, `M N` を implicit に取り直す (Isaacs 流の呼び出し記法).
Thm 2.6 等で複数回使用予定. (CLAUDE.md mathlib ラッパー方針の例外規定に該当.) -/
theorem commute_of_disjoint_normal {M N : Subgroup G} [hM : M.Normal] [hN : N.Normal]
    (hDis : Disjoint M N) {m n : G} (hm : m ∈ M) (hn : n ∈ N) : Commute m n :=
  Subgroup.commute_of_normal_of_disjoint M N hM hN hDis m n hm hn

/-! ### Socle (全 minimal normal subgroup の sup), Thm 2.6 への準備 -/

variable (G) in
/-- **Socle**: `G` の全ての minimal normal subgroup の sup.

`Soc(G)` (Isaacs では §4Aで導入, p.92). Thm 2.6 で `M ≤ Soc(N)` の経路を作るのに使う.
mathlib 未収載. -/
def socle : Subgroup G :=
  ⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)

/-- minimal normal subgroup は socle に含まれる. (`le_iSup` 適応; 章内で 2 回以上使う.) -/
theorem isMinimalNormal_le_socle {M : Subgroup G} (hM : IsMinimalNormal M) :
    M ≤ socle G :=
  le_iSup (fun M : {M : Subgroup G // IsMinimalNormal M} => (M : Subgroup G)) ⟨M, hM⟩

/-- `Soc(G)` は `G` の正規部分群. 各 minimal normal の正規性を `iSup_induction` で
全体に持ち上げる. テンプレートは [`Ch01_Sylow.lean` `fitting.normal`](Ch01_Sylow.lean#L834). -/
instance socle.normal : (socle G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ socle G) hn
    ?mem ?one ?mul
  case mem =>
    rintro ⟨M, hM⟩ x hx
    exact isMinimalNormal_le_socle hM (hM.1.conj_mem x hx g)
  case one => simp
  case mul =>
    intro x y hx hy
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (socle G).mul_mem hx hy

/-- minimal normal subgroup は MulEquiv `ϕ : G ≃* G` による像も minimal normal. -/
theorem IsMinimalNormal.map_equiv {M : Subgroup G} (hM : IsMinimalNormal M) (ϕ : G ≃* G) :
    IsMinimalNormal (M.map ϕ.toMonoidHom) := by
  refine ⟨hM.1.map ϕ.toMonoidHom ϕ.surjective, ?_, ?_⟩
  · -- `M.map ϕ ≠ ⊥` since `ϕ` injective ⇒ image of a nontrivial subgroup is nontrivial.
    intro heq
    apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    have hmem : ϕ m ∈ M.map ϕ.toMonoidHom := ⟨m, hm, rfl⟩
    rw [heq, Subgroup.mem_bot] at hmem
    have h1 : m = 1 := ϕ.injective (by rw [hmem]; exact (ϕ.map_one).symm)
    rw [h1]; exact Subgroup.one_mem _
  · -- minimality: any `N ≤ M.map ϕ` normal in `G` must be `⊥` or `M.map ϕ`.
    intro N hN hNle
    -- Move along ϕ.symm.
    have hN' : (N.map ϕ.symm.toMonoidHom).Normal := hN.map ϕ.symm.toMonoidHom ϕ.symm.surjective
    have hle : N.map ϕ.symm.toMonoidHom ≤ M := by
      rintro _ ⟨y, hyN, rfl⟩
      rcases hNle hyN with ⟨z, hzM, hzeq⟩
      have h1 : ϕ.symm.toMonoidHom y = z := by
        show ϕ.symm y = z
        rw [← hzeq]; exact ϕ.symm_apply_apply z
      rw [h1]; exact hzM
    -- Transport back: N = (N.map ϕ.symm).map ϕ via map_map and ϕ.symm.trans ϕ = id.
    have hback : (N.map ϕ.symm.toMonoidHom).map ϕ.toMonoidHom = N := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id N
      ext x; simp
    rcases hM.2.2 _ hN' hle with hbot | htop
    · left
      rw [← hback, hbot, Subgroup.map_bot]
    · right
      rw [← hback, htop]

/-- `Soc(G)` は `G` の特性部分群. 任意の `ϕ : G ≃* G` について `(Soc G).map ϕ ≤ Soc G`
を `characteristic_iff_map_le` で示す. -/
instance socle.characteristic : (socle G).Characteristic := by
  refine (Subgroup.characteristic_iff_map_le).mpr ?_
  intro ϕ
  show (⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)).map
      ϕ.toMonoidHom ≤ socle G
  rw [Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨M, hM⟩
  exact isMinimalNormal_le_socle (hM.map_equiv ϕ)

/-- 有限群の任意の非自明な正規部分群は minimal normal subgroup を含む.
`Nat.card N` の強induction. テンプレートは `isSubnormal_of_isNilpotent_finite`. -/
theorem exists_isMinimalNormal_le_of_normal [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N := by
  classical
  -- We need to carry `N.Normal` through the induction; promote it to an explicit hyp.
  suffices h : ∀ (k : ℕ) (N : Subgroup G), N.Normal → Nat.card N ≤ k → N ≠ ⊥ →
      ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N by
    exact h (Nat.card N) N ‹N.Normal› le_rfl hN
  intro k
  induction k with
  | zero =>
    intro N _ hcard _
    -- Nat.card N = 0 contradiction with Nat.card_pos
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ k ih =>
    intro N hNn hcard hNne
    by_cases hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N
    · exact ⟨N, ⟨hNn, hNne, hmin⟩, le_rfl⟩
    · push_neg at hmin
      obtain ⟨K, hKnorm, hKleN, hKne_bot, hKne_N⟩ := hmin
      have hKlt : K < N := lt_of_le_of_ne hKleN hKne_N
      have hsub : (K : Set G) ⊂ (N : Set G) := SetLike.coe_ssubset_coe.mpr hKlt
      obtain ⟨x, hxN, hxK⟩ := Set.exists_of_ssubset hsub
      have hcard_K : Nat.card K < Nat.card N := by
        have hequiv : K ≃ {n : N // (n : G) ∈ K} :=
          { toFun := fun ⟨g, hg⟩ => ⟨⟨g, hKleN hg⟩, hg⟩
            invFun := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, hg⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
        rw [Nat.card_congr hequiv]
        exact Finite.card_subtype_lt (p := fun n : N => (n : G) ∈ K)
          (x := ⟨x, hxN⟩) hxK
      have hcard_K_le : Nat.card K ≤ k := by omega
      obtain ⟨M, hMmin, hMleK⟩ := ih K hKnorm hcard_K_le hKne_bot
      exact ⟨M, hMmin, hMleK.trans hKleN⟩

/-- 非自明な有限群は socle が非自明. (Thm 2.6 Case 2 で使う.) -/
theorem socle_ne_bot_of_nontrivial [Finite G] [Nontrivial G] : socle G ≠ ⊥ := by
  obtain ⟨M, hM, _⟩ := exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  intro hbot
  apply hM.2.1
  exact le_bot_iff.mp (hbot ▸ isMinimalNormal_le_socle hM)

/-! ### Isaacs Thm 2.2 (`H ⊆ F(G) ⇔ H` 冪零 + subnormal) -/

/-- Thm 2.2 逆方向の strong induction を `|G| ≤ n` で外側に出した補助補題.
`G` を generalize するため `∀ n, ∀ G, ...` の形を取る (Ch.2 内の
`isMinimalNormal_le_normalizer_aux` と同じパターン). -/
private theorem le_fitting_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {H : Subgroup G},
      Group.IsNilpotent H → H.IsSubnormal → H ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ H hNilp hSn
    by_cases hHtop : H = ⊤
    · -- H = ⊤: `G` 冪零 ⇒ `(⊤ : Subgroup G) ≤ fitting G`
      subst hHtop
      haveI := hNilp
      exact nilpotent_normal_le_fitting
    · -- H < ⊤: penultimate term `K` を取って IH を `K` に適用
      obtain ⟨K, hKnorm, hHK, hKlt⟩ := hSn.exists_normal_and_le_and_lt_top_of_ne hHtop
      have _ := hKnorm
      -- `Nat.card K < Nat.card G ≤ succ n`, so `Nat.card K ≤ n`.
      have hKcard_le : Nat.card K ≤ n := by
        have hKle : Nat.card K ≤ Nat.card G := K.card_le_card_group
        have hKne_top : K ≠ ⊤ := hKlt.ne
        have hKne : Nat.card K ≠ Nat.card G := fun heq =>
          hKne_top (Subgroup.eq_top_of_card_eq K heq)
        omega
      -- IH の入力: subnormality と nilpotency を `H.subgroupOf K` (K の部分群) に転送.
      have hH_sn_in_K : (H.subgroupOf K).IsSubnormal := hSn.subgroupOf
      have hH_nilp_in_K : Group.IsNilpotent (H.subgroupOf K) :=
        nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK).symm
      have hH_le_fitK : H.subgroupOf K ≤ fitting K :=
        ih K hKcard_le hH_nilp_in_K hH_sn_in_K
      -- `H = (H.subgroupOf K).map K.subtype ≤ (fitting K).map K.subtype`.
      have hHeq : (H.subgroupOf K).map K.subtype = H :=
        Subgroup.map_subgroupOf_eq_of_le hHK
      have hpush : H ≤ (fitting K).map K.subtype := by
        rw [← hHeq]; exact Subgroup.map_mono hH_le_fitK
      -- `(fitting K).map K.subtype` は normal (characteristic in K + K ⊴ G) かつ nilpotent.
      haveI : ((fitting K).map K.subtype).Normal := inferInstance
      haveI : Group.IsNilpotent ((fitting K).map K.subtype) :=
        nilpotent_of_mulEquiv ((fitting K).equivMapOfInjective K.subtype K.subtype_injective)
      exact hpush.trans nilpotent_normal_le_fitting

/-- **Isaacs Thm 2.2**: 有限群 `G` の部分群 `H` について,
`H ≤ F(G) ↔ H が冪零かつ G で部分正規`.

形式化メモ:
- 順方向: `H ≤ F(G)`, `F(G)` 冪零 (Ch.1 `fitting.isNilpotent`) ⇒ `H` も冪零
  (`Subgroup.subgroupOfEquivOfLe` 経由).  `F(G) ⊴ G` で `F(G).IsSubnormal`,
  Lemma 2.1 (`isSubnormal_of_isNilpotent_finite`) で `H.subgroupOf (F(G))` も subnormal,
  `IsSubnormal.trans` で `H.IsSubnormal`.
- 逆方向: `|G|`-induction (`le_fitting_aux`).  `H = ⊤` なら `G` 冪零 ⇒
  `nilpotent_normal_le_fitting`.  `H < ⊤` なら `K ⊴ G, H ≤ K, K < ⊤` を取り
  (`exists_normal_and_le_and_lt_top_of_ne`), IH を `K` に適用して
  `H.subgroupOf K ≤ fitting K`.  `fitting K` は `K` で特性的 (Ch.1
  `fitting.characteristic`) + `K ⊴ G` ⇒ `(fitting K).map K.subtype ⊴ G`, 冪零でもあるので
  `nilpotent_normal_le_fitting` で `fitting G` 配下. -/
theorem le_fitting_iff_isNilpotent_and_isSubnormal [Finite G] (H : Subgroup G) :
    H ≤ fitting G ↔ Group.IsNilpotent H ∧ H.IsSubnormal := by
  refine ⟨fun hH => ⟨?_, ?_⟩,
    fun ⟨hNilp, hSn⟩ => le_fitting_aux (Nat.card G) G le_rfl hNilp hSn⟩
  · -- H ≤ F(G) ⇒ H 冪零 (`H.subgroupOf F(G) ≃* H`, F(G) 冪零, subgroup 継承)
    exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hH)
  · -- H ≤ F(G) ⇒ H subnormal (F(G) subnormal in G + H.subgroupOf F(G) subnormal in F(G))
    have hFsn : (fitting G).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
    have hHsn_in_F : (H.subgroupOf (fitting G)).IsSubnormal :=
      isSubnormal_of_isNilpotent_finite _
    exact Subgroup.IsSubnormal.trans hH hHsn_in_F hFsn

/-- 補助補題 (Thm 2.6 の strong induction の generalized core).

`n : ℕ` についての induction で, 任意の有限群 `G` (with `|G| ≤ n`) に対し,
任意の subnormal `S` と minimal normal `M` で `M ≤ N_G(S)` を示す. -/
private theorem isMinimalNormal_le_normalizer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S M : Subgroup G}, S.IsSubnormal → IsMinimalNormal M →
      M ≤ Subgroup.normalizer (S : Set G) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _ _
    -- Nat.card G = 0 contradicts the fact that G has the identity.
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hG S M hS hM
    classical
    have _ : M.Normal := hM.1
    by_cases hStop : S = ⊤
    · -- normalizer of ⊤ is ⊤ (since ⊤ is normal).
      subst hStop
      rw [Subgroup.normalizer_eq_top (⊤ : Subgroup G)]
      exact le_top
    · obtain ⟨N, hNnorm, hSleN, hNlt⟩ := hS.exists_normal_and_le_and_lt_top_of_ne hStop
      have _ := hNnorm
      by_cases hMN : M ⊓ N = ⊥
      · -- Case 1: M ⊓ N = ⊥. M and N commute; S ≤ N ⇒ M centralizes S.
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hsS
          have hsN : s ∈ N := hSleN hsS
          have hcomm : Commute m s := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm hsN
          have hmsm : m * s * m⁻¹ = s := by
            rw [Commute.eq hcomm, mul_inv_cancel_right]
          rw [hmsm]; exact hsS
        · intro hmsm
          have hsN : m * s * m⁻¹ ∈ N := hSleN hmsm
          have hm_inv : m⁻¹ ∈ M := M.inv_mem hm
          have hcomm : Commute m⁻¹ (m * s * m⁻¹) := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm_inv hsN
          have hseq : s = m⁻¹ * (m * s * m⁻¹) * m := by group
          rw [hseq, Commute.eq hcomm, mul_assoc, inv_mul_cancel, mul_one]
          exact hmsm
      · -- Case 2: M ⊓ N ≠ ⊥. By minimality of M, M ⊓ N = M, i.e., M ≤ N.
        have hMN_le_M : M ⊓ N ≤ M := inf_le_left
        haveI hMN_norm : (M ⊓ N).Normal := Subgroup.normal_inf_normal M N
        have hMN_eq_M : M ⊓ N = M := by
          rcases hM.2.2 (M ⊓ N) hMN_norm hMN_le_M with h | h
          · exact absurd h hMN
          · exact h
        have hMleN : M ≤ N := by
          have h : M ≤ M ⊓ N := le_of_eq hMN_eq_M.symm
          exact (le_inf_iff.mp h).2
        -- |N| < |G| ≤ n+1 so |N| ≤ n.
        have hN_ne_top : N ≠ ⊤ := hNlt.ne
        obtain ⟨g, hg⟩ : ∃ g : G, g ∉ N := by
          by_contra h
          push_neg at h
          exact hN_ne_top (eq_top_iff.mpr fun x _ => h x)
        have hN_card_lt : Nat.card N < Nat.card G :=
          Finite.card_subtype_lt (p := fun x : G => x ∈ N) (x := g) hg
        have hN_card_le_n : Nat.card N ≤ n := by omega
        have hNne_bot : N ≠ ⊥ := by
          intro h
          apply hM.2.1
          rw [eq_bot_iff]; rw [h] at hMleN; exact hMleN
        haveI hNNontriv : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne_bot
        -- IH on ↥N.
        have hSsubN_sn : (S.subgroupOf N).IsSubnormal := hS.subgroupOf
        have hIH : ∀ K : Subgroup N, IsMinimalNormal K →
            K ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          intro K hK
          exact ih N hN_card_le_n hSsubN_sn hK
        have hSoc_le_norm_inner : socle N ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          refine iSup_le ?_
          rintro ⟨K, hK⟩
          exact hIH K hK
        -- Lift: (socle N).map N.subtype ≤ normalizer S in G.
        have hSoc_lift_le_norm :
            (socle N).map N.subtype ≤ Subgroup.normalizer (S : Set G) := by
          rintro _ ⟨⟨g', hg'N⟩, hg'soc, rfl⟩
          change (g' : G) ∈ Subgroup.normalizer (S : Set G)
          have hg'norm : (⟨g', hg'N⟩ : N) ∈
              Subgroup.normalizer (S.subgroupOf N : Set N) := hSoc_le_norm_inner hg'soc
          rw [Subgroup.mem_normalizer_iff] at hg'norm ⊢
          intro s
          by_cases hsN : s ∈ N
          · -- s ∈ N: lift to N, apply hg'norm.
            have hpair := hg'norm ⟨s, hsN⟩
            constructor
            · intro hsS
              have h1 : (⟨s, hsN⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              have h2 := hpair.mp h1
              rw [Subgroup.mem_subgroupOf] at h2
              -- h2 : ((⟨g', _⟩ * ⟨s, _⟩ * ⟨g', _⟩⁻¹ : N) : G) ∈ S
              -- coerce: (⟨a, _⟩ * ⟨b, _⟩ : N : G) = a * b in G.
              convert h2 using 1
            · intro hgsg
              have hgsg_N : g' * s * g'⁻¹ ∈ N := hNnorm.conj_mem s hsN g'
              have h1 : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              -- Identify ⟨g' * s * g'⁻¹, _⟩ with ⟨g', _⟩ * ⟨s, _⟩ * ⟨g', _⟩⁻¹ as N-element.
              have hcong : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) =
                  ⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ := by
                apply Subtype.ext
                change g' * s * g'⁻¹ = (↑(⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ : N) : G)
                push_cast
                rfl
              rw [hcong] at h1
              have h2 := hpair.mpr h1
              rwa [Subgroup.mem_subgroupOf] at h2
          · -- s ∉ N: both sides false.
            have hgsg_notN : g' * s * g'⁻¹ ∉ N := by
              intro h
              apply hsN
              have hseq : s = g'⁻¹ * (g' * s * g'⁻¹) * g' := by group
              rw [hseq]
              have h' : g'⁻¹ * (g' * s * g'⁻¹) * (g'⁻¹)⁻¹ ∈ N :=
                hNnorm.conj_mem _ h g'⁻¹
              rwa [inv_inv] at h'
            constructor
            · intro hsS; exact absurd (hSleN hsS) hsN
            · intro hgsg; exact absurd (hSleN hgsg) hgsg_notN
        -- M.subgroupOf N is normal in N (since M is normal in G and M ≤ N).
        haveI hMsubN_norm : (M.subgroupOf N).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mpr
            Subgroup.le_normalizer_of_normal
        -- M.subgroupOf N ≠ ⊥ (since M ≠ ⊥ and M ≤ N).
        have hMsubN_ne_bot : M.subgroupOf N ≠ ⊥ := by
          intro heq
          apply hM.2.1
          have hM_eq : M = (M.subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hMleN).symm
          rw [hM_eq, heq, Subgroup.map_bot]
        -- Pick a minimal-normal-in-N subgroup K ≤ M.subgroupOf N.
        obtain ⟨K, hKmin, hKle⟩ :=
          exists_isMinimalNormal_le_of_normal (G := N) (M.subgroupOf N) hMsubN_ne_bot
        have hK_le_socN : K ≤ socle N := isMinimalNormal_le_socle hKmin
        -- K.map N.subtype ≤ M ∩ (socle N).map N.subtype, and ≠ ⊥.
        have hKmap_le_M : K.map N.subtype ≤ M := by
          rintro _ ⟨k, hk, rfl⟩
          have := hKle hk
          rwa [Subgroup.mem_subgroupOf] at this
        have hKmap_le_socMap : K.map N.subtype ≤ (socle N).map N.subtype :=
          Subgroup.map_mono hK_le_socN
        have hKmap_ne_bot : K.map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmin.2.1
          rw [eq_bot_iff]
          intro k hk
          have hmem : (k : G) ∈ K.map N.subtype := ⟨k, hk, rfl⟩
          rw [heq, Subgroup.mem_bot] at hmem
          have : k = 1 := Subtype.ext hmem
          rw [this]; exact Subgroup.one_mem _
        -- M ⊓ ((socle N).map N.subtype) is G-normal, ≤ M, ≠ ⊥.
        haveI hSocLift_normal : ((socle N).map N.subtype).Normal := inferInstance
        haveI hM_inf_norm : (M ⊓ (socle N).map N.subtype).Normal :=
          Subgroup.normal_inf_normal _ _
        have hM_inf_ne_bot : M ⊓ (socle N).map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmap_ne_bot
          rw [eq_bot_iff]
          exact (le_inf hKmap_le_M hKmap_le_socMap).trans heq.le
        have hM_inf_eq_M : M ⊓ (socle N).map N.subtype = M := by
          rcases hM.2.2 _ hM_inf_norm inf_le_left with h | h
          · exact absurd h hM_inf_ne_bot
          · exact h
        have hM_le_SocLift : M ≤ (socle N).map N.subtype := by
          intro m hm
          have hmem : m ∈ M ⊓ (socle N).map N.subtype := by rw [hM_inf_eq_M]; exact hm
          exact hmem.2
        exact hM_le_SocLift.trans hSoc_lift_le_norm

/-- **Isaacs Thm 2.6** (minimal normal が subnormal を正規化).

Subnormal `S ⊴⊴ G` と minimal normal `M` について `M ≤ N_G(S)`.

Isaacs p.46 の証明: `|G|`-induction.
* `S = ⊤` なら `N_G(⊤) = ⊤` で trivial.
* `S ≠ ⊤` なら proper G-正規 `N` で `S ≤ N` を取る.
  - **Case 1** `M ⊓ N = ⊥`: `commute_of_disjoint_normal` で `M` と `N` の元は可換,
    特に `S ≤ N` の元とも可換 ⇒ `M ≤ centralizer S ≤ normalizer S`.
  - **Case 2** `M ⊓ N ≠ ⊥`: minimality で `M ≤ N`. IH を ambient group `↥N` に適用し,
    `socle ↥N` の各 minimal normal が `S.subgroupOf N` を正規化 ⇒ `S` を正規化.
    Characteristic 経由で `(socle ↥N).map N.subtype` は `G` 正規, `M ≤ ↥N` と合わせ
    minimality 適用. -/
theorem isMinimalNormal_le_normalizer_of_isSubnormal [Finite G]
    {S M : Subgroup G} (hS : S.IsSubnormal) (hM : IsMinimalNormal M) :
    M ≤ Subgroup.normalizer (S : Set G) :=
  isMinimalNormal_le_normalizer_aux (Nat.card G) G le_rfl hS hM

/-- 補助補題 (Thm 2.5 の strong induction の generalized core).

任意の有限群 `G` (with `Nat.card G ≤ n`) について, subnormal `S, T : Subgroup G`
の sup `S ⊔ T` も subnormal. -/
private theorem isSubnormal_sup_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S T : Subgroup G}, S.IsSubnormal → T.IsSubnormal →
      (S ⊔ T).IsSubnormal := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hG S T hS hT
    classical
    by_cases hGnontriv : Nontrivial G
    case neg =>
      -- Subsingleton G ⇒ every subgroup = ⊤ ⇒ IsSubnormal.top.
      rw [not_nontrivial_iff_subsingleton] at hGnontriv
      haveI := hGnontriv
      have hST_top : (S ⊔ T : Subgroup G) = ⊤ := by
        refine eq_top_iff.mpr (fun x _ => ?_)
        rw [show x = 1 from Subsingleton.elim x 1]
        exact (S ⊔ T).one_mem
      rw [hST_top]
      exact Subgroup.IsSubnormal.top
    case pos =>
      haveI := hGnontriv
      -- Pick minimal normal M ≤ ⊤.
      have htop_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := by
        intro h
        obtain ⟨x, y, hxy⟩ := hGnontriv
        apply hxy
        have hxbot : x ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top x
        have hybot : y ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top y
        rw [Subgroup.mem_bot] at hxbot hybot
        rw [hxbot, hybot]
      obtain ⟨M, hM, _⟩ :=
        exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) htop_ne_bot
      haveI hMnorm : M.Normal := hM.1
      -- Quotient map f : G →* G ⧸ M.
      let f : G →* G ⧸ M := QuotientGroup.mk' M
      have hSbar : (S.map f).IsSubnormal := hS.map (QuotientGroup.mk'_surjective M)
      have hTbar : (T.map f).IsSubnormal := hT.map (QuotientGroup.mk'_surjective M)
      -- Card bound: |G/M| < |G| ≤ n+1, so |G/M| ≤ n.
      have h1lt_M : 1 < Nat.card M := by
        have h_ne_one : Nat.card M ≠ 1 := by
          intro h1
          apply hM.2.1
          haveI hSub : Subsingleton M := Nat.card_eq_one_iff_unique.mp h1 |>.1
          refine eq_bot_iff.mpr (fun x hx => ?_)
          rw [Subgroup.mem_bot]
          exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : M) 1)
        have h_pos : 0 < Nat.card M := Nat.card_pos
        omega
      have hquot_lt : Nat.card (G ⧸ M) < Nat.card G := by
        have heq : M.index * Nat.card M = Nat.card G := M.index_mul_card
        have hM_pos : 0 < Nat.card M := Nat.card_pos
        have hidx_eq : M.index = Nat.card G / Nat.card M := by
          rw [← heq, Nat.mul_div_cancel _ hM_pos]
        change M.index < Nat.card G
        rw [hidx_eq]
        exact Nat.div_lt_self Nat.card_pos h1lt_M
      have hquot_le : Nat.card (G ⧸ M) ≤ n := by omega
      -- IH on G ⧸ M.
      have hIH : (S.map f ⊔ T.map f).IsSubnormal :=
        ih (G ⧸ M) hquot_le hSbar hTbar
      rw [← Subgroup.map_sup] at hIH
      -- Comap back to G: comap f (map f (S ⊔ T)) = (S ⊔ T) ⊔ ker f = (S ⊔ T) ⊔ M.
      have hcomap_subn : (((S ⊔ T).map f).comap f).IsSubnormal := hIH.comap f
      have hcomap_eq : ((S ⊔ T).map f).comap f = (S ⊔ T) ⊔ M := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      rw [hcomap_eq] at hcomap_subn
      -- Thm 2.6: M ≤ N(S) ⊓ N(T) ≤ N(S ⊔ T).
      have hMS : M ≤ Subgroup.normalizer (S : Set G) :=
        isMinimalNormal_le_normalizer_of_isSubnormal hS hM
      have hMT : M ≤ Subgroup.normalizer (T : Set G) :=
        isMinimalNormal_le_normalizer_of_isSubnormal hT hM
      have hMnormST : M ≤ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
        (le_inf hMS hMT).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup S T)
      -- S ⊔ T ⊴ (S ⊔ T) ⊔ M. Both summands ⊆ N(S ⊔ T).
      have hSupSup_le_norm :
          (S ⊔ T) ⊔ M ≤ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
        sup_le Subgroup.le_normalizer hMnormST
      have hSupNormal : ((S ⊔ T).subgroupOf ((S ⊔ T) ⊔ M)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hSupSup_le_norm
      exact Subgroup.IsSubnormal.step _ _ le_sup_left hcomap_subn hSupNormal

/-- **Isaacs Thm 2.5 Wielandt 結合定理**: 部分正規部分群の sup は部分正規.

有限群 `G` の subnormal `S, T : Subgroup G` について `S ⊔ T` も subnormal.

Isaacs p.46 の証明: `|G|`-induction. minimal normal `M` を取って `G ⧸ M` に IH を
適用 ⇒ `(S ⊔ T) ⊔ M ⊴⊴ G`. Thm 2.6 で `M ≤ N(S ⊔ T)` ⇒ `S ⊔ T ⊴ (S ⊔ T) ⊔ M`.
合わせて `S ⊔ T ⊴⊴ G`. -/
theorem isSubnormal_sup_of_isSubnormal [Finite G] {S T : Subgroup G}
    (hS : S.IsSubnormal) (hT : T.IsSubnormal) : (S ⊔ T).IsSubnormal :=
  isSubnormal_sup_aux (Nat.card G) G le_rfl hS hT

open scoped Pointwise in
/-- **Isaacs Lemma 2.10**: if `H ≤ G` and `H · H^x = G` (as sets) for some `x ∈ G`,
then `H = G`.

`H^x` (Isaacs convention `x⁻¹ H x`) は mathlib `MulAut.conj x⁻¹ • H` に対応.
仮定は **集合** の等式 (積 `HH^x` は一般に部分群ではない).

Proof (Isaacs p.49):
1. `x ∈ HH^x = G` ⇒ `x = u * v` with `u ∈ H`, `v ∈ H^x`.
2. `v ∈ H^x ↔ x v x⁻¹ ∈ H`. `u * v = x` ⇒ `v = u⁻¹ * x` ⇒ `x v x⁻¹ = x u⁻¹ ∈ H`.
   よって `x = (x u⁻¹) * u ∈ H`.
3. `x ∈ H` ⇒ `MulAut.conj x⁻¹ • H = H` (`Subgroup.conj_smul_eq_self_of_mem` 適用).
4. `H · H = H` (`Submonoid.coe_mul_self_eq`) と `HH^x = univ` から `H = univ`. -/
theorem eq_top_of_set_mul_conj_eq_top {H : Subgroup G} (x : G)
    (h : (H : Set G) * (((MulAut.conj x⁻¹) • H : Subgroup G) : Set G) = Set.univ) :
    H = ⊤ := by
  -- Step 1+2: x ∈ H.
  have hx_in_H : x ∈ H := by
    have hx_in_prod : x ∈ (H : Set G) * (((MulAut.conj x⁻¹) • H : Subgroup G) : Set G) := by
      rw [h]; exact Set.mem_univ _
    rcases Set.mem_mul.mp hx_in_prod with ⟨u, hu, v, hv, huv⟩
    -- v ∈ H^x ⇒ x v x⁻¹ ∈ H.
    have hconj_inv : (MulAut.conj x⁻¹ : MulAut G)⁻¹ = MulAut.conj x := by
      rw [← map_inv MulAut.conj, inv_inv]
    rw [SetLike.mem_coe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hconj_inv] at hv
    -- hv : (MulAut.conj x) • v ∈ H. By definition this is x * v * x⁻¹.
    have hxvx : x * v * x⁻¹ ∈ H := hv
    -- hu : u ∈ H, huv : u * v = x ⇒ v = u⁻¹ * x ⇒ x v x⁻¹ = x u⁻¹ ∈ H.
    have hv_eq : v = u⁻¹ * x := by rw [← huv]; group
    rw [hv_eq] at hxvx
    have heq : x * (u⁻¹ * x) * x⁻¹ = x * u⁻¹ := by group
    rw [heq] at hxvx
    -- Now hxvx : x * u⁻¹ ∈ H, hu : u ∈ H ⇒ x = (x * u⁻¹) * u ∈ H.
    have : x = (x * u⁻¹) * u := by group
    rw [this]
    exact H.mul_mem hxvx hu
  -- Step 3: H^x = H (subgroup equality).
  have hHx_eq_H : (MulAut.conj x⁻¹ : MulAut G) • H = H :=
    Subgroup.conj_smul_eq_self_of_mem (H.inv_mem hx_in_H)
  -- Step 4: HH^x = univ + H^x = H ⇒ HH = univ ⇒ H = univ (subgroup closure under mul).
  rw [hHx_eq_H] at h
  -- h : (H : Set G) * (H : Set G) = Set.univ
  refine eq_top_iff.mpr (fun g _ => ?_)
  have hg_in : g ∈ (H : Set G) * (H : Set G) := h ▸ Set.mem_univ g
  rcases Set.mem_mul.mp hg_in with ⟨h1, hh1, h2, hh2, hg⟩
  exact hg ▸ H.mul_mem hh1 hh2

open scoped Pointwise in
/-- **Isaacs Thm 2.9 Wielandt's Zipper Lemma**. 有限群 `G` の部分群 `S` で,
`S` を真に含む任意の真部分群 `H` について `S ⊴⊴ H` であり, かつ `S` 自身は
`G` で部分正規でないとする. このとき `S` を含む `G` の極大部分群は一意.

Isaacs p.49 の証明: `|G:S|` (= `S.index`) についての強induction.
* `S.index = 1` ⇒ `S = ⊤` ⇒ `S ⊴⊴ G` (`IsSubnormal.top`) で仮定矛盾, vacuous.
* induction step: `S` が `G` で正規でない (else `S ⊴⊴ G`, 矛盾) ので
  `N_G(S) < ⊤`, 極大 `M ≥ N_G(S)` を取る. 任意の極大 `K ≥ S` で `K = M` を示す:
  - **Case A** `S ⊴ K`: `K ≤ N_G(S) ≤ M`, `K` 極大 で `K = M`.
  - **Case B** `S ⊴⊴ K` だが `S ⋬ K`: K の subnormal chain で「`S` が正規でなくなる」
    最初の `f i` を Nat.find で取り, x ∈ f i \ N_K(S) を選ぶ. `T := S ⊔ S^x` は
    `T > S`, `T ≤ N_G(S) ≤ M`, `T ≤ K` で, T が IH の hypotheses を満たす
    (Thm 2.5 を使う). IH で T を含む極大は一意 ⇒ M = K. -/
theorem zipper_lemma [Finite G] {S : Subgroup G}
    (hS_proper : ∀ H : Subgroup G, S ≤ H → H ≠ ⊤ → (S.subgroupOf H).IsSubnormal)
    (hS_not_sn : ¬ S.IsSubnormal) :
    ∃ M : Subgroup G, IsCoatom M ∧ S ≤ M ∧
      ∀ K : Subgroup G, IsCoatom K → S ≤ K → K = M := by
  classical
  -- Strong induction on S.index.
  induction hIdx : S.index using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    -- Rule out S.index = 1 first. In finite group, S.index ≥ 1.
    have hS_idx_pos : 0 < S.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rcases Nat.lt_or_ge 1 n with hgt | hle
    swap
    · -- n ≤ 1: since S.index = n > 0, we have n = 1.
      have hn_eq : n = 1 := by
        have hn_pos : 0 < n := hIdx ▸ hS_idx_pos
        omega
      -- S.index = 1 ⇒ S = ⊤ ⇒ S subnormal, contradiction.
      have hS_top : S = ⊤ := Subgroup.index_eq_one.mp (hIdx.trans hn_eq)
      exact absurd (hS_top ▸ Subgroup.IsSubnormal.top) hS_not_sn
    · -- n > 1: induction step.
      -- Step 1: S not normal in G.
      have hS_not_normal : ¬ S.Normal := fun hN => hS_not_sn hN.isSubnormal
      -- N_G(S) < ⊤.
      have hN_lt_top : Subgroup.normalizer (S : Set G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro hN_top
        exact hS_not_normal (Subgroup.normalizer_eq_top_iff.mp hN_top)
      -- Step 2: pick maximal M ≥ N_G(S). Note S ≤ N_G(S).
      obtain ⟨M, hM_coatom, hN_le_M⟩ :=
        (eq_top_or_exists_le_coatom (Subgroup.normalizer (S : Set G))).resolve_left hN_lt_top.ne
      have hS_le_NS : S ≤ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer
      have hS_le_M : S ≤ M := hS_le_NS.trans hN_le_M
      refine ⟨M, hM_coatom, hS_le_M, ?_⟩
      intro K hK_coatom hS_le_K
      -- K is a maximal subgroup containing S; show K = M.
      have hK_ne_top : K ≠ ⊤ := hK_coatom.1
      -- H1 ⇒ S.subgroupOf K is subnormal.
      have hSsubK_sn : (S.subgroupOf K).IsSubnormal := hS_proper K hS_le_K hK_ne_top
      -- Case split: is S normal in K?
      by_cases hSK_normal : (S.subgroupOf K).Normal
      · -- Case A: S ⊴ K. Then K ≤ N_G(S) ≤ M, K coatom ⇒ K = M.
        have hK_le_NS : K ≤ Subgroup.normalizer (S : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_K).mp hSK_normal
        have hK_le_M : K ≤ M := hK_le_NS.trans hN_le_M
        -- K coatom and K ≤ M ≠ ⊤ (M coatom).
        rcases hK_coatom.le_iff.mp hK_le_M with hM_top | hM_eq
        · exact absurd hM_top hM_coatom.1
        · exact hM_eq.symm
      · -- Case B: S subnormal in K but not normal in K. Extract chain.
        obtain ⟨nChain, f, hf_mono, hf_step, hf0, hfN⟩ :=
          hSsubK_sn.exists_chain
        -- f : ℕ → Subgroup ↥K with f 0 = S.subgroupOf K, f nChain = ⊤, chain property.
        -- Find smallest i with S.subgroupOf K NOT normal in f i.
        -- (S.subgroupOf K).subgroupOf (f i) Normal ⇔ f i ≤ normalizer (S.subgroupOf K).
        have hPred_exists : ∃ i, ¬ (((S.subgroupOf K).subgroupOf (f i)).Normal) := by
          refine ⟨nChain, ?_⟩
          intro hN
          apply hSK_normal
          -- hN : (S.subgroupOf K).subgroupOf (f nChain) Normal.
          -- f nChain = ⊤_K, so subgroupOf ⊤_K = identification, giving normality in K.
          rw [hfN] at hN
          -- (S.subgroupOf K).subgroupOf ⊤ Normal ⇒ ⊤ ≤ normalizer (S.subgroupOf K)
          have h1 : (⊤ : Subgroup K) ≤
              Subgroup.normalizer ((S.subgroupOf K) : Set K) :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN
          rw [top_le_iff, Subgroup.normalizer_eq_top_iff] at h1
          exact h1
        -- Smallest such i.
        let m := Nat.find hPred_exists
        have hm_spec : ¬ (((S.subgroupOf K).subgroupOf (f m)).Normal) := Nat.find_spec hPred_exists
        have hm_min : ∀ k < m, ((S.subgroupOf K).subgroupOf (f k)).Normal := by
          intro k hk
          by_contra h
          exact absurd (Nat.find_min hPred_exists hk) (not_not.mpr h)
        -- f 0 = S.subgroupOf K, normal in itself, so m ≥ 1.
        have hm_pos : 0 < m := by
          by_contra h
          push Not at h
          interval_cases m
          apply hm_spec
          rw [hf0]
          -- (S.subgroupOf K).subgroupOf (S.subgroupOf K) = ⊤, hence normal.
          rw [show (S.subgroupOf K).subgroupOf (S.subgroupOf K) = ⊤ from
            Subgroup.subgroupOf_self _]
          exact Subgroup.normal_top
        -- f (m-1) ≤ normalizer (S.subgroupOf K). f m has element not normalizing S.subgroupOf K.
        have hfm1_norm : ((S.subgroupOf K).subgroupOf (f (m - 1))).Normal :=
          hm_min (m - 1) (Nat.sub_lt hm_pos Nat.zero_lt_one)
        -- f (m-1) ≤ N_K(S.subgroupOf K).
        -- Need S.subgroupOf K ≤ f (m-1) first.
        have hS_le_fm1 : S.subgroupOf K ≤ f (m - 1) := by
          rw [← hf0]; exact hf_mono (Nat.zero_le _)
        have hfm1_le_norm : f (m - 1) ≤
            Subgroup.normalizer ((S.subgroupOf K) : Set K) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_fm1).mp hfm1_norm
        -- f (m-1) ≤ f m: take an element of f m not in N_K(S.subgroupOf K).
        have hS_le_fm : S.subgroupOf K ≤ f m := by
          rw [← hf0]; exact hf_mono (Nat.zero_le _)
        have hfm_not_le_norm : ¬ (f m ≤
            Subgroup.normalizer ((S.subgroupOf K) : Set K)) := by
          intro h
          exact hm_spec ((Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_fm).mpr h)
        -- Get x in f m not in N_K(S.subgroupOf K).
        obtain ⟨x, hx_in_fm, hx_not_norm⟩ : ∃ x : K, x ∈ f m ∧
            x ∉ Subgroup.normalizer ((S.subgroupOf K) : Set K) := by
          by_contra h
          push Not at h
          apply hfm_not_le_norm
          intro y hy
          exact h y hy
        -- f (m-1) ⊴ f m by chain property; so x normalizes f (m-1) in f m, i.e.,
        -- (MulAut.conj (x : K)⁻¹) • (f (m-1)) ≤ f (m-1) as subgroups of f m... wait, simpler:
        -- (f (m-1)).subgroupOf (f m) is Normal, so x in f m normalizes (f (m-1)).subgroupOf (f m).
        -- Translate to: x · f (m-1) · x⁻¹ ≤ f (m-1) as subgroup of K (since f (m-1) ≤ f m).
        have hfm1_le_fm : f (m - 1) ≤ f m := by
          have : m - 1 ≤ m := Nat.sub_le _ _
          exact hf_mono this
        -- Use chain property at index m - 1: ((f (m-1)).subgroupOf (f m)).Normal
        have hfm1_norm_in_fm : ((f (m - 1)).subgroupOf (f m)).Normal := by
          have hstep := hf_step (m - 1)
          rwa [Nat.sub_add_cancel hm_pos] at hstep
        have hfm_le_normfm1 : f m ≤ Subgroup.normalizer ((f (m - 1)) : Set K) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hfm1_le_fm).mp hfm1_norm_in_fm
        -- Now translate to G-level. x : K, x.val : G is in K.
        -- We want to construct S^x.
        set xG : G := (x : G)
        have hxG_in_K : xG ∈ K := x.2
        -- Key: x normalizes f (m-1) in K. In particular,
        -- (MulAut.conj x.val⁻¹) • S ≤ image of f (m-1) in G ≤ N_G(S).
        -- Image of f (m-1) in G:
        let J : Subgroup G := (f (m - 1)).map K.subtype
        -- S ≤ J (since S.subgroupOf K ≤ f (m-1), and (S.subgroupOf K).map K.subtype = S).
        have hS_le_J : S ≤ J := by
          rw [show S = (S.subgroupOf K).map K.subtype from
            (Subgroup.map_subgroupOf_eq_of_le hS_le_K).symm]
          exact Subgroup.map_mono hS_le_fm1
        -- J ≤ K.
        have hJ_le_K : J ≤ K := by
          rintro _ ⟨⟨y, hyK⟩, _, rfl⟩
          exact hyK
        -- J ≤ N_G(S) (since (f (m-1)).subgroupOf K ≤ N_K(S.subgroupOf K) lifted to G).
        have hJ_le_NS : J ≤ Subgroup.normalizer (S : Set G) := by
          intro y hy
          rcases hy with ⟨⟨y', hy'K⟩, hy'_in, rfl⟩
          -- y'_in : ⟨y', hy'K⟩ ∈ f (m-1), so it's in N_K(S.subgroupOf K).
          have hy'_norm : (⟨y', hy'K⟩ : K) ∈
              Subgroup.normalizer ((S.subgroupOf K) : Set K) := hfm1_le_norm hy'_in
          rw [Subgroup.mem_normalizer_iff] at hy'_norm ⊢
          intro s
          by_cases hsK : s ∈ K
          · -- s ∈ K: lift to K, apply hy'_norm.
            have h := hy'_norm ⟨s, hsK⟩
            constructor
            · intro hsS
              have h1 : (⟨s, hsK⟩ : K) ∈ S.subgroupOf K := by
                rwa [Subgroup.mem_subgroupOf]
              have h2 := h.mp h1
              rw [Subgroup.mem_subgroupOf] at h2
              -- Coerce computation. y' * s * y'⁻¹ as K-element coerces correctly.
              exact h2
            · intro hys
              have hys_in_K : y' * s * y'⁻¹ ∈ K :=
                K.mul_mem (K.mul_mem hy'K hsK) (K.inv_mem hy'K)
              have h1 : (⟨y' * s * y'⁻¹, hys_in_K⟩ : K) ∈ S.subgroupOf K := by
                rwa [Subgroup.mem_subgroupOf]
              have hcong : (⟨y' * s * y'⁻¹, hys_in_K⟩ : K) =
                  ⟨y', hy'K⟩ * ⟨s, hsK⟩ * ⟨y', hy'K⟩⁻¹ := by
                apply Subtype.ext
                change y' * s * y'⁻¹ =
                  ((⟨y', hy'K⟩ * ⟨s, hsK⟩ * ⟨y', hy'K⟩⁻¹ : K) : G)
                push_cast
                rfl
              rw [hcong] at h1
              have h2 := h.mpr h1
              rwa [Subgroup.mem_subgroupOf] at h2
          · -- s ∉ K: both sides false (since S ≤ K).
            have hys_notK : y' * s * y'⁻¹ ∉ K := by
              intro h
              apply hsK
              have hseq : s = y'⁻¹ * (y' * s * y'⁻¹) * y' := by group
              rw [hseq]
              exact K.mul_mem (K.mul_mem (K.inv_mem hy'K) h) hy'K
            constructor
            · intro hsS; exact absurd (hS_le_K hsS) hsK
            · intro hys; exact absurd (hS_le_K hys) hys_notK
        -- Now construct T = S ⊔ MulAut.conj xG⁻¹ • S.
        set Sx : Subgroup G := (MulAut.conj xG⁻¹ : MulAut G) • S with hSx_def
        set T : Subgroup G := S ⊔ Sx with hT_def
        -- Sx ≤ J ≤ N_G(S): show Sx ≤ J.
        -- xG normalizes J: J = (f(m-1)).map K.subtype. We need
        -- MulAut.conj xG⁻¹ • J ≤ J (since x in K normalizes f(m-1) in K).
        have hJ_normalizes_xG : (MulAut.conj xG : MulAut G) • J ≤ J := by
          rintro - ⟨z, hzJ, rfl⟩
          rcases hzJ with ⟨⟨z', hz'K⟩, hz'_in_fm1, rfl⟩
          have hx_norm_fm1 : x ∈ Subgroup.normalizer ((f (m - 1)) : Set K) :=
            hfm_le_normfm1 hx_in_fm
          have h_conj : x * ⟨z', hz'K⟩ * x⁻¹ ∈ f (m - 1) :=
            ((Subgroup.mem_normalizer_iff.mp hx_norm_fm1) ⟨z', hz'K⟩).mp hz'_in_fm1
          refine ⟨x * ⟨z', hz'K⟩ * x⁻¹, h_conj, ?_⟩
          change ((x * ⟨z', hz'K⟩ * x⁻¹ : K) : G) = MulAut.conj xG z'
          push_cast
          simp [xG]
        -- Also need MulAut.conj xG⁻¹ • J ≤ J (same argument with x⁻¹).
        have hx_inv_in_fm : x⁻¹ ∈ f m := (f m).inv_mem hx_in_fm
        have hJ_normalizes_xG_inv : (MulAut.conj xG⁻¹ : MulAut G) • J ≤ J := by
          rintro - ⟨z, hzJ, rfl⟩
          rcases hzJ with ⟨⟨z', hz'K⟩, hz'_in_fm1, rfl⟩
          have hxinv_norm_fm1 : x⁻¹ ∈ Subgroup.normalizer ((f (m - 1)) : Set K) :=
            hfm_le_normfm1 hx_inv_in_fm
          have h_conj : x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹ ∈ f (m - 1) :=
            ((Subgroup.mem_normalizer_iff.mp hxinv_norm_fm1) ⟨z', hz'K⟩).mp hz'_in_fm1
          refine ⟨x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹, h_conj, ?_⟩
          change ((x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹ : K) : G) = MulAut.conj xG⁻¹ z'
          push_cast
          simp [xG]
        have hSx_le_J : Sx ≤ J := by
          rw [hSx_def]
          calc (MulAut.conj xG⁻¹ : MulAut G) • S
              ≤ (MulAut.conj xG⁻¹ : MulAut G) • J :=
                Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hS_le_J
            _ ≤ J := hJ_normalizes_xG_inv
        have hSx_le_NS : Sx ≤ Subgroup.normalizer (S : Set G) := hSx_le_J.trans hJ_le_NS
        have hSx_le_K : Sx ≤ K := hSx_le_J.trans hJ_le_K
        have hT_le_NS : T ≤ Subgroup.normalizer (S : Set G) :=
          sup_le hS_le_NS hSx_le_NS
        have hT_le_K : T ≤ K := sup_le hS_le_K hSx_le_K
        have hT_le_M : T ≤ M := hT_le_NS.trans hN_le_M
        -- T > S strictly: Sx ⊈ S since xG ∉ N_G(S).
        -- Strategy: if Sx ≤ S, then |Sx| = |S| and Sx = S in finite ⇒ xG⁻¹ ∈ N_G(S) ⇒ xG ∈ N_G(S).
        -- This translates to x ∈ N_K(S.subgroupOf K), contradicting hx_not_norm.
        have hSx_card : Nat.card Sx = Nat.card S :=
          Nat.card_congr (Subgroup.equivSMul (MulAut.conj xG⁻¹) S).toEquiv.symm
        have hSx_not_le_S : ¬ (Sx ≤ S) := by
          intro h
          -- Cardinality forces Sx = S.
          have hSx_eq : Sx = S := Subgroup.eq_of_le_of_card_ge h hSx_card.ge
          -- From Sx = S, we extract xG⁻¹ ∈ N_G(S).
          have hxG_norm_S : xG ∈ Subgroup.normalizer (S : Set G) := by
            -- Sx = S ⇒ xG⁻¹ ∈ N_G(S), hence xG ∈ N_G(S).
            rw [Subgroup.mem_normalizer_iff]
            intro u
            constructor
            · -- u ∈ S → xG * u * xG⁻¹ ∈ S.
              -- xG * u * xG⁻¹ = MulAut.conj xG u; via hSx_eq, MulAut.conj xG • S = S.
              intro huS
              have hsmul_eq : (MulAut.conj xG : MulAut G) • S = S := by
                have h1 : (MulAut.conj xG⁻¹ : MulAut G) • S = S := hSx_eq
                have h2 : (MulAut.conj xG : MulAut G)⁻¹ • S = S := by
                  rw [← map_inv MulAut.conj]; exact h1
                calc (MulAut.conj xG : MulAut G) • S
                    = (MulAut.conj xG : MulAut G) •
                      ((MulAut.conj xG : MulAut G)⁻¹ • S) := by rw [h2]
                  _ = S := by rw [smul_inv_smul]
              have hu_smul : MulAut.conj xG u ∈ (MulAut.conj xG : MulAut G) • S := ⟨u, huS, rfl⟩
              rw [hsmul_eq] at hu_smul
              change xG * u * xG⁻¹ ∈ S
              exact hu_smul
            · intro hxu
              -- have: xG * u * xG⁻¹ ∈ S. Want u ∈ S.
              -- xG * u * xG⁻¹ ∈ S ⇒ MulAut.conj xG u ∈ S.
              -- Apply (MulAut.conj xG⁻¹ • -) and use hSx_eq.
              have h_smul_eq : (MulAut.conj xG⁻¹ : MulAut G) • S = S := hSx_eq
              have : MulAut.conj xG⁻¹ (xG * u * xG⁻¹) ∈ (MulAut.conj xG⁻¹ : MulAut G) • S :=
                ⟨xG * u * xG⁻¹, hxu, rfl⟩
              rw [h_smul_eq] at this
              -- MulAut.conj xG⁻¹ (xG * u * xG⁻¹) = xG⁻¹ * (xG * u * xG⁻¹) * xG = u.
              have hsimp : MulAut.conj xG⁻¹ (xG * u * xG⁻¹) = u := by
                change xG⁻¹ * (xG * u * xG⁻¹) * (xG⁻¹)⁻¹ = u
                group
              rwa [hsimp] at this
          -- Translate to x ∈ N_K(S.subgroupOf K), contradicting hx_not_norm.
          apply hx_not_norm
          rw [Subgroup.mem_normalizer_iff]
          intro a
          have hmem : ∀ b : K, b ∈ S.subgroupOf K ↔ (b : G) ∈ S := fun b => Subgroup.mem_subgroupOf
          rw [hmem a]
          have hcoe : (((x : K) * a * (x : K)⁻¹ : K) : G) = xG * (a : G) * xG⁻¹ := by
            push_cast; rfl
          rw [hmem _, hcoe]
          rw [Subgroup.mem_normalizer_iff] at hxG_norm_S
          exact hxG_norm_S a
        -- T > S strictly: Sx ≤ T, Sx ⊈ S.
        have hS_le_T : S ≤ T := le_sup_left
        have hS_lt_T : S < T := by
          refine lt_of_le_of_ne hS_le_T ?_
          intro hST
          apply hSx_not_le_S
          -- hST : S = T = S ⊔ Sx, so Sx ≤ S ⊔ Sx = S.
          have : Sx ≤ T := le_sup_right
          rw [← hST] at this
          exact this
        -- T.index < S.index.
        haveI : S.FiniteIndex := ⟨by rw [hIdx]; omega⟩
        have hT_idx_lt : T.index < S.index := Subgroup.index_strictAnti hS_lt_T
        -- ¬ T.IsSubnormal:
        -- T ≤ N_G(S) means S.subgroupOf T Normal. If T.IsSubnormal, then S.IsSubnormal via trans.
        have hT_not_sn : ¬ T.IsSubnormal := by
          intro hT_sn
          apply hS_not_sn
          have hS_norm_T : (S.subgroupOf T).Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_T).mpr hT_le_NS
          exact Subgroup.IsSubnormal.trans hS_le_T hS_norm_T.isSubnormal hT_sn
        -- T satisfies hS_proper:
        have hT_proper : ∀ H : Subgroup G, T ≤ H → H ≠ ⊤ → (T.subgroupOf H).IsSubnormal := by
          intro H hTH hH_ne
          -- S ≤ T ≤ H, Sx ≤ T ≤ H.
          have hS_le_H : S ≤ H := hS_le_T.trans hTH
          have hSx_le_H : Sx ≤ H := le_sup_right.trans hTH
          -- (S.subgroupOf H).IsSubnormal by H1.
          have h1 : (S.subgroupOf H).IsSubnormal := hS_proper H hS_le_H hH_ne
          -- (Sx.subgroupOf H).IsSubnormal: apply H1 to MulAut.conj xG⁻¹ • H ≠ ⊤ (containing S).
          have hH_conj_ne_top : (MulAut.conj xG : MulAut G) • H ≠ ⊤ := by
            intro h
            apply hH_ne
            -- (MulAut.conj xG) is a MulAut, so it's a bijection. smul preserves ⊤ iff arg = ⊤.
            have h1 : (MulAut.conj xG : MulAut G) • H = (MulAut.conj xG : MulAut G) • ⊤ := by
              rw [h]
              ext y
              simp
            -- pointwise_smul cancels (it's a MulAut, hence bijection).
            have h2 : H ≤ ⊤ := le_top
            have h3 : ⊤ ≤ H :=
              Subgroup.pointwise_smul_le_pointwise_smul_iff.mp h1.ge
            exact le_antisymm h2 h3
          have hS_le_HConj : S ≤ (MulAut.conj xG : MulAut G) • H := by
            -- S = conj xG • Sx and Sx ≤ H, so S ≤ conj xG • H.
            have hSx_eq : (MulAut.conj xG : MulAut G) • Sx = S := by
              rw [hSx_def, ← smul_assoc]
              change (MulAut.conj xG * MulAut.conj xG⁻¹ : MulAut G) • S = S
              rw [← map_mul, mul_inv_cancel, map_one]
              exact one_smul _ _
            rw [← hSx_eq]
            exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSx_le_H
          have h_sub_subn : (S.subgroupOf ((MulAut.conj xG : MulAut G) • H)).IsSubnormal :=
            hS_proper _ hS_le_HConj hH_conj_ne_top
          -- Transport via iso H ≃* conj xG • H. Under h ↦ xG h xG⁻¹,
          -- Sx.subgroupOf H corresponds to S.subgroupOf (conj xG • H).
          let φ : H →* ((MulAut.conj xG : MulAut G) • H : Subgroup G) :=
            (Subgroup.equivSMul (MulAut.conj xG) H).toMonoidHom
          have hφ_surj : Function.Surjective φ :=
            (Subgroup.equivSMul (MulAut.conj xG) H).surjective
          -- (S.subgroupOf (conj xG • H)).comap φ = Sx.subgroupOf H.
          have hcomap_eq : (S.subgroupOf ((MulAut.conj xG : MulAut G) • H)).comap φ =
              Sx.subgroupOf H := by
            ext ⟨h, hhH⟩
            constructor
            · intro hh
              -- hh : φ ⟨h, hhH⟩ ∈ S.subgroupOf (conj xG • H), i.e., (φ ⟨h, hhH⟩ : G) ∈ S.
              -- φ ⟨h, hhH⟩ has coercion to G = xG * h * xG⁻¹.
              rw [Subgroup.mem_subgroupOf]
              -- Goal: h ∈ Sx = conj xG⁻¹ • S = {xG⁻¹ * s * xG : s ∈ S}.
              -- From xG * h * xG⁻¹ ∈ S, h = xG⁻¹ * (xG * h * xG⁻¹) * xG ∈ Sx.
              rw [Subgroup.mem_comap] at hh
              rw [Subgroup.mem_subgroupOf] at hh
              -- hh : (φ ⟨h, hhH⟩ : G) ∈ S.
              -- φ ⟨h, hhH⟩ = ⟨xG * h * xG⁻¹, _⟩, so (φ ⟨h, hhH⟩ : G) = xG * h * xG⁻¹.
              refine ⟨xG * h * xG⁻¹, hh, ?_⟩
              change xG⁻¹ * (xG * h * xG⁻¹) * (xG⁻¹)⁻¹ = h
              group
            · intro hh
              rw [Subgroup.mem_comap]
              rw [Subgroup.mem_subgroupOf] at hh
              rw [Subgroup.mem_subgroupOf]
              -- hh : h ∈ Sx = conj xG⁻¹ • S. Get s ∈ S with h = xG⁻¹ * s * xG.
              rcases hh with ⟨s, hsS, hhs⟩
              -- φ ⟨h, hhH⟩ as G-element: xG * h * xG⁻¹.
              have hφ_coe : (((φ ⟨h, hhH⟩) :
                  ((MulAut.conj xG : MulAut G) • H : Subgroup G)) : G) = xG * h * xG⁻¹ := rfl
              -- Convert hhs : MulAut.conj xG⁻¹ s = h to xG * h * xG⁻¹ = s.
              have hsh : xG * h * xG⁻¹ = s := by
                -- hhs has form (MulDistribMulAction action).
                -- We unfold: pointwise smul of an element via MulAut is conj.
                -- The membership in MulAut.conj xG⁻¹ • S says ∃ s ∈ S, conj xG⁻¹ s = h.
                -- I.e., xG⁻¹ * s * xG = h.
                have hh_eq : xG⁻¹ * s * xG = h := by
                  have hh_eq' : (MulAut.conj xG⁻¹ : MulAut G) s = h := hhs
                  have h2 : (MulAut.conj xG⁻¹ : MulAut G) s = xG⁻¹ * s * xG := by
                    change xG⁻¹ * s * (xG⁻¹)⁻¹ = xG⁻¹ * s * xG
                    rw [inv_inv]
                  rw [← h2]; exact hh_eq'
                -- s = xG * h * xG⁻¹.
                have : s = xG * h * xG⁻¹ := by rw [← hh_eq]; group
                exact this.symm
              rw [hφ_coe, hsh]; exact hsS
          have h2 : (Sx.subgroupOf H).IsSubnormal := hcomap_eq ▸ h_sub_subn.comap φ
          -- (S.subgroupOf H).IsSubnormal and (Sx.subgroupOf H).IsSubnormal; their sup is subnormal.
          have hsup : ((S.subgroupOf H) ⊔ (Sx.subgroupOf H)).IsSubnormal :=
            isSubnormal_sup_of_isSubnormal h1 h2
          -- (S.subgroupOf H) ⊔ (Sx.subgroupOf H) = (S ⊔ Sx).subgroupOf H = T.subgroupOf H.
          rw [show (S.subgroupOf H) ⊔ (Sx.subgroupOf H) = T.subgroupOf H from
            (Subgroup.subgroupOf_sup hS_le_H hSx_le_H).symm] at hsup
          exact hsup
        -- Apply IH to T.
        obtain ⟨M', hM'_coatom, _, hM'_uniq⟩ :=
          ih T.index (hIdx ▸ hT_idx_lt) hT_proper hT_not_sn rfl
        -- Both M and K are maximal subgroups containing T (M via hT_le_M, K via hT_le_K).
        -- By uniqueness: M = M' and K = M'. So K = M.
        have hM_eq_M' : M = M' := hM'_uniq M hM_coatom hT_le_M
        have hK_eq_M' : K = M' := hM'_uniq K hK_coatom hT_le_K
        rw [hM_eq_M', hK_eq_M']

/-! ### Isaacs Thm 2.8 (permutability ⇒ subnormality) -/

open scoped Pointwise in
/-- `HK = KH` (set equation, permutable) なら `↑(H ⊔ K) = HK` (集合等式). -/
private theorem coe_sup_eq_set_mul_of_set_mul_comm {H K : Subgroup G}
    (hcomm : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) := by
  -- Construct HK as a Subgroup with carrier H * K (set product).
  let HK : Subgroup G := {
    carrier := (H : Set G) * (K : Set G)
    one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
    mul_mem' := by
      rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
      have hbc : b * c ∈ (K : Set G) * (H : Set G) := ⟨b, hb, c, hc, rfl⟩
      rw [← hcomm] at hbc
      obtain ⟨e, he, f, hf, hef⟩ := hbc
      refine ⟨a * e, H.mul_mem ha he, f * d, K.mul_mem hf hd, ?_⟩
      have eq1 : a * e * (f * d) = a * (e * f) * d := by group
      have eq2 : a * (e * f) * d = a * (b * c) * d := congrArg (fun x => a * x * d) hef
      have eq3 : a * (b * c) * d = a * b * (c * d) := by group
      exact eq1.trans (eq2.trans eq3)
    inv_mem' := by
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * (H : Set G) :=
        ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
      rw [← hcomm] at hba
      rw [mul_inv_rev]
      exact hba
  }
  have hHK_eq : HK = H ⊔ K := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    · refine sup_le ?_ ?_
      · intro a ha
        exact ⟨a, ha, 1, K.one_mem, mul_one a⟩
      · intro b hb
        exact ⟨1, H.one_mem, b, hb, one_mul b⟩
  change ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G)
  rw [← hHK_eq]
  rfl

open scoped Pointwise in
/-- Thm 2.8 のメイン induction 補助補題 (|G| ≤ n に generalize). -/
private theorem isSubnormal_of_permutable_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S : Subgroup G},
      (∀ x : G, (S : Set G) * (((MulAut.conj x) • S : Subgroup G) : Set G)
              = (((MulAut.conj x) • S : Subgroup G) : Set G) * (S : Set G)) →
      S.IsSubnormal := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG S _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ S hperm
    by_contra hSn
    -- S < ⊤.
    have hSlt : S < (⊤ : Subgroup G) := by
      refine lt_of_le_of_ne le_top fun hSt => hSn ?_
      rw [hSt]; exact Subgroup.IsSubnormal.top
    -- IH 適用: 真部分群 H ⊇ S で `S.subgroupOf H` は H で部分正規.
    have hS_in_H : ∀ (H : Subgroup G), S ≤ H → H ≠ ⊤ →
        (S.subgroupOf H).IsSubnormal := by
      intro H hSH hHne
      have hHcard : Nat.card H ≤ n := by
        have hHle : Nat.card H ≤ Nat.card G := H.card_le_card_group
        have hHne_card : Nat.card H ≠ Nat.card G := fun heq =>
          hHne (Subgroup.eq_top_of_card_eq H heq)
        omega
      refine ih H hHcard ?_
      intro y
      -- Permutability transfer G → ↥H via Subgroup.conj_smul_subgroupOf.
      rw [Subgroup.conj_smul_subgroupOf hSH]
      -- Lift to G via H.subtype injective image, then apply G-permutability.
      have hSy_le_H : ((MulAut.conj (y : G)) • S : Subgroup G) ≤ H :=
        Subgroup.conj_smul_le_of_le hSH y
      apply H.subtype_injective.image_injective
      simp only [Set.image_mul]
      have hS_im : H.subtype '' ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) = (S : Set G) := by
        rw [show H.subtype '' ((S.subgroupOf H : Subgroup ↥H) : Set ↥H)
              = (((S.subgroupOf H).map H.subtype : Subgroup G) : Set G)
            from (Subgroup.coe_map _ _).symm,
            Subgroup.map_subgroupOf_eq_of_le hSH]
      have hSy_im : H.subtype '' ((((MulAut.conj (y : G)) • S : Subgroup G).subgroupOf H :
            Subgroup ↥H) : Set ↥H)
          = (((MulAut.conj (y : G)) • S : Subgroup G) : Set G) := by
        rw [show H.subtype '' ((((MulAut.conj (y : G)) • S : Subgroup G).subgroupOf H :
              Subgroup ↥H) : Set ↥H)
              = (((((MulAut.conj (y : G)) • S : Subgroup G).subgroupOf H).map H.subtype :
                  Subgroup G) : Set G)
            from (Subgroup.coe_map _ _).symm,
            Subgroup.map_subgroupOf_eq_of_le hSy_le_H]
      rw [hS_im, hSy_im]
      exact hperm (y : G)
    -- Zipper Lemma で `S` を含む極大部分群 `M` の一意性.
    obtain ⟨M, hMcoatom, hSM, hMuniq⟩ := zipper_lemma hS_in_H hSn
    -- 各 x : G で `MulAut.conj x • S ≤ M`.
    have hSx_le_M : ∀ x : G, ((MulAut.conj x) • S : Subgroup G) ≤ M := by
      intro x
      -- `S ⊔ S^x ≠ ⊤`: 集合等式から Lemma 2.10 で `S = ⊤` を排除.
      have hSup_lt : (S ⊔ ((MulAut.conj x) • S : Subgroup G) : Subgroup G) ≠ ⊤ := by
        intro hSup_top
        have hHK_eq : ((S ⊔ ((MulAut.conj x) • S : Subgroup G) : Subgroup G) : Set G)
            = (S : Set G) * (((MulAut.conj x) • S : Subgroup G) : Set G) :=
          coe_sup_eq_set_mul_of_set_mul_comm (hperm x)
        have huniv : (S : Set G) * (((MulAut.conj x) • S : Subgroup G) : Set G) = Set.univ := by
          rw [← hHK_eq, hSup_top]
          rfl
        have hS_top : S = ⊤ :=
          eq_top_of_set_mul_conj_eq_top x⁻¹ (by rw [inv_inv]; exact huniv)
        exact hSlt.ne hS_top
      -- `S ⊔ S^x ≤ M` (M は S を含む唯一の極大).
      obtain ⟨K, hKcoatom, hKle⟩ :=
        (eq_top_or_exists_le_coatom (S ⊔ ((MulAut.conj x) • S : Subgroup G) :
          Subgroup G)).resolve_left hSup_lt
      have hSK : S ≤ K := le_sup_left.trans hKle
      have hKM : K = M := hMuniq K hKcoatom hSK
      exact (le_sup_right.trans hKle).trans hKM.le
    -- 正規閉包 `S^G ≤ M`.
    have hNS_le_M : Subgroup.normalClosure (S : Set G) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro y hy
      rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨a, haS, hConj⟩
      rcases hConj with ⟨c, hc⟩
      apply hSx_le_M (c : G)
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
      -- 目標: `(MulAut.conj (c : G)⁻¹) y ∈ S`, つまり `(c : G)⁻¹ * y * (c : G) ∈ S`.
      change ((c : G)⁻¹) * y * ((c : G)⁻¹)⁻¹ ∈ S
      rw [inv_inv]
      -- hc : SemiconjBy (c : G) a y, i.e., (c : G) * a = y * (c : G).
      have hc_eq : (c : G) * a = y * (c : G) := hc
      have ha_eq : ((c : G)⁻¹) * y * ((c : G)) = a := by
        rw [mul_assoc, ← hc_eq]
        group
      rw [ha_eq]
      exact haS
    -- 正規閉包 < ⊤ (since ≤ M coatom).
    have hNS_lt : Subgroup.normalClosure (S : Set G) ≠ ⊤ := fun hNStop =>
      hMcoatom.1 (le_top.antisymm (hNStop.symm.le.trans hNS_le_M))
    -- IH を `normalClosure S` に適用.
    have hSle_NS : S ≤ Subgroup.normalClosure (S : Set G) :=
      Subgroup.le_normalClosure
    have hS_sn_in_NS : (S.subgroupOf (Subgroup.normalClosure (S : Set G))).IsSubnormal :=
      hS_in_H _ hSle_NS hNS_lt
    have hNS_sn : (Subgroup.normalClosure (S : Set G)).IsSubnormal :=
      Subgroup.Normal.isSubnormal inferInstance
    exact hSn (Subgroup.IsSubnormal.trans hSle_NS hS_sn_in_NS hNS_sn)

open scoped Pointwise in
/-- **Isaacs Thm 2.8** (permutability ⇒ subnormality). 有限群 `G` の部分群 `S` で,
全ての共役 `S^x = MulAut.conj x • S` について `S · S^x = S^x · S` (集合等式) ならば,
`S` は `G` で部分正規.

Isaacs p.49 の証明: `|G|`-induction. `S ⊴⊴ G` でないと仮定して矛盾.
1. IH: 真部分群 `H ⊇ S` で `S` は `H` で部分正規 (G → ↥H の permutability transfer).
2. Zipper Lemma (Thm 2.9) で `S` を含む極大 `M` 一意.
3. 任意 `x` で `S ⊔ S^x` は ≠ ⊤ (Lemma 2.10) で `S ⊆ S ⊔ S^x ⊆ M`, よって `S^x ⊆ M`.
4. 正規閉包 `S^G ⊆ M < ⊤`. IH で `S` は `S^G` で部分正規, `S^G ⊴ G` で `S` は `G` で部分正規, 矛盾. -/
theorem isSubnormal_of_permutable_with_conjugates [Finite G] {S : Subgroup G}
    (hperm : ∀ x : G, (S : Set G) * (((MulAut.conj x) • S : Subgroup G) : Set G)
                    = (((MulAut.conj x) • S : Subgroup G) : Set G) * (S : Set G)) :
    S.IsSubnormal :=
  isSubnormal_of_permutable_aux (Nat.card G) G le_rfl hperm

/-! ### Isaacs Thm 2.11 (Wielandt abelian-in-F(G)) -/

open scoped Pointwise in
/-- **古典的計数公式** `|H · K| · |H ∩ K| = |H| · |K|` (group counting formula).
有限群 `G` の部分群 `H, K` の **集合積** の cardinality と intersection の cardinality
が, `H`, `K` の cardinality の積に等しい. mathlib 未収載なので, ここで一度示しておく.

証明: H を G/K (左 coset 集合) に左乗法で作用させ, `(1 : G ⧸ K)` の軌道が
`(H : Set G).image (↑ : G → G ⧸ K)`, 安定化群が `K.subgroupOf H` (≃ `H ⊓ K`).
orbit-stabilizer + `Subgroup.card_mul_eq_card_subgroup_mul_card_quotient` で合成.

Thm 2.11 (Wielandt) と Cor 2.19 で `H = K = A` (またはその共役) の形で使う. -/
private lemma card_set_mul_card_inf {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) :
    Nat.card ((H : Set G) * (K : Set G)) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  classical
  have h1 : Nat.card ((H : Set G) * (K : Set G)) =
      Nat.card ↥K * Nat.card ((H : Set G).image ((↑) : G → G ⧸ K)) :=
    Subgroup.card_mul_eq_card_subgroup_mul_card_quotient K (H : Set G)
  have h_orbit_eq : (MulAction.orbit (↥H) (((1 : G) : G ⧸ K))) =
      (H : Set G).image ((↑) : G → G ⧸ K) := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨(h : G), h.2, ?_⟩
      change ((h : G) : G ⧸ K) = (((h : G) : G) * (1 : G) : G ⧸ K)
      rw [mul_one]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, by
        change ((⟨g, hg⟩ : ↥H).val * (1 : G) : G ⧸ K) = ((g : G) : G ⧸ K)
        rw [mul_one]⟩
  have h_stab_eq : MulAction.stabilizer ↥H (((1 : G) : G ⧸ K)) = K.subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hsmul
      have hraw : (((h : G) : G) * (1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := hsmul
      rw [mul_one] at hraw
      have := QuotientGroup.eq.mp hraw
      simpa using this
    · intro hh
      change (((h : G) : G) * (1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K)
      rw [mul_one]
      apply QuotientGroup.eq.mpr
      simpa using hh
  have h_orbstab : Nat.card (MulAction.orbit ↥H (((1 : G) : G ⧸ K))) *
      Nat.card (MulAction.stabilizer ↥H (((1 : G) : G ⧸ K))) = Nat.card ↥H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥H _)
  have h_subgrpof_card : Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [show K.subgroupOf H = (H ⊓ K).subgroupOf H from
      (Subgroup.inf_subgroupOf_left K H).symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h_orbit_eq, h_stab_eq, h_subgrpof_card] at h_orbstab
  rw [h1, mul_assoc, h_orbstab, mul_comm]

open scoped Pointwise in
/-- **Isaacs Thm 2.11** (Wielandt abelian-in-F(G)) の `|G|`-induction 補助補題. -/
private theorem subset_fitting_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {A : Subgroup G},
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ H : Subgroup G, A ≤ H →
        ((A.subgroupOf H).index) ^ 2 ≤ (Subgroup.center ↥H).index) →
      A ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hcard A _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ hGcard A hAab h
    classical
    -- A is nilpotent (abelian).
    have hA_center_top : Subgroup.center ↥A = ⊤ := by
      ext ⟨x, hx⟩
      refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
      rw [Subgroup.mem_center_iff]
      intro ⟨g, hg⟩
      exact Subtype.ext (hAab g hg x hx)
    haveI hA_nilp : Group.IsNilpotent ↥A := ⟨1, by
      rw [upperCentralSeries_one]; exact hA_center_top⟩
    -- Case split: A subnormal in G.
    by_cases hA_sn : A.IsSubnormal
    · exact (le_fitting_iff_isNilpotent_and_isSubnormal A).mpr ⟨hA_nilp, hA_sn⟩
    -- Case: A not subnormal. Derive contradiction.
    exfalso
    -- IH gives `A.subgroupOf K` subnormal in K for every proper K ⊇ A.
    have hAK_sn : ∀ K : Subgroup G, A ≤ K → K ≠ ⊤ → (A.subgroupOf K).IsSubnormal := by
      intro K hAK hKne
      haveI : Finite K := inferInstance
      have hKcard : Nat.card K ≤ n := by
        have hKlt_card : Nat.card K < Nat.card G := by
          have hKlag := K.card_mul_index
          have h1 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
          have h2 : K.index ≠ 1 := fun he => hKne (Subgroup.index_eq_one.mp he)
          have hKidx : K.index ≥ 2 := by omega
          have hKpos : 0 < Nat.card K := Nat.card_pos
          nlinarith
        omega
      -- Inherited abelianness of A.subgroupOf K.
      have hAK_ab : ∀ a ∈ A.subgroupOf K, ∀ b ∈ A.subgroupOf K, a * b = b * a := by
        intro a ha b hb
        rw [Subgroup.mem_subgroupOf] at ha hb
        exact Subtype.ext (hAab _ ha _ hb)
      -- Inherited index hypothesis: for H' ⊇ A.subgroupOf K in K, transfer h on H'.map K.subtype.
      have hAK_h : ∀ H' : Subgroup ↥K, A.subgroupOf K ≤ H' →
          (((A.subgroupOf K).subgroupOf H').index) ^ 2 ≤ (Subgroup.center ↥H').index := by
        intro H' hAH'
        set H : Subgroup G := H'.map K.subtype with hH_def
        have hAH : A ≤ H := by
          intro a ha
          have haK : a ∈ K := hAK ha
          exact ⟨⟨a, haK⟩, hAH' ((Subgroup.mem_subgroupOf).mpr ha), rfl⟩
        have hkey := h H hAH
        -- Iso φ : H' ≃* H (= H'.map K.subtype).
        set φ : ↥H' ≃* ↥H :=
          Subgroup.equivMapOfInjective H' K.subtype K.subtype_injective with hφ_def
        have hφ_surj : Function.Surjective (φ.toMonoidHom) := φ.surjective
        -- Subgroup correspondence: (A.subgroupOf H).comap φ.toMonoidHom = (A.subgroupOf K).subgroupOf H'.
        have h_S_eq : (A.subgroupOf H).comap φ.toMonoidHom =
            (A.subgroupOf K).subgroupOf H' := by
          ext x
          rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
              Subgroup.mem_subgroupOf]
          rfl
        -- Index transfer for A.
        have h_idx_S : ((A.subgroupOf K).subgroupOf H').index =
            (A.subgroupOf H).index := by
          rw [← h_S_eq]
          exact (A.subgroupOf H).index_comap_of_surjective hφ_surj
        -- Center correspondence via iso.
        have h_C_eq : (Subgroup.center ↥H).comap φ.toMonoidHom = Subgroup.center ↥H' := by
          ext x
          rw [Subgroup.mem_comap, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
          constructor
          · intro hx y
            apply φ.injective
            show φ.toMonoidHom (y * x) = φ.toMonoidHom (x * y)
            rw [map_mul, map_mul]
            exact hx (φ.toMonoidHom y)
          · intro hx z
            obtain ⟨y, hy⟩ := hφ_surj z
            calc z * φ.toMonoidHom x = φ.toMonoidHom y * φ.toMonoidHom x := by rw [← hy]
              _ = φ.toMonoidHom (y * x) := (map_mul _ _ _).symm
              _ = φ.toMonoidHom (x * y) := by rw [hx y]
              _ = φ.toMonoidHom x * φ.toMonoidHom y := map_mul _ _ _
              _ = φ.toMonoidHom x * z := by rw [hy]
        have h_idx_C : (Subgroup.center ↥H').index = (Subgroup.center ↥H).index := by
          rw [← h_C_eq]
          exact (Subgroup.center ↥H).index_comap_of_surjective hφ_surj
        rw [h_idx_S, h_idx_C]
        exact hkey
      have hAK_le_F : A.subgroupOf K ≤ fitting ↥K := ih ↥K hKcard hAK_ab hAK_h
      -- F(K) nilpotent (Cor 1.28(a) instance), A.subgroupOf K ≤ F(K) subnormal in F(K).
      have hAK_in_FK : ((A.subgroupOf K).subgroupOf (fitting ↥K)).IsSubnormal :=
        isSubnormal_of_isNilpotent_finite _
      have hFK_sn : (fitting ↥K).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
      exact Subgroup.IsSubnormal.trans hAK_le_F hAK_in_FK hFK_sn
    -- Zipper Lemma.
    obtain ⟨M, hMcoatom, hAM, hMuniq⟩ := zipper_lemma hAK_sn hA_sn
    -- A ≠ ⊤ (else A ⊴⊴ G via top).
    have h_A_ne_top : A ≠ ⊤ := by
      intro hAtop
      apply hMcoatom.1
      exact le_top.antisymm (hAtop ▸ hAM)
    -- Show ∃ g, ⟨A, (MulAut.conj g) • A⟩ = ⊤.
    have h_exists_g : ∃ g : G, A ⊔ ((MulAut.conj g) • A : Subgroup G) = ⊤ := by
      by_contra h_all_proper
      push_neg at h_all_proper
      -- ∀ g, A ⊔ A^g < ⊤, hence ≤ some maximal = M.
      have hAg_le_M : ∀ g : G, ((MulAut.conj g) • A : Subgroup G) ≤ M := by
        intro g
        have hne : A ⊔ ((MulAut.conj g) • A : Subgroup G) ≠ ⊤ := h_all_proper g
        obtain ⟨K, hKcoatom, hKle⟩ :=
          (eq_top_or_exists_le_coatom (A ⊔ ((MulAut.conj g) • A : Subgroup G))).resolve_left hne
        have hAK : A ≤ K := le_sup_left.trans hKle
        have hKM : K = M := hMuniq K hKcoatom hAK
        exact (le_sup_right.trans hKle).trans hKM.le
      -- A^G (normal closure) ≤ M.
      have hNH_le_M : Subgroup.normalClosure (A : Set G) ≤ M := by
        rw [Subgroup.normalClosure, Subgroup.closure_le]
        intro y hy
        rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨a, haA, hConj⟩
        rcases hConj with ⟨c, hc⟩
        apply hAg_le_M (c : G)
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
        change ((c : G)⁻¹) * y * ((c : G)⁻¹)⁻¹ ∈ A
        rw [inv_inv]
        have hc_eq : (c : G) * a = y * (c : G) := hc
        have ha_eq : ((c : G)⁻¹) * y * ((c : G)) = a := by
          rw [mul_assoc, ← hc_eq]
          group
        rw [ha_eq]; exact haA
      have hNH_lt : Subgroup.normalClosure (A : Set G) ≠ ⊤ := fun hNHtop =>
        hMcoatom.1 (le_top.antisymm (hNHtop.symm.le.trans hNH_le_M))
      -- A ⊴⊴ A^G ⊴ G ⇒ A ⊴⊴ G, contradiction.
      have hA_le_NH : A ≤ Subgroup.normalClosure (A : Set G) := Subgroup.le_normalClosure
      have hA_sn_NH : (A.subgroupOf (Subgroup.normalClosure (A : Set G))).IsSubnormal :=
        hAK_sn _ hA_le_NH hNH_lt
      have hNH_normal_sn : (Subgroup.normalClosure (A : Set G)).IsSubnormal :=
        Subgroup.Normal.isSubnormal inferInstance
      exact hA_sn (Subgroup.IsSubnormal.trans hA_le_NH hA_sn_NH hNH_normal_sn)
    obtain ⟨g, hsup_top⟩ := h_exists_g
    -- Helper: A^g is abelian. For b₁, b₂ ∈ A^g, write back via g⁻¹.
    have hAg_ab : ∀ b₁ ∈ ((MulAut.conj g) • A : Subgroup G),
        ∀ b₂ ∈ ((MulAut.conj g) • A : Subgroup G), b₁ * b₂ = b₂ * b₁ := by
      intro b₁ hb₁ b₂ hb₂
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def] at hb₁ hb₂
      have hb₁' : g⁻¹ * b₁ * g ∈ A := by
        have : g⁻¹ * b₁ * (g⁻¹)⁻¹ ∈ A := hb₁
        rwa [inv_inv] at this
      have hb₂' : g⁻¹ * b₂ * g ∈ A := by
        have : g⁻¹ * b₂ * (g⁻¹)⁻¹ ∈ A := hb₂
        rwa [inv_inv] at this
      have habelian := hAab _ hb₁' _ hb₂'
      -- (g⁻¹ b₁ g)(g⁻¹ b₂ g) = g⁻¹ (b₁ b₂) g, similarly for swap. Cancel.
      have hs1 : (g⁻¹ * b₁ * g) * (g⁻¹ * b₂ * g) = g⁻¹ * (b₁ * b₂) * g := by group
      have hs2 : (g⁻¹ * b₂ * g) * (g⁻¹ * b₁ * g) = g⁻¹ * (b₂ * b₁) * g := by group
      rw [hs1, hs2] at habelian
      -- conjugate both sides by g to cancel.
      have := congrArg (fun z => g * z * g⁻¹) habelian
      simp only at this
      calc b₁ * b₂ = g * (g⁻¹ * (b₁ * b₂) * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * (b₂ * b₁) * g) * g⁻¹ := this
        _ = b₂ * b₁ := by group
    -- A ⊓ A^g ⊆ Z(G): For c ∈ A ⊓ A^g, show centralizer contains both A and A^g, hence ⊤.
    have h_inf_center : (A ⊓ ((MulAut.conj g) • A : Subgroup G) : Subgroup G) ≤
        Subgroup.center G := by
      intro c hc
      rw [Subgroup.mem_inf] at hc
      obtain ⟨hc_A, hc_Ag⟩ := hc
      rw [Subgroup.mem_center_iff]
      intro x
      -- Show centralizer of {c} contains A and A^g, hence ⊤ ≤ centralizer.
      have h_central_A : A ≤ Subgroup.centralizer ({c} : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hAab a ha c hc_A).symm
      have h_central_Ag : ((MulAut.conj g) • A : Subgroup G) ≤
          Subgroup.centralizer ({c} : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hAg_ab b hb c hc_Ag).symm
      have h_sup_le : (A ⊔ ((MulAut.conj g) • A : Subgroup G) : Subgroup G) ≤
          Subgroup.centralizer ({c} : Set G) := sup_le h_central_A h_central_Ag
      have h_central_top : Subgroup.centralizer ({c} : Set G) = ⊤ :=
        top_le_iff.mp (hsup_top ▸ h_sup_le)
      have hx_central : x ∈ Subgroup.centralizer ({c} : Set G) := by
        rw [h_central_top]; exact Subgroup.mem_top x
      rw [Subgroup.mem_centralizer_iff] at hx_central
      exact (hx_central c (Set.mem_singleton _)).symm
    -- Counting: |A·A^g| · |A⊓A^g| = |A|² (via card_set_mul_card_inf).
    have h_count_eq : Nat.card ((A : Set G) *
        (((MulAut.conj g) • A : Subgroup G) : Set G)) *
        Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) =
        Nat.card ↥A * Nat.card ↥((MulAut.conj g) • A : Subgroup G) :=
      card_set_mul_card_inf A ((MulAut.conj g) • A)
    have h_conj_card : Nat.card ↥((MulAut.conj g) • A : Subgroup G) = Nat.card ↥A := by
      rw [Subgroup.pointwise_smul_def]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))
    rw [h_conj_card] at h_count_eq
    -- |A·A^g| < |G| (Lemma 2.10 対偶).
    have h_set_mul_lt : Nat.card ((A : Set G) *
        (((MulAut.conj g) • A : Subgroup G) : Set G)) < Nat.card G := by
      have h_subset : (A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G) ⊆ Set.univ := Set.subset_univ _
      have h_set_ne_univ : (A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G) ≠ Set.univ := by
        intro h_univ
        apply h_A_ne_top
        apply eq_top_of_set_mul_conj_eq_top g⁻¹
        convert h_univ using 2
        rw [inv_inv]
      -- |set| ≤ |G|, and |set| ≠ |G| (else set = univ).
      have h_card_le : Nat.card ((A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G)) ≤ Nat.card G := by
        rw [← Nat.card_univ (α := G)]
        refine Nat.card_le_card_of_injective (fun x => ⟨x.val, Set.mem_univ _⟩) ?_
        intro x y hxy
        exact Subtype.ext (Subtype.mk.injEq _ _ _ _ |>.mp hxy)
      rcases lt_or_eq_of_le h_card_le with hlt | heq
      · exact hlt
      · exfalso
        apply h_set_ne_univ
        apply Set.eq_of_subset_of_ncard_le h_subset _ Set.finite_univ
        rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
        exact le_of_eq heq.symm
    -- |A⊓A^g| ≤ |Z(G)|.
    have h_inf_le_center_card : Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) ≤
        Nat.card ↥(Subgroup.center G) :=
      Subgroup.card_le_of_le h_inf_center
    -- Counting: derive |G| · |Z(G)| > |A|² .
    have h_card_inf_pos : 0 < Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) := Nat.card_pos
    have h_card_A_pos : 0 < Nat.card ↥A := Nat.card_pos
    have h_card_G_pos : 0 < Nat.card G := Nat.card_pos
    have h_count_lt : Nat.card G * Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) >
        Nat.card ↥A * Nat.card ↥A := by
      have h1 : Nat.card ((A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G)) *
          Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) <
          Nat.card G * Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) :=
        (Nat.mul_lt_mul_right h_card_inf_pos).mpr h_set_mul_lt
      omega
    have h_G_center_gt : Nat.card G * Nat.card ↥(Subgroup.center G) >
        Nat.card ↥A * Nat.card ↥A := by
      calc Nat.card G * Nat.card ↥(Subgroup.center G)
          ≥ Nat.card G * Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) :=
            Nat.mul_le_mul_left _ h_inf_le_center_card
        _ > Nat.card ↥A * Nat.card ↥A := h_count_lt
    -- Apply h at H = ⊤: convert to A.index^2 ≤ (center G).index.
    have h_at_top := h ⊤ le_top
    -- h_at_top : (A.subgroupOf ⊤).index ^ 2 ≤ (Subgroup.center ↥(⊤ : Subgroup G)).index
    -- Conversion 1: (A.subgroupOf ⊤).index = A.index.
    have h_idx_A : (A.subgroupOf ⊤).index = A.index := A.relIndex_top_right
    -- Conversion 2: (center ↥⊤).index = (center G).index, via topEquiv.
    have h_topEquiv_surj : Function.Surjective
        ((Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).toMonoidHom) :=
      (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).surjective
    have h_idx_C : (Subgroup.center ↥(⊤ : Subgroup G)).index = (Subgroup.center G).index := by
      have hcenter_eq : (Subgroup.center G).comap
          (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).toMonoidHom =
          Subgroup.center ↥(⊤ : Subgroup G) := by
        ext x
        rw [Subgroup.mem_comap, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
        constructor
        · intro hx y
          apply Subgroup.topEquiv.injective
          show Subgroup.topEquiv.toMonoidHom (y * x) = Subgroup.topEquiv.toMonoidHom (x * y)
          rw [map_mul, map_mul]
          exact hx (Subgroup.topEquiv.toMonoidHom y)
        · intro hx z
          obtain ⟨y, hy⟩ := h_topEquiv_surj z
          calc z * Subgroup.topEquiv.toMonoidHom x
              = Subgroup.topEquiv.toMonoidHom y * Subgroup.topEquiv.toMonoidHom x := by rw [← hy]
            _ = Subgroup.topEquiv.toMonoidHom (y * x) := (map_mul _ _ _).symm
            _ = Subgroup.topEquiv.toMonoidHom (x * y) := by rw [hx y]
            _ = Subgroup.topEquiv.toMonoidHom x * Subgroup.topEquiv.toMonoidHom y := map_mul _ _ _
            _ = Subgroup.topEquiv.toMonoidHom x * z := by rw [hy]
      rw [← hcenter_eq]
      exact (Subgroup.center G).index_comap_of_surjective h_topEquiv_surj
    rw [h_idx_A, h_idx_C] at h_at_top
    -- Numerical derivation: from h_at_top + h_G_center_gt, contradiction.
    -- h_at_top : A.index ^ 2 ≤ (Subgroup.center G).index
    -- hA_lag : A.index * |A| = |G|
    -- hC_lag : (Subgroup.center G).index * |Z(G)| = |G|
    -- h_G_center_gt : |G| * |Z(G)| > |A| * |A|
    -- Derivation: |G|^2 * |Z(G)| = A.index^2 * |A|^2 * |Z(G)| ≤ (center G).index * |A|^2 * |Z(G)|
    --   = ((center G).index * |Z(G)|) * |A|^2 = |G| * |A|^2.
    -- So |G|^2 * |Z(G)| ≤ |G| * |A|^2, cancel |G|: |G| * |Z(G)| ≤ |A|^2.
    -- Contradicts h_G_center_gt.
    have hA_lag : A.index * Nat.card ↥A = Nat.card G := A.index_mul_card
    have hC_lag : (Subgroup.center G).index * Nat.card ↥(Subgroup.center G) = Nat.card G :=
      (Subgroup.center G).index_mul_card
    -- |G|^2 = A.index^2 * |A|^2.
    have hGG_eq : Nat.card G * Nat.card G =
        A.index ^ 2 * (Nat.card ↥A * Nat.card ↥A) := by
      have h := hA_lag
      calc Nat.card G * Nat.card G
          = (A.index * Nat.card ↥A) * (A.index * Nat.card ↥A) := by rw [h]
        _ = A.index ^ 2 * (Nat.card ↥A * Nat.card ↥A) := by ring
    -- Step: A.index^2 * |A|^2 * |Z(G)| ≤ (center G).index * |A|^2 * |Z(G)| = |G| * |A|^2.
    have h_step : Nat.card G * Nat.card G * Nat.card ↥(Subgroup.center G) ≤
        Nat.card G * (Nat.card ↥A * Nat.card ↥A) := by
      calc Nat.card G * Nat.card G * Nat.card ↥(Subgroup.center G)
          = A.index ^ 2 * (Nat.card ↥A * Nat.card ↥A) * Nat.card ↥(Subgroup.center G) := by
            rw [hGG_eq]
        _ ≤ (Subgroup.center G).index * (Nat.card ↥A * Nat.card ↥A) *
              Nat.card ↥(Subgroup.center G) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h_at_top)
        _ = ((Subgroup.center G).index * Nat.card ↥(Subgroup.center G)) *
              (Nat.card ↥A * Nat.card ↥A) := by ring
        _ = Nat.card G * (Nat.card ↥A * Nat.card ↥A) := by rw [hC_lag]
    -- Cancel |G| > 0.
    have h_GZ_le : Nat.card G * Nat.card ↥(Subgroup.center G) ≤
        Nat.card ↥A * Nat.card ↥A := by
      have h_pos := Nat.card_pos (α := G)
      have h_eq : Nat.card G * (Nat.card G * Nat.card ↥(Subgroup.center G)) ≤
          Nat.card G * (Nat.card ↥A * Nat.card ↥A) := by
        calc Nat.card G * (Nat.card G * Nat.card ↥(Subgroup.center G))
            = Nat.card G * Nat.card G * Nat.card ↥(Subgroup.center G) := by ring
          _ ≤ Nat.card G * (Nat.card ↥A * Nat.card ↥A) := h_step
      exact Nat.le_of_mul_le_mul_left h_eq h_pos
    -- Contradiction.
    omega

/-- **Isaacs Thm 2.11** (Wielandt abelian-in-F(G)). 有限群 `G` の abelian 部分群 `A`
で, 全ての `H ⊇ A` について `|H:A|² ≤ |H:Z(H)|` ならば `A ≤ F(G)`.

書籍 p.50 の証明 (`|G|`-induction; cf. Wielandt 1958):
1. **IH**: 任意の真部分群 `H ⊋ A` で `A ≤ F(H)` ⇒ `A ⊴⊴ H` (Thm 2.2 経由).
2. **Zipper Lemma (2.9)** で, `A` が `G` で部分正規でないなら `A` を含む極大 `M` が一意.
3. ある `g ∈ G` で `⟨A, A^g⟩ = G`: 全 `g` で `⟨A, A^g⟩ < G` なら `A^g ⊆ M` 故 `A^G ⊆ M < G`,
   `A ⊴ A^G ⊴ G` で `A ⊴⊴ G`, 矛盾.
4. `A, A^g` abelian で `⟨A, A^g⟩ = G` ⇒ `A ⊓ A^g ⊆ Z(G)`.
5. Lemma 2.10 で `|A · A^g| < |G|`. 計数 `|A·A^g| = |A|²/|A⊓A^g| ≥ |A|²/|Z(G)|`
   で `|G:A|² > |G:Z(G)|`, 仮定 (`H = G`) に矛盾. -/
theorem subset_fitting_of_index_sq_le_index_center [Finite G] {A : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h : ∀ H : Subgroup G, A ≤ H →
      ((A.subgroupOf H).index) ^ 2 ≤ (Subgroup.center ↥H).index) :
    A ≤ fitting G :=
  subset_fitting_aux (Nat.card G) G le_rfl hAab h

end -- 2A

section /- 2B: Baer's theorem (pp. 55-58) -/

variable {G : Type*} [Group G]

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** — 順方向: `H ≤ F(G)` ⇒ ∀x, `⟨H, H^x⟩` 冪零.

`H, H^x ⊆ F(G)` (F(G) ⊴ G で `H^x ⊆ F(G)`), `⟨H, H^x⟩ = H ⊔ H^x ≤ F(G)`,
F(G) 冪零, subgroup of nilpotent も冪零. -/
theorem baer_sup_conj_isNilpotent_of_le_fitting [Finite G] {H : Subgroup G}
    (hH : H ≤ fitting G) (x : G) :
    Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) := by
  -- MulAut.conj x • F(G) = F(G) (F(G) ⊴ G).
  have hFnormal : (MulAut.conj x : MulAut G) • (fitting G : Subgroup G) = fitting G :=
    Subgroup.Normal.conj_smul_eq_self (h := fitting.normal G) x (fitting G)
  -- H^x ≤ F(G).
  have hHx_le : ((MulAut.conj x) • H : Subgroup G) ≤ fitting G := by
    rw [← hFnormal]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hH
  -- H ⊔ H^x ≤ F(G).
  have hSup_le : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≤ fitting G := sup_le hH hHx_le
  -- Subgroup of nilpotent F(G) is nilpotent.
  exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSup_le)

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 逆方向の `|G|`-induction の generalized core.

任意の有限群 `G` (with `Nat.card G ≤ n`) について,
`∀x ∈ G, ⟨H, H^x⟩ 冪零` ならば `H ≤ F(G)`.

Isaacs p.55 の証明戦略:
1. `x = 1` 適用で `H` 自身が冪零.
2. Thm 2.2 で `H ≤ F(G) ⟺ H 冪零 ∧ H 部分正規`. 部分正規性のみ示せばよい.
3. 部分正規性を背理法 + `|G|`-induction.  IH が真部分群 `K ⊇ H` で `H` の部分正規性を
   与える (Zipper Lemma の hypothesis を充足).
4. Zipper Lemma で `H` を含む極大 `M` 一意.
5. 各 `x` で `⟨H, H^x⟩` 冪零 ≠ ⊤ (= ⊤ なら `G` 冪零 ⇒ 矛盾) ⇒ `⟨H, H^x⟩ ⊆ M`.
6. 正規閉包 `H^G ⊆ M < ⊤`. IH で `H ⊴⊴ H^G ⊴ G`, 矛盾. -/
private theorem le_fitting_of_baer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {H : Subgroup G},
      (∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) →
      H ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ H hN
    -- Step 0: H は冪零 (x = 1 で hN 適用).
    have hH_nilp : Group.IsNilpotent ↥H := by
      have h1 := hN 1
      rw [map_one, one_smul, sup_idem] at h1
      exact h1
    -- Step 1: H が部分正規であれば Thm 2.2 で結論.
    suffices hSn : H.IsSubnormal from
      (le_fitting_iff_isNilpotent_and_isSubnormal H).mpr ⟨hH_nilp, hSn⟩
    -- Step 2: H 部分正規でないと仮定 ⇒ 矛盾.
    by_contra hSnneg
    -- IH: 真部分群 K ⊇ H で H.subgroupOf K は部分正規.
    have hIH : ∀ K : Subgroup G, H ≤ K → K ≠ ⊤ →
        (H.subgroupOf K).IsSubnormal := by
      intro K hHK hKne
      have hK_card : Nat.card K ≤ n := by
        have hKle : Nat.card K ≤ Nat.card G := K.card_le_card_group
        have hKne_card : Nat.card K ≠ Nat.card G := fun heq =>
          hKne (Subgroup.eq_top_of_card_eq K heq)
        omega
      have hIH_K : (H.subgroupOf K) ≤ fitting K := by
        apply ih K hK_card
        intro y
        -- Permutability transfer G → ↥K via Subgroup.conj_smul_subgroupOf.
        rw [Subgroup.conj_smul_subgroupOf hHK]
        have hHy_le_K : ((MulAut.conj (y : G)) • H : Subgroup G) ≤ K :=
          Subgroup.conj_smul_le_of_le hHK y
        rw [← Subgroup.subgroupOf_sup hHK hHy_le_K]
        haveI : Group.IsNilpotent
            ↥(H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) := hN (y : G)
        have hsup_le_K : (H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) ≤ K :=
          sup_le hHK hHy_le_K
        exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hsup_le_K).symm
      exact ((le_fitting_iff_isNilpotent_and_isSubnormal _).mp hIH_K).2
    -- Zipper Lemma で `H` を含む極大部分群 `M` の一意性.
    obtain ⟨M, hMcoatom, _, hMuniq⟩ := zipper_lemma hIH hSnneg
    -- 各 x : G で `MulAut.conj x • H ≤ M`.
    have hHx_le_M : ∀ x : G, ((MulAut.conj x) • H : Subgroup G) ≤ M := by
      intro x
      have hNx := hN x
      -- ⟨H, H^x⟩ ≠ ⊤ (else G 冪零 ⇒ H 部分正規, 矛盾).
      have hsup_ne_top : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≠ ⊤ := by
        intro h_top
        apply hSnneg
        rw [h_top] at hNx
        haveI := hNx
        haveI hG_nilp : Group.IsNilpotent G :=
          nilpotent_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        exact isSubnormal_of_isNilpotent_finite H
      -- ⟨H, H^x⟩ ≤ M (M は H を含む唯一の極大).
      obtain ⟨K, hKcoatom, hKle⟩ :=
        (eq_top_or_exists_le_coatom (H ⊔ ((MulAut.conj x) • H : Subgroup G) :
          Subgroup G)).resolve_left hsup_ne_top
      have hHK : H ≤ K := le_sup_left.trans hKle
      have hKM : K = M := hMuniq K hKcoatom hHK
      exact (le_sup_right.trans hKle).trans hKM.le
    -- 正規閉包 `H^G ≤ M`.
    have hNH_le_M : Subgroup.normalClosure (H : Set G) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro y hy
      rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨a, haH, hConj⟩
      rcases hConj with ⟨c, hc⟩
      apply hHx_le_M (c : G)
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
      change ((c : G)⁻¹) * y * ((c : G)⁻¹)⁻¹ ∈ H
      rw [inv_inv]
      have hc_eq : (c : G) * a = y * (c : G) := hc
      have ha_eq : ((c : G)⁻¹) * y * ((c : G)) = a := by
        rw [mul_assoc, ← hc_eq]
        group
      rw [ha_eq]
      exact haH
    -- 正規閉包 < ⊤ (since ≤ M coatom).
    have hNH_lt : Subgroup.normalClosure (H : Set G) ≠ ⊤ := fun hNHtop =>
      hMcoatom.1 (le_top.antisymm (hNHtop.symm.le.trans hNH_le_M))
    -- IH を `normalClosure H` に適用.
    have hHle_NH : H ≤ Subgroup.normalClosure (H : Set G) :=
      Subgroup.le_normalClosure
    have hH_sn_in_NH : (H.subgroupOf (Subgroup.normalClosure (H : Set G))).IsSubnormal :=
      hIH _ hHle_NH hNH_lt
    have hNH_sn : (Subgroup.normalClosure (H : Set G)).IsSubnormal :=
      Subgroup.Normal.isSubnormal inferInstance
    exact hSnneg (Subgroup.IsSubnormal.trans hHle_NH hH_sn_in_NH hNH_sn)

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 逆方向: `∀ x ∈ G, ⟨H, H^x⟩` 冪零 ⇒ `H ≤ F(G)`.

Isaacs p.55 の証明: Wielandt's Zipper Lemma (Thm 2.9) + Thm 2.2 経由の `|G|`-induction.
詳細は補助 [`le_fitting_of_baer_aux`](#le_fitting_of_baer_aux) の docstring 参照. -/
theorem le_fitting_of_baer_sup_conj_isNilpotent [Finite G] {H : Subgroup G}
    (hN : ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) :
    H ≤ fitting G :=
  le_fitting_of_baer_aux (Nat.card G) G le_rfl hN

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 完全形 (iff): 有限群 `G` の部分群 `H` について,
`H ≤ F(G) ↔ ∀ x ∈ G, ⟨H, H^x⟩ 冪零`.

順方向 (`baer_sup_conj_isNilpotent_of_le_fitting`) は F(G) ⊴ G の単なる帰結.
逆方向 (`le_fitting_of_baer_sup_conj_isNilpotent`) は Zipper Lemma 経由の核心. -/
theorem le_fitting_iff_baer_sup_conj_isNilpotent [Finite G] (H : Subgroup G) :
    H ≤ fitting G ↔
      ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) :=
  ⟨fun hH => baer_sup_conj_isNilpotent_of_le_fitting hH,
   le_fitting_of_baer_sup_conj_isNilpotent⟩

/-! ### Lemma 2.14 (dihedral structure) + Thm 2.13 (Matsuyama)

Lemma 2.14 の full statement (D が dihedral group `DihedralGroup n` と同型) は別途.
ここでは Matsuyama 2.13 の証明に必要な核心のみ:
- `inv_by_two_involutions`: `t * z * t = z⁻¹` for `z ∈ ⟨s * t⟩` (Lemma 2.14 inversion).
- `mem_zpowers_or_mul_t_mem_of_mem_closure_pair`: ⟨{s, t}⟩ の元の構造 ∈ ⟨s*t⟩ または `x*t`.

これらから, `⟨{s, t}⟩` の non-2-power 位数の元は ⟨s*t⟩ にあると示し, Matsuyama に使う.
-/

/-- **Isaacs Lemma 2.14 essence (inversion)**: 2 つの involution `s, t ∈ G` の積 `s * t`
の zpower 部分群 `⟨s * t⟩` の任意の元は involution `t` で反転される.

書籍 p.56-57 Lemma 2.14(a),(b) の核心. Dihedral group の "rotation subgroup is inverted
by reflections" の代数版. Matsuyama 2.13 で奇素数位数元の存在から最終結論 `x^t = x⁻¹`
を導くのに使用. -/
theorem inv_by_two_involutions {s t : G} (hs : s * s = 1) (ht : t * t = 1) {z : G}
    (hz : z ∈ Subgroup.zpowers (s * t)) : t * z * t = z⁻¹ := by
  have ht_inv : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht).symm
  have hs_inv : s⁻¹ = s := (eq_inv_iff_mul_eq_one.mpr hs).symm
  -- t * (s * t) * t⁻¹ = (s * t)⁻¹.
  have h_conj_st : t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
    have h1 : t * (s * t) * t⁻¹ = t * s := by group
    rw [h1, mul_inv_rev, hs_inv, ht_inv]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
  calc t * z * t
      = t * (s * t) ^ n * t := by rw [← hn]
    _ = t * (s * t) ^ n * t⁻¹ := by congr 1; exact ht_inv.symm
    _ = (t * (s * t) * t⁻¹) ^ n := conj_zpow.symm
    _ = ((s * t)⁻¹) ^ n := by rw [h_conj_st]
    _ = ((s * t) ^ n)⁻¹ := inv_zpow _ _
    _ = z⁻¹ := by rw [hn]

/-- **Lemma 2.14 (structural form)**: 2 つの involution `s, t ∈ G` について,
`⟨{s, t}⟩` の任意の元は `⟨s * t⟩` に属するか, `x * t` (`x ∈ ⟨s * t⟩`) の形.

書籍 p.56-57 Lemma 2.14 の dihedral 構造の代数版. Closure induction で証明.
4 つの mul cases + 2 つの inv cases を `inv_by_two_involutions` で繋ぐ.

Matsuyama 2.13 で ⟨{s, t}⟩ が 2-group iff ⟨s*t⟩ が 2-group, を導くのに使用. -/
theorem mem_zpowers_or_mul_t_mem_of_mem_closure_pair {s t : G}
    (hs : s * s = 1) (ht : t * t = 1) {y : G}
    (hy : y ∈ Subgroup.closure ({s, t} : Set G)) :
    y ∈ Subgroup.zpowers (s * t) ∨ ∃ x ∈ Subgroup.zpowers (s * t), y = x * t := by
  have ht_inv : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht).symm
  -- t * x = x⁻¹ * t for x ∈ ⟨s * t⟩.
  have h_t_mul : ∀ x ∈ Subgroup.zpowers (s * t), t * x = x⁻¹ * t := by
    intro x hx
    have h := inv_by_two_involutions hs ht hx
    have h' : t * x = x⁻¹ * t⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact h
    rwa [ht_inv] at h'
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy_eq | hy_mem
    · -- y = s.
      rw [hy_eq]
      right
      refine ⟨s * t, Subgroup.mem_zpowers _, ?_⟩
      rw [mul_assoc, ht, mul_one]
    · -- y ∈ {t}, i.e., y = t.
      rw [Set.mem_singleton_iff.mp hy_mem]
      right
      exact ⟨1, Subgroup.one_mem _, (one_mul t).symm⟩
  | one => left; exact Subgroup.one_mem _
  | mul a b _ _ iha ihb =>
    rcases iha with ha_K | ⟨a', ha'_K, ha_eq⟩
    · rcases ihb with hb_K | ⟨b', hb'_K, hb_eq⟩
      · left; exact Subgroup.mul_mem _ ha_K hb_K
      · subst hb_eq
        right
        refine ⟨a * b', Subgroup.mul_mem _ ha_K hb'_K, ?_⟩
        rw [← mul_assoc]
    · subst ha_eq
      rcases ihb with hb_K | ⟨b', hb'_K, hb_eq⟩
      · -- (a' * t) * b. Push t through: t * b = b⁻¹ * t.
        right
        refine ⟨a' * b⁻¹, Subgroup.mul_mem _ ha'_K (Subgroup.inv_mem _ hb_K), ?_⟩
        calc a' * t * b
            = a' * (t * b) := mul_assoc a' t b
          _ = a' * (b⁻¹ * t) := by rw [h_t_mul b hb_K]
          _ = (a' * b⁻¹) * t := (mul_assoc _ _ _).symm
      · subst hb_eq
        -- (a' * t) * (b' * t) = a' * b'⁻¹ ∈ K (using t² = 1 + inversion).
        left
        have h_eq : a' * t * (b' * t) = a' * b'⁻¹ := by
          calc a' * t * (b' * t)
              = a' * (t * b') * t := by group
            _ = a' * (b'⁻¹ * t) * t := by rw [h_t_mul b' hb'_K]
            _ = a' * b'⁻¹ * (t * t) := by group
            _ = a' * b'⁻¹ * 1 := by rw [ht]
            _ = a' * b'⁻¹ := mul_one _
        rw [h_eq]
        exact Subgroup.mul_mem _ ha'_K (Subgroup.inv_mem _ hb'_K)
  | inv y _ ihy =>
    rcases ihy with hy_K | ⟨y', hy'_K, hy_eq⟩
    · left; exact Subgroup.inv_mem _ hy_K
    · subst hy_eq
      -- y⁻¹ = (y' * t)⁻¹ = t⁻¹ * y'⁻¹ = t * y'⁻¹ = y' * t (using inversion: t * y'⁻¹ = y' * t).
      right
      refine ⟨y', hy'_K, ?_⟩
      calc (y' * t)⁻¹
          = t⁻¹ * y'⁻¹ := mul_inv_rev _ _
        _ = t * y'⁻¹ := by rw [ht_inv]
        _ = (y'⁻¹)⁻¹ * t := h_t_mul y'⁻¹ (Subgroup.inv_mem _ hy'_K)
        _ = y' * t := by rw [inv_inv]

/-! ### Helpers for Thm 2.13 (Matsuyama) -/

/-- 自然数の補助: `N > 0` で `N` が `2` のべきでないなら, 奇素数の約数が存在する. -/
private theorem exists_odd_prime_dvd_of_not_pow_two :
    ∀ N : ℕ, 0 < N → (∀ k : ℕ, N ≠ 2^k) → ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ Odd q := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro _ hN_not_pow
    have hN_ne_one : N ≠ 1 := fun h => hN_not_pow 0 (by rw [h, pow_zero])
    obtain ⟨q, hq, hq_dvd⟩ := Nat.exists_prime_and_dvd hN_ne_one
    by_cases hq_two : q = 2
    · subst hq_two
      obtain ⟨m, hm⟩ := hq_dvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hm; omega
        · exact h
      have hm_lt : m < N := by rw [hm]; omega
      have hm_not_pow : ∀ k, m ≠ 2^k := fun k hk => by
        apply hN_not_pow (k + 1)
        rw [hm, hk, pow_succ, mul_comm]
      obtain ⟨q', hq', hq'_dvd, hq'_odd⟩ := ih m hm_lt hm_pos hm_not_pow
      exact ⟨q', hq', dvd_trans hq'_dvd ⟨2, by rw [hm, Nat.mul_comm]⟩, hq'_odd⟩
    · exact ⟨q, hq, hq_dvd, hq.odd_of_ne_two hq_two⟩

/-- `H ≤ F(G)` で `H` が `p`-subgroup なら `H ≤ O_p(G)`.

証明: `F(G)` は冪零 ⇒ 各素数 `p` について Sylow `p` が一意 (`Sylow.normal_of_isNilpotent`
+ `Sylow.characteristic_of_normal`). `H` をその unique Sylow に含め, characteristic
in normal で `G` の正規 `p`-部分群 ⇒ `normal_pgroup_le_opCore` で `O_p(G)` 配下. -/
private theorem mem_opCore_of_le_fitting_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH_pgroup : IsPGroup p H) (hH_fit : H ≤ fitting G) :
    H ≤ opCore p G := by
  -- Lift H to a subgroup of fitting G.
  set Hin : Subgroup (fitting G) := H.subgroupOf (fitting G) with hHin_def
  have hHin_pgroup : IsPGroup p Hin :=
    hH_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hH_fit).symm
  -- Sylow p of fitting G containing Hin.
  obtain ⟨Q, hHin_le_Q⟩ := hHin_pgroup.exists_le_sylow
  haveI hQ_normal : (Q : Subgroup (fitting G)).Normal := Sylow.normal_of_isNilpotent _
  haveI hQ_char : (Q : Subgroup (fitting G)).Characteristic :=
    Sylow.characteristic_of_normal _ hQ_normal
  haveI : ((Q : Subgroup (fitting G)).map (fitting G).subtype).Normal := inferInstance
  have hpgroupG : IsPGroup p ((Q : Subgroup (fitting G)).map (fitting G).subtype) :=
    Q.2.map (fitting G).subtype
  have hQ_le_op : (Q : Subgroup (fitting G)).map (fitting G).subtype ≤ opCore p G :=
    normal_pgroup_le_opCore hpgroupG
  intro x hx
  have hx_fit : x ∈ fitting G := hH_fit hx
  have hx_Hin : (⟨x, hx_fit⟩ : fitting G) ∈ Hin := by
    rw [hHin_def, Subgroup.mem_subgroupOf]
    exact hx
  have hx_Q : (⟨x, hx_fit⟩ : fitting G) ∈ (Q : Subgroup (fitting G)) :=
    hHin_le_Q hx_Hin
  exact hQ_le_op ⟨⟨x, hx_fit⟩, hx_Q, rfl⟩

open scoped Pointwise in
/-- **Isaacs Thm 2.13 (Matsuyama)**: 有限群 `G` の involution `t` (`t * t = 1`) で
`t ∉ O_2(G)` ならば, 奇素数位数の元 `x` で `t * x * t = x⁻¹` (Isaacs notation `x^t = x⁻¹`).

書籍 p.57 の証明 (Goldschmidt の Burnside `p^a q^b` 定理 (両素数奇) を偶数位数に拡張する
Matsuyama の核心):
1. `T = ⟨t⟩` は 2-subgroup, `t ≠ 1`.
2. `t ∉ O_2(G)` ⇒ `T ⊄ F(G)` (補助 `mem_opCore_of_le_fitting_of_isPGroup`).
3. Baer 逆 (Thm 2.12 iff) で ∃ g, `⟨T, T^g⟩` 非冪零.
4. `s = g·t·g⁻¹` も involution. `s = t` なら `⟨T, T^g⟩ = T` で冪零, 矛盾.
5. `s ≠ t` で `⟨{s, t}⟩` 非冪零 ⇒ 非 2-group (有限 p-group は冪零).
6. ∃ 奇素数 `q ∣ |⟨{s, t}⟩|`. Cauchy で `y ∈ ⟨{s, t}⟩` で `orderOf y = q`.
7. 構造補題 (`mem_zpowers_or_mul_t_mem_of_mem_closure_pair`) で `y ∈ ⟨s*t⟩` or `y = x*t`.
   後者なら `y² = 1` で `q ∣ 2` 矛盾 (q odd).
8. `y ∈ ⟨s*t⟩` で Lemma 2.14 essence (`inv_by_two_involutions`) ⇒ `t * y * t = y⁻¹`. -/
theorem matsuyama [Finite G] {t : G} (ht_sq : t * t = 1)
    (ht_notin : t ∉ opCore 2 G) :
    ∃ x : G, ∃ p : ℕ, p.Prime ∧ Odd p ∧ orderOf x = p ∧ t * x * t = x⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Step 1: t ≠ 1.
  have ht_ne_one : t ≠ 1 := fun h => ht_notin (h ▸ Subgroup.one_mem _)
  set T : Subgroup G := Subgroup.zpowers t with hT_def
  -- orderOf t = 2.
  have h_ord_t : orderOf t = 2 := by
    have h_dvd : orderOf t ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht_sq)
    rcases (Nat.dvd_prime Nat.prime_two).mp h_dvd with hone | htwo
    · exact absurd (orderOf_eq_one_iff.mp hone) ht_ne_one
    · exact htwo
  have hT_pgroup : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, h_ord_t, pow_one]
  -- Step 2: T ⊄ fitting G.
  have hT_not_fit : ¬ T ≤ fitting G := fun hTF => ht_notin
    (mem_opCore_of_le_fitting_of_isPGroup hT_pgroup hTF (Subgroup.mem_zpowers _))
  -- Step 3: Baer iff ⇒ ∃ g, ⟨T, T^g⟩ not nilpotent.
  have hExist : ∃ g : G, ¬ Group.IsNilpotent ↥(T ⊔ ((MulAut.conj g) • T : Subgroup G)) := by
    by_contra h
    push_neg at h
    exact hT_not_fit ((le_fitting_iff_baer_sup_conj_isNilpotent T).mpr h)
  obtain ⟨g, hg⟩ := hExist
  -- Step 4: s := g·t·g⁻¹.
  set s : G := g * t * g⁻¹ with hs_def
  have hs_sq : s * s = 1 := by
    change (g * t * g⁻¹) * (g * t * g⁻¹) = 1
    calc (g * t * g⁻¹) * (g * t * g⁻¹)
        = g * t * (g⁻¹ * g) * t * g⁻¹ := by group
      _ = g * t * 1 * t * g⁻¹ := by rw [inv_mul_cancel]
      _ = g * (t * t) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [ht_sq]
      _ = 1 := by group
  -- T^g = zpowers s.
  have hTg_eq : ((MulAut.conj g) • T : Subgroup G) = Subgroup.zpowers s := by
    rw [hT_def, Subgroup.pointwise_smul_def]
    exact MonoidHom.map_zpowers _ _
  rw [hTg_eq] at hg
  -- Step 5: Case s = t ⇒ T ⊔ T = T nilpotent, 矛盾.
  by_cases hst : s = t
  · exfalso
    rw [hst, ← hT_def, sup_idem] at hg
    exact hg hT_pgroup.isNilpotent
  -- Step 6: s ≠ t. T ⊔ zpowers s = closure {s, t}.
  have h_sup_eq : T ⊔ Subgroup.zpowers s = Subgroup.closure ({s, t} : Set G) := by
    rw [hT_def, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_union]
    congr 1
    ext x
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
  rw [h_sup_eq] at hg
  haveI hClosure_fin : Finite ↥(Subgroup.closure ({s, t} : Set G)) := Subtype.finite
  -- Step 7: ⟨{s, t}⟩ not 2-group.
  have h_not_pgroup : ¬ IsPGroup 2 ↥(Subgroup.closure ({s, t} : Set G)) := fun h =>
    hg h.isNilpotent
  have h_card_not_pow : ∀ k : ℕ,
      Nat.card ↥(Subgroup.closure ({s, t} : Set G)) ≠ 2^k := fun k hk =>
    h_not_pgroup (IsPGroup.iff_card.mpr ⟨k, hk⟩)
  obtain ⟨q, hq_prime, hq_dvd, hq_odd⟩ :=
    exists_odd_prime_dvd_of_not_pow_two _ Nat.card_pos h_card_not_pow
  haveI hq_fact : Fact q.Prime := ⟨hq_prime⟩
  -- Step 8: Cauchy ⇒ ∃ y of order q.
  obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card' q hq_dvd
  have h_ord_y_G : orderOf (y : G) = q := by
    rw [← hy_ord]; exact Subgroup.orderOf_coe y
  have hy_inG : (y : G) ∈ Subgroup.closure ({s, t} : Set G) := y.2
  -- Step 9: 構造補題で y ∈ ⟨s*t⟩ or y = x*t.
  rcases mem_zpowers_or_mul_t_mem_of_mem_closure_pair hs_sq ht_sq hy_inG with
    hy_K | ⟨x, hx_K, hy_eq⟩
  · -- y ∈ ⟨s*t⟩ ⇒ Lemma 2.14 で t * y * t = y⁻¹.
    exact ⟨(y : G), q, hq_prime, hq_odd, h_ord_y_G,
           inv_by_two_involutions hs_sq ht_sq hy_K⟩
  · -- y = x * t ⇒ y² = 1 ⇒ q ∣ 2 ⇒ q = 2, 矛盾 (q odd).
    exfalso
    have h_sq : (y : G) * (y : G) = 1 := by
      rw [hy_eq]
      calc (x * t) * (x * t)
          = x * (t * x * t) := by group
        _ = x * x⁻¹ := by rw [inv_by_two_involutions hs_sq ht_sq hx_K]
        _ = 1 := mul_inv_cancel x
    have h_ord_dvd : orderOf (y : G) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h_sq)
    rw [h_ord_y_G] at h_ord_dvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h_ord_dvd with h1 | h2
    · exact hq_prime.one_lt.ne' h1
    · rw [h2] at hq_odd
      rcases hq_odd with ⟨k, hk⟩
      omega

end -- 2B

/-! ### §2C 状態 (TODO)

§2C 全体 (Thm 2.15 p-local + Lemma 2.16/2.17) は p-local 部分群の準同型像/逆像の構造
定理. Isaacs 自身が「subnormality との直接関連無く脱線」と明言する独立小節. FT クリティカル
度低く, Lemma 2.17 のみ Ch.4+ で 3 回引用される. 本リポでは別 commit で §2D 完了後に追加. -/

section /- 2D: Zenkov + Lucchini (pp. 61-64) -/

variable {G : Type*} [Group G]

/-! ### §2D 状態

* Cor 2.19 完成 (Zenkov axiom 経由)
* Thm 2.18 Zenkov, Thm 2.20 Lucchini は引き続き axiom 化
* 補助補題 `card_set_mul_card_inf` は §2A 末尾に移動 (Thm 2.11 でも使用)
* Zenkov 用 Case 1 補助補題 (`conj_smul_abelian`, `inf_le_center_of_join_eq_top`,
  `center_le_fitting`) を standalone で提供 — Zenkov 完成時 + Lucchini 完成時に再利用
-/

open scoped Pointwise in
/-- 共役で abelian 性は保たれる: `B` abelian なら `(MulAut.conj g) • B` も abelian.

Zenkov Case 1 / Wielandt Case 1 等で頻用. -/
private lemma conj_smul_abelian {G : Type*} [Group G] {B : Subgroup G}
    (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (g : G) :
    ∀ b ∈ ((MulAut.conj g) • B : Subgroup G),
      ∀ b' ∈ ((MulAut.conj g) • B : Subgroup G), b * b' = b' * b := by
  intro b₁ hb₁ b₂ hb₂
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def] at hb₁ hb₂
  have hb₁' : g⁻¹ * b₁ * g ∈ B := by
    have h : g⁻¹ * b₁ * (g⁻¹)⁻¹ ∈ B := hb₁
    rwa [inv_inv] at h
  have hb₂' : g⁻¹ * b₂ * g ∈ B := by
    have h : g⁻¹ * b₂ * (g⁻¹)⁻¹ ∈ B := hb₂
    rwa [inv_inv] at h
  have habelian := hBab _ hb₁' _ hb₂'
  have hs1 : (g⁻¹ * b₁ * g) * (g⁻¹ * b₂ * g) = g⁻¹ * (b₁ * b₂) * g := by group
  have hs2 : (g⁻¹ * b₂ * g) * (g⁻¹ * b₁ * g) = g⁻¹ * (b₂ * b₁) * g := by group
  rw [hs1, hs2] at habelian
  have hconj := congrArg (fun z => g * z * g⁻¹) habelian
  simp only at hconj
  calc b₁ * b₂ = g * (g⁻¹ * (b₁ * b₂) * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * (b₂ * b₁) * g) * g⁻¹ := hconj
    _ = b₂ * b₁ := by group

/-- `A`, `B` abelian で `⟨A, B⟩ = ⊤` ⇒ `A ⊓ B ⊆ Z(G)`.

Wielandt と Zenkov Case 1 共通の中心性論証. centralizer ⊇ A ∪ B ⇒ centralizer ⊇ ⟨A,B⟩ = ⊤. -/
private lemma inf_le_center_of_join_eq_top {G : Type*} [Group G] {A B : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hsup : A ⊔ B = ⊤) :
    (A ⊓ B : Subgroup G) ≤ Subgroup.center G := by
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hc_A, hc_B⟩ := hc
  rw [Subgroup.mem_center_iff]
  intro x
  have h_central_A : A ≤ Subgroup.centralizer ({c} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
    exact (hAab a ha c hc_A).symm
  have h_central_B : B ≤ Subgroup.centralizer ({c} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
    exact (hBab b hb c hc_B).symm
  have h_sup_le := sup_le h_central_A h_central_B
  have h_centralizer_top : Subgroup.centralizer ({c} : Set G) = ⊤ :=
    top_le_iff.mp (hsup ▸ h_sup_le)
  have hx_central : x ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [h_centralizer_top]; exact Subgroup.mem_top x
  rw [Subgroup.mem_centralizer_iff] at hx_central
  exact (hx_central c (Set.mem_singleton _)).symm

/-- `Subgroup.center G ≤ fitting G`. Center は abelian → 冪零, 正規部分群. -/
private lemma center_le_fitting (G : Type*) [Group G] [Finite G] :
    Subgroup.center G ≤ fitting G := by
  haveI : Group.IsNilpotent ↥(Subgroup.center G) := inferInstance
  exact nilpotent_normal_le_fitting

/-- 有限群 `M` は **その全 Sylow 部分群の sup** で生成される: 各素因子 `p` ごとの
全 Sylow `p` 部分群を sup したものは `⊤_M`.

書籍では「`M` は Sylow 部分群で生成される」と頻用される. mathlib の
`iSup_default_sylow_eq_top_of_nilpotent` は冪零版 (一つの Sylow per prime で十分).
本版は一般有限群対応 (Sylow 共役を全て取る).

証明: 各素因子 `p` に対し `|Sylow p| = p ^ v_p(|M|)` (`Sylow.card_eq_multiplicity`),
これが sup の card を割る. 異素因子で coprime ⇒ factorization 比較で `|sup| = |M|`. -/
private lemma iSup_sylow_eq_top {M : Type*} [Group M] [Finite M] :
    (⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M)) = ⊤ := by
  classical
  set sup := ⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M) with hsup_def
  -- |sup| ∣ |M|.
  have h_sup_dvd : Nat.card sup ∣ Nat.card M := Subgroup.card_subgroup_dvd_card sup
  -- For each p ∈ primeFactors |M|, p^{v_p(|M|)} ∣ |sup|.
  have h_pow_dvd : ∀ p ∈ (Nat.card M).primeFactors,
      p ^ (Nat.card M).factorization p ∣ Nat.card sup := by
    intro p hp
    haveI hp_prime : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hP_le : ((default : Sylow p M) : Subgroup M) ≤ sup := by
      rw [hsup_def]
      refine le_trans ?_ (le_iSup (fun q : (Nat.card M).primeFactors =>
        ⨆ Q : Sylow q.val M, (Q : Subgroup M)) ⟨p, hp⟩)
      exact le_iSup (fun Q : Sylow p M => (Q : Subgroup M)) default
    have h_dvd := Subgroup.card_dvd_of_le hP_le
    rwa [Sylow.card_eq_multiplicity] at h_dvd
  -- v_p(|M|) ≤ v_p(|sup|) for all p.
  have h_factorization_le : ∀ p, (Nat.card M).factorization p ≤ (Nat.card sup).factorization p := by
    intro p
    rcases Nat.eq_zero_or_pos ((Nat.card M).factorization p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hp_in : p ∈ (Nat.card M).primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr (by omega)
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
      exact (hp_prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (h_pow_dvd p hp_in)
  -- v_p(|sup|) ≤ v_p(|M|) for all p.
  have h_factorization_le' : ∀ p, (Nat.card sup).factorization p ≤ (Nat.card M).factorization p :=
    fun p => (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr h_sup_dvd p
  -- |sup| = |M|.
  have h_eq : Nat.card sup = Nat.card M := by
    apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
    intro p
    exact le_antisymm (h_factorization_le' p) (h_factorization_le p)
  exact Subgroup.eq_top_of_card_eq sup h_eq

/-- 補助: `S ≤ opCore p H` (p-subgroup of opCore), `S'` p-subgroup of H ⇒ `S ⊔ S'` p-group.

Zenkov Case 2 で `⟨P, P^x⟩` (P が p-Sylow of M, P^x conjugate) を p-group と
示す核心. `opCore p H ⊴ H` で normal-sup-pgroup を経由. -/
private lemma sup_isPGroup_of_le_opCore_left {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {S S' : Subgroup H}
    (hS : S ≤ opCore p H) (hS' : IsPGroup p S') :
    IsPGroup p ↥(S ⊔ S' : Subgroup H) := by
  have h_op_pgroup : IsPGroup p ↥(opCore p H) := opCore_isPGroup p H
  haveI : (opCore p H).Normal := opCore.normal p H
  have h_op_sup : IsPGroup p ↥(opCore p H ⊔ S' : Subgroup H) :=
    h_op_pgroup.to_sup_of_normal_left hS'
  exact h_op_sup.to_le (sup_le_sup_right hS _)

open scoped Pointwise in
/-- 補助: G の Zenkov minimality `hMin` を `↥H` に転送 (Zenkov Case 2 IH 適用用).

`A ≤ H` のとき, G レベルの `A ⊓ B^g ≤ A ⊓ B ⇒ equal` から ↥H レベルの対応する
minimality を導く. `conj_smul_subgroupOf` (`h ∈ H` で `H` 共役不変) + subgroupOf 同型. -/
private lemma zenkov_minimality_transfer {G : Type*} [Group G] {A B : Subgroup G}
    (hMin : ∀ g : G, (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ A ⊓ B →
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) = A ⊓ B)
    {H : Subgroup G} (hAH : A ≤ H) :
    ∀ h : ↥H,
      ((A.subgroupOf H : Subgroup ↥H) ⊓
        ((MulAut.conj h) • (B.subgroupOf H) : Subgroup ↥H)) ≤
        A.subgroupOf H ⊓ B.subgroupOf H →
      ((A.subgroupOf H : Subgroup ↥H) ⊓
        ((MulAut.conj h) • (B.subgroupOf H) : Subgroup ↥H)) =
        A.subgroupOf H ⊓ B.subgroupOf H := by
  intro h hle
  have hB_sub : B.subgroupOf H = (B ⊓ H).subgroupOf H :=
    (Subgroup.inf_subgroupOf_right B H).symm
  have hBcap_le_H : (B ⊓ H : Subgroup G) ≤ H := inf_le_right
  have hconj : ((MulAut.conj h) • B.subgroupOf H : Subgroup ↥H) =
      (((MulAut.conj (h : G)) • (B ⊓ H) : Subgroup G).subgroupOf H : Subgroup ↥H) := by
    rw [hB_sub]
    exact Subgroup.conj_smul_subgroupOf hBcap_le_H h
  have h_conj_H_eq_H : ((MulAut.conj (h : G)) • H : Subgroup G) = H := by
    ext y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
    change (h : G)⁻¹ * y * ((h : G)⁻¹)⁻¹ ∈ H ↔ y ∈ H
    rw [inv_inv]
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have heq : (h : G) * ((h : G)⁻¹ * y * (h : G)) * (h : G)⁻¹ = y := by group
      rw [← heq]
      exact H.mul_mem (H.mul_mem h.2 hy) (H.inv_mem h.2)
    · exact H.mul_mem (H.mul_mem (H.inv_mem h.2) hy) h.2
  have h_conj_inter : ((MulAut.conj (h : G)) • (B ⊓ H) : Subgroup G) =
      ((MulAut.conj (h : G)) • B : Subgroup G) ⊓ H := by
    rw [Subgroup.smul_inf, h_conj_H_eq_H]
  rw [hconj, h_conj_inter] at hle ⊢
  have h_lhs_eq : ((A.subgroupOf H : Subgroup ↥H) ⊓
      (((MulAut.conj (h : G)) • B ⊓ H : Subgroup G).subgroupOf H : Subgroup ↥H)) =
      ((A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G).subgroupOf H : Subgroup ↥H) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    refine ⟨fun ⟨hxA, hxB_H⟩ => ⟨hxA, hxB_H.1⟩, fun ⟨hxA, hxB⟩ => ⟨hxA, hxB, x.2⟩⟩
  have h_rhs_eq : ((A.subgroupOf H : Subgroup ↥H) ⊓ B.subgroupOf H) =
      ((A ⊓ B : Subgroup G).subgroupOf H : Subgroup ↥H) := by
    ext x; simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [h_lhs_eq, h_rhs_eq] at hle ⊢
  have hLA_le_H : (A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G) ≤ H :=
    le_trans inf_le_left hAH
  have hle_G : (A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G) ≤ (A ⊓ B : Subgroup G) := by
    intro y hy
    have hyH : y ∈ H := hLA_le_H hy
    have : (⟨y, hyH⟩ : ↥H) ∈
        ((A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G).subgroupOf H : Subgroup ↥H) := hy
    exact hle this
  have h_eq_G := hMin (h : G) hle_G
  exact congrArg (·.subgroupOf H) h_eq_G

open scoped Pointwise in
/-- **Zenkov Case 1** (Isaacs Thm 2.18 の Case 1, WLOG `g₀ = 1`):
`A`, `B` abelian, `M = A ⊓ B` minimal in family, **かつ ある `g` で `A ⊔ B^g = ⊤`** ⇒
`M ⊆ F(G)`.

書籍 p.61 Case 1: `A ⊓ B^g ⊆ Z(G)` (A, B^g abelian + 生成) → 中心元は conj 不変
⇒ `A ⊓ B^g ⊆ B` ⇒ `A ⊓ B^g ⊆ M`. Minimality で `M = A ⊓ B^g ⊆ Z(G) ⊆ F(G)`. -/
theorem zenkov_case1_le_fitting {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hMin : ∀ g : G, (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ A ⊓ B →
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) = A ⊓ B)
    (hExists : ∃ g : G, A ⊔ ((MulAut.conj g) • B : Subgroup G) = ⊤) :
    (A ⊓ B : Subgroup G) ≤ fitting G := by
  obtain ⟨g, hsup⟩ := hExists
  have hBg_ab := conj_smul_abelian hBab g
  have h_inf_center : (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤
      Subgroup.center G := inf_le_center_of_join_eq_top hAab hBg_ab hsup
  -- A ⊓ B^g ⊆ B: central c は g⁻¹ c g = c, c = g b g⁻¹ ⇒ b = c ∈ B.
  have h_inf_le_B : (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ B := by
    intro c hc
    have hc_central : c ∈ Subgroup.center G := h_inf_center hc
    rw [Subgroup.mem_inf] at hc
    obtain ⟨_, hc_Bg⟩ := hc
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def] at hc_Bg
    change g⁻¹ * c * (g⁻¹)⁻¹ ∈ B at hc_Bg
    rw [Subgroup.mem_center_iff] at hc_central
    have h_inv_c_g : g⁻¹ * c = c * g⁻¹ := hc_central g⁻¹
    have h_eq : g⁻¹ * c * (g⁻¹)⁻¹ = c := by rw [h_inv_c_g]; group
    rwa [h_eq] at hc_Bg
  have h_inf_le_M : (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ A ⊓ B :=
    le_inf inf_le_left h_inf_le_B
  have h_eq := hMin g h_inf_le_M
  rw [← h_eq]
  exact h_inf_center.trans (center_le_fitting G)

open scoped Pointwise in
/-- **Isaacs Thm 2.18 (Zenkov)**: 有限群 `G` の abelian 部分群 `A, B`. `g₀ ∈ G` で
`M = A ⊓ B^{g₀}` が集合 `{A ⊓ B^g | g ∈ G}` の minimal member (包含関係について) なら,
`M ⊆ F(G)`.

書籍 p.61 の証明 (induction on `|G|`):
1. WLOG `g₀ = 1` (B を `B^{g₀}` で置き換え).
2. **Case G = ⟨A, B^g⟩ for some g**: A, B^g abelian ⇒ `A ⊓ B^g ⊆ Z(G)`. Z(G) 共役不変 ⇒
   `A ⊓ B^g = (A ⊓ B^g)^{g⁻¹} ⊆ B`. 故に `A ⊓ B^g ⊆ A ⊓ B = M`. Minimality で
   `M = A ⊓ B^g ⊆ Z(G) ⊆ F(G)`.
3. **Case ⟨A, B^g⟩ < G for all g**: `M` の各 Sylow `p` `P` について `P ⊆ F(G)` を示す
   (Baer iff). Fix `h`. `H = ⟨A, B^h⟩ < G`. `C = B ⊓ H`. `x ∈ H` で
   `A ⊓ C^x = A ⊓ B^x ⊓ H = A ⊓ B^x` (A ⊆ H). `M = A ⊓ C` minimal in
   `{A ⊓ C^x | x ∈ H}`. IH in H ⇒ `M ⊆ F(H)`, `P ⊆ O_p(H)` (Sylow p of nilpotent F(H)).
   `P^h ⊆ B^h ⊆ H` ⇒ `P^h` normalizes `O_p(H)` ⇒ `O_p(H) · P^h` は p-group ⊇ `⟨P, P^h⟩`.
   故に `⟨P, P^h⟩` 冪零. Baer で `P ⊆ F(G)`. -/
axiom zenkov_minimal_le_fitting [Finite G] {A B : Subgroup G}
    (_hA_ab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (_hB_ab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (g₀ : G)
    (_hMin : ∀ g : G,
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤
          A ⊓ ((MulAut.conj g₀) • B : Subgroup G) →
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) =
          A ⊓ ((MulAut.conj g₀) • B : Subgroup G)) :
    (A ⊓ ((MulAut.conj g₀) • B : Subgroup G) : Subgroup G) ≤ fitting G

open scoped Pointwise in
/-- **Isaacs Cor 2.19**: `G` 非自明有限群, `A` abelian 部分群, `|A| ≥ |G:A|`
⇒ `A ⊓ F(G) ≠ ⊥`.

書籍 p.62 の証明: g ∈ G について `|A| · |A^g| = |A|² ≥ |G|`. `A < G` ならば Lemma 2.10
で `A · A^g ≠ G` (集合), `|A · A^g| = |A|² / |A ⊓ A^g|` の formula で `A ⊓ A^g > 1`.
Zenkov で minimal-card `g₀` を取り `A ⊓ A^{g₀} ⊆ F(G)`, これが `> 1` で `A ⊓ F(G) > 1`. -/
theorem inf_fitting_ne_bot_of_abelian_card_ge_index [Finite G] [Nontrivial G] {A : Subgroup G}
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCard : A.index ≤ Nat.card A) :
    A ⊓ fitting G ≠ ⊥ := by
  classical
  -- Case 1: A = ⊤. Then G is abelian, F(G) = G ≠ ⊥.
  by_cases hAtop : A = ⊤
  · subst hAtop
    rw [top_inf_eq]
    -- G is commutative via hA_ab on ⊤.
    have hG_commute : ∀ a b : G, a * b = b * a := fun a b =>
      hA_ab a (Subgroup.mem_top a) b (Subgroup.mem_top b)
    -- center G = ⊤.
    have hcenter : Subgroup.center G = ⊤ := by
      ext x
      refine ⟨fun _ => Subgroup.mem_top x, fun _ => ?_⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact hG_commute g x
    -- G is nilpotent.
    haveI hGnilp : Group.IsNilpotent G := ⟨1, by
      rw [upperCentralSeries_one]; exact hcenter⟩
    -- ↥⊤ is also nilpotent.
    haveI : Group.IsNilpotent ↥(⊤ : Subgroup G) :=
      nilpotent_of_mulEquiv Subgroup.topEquiv.symm
    -- F(G) = ⊤.
    have hFtop : fitting G = ⊤ := top_le_iff.mp (nilpotent_normal_le_fitting (N := ⊤))
    rw [hFtop]
    exact top_ne_bot
  · -- Case 2: A < ⊤.
    -- Pick g₀ minimizing |A ⊓ A^g| over g ∈ G.
    haveI : Fintype G := Fintype.ofFinite G
    set M : G → Subgroup G := fun g => A ⊓ ((MulAut.conj g) • A : Subgroup G) with hM_def
    obtain ⟨g₀, _, hg₀_min⟩ := Finset.exists_min_image Finset.univ
      (fun g => Nat.card ↥(M g)) Finset.univ_nonempty
    -- g₀ is ≤-minimal (used in Zenkov hypothesis).
    have hg₀_minimal : ∀ g : G, M g ≤ M g₀ → M g = M g₀ := by
      intro g hle
      have h_card_g₀_le_g : Nat.card ↥(M g₀) ≤ Nat.card ↥(M g) :=
        hg₀_min g (Finset.mem_univ _)
      -- M g ≤ M g₀ and |M g₀| ≤ |M g| ⇒ M g₀ = M g, hence M g = M g₀.
      exact (Subgroup.eq_of_le_of_card_ge hle h_card_g₀_le_g)
    -- Apply Zenkov to A, A.
    have h_M_le_F : M g₀ ≤ fitting G :=
      zenkov_minimal_le_fitting hA_ab hA_ab g₀ hg₀_minimal
    -- Show M g₀ ≠ ⊥ (using A < ⊤ + Lemma 2.10 + counting).
    have h_M_neBot : M g₀ ≠ ⊥ := by
      intro h_M_bot
      -- M g₀ = ⊥ means |M g₀| = 1.
      have h_card_one : Nat.card ↥(M g₀) = 1 := by
        rw [h_M_bot]; exact Subgroup.card_bot
      -- |A · A^g₀| · |M g₀| = |A| · |A^g₀| (counting helper).
      have h_count : Nat.card ((A : Set G) *
          (((MulAut.conj g₀) • A : Subgroup G) : Set G)) *
          Nat.card ↥(A ⊓ (MulAut.conj g₀) • A : Subgroup G) =
          Nat.card ↥A * Nat.card ↥((MulAut.conj g₀) • A : Subgroup G) :=
        card_set_mul_card_inf A ((MulAut.conj g₀) • A)
      -- |A^g₀| = |A| (conjugation preserves card).
      have h_conj_card : Nat.card ↥((MulAut.conj g₀) • A : Subgroup G) = Nat.card ↥A := by
        rw [Subgroup.pointwise_smul_def]
        exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g₀))
      -- M g₀ = A ⊓ ((MulAut.conj g₀) • A) by definition.
      have h_M_unfold : M g₀ = A ⊓ ((MulAut.conj g₀) • A : Subgroup G) := rfl
      rw [← h_M_unfold] at h_count
      rw [h_card_one, mul_one, h_conj_card] at h_count
      -- h_count : |A · A^g₀| = |A|²
      -- |A|² ≥ |G| (from hypothesis hCard).
      have h_A_sq : Nat.card G ≤ Nat.card ↥A * Nat.card ↥A := by
        calc Nat.card G = Nat.card ↥A * A.index := (Subgroup.card_mul_index A).symm
          _ ≤ Nat.card ↥A * Nat.card ↥A := Nat.mul_le_mul_left _ hCard
      -- |A · A^g₀| ≤ |G| (subset of G).
      have h_prod_subset : (A : Set G) *
          (((MulAut.conj g₀) • A : Subgroup G) : Set G) ⊆ Set.univ :=
        Set.subset_univ _
      -- A · A^g₀ = Set.univ (subset of G with cardinality |G|).
      have h_prod_eq_univ : (A : Set G) *
          (((MulAut.conj g₀) • A : Subgroup G) : Set G) = Set.univ := by
        apply Set.eq_of_subset_of_ncard_le h_prod_subset _ Set.finite_univ
        rw [Set.ncard_univ, ← Nat.card_coe_set_eq, h_count]
        exact h_A_sq
      -- Lemma 2.10: A · A^g₀ = univ ⇒ A = ⊤.
      -- For eq_top_of_set_mul_conj_eq_top, need: A * (MulAut.conj x⁻¹) • A = univ for some x.
      -- With x = g₀⁻¹: (MulAut.conj (g₀⁻¹)⁻¹) • A = (MulAut.conj g₀) • A. So apply with x = g₀⁻¹.
      have h_A_top : A = ⊤ := by
        apply eq_top_of_set_mul_conj_eq_top g₀⁻¹
        convert h_prod_eq_univ using 2
        rw [inv_inv]
      exact hAtop h_A_top
    -- Conclude.
    have h_M_le_inf : M g₀ ≤ A ⊓ fitting G := le_inf inf_le_left h_M_le_F
    intro hbot
    rw [hbot, le_bot_iff] at h_M_le_inf
    exact h_M_neBot h_M_le_inf

/-- **Isaacs Thm 2.20 (Lucchini)**: `G` 有限群, `A` cyclic 真部分群, `K = core_G(A)`.
ならば `|A:K| < |G:A|`. 特に `|A| ≥ |G:A|` なら `K > 1`.

書籍 p.62-63 の証明 (induction on `|G|`):
* `A/K` cyclic 真部分群 of `G/K`, `core_{G/K}(A/K) = 1`. `K > 1` なら IH in `G/K` で結論.
* `K = 1` のとき矛盾を導く. 仮に `|A| ≥ |G:A|`. Cor 2.19 で `A ⊓ F(G) > 1`. F(G) > 1.
  minimal normal `E ⊆ F(G)`, E ⊆ Z(F(G)), E elementary abelian `p`-group.
* `A ⊓ F(G) ⊴ AE`, `K = 1` で `AE < G`. Ḡ = G/E. `M̄ = core_{Ḡ}(Ā)`, M ⊇ E. AM = AE.
  IH in Ḡ で `|AE:M| < |G:AE|`. `B = A ⊓ M` cyclic.
* `|AE:A| = |M:B|`, `|AE:M| = |A:B|`. 計算で `|M:B| < |B|`.
* `M` abelian の場合: φ: m ↦ m^p, ker ⊇ E, M = EB ⇒ φ(M) = φ(B) ⊆ B ⊆ A. φ(M) ⊴ G で
  K = 1 より φ(M) = 1, B cyclic で `|B| ≤ p`, `|M:B| < p`, `M/B` p-group ⇒ `M = B ⊆ A`,
  M ⊴ G で M ⊆ K = 1 ⇒ E = 1 矛盾.
* `M` 非可換 + `M/E` cyclic ⇒ E 非中心 in M ⇒ `E ∩ Z(M) = 1`, Z(M) cyclic. B abelian in M,
  `|M:B| < |B|`, Cor 2.19 で `B ⊓ F(M) > 1`. F(M) ⊆ F(G), E centralizes F(M),
  `B ⊓ F(M)` central in `BE = M`. Z(M) cyclic ⇒ `B ⊓ F(M)` characteristic in Z(M) ⊴ G
  ⇒ G で正規 ⊆ A, K = 1 矛盾.

実装方針: 完全形式化は ~200-300 行の大規模作業. 本リポでは axiom で受け入れ. -/
axiom lucchini_index_normalCore_lt_index [Finite G] {A : Subgroup G} (_hA_proper : A < ⊤)
    (_hA_cyclic : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (_hA_isCyclic : ∃ g : G, A = Subgroup.zpowers g) :
    (A.normalCore.subgroupOf A).index < A.index

end -- 2D

end OddOrder.Isaacs.Ch02
