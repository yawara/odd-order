/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch01_Sylow

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

-- TODO **Isaacs Thm 2.2** (`H ⊆ F(G) ⇔ H` 冪零かつ部分正規).
--   `(⇒)`: H ⊆ F(G) で F(G) 冪零 (Cor 1.28(a), Ch.1 TODO 未済) → H 冪零 (mathlib).
--          F(G) ⊴ G → F(G).IsSubnormal. Lemma 2.1 を F(G) に適用して H ⊴⊴ F(G).
--          IsSubnormal.trans で H ⊴⊴ G.
--   `(⇐)`: H ⊴⊴ G かつ H 冪零 で induction on |G|.  H = G なら G 冪零 = F(G).
--          さもなくば subnormal chain の penultimate term M < G を取り IH で
--          H ≤ F(M) ⊴ G (F(M) 冪零 + 正規) ⇒ H ≤ fitting G (`nilpotent_normal_le_fitting`).
--   Ch.1 Cor 1.28(a) 完成後に着手.

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
          show (g' : G) ∈ Subgroup.normalizer (S : Set G)
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
                show g' * s * g'⁻¹ = (↑(⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ : N) : G)
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

end -- 2A

end OddOrder.Isaacs.Ch02
