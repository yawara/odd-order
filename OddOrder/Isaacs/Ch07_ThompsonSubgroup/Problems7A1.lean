/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.ThompsonPComplement
import OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement

/-!
# Isaacs Problem 7A.1 — 単純群の冪零な極大部分群は `2`-群 (書籍 p. 209)

**主張**: 単純群 `G` の極大部分群 `M` が冪零なら `M` は `2`-群。

**証明**: 奇素数 `p ∣ |M|` を仮定して矛盾を出す。`P` を `M` の Sylow `p`-部分群 (を `G` の
部分群として見たもの) とすると

* `M` 冪零なので `P ⊴ M`, つまり `M ≤ N_G(P)`。単純性から `N_G(P) ≠ ⊤`
  (`P ≠ ⊥`, `P = ⊤` は `M = ⊤` に矛盾) なので極大性で **`N_G(P) = M`**。
* したがって `P` は `N_G(P)` の中で極大 `p`-部分群なので **`P ∈ Syl_p(G)`**。
* `P` の任意の非自明 characteristic 部分群 `X` について `M ≤ N_G(X)`
  (`P` は `X` を正規化し, `M` の `p`-complement `H` は `⁅P, H⁆ ≤ P ⊓ H = ⊥` で `P` を
  中心化する)。再び単純性 + 極大性で `N_G(X) = M` で, `M` は冪零だから normal
  `p`-complement を持つ。
* **Isaacs Thm 6.23** (`hasNormalPComplement_of_forall_characteristic_normalizer`,
  `p ≠ 2` が必須) より `G` が normal `p`-complement `N` を持つ。単純性で `N = ⊥` なら
  `P = ⊤ ≤ M` で `M ≠ ⊤` に反し, `N = ⊤` なら `P = ⊥` で `p ∣ |M|` に反する。

教科書 Thm 7.1 (`Z(P)` と `J(P)` の 2 つだけを仮定する強い版) は不要で, Thm 6.23 で足りる —
冪零な極大部分群は `P` の characteristic 部分群を**すべて**正規化するから。
-/

namespace OddOrder.Isaacs.Ch07

section /- 7A.1: 単純群の冪零極大部分群 (p. 209) -/

/-- **`N_G(P)` の中で極大な `p`-部分群は `G` の Sylow `p`-部分群**。

`P ≤ S ∈ Syl_p(G)` を取る。`P < S` なら `S` (`p`-群ゆえ冪零) の normalizer condition から
`P` を正規化する `x ∈ S \ P` があり, `P⟨x⟩` は `N_G(P)` 内の `p`-部分群で `P` を真に含むので
極大性に反する。 -/
theorem exists_sylow_eq_of_maximal_pSubgroup_in_normalizer {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p ↥P)
    (hmax : ∀ R : Subgroup G, IsPGroup p ↥R → P ≤ R → R ≤ Subgroup.normalizer P → R = P) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  classical
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hPS⟩
  by_contra hnot
  -- `P.subgroupOf S ≠ ⊤`
  have hHne : (P.subgroupOf (S : Subgroup G)) ≠ ⊤ := by
    intro htop
    exact hnot (Subgroup.subgroupOf_eq_top.mp htop)
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup G))
    (P.subgroupOf (S : Subgroup G)) (lt_top_iff_ne_top.mpr hHne)
  obtain ⟨x, hxnorm, hxnot⟩ := SetLike.exists_of_lt hlt
  -- `x` は `P` を (G の中で) 正規化する
  have hxN : ((x : ↥(S : Subgroup G)) : G) ∈ Subgroup.normalizer P := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · intro hy
      have hyS : y ∈ (S : Subgroup G) := hPS hy
      have hmem : (⟨y, hyS⟩ : ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := hy
      have := (Subgroup.mem_normalizer_iff.mp hxnorm ⟨y, hyS⟩).mp hmem
      exact this
    · intro hy
      have hyS : ((x : ↥(S : Subgroup G)) : G) * y * ((x : ↥(S : Subgroup G)) : G)⁻¹
          ∈ (S : Subgroup G) := hPS hy
      have hyS' : y ∈ (S : Subgroup G) := by
        have hx1 : ((x : ↥(S : Subgroup G)) : G) ∈ (S : Subgroup G) := x.2
        have := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
          ((S : Subgroup G).inv_mem hx1) hyS) hx1
        simpa [mul_assoc] using this
      have hmem : (⟨((x : ↥(S : Subgroup G)) : G) * y * ((x : ↥(S : Subgroup G)) : G)⁻¹, hyS⟩ :
          ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := hy
      exact (Subgroup.mem_normalizer_iff.mp hxnorm ⟨y, hyS'⟩).mpr hmem
  -- `P ⊔ ⟨x⟩` は `N_G(P)` 内の `p`-部分群
  have hxp : IsPGroup p ↥(Subgroup.zpowers ((x : ↥(S : Subgroup G)) : G)) := by
    refine S.isPGroup'.to_le ?_
    exact Subgroup.zpowers_le.mpr x.2
  have hsup_p : IsPGroup p ↥(P ⊔ Subgroup.zpowers ((x : ↥(S : Subgroup G)) : G)) :=
    hP.to_sup_of_normal_left' hxp (Subgroup.zpowers_le.mpr hxN)
  have hsup_le : P ⊔ Subgroup.zpowers ((x : ↥(S : Subgroup G)) : G) ≤ Subgroup.normalizer P :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN)
  have heq := hmax _ hsup_p le_sup_left hsup_le
  -- すると `x ∈ P` で矛盾
  refine hxnot ?_
  have hxP : ((x : ↥(S : Subgroup G)) : G) ∈ P := by
    rw [← heq]
    exact (le_sup_right : Subgroup.zpowers _ ≤ _) (Subgroup.mem_zpowers _)
  exact hxP

/-- **冪零群の Sylow 分解 (片側)**: `M ≤ G` が冪零で `Pm` がその Sylow `p`-部分群なら,
`M` の元はすべて「`Pm` の元」×「`Pm` を中心化する元」の積に書ける。

`M` 冪零 ⟹ `Pm ⊴ M` かつ normal `p`-complement `N ⊴ M` が在り, `N ⊓ Pm = ⊥` から
`N` は `Pm` を元ごとに中心化する (`Subgroup.commute_of_normal_of_disjoint`)。 -/
theorem exists_mul_centralizing_of_isNilpotent {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M : Subgroup G} (hMnil : Group.IsNilpotent ↥M) (Pm : Sylow p ↥M)
    {m : G} (hm : m ∈ M) :
    ∃ u ∈ (Pm : Subgroup ↥M).map M.subtype, ∃ h : G,
      (∀ v ∈ (Pm : Subgroup ↥M).map M.subtype, h * v = v * h) ∧ m = u * h := by
  classical
  haveI := hMnil
  haveI hPnormal : (Pm : Subgroup ↥M).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent Pm
  obtain ⟨N, hNnormal, hNcompl⟩ :=
    OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent (H := ↥M) (p := p)
  haveI := hNnormal
  have hcompl := hNcompl Pm
  have hcomm := Subgroup.commute_of_normal_of_disjoint N (Pm : Subgroup ↥M) hNnormal hPnormal
    hcompl.disjoint
  obtain ⟨⟨n, u⟩, hnu⟩ := hcompl.2 (⟨m, hm⟩ : ↥M)
  refine ⟨((u : ↥M) : G), ⟨(u : ↥M), u.2, rfl⟩, ((n : ↥M) : G), ?_, ?_⟩
  · rintro v ⟨v', hv', rfl⟩
    exact congrArg (fun w : ↥M => (w : G)) (hcomm (n : ↥M) v' n.2 hv')
  · have h2 : ((u : ↥M)) * ((n : ↥M)) = (⟨m, hm⟩ : ↥M) :=
      ((hcomm (n : ↥M) (u : ↥M) n.2 u.2).eq).symm.trans hnu
    have h3 := congrArg (fun w : ↥M => (w : G)) h2
    simpa using h3.symm

/-- **冪零 `M` は Sylow `P` の中の `P`-正規部分群を正規化する**。

`m = u * h` (`u ∈ P`, `h` は `P` を中心化) と書けば `m y m⁻¹ = u y u⁻¹ ∈ X`。
`M` が群であることから逆包含も従う。 -/
theorem le_normalizer_of_isNilpotent {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (hMnil : Group.IsNilpotent ↥M) (Pm : Sylow p ↥M)
    {X : Subgroup G} (hXP : X ≤ (Pm : Subgroup ↥M).map M.subtype)
    (hXnorm : ∀ u ∈ (Pm : Subgroup ↥M).map M.subtype, ∀ y ∈ X, u * y * u⁻¹ ∈ X) :
    M ≤ Subgroup.normalizer X := by
  have hinv : ∀ m ∈ M, ∀ y ∈ X, m * y * m⁻¹ ∈ X := by
    intro m hm y hy
    obtain ⟨u, hu, h, hcentral, hmeq⟩ := exists_mul_centralizing_of_isNilpotent hMnil Pm hm
    have hcomm : h * y = y * h := hcentral y (hXP hy)
    have hrw : m * y * m⁻¹ = u * y * u⁻¹ := by
      rw [hmeq, mul_inv_rev]
      calc u * h * y * (h⁻¹ * u⁻¹) = u * (h * y * h⁻¹) * u⁻¹ := by group
        _ = u * (y * h * h⁻¹) * u⁻¹ := by rw [hcomm]
        _ = u * y * u⁻¹ := by group
    rw [hrw]
    exact hXnorm u hu y hy
  intro m hm
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hinv m hm y hy, fun hy => ?_⟩
  have h1 := hinv m⁻¹ (M.inv_mem hm) _ hy
  simpa [mul_assoc] using h1

/-- **Isaacs Problem 7A.1** (p. 209) ⭐: 単純群の冪零な極大部分群は `2`-群。 -/
theorem isPGroup_two_of_isNilpotent_of_isCoatom {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] {M : Subgroup G} (hM : IsCoatom M) (hnil : Group.IsNilpotent ↥M) :
    IsPGroup 2 ↥M := by
  classical
  by_contra hnot
  -- 奇素数 `p ∣ |M|` を取る
  obtain ⟨p, hp, hpdvd, hp2⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card ↥M ∧ p ≠ 2 := by
    by_contra hcon
    refine hnot ?_
    have hall : ∀ q, q.Prime → q ∣ Nat.card ↥M → q = 2 := by
      intro q hq hqd
      by_contra hq2
      exact hcon ⟨q, hq, hqd, hq2⟩
    exact IsPGroup.of_card
      (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd => hall q hq hqd)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hnil
  obtain ⟨Pm⟩ : Nonempty (Sylow p ↥M) := inferInstance
  -- `P` = `M` の Sylow `p` を `G` の部分群として見たもの
  have hPM : (Pm : Subgroup ↥M).map M.subtype ≤ M := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  have hPp : IsPGroup p ↥((Pm : Subgroup ↥M).map M.subtype) := Pm.isPGroup'.map _
  have hPne : (Pm : Subgroup ↥M).map M.subtype ≠ ⊥ := by
    intro hbot
    refine Pm.ne_bot_of_dvd_card hpdvd ?_
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective M)] at hbot
  -- 極大性 + 単純性から `N_G(Y) = M` を出す道具
  have hnormeq : ∀ Y : Subgroup G, Y ≤ (Pm : Subgroup ↥M).map M.subtype → Y ≠ ⊥ →
      (∀ u ∈ (Pm : Subgroup ↥M).map M.subtype, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) →
      Subgroup.normalizer (Y : Set G) = M := by
    intro Y hYP hYne hYnorm
    have hle : M ≤ Subgroup.normalizer (Y : Set G) :=
      le_normalizer_of_isNilpotent hnil Pm hYP hYnorm
    have hne : Subgroup.normalizer (Y : Set G) ≠ ⊤ := by
      intro htop
      haveI hYnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y hYnormal with hb | ht
      · exact hYne hb
      · exact hM.1 (top_le_iff.mp ((ht ▸ hYP).trans hPM))
    have hnlt : ¬ M < Subgroup.normalizer (Y : Set G) := fun hlt => hne (hM.2 _ hlt)
    exact (eq_of_le_of_not_lt hle hnlt).symm
  sorry

end

end OddOrder.Isaacs.Ch07
