/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch02_Subnormality.Problems
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02

/-!
# Isaacs Chapter 2 — Problems §2D: `G = NA` での `|A| < |N|` (p. 64)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) の章末演習 §2D。いずれも
`G = NA` (`N ⊴ G`)、`C_A(N) = 1` の状況で `|A| < |N|` を示す問題で、§2D 本文の
**Zenkov (Thm 2.18) / Cor 2.19 / Lucchini (Thm 2.20)** を使う。

- **2D.1(a)** `card_lt_card_of_fitting_eq_bot`: `A` 可換 + `F(N) = 1` ⟹ `|A| < |N|`。
- **2D.1(b)** `card_lt_card_of_coprime`: `A` 可換 + `|N|`, `|A|` 互いに素 ⟹ `|A| < |N|`。
- **2D.2** `card_lt_card_of_isCyclic`: `A` 巡回 + `A ∩ N = 1` + `N ≠ 1` ⟹ `|A| < |N|`。

⚠ **2D.1 には書籍が書いていない `N ≠ 1` が要る**: `N = 1` なら `C_A(N) = A` なので仮説から
`A = 1`、すなわち `|A| = |N| = 1` となり結論 `|A| < |N|` は成り立たない。2D.2 では書籍自身が
`N` 非自明を明示しているので、2D.1 でも同じ暗黙の仮定を置くのが原意と解した。
-/

namespace OddOrder.Isaacs.Ch02

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03

variable {G : Type*} [Group G]

open scoped Pointwise in
section /- Problems 2D: |A| < |N| for G = NA (p. 64) -/

/-- `G = NA` (`N ⊴ G`) のときの位数関係 `|G : A| · |N ∩ A| = |N|`
(積の位数公式 `|NA| · |N ∩ A| = |N| · |A|` と Lagrange `|G : A| · |A| = |G|`)。 -/
theorem index_mul_card_inf_eq_card_of_sup_eq_top [Finite G] {N A : Subgroup G} [N.Normal]
    (hG : N ⊔ A = ⊤) : A.index * Nat.card ↥(N ⊓ A) = Nat.card ↥N := by
  have h1 : Nat.card ((N : Set G) * (A : Set G) : Set G) * Nat.card ↥(N ⊓ A)
      = Nat.card ↥N * Nat.card ↥A := card_mul_card_inf N A
  have h2 : Nat.card ((N : Set G) * (A : Set G) : Set G) = Nat.card G := by
    rw [← Subgroup.normal_mul, hG]
    simp
  rw [h2, ← Subgroup.index_mul_card A] at h1
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥A)) ?_
  calc A.index * Nat.card ↥(N ⊓ A) * Nat.card ↥A
      = A.index * Nat.card ↥A * Nat.card ↥(N ⊓ A) := by ring
    _ = Nat.card ↥N * Nat.card ↥A := h1

/-- `G = NA` で `|N| ≤ |A|` なら Cor 2.19 の仮説 `|G : A| ≤ |A|` が成り立つ。 -/
theorem index_le_card_of_card_le [Finite G] {N A : Subgroup G} [N.Normal]
    (hG : N ⊔ A = ⊤) (hle : Nat.card ↥N ≤ Nat.card ↥A) : A.index ≤ Nat.card ↥A := by
  have hkey := index_mul_card_inf_eq_card_of_sup_eq_top hG
  have : A.index ≤ Nat.card ↥N := by
    rw [← hkey]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  omega

/-- `G` の正規部分群 `M`, `N` が交わらなければ `M ≤ C_G(N)`。 -/
theorem le_centralizer_of_inf_eq_bot {M N : Subgroup G} [M.Normal] [N.Normal]
    (h : M ⊓ N = ⊥) : M ≤ Subgroup.centralizer (N : Set G) := fun x hx => by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  exact (Subgroup.commute_of_normal_of_disjoint M N ‹M.Normal› ‹N.Normal›
    (disjoint_iff.mpr h) x n hx hn).symm.eq

/-- `F(G) ∩ N ≤ F(N)` (`N ⊴ G`): `F(G) ⊓ N` は `N` で正規かつ冪零ゆえ Thm 2.2 で `F(N)` 以下。
とくに `F(N) = 1` なら `F(G) ⊓ N = ⊥`。 -/
theorem fitting_inf_eq_bot_of_fitting_eq_bot [Finite G] {N : Subgroup G} [N.Normal]
    (hFN : fitting ↥N = ⊥) : fitting G ⊓ N = ⊥ := by
  have hle : fitting G ⊓ N ≤ N := inf_le_right
  have hnorm : ((fitting G ⊓ N).subgroupOf N).Normal :=
    (Subgroup.normal_inf_normal (fitting G) N).subgroupOf N
  have hfitnilp : Group.IsNilpotent ↥(fitting G) := fitting.isNilpotent
  have : Group.IsNilpotent ↥(fitting G ⊓ N) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : fitting G ⊓ N ≤ fitting G))
  have hnilp : Group.IsNilpotent ↥((fitting G ⊓ N).subgroupOf N) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hsub : (fitting G ⊓ N).subgroupOf N ≤ fitting ↥N :=
    (le_fitting_iff_isNilpotent_and_isSubnormal _).mpr ⟨hnilp, hnorm.isSubnormal⟩
  rw [hFN, le_bot_iff] at hsub
  rwa [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hle] at hsub

/-- **Isaacs Problem 2D.1(a)**. `G = NA` (`N ⊴ G`, `N ≠ 1`)、`C_A(N) = 1`、`A` 可換で
`F(N) = 1` ならば `|A| < |N|`。

`|A| ≥ |N|` と仮定すると `|G : A| ≤ |N| ≤ |A|` (`index_le_card_of_card_le`) なので
**Cor 2.19** で `A ⊓ F(G) ≠ 1`。一方 `F(N) = 1` から `F(G) ⊓ N = ⊥`
(`fitting_inf_eq_bot_of_fitting_eq_bot`)、`F(G)` と `N` はともに `G`-正規で交わらないから
`F(G) ≤ C_G(N)`、よって `A ⊓ F(G) ≤ A ⊓ C_G(N) = 1` で矛盾。 -/
theorem card_lt_card_of_fitting_eq_bot [Finite G] {N A : Subgroup G} [N.Normal]
    (hN : N ≠ ⊥) (hG : N ⊔ A = ⊤)
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCA : A ⊓ Subgroup.centralizer (N : Set G) = ⊥)
    (hFN : fitting ↥N = ⊥) :
    Nat.card ↥A < Nat.card ↥N := by
  by_contra hcon
  push Not at hcon
  have : Nontrivial G := by
    rcases (Subgroup.nontrivial_iff_ne_bot N).mpr hN with ⟨a, b, hab⟩
    exact ⟨(a : G), (b : G), fun h => hab (Subtype.ext h)⟩
  have hFne := inf_fitting_ne_bot_of_abelian_card_ge_index hA_ab
    (index_le_card_of_card_le hG hcon)
  exact hFne (le_bot_iff.mp
    ((inf_le_inf_left A (le_centralizer_of_inf_eq_bot
      (fitting_inf_eq_bot_of_fitting_eq_bot hFN))).trans hCA.le))

/-- **Isaacs Problem 2D.1(b)**. `G = NA` (`N ⊴ G`, `N ≠ 1`)、`C_A(N) = 1`、`A` 可換で
`|N|` と `|A|` が互いに素ならば `|A| < |N|`。

`|A| ≥ |N|` と仮定すると **Cor 2.19** で `A ⊓ F(G) ≠ 1`。`π := {q | q ∤ |N|}` とおくと
`A ⊓ F(G)` は π-群 (位数が `|A|` を割り、`|A|` は `|N|` と互いに素)。`F(G)` は冪零だから
`↥F(G)` の部分群はすべて部分正規 (Lemma 2.1) で、**2A.1**
(`le_oPiCore_of_isSubnormal_of_isPiGroup`) より `A ⊓ F(G)` は `O_π(↥F(G))` に含まれる。
`O_π` は特性的なので `G` へ押し出した `Q` は `G`-正規な π-群、`N` は π'-群だから
`Q ⊓ N = ⊥`、ゆえに `Q ≤ C_G(N)`。したがって `A ⊓ F(G) ≤ Q ≤ C_G(N)` となり
`A ⊓ F(G) ≤ A ⊓ C_G(N) = 1` で矛盾。 -/
theorem card_lt_card_of_coprime [Finite G] {N A : Subgroup G} [N.Normal]
    (hN : N ≠ ⊥) (hG : N ⊔ A = ⊤)
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCA : A ⊓ Subgroup.centralizer (N : Set G) = ⊥)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥A)) :
    Nat.card ↥A < Nat.card ↥N := by
  by_contra hcon
  push Not at hcon
  have : Nontrivial G := by
    rcases (Subgroup.nontrivial_iff_ne_bot N).mpr hN with ⟨a, b, hab⟩
    exact ⟨(a : G), (b : G), fun h => hab (Subtype.ext h)⟩
  have hFne := inf_fitting_ne_bot_of_abelian_card_ge_index hA_ab
    (index_le_card_of_card_le hG hcon)
  set π : Set ℕ := {q : ℕ | ¬ q ∣ Nat.card ↥N} with hπ
  -- `A ⊓ F(G)` は π-群 (位数が `|A|` を割り `|N|` と互いに素)
  have hAF_pi : Subgroup.IsPiGroup π (A ⊓ fitting G) := by
    intro q hq hqN
    have hqA : q ∣ Nat.card ↥A :=
      (Nat.mem_primeFactors.mp hq).2.1.trans (Subgroup.card_dvd_of_le inf_le_left)
    exact (Nat.mem_primeFactors.mp hq).1.one_lt.ne' (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqN hqA))
  -- `↥F(G)` は冪零ゆえ部分群はすべて部分正規、2A.1 で `O_π(↥F(G))` に落ちる
  have hfitnilp : Group.IsNilpotent ↥(fitting G) := fitting.isNilpotent
  have hcardeq : Nat.card ↥((A ⊓ fitting G).subgroupOf (fitting G)) = Nat.card ↥(A ⊓ fitting G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : A ⊓ fitting G ≤ fitting G)).toEquiv
  have hsn : ((A ⊓ fitting G).subgroupOf (fitting G)).IsSubnormal :=
    isSubnormal_of_isNilpotent_finite _
  have hle : (A ⊓ fitting G).subgroupOf (fitting G) ≤ oPiCore π ↥(fitting G) :=
    le_oPiCore_of_isSubnormal_of_isPiGroup hsn
      (fun q hq => hAF_pi q (by rwa [hcardeq] at hq))
  -- `Q := O_π(↥F(G))` の押し出しは `G`-正規な π-群
  set Q : Subgroup G := (oPiCore π ↥(fitting G)).map (fitting G).subtype with hQ
  have : Q.Normal := inferInstance
  have hQpi : Subgroup.IsPiGroup π Q := by
    intro q hq
    refine oPiCore.isPiGroup (G := ↥(fitting G)) π q ?_
    rwa [hQ, ← Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (fitting G).subtype_injective).toEquiv] at hq
  have hQN : Q ⊓ N = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(Q ⊓ N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥(Q ⊓ N))).ne'
    exact hQpi q (Nat.mem_primeFactors.mpr ⟨hq,
      hqdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
      (hqdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hAF_le : A ⊓ fitting G ≤ Q := by
    rw [hQ, ← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : A ⊓ fitting G ≤ fitting G)]
    exact Subgroup.map_mono hle
  refine hFne (le_bot_iff.mp ?_)
  calc A ⊓ fitting G
      ≤ A ⊓ Subgroup.centralizer (N : Set G) :=
        le_inf inf_le_left (hAF_le.trans (le_centralizer_of_inf_eq_bot hQN))
    _ = ⊥ := hCA

/-- **Isaacs Problem 2D.2**. `G = NA` (`N ⊴ G`, `N ≠ 1`)、`C_A(N) = 1`、`A ∩ N = 1` で
`A` が巡回ならば `|A| < |N|`。

`A ∩ N = 1` と `G = NA` から `|G : A| = |N|`。`core_G(A) ⊴ G` は `A` に含まれるので
`core_G(A) ⊓ N ≤ A ⊓ N = 1`、両者正規ゆえ `core_G(A) ≤ C_G(N)`、したがって
`core_G(A) ≤ A ⊓ C_G(N) = 1`。**Lucchini (Thm 2.20)** の
`|A : core_G(A)| < |G : A|` に代入して `|A| < |N|`。 -/
theorem card_lt_card_of_isCyclic [Finite G] {N A : Subgroup G} [N.Normal]
    (hN : N ≠ ⊥) (hG : N ⊔ A = ⊤) (hNA : N ⊓ A = ⊥)
    (hCA : A ⊓ Subgroup.centralizer (N : Set G) = ⊥)
    (hA_cyc : ∃ g : G, A = Subgroup.zpowers g) :
    Nat.card ↥A < Nat.card ↥N := by
  -- `A` は可換 (巡回)
  obtain ⟨g, rfl⟩ := hA_cyc
  have hA_ab : ∀ a ∈ Subgroup.zpowers g, ∀ b ∈ Subgroup.zpowers g, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact zpow_mul_comm g i j
  -- `A < ⊤` (さもなくば `N = N ⊓ A = ⊥`)
  have hAproper : Subgroup.zpowers g < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hN ?_
    rw [← hNA, h, inf_top_eq]
  -- `|G : A| = |N|`
  have hidx : (Subgroup.zpowers g).index = Nat.card ↥N := by
    have := index_mul_card_inf_eq_card_of_sup_eq_top hG
    rwa [hNA, Subgroup.card_bot, mul_one] at this
  -- `core_G(A) = ⊥`
  have hcore : (Subgroup.zpowers g).normalCore = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hCA, le_inf_iff]
    refine ⟨Subgroup.normalCore_le _, le_centralizer_of_inf_eq_bot ?_⟩
    refine le_bot_iff.mp ?_
    rw [← hNA, le_inf_iff]
    exact ⟨inf_le_right, (inf_le_left.trans (Subgroup.normalCore_le _))⟩
  -- Lucchini
  have hL := Ch04.lucchini_index_normalCore_lt_index hAproper hA_ab ⟨g, rfl⟩
  rwa [hcore, Subgroup.bot_subgroupOf, Subgroup.index_bot, hidx] at hL

end

end OddOrder.Isaacs.Ch02
