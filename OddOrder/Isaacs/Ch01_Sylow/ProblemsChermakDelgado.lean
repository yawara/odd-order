/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ChermakDelgado

/-!
# Isaacs Problems 1G (書籍 p. 43) — Chermak–Delgado 周辺

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1G の形式化
(campaign issue 1055)。§1G は Chermak–Delgado の定理 (Thm 1.41) と最大測度束 `L(G)`
(Thm 1.44) の節で, 本文の定理は `OddOrder/GroupTheory/ChermakDelgado.lean` に landing 済。

⚠ **文言は PDF ページ画像で確定** (`references/isaacs/pages/isaacs-p043-056.png`)。
pdftotext は `<` と `≤` を潰すが, **1G.1 と 1G.4 の不等号は厳密 `<`** である
(`≤` なら Thm 1.41 そのもので自明になってしまう)。

* **1G.1**: `A ≤ G` 可換で, `|G : N| < |G : A|²` なる特性可換部分群 `N` が存在しないなら,
  `A = C_G(A)` は `L(G)` に属し `|G : Z(G)| = |G : A|²`。
* **1G.2**: `H ∈ L(G)`, `H < G` なら `H ⊆ M < G` なる正規部分群 `M` が存在する。
* **1G.3**: `G` 単純, `H ≤ G`, `|H|·|C_G(H)| = |G|` なら `H = 1` または `H = G`。
* **1G.4**: `A ≤ G` 可換, `G` 非可換なら `|G : N| < |G : A|²` なる**正規**可換部分群 `N`
  が存在する。

これで **§1G は 1G.1–1G.4 全問完済** (したがって Isaacs Ch.1 の演習は §1A–§1G 全完済)。

## Main results

- `eq_centralizer_and_mem_lattice_of_no_smaller_characteristic` — **Problem 1G.1**。
- `card_conj_smul` / `centralizer_conj_smul` / `chermakDelgadoMeasure_conj_smul` /
  `chermakDelgadoLattice_conj_smul_mem` — **1G.2 の Hint 第 1 文**
  (`L(G)` は共役で閉じる) とその部品。
- `conj_smul_self_of_mem` — 部分群はその元による共役で不変。
- `exists_normal_lt_top_of_mem_lattice` — **Problem 1G.2**。
- `eq_bot_or_eq_top_of_chermakDelgadoMeasure_eq_card` — **Problem 1G.3**。
- `sInf_mem_lattice_and_centralizer_eq` — `L(G)` の有限族の交わりは `L(G)` に属し
  中心化群は各元の中心化群の `sSup` (Thm 1.44 の 2 元版の反復; 1G.4 の準備)。
- `exists_normal_isMulCommutative_index_lt` — **Problem 1G.4**。
-/

namespace OddOrder.Isaacs.Ch01

open Subgroup

section /- 1G: Problem 1G.1 (p. 43) -/

variable {G : Type*} [Group G] [Finite G]

/-- **Isaacs Problem 1G.1** (p. 43)。可換部分群 `A` について,
`|G : N| < |G : A|²` を満たす特性可換部分群 `N` が存在しないならば
`A = C_G(A)`, `A ∈ L(G)`, `|G : Z(G)| = |G : A|²` の 3 つが同時に成り立つ。

Thm 1.41 の証明の不等式の連鎖

  `|G : M| · |A|² ≤ |G : M| · m_G(A) ≤ |G : M| · m_G(M) = |G| · |C_G(M)| ≤ |G|²
     = |G : A|² · |A|²`

において, 仮定より `|G : M| = |G : A|²` (`M` = Chermak–Delgado 部分群) なので**全ての
不等号が等号**になる。それぞれの等号が

* `|A|² = m_G(A)` ⟹ `|C_G(A)| = |A|` ⟹ `A = C_G(A)`,
* `m_G(A) = m_G(M)` ⟹ `A ∈ L(G)`,
* `|C_G(M)| = |G|` ⟹ `C_G(M) = ⊤` ⟹ `M ≤ Z(G)`, `Z(G) ≤ M` と合わせて `M = Z(G)`

を与える。 -/
theorem eq_centralizer_and_mem_lattice_of_no_smaller_characteristic {A : Subgroup G}
    [IsMulCommutative A]
    (hno : ∀ N : Subgroup G, N.Characteristic → IsMulCommutative N →
      ¬ N.index < A.index ^ 2) :
    A = centralizer (A : Set G) ∧ A ∈ chermakDelgadoLattice G ∧
      (center G).index = A.index ^ 2 := by
  set M : Subgroup G := chermakDelgadoSubgroup G with hMdef
  have hMmem : M ∈ chermakDelgadoLattice G := chermakDelgadoSubgroup_mem_lattice
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hMipos : 0 < M.index := Nat.pos_of_ne_zero (by
    have := Subgroup.card_mul_index M
    intro hc
    rw [hc, mul_zero] at this
    omega)
  -- `|A| ≤ |C_G(A)|` から `|A|² ≤ m_G(A)`
  have hAle : Nat.card ↥A ≤ Nat.card ↥(centralizer (A : Set G)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion A.le_centralizer)
      (Subgroup.inclusion_injective _)
  have hAsq : Nat.card ↥A ^ 2 ≤ A.chermakDelgadoMeasure := by
    rw [chermakDelgadoMeasure_def, sq]
    exact Nat.mul_le_mul_left _ hAle
  have hAM : A.chermakDelgadoMeasure ≤ M.chermakDelgadoMeasure := hMmem A
  have hCM : Nat.card ↥(centralizer ((M : Subgroup G) : Set G)) ≤ Nat.card G :=
    Nat.le_of_dvd hGpos (Subgroup.card_subgroup_dvd_card _)
  have hGM : Nat.card ↥M * M.index = Nat.card G := Subgroup.card_mul_index M
  have hGA : Nat.card ↥A * A.index = Nat.card G := Subgroup.card_mul_index A
  -- 連鎖の各段
  have e1 : M.index * Nat.card ↥A ^ 2 ≤ M.index * A.chermakDelgadoMeasure :=
    Nat.mul_le_mul_left _ hAsq
  have e2 : M.index * A.chermakDelgadoMeasure ≤ M.index * M.chermakDelgadoMeasure :=
    Nat.mul_le_mul_left _ hAM
  have e3 : M.index * M.chermakDelgadoMeasure
      = Nat.card G * Nat.card ↥(centralizer ((M : Subgroup G) : Set G)) := by
    rw [chermakDelgadoMeasure_def, ← mul_assoc, mul_comm M.index, hGM]
  have e4 : Nat.card G * Nat.card ↥(centralizer ((M : Subgroup G) : Set G))
      ≤ Nat.card G * Nat.card G := Nat.mul_le_mul_left _ hCM
  have hGsq : Nat.card G * Nat.card G = A.index ^ 2 * Nat.card ↥A ^ 2 := by
    rw [← hGA]; ring
  -- `|G : M| ≤ |G : A|²`, 仮定より等号
  have hle : M.index ≤ A.index ^ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hApos 2)
    calc M.index * Nat.card ↥A ^ 2 ≤ Nat.card G * Nat.card G := by omega
      _ = A.index ^ 2 * Nat.card ↥A ^ 2 := hGsq
  have heq : M.index = A.index ^ 2 := by
    have := hno M inferInstance inferInstance
    omega
  -- 等号なので連鎖は全て等号
  have hall : M.index * Nat.card ↥A ^ 2 = Nat.card G * Nat.card G := by
    rw [hGsq, heq]
  have hAsq' : Nat.card ↥A ^ 2 = A.chermakDelgadoMeasure := by
    have : M.index * Nat.card ↥A ^ 2 = M.index * A.chermakDelgadoMeasure := by omega
    exact Nat.eq_of_mul_eq_mul_left hMipos this
  have hAM' : A.chermakDelgadoMeasure = M.chermakDelgadoMeasure := by
    have : M.index * A.chermakDelgadoMeasure = M.index * M.chermakDelgadoMeasure := by omega
    exact Nat.eq_of_mul_eq_mul_left hMipos this
  have hCM' : Nat.card ↥(centralizer ((M : Subgroup G) : Set G)) = Nat.card G := by
    have : Nat.card G * Nat.card ↥(centralizer ((M : Subgroup G) : Set G))
        = Nat.card G * Nat.card G := by omega
    exact Nat.eq_of_mul_eq_mul_left hGpos this
  refine ⟨?_, ?_, ?_⟩
  · -- `A = C_G(A)`
    refine Subgroup.eq_of_le_of_card_ge A.le_centralizer (le_of_eq ?_)
    have : Nat.card ↥A * Nat.card ↥A
        = Nat.card ↥A * Nat.card ↥(centralizer (A : Set G)) := by
      rw [← sq, hAsq', chermakDelgadoMeasure_def]
    exact (Nat.eq_of_mul_eq_mul_left hApos this).symm
  · -- `A ∈ L(G)`
    intro K
    exact hAM' ▸ hMmem K
  · -- `M = Z(G)`
    have hCtop : centralizer ((M : Subgroup G) : Set G) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ hCM'
    have hMZ : M ≤ center G :=
      Subgroup.centralizer_eq_top_iff_subset.mp hCtop
    have hZM : M = center G := le_antisymm hMZ center_le_chermakDelgadoSubgroup
    rw [← hZM]; exact heq

end -- Problem 1G.1

section /- 1G: `L(G)` は共役で閉じる (1G.2 の Hint 第 1 文) -/

open Pointwise

variable {G : Type*} [Group G]

/-- 共役は部分群の位数を変えない。 -/
theorem card_conj_smul (g : G) (S : Subgroup G) :
    Nat.card ↥(MulAut.conj g • S) = Nat.card ↥S :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

/-- 共役部分群の中心化群は中心化群の共役: `C_G(gHg⁻¹) = g C_G(H) g⁻¹`。 -/
theorem centralizer_conj_smul (g : G) (H : Subgroup G) :
    (centralizer ((MulAut.conj g • H : Subgroup G) : Set G) : Subgroup G)
      = MulAut.conj g • (centralizer (H : Set G) : Subgroup G) := by
  ext u
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hu
    refine (Subgroup.mem_smul_pointwise_iff_exists u (MulAut.conj g) _).mpr
      ⟨g⁻¹ * u * g, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_,
        by change g * (g⁻¹ * u * g) * g⁻¹ = u; group⟩
    have hmem : g * w * g⁻¹ ∈ (MulAut.conj g • H : Subgroup G) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) H).mpr ⟨w, hw, rfl⟩
    have hc := hu _ hmem
    calc w * (g⁻¹ * u * g) = g⁻¹ * ((g * w * g⁻¹) * u) * g := by group
      _ = g⁻¹ * (u * (g * w * g⁻¹)) * g := by rw [hc]
      _ = (g⁻¹ * u * g) * w := by group
  · intro hu h hh
    obtain ⟨v, hv, hvu⟩ := (Subgroup.mem_smul_pointwise_iff_exists u (MulAut.conj g) _).mp hu
    obtain ⟨w, hw, hwh⟩ := (Subgroup.mem_smul_pointwise_iff_exists h (MulAut.conj g) H).mp hh
    have hc : w * v = v * w := Subgroup.mem_centralizer_iff.mp hv w hw
    have hu' : u = g * v * g⁻¹ := hvu.symm
    have hh' : h = g * w * g⁻¹ := hwh.symm
    rw [hu', hh']
    calc (g * w * g⁻¹) * (g * v * g⁻¹) = g * (w * v) * g⁻¹ := by group
      _ = g * (v * w) * g⁻¹ := by rw [hc]
      _ = (g * v * g⁻¹) * (g * w * g⁻¹) := by group

/-- 共役は Chermak–Delgado 測度を変えない。 -/
theorem chermakDelgadoMeasure_conj_smul (g : G) (H : Subgroup G) :
    (MulAut.conj g • H).chermakDelgadoMeasure = H.chermakDelgadoMeasure := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def, centralizer_conj_smul,
    card_conj_smul, card_conj_smul]

/-- **1G.2 の Hint 第 1 文**: 最大測度束 `L(G)` は共役で閉じている。 -/
theorem chermakDelgadoLattice_conj_smul_mem {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (g : G) :
    MulAut.conj g • H ∈ chermakDelgadoLattice G := by
  intro K
  rw [chermakDelgadoMeasure_conj_smul]
  exact hH K

/-- 部分群はその元による共役で不変。 -/
theorem conj_smul_self_of_mem {H : Subgroup G} {y : G} (hy : y ∈ H) :
    MulAut.conj y • H = H := by
  ext u
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem hy hv) (H.inv_mem hy)
  · intro hu
    exact ⟨y⁻¹ * u * y, H.mul_mem (H.mul_mem (H.inv_mem hy) hu) hy,
      by change y * (y⁻¹ * u * y) * y⁻¹ = u; group⟩

end -- `L(G)` は共役で閉じる

section /- 1G: Problem 1G.2 (p. 43) -/

open Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- **Isaacs Problem 1G.2** (p. 43)。`H ∈ L(G)` が `G` の真の部分群なら,
`H ⊆ M < G` を満たす正規部分群 `M` が存在する。

背理法。`H` を含む `L(G)` の真の部分群のうち位数最大のものを `K` とする。

* 全ての共役 `gHg⁻¹` が `K` に含まれるなら, `H` の正規閉包が `K < ⊤` に収まり,
  それが求める `M` になってしまう (仮定に反する)。
* そうでない共役 `H' := gHg⁻¹` を取ると `K ⊔ H' ∈ L(G)` は `H` を含み `K` を真に含むので,
  `K` の最大性から `K ⊔ H' = ⊤`。**Thm 1.44** (`chermakDelgadoLattice_sup_eq_mul`) より
  `⊤ = K · H'` なので `g⁻¹ = k y` (`k ∈ K`, `y ∈ H'`) と書ける。`y` は `H'` を正規化するから
  `H = g⁻¹ H' g = k H' k⁻¹`, ゆえに `H' = k⁻¹ H k ≤ K` で `H' ⊄ K` に矛盾。 -/
theorem exists_normal_lt_top_of_mem_lattice {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hlt : H < ⊤) :
    ∃ M : Subgroup G, M.Normal ∧ H ≤ M ∧ M < ⊤ := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  -- `H` を含む `L(G)` の真の部分群のうち位数最大のもの
  obtain ⟨K, hKmem, hKmax⟩ :=
    (Finset.univ.filter (fun X : Subgroup G =>
        X ∈ chermakDelgadoLattice G ∧ H ≤ X ∧ X < ⊤)).exists_max_image
      (fun X => Nat.card ↥X)
      ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH, le_refl _, hlt⟩⟩
  obtain ⟨hKL, hHK, hKtop⟩ := (Finset.mem_filter.mp hKmem).2
  -- `K` に含まれない共役が存在する
  have hex : ∃ g : G, ¬ (MulAut.conj g • H ≤ K) := by
    by_contra hall
    push Not at hall
    have hnc : Subgroup.normalClosure (H : Set G) ≤ K := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro y hy
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      exact hall c (hc ▸ (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj c) H).mpr
        ⟨a, ha, rfl⟩)
    exact hcon (Subgroup.normalClosure (H : Set G)) inferInstance
      Subgroup.subset_normalClosure (lt_of_le_of_lt hnc hKtop)
  obtain ⟨g, hg⟩ := hex
  set H' : Subgroup G := MulAut.conj g • H with hH'def
  have hH'L : H' ∈ chermakDelgadoLattice G := chermakDelgadoLattice_conj_smul_mem hH g
  have hsupL : K ⊔ H' ∈ chermakDelgadoLattice G := chermakDelgadoLattice_sup_mem hKL hH'L
  -- `K < K ⊔ H'` なので最大性から `K ⊔ H' = ⊤`
  have hKlt : K < K ⊔ H' := lt_of_le_of_ne le_sup_left fun hc => hg (hc ▸ le_sup_right)
  have hsuptop : K ⊔ H' = ⊤ := by
    by_contra hne
    have hmem : K ⊔ H' ∈ Finset.univ.filter (fun X : Subgroup G =>
        X ∈ chermakDelgadoLattice G ∧ H ≤ X ∧ X < ⊤) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupL, hHK.trans le_sup_left,
        lt_of_le_of_ne le_top hne⟩
    have hcard : Nat.card ↥(K ⊔ H') ≤ Nat.card ↥K := hKmax _ hmem
    exact absurd (Subgroup.eq_of_le_of_card_ge le_sup_left hcard) hKlt.ne
  -- `⊤ = K · H'` から `g⁻¹ = k y`
  have hprod : ((⊤ : Subgroup G) : Set G) = (K : Set G) * (H' : Set G) := by
    rw [← hsuptop]; exact chermakDelgadoLattice_sup_eq_mul hKL hH'L
  obtain ⟨k, hk, y, hy, hky0⟩ : g⁻¹ ∈ (K : Set G) * (H' : Set G) := by
    rw [← hprod]; exact Subgroup.mem_top _
  have hky : k * y = g⁻¹ := hky0
  -- `H = k H' k⁻¹`
  have hHconj : H = MulAut.conj k • H' := by
    have h1 : MulAut.conj g⁻¹ • H' = H := by
      rw [hH'def, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [← h1, ← hky, map_mul, ← smul_smul, conj_smul_self_of_mem hy]
  -- したがって `H' ≤ K` で矛盾
  refine hg ?_
  have : H' = MulAut.conj k⁻¹ • H := by
    rw [hHconj, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [this]
  calc MulAut.conj k⁻¹ • H ≤ MulAut.conj k⁻¹ • K :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hHK
    _ = K := conj_smul_self_of_mem (K.inv_mem hk)

end -- Problem 1G.2

section /- 1G: Problem 1G.3 (p. 43) -/

variable {G : Type*} [Group G] [Finite G]

/-- **Isaacs Problem 1G.3** (p. 43)。`G` が単純で `|H|·|C_G(H)| = |G|` なら
`H = 1` または `H = G`。

* `G` が可換なら全ての部分群が正規なので単純性から直ちに従う。
* `G` が非可換なら, **Cor 1.46**
  (`not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt`) より
  どの部分群も測度が `|G|` を超えられないので `m_G(H) = |G|` は最大値, つまり
  `H ∈ L(G)`。**1G.2** より `H` が真の部分群なら真の正規部分群に含まれるが,
  単純性からそれは `⊥` しかない。 -/
theorem eq_bot_or_eq_top_of_chermakDelgadoMeasure_eq_card [IsSimpleGroup G] {H : Subgroup G}
    (h : H.chermakDelgadoMeasure = Nat.card G) : H = ⊥ ∨ H = ⊤ := by
  by_cases hab : IsMulCommutative G
  · -- 可換なら全部分群が正規
    have : H.Normal := ⟨fun n hn g => by
      rw [show g * n * g⁻¹ = n from by
        rw [isMulCommutative_iff.mp hab g n]; group]
      exact hn⟩
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H inferInstance
  · -- 非可換なら `H ∈ L(G)`
    have hHL : H ∈ chermakDelgadoLattice G := by
      intro K
      rw [h]
      by_contra hgt
      push Not at hgt
      exact not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt hgt ⟨inferInstance, hab⟩
    rcases eq_or_lt_of_le (le_top : H ≤ ⊤) with htop | hlt
    · exact Or.inr htop
    · obtain ⟨M, hMnorm, hHM, hMlt⟩ := exists_normal_lt_top_of_mem_lattice hHL hlt
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M hMnorm with hM | hM
      · exact Or.inl (le_bot_iff.mp (hM ▸ hHM))
      · exact absurd hM hMlt.ne

end -- Problem 1G.3

section /- 1G: `L(G)` の有限族の交わり (1G.4 の準備) -/

variable {G : Type*} [Group G] [Finite G]

/-- **Thm 1.44 の 2 元版の反復**。`L(G)` の元からなる有限で空でない族 `S` について,
`sInf S` は `L(G)` に属し, その中心化群は各元の中心化群の `sSup` に等しい。

`chermakDelgadoLattice_inf_mem` と `chermakDelgadoLattice_centralizer_inf_eq_mul`
(`C_G(H ⊓ K) = C_G(H)·C_G(K)`) を `Set.Finite.induction_on` で回す。積が join になるのは
`chermakDelgadoLattice_sup_eq_mul` (両者が `L(G)` に属すため)。 -/
theorem sInf_mem_lattice_and_centralizer_eq (S : Set (Subgroup G)) (hfin : S.Finite) :
    S.Nonempty → S ⊆ chermakDelgadoLattice G →
      sInf S ∈ chermakDelgadoLattice G ∧
        (centralizer ((sInf S : Subgroup G) : Set G) : Subgroup G)
          = sSup ((fun H : Subgroup G => (centralizer (H : Set G) : Subgroup G)) '' S) := by
  induction S, hfin using Set.Finite.induction_on with
  | empty => intro hne _; exact (Set.not_nonempty_empty hne).elim
  | @insert a t hat ht_fin ih =>
    intro _hne hsub
    have ha : a ∈ chermakDelgadoLattice G := hsub (Set.mem_insert _ _)
    rcases t.eq_empty_or_nonempty with rfl | ht_ne
    · refine ⟨?_, ?_⟩
      · rw [Set.insert_eq, Set.union_empty, sInf_singleton]; exact ha
      · rw [Set.insert_eq, Set.union_empty, sInf_singleton, Set.image_singleton, sSup_singleton]
    · have hsub_t : t ⊆ chermakDelgadoLattice G :=
        fun H hH => hsub (Set.mem_insert_of_mem _ hH)
      obtain ⟨hIt, hCt⟩ := ih ht_ne hsub_t
      have hCa : (centralizer (a : Set G) : Subgroup G) ∈ chermakDelgadoLattice G :=
        chermakDelgadoLattice_centralizer_mem ha
      have hCIt : (centralizer ((sInf t : Subgroup G) : Set G) : Subgroup G)
          ∈ chermakDelgadoLattice G := chermakDelgadoLattice_centralizer_mem hIt
      refine ⟨?_, ?_⟩
      · rw [sInf_insert]; exact chermakDelgadoLattice_inf_mem ha hIt
      · rw [sInf_insert, Set.image_insert_eq, sSup_insert, ← hCt]
        refine SetLike.coe_injective ?_
        rw [chermakDelgadoLattice_centralizer_inf_eq_mul ha hIt,
          chermakDelgadoLattice_sup_eq_mul hCa hCIt]

end -- `L(G)` の有限族の交わり

section /- 1G: Problem 1G.4 (p. 43) -/

open Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- **Isaacs Problem 1G.4** (p. 43)。`G` が非可換で `A ≤ G` が可換なら,
`|G : N| < |G : A|²` を満たす**正規**可換部分群 `N` が存在する。

背理法。そのような `N` が無いなら特性可換なものも無いので **1G.1** より
`A = C_G(A) ∈ L(G)`。`G` 非可換ゆえ `A < ⊤` で, **1G.2** から `A ⊆ M' < ⊤` なる正規 `M'`
が取れる。ここで `N := ⋂_g gAg⁻¹` (共役全体の交わり) を取ると:

* 共役全体 `S` は `L(G)` に含まれる (`chermakDelgadoLattice_conj_smul_mem`) ので
  `N ∈ L(G)` かつ `C_G(N) = sSup S` (`sInf_mem_lattice_and_centralizer_eq`)。
  ここで `C_G(gAg⁻¹) = g C_G(A) g⁻¹ = gAg⁻¹` (`centralizer_conj_smul` + `A = C_G(A)`)
  なので `C_G '' S = S` となるのが鍵。
* `A ≤ M'` と `M'` の正規性から `sSup S ≤ M' < ⊤`, つまり `|C_G(N)| < |G|`。
* `N ≤ A` ゆえ可換, `S` が共役で閉じるので `N` は正規。
* `N ∈ L(G)` の測度等式 `|N|·|C_G(N)| = m(N) = m(A) = |A|²` と `|C_G(N)| < |G|` から
  `|G:N|·|A|² = |G|·|C_G(N)| < |G|² = |G:A|²·|A|²`, すなわち `|G:N| < |G:A|²`。 -/
theorem exists_normal_isMulCommutative_index_lt {A : Subgroup G} [hA : IsMulCommutative A]
    (hG : ¬ IsMulCommutative G) :
    ∃ N : Subgroup G, N.Normal ∧ IsMulCommutative N ∧ N.index < A.index ^ 2 := by
  classical
  by_contra hcon
  have hno : ∀ N : Subgroup G, N.Normal → IsMulCommutative N → ¬ N.index < A.index ^ 2 :=
    fun N h1 h2 h3 => hcon ⟨N, h1, h2, h3⟩
  obtain ⟨hCA, hAL, -⟩ := eq_centralizer_and_mem_lattice_of_no_smaller_characteristic
    (A := A) (fun N hchar hab => hno N (by have := hchar; infer_instance) hab)
  -- `G` 非可換なので `A < ⊤`
  have hAlt : A < ⊤ := by
    refine lt_of_le_of_ne le_top fun hc => hG (isMulCommutative_iff.mpr fun x y => ?_)
    have hx : x ∈ A := by rw [hc]; exact Subgroup.mem_top x
    have hy : y ∈ A := by rw [hc]; exact Subgroup.mem_top y
    exact congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨M', hM'norm, hAM', hM'lt⟩ := exists_normal_lt_top_of_mem_lattice hAL hAlt
  -- 共役全体 `S` とその交わり `N`
  set S : Set (Subgroup G) := Set.range (fun g : G => MulAut.conj g • A) with hSdef
  have hAS : A ∈ S := ⟨1, by simp⟩
  have hSsub : S ⊆ chermakDelgadoLattice G := by
    intro H hH
    rw [hSdef] at hH
    obtain ⟨g, rfl⟩ := hH
    exact chermakDelgadoLattice_conj_smul_mem hAL g
  obtain ⟨hNL, hCN⟩ :=
    sInf_mem_lattice_and_centralizer_eq S (Set.toFinite _) ⟨A, hAS⟩ hSsub
  set N : Subgroup G := sInf S with hNdef
  -- `C_G '' S = S`
  have hconjC : ∀ g : G, (centralizer ((MulAut.conj g • A : Subgroup G) : Set G) : Subgroup G)
      = MulAut.conj g • A := by
    intro g; rw [centralizer_conj_smul, ← hCA]
  have himg : (fun H : Subgroup G => (centralizer (H : Set G) : Subgroup G)) '' S = S := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro X ⟨H, hH, rfl⟩
      rw [hSdef] at hH ⊢
      obtain ⟨g, rfl⟩ := hH
      exact ⟨g, (hconjC g).symm⟩
    · intro X hX
      refine ⟨X, hX, ?_⟩
      rw [hSdef] at hX
      obtain ⟨g, rfl⟩ := hX
      exact hconjC g
  rw [himg] at hCN
  -- `C_G(N) = sSup S ≤ M' < ⊤`
  have hSupM : sSup S ≤ M' := by
    refine sSup_le fun H hH => ?_
    rw [hSdef] at hH
    obtain ⟨g, rfl⟩ := hH
    intro u hu
    obtain ⟨a, ha, hau⟩ := (Subgroup.mem_smul_pointwise_iff_exists u (MulAut.conj g) A).mp hu
    rw [← hau]
    exact hM'norm.conj_mem _ (hAM' ha) g
  have hCNlt : Nat.card ↥(centralizer ((N : Subgroup G) : Set G)) < Nat.card G := by
    have hne : (centralizer ((N : Subgroup G) : Set G) : Subgroup G) ≠ ⊤ := by
      rw [hCN]
      intro hc
      exact hM'lt.ne (le_antisymm le_top (hc ▸ hSupM))
    rcases lt_or_eq_of_le (Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_subgroup_dvd_card
        (centralizer ((N : Subgroup G) : Set G) : Subgroup G))) with h | h
    · exact h
    · exact absurd (Subgroup.eq_top_of_card_eq _ h) hne
  -- `N` は可換かつ正規
  have hNA : N ≤ A := sInf_le hAS
  have hNcomm : IsMulCommutative N := isMulCommutative_iff.mpr fun x y => by
    have h := isMulCommutative_iff.mp hA ⟨(x : G), hNA x.2⟩ ⟨(y : G), hNA y.2⟩
    have h' : (x : G) * (y : G) = (y : G) * (x : G) := congrArg Subtype.val h
    exact Subtype.ext h'
  have hNnorm : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [hNdef, Subgroup.mem_sInf] at hn ⊢
    intro H hH
    rw [hSdef] at hH
    obtain ⟨g, rfl⟩ := hH
    have hmem : n ∈ MulAut.conj (x⁻¹ * g) • A :=
      hn _ (by rw [hSdef]; exact ⟨x⁻¹ * g, rfl⟩)
    obtain ⟨a, ha, han⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists n (MulAut.conj (x⁻¹ * g)) A).mp hmem
    refine (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) A).mpr ⟨a, ha, ?_⟩
    have han' : (x⁻¹ * g) * a * (x⁻¹ * g)⁻¹ = n := han
    change g * a * g⁻¹ = x * n * x⁻¹
    rw [← han']
    group
  -- 測度等式から指数の評価
  have hmA : A.chermakDelgadoMeasure = Nat.card ↥A ^ 2 := by
    rw [chermakDelgadoMeasure_def, ← hCA, sq]
  have hmN : N.chermakDelgadoMeasure = Nat.card ↥A ^ 2 := by
    rw [← hmA]; exact le_antisymm (hAL N) (hNL A)
  have hGN : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hGA : Nat.card ↥A * A.index = Nat.card G := Subgroup.card_mul_index A
  refine hno N hNnorm hNcomm (lt_of_mul_lt_mul_right ?_ (Nat.zero_le (Nat.card ↥A ^ 2)))
  calc N.index * Nat.card ↥A ^ 2
      = N.index * N.chermakDelgadoMeasure := by rw [hmN]
    _ = N.index * (Nat.card ↥N * Nat.card ↥(centralizer ((N : Subgroup G) : Set G))) := by
        rw [chermakDelgadoMeasure_def]
    _ = Nat.card G * Nat.card ↥(centralizer ((N : Subgroup G) : Set G)) := by
        rw [← mul_assoc, mul_comm N.index, hGN]
    _ < Nat.card G * Nat.card G := mul_lt_mul_of_pos_left hCNlt Nat.card_pos
    _ = A.index ^ 2 * Nat.card ↥A ^ 2 := by rw [← hGA]; ring

end -- Problem 1G.4

end OddOrder.Isaacs.Ch01
