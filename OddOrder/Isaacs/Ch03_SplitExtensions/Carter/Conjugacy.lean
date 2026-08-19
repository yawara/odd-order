/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Carter.QuotientTransfer
import OddOrder.Isaacs.Ch03_SplitExtensions.Carter.MinimalNormal

/-!
# Isaacs Problem 3C.7(b) — Carter 部分群の共役性

有限可解群の 2 つの Carter 部分群は共役である。書籍は証明を与えない (challenge problem)
ので証明は自前 (設計は issue 1055 の「3C.7 の設計」節)。

証明は `|G|` に関する強帰納で、極小正規部分群 `N` (可換, elementary abelian) を取って
`G ⧸ N` に降りる。本ファイルはその各ステップを、**帰納法の仮説を明示的な引数に取る
独立補題**として積み上げる (Lean の強帰納を 1 本の巨大な証明にしないため)。

## 帰納法の骨格

`C`, `D` を `G` の Carter 部分群、`N` を極小正規部分群とする。

1. `normalizer_sup_eq_self_of_ih` — **`N_G(C ⊔ N) = C ⊔ N`**。`g` が `C ⊔ N` を正規化すれば
   `C` と `C^g` はともに `C ⊔ N` の Carter 部分群なので、`C ⊔ N < G` のとき帰納法の仮説で
   `C ⊔ N` 内共役、それを `N_G(C) = C` に流し込むと `g ∈ C ⊔ N`。
2. ⟹ `(C ⊔ N)/N` は `G/N` の Carter 部分群 (`isCarterSubgroup_map_mk'_of_ih`)。
3. `G/N` で帰納法の仮説 ⟹ `C ⊔ N` と `D ⊔ N` は `G` 内共役。`D` を取り替えて
   `C ⊔ N = D ⊔ N =: K` としてよい。
4. `K < G` なら `K` 内で帰納法の仮説。`K = G` の場合が本丸で、`C ⊓ N` の極小性に
   よる場合分けの後、`G` の Sylow `p` `P` (`N ≤ P`, `P ⊴ G`) と `C` の Hall `p'` 部分に
   分けて `C = C_P(Q) · Q = D` を示す。

## Main results

- `normalizer_sup_eq_self_of_ih` — 上記 step 1。
- `isCarterSubgroup_map_mk'_of_ih` — 上記 step 2。
- `exists_conj_sup_eq_sup_of_ih` — 上記 step 3。
- `exists_conj_of_isCarterSubgroup` — **3C.7(b) 本体** (2 つの Carter 部分群は共役)。
-/

namespace OddOrder.Isaacs.Ch03

open _root_.OddOrder.Isaacs.Ch03.Subgroup Pointwise

section /- 3C.7(b): Carter 部分群の共役性 -/

universe u

variable {G : Type*} [Group G]

/-- **3C.7(b) step 1**: `C` が `G` の Carter 部分群, `N ⊴ G` のとき `N_G(C ⊔ N) = C ⊔ N`。

`g ∈ N_G(C ⊔ N)` とすると `C` と `C^g` はともに `↥(C ⊔ N)` の Carter 部分群
(`IsCarterSubgroup.subgroupOf`)。`C ⊔ N = ⊤` なら結論は自明。そうでなければ
`|↥(C ⊔ N)| < |G|` なので帰納法の仮説が使え, `↥(C ⊔ N)` 内の元 `y` で `C^y = C^g`。
すると `C^(g⁻¹ y) = C` すなわち `g⁻¹ y ∈ N_G(C) = C ≤ C ⊔ N`、`y ∈ C ⊔ N` と
合わせて `g ∈ C ⊔ N`。

帰納法の仮説 `IH` は「`|H| < |G|` なる可解群 `H` の Carter 部分群は共役」。 -/
theorem normalizer_sup_eq_self_of_ih {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (IH : ∀ {H : Type u} [Group H] [Finite H] [Group.IsSolvable H] (C' D' : Subgroup H),
      Nat.card H < Nat.card G → IsCarterSubgroup C' → IsCarterSubgroup D' →
      ∃ h : H, C'.map (MulAut.conj h).toMonoidHom = D')
    {C : Subgroup G} (hC : IsCarterSubgroup C) (N : Subgroup G) [N.Normal] :
    Subgroup.normalizer ((C ⊔ N : Subgroup G) : Set G) = C ⊔ N := by
  set K : Subgroup G := C ⊔ N with hK
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  by_cases hKtop : K = ⊤
  · rw [hKtop]; trivial
  -- `|↥K| < |G|` since `K ≠ ⊤`.
  have hKlt : Nat.card ↥K < Nat.card G := by
    classical
    obtain ⟨x, hx⟩ : ∃ x : G, x ∉ K := by
      simpa [Subgroup.eq_top_iff'] using hKtop
    exact Finite.card_subtype_lt (x := x) hx
  have hCK : C ≤ K := le_sup_left
  -- `C^g ≤ K` and both `C`, `C^g` are Carter in `↥K`.
  have hCgK : C.map (MulAut.conj g).toMonoidHom ≤ K := map_conj_le_of_mem_normalizer hCK hg
  have hCarterC : IsCarterSubgroup (C.subgroupOf K) := hC.subgroupOf hCK
  have hCarterCg : IsCarterSubgroup ((C.map (MulAut.conj g).toMonoidHom).subgroupOf K) :=
    (hC.map_conj g).subgroupOf hCgK
  have : Group.IsSolvable ↥K := inferInstance
  obtain ⟨y, hy⟩ := IH (C.subgroupOf K) ((C.map (MulAut.conj g).toMonoidHom).subgroupOf K)
    hKlt hCarterC hCarterCg
  -- Translate the conjugacy back to `G`.
  rw [map_conj_eq_iff_subgroupOf hCK hCgK y] at hy
  -- `C^(g⁻¹ * y) = C`, so `g⁻¹ * y ∈ N_G(C) = C ≤ K`.
  have hgy : C.map (MulAut.conj (g⁻¹ * (y : G))).toMonoidHom = C := by
    rw [← map_conj_trans, hy, map_conj_trans, inv_mul_cancel, map_conj_one]
  have hmem : g⁻¹ * (y : G) ∈ C := by
    rw [← hC.normalizer_eq]
    exact map_conj_eq_self_iff_mem_normalizer.mp hgy
  have : g⁻¹ ∈ K := by
    have := K.mul_mem (hCK hmem) (K.inv_mem y.2)
    simpa [mul_assoc] using this
  simpa using K.inv_mem this

/-- **3C.7(b) step 2**: `C ⊔ N` は `N` を含み自己正規化なので, その像 `(C ⊔ N)/N` は
`G/N` の Carter 部分群。

冪零性は `(C ⊔ N)/N = C/N` (`sup_map_mk'_eq_map_mk'`) と `C` の冪零性の像
(`isNilpotent_map_of_isNilpotent`), 自己正規化性は step 1 を対応定理
(`normalizer_eq_iff_map_mk'`) で商へ送る。 -/
theorem isCarterSubgroup_map_mk'_of_ih {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (IH : ∀ {H : Type u} [Group H] [Finite H] [Group.IsSolvable H] (C' D' : Subgroup H),
      Nat.card H < Nat.card G → IsCarterSubgroup C' → IsCarterSubgroup D' →
      ∃ h : H, C'.map (MulAut.conj h).toMonoidHom = D')
    {C : Subgroup G} (hC : IsCarterSubgroup C) (N : Subgroup G) [N.Normal] :
    IsCarterSubgroup ((C ⊔ N).map (QuotientGroup.mk' N)) := by
  refine ⟨?_, ?_⟩
  · rw [sup_map_mk'_eq_map_mk']
    exact isNilpotent_map_of_isNilpotent hC.1 _
  · exact (normalizer_eq_iff_map_mk' (C ⊔ N) le_sup_right).mpr
      (normalizer_sup_eq_self_of_ih IH hC N)

/-- **3C.7(b) step 3**: `N ≠ ⊥` のとき, `C` を適当に共役して `C ⊔ N = D ⊔ N` にできる。

`G/N` は `|G|` より小さいので帰納法の仮説が使え, step 2 の 2 つの Carter 部分群
`(C ⊔ N)/N`, `(D ⊔ N)/N` が `G/N` 内で共役。それを `exists_conj_of_map_mk'_conj` で
`G` に引き戻すと `(C ⊔ N)^g = D ⊔ N`, `N` は正規なので左辺は `C^g ⊔ N`。 -/
theorem exists_conj_sup_eq_sup_of_ih {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (IH : ∀ {H : Type u} [Group H] [Finite H] [Group.IsSolvable H] (C' D' : Subgroup H),
      Nat.card H < Nat.card G → IsCarterSubgroup C' → IsCarterSubgroup D' →
      ∃ h : H, C'.map (MulAut.conj h).toMonoidHom = D')
    {C D : Subgroup G} (hC : IsCarterSubgroup C) (hD : IsCarterSubgroup D)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    ∃ g : G, C.map (MulAut.conj g).toMonoidHom ⊔ N = D ⊔ N := by
  obtain ⟨q, hq⟩ := IH ((C ⊔ N).map (QuotientGroup.mk' N)) ((D ⊔ N).map (QuotientGroup.mk' N))
    (card_quotient_lt hN) (isCarterSubgroup_map_mk'_of_ih IH hC N)
    (isCarterSubgroup_map_mk'_of_ih IH hD N)
  obtain ⟨g, hg⟩ := exists_conj_of_map_mk'_conj (K₁ := C ⊔ N) (K₂ := D ⊔ N)
    le_sup_right le_sup_right ⟨q, hq⟩
  refine ⟨g, ?_⟩
  have hNconj : N.map (MulAut.conj g).toMonoidHom = N := Subgroup.Normal.map_conj_eq N g
  rw [← hg, Subgroup.map_sup, hNconj]

/-- 3C.7(b) の `|G|` 強帰納本体。型を量化して 1 段ずつ小さい群へ降りる。 -/
private theorem exists_conj_aux : ∀ (n : ℕ) {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (C D : Subgroup G), Nat.card G ≤ n → IsCarterSubgroup C → IsCarterSubgroup D →
    ∃ g : G, C.map (MulAut.conj g).toMonoidHom = D := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ C D hcard _ _
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ C D hcard hC hD
    have IH : ∀ {H : Type u} [Group H] [Finite H] [Group.IsSolvable H] (C' D' : Subgroup H),
        Nat.card H < Nat.card G → IsCarterSubgroup C' → IsCarterSubgroup D' →
        ∃ h : H, C'.map (MulAut.conj h).toMonoidHom = D' := fun C' D' hlt hC' hD' =>
      ih C' D' (Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hcard)) hC' hD'
    by_cases hGtriv : (⊤ : Subgroup G) = ⊥
    · -- `G` が自明なら `C = ⊥ = D`。
      have hCbot : C = ⊥ := le_bot_iff.mp (by rw [← hGtriv]; exact le_top)
      have hDbot : D = ⊥ := le_bot_iff.mp (by rw [← hGtriv]; exact le_top)
      exact ⟨1, by rw [map_conj_one, hCbot, hDbot]⟩
    -- 極小正規部分群 `N` を取る。
    obtain ⟨N, hN, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) hGtriv
    have := hN.1
    -- step 3: `C` を共役して `C₀ ⊔ N = D ⊔ N` にする。
    obtain ⟨g₀, hg₀⟩ := exists_conj_sup_eq_sup_of_ih IH hC hD N hN.2.1
    have hC₀ : IsCarterSubgroup (C.map (MulAut.conj g₀).toMonoidHom) := hC.map_conj g₀
    by_cases hKtop : C.map (MulAut.conj g₀).toMonoidHom ⊔ N = ⊤
    · -- step 4: `C₀ ⊔ N = D ⊔ N = ⊤`。
      have hDNtop : D ⊔ N = ⊤ := by rw [← hg₀]; exact hKtop
      obtain ⟨g, hg⟩ :=
        exists_conj_of_isCarterSubgroup_of_isMinimalNormal hC₀ hD hN hKtop hDNtop
      exact ⟨g * g₀, by rw [← map_conj_trans, hg]⟩
    · -- `K := C₀ ⊔ N < ⊤` なら `↥K` の中で帰納法の仮説。
      set K : Subgroup G := C.map (MulAut.conj g₀).toMonoidHom ⊔ N with hKdef
      have hKlt : Nat.card ↥K < Nat.card G := by
        classical
        obtain ⟨x, hx⟩ : ∃ x : G, x ∉ K := by
          simpa [Subgroup.eq_top_iff'] using hKtop
        exact Finite.card_subtype_lt (x := x) hx
      have hC₀K : C.map (MulAut.conj g₀).toMonoidHom ≤ K := le_sup_left
      have hDK : D ≤ K := by
        rw [hg₀]
        exact le_sup_left
      obtain ⟨y, hy⟩ := IH ((C.map (MulAut.conj g₀).toMonoidHom).subgroupOf K) (D.subgroupOf K)
        hKlt (hC₀.subgroupOf hC₀K) (hD.subgroupOf hDK)
      rw [map_conj_eq_iff_subgroupOf hC₀K hDK y] at hy
      exact ⟨(y : G) * g₀, by rw [← map_conj_trans, hy]⟩

/-- **Isaacs Problem 3C.7(b)** (書籍 p. 91): 有限可解群の 2 つの Carter 部分群は共役。

書籍は証明を与えない (challenge problem)。証明は `|G|` の強帰納で、極小正規部分群 `N` を
取り step 1–4 (ファイル冒頭) を積む。 -/
theorem exists_conj_of_isCarterSubgroup {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    {C D : Subgroup G} (hC : IsCarterSubgroup C) (hD : IsCarterSubgroup D) :
    ∃ g : G, C.map (MulAut.conj g).toMonoidHom = D :=
  exists_conj_aux (Nat.card G) C D le_rfl hC hD

end -- 3C.7(b)

end OddOrder.Isaacs.Ch03
