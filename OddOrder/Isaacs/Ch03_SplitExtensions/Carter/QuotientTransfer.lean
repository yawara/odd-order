/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Carter.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Carter 部分群 (Isaacs 3C.7) — 商群への往復

`G ⧸ N` での Carter 性を `G` の言葉に翻訳する部品。3C.7 の帰納は極小正規部分群 `N` を
取って `G ⧸ N` に降りるので、以下の 3 点が要る:

1. **正規化群の対応**: `N ≤ K` なら `N_{G/N}(K/N) = N_G(K)/N`, したがって
   `K/N` が自己正規化 ⟺ `K` が自己正規化 (`normalizer_map_mk'` / `normalizer_eq_iff_map_mk'`)。
2. **冪零性**: `C` 冪零なら像 `C/N ∩ …` も冪零 (`isNilpotent_map_of_isNilpotent`)。
   3C.7 では `(C ⊔ N)/N = C.map (mk' N)` (`N` は核に落ちる) を使うので、像の冪零性で足りる。
3. **共役の引き戻し**: `G/N` で `K₁/N` と `K₂/N` が共役なら `K₁` と `K₂` も共役
   (`exists_conj_of_map_mk'_conj`)。

## Main results

- `normalizer_map_mk'` — `N ≤ K` での正規化群の対応定理。
- `normalizer_eq_iff_map_mk'` — 自己正規化性の往復。
- `sup_map_mk'_eq_map_mk'` — `(C ⊔ N).map (mk' N) = C.map (mk' N)`。
- `isNilpotent_map_of_isNilpotent` — 冪零部分群の像は冪零。
- `exists_conj_of_map_mk'_conj` — 商での共役を `G` へ引き戻す。
- `card_quotient_lt` — `N ≠ ⊥` なら `|G/N| < |G|` (帰納の測度)。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C.7: 商群への往復 -/

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal]

/-- **正規化群の対応定理** (`N ≤ K`): `N_{G/N}(K/N) = N_G(K)/N`。

`mk' N` は全射なので `comap_normalizer_eq_of_surjective` が使え, `N ≤ K` から
`(K/N).comap (mk' N) = K` (`comap_map_eq_self`)。 -/
theorem normalizer_map_mk' (K : Subgroup G) (hNK : N ≤ K) :
    Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.normalizer (K : Set G)).map (QuotientGroup.mk' N) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hcm : (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = K :=
    Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hNK)
  have h2 := Subgroup.comap_normalizer_eq_of_surjective
    (K.map (QuotientGroup.mk' N)) hsurj
  rw [hcm] at h2
  rw [← h2, Subgroup.map_comap_eq_self_of_surjective hsurj]

/-- 自己正規化性は `G ⧸ N` との間を往復する (`N ≤ K`)。 -/
theorem normalizer_eq_iff_map_mk' (K : Subgroup G) (hNK : N ≤ K) :
    Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
        = K.map (QuotientGroup.mk' N) ↔
      Subgroup.normalizer (K : Set G) = K := by
  rw [normalizer_map_mk' K hNK]
  constructor
  · intro h
    have hker : (QuotientGroup.mk' N).ker ≤ Subgroup.normalizer (K : Set G) := by
      rw [QuotientGroup.ker_mk']
      exact hNK.trans K.le_normalizer
    calc Subgroup.normalizer (K : Set G)
        = ((Subgroup.normalizer (K : Set G)).map (QuotientGroup.mk' N)).comap
            (QuotientGroup.mk' N) := (Subgroup.comap_map_eq_self hker).symm
      _ = (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by rw [h]
      _ = K := Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hNK)
  · intro h
    rw [h]

/-- `N` は `mk' N` の核なので `(C ⊔ N).map (mk' N) = C.map (mk' N)`。 -/
theorem sup_map_mk'_eq_map_mk' (C : Subgroup G) :
    (C ⊔ N).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N) := by
  rw [Subgroup.map_sup]
  simp [QuotientGroup.map_mk'_self]

/-- 冪零部分群の準同型像は冪零。 -/
theorem isNilpotent_map_of_isNilpotent {G' : Type*} [Group G'] {C : Subgroup G}
    (hC : Group.IsNilpotent ↥C) (f : G →* G') : Group.IsNilpotent ↥(C.map f) :=
  haveI := hC
  Group.nilpotent_of_surjective (f.subgroupMap C) (f.subgroupMap_surjective C)

/-- 商での共役を `G` へ引き戻す: `K₁/N` が `K₂/N` に共役なら `K₁` は `K₂` に共役
(`N ≤ K₁`, `N ≤ K₂`)。 -/
theorem exists_conj_of_map_mk'_conj {K₁ K₂ : Subgroup G} (h₁ : N ≤ K₁) (h₂ : N ≤ K₂)
    (h : ∃ q : G ⧸ N, (K₁.map (QuotientGroup.mk' N)).map (MulAut.conj q).toMonoidHom
      = K₂.map (QuotientGroup.mk' N)) :
    ∃ g : G, K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  refine ⟨g, ?_⟩
  -- 共役と `mk'` は交換する: `(K₁^g).map mk' = (K₁.map mk')^(mk' g)`
  have hcomm : (K₁.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N)
      = (K₁.map (QuotientGroup.mk' N)).map (MulAut.conj (QuotientGroup.mk' N g)).toMonoidHom := by
    -- `mk'` の `map_mul`/`map_inv` は商群では `rfl` なので 2 つの合成は定義的に等しい
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  -- 両辺の像が一致 ⟹ `comap` で戻して一致 (`N` は両辺に含まれる)
  have hN₁ : N ≤ K₁.map (MulAut.conj g).toMonoidHom := by
    intro n hn
    refine ⟨g⁻¹ * n * g, h₁ (?_), by simp [MulAut.conj_apply]; group⟩
    simpa using ‹N.Normal›.conj_mem n hn g⁻¹
  have hkey : (K₁.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N)
      = K₂.map (QuotientGroup.mk' N) := by rw [hcomm, hq]
  calc K₁.map (MulAut.conj g).toMonoidHom
      = ((K₁.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N)).comap
          (QuotientGroup.mk' N) :=
        (Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hN₁)).symm
    _ = (K₂.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by rw [hkey]
    _ = K₂ := Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact h₂)

omit [N.Normal] in
/-- 帰納の測度: `N ≠ ⊥` なら `|G/N| < |G|` (剰余類の個数なので正規性は不要)。 -/
theorem card_quotient_lt [Finite G] (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hlt : 1 < Nat.card ↥N := Finite.one_lt_card
  have heq : N.index * Nat.card ↥N = Nat.card G := N.index_mul_card
  have hidx : N.index = Nat.card G / Nat.card ↥N := by
    rw [← heq, Nat.mul_div_cancel _ Nat.card_pos]
  change N.index < Nat.card G
  rw [hidx]
  exact Nat.div_lt_self Nat.card_pos hlt

end -- 商群への往復

end OddOrder.Isaacs.Ch03
