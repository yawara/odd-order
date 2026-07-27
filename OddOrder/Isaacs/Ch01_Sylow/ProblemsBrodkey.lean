/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main

/-!
# Isaacs Problems 1F (pp. 40–41) — Brodkey 周辺

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1F の形式化
(campaign issue 1055)。§1F は Brodkey の定理 (Thm 1.37) とその一般化 (Thm 1.38,
「交わり極小な Sylow 対 `S, T` に対し `O_p(G)` は `D = S ∩ T` の中で `S` でも `T` でも
正規な最大の部分群」) を扱う節で, 演習もその周辺。

* **1F.1**: `M ⊴ G`, `N ⊴ G`, `M ∩ N = 1` なら `M` と `N` は互いに中心化する。
  → **mathlib `Subgroup.commute_of_normal_of_disjoint` がそのままこの主張**
  (証明も Hint どおり交換子 `[m, n] = m⁻¹n⁻¹mn` が `M ∩ N` に入ることを見る)。
  ラッパー方針によりここでは対応を記録するだけで再述しない。
* **1F.2**: `O_p(G) = 1` なら `Z(S) ∩ Z(T) = 1` となる `S, T ∈ Syl_p(G)` が存在する。
  → `exists_sylow_pair_inf_center_eq_bot` (本ファイル)。

## Main results

- `exists_sylow_pair_inf_center_eq_bot` — **Problem 1F.2**。
-/

namespace OddOrder.Isaacs.Ch01

open Subgroup

section /- 1F: Problem 1F.2 (p. 41) -/

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **Isaacs Problem 1F.2** (p. 41)。`O_p(G) = 1` なら, 中心の交わりが自明な
Sylow `p`-部分群の対 `S, T` が存在する。

ここで `Z(S)` は `G` の部分群として `S ⊓ C_G(S)` の形で表す。

交わりの位数が最小 (したがって包含極小) な対 `S, T` を取り
`K := Z(S) ⊓ Z(T)` とおくと `K ≤ S ⊓ T` であり, `K` の元は `S` の全元とも `T` の全元とも
可換なので `S`, `T ≤ N_G(K)`。**Thm 1.38**
(`opCore_eq_inf_of_minimal_sylow_inter`) より `K ≤ O_p(G) = 1`。 -/
theorem exists_sylow_pair_inf_center_eq_bot (h : opCore p G = ⊥) :
    ∃ S T : Sylow p G,
      ((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) ⊓
        ((T : Subgroup G) ⊓ centralizer ((T : Subgroup G) : Set G)) = ⊥ := by
  classical
  haveI := Fintype.ofFinite (Sylow p G)
  obtain ⟨ST, -, hminST⟩ :=
    (Finset.univ : Finset (Sylow p G × Sylow p G)).exists_min_image
      (fun ST => Nat.card ((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G) : Subgroup G))
      ⟨(default : Sylow p G × Sylow p G), Finset.mem_univ _⟩
  obtain ⟨S, T⟩ := ST
  refine ⟨S, T, ?_⟩
  -- 位数最小の対は特に包含極小 (Thm 1.38 が要求する形)
  have hmin : ∀ S' T' : Sylow p G,
      (S' : Subgroup G) ⊓ (T' : Subgroup G) ≤ (S : Subgroup G) ⊓ (T : Subgroup G) →
      (S' : Subgroup G) ⊓ (T' : Subgroup G) = (S : Subgroup G) ⊓ (T : Subgroup G) :=
    fun S' T' hle =>
      Subgroup.eq_of_le_of_card_ge hle (hminST (S', T') (Finset.mem_univ _))
  set K : Subgroup G :=
    ((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) ⊓
      ((T : Subgroup G) ⊓ centralizer ((T : Subgroup G) : Set G)) with hKdef
  have hKD : K ≤ (S : Subgroup G) ⊓ (T : Subgroup G) :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  -- `K` の元は `R` (= `S` または `T`) の全元と可換なので `R ≤ N_G(K)`
  have hnorm : ∀ R : Sylow p G, K ≤ centralizer ((R : Subgroup G) : Set G) →
      (R : Subgroup G) ≤ normalizer (K : Set G) := by
    intro R hKC r hr
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hc : r * k = k * r := Subgroup.mem_centralizer_iff.mp (hKC hk) r hr
      rwa [show r * k * r⁻¹ = k from by rw [hc]; group]
    · intro hk
      have hc : r * (r * k * r⁻¹) = (r * k * r⁻¹) * r :=
        Subgroup.mem_centralizer_iff.mp (hKC hk) r hr
      have hfix : r * k * r⁻¹ = k := by
        have h1 : r⁻¹ * (r * (r * k * r⁻¹)) = r⁻¹ * ((r * k * r⁻¹) * r) := by rw [hc]
        calc r * k * r⁻¹ = r⁻¹ * (r * (r * k * r⁻¹)) := by group
          _ = r⁻¹ * ((r * k * r⁻¹) * r) := h1
          _ = k := by group
      rwa [hfix] at hk
  have hSC : K ≤ centralizer ((S : Subgroup G) : Set G) := inf_le_left.trans inf_le_right
  have hTC : K ≤ centralizer ((T : Subgroup G) : Set G) := inf_le_right.trans inf_le_right
  have hKle := opCore_eq_inf_of_minimal_sylow_inter S T hmin hKD (hnorm S hSC) (hnorm T hTC)
  rw [h] at hKle
  exact le_bot_iff.mp hKle

end -- Problem 1F.2

end OddOrder.Isaacs.Ch01
