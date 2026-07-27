/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ThompsonSubgroup
import OddOrder.Isaacs.Ch01_Sylow.Problems

/-!
# Isaacs Problem 7A.5 — 正規 elementary abelian 部分群は `𝓔(P)` の元を正規化する

**主張** (書籍 p. 209): `P` を `p`-群, `U ⊴ P` を elementary abelian とすると, `U` は
ある `E ∈ 𝓔(P)` を正規化する。ここで `𝓔(P)` (= `Subgroup.maxElemAbelianIn P p`) は
`P` の最大位数 elementary abelian 部分群全体 (Isaacs p. 202)。

**証明** (書籍 hint): `|U ⊓ E|` が最大の `E ∈ 𝓔(P)` を取る。`U` が `E` を正規化しないとして
`u ∈ U`, `F := E^u ≠ E`, `H := E ⊔ F`, `Z := E ⊓ F`, `W := H ⊓ U`, `A := Z ⊔ W` とおくと

* `E ⊓ U = F ⊓ U` (`U` 可換ゆえ `u` は `E ⊓ U` を各元固定),
* `Z ≤ C(H)` (`Z` は可換な `E` と `F` の両方に入る) ⟹ `A` は elementary abelian,
* `W` は `E ⊓ U` に入らない元 `u e u⁻¹ e⁻¹` を含む,
* `H = E · W` (`|H|·|E ⊓ U| = |E|·|W|`) と `|E·F|·|Z| = |E|²` (`E·F ⊆ H`) から
  `|A| ≥ |E|`, すなわち `A ∈ 𝓔(P)`

となり `U ⊓ E = U ⊓ A` (最大性) に反する元が `W` に在る。

⚠ 書籍は `P` を `p`-群としているが, **証明は `P` が `p`-群であることを使わない** ので
一般の有限群の部分群 `P` (と `U ⊴ P` elementary abelian) で形式化する。
-/

namespace OddOrder.Isaacs.Ch07

open Pointwise

section /- 7A.5: `𝓔(P)` の元の正規化 (p. 209) -/

variable {G : Type*} [Group G] {p : ℕ}

/-- 共役 `E ↦ E^u = u E u⁻¹` を `Subgroup.map` で表す。 -/
private def conjSubgroup (u : G) (E : Subgroup G) : Subgroup G :=
  E.map (MulAut.conj u).toMonoidHom

private theorem mem_conjSubgroup {u x : G} {E : Subgroup G} :
    x ∈ conjSubgroup u E ↔ ∃ e ∈ E, u * e * u⁻¹ = x := by
  simp [conjSubgroup, Subgroup.mem_map, MulAut.conj]

private theorem conjSubgroup_injective (u : G) :
    Function.Injective ((MulAut.conj u).toMonoidHom) :=
  (MulAut.conj u).injective

private theorem natCard_conjSubgroup (u : G) (E : Subgroup G) :
    Nat.card (conjSubgroup u E) = Nat.card E :=
  (Nat.card_congr
    (Subgroup.equivMapOfInjective E _ (conjSubgroup_injective u)).toEquiv).symm

/-- elementary abelian 部分群の部分群は elementary abelian。 -/
private theorem isElementaryAbelian_of_le {H K : Subgroup G} (hKH : K ≤ H)
    (hH : H.IsElementaryAbelian p) : K.IsElementaryAbelian p := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h := hH.comm ⟨(x : G), hKH x.2⟩ ⟨(y : G), hKH y.2⟩
    have h' : (x : G) * (y : G) = (y : G) * (x : G) := Subtype.ext_iff.mp h
    exact Subtype.ext h'
  · have h := hH.pow_eq_one ⟨(x : G), hKH x.2⟩
    have h' : (x : G) ^ p = 1 := Subtype.ext_iff.mp h
    exact Subtype.ext h'

variable [Finite G]

/-- **Isaacs Problem 7A.5** — `U ⊴ P` が elementary abelian なら, `U` は最大位数
elementary abelian 部分群 `E ∈ 𝓔(P)` のどれかを正規化する。

書籍は `P` を `p`-群としているが, 証明はそれを使わない。 -/
theorem exists_mem_maxElemAbelianIn_le_normalizer {P U : Subgroup G}
    (hUP : U ≤ P) (hUnorm : P ≤ Subgroup.normalizer (U : Set G))
    (hU : U.IsElementaryAbelian p) :
    ∃ E ∈ Subgroup.maxElemAbelianIn P p, U ≤ Subgroup.normalizer (E : Set G) := by
  classical
  -- `|U ⊓ E|` が最大の `E ∈ 𝓔(P)` を選ぶ
  obtain ⟨E, hE, hEmax⟩ := Set.exists_max_image (Subgroup.maxElemAbelianIn P p)
    (fun E => Nat.card ↥(U ⊓ E)) (Set.toFinite _)
    (Subgroup.maxElemAbelianIn_nonempty P p)
  obtain ⟨hEP, hEel, hEtop⟩ := hE
  refine ⟨E, ⟨hEP, hEel, hEtop⟩, ?_⟩
  by_contra hno
  -- `E` を正規化しない `u ∈ U` を取る
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, u ∉ Subgroup.normalizer (E : Set G) := by
    by_contra hcon
    exact hno fun x hx => by
      by_contra hxn
      exact hcon ⟨x, hx, hxn⟩
  have huP : u ∈ P := hUP huU
  set F : Subgroup G := conjSubgroup u E with hFdef
  -- `F ∈ 𝓔(P)`
  have hFcard : Nat.card F = Nat.card E := natCard_conjSubgroup u E
  have hFP : F ≤ P := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_conjSubgroup.mp hx
    exact mul_mem (mul_mem huP (hEP he)) (inv_mem huP)
  have hFel : F.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map (conjSubgroup_injective u) hEel
  -- `E ≠ F`
  have hEF : E ≠ F := by
    intro h
    refine hu ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hmem : u * x * u⁻¹ ∈ F := mem_conjSubgroup.mpr ⟨x, hx, rfl⟩
      rwa [← h] at hmem
    · intro hx
      have hx' : u * x * u⁻¹ ∈ F := by rwa [← h]
      obtain ⟨e, he, hex⟩ := mem_conjSubgroup.mp hx'
      have hxe : x = e := by
        have h2 : u * e = u * x := by
          have h1 := congrArg (fun y => y * u) hex
          simpa [mul_assoc] using h1
        exact (mul_left_cancel h2).symm
      rwa [hxe]
  -- `E ⊓ U = F ⊓ U`
  have hEU_FU : E ⊓ U = F ⊓ U := by
    apply le_antisymm
    · rintro x ⟨hxE, hxU⟩
      refine ⟨mem_conjSubgroup.mpr ⟨x, hxE, ?_⟩, hxU⟩
      have hcomm : u * x = x * u :=
        congrArg Subtype.val (hU.comm ⟨u, huU⟩ ⟨x, hxU⟩)
      rw [hcomm]; group
    · rintro x ⟨hxF, hxU⟩
      obtain ⟨e, he, rfl⟩ := mem_conjSubgroup.mp hxF
      have heU : e ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hUnorm huP) e).mpr hxU
      have hcomm : u * e = e * u :=
        congrArg Subtype.val (hU.comm ⟨u, huU⟩ ⟨e, heU⟩)
      have hfix : u * e * u⁻¹ = e := by rw [hcomm]; group
      exact ⟨by rw [hfix]; exact he, hxU⟩
  set H : Subgroup G := E ⊔ F with hHdef
  set Z : Subgroup G := E ⊓ F with hZdef
  set W : Subgroup G := H ⊓ U with hWdef
  set A : Subgroup G := Z ⊔ W with hAdef
  have hEH : E ≤ H := le_sup_left
  have hFH : F ≤ H := le_sup_right
  have hWH : W ≤ H := inf_le_left
  have hWU : W ≤ U := inf_le_right
  have hZE : Z ≤ E := inf_le_left
  have hZF : Z ≤ F := inf_le_right
  -- `Z ≤ C(H)`
  have hHcentZ : H ≤ Subgroup.centralizer (Z : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      exact fun z hz => congrArg Subtype.val (hEel.comm ⟨z, hZE hz⟩ ⟨x, hx⟩)
    · rw [Subgroup.mem_centralizer_iff]
      exact fun z hz => congrArg Subtype.val (hFel.comm ⟨z, hZF hz⟩ ⟨x, hx⟩)
  have hZcentH : Z ≤ Subgroup.centralizer (H : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact fun h hh => ((Subgroup.mem_centralizer_iff.mp (hHcentZ hh)) z hz).symm
  have hZcentW : Z ≤ Subgroup.centralizer (W : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact fun x hx => Subgroup.mem_centralizer_iff.mp (hZcentH hz) x (hWH hx)
  -- `A` は elementary abelian で `P` に含まれる
  have hZel : Z.IsElementaryAbelian p := isElementaryAbelian_of_le hZE hEel
  have hWel : W.IsElementaryAbelian p := isElementaryAbelian_of_le hWU hU
  have hAel : A.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hZel hWel hZcentW
  have hAP : A ≤ P := sup_le (hZE.trans hEP) (hWU.trans hUP)
  -- `E ⊓ U ≤ W`
  have hEUW : E ⊓ U ≤ W := le_inf (inf_le_left.trans hEH) inf_le_right
  -- `W` は `E` に入らない元を含む
  obtain ⟨w, hwW, hwE⟩ : ∃ w ∈ W, w ∉ E := by
    obtain ⟨x, hxF, hxE⟩ : ∃ x ∈ F, x ∉ E := by
      by_contra hcon
      refine hEF ?_
      have hFE : F ≤ E := fun x hx => by
        by_contra hxE
        exact hcon ⟨x, hx, hxE⟩
      exact (Subgroup.eq_of_le_of_card_ge hFE (le_of_eq hFcard.symm)).symm
    obtain ⟨e, he, rfl⟩ := mem_conjSubgroup.mp hxF
    refine ⟨u * e * u⁻¹ * e⁻¹, ⟨H.mul_mem (hFH hxF) (H.inv_mem (hEH he)), ?_⟩, ?_⟩
    · have hconj : e * u⁻¹ * e⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hUnorm (hEP he)) u⁻¹).mp (inv_mem huU)
      have heq : u * e * u⁻¹ * e⁻¹ = u * (e * u⁻¹ * e⁻¹) := by group
      rw [heq]
      exact mul_mem huU hconj
    · intro hmem
      refine hxE ?_
      have : u * e * u⁻¹ = (u * e * u⁻¹ * e⁻¹) * e := by group
      rw [this]
      exact mul_mem hmem he
  -- `H = E · W` (集合の積)
  have hHEU : H ≤ E ⊔ U := by
    refine sup_le le_sup_left (fun x hx => ?_)
    obtain ⟨e, he, rfl⟩ := mem_conjSubgroup.mp hx
    exact mul_mem (mul_mem (Subgroup.mem_sup_right huU) (Subgroup.mem_sup_left he))
      (inv_mem (Subgroup.mem_sup_right huU))
  have hEUcoe : ((E ⊔ U : Subgroup G) : Set G) = (E : Set G) * (U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right E U (fun x hx => hUnorm (hEP hx))
  have hHcoe : ((H : Subgroup G) : Set G) = (E : Set G) * (W : Set G) := by
    apply Set.Subset.antisymm
    · intro h hh
      have hh' : h ∈ ((E ⊔ U : Subgroup G) : Set G) := hHEU hh
      rw [hEUcoe] at hh'
      obtain ⟨e, he, v, hv, rfl⟩ := hh'
      refine ⟨e, he, v, ⟨?_, hv⟩, rfl⟩
      have hveq : v = e⁻¹ * (e * v) := by group
      rw [hveq]
      exact H.mul_mem (H.inv_mem (hEH he)) hh
    · rintro x ⟨e, he, v, hv, rfl⟩
      exact mul_mem (hEH he) (hWH hv)
  -- 交わりの計算
  have hEW : E ⊓ W = E ⊓ U := by
    refine le_antisymm (fun x hx => ⟨hx.1, hWU hx.2⟩) (fun x hx => ⟨hx.1, hEUW hx⟩)
  have hZW : Z ⊓ W = E ⊓ U := by
    refine le_antisymm (fun x hx => ⟨hZE hx.1, hWU hx.2⟩) (fun x hx => ⟨⟨hx.1, ?_⟩, hEUW hx⟩)
    exact (hEU_FU.le hx).1
  -- 位数の関係式
  have hcardH : Nat.card ↥H * Nat.card ↥(E ⊓ U) = Nat.card ↥E * Nat.card ↥W := by
    have hprod := Ch01.card_mul_card_inf E W
    rw [hEW, ← hHcoe] at hprod
    exact hprod
  have hAcoe : ((A : Subgroup G) : Set G) = (Z : Set G) * (W : Set G) := by
    refine Subgroup.coe_mul_of_right_le_normalizer_left Z W (fun x hx => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hcomm : ∀ y ∈ Z, y * x = x * y := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hZcentW hy) x hx).symm
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · have hfix : x * z * x⁻¹ = z := by rw [← hcomm z hz]; group
      rwa [hfix]
    · have h1 := hcomm _ hz
      have h2 : x * z = x * (x * z * x⁻¹) := by rw [← h1]; group
      have h3 : z = x * z * x⁻¹ := mul_left_cancel h2
      rw [h3]; exact hz
  have hcardA : Nat.card ↥A * Nat.card ↥(E ⊓ U) = Nat.card ↥Z * Nat.card ↥W := by
    have hprod := Ch01.card_mul_card_inf Z W
    rw [hZW, ← hAcoe] at hprod
    exact hprod
  have hcardEF : Nat.card ↥E * Nat.card ↥E ≤ Nat.card ↥H * Nat.card ↥Z := by
    have hprod := Ch01.card_mul_card_inf E F
    have hsub : (E : Set G) * (F : Set G) ⊆ ((H : Subgroup G) : Set G) := by
      rintro x ⟨e, he, f, hf, rfl⟩
      exact mul_mem (hEH he) (hFH hf)
    have hle : Nat.card ((E : Set G) * (F : Set G)) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    calc Nat.card ↥E * Nat.card ↥E = Nat.card ↥E * Nat.card ↥F := by rw [hFcard]
      _ = Nat.card ((E : Set G) * (F : Set G)) * Nat.card ↥Z := hprod.symm
      _ ≤ Nat.card ↥H * Nat.card ↥Z := Nat.mul_le_mul_right _ hle
  -- `|A| ≥ |E|`
  have hAE : Nat.card ↥E ≤ Nat.card ↥A := by
    have hkey : Nat.card ↥E * (Nat.card ↥E * Nat.card ↥(E ⊓ U)) ≤
        Nat.card ↥A * (Nat.card ↥E * Nat.card ↥(E ⊓ U)) := by
      calc Nat.card ↥E * (Nat.card ↥E * Nat.card ↥(E ⊓ U))
          = Nat.card ↥E * Nat.card ↥E * Nat.card ↥(E ⊓ U) := by ring
        _ ≤ Nat.card ↥H * Nat.card ↥Z * Nat.card ↥(E ⊓ U) :=
            Nat.mul_le_mul_right _ hcardEF
        _ = Nat.card ↥Z * (Nat.card ↥H * Nat.card ↥(E ⊓ U)) := by ring
        _ = Nat.card ↥Z * (Nat.card ↥E * Nat.card ↥W) := by rw [hcardH]
        _ = Nat.card ↥Z * Nat.card ↥W * Nat.card ↥E := by ring
        _ = Nat.card ↥A * Nat.card ↥(E ⊓ U) * Nat.card ↥E := by rw [hcardA]
        _ = Nat.card ↥A * (Nat.card ↥E * Nat.card ↥(E ⊓ U)) := by ring
    exact Nat.le_of_mul_le_mul_right hkey (Nat.mul_pos Nat.card_pos Nat.card_pos)
  -- `A ∈ 𝓔(P)` で `E` の最大性に矛盾
  have hAmem : A ∈ Subgroup.maxElemAbelianIn P p :=
    ⟨hAP, hAel, fun K hKP hKel => (hEtop K hKP hKel).trans hAE⟩
  have hUEA : U ⊓ E ≤ U ⊓ A :=
    le_inf inf_le_left (fun x hx => Subgroup.mem_sup_right (hEUW ⟨hx.2, hx.1⟩))
  have heqUA : U ⊓ E = U ⊓ A :=
    Subgroup.eq_of_le_of_card_ge hUEA (hEmax A hAmem)
  have hwUE : w ∈ U ⊓ E := by
    rw [heqUA]
    exact ⟨hWU hwW, Subgroup.mem_sup_right hwW⟩
  exact hwE hwUE.2

end

end OddOrder.Isaacs.Ch07
