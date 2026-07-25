/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315
import OddOrder.Isaacs.Ch03_SplitExtensions.PiResidual
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalSocle
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalClosure

/-!
# Isaacs Chapter 2 — Problems §2A (Subnormality)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 2 "Subnormality" の章末演習 §2A
(pp. 53-54)。部分正規性 (`Subgroup.IsSubnormal`, mathlib inductive) の基本性質を扱う。

方針は Ch.1 の `Ch01_Sylow/Problems.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch02

section /- Problems 2A: Subnormality basics (pp. 53-54) -/

/-- **Isaacs Problem 2A.3(a)**. `H` が部分正規で `|G : H|` と `|K|` が互いに素ならば `K ≤ H`。

`H.IsSubnormal` の帰納法。`H = ⊤` は自明。step (`H' ≤ K'`, `K'` 部分正規, `H' ⊴ K'`, IH) では
`|G:K'| ∣ |G:H'|` ゆえ IH で `K ≤ K'`。次に商 `K' / H'` への像 `K.subgroupOf K' ↦ mk'` の位数は
`|K|` (`card_map_dvd` + `subgroupOfEquivOfLe`) と `|K':H'|` (`card_subgroup_dvd_card`) の両方を割り、
`|K':H'| ∣ |G:H'|` は `|K|` と互いに素ゆえ像の位数 `= 1`、したがって `K.subgroupOf K' ≤ H'.subgroupOf K'`、
`K'.subtype` で押し戻して `K ≤ H'`。 -/
theorem le_of_isSubnormal_of_coprime_index {G : Type*} [Group G] [Finite G] {K : Subgroup G} :
    ∀ {H : Subgroup G}, H.IsSubnormal → (H.index).Coprime (Nat.card K) → K ≤ H := by
  intro H hH
  induction hH with
  | top => exact fun _ => le_top
  | @step H' K' hle hsubK' hN ih =>
    intro hcop
    have hcopK' : (K'.index).Coprime (Nat.card K) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.index_dvd_of_le hle) hcop
    have hKK' : K ≤ K' := ih hcopK'
    haveI := hN
    -- `|K':H'| = (H'.subgroupOf K').index ∣ |G:H'|` は `|K|` と互いに素
    have hidxdvd : (H'.subgroupOf K').index ∣ H'.index :=
      Subgroup.relIndex_dvd_index_of_le hle
    have hcopIdx : ((H'.subgroupOf K').index).Coprime (Nat.card K) :=
      Nat.Coprime.coprime_dvd_left hidxdvd hcop
    -- `K.subgroupOf K'` の `K' / H'` への像は自明
    have himg : (K.subgroupOf K').map (QuotientGroup.mk' (H'.subgroupOf K')) = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      refine Nat.eq_one_of_dvd_coprimes hcopIdx ?_ ?_
      · rw [Subgroup.index_eq_card]
        exact Subgroup.card_subgroup_dvd_card _
      · exact (Subgroup.card_map_dvd _ _).trans
          (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKK').toEquiv))
    -- 像 `⊥` ⟹ `K.subgroupOf K' ≤ ker = H'.subgroupOf K'`
    have hle' : K.subgroupOf K' ≤ H'.subgroupOf K' := by
      rw [← QuotientGroup.ker_mk' (H'.subgroupOf K')]
      intro x hx
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← himg]
      exact Subgroup.mem_map_of_mem _ hx
    -- `K'.subtype` で押し戻して `K ≤ H'`
    calc K = (K.subgroupOf K').map K'.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKK']
      _ ≤ (H'.subgroupOf K').map K'.subtype := Subgroup.map_mono hle'
      _ = H' := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 in
/-- 部分正規部分群 `H` について `O_π(↥H)` を `G` へ押し出すと `O_π(G)` を超えない。`IsSubnormal` の
構造帰納 (motive を `(oPiCore π ↥H).map H.subtype ≤ oPiCore π G` とすると step の IH が上の `K'` に
ついてで整合する)。top は `oPiCore.map_le_of_surjective`、step は同型
`(subgroupOfEquivOfLe hle).symm` で `oPiCore π ↥H'` を `oPiCore π ↥(H'.subgroupOf K')` に移送
(`oPiCore.map_eq_of_mulEquiv`)、`characteristic_map_subtype_normal` で `↥K'` 正規、`le_oPiCore` で
`≤ oPiCore π ↥K'`、`H.subtype = K'.subtype ∘ (subgroupOf).subtype ∘ e.symm` で合成して IH。 -/
theorem oPiCore_map_subtype_le_of_isSubnormal {G : Type*} [Group G] [Finite G] {π : Set ℕ} :
    ∀ {H : Subgroup G}, H.IsSubnormal → (oPiCore π ↥H).map H.subtype ≤ oPiCore π G := by
  intro H hH
  induction hH with
  | top =>
    exact oPiCore.map_le_of_surjective π (⊤ : Subgroup G).subtype
      (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
  | @step H' K' hle hsubK' hN ih =>
    haveI := hN
    set e := Subgroup.subgroupOfEquivOfLe hle with he
    have htrans : (oPiCore π ↥H').map (e.symm : ↥H' →* ↥(H'.subgroupOf K'))
        = oPiCore π ↥(H'.subgroupOf K') := oPiCore.map_eq_of_mulEquiv π e.symm
    haveI hnorm : ((oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype).Normal :=
      characteristic_map_subtype_normal (oPiCore π ↥(H'.subgroupOf K'))
    have hpi : Subgroup.IsPiGroup π
        ((oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype) := fun q hq =>
      oPiCore.isPiGroup π q
        (by rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hq)
    have hle_oPiK' : (oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype
        ≤ oPiCore π ↥K' := Subgroup.IsPiGroup.le_oPiCore hpi
    have hcomp : H'.subtype
        = (K'.subtype.comp (H'.subgroupOf K').subtype).comp
          (e.symm : ↥H' →* ↥(H'.subgroupOf K')) := by
      ext h; rfl
    have hmapeq : (oPiCore π ↥H').map H'.subtype
        = ((oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype).map K'.subtype := by
      rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, htrans]
    rw [hmapeq]
    exact (Subgroup.map_mono hle_oPiK').trans ih

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 in
/-- **Isaacs Problem 2A.1**. 有限群 `G` の部分正規 π-部分群 `K` は π-radical `O_π(G)` に含まれる。
`↥K` は π-群なので `O_π(↥K) = ⊤`、`oPiCore_map_subtype_le_of_isSubnormal` で
`K = (O_π ↥K).map K.subtype ≤ O_π(G)`。系として二つの部分正規 π-部分群の生成する部分群も π-群
(ともに `O_π(G)` に含まれ `O_π(G)` は π-群)。 -/
theorem le_oPiCore_of_isSubnormal_of_isPiGroup {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {K : Subgroup G} (hK : K.IsSubnormal) (hπ : Subgroup.IsPiGroup π K) : K ≤ oPiCore π G := by
  have h := oPiCore_map_subtype_le_of_isSubnormal (π := π) hK
  have htop : oPiCore π (↥K) = ⊤ := by
    refine top_le_iff.mp (Subgroup.IsPiGroup.le_oPiCore (H := (⊤ : Subgroup ↥K)) (fun q hq => ?_))
    exact hπ q (by rwa [Subgroup.card_top] at hq)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

open OddOrder.Isaacs.Ch01 in
/-- 正規部分群 `N` の位数が `|G : H|` と互いに素ならば `N ≤ H`。`|H⊔N : H|` は `card_mul_card_inf`
(正規積公式) より `|N|` を割り、また `|G : H|` も割る (`relIndex_dvd_index_of_le`) ので互いに素で `= 1`、
したがって `H⊔N = H`、`N ≤ H`。 -/
theorem coprime_normal_le {G : Type*} [Group G] [Finite G] {N H : Subgroup G} [N.Normal]
    (hcop : Nat.Coprime (Nat.card ↥N) H.index) : N ≤ H := by
  have hlag : H.relIndex (H ⊔ N) * Nat.card ↥H = Nat.card ↥(H ⊔ N) := by
    rw [Subgroup.relIndex,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ N)).toEquiv]
    exact Subgroup.index_mul_card (H.subgroupOf (H ⊔ N))
  have hcmi : Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥H * Nat.card ↥N := by
    have h := card_mul_card_inf H N
    rwa [← Subgroup.mul_normal H N] at h
  have hkey : H.relIndex (H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥N := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥H)) ?_
    rw [← mul_assoc, mul_comm (Nat.card ↥H) (H.relIndex (H ⊔ N)), hlag, hcmi]
  have hdN : H.relIndex (H ⊔ N) ∣ Nat.card ↥N := ⟨Nat.card ↥(H ⊓ N), hkey.symm⟩
  have hdidx : H.relIndex (H ⊔ N) ∣ H.index := Subgroup.relIndex_dvd_index_of_le le_sup_left
  have hd1 : H.relIndex (H ⊔ N) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdN hdidx
  have hcardeq : Nat.card ↥(H ⊔ N) = Nat.card ↥H := by rw [← hlag, hd1, one_mul]
  exact le_sup_right.trans (Subgroup.eq_of_le_of_card_ge le_sup_left hcardeq.le).ge

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 in
/-- **Isaacs Problem 2A.3(b)**. `K` が部分正規で `|G : H|` と `|K|` が互いに素ならば `K ≤ H`。
`π := |K| の素因数集合` とおくと `K` は π-群、2A.1 で `K ≤ O_π(G)`。`O_π(G)` は正規 π-群で、その位数の
素因数は `π ⊆ |K| の素因数`、`|G:H|` は `|K|` と互いに素ゆえ `|O_π(G)|` とも互いに素、`coprime_normal_le`
で `O_π(G) ≤ H`、したがって `K ≤ H`。 -/
theorem le_of_isSubnormal_of_coprime_index' {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hK : K.IsSubnormal) (hcop : (H.index).Coprime (Nat.card ↥K)) : K ≤ H := by
  set π : Set ℕ := ↑(Nat.card ↥K).primeFactors with hπdef
  have hπK : Subgroup.IsPiGroup π K := fun q hq => Finset.mem_coe.mpr hq
  have hKoP : K ≤ oPiCore π G := le_oPiCore_of_isSubnormal_of_isPiGroup hK hπK
  have hsub : (Nat.card ↥(oPiCore π G)).primeFactors ⊆ (Nat.card ↥K).primeFactors := fun q hq =>
    Finset.mem_coe.mp (oPiCore.isPiGroup π q hq)
  have hcopOP : Nat.Coprime (Nat.card ↥(oPiCore π G)) H.index := by
    rw [← Nat.disjoint_primeFactors (Nat.card_pos (α := ↥(oPiCore π G))).ne'
      Subgroup.index_ne_zero_of_finite]
    exact Finset.disjoint_of_subset_left hsub hcop.symm.disjoint_primeFactors
  exact hKoP.trans (coprime_normal_le hcopOP)

open OddOrder.Isaacs.Ch03 in
/-- **Isaacs Problem 2A.2**. `K` が部分正規で `|G : K|` が π-数ならば `O^π(G) ≤ K`。`O^π(G)` は π'-元で
生成される (`oPiResidual_eq_closure_piPrimeElements`)。各 π'-元 `g` について `⟨g⟩` の位数
(= `orderOf g`) は π'-数、`|G:K|` は π-数ゆえ互いに素、`K` 部分正規で 2A.3(a) より `⟨g⟩ ≤ K`、
すなわち `g ∈ K`。したがって生成部分群 `O^π(G) ≤ K`。 -/
theorem oPiResidual_le_of_isSubnormal_of_index_isPiNumber {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K : Subgroup G} (hK : K.IsSubnormal)
    (hidx : ∀ q ∈ (K.index).primeFactors, q ∈ π) : oPiResidual π G ≤ K := by
  rw [oPiResidual_eq_closure_piPrimeElements, Subgroup.closure_le]
  intro g hg
  have hcop : (K.index).Coprime (Nat.card ↥(Subgroup.zpowers g)) := by
    rw [Nat.card_zpowers]
    refine (Nat.disjoint_primeFactors Subgroup.index_ne_zero_of_finite (orderOf_pos g).ne').mp ?_
    exact Finset.disjoint_left.mpr fun q hqi hqo => hg q hqo (hidx q hqi)
  exact le_of_isSubnormal_of_coprime_index hK hcop (Subgroup.mem_zpowers g)

/-
**Isaacs Problem 2A.7** (`S ◁◁ G` 非可換単純 ⟹ `S^G` = normal closure が minimal normal): repo の
`OddOrder.Isaacs.Ch09.isMinimalNormal_normalClosure_of_isSubnormal` (Isaacs Lemma 9.17) がまさにこれ
(`S.IsSubnormal → IsSimpleGroup ↥S → ¬IsMulCommutative ↥S → IsMinimalNormal (normalClosure ↑S)`)。
純粋対応ゆえラッパーは書かない (ラッパー方針)。
-/

open OddOrder.Isaacs.Ch09 in
/-- **Isaacs Problem 2A.8**. 異なる非可換単純な部分正規部分群 `S`, `T` は元ごとに可換 (`⁅S, T⁆ = ⊥`)。
非可換単純な部分正規部分群は component (`isQuasisimple_of_isSimpleGroup_not_isMulCommutative`)、
異なる component は可換 (`IsComponent.commutator_eq_bot_of_ne`)。 -/
theorem commutator_eq_bot_of_ne_of_isSubnormal_of_simple {G : Type*} [Group G] [Finite G]
    {S T : Subgroup G} (hS : S.IsSubnormal) (hSsimp : IsSimpleGroup ↥S)
    (hSnc : ¬ IsMulCommutative ↥S) (hT : T.IsSubnormal) (hTsimp : IsSimpleGroup ↥T)
    (hTnc : ¬ IsMulCommutative ↥T) (hne : S ≠ T) : ⁅S, T⁆ = ⊥ :=
  IsComponent.commutator_eq_bot_of_ne
    ⟨hS, isQuasisimple_of_isSimpleGroup_not_isMulCommutative hSsimp hSnc⟩
    ⟨hT, isQuasisimple_of_isSimpleGroup_not_isMulCommutative hTsimp hTnc⟩ hne

open Pointwise in
/-- 部分群の積集合が可換 (`S·H = H·S`) ならば `S ⊔ H` の台集合は `S·H`
(Isaacs の「`SH = HS` ⟺ `SH ≤ G`」の構成側)。 -/
theorem coe_sup_of_mul_comm {G : Type*} [Group G] {S H : Subgroup G}
    (hcomm : ((S : Set G) * H : Set G) = (H : Set G) * S) :
    ((S ⊔ H : Subgroup G) : Set G) = (S : Set G) * H := by
  let K : Subgroup G :=
    { carrier := ((S : Set G) * H : Set G)
      one_mem' := ⟨1, S.one_mem, 1, H.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro a b ⟨s₁, hs₁, h₁, hh₁, rfl⟩ ⟨s₂, hs₂, h₂, hh₂, rfl⟩
        have hmid : (h₁ * s₂ : G) ∈ ((S : Set G) * H : Set G) := by
          rw [hcomm]; exact ⟨h₁, hh₁, s₂, hs₂, rfl⟩
        obtain ⟨s₃, hs₃, h₃, hh₃, heq⟩ := hmid
        refine ⟨s₁ * s₃, S.mul_mem hs₁ hs₃, h₃ * h₂, H.mul_mem hh₃ hh₂, ?_⟩
        calc s₁ * s₃ * (h₃ * h₂) = s₁ * (s₃ * h₃) * h₂ := by group
          _ = s₁ * (h₁ * s₂) * h₂ := by rw [show s₃ * h₃ = h₁ * s₂ from heq]
          _ = s₁ * h₁ * (s₂ * h₂) := by group
      inv_mem' := by
        rintro a ⟨s, hs, h, hh, rfl⟩
        have hmem : (h⁻¹ * s⁻¹ : G) ∈ ((H : Set G) * S : Set G) :=
          ⟨h⁻¹, H.inv_mem hh, s⁻¹, S.inv_mem hs, rfl⟩
        rw [← hcomm] at hmem
        simpa [mul_inv_rev] using hmem }
  have hSK : S ≤ K := fun s hs => ⟨s, hs, 1, H.one_mem, mul_one s⟩
  have hHK : H ≤ K := fun h hh => ⟨1, S.one_mem, h, hh, one_mul h⟩
  refine Set.Subset.antisymm (fun x hx => (sup_le hSK hHK) hx) ?_
  rintro x ⟨s, hs, h, hh, rfl⟩
  exact Subgroup.mul_mem _ ((le_sup_left : S ≤ S ⊔ H) hs) ((le_sup_right : H ≤ S ⊔ H) hh)

open Pointwise in
/-- **Isaacs Problem 2A.4** の帰納核 (`|G|` の強帰納法 + `IsSubnormal` 構造帰納)。

step (`H ⊴ K'` ◁◁ `G`, IH: `S ≤ N_G(K')`) の場合分け:
- `K' = ⊤`: `H ⊴ G` で自明。
- `S ≤ K'`: `↥K'` に降りて `|K'| < |G|` の帰納 (部分正規性は `IsSubnormal.subgroupOf` で
  制限、`IsSubnormal.trans'` で戻す; permutability・単純性も移送)。
- `S ⊄ K'`: `S ⊓ K' ⊴ S` (`S ≤ N(K')`) + 単純性で `S ⊓ K' = ⊥`。`K := S ⊔ H` は台集合
  `S·H` (permutability)、`M := (H の K 内正規閉包) ≤ K'` (∵ `k = s·h` の共役は
  `S ≤ N(K')`・`H ≤ K'` で `K'` に残る)、`S ⊓ M = ⊥` から `|S|·|M| ≤ |K| = |S|·|H|`
  ⟹ `M = H` ⟹ `H ⊴ K` ⟹ `S ≤ K ≤ N_G(H)`。 -/
private theorem le_normalizer_of_isSubnormal_aux :
    ∀ (n : ℕ) (G : Type*) (_ : Group G) (_ : Finite G), Nat.card G ≤ n →
    ∀ S : Subgroup G, IsSimpleGroup ↥S →
    (∀ J : Subgroup G, J.IsSubnormal → ((S : Set G) * J : Set G) = (J : Set G) * S) →
    ∀ H : Subgroup G, H.IsSubnormal → S ≤ Subgroup.normalizer H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.card_pos.trans_le hcard) (lt_irrefl 0)
  | succ n ih =>
    intro G _ _ hcard S hSsimp hperm H hH
    haveI := hSsimp
    induction hH with
    | top =>
      intro s _
      rw [Subgroup.mem_normalizer_iff]
      simp
    | step H K' h_le hSubn hN ihK' =>
      by_cases hK'top : K' = ⊤
      · -- H ⊴ G
        subst hK'top
        exact le_trans le_top ((Subgroup.normal_subgroupOf_iff_le_normalizer h_le).mp hN)
      by_cases hSK' : S ≤ K'
      · -- case A: ↥K' に降りる
        have hK'card : Nat.card ↥K' ≤ n := by
          have hdvd := Subgroup.card_subgroup_dvd_card K'
          have hne : Nat.card ↥K' ≠ Nat.card G :=
            fun h => hK'top (Subgroup.eq_top_of_card_eq _ h)
          have hlt : Nat.card ↥K' < Nat.card G :=
            lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) hne
          omega
        have hSsub : IsSimpleGroup ↥(S.subgroupOf K') :=
          (Subgroup.subgroupOfEquivOfLe hSK').isSimpleGroup
        have hSmapback : (S.subgroupOf K').map K'.subtype = S := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSK']
        -- 積集合可換性の移送 (片方向の一般補題を両向きに使う)
        have transport : ∀ A B : Subgroup ↥K',
            (((A.map K'.subtype : Subgroup G) : Set G) * (B.map K'.subtype) : Set G) ⊆
              ((B.map K'.subtype : Subgroup G) : Set G) * (A.map K'.subtype) →
            ((A : Set ↥K') * B : Set ↥K') ⊆ (B : Set ↥K') * A := by
          intro A B hsub x hx
          obtain ⟨a, ha, b, hb, rfl⟩ := hx
          have hmem : ((a : G) * b) ∈
              ((B.map K'.subtype : Subgroup G) : Set G) * (A.map K'.subtype) :=
            hsub ⟨(a : G), ⟨a, ha, rfl⟩, (b : G), ⟨b, hb, rfl⟩, rfl⟩
          obtain ⟨c, hc, d, hd, heq⟩ := hmem
          obtain ⟨cc, hcc, rfl⟩ := hc
          obtain ⟨dd, hdd, rfl⟩ := hd
          exact ⟨cc, hcc, dd, hdd, Subtype.coe_injective heq⟩
        have hpermK' : ∀ J : Subgroup ↥K', J.IsSubnormal →
            ((S.subgroupOf K' : Subgroup ↥K') : Set ↥K') * J =
              ((J : Subgroup ↥K') : Set ↥K') * (S.subgroupOf K') := by
          intro J hJ
          have hcomm := hperm (J.map K'.subtype) (hJ.trans' hSubn)
          refine Set.Subset.antisymm
            (transport _ _ ?_) (transport _ _ ?_)
          · rw [hSmapback]; exact hcomm.le
          · rw [hSmapback]; exact hcomm.ge
        have hres := ih ↥K' inferInstance inferInstance hK'card (S.subgroupOf K') hSsub hpermK'
          (H.subgroupOf K') hN.isSubnormal
        rw [← Subgroup.subgroupOf_normalizer_eq h_le] at hres
        intro s hs
        exact Subgroup.mem_subgroupOf.mp
          (hres (Subgroup.mem_subgroupOf.mpr (show ((⟨s, hSK' hs⟩ : ↥K') : G) ∈ S from hs)))
      · -- case B: S ⊓ K' = ⊥ → 計数で H ⊴ S⊔H
        have hHsn : H.IsSubnormal := Subgroup.IsSubnormal.step H K' h_le hSubn hN
        -- S ⊓ K' ⊴ S + 単純性 → ⊥
        have hinfbot : S ⊓ K' = ⊥ := by
          have hnormal : ((S ⊓ K').subgroupOf S).Normal := by
            constructor
            rintro ⟨x, hxS⟩ hx ⟨s, hsS⟩
            rw [Subgroup.mem_subgroupOf] at hx ⊢
            obtain ⟨hx1, hx2⟩ := hx
            refine ⟨S.mul_mem (S.mul_mem hsS hx1) (S.inv_mem hsS), ?_⟩
            have hsN := ihK' hsS
            rw [Subgroup.mem_normalizer_iff] at hsN
            exact (hsN x).mp hx2
          rcases hnormal.eq_bot_or_eq_top with hbot | htop
          · have h := congrArg (Subgroup.map S.subtype) hbot
            rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left,
              Subgroup.map_bot] at h
          · exact absurd ((Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right) hSK'
        have hSH_bot : S ⊓ H = ⊥ :=
          le_bot_iff.mp (hinfbot ▸ inf_le_inf_left S h_le)
        -- K := S ⊔ H, 台集合 = S·H
        have hKset : ((S ⊔ H : Subgroup G) : Set G) = (S : Set G) * H :=
          coe_sup_of_mul_comm (hperm H hHsn)
        -- Kg の全元は K' を正規化する
        have hKgN : S ⊔ H ≤ Subgroup.normalizer K' := by
          intro x hx
          rw [← SetLike.mem_coe, hKset] at hx
          obtain ⟨s, hs, h, hh, rfl⟩ := hx
          exact Subgroup.mul_mem _ (ihK' hs) (Subgroup.le_normalizer (h_le hh))
        haveI hK'norm : (K'.subgroupOf (S ⊔ H)).Normal := by
          constructor
          rintro ⟨x, hxKg⟩ hx ⟨k, hkKg⟩
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          have hkN := hKgN hkKg
          rw [Subgroup.mem_normalizer_iff] at hkN
          exact (hkN x).mp hx
        -- M := H の (S⊔H) 内正規閉包 ≤ K'
        set M : Subgroup ↥(S ⊔ H) :=
          Subgroup.normalClosure ((H.subgroupOf (S ⊔ H) : Subgroup ↥(S ⊔ H)) : Set ↥(S ⊔ H))
          with hMdef
        have hMnormal : M.Normal := Subgroup.normalClosure_normal
        have hHM : H.subgroupOf (S ⊔ H) ≤ M := Subgroup.le_normalClosure
        have hMK' : M ≤ K'.subgroupOf (S ⊔ H) := by
          rw [hMdef]
          apply Subgroup.normalClosure_le_normal
          intro x hx
          rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
          rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
          exact h_le hx
        -- S ⊓ M = ⊥ (↥(S⊔H) 内)
        have hSM : S.subgroupOf (S ⊔ H) ⊓ M = ⊥ := by
          rw [eq_bot_iff]
          rintro x ⟨hx1, hx2⟩
          have h1 : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx1
          have h2 : (x : G) ∈ K' := Subgroup.mem_subgroupOf.mp (hMK' hx2)
          have hx' : (x : G) ∈ S ⊓ K' := ⟨h1, h2⟩
          rw [hinfbot, Subgroup.mem_bot] at hx'
          exact Subgroup.mem_bot.mpr (Subtype.ext hx')
        -- 位数勘定
        have hScard : Nat.card (S.subgroupOf (S ⊔ H)) = Nat.card S :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
        have hHcard : Nat.card (H.subgroupOf (S ⊔ H)) = Nat.card H :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
        have hKgcard : Nat.card ↥(S ⊔ H) = Nat.card S * Nat.card H := by
          have h := Ch01.card_mul_card_inf S H
          rw [hSH_bot, Subgroup.card_bot, mul_one] at h
          rw [← h]
          exact Nat.card_congr (Equiv.setCongr hKset)
        have hprod := Ch01.card_mul_card_inf (S.subgroupOf (S ⊔ H)) M
        rw [hSM, Subgroup.card_bot, mul_one] at hprod
        have hle_amb : Nat.card
            ((((S.subgroupOf (S ⊔ H) : Subgroup ↥(S ⊔ H)) : Set ↥(S ⊔ H)) * M : Set ↥(S ⊔ H)))
            ≤ Nat.card ↥(S ⊔ H) := by
          rw [Nat.card_coe_set_eq, ← Set.ncard_univ]
          exact Set.ncard_le_ncard (Set.subset_univ _)
        have hMle : Nat.card M ≤ Nat.card H := by
          have hcombo : Nat.card S * Nat.card M ≤ Nat.card S * Nat.card H := by
            rw [← hScard]
            calc Nat.card (S.subgroupOf (S ⊔ H)) * Nat.card M
                = Nat.card ((((S.subgroupOf (S ⊔ H) : Subgroup ↥(S ⊔ H)) : Set ↥(S ⊔ H)) * M :
                    Set ↥(S ⊔ H))) := hprod.symm
              _ ≤ Nat.card ↥(S ⊔ H) := hle_amb
              _ = Nat.card S * Nat.card H := hKgcard
              _ = Nat.card (S.subgroupOf (S ⊔ H)) * Nat.card H := by rw [hScard]
          exact Nat.le_of_mul_le_mul_left hcombo Nat.card_pos
        have hMeq : H.subgroupOf (S ⊔ H) = M :=
          Subgroup.eq_of_le_of_card_ge hHM (by rw [hHcard]; exact hMle)
        have hHnorm : (H.subgroupOf (S ⊔ H)).Normal := by rw [hMeq]; exact hMnormal
        exact le_trans le_sup_left
          ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp hHnorm)

open Pointwise in
/-- **Isaacs Problem 2A.4** (Wielandt 部分群). `S ≤ G` 単純で `G` の全部分正規部分群と可換
(`SH = HS`) ならば、`S` は全部分正規部分群を正規化する — すなわち `S` は Wielandt 部分群
`⋂_{H ◁◁ G} N_G(H)` に含まれる。 -/
theorem le_normalizer_of_isSubnormal_of_forall_mul_comm {G : Type*} [Group G] [Finite G]
    {S : Subgroup G} (hSsimp : IsSimpleGroup ↥S)
    (hperm : ∀ J : Subgroup G, J.IsSubnormal → ((S : Set G) * J : Set G) = (J : Set G) * S)
    {H : Subgroup G} (hH : H.IsSubnormal) : S ≤ Subgroup.normalizer H :=
  le_normalizer_of_isSubnormal_aux (Nat.card G) G inferInstance inferInstance le_rfl
    S hSsimp hperm H hH

open Pointwise in
/-- **Isaacs Problem 2A.5(a)** (種付き強化形). `X` を `G` の minimal normal subgroups の
任意の族、`Y₀ ⊆ X` を独立な部分族 (各メンバーが残りの join と disjoint) とすると、
`Y₀` を含む独立な部分族 `Y ⊆ X` で `sSup Y = sSup X` なるものが存在する — すなわち
`N := sSup X` は `X` のいくつかのメンバーの**直積** (独立性 + join が直積の内部的定式化;
メンバーは正規で pairwise disjoint ゆえ元は可換)。

種 `Y₀` は (b) で「与えられた minimal normal `V` をメンバーに含む分解」を取るために使う
(`Y₀ = ∅` が Isaacs の (a) そのもの)。

証明: `Y` を独立性を保つ `Y₀` 以上の極大部分族に取る (`Finite.exists_le_maximal`)。
`sSup Y < sSup X` なら `M ⊄ sSup Y` なる `M ∈ X` があり、`M ⊓ sSup Y` は正規 ≤ `M` ゆえ
minimality で `= ⊥`。`insert M Y` の独立性: `T = M` は今の disjointness、`T ∈ Y` は
`x ∈ T ⊓ (sSup (Y∖{T}) ⊔ M)` を `x = w·m` (`M` 正規で積集合) と分解し
`m ∈ M ⊓ sSup Y = ⊥`、`x = w ∈ T ⊓ sSup (Y∖{T}) = ⊥`。極大性に矛盾。 -/
theorem exists_subfamily_indep_sSup_eq {G : Type*} [Group G] [Finite G]
    {X Y₀ : Set (Subgroup G)} (hX : ∀ M ∈ X, IsMinimalNormal M) (hY₀X : Y₀ ⊆ X)
    (hY₀ : ∀ T ∈ Y₀, Disjoint T (sSup (Y₀ \ {T}))) :
    ∃ Y : Set (Subgroup G), Y₀ ⊆ Y ∧ Y ⊆ X ∧
      (∀ T ∈ Y, Disjoint T (sSup (Y \ {T}))) ∧ sSup Y = sSup X := by
  classical
  obtain ⟨Y, hY₀Y, hYmax⟩ := Finite.exists_le_maximal
    (p := fun Y : Set (Subgroup G) =>
      Y ⊆ X ∧ ∀ T ∈ Y, Disjoint T (sSup (Y \ {T})))
    (a := Y₀) ⟨hY₀X, hY₀⟩
  obtain ⟨⟨hYX, hYind⟩, hmax⟩ := hYmax
  refine ⟨Y, hY₀Y, hYX, hYind, le_antisymm (sSup_le_sSup hYX) (sSup_le fun M hM => ?_)⟩
  by_contra hMle
  have hMnorm : M.Normal := (hX M hM).1
  haveI := hMnorm
  haveI hsupnorm : (sSup Y).Normal := Subgroup.sSup_normal _ fun T hT => (hX T (hYX hT)).1
  have hdisj : Disjoint M (sSup Y) := by
    rcases (hX M hM).2.2 (M ⊓ sSup Y) (Subgroup.normal_inf_normal M (sSup Y))
        inf_le_left with h | h
    · exact disjoint_iff.mpr h
    · exact absurd (h ▸ inf_le_right) hMle
  have hMY : M ∉ Y := fun h => hMle (le_sSup h)
  -- insert M Y も独立
  have hins : (insert M Y : Set (Subgroup G)) ⊆ X ∧
      ∀ T ∈ (insert M Y : Set (Subgroup G)), Disjoint T (sSup (insert M Y \ {T})) := by
    refine ⟨Set.insert_subset hM hYX, fun T hT => ?_⟩
    rcases Set.mem_insert_iff.mp hT with rfl | hTY
    · rw [Set.insert_sdiff_self_of_notMem hMY]
      exact hdisj
    · have hle : sSup (insert M Y \ {T}) ≤ sSup (Y \ {T}) ⊔ M := by
        refine sSup_le fun A hA => ?_
        obtain ⟨hA1, hA2⟩ := hA
        rcases Set.mem_insert_iff.mp hA1 with rfl | h
        · exact le_sup_right
        · exact le_trans (le_sSup (show A ∈ Y \ {T} from ⟨h, hA2⟩)) le_sup_left
      rw [disjoint_iff_inf_le]
      rintro x ⟨hxT, hx2⟩
      have hx3 : x ∈ sSup (Y \ {T}) ⊔ M := hle hx2
      have hxset : x ∈ ((sSup (Y \ {T}) : Subgroup G) : Set G) * (M : Set G) := by
        rw [← Subgroup.mul_normal]
        exact hx3
      obtain ⟨w, hw, m, hm, heq⟩ := hxset
      have heq' : w * m = x := heq
      have hwY : w ∈ sSup Y :=
        (sSup_le_sSup (Set.sdiff_subset : Y \ {T} ⊆ Y) :
          sSup (Y \ {T}) ≤ sSup Y) hw
      have hxY : x ∈ sSup Y := le_sSup hTY hxT
      have hm1 : m = 1 := by
        have hmY : m ∈ sSup Y := by
          have hrw : m = w⁻¹ * x := by rw [← heq']; group
          rw [hrw]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hwY) hxY
        exact Subgroup.mem_bot.mp (hdisj.le_bot (Subgroup.mem_inf.mpr ⟨hm, hmY⟩))
      have hxw : x = w := by rw [← heq', hm1, mul_one]
      rw [hxw] at hxT ⊢
      exact (hYind T hTY).le_bot (Subgroup.mem_inf.mpr ⟨hxT, hw⟩)
  have hcontra := hmax hins (Set.subset_insert M Y)
  exact hMY (hcontra (Set.mem_insert M Y))

/-- socle は `G` の自己同型で不変 (elementwise): minimal normal の `ϕ`-像が minimal normal
(`IsMinimalNormal.map_equiv`) であることの `iSup_induction` 持ち上げ。 -/
private lemma apply_mem_socle {H : Type*} [Group H] (e : H ≃* H) {w : H}
    (hw : w ∈ socle H) : e w ∈ socle H := by
  refine Subgroup.iSup_induction _ (C := fun x => e x ∈ socle H) hw ?_ (by simp) ?_
  · rintro ⟨M, hM⟩ x hx
    exact isMinimalNormal_le_socle (hM.map_equiv e) ⟨x, hx, rfl⟩
  · intro x y hx hy
    rw [map_mul]
    exact (socle H).mul_mem hx hy

/-- 有限群の非自明な正規部分群は minimal normal subgroup を含む。 -/
private lemma exists_isMinimalNormal_le {H : Type*} [Group H] [Finite H] {W : Subgroup H}
    (hW : W.Normal) (hWne : W ≠ ⊥) : ∃ V : Subgroup H, IsMinimalNormal V ∧ V ≤ W := by
  obtain ⟨V, hVle, hVmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun V : Subgroup H => V.Normal ∧ V ≠ ⊥) W ⟨hW, hWne⟩
  refine ⟨V, ⟨hVmin.1.1, hVmin.1.2, fun K hK hKle => ?_⟩, hVle⟩
  by_cases hKbot : K = ⊥
  · exact Or.inl hKbot
  · exact Or.inr (le_antisymm hKle (hVmin.2 ⟨hK, hKbot⟩ hKle))

/-- **Isaacs Problem 2A.5(b) の hint**: minimal normal subgroups の族の join `N` は
`Soc(N) = N` をみたす。

各 `M ∈ X` について: `M ⊓ N`-側の minimal normal `W₁ ≤ M.subgroupOf N` を取り
(`exists_isMinimalNormal_le`)、`G`-正規閉包 `normalClosure W = M` (`M` の minimality)。
各 `G`-共役は `MulAut.conjNormal` による `↥N` の自己同型像ゆえ minimal normal のまま
(`IsMinimalNormal.map_equiv`) なので、`(socle ↥N).map N.subtype` は `G`-正規であり
`normalClosure W` を含む。よって `N ≤ (socle ↥N).map N.subtype` ⟹ `socle = ⊤`。 -/
theorem socle_eq_top_of_forall_isMinimalNormal {G : Type*} [Group G] [Finite G]
    {X : Set (Subgroup G)} (hX : ∀ M ∈ X, IsMinimalNormal M) :
    socle ↥(sSup X : Subgroup G) = ⊤ := by
  set N : Subgroup G := sSup X with hNdef
  haveI hNnorm : N.Normal := Subgroup.sSup_normal _ fun M hM => (hX M hM).1
  haveI hmap_normal : ((socle ↥N).map N.subtype).Normal := by
    constructor
    intro x hx g
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨(MulAut.conjNormal g : MulAut ↥N) w, apply_mem_socle _ hw,
      MulAut.conjNormal_apply g w⟩
  have hkey : N ≤ (socle ↥N).map N.subtype := by
    conv_lhs => rw [hNdef]
    refine sSup_le fun M hM => ?_
    have hMN : M ≤ N := le_sSup hM
    haveI hMnorm : M.Normal := (hX M hM).1
    have hsub_norm : (M.subgroupOf N).Normal := hMnorm.subgroupOf N
    have hsub_ne : M.subgroupOf N ≠ ⊥ := by
      intro h
      apply (hX M hM).2.1
      have h2 := congrArg (Subgroup.map N.subtype) h
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMN, Subgroup.map_bot] at h2
    obtain ⟨W₁, hW₁min, hW₁le⟩ := exists_isMinimalNormal_le hsub_norm hsub_ne
    have hWM : W₁.map N.subtype ≤ M := by
      calc W₁.map N.subtype ≤ (M.subgroupOf N).map N.subtype := Subgroup.map_mono hW₁le
        _ = M := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMN]
    have hWne : W₁.map N.subtype ≠ ⊥ := by
      intro h
      apply hW₁min.2.1
      have h2 := (Subgroup.map_eq_bot_iff _).mp h
      rwa [Subgroup.ker_subtype, le_bot_iff] at h2
    have hJ : Subgroup.normalClosure ((W₁.map N.subtype : Subgroup G) : Set G) = M := by
      rcases (hX M hM).2.2 _ Subgroup.normalClosure_normal
          (Subgroup.normalClosure_le_normal (SetLike.coe_subset_coe.mpr hWM)) with h | h
      · exact absurd (le_bot_iff.mp (h ▸ Subgroup.le_normalClosure)) hWne
      · exact h
    rw [← hJ]
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨w₁, hw₁, rfl⟩
    exact ⟨w₁, isMinimalNormal_le_socle hW₁min hw₁, rfl⟩
  have heq : (socle ↥N).map N.subtype = N := le_antisymm (Subgroup.map_subtype_le _) hkey
  have htop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact Subgroup.map_injective N.subtype_injective (heq.trans htop.symm)

/-- **Isaacs Problem 2A.5(b)**. `X` を `G` の minimal normal subgroups の任意の族、
`N := sSup X` とすると、`N` の minimal normal subgroup `V` は単純群。

証明: `Soc(N) = N` (前補題) の下で (a) を種 `{V}` で `↥N` に適用し、`V` を含む独立分解
`N = V ⊔ rest` を得る。`rest` は `V` と disjoint な正規部分群の join ゆえ `V` を中心化。
任意の `K ⊴ ↥V` の押し出しは `V`-共役 (正規性) と `rest`-共役 (中心化) で不変 → `↥N`-正規
→ `V` の minimality で `⊥` か `V` → `V` は単純。 -/
theorem isSimpleGroup_of_isMinimalNormal_of_forall_isMinimalNormal {G : Type*} [Group G]
    [Finite G] {X : Set (Subgroup G)} (hX : ∀ M ∈ X, IsMinimalNormal M)
    {V : Subgroup ↥(sSup X : Subgroup G)} (hV : IsMinimalNormal V) : IsSimpleGroup ↥V := by
  -- socle = ⊤ → minimal normal 族の join = ⊤
  have hsoc : socle ↥(sSup X : Subgroup G) = ⊤ := socle_eq_top_of_forall_isMinimalNormal hX
  have hsSup_socle : sSup {W : Subgroup ↥(sSup X : Subgroup G) | IsMinimalNormal W}
      = socle ↥(sSup X : Subgroup G) := by
    apply le_antisymm
    · exact sSup_le fun W hW => isMinimalNormal_le_socle hW
    · exact iSup_le fun W => le_sSup W.2
  -- (a) を種 {V} で適用
  obtain ⟨Y, hVY, hYX, hYind, hYsup⟩ := exists_subfamily_indep_sSup_eq
    (X := {W : Subgroup ↥(sSup X : Subgroup G) | IsMinimalNormal W}) (Y₀ := {V})
    (fun _ h => h)
    (Set.singleton_subset_iff.mpr
      (show V ∈ {W : Subgroup ↥(sSup X : Subgroup G) | IsMinimalNormal W} from hV))
    (by
      intro T hT
      rw [Set.mem_singleton_iff] at hT
      subst hT
      simp)
  have hVmem : V ∈ Y := hVY (Set.mem_singleton V)
  have hYtop : sSup Y = ⊤ := by rw [hYsup, hsSup_socle, hsoc]
  -- rest は V を中心化
  have hrest_cent : sSup (Y \ {V})
      ≤ Subgroup.centralizer (V : Set ↥(sSup X : Subgroup G)) := by
    refine sSup_le fun T hT => ?_
    obtain ⟨hTY, hTne⟩ := hT
    have hdisjTV : Disjoint (T : Subgroup ↥(sSup X : Subgroup G)) V := by
      refine Disjoint.mono_right ?_ (hYind T hTY)
      exact le_sSup ⟨hVmem, fun h => hTne (Set.mem_singleton_iff.mpr
        (Set.mem_singleton_iff.mp h).symm)⟩
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.commute_of_normal_of_disjoint T V (hYX hTY).1 hV.1 hdisjTV
      t v ht hv).symm).eq
  -- N = V ⊔ rest
  have htop : V ⊔ sSup (Y \ {V}) = ⊤ := by
    rw [← hYtop]
    apply le_antisymm
    · exact sup_le (le_sSup hVmem) (sSup_le_sSup Set.sdiff_subset)
    · refine sSup_le fun T hT => ?_
      by_cases h : T = V
      · exact h ▸ le_sup_left
      · exact le_trans (le_sSup (show T ∈ Y \ {V} from ⟨hT, h⟩)) le_sup_right
  -- 単純性
  haveI hVnontriv : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV.2.1
  haveI hVnorm := hV.1
  haveI hrestnorm : (sSup (Y \ {V})).Normal :=
    Subgroup.sSup_normal _ fun T hT => (hYX hT.1).1
  refine ⟨fun K hK => ?_⟩
  -- K₀ := K.map V.subtype ⊴ ↥N
  have hK₀norm : (K.map V.subtype).Normal := by
    constructor
    intro k hk n
    -- n ∈ ⊤ = V ⊔ rest → n = v·r
    have hn : n ∈ ((V ⊔ sSup (Y \ {V}) : Subgroup ↥(sSup X : Subgroup G))
        : Set ↥(sSup X : Subgroup G)) := by
      rw [htop]; trivial
    rw [Subgroup.mul_normal] at hn
    obtain ⟨v, hv, r, hr, heq⟩ := hn
    have heq' : v * r = n := heq
    obtain ⟨k₁, hk₁, rfl⟩ := hk
    -- r は k と可換
    have hcomm : Commute r (V.subtype k₁) :=
      (Subgroup.mem_centralizer_iff.mp (hrest_cent hr) _
        (SetLike.mem_coe.mpr k₁.2)).symm
    have hstep : n * V.subtype k₁ * n⁻¹ = v * V.subtype k₁ * v⁻¹ := by
      rw [← heq']
      calc v * r * V.subtype k₁ * (v * r)⁻¹
          = v * (r * V.subtype k₁ * r⁻¹) * v⁻¹ := by group
        _ = v * (V.subtype k₁ * r * r⁻¹) * v⁻¹ := by rw [hcomm.eq]
        _ = v * V.subtype k₁ * v⁻¹ := by group
    rw [hstep]
    -- v-共役: K ⊴ ↥V
    exact ⟨(⟨v, hv⟩ : ↥V) * k₁ * (⟨v, hv⟩ : ↥V)⁻¹, hK.conj_mem k₁ hk₁ ⟨v, hv⟩, rfl⟩
  -- minimality → K₀ = ⊥ か V
  rcases hV.2.2 (K.map V.subtype) hK₀norm (Subgroup.map_subtype_le K) with h | h
  · left
    have h2 := (Subgroup.map_eq_bot_iff _).mp h
    rwa [Subgroup.ker_subtype, le_bot_iff] at h2
  · right
    have htopmap : (⊤ : Subgroup ↥V).map V.subtype = V := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.map_injective V.subtype_injective (h.trans htopmap.symm)

/-- **Isaacs Problem 2A.5(c)**. minimal normal subgroups の族の join `N := sSup X` は
**単純群の直積**: `↥N` の部分群の独立族 `Y` (各メンバー単純、join = `⊤`) が存在する。

(a) を `↥N` の全 minimal normal の族に適用し (join = socle = `⊤`)、各メンバーの単純性は
(b)。Note にある通り、`X` を単一の minimal normal や `{socle 生成族}` に取れば
「有限群の minimal normal subgroup・socle は単純群の直積」を得る。 -/
theorem exists_indep_isSimpleGroup_sSup_eq_top {G : Type*} [Group G] [Finite G]
    {X : Set (Subgroup G)} (hX : ∀ M ∈ X, IsMinimalNormal M) :
    ∃ Y : Set (Subgroup ↥(sSup X : Subgroup G)),
      (∀ T ∈ Y, IsSimpleGroup ↥T) ∧ (∀ T ∈ Y, Disjoint T (sSup (Y \ {T}))) ∧
      sSup Y = ⊤ := by
  obtain ⟨Y, -, hYX, hYind, hYsup⟩ := exists_subfamily_indep_sSup_eq
    (X := {W : Subgroup ↥(sSup X : Subgroup G) | IsMinimalNormal W}) (Y₀ := ∅)
    (fun _ h => h) (Set.empty_subset _) (by simp)
  refine ⟨Y, fun T hT => ?_, hYind, ?_⟩
  · exact isSimpleGroup_of_isMinimalNormal_of_forall_isMinimalNormal hX (hYX hT)
  · rw [hYsup]
    apply le_antisymm le_top
    calc (⊤ : Subgroup ↥(sSup X : Subgroup G))
        = socle ↥(sSup X : Subgroup G) := (socle_eq_top_of_forall_isMinimalNormal hX).symm
      _ ≤ sSup {W : Subgroup ↥(sSup X : Subgroup G) | IsMinimalNormal W} :=
        iSup_le fun W => le_sSup W.2

/-- **Isaacs Problem 2A.6**. 2A.5 の状況で、`N := sSup X` に含まれる `G` の非可換正規部分群
`U` は `X` のメンバーを含む。

対偶: どの `M ∈ X` も `U` に含まれなければ、`U ⊓ M ⊴ G` は `M` の minimality で `⊥`、
`U` と `M` は正規 disjoint ゆえ元ごとに可換 (`commute_of_normal_of_disjoint`) で
`M ≤ C_G(U)`。全メンバーで成り立つから `U ≤ N = sSup X ≤ C_G(U)`、つまり `U` は可換 — 矛盾。 -/
theorem exists_mem_le_of_normal_le_sSup_of_not_isMulCommutative {G : Type*} [Group G]
    [Finite G] {X : Set (Subgroup G)} (hX : ∀ M ∈ X, IsMinimalNormal M) {U : Subgroup G}
    (hU : U.Normal) (hUle : U ≤ sSup X) (hUnc : ¬ IsMulCommutative ↥U) :
    ∃ M ∈ X, M ≤ U := by
  by_contra hno
  push Not at hno
  apply hUnc
  have hcent : sSup X ≤ Subgroup.centralizer (U : Set G) := by
    refine sSup_le fun M hM => ?_
    haveI := hU
    haveI := (hX M hM).1
    have hdisj : Disjoint U M := by
      rcases (hX M hM).2.2 (U ⊓ M) (Subgroup.normal_inf_normal U M) inf_le_right with h | h
      · exact disjoint_iff.mpr h
      · exact absurd (h ▸ inf_le_left) (hno M hM)
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.commute_of_normal_of_disjoint U M hU (hX M hM).1 hdisj u m hu hm).eq
  exact ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (hcent (hUle b.2)) a a.2)⟩⟩

open Pointwise OddOrder.Isaacs.Ch03 in
/-- **Isaacs Problem 2A.9**. `H ◁◁ G` が **π-perfect** (`H = O^π(H)`、すなわち `↥H` の π-residual
が `⊤`) ならば `O_π(G)` は `H` を正規化する。

証明 (Isaacs の hint「`G = H·O_π(G)` と仮定してよい」を `K := H ⊔ O_π(G)` への降下として実装):
`P := O_π(G)` は正規ゆえ `↑K = ↑H · ↑P`、積の位数公式 (`Ch01.card_mul_card_inf`) と Lagrange で
`|K : H| · |H ⊓ P| = |P|`、よって `|K : H|` は `|P|` を割り (`oPiCore.isPiGroup` で) π-数。
2A.2 を `↥K` に適用して `O^π(K) ≤ H.subgroupOf K`。逆向きは π-perfect 性を
`Subgroup.inclusion : ↥H →* ↥K` で押し出して `H.subgroupOf K ≤ O^π(K)`
(`subgroupOf_le_oPiResidual_of_eq_top`)。したがって `H.subgroupOf K = O^π(K)` は `↥K` で正規、
`normal_subgroupOf_iff_le_normalizer` で `P ≤ K ≤ N_G(H)`。 -/
theorem oPiCore_le_normalizer_of_isSubnormal_of_oPiResidual_eq_top {G : Type*} [Group G]
    [Finite G] {π : Set ℕ} {H : Subgroup G} (hH : H.IsSubnormal)
    (hperf : oPiResidual π ↥H = ⊤) : oPiCore π G ≤ Subgroup.normalizer H := by
  set P : Subgroup G := oPiCore π G with hPdef
  set K : Subgroup G := H ⊔ P with hKdef
  have hHK : H ≤ K := le_sup_left
  -- |K| · |H ⊓ P| = |H| · |P| (P 正規ゆえ ↑K = ↑H · ↑P)
  have hKcoe : Nat.card ↥K = Nat.card (↑H * ↑P : Set G) := by
    rw [← Subgroup.mul_normal, SetLike.coe_sort_coe, hKdef]
  have hcard : Nat.card ↥K * Nat.card ↥(H ⊓ P) = Nat.card ↥H * Nat.card ↥P := by
    rw [hKcoe, Ch01.card_mul_card_inf H P]
  -- |K : H| · |H ⊓ P| = |P|
  have hidxP : (H.subgroupOf K).index * Nat.card ↥(H ⊓ P) = Nat.card ↥P := by
    have hlag : Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥K := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
      exact Subgroup.card_mul_index _
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥H)) ?_
    rw [← mul_assoc, hlag, hcard]
  -- ゆえに |K : H| は π-数
  have hidx : ∀ q ∈ (H.subgroupOf K).index.primeFactors, q ∈ π := fun q hq =>
    oPiCore.isPiGroup π q
      (Nat.primeFactors_mono ⟨_, hidxP.symm⟩ Nat.card_pos.ne' hq)
  -- 2A.2 (↥K 版) と π-perfect 性で H.subgroupOf K = O^π(↥K)
  have hle₁ : oPiResidual π ↥K ≤ H.subgroupOf K :=
    oPiResidual_le_of_isSubnormal_of_index_isPiNumber hH.subgroupOf hidx
  have hle₂ : H.subgroupOf K ≤ oPiResidual π ↥K :=
    subgroupOf_le_oPiResidual_of_eq_top hHK hperf
  haveI hnorm : (H.subgroupOf K).Normal := by
    rw [le_antisymm hle₂ hle₁]; infer_instance
  exact le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hnorm)

open OddOrder.Isaacs.Ch09 in
/-- **Isaacs Problem 2A.10**. `H, K ≤ G` が **強共役** (strongly conjugate) とは
`⟨H, K⟩ = H ⊔ K` の中で共役なこと (`Ch09.IsStronglyConjugate`)。このとき
`H ◁◁ G ⟺ H に強共役な部分群は H 自身だけ`。

書籍 p. 290 が「2A.10 は Bartels の定理 (Thm 9.28) の直接の帰結」と述べる通りに実装:
- `⟸` 強共役が `H` のみなら `H^{(G)} = H` (`strongClosure` の定義)、Bartels
  (`strongClosure_isSubnormal`) で `H` は部分正規。
- `⟹` `H ◁◁ G` なら Lemma 9.29(a) (`strongClosure_le_of_isSubnormal`) で `H^{(G)} ≤ H`、
  よって強共役 `K` は `K ≤ H` かつ `|K| = |H|` (共役ゆえ) で `K = H`。 -/
theorem isSubnormal_iff_forall_isStronglyConjugate_eq {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) :
    H.IsSubnormal ↔ ∀ K : Subgroup G, IsStronglyConjugate H K → K = H := by
  constructor
  · intro hH K hK
    have hKsc : K ≤ strongClosure H :=
      le_sSup (show K ∈ {Y : Subgroup G | IsStronglyConjugate H Y} from hK)
    have hKle : K ≤ H := hKsc.trans (strongClosure_le_of_isSubnormal hH H le_rfl)
    obtain ⟨g, -, rfl⟩ := hK
    refine Subgroup.eq_of_le_of_card_ge hKle (le_of_eq ?_)
    rw [conjAct_smul_eq_map]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective H _ (MulAut.conj g).injective).toEquiv
  · intro h
    have hfix : strongClosure H = H :=
      le_antisymm (strongClosure_le fun Y hY => (h Y hY).le) (le_strongClosure H)
    exact hfix ▸ strongClosure_isSubnormal H

end

end OddOrder.Isaacs.Ch02
