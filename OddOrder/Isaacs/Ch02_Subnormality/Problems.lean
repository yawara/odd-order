/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315
import OddOrder.Isaacs.Ch03_SplitExtensions.PiResidual
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalSocle

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

end

end OddOrder.Isaacs.Ch02
