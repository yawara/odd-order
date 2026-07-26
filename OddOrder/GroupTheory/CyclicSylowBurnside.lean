/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# 巡回 Sylow 部分群と Burnside の正規 `p`-補群定理

`OddOrder.GroupTheory` shared module。

mathlib の `IsCyclic.normalizer_le_centralizer` は `p` が `|G|` の**最小素因数**であることを
要求するが、実際に効いているのは「`|N_G(P) : C_G(P)|` が `|Aut P| = φ(|P|)` と `|G|` の
両方を割る」ことだけである。ここではその一般形

* `normalizer_le_centralizer_of_coprime_totient` — `P` 巡回 Sylow で
  `gcd(|G|, φ(|P|)) = 1` なら `N_G(P) ≤ C_G(P)`
* `exists_normal_complement_of_isCyclic_sylow` — さらに Burnside を適用した正規 `p`-補群

を与える。最小素数の場合は `φ(p^k) = p^{k-1}(p-1)` の `p`-部分を別扱いする必要があるので
mathlib 版とは独立 (どちらも他方の特殊化ではない)。

用途: Isaacs Problem 5C.7 (`|G| = 3^a · 5 · 11` ⇒ Sylow-3 が正規) — `p = 5` (`φ(5) = 4`)
と `p = 11` (`φ(11) = 10`) で使う。どちらも最小素因数ではない。
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- **Burnside の前提の一般形**: `P` が巡回 Sylow `p`-部分群で `gcd(|G|, φ(|P|)) = 1` なら
`N_G(P) ≤ C_G(P)`。

`N_G(P)/C_G(P) ↪ Aut(P)` (`Subgroup.normalizerMonoidHom`) より
`|N_G(P) : C_G(P)|` は `|Aut P| = φ(|P|)` を割り、同時に `|G|` も割るので互いに素なら 1。 -/
theorem normalizer_le_centralizer_of_coprime_totient (P : Sylow p G)
    (hP : IsCyclic ↥(P : Subgroup G))
    (hcop : Nat.Coprime (Nat.card G) (Nat.totient (Nat.card ↥(P : Subgroup G)))) :
    Subgroup.normalizer (P : Subgroup G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
  have key := Subgroup.card_dvd_of_injective _
    (QuotientGroup.kerLift_injective (P : Subgroup G).normalizerMonoidHom)
  rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex,
    hP.card_mulAut] at key
  refine Subgroup.relIndex_eq_one.mp ?_
  exact Nat.eq_one_of_dvd_coprimes hcop
    (dvd_trans (Subgroup.relIndex_dvd_card _ _) (Subgroup.card_subgroup_dvd_card _)) key

/-- **Burnside の正規 `p`-補群定理 (巡回 Sylow + totient 互いに素の形)**:
`|K| · |P| = |G|` かつ `p ∤ |K|` となる正規部分群 `K` が存在する。 -/
theorem exists_normal_complement_of_isCyclic_sylow (P : Sylow p G)
    (hP : IsCyclic ↥(P : Subgroup G))
    (hcop : Nat.Coprime (Nat.card G) (Nat.totient (Nat.card ↥(P : Subgroup G)))) :
    ∃ K : Subgroup G, K.Normal ∧
      Nat.card ↥K * Nat.card ↥(P : Subgroup G) = Nat.card G ∧ ¬ p ∣ Nat.card ↥K := by
  have hNC := normalizer_le_centralizer_of_coprime_totient P hP hcop
  refine ⟨(MonoidHom.transferSylow P hNC).ker, inferInstance, ?_, ?_⟩
  · exact (MonoidHom.ker_transferSylow_isComplement' P hNC).card_mul
  · exact MonoidHom.not_dvd_card_ker_transferSylow P hNC

end OddOrder.GroupTheory
