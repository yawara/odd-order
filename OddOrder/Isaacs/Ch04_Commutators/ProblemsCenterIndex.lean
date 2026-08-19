/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini

/-!
# Isaacs Chapter 4 — Problem 4A.10 (中心の指数が小さい `p`-群の導来部分群)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.10 (書籍 p. 124)。

`P` を `p`-群で `|P : Z(P)| ≤ p^n` とすると **`|P'| ≤ p^{n(n-1)/2}`**。

書籍の hint どおり `n` に関する帰納法。`P` が非可換なら `Z(P) ⊆ Q ⊆ P` かつ `|P : Q| = p`
なる `Q` を取り, `|Q'|` を帰納法で抑え, `P/Q'` に **Lemma 4.6** を適用する。

## 中核: Lemma 4.6 から出る指数評価

`Q ⊴ G`, `G/Q` cyclic, `Z(G) ≤ Q` なら **`|G'| ≤ |⁅Q,Q⁆| · |Q : Z(G)|`**
(`card_commutator_le_of_normal_cyclic_quotient`)。

`Ḡ = G/⁅Q,Q⁆` で `Ā = Q/⁅Q,Q⁆` は可換正規で `Ḡ/Ā ≅ G/Q` は cyclic ゆえ Lemma 4.6
(`card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient`) が
`|Ḡ'| · |Ā ⊓ Z(Ḡ)| = |Ā|` を与える。`Z(G)` の像が `Ā ⊓ Z(Ḡ)` に入ることと
像・核の位数関係を組み合わせる。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4A.10 (p. 124) -/

variable {G : Type*} [Group G]

/-! ### 像と核の位数関係 -/

/-- 準同型の制限に対する第一同型定理の位数形: `|f(H)| · |H ⊓ ker f| = |H|`. -/
theorem card_map_mul_card_inf_ker {N : Type*} [Group N] [Finite G] (H : Subgroup G)
    (f : G →* N) : Nat.card (H.map f) * Nat.card ((H ⊓ f.ker : Subgroup G)) = Nat.card H := by
  have hker : Nat.card ((f.domRestrict H).ker) = Nat.card ((H ⊓ f.ker : Subgroup G)) := by
    rw [MonoidHom.ker_domRestrict, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ f.ker ≤ H)).toEquiv
  have h1 := Subgroup.card_mul_index ((f.domRestrict H).ker)
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, hker, mul_comm] at h1
  exact h1

/-! ### Lemma 4.6 から出る指数評価 -/

/-- **4A.10 の中核**: `Q ⊴ G`, `G/Q` cyclic, `Z(G) ≤ Q` なら
`|G'| ≤ |⁅Q,Q⁆| · |Q : Z(G)|`.

`Ḡ = G/⁅Q,Q⁆` で `Ā = Q/⁅Q,Q⁆` は可換正規, `Ḡ/Ā ≅ G/Q` は cyclic なので Lemma 4.6 が
`|Ḡ'| · |Ā ⊓ Z(Ḡ)| = |Ā|` を与える。`Z(G)` の像は `Ā ⊓ Z(Ḡ)` に入るので, 像・核の位数関係
(`card_map_mul_card_inf_ker`) と合わせて `|G'| · |Z(G) の像| ≤ |Z(G) の像| · |⁅Q,Q⁆| · |Q:Z(G)|`,
両辺を約せばよい。 -/
theorem card_commutator_le_of_normal_cyclic_quotient [Finite G] {Q : Subgroup G} [Q.Normal]
    (hCyc : IsCyclic (G ⧸ Q)) (hZ : Subgroup.center G ≤ Q) :
    Nat.card (_root_.commutator G)
      ≤ Nat.card (⁅Q, Q⁆ : Subgroup G) * (Subgroup.center G).relIndex Q := by
  set Z : Subgroup G := Subgroup.center G with hZdef
  set K : Subgroup G := ⁅Q, Q⁆ with hKdef
  have : K.Normal := Subgroup.commutator_normal Q Q
  set f : G →* G ⧸ K := QuotientGroup.mk' K with hfdef
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective K
  have hKQ : K ≤ Q := Subgroup.commutator_le_left Q Q
  have hKG : K ≤ _root_.commutator G := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  set A : Subgroup (G ⧸ K) := Q.map f with hAdef
  have hAnorm : A.Normal := Subgroup.Normal.map inferInstance f hfsurj
  -- `Ā` は可換
  have hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    have hmem : (x * y)⁻¹ * (y * x) ∈ K := by
      have heq : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact Subgroup.commutator_mem_commutator (Q.inv_mem hy) (Q.inv_mem hx)
    exact (QuotientGroup.mk'_eq_mk' K).mpr ⟨(x * y)⁻¹ * (y * x), hmem, by group⟩
  -- `Ḡ/Ā ≅ G/Q` は cyclic
  have hCycA : IsCyclic ((G ⧸ K) ⧸ A) := by
    exact isCyclic_of_surjective
      (QuotientGroup.quotientQuotientEquivQuotient K Q hKQ).symm.toMonoidHom
      (QuotientGroup.quotientQuotientEquivQuotient K Q hKQ).symm.surjective
  -- Lemma 4.6 (位数形)
  have hL46 := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
    hAb hCycA
  -- `Ḡ' = G' の像`
  have hcomm : _root_.commutator (G ⧸ K) = (_root_.commutator G).map f := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f hfsurj]
  -- 位数関係
  have hQK : Nat.card A * Nat.card K = Nat.card Q := by
    have h := card_map_mul_card_inf_ker Q f
    rwa [QuotientGroup.ker_mk', inf_eq_right.mpr hKQ] at h
  have hGK : Nat.card ((_root_.commutator G).map f) * Nat.card K
      = Nat.card (_root_.commutator G) := by
    have h := card_map_mul_card_inf_ker (_root_.commutator G) f
    rwa [QuotientGroup.ker_mk', inf_eq_right.mpr hKG] at h
  have hZK : Nat.card (Z.map f) * Nat.card ((Z ⊓ K : Subgroup G)) = Nat.card Z := by
    have h := card_map_mul_card_inf_ker Z f
    rwa [QuotientGroup.ker_mk'] at h
  have hrel : Nat.card Z * Z.relIndex Q = Nat.card Q := by
    have h := Subgroup.card_mul_index (Z.subgroupOf Q)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv] at h
  -- `Z(G)` の像は `Ā ⊓ Z(Ḡ)` に入る
  have hle : Z.map f ≤ A ⊓ Subgroup.center (G ⧸ K) := by
    refine le_inf (Subgroup.map_mono hZ) ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hfsurj y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) x]
  have hmle : Nat.card (Z.map f) ≤ Nat.card ((A ⊓ Subgroup.center (G ⧸ K) : Subgroup (G ⧸ K))) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hKle : Nat.card ((Z ⊓ K : Subgroup G)) ≤ Nat.card K :=
    Nat.card_le_card_of_injective (Subgroup.inclusion (inf_le_right : Z ⊓ K ≤ K))
      (Subgroup.inclusion_injective _)
  -- 数え上げ
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := Z.map f))
  calc Nat.card (_root_.commutator G) * Nat.card (Z.map f)
      ≤ Nat.card (_root_.commutator G)
          * Nat.card ((A ⊓ Subgroup.center (G ⧸ K) : Subgroup (G ⧸ K))) :=
        Nat.mul_le_mul_left _ hmle
    _ = Nat.card K * (Nat.card (_root_.commutator (G ⧸ K))
          * Nat.card ((A ⊓ Subgroup.center (G ⧸ K) : Subgroup (G ⧸ K)))) := by
        rw [hcomm, ← hGK]
        ring
    _ = Nat.card Q := by rw [hL46, mul_comm (Nat.card K), hQK]
    _ = Nat.card (Z.map f) * Nat.card ((Z ⊓ K : Subgroup G)) * Z.relIndex Q := by
        rw [hZK, hrel]
    _ ≤ Nat.card (Z.map f) * Nat.card K * Z.relIndex Q := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKle)
    _ = Nat.card K * Z.relIndex Q * Nat.card (Z.map f) := by ring

/-! ### Problem 4A.10 -/

/-- **Isaacs Problem 4A.10**: `p`-群 `P` が `|P : Z(P)| ≤ p^n` を満たせば
`|P'| ≤ p^{n(n-1)/2}` (`n(n-1)/2 = n.choose 2`).

`n` の帰納法 (群も動くので `∀ G` の形)。`P` が非可換なら `Z(P)` を含む極大部分群 `Q` を取る
と `|P : Q| = p` (冪零群の極大部分群は素数指数, Problem 1D.6) で `Q ⊴ P`。
`|Q'| ≤ p^{n.choose 2}` は帰納法 (`Z(P) ≤ Z(Q)` から `|Q : Z(Q)| ≤ |Q : Z(P)| ≤ p^n`),
`|P' : Q'| ≤ |Q : Z(P)| ≤ p^n` は `card_commutator_le_of_normal_cyclic_quotient` (Lemma 4.6)。
Pascal `(n+1).choose 2 = n + n.choose 2` がちょうど指数の勘定に合う。 -/
theorem card_commutator_le_pow_choose_two {p : ℕ} [Fact p.Prime] :
    ∀ (n : ℕ) (G : Type*) (_ : Group G) (_ : Finite G), IsPGroup p G →
      (Subgroup.center G).index ≤ p ^ n →
        Nat.card (_root_.commutator G) ≤ p ^ (n.choose 2) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hidx
    have hpos : 0 < (Subgroup.center G).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hle1 : (Subgroup.center G).index ≤ 1 := by simpa using hidx
    have htop : Subgroup.center G = ⊤ := Subgroup.index_eq_one.mp (le_antisymm hle1 hpos)
    simp [(_root_.commutator_eq_bot_iff_center_eq_top (G := G)).mpr htop]
  | succ n ih =>
    intro G _ _ hP hidx
    have : Group.IsNilpotent G := hP.isNilpotent
    rcases eq_or_ne (Subgroup.center G) ⊤ with htop | hne
    · simp only [(_root_.commutator_eq_bot_iff_center_eq_top (G := G)).mpr htop,
        Subgroup.card_bot]
      exact Nat.one_le_pow _ _ (by omega)
    -- `Z(G)` を含む極大部分群 `Q`
    obtain ⟨Q, hQco, hZQ⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.center G)).resolve_left hne
    have hQnorm : Q.Normal :=
      Subgroup.NormalizerCondition.normal_of_coatom Q
        (Group.normalizerCondition_of_isNilpotent (G := G)) hQco
    have hQprime : (Q.index).Prime :=
      (OddOrder.Isaacs.Ch01.isCoatom_iff_index_prime Q).mp hQco
    have hQp : Q.index = p := by
      obtain ⟨k, hk⟩ := hP.exists_card_eq
      have hdvd : Q.index ∣ p ^ k := hk ▸ Subgroup.index_dvd_card Q
      exact (Nat.prime_dvd_prime_iff_eq hQprime Fact.out).mp (hQprime.dvd_of_dvd_pow hdvd)
    have hCyc : IsCyclic (G ⧸ Q) :=
      isCyclic_of_prime_card (p := p) (by rw [← Subgroup.index_eq_card, hQp])
    -- `|Q : Z(G)| ≤ p^n`
    have hrel : (Subgroup.center G).relIndex Q ≤ p ^ n := by
      have h := Subgroup.relIndex_mul_index hZQ
      rw [hQp] at h
      refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < p)
      rw [h]
      rw [pow_succ] at hidx
      exact hidx
    -- `|Q'| ≤ p ^ (n.choose 2)` (帰納法)
    have hZQsub : (Subgroup.center G).subgroupOf Q ≤ Subgroup.center Q := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hx) (y : G))
    have hQidx : (Subgroup.center Q).index ≤ p ^ n :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hZQsub)) hrel
    have hQ' : Nat.card (_root_.commutator Q) ≤ p ^ (n.choose 2) :=
      ih Q inferInstance inferInstance (hP.to_subgroup Q) hQidx
    have hcommQ : Nat.card (⁅Q, Q⁆ : Subgroup G) ≤ p ^ (n.choose 2) := by
      calc Nat.card (⁅Q, Q⁆ : Subgroup G)
          = Nat.card ((_root_.commutator Q).map Q.subtype) := by
            rw [Subgroup.map_subtype_commutator]
        _ = Nat.card (_root_.commutator Q) :=
            (Nat.card_congr (Subgroup.equivMapOfInjective _ _ Q.subtype_injective).toEquiv).symm
        _ ≤ p ^ (n.choose 2) := hQ'
    -- 合体
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ n 1]
      simp [Nat.add_comm]
    calc Nat.card (_root_.commutator G)
        ≤ Nat.card (⁅Q, Q⁆ : Subgroup G) * (Subgroup.center G).relIndex Q :=
          card_commutator_le_of_normal_cyclic_quotient hCyc hZQ
      _ ≤ p ^ (n.choose 2) * p ^ n := Nat.mul_le_mul hcommQ hrel
      _ = p ^ ((n + 1).choose 2) := by rw [hchoose, pow_add]

/-- **Isaacs Problem 4A.10** (書籍の形): `p`-群 `P` で `|P : Z(P)| ≤ p^n` なら
`|P'| ≤ p^{n(n-1)/2}`.

書籍の注意: 「中心の指数が小さい群はある意味で "ほとんど可換" なので, 導来部分群が
大きくならないのは驚くにあたらない」。 -/
theorem card_commutator_le_of_index_center_le [Finite G] {p n : ℕ} [Fact p.Prime]
    (hP : IsPGroup p G) (hidx : (Subgroup.center G).index ≤ p ^ n) :
    Nat.card (_root_.commutator G) ≤ p ^ (n * (n - 1) / 2) := by
  have h := card_commutator_le_pow_choose_two n G inferInstance inferInstance hP hidx
  rwa [Nat.choose_two_right] at h

end

end OddOrder.Isaacs.Ch04
