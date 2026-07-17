import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Dual.Lemmas
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Mathlib.SemidirectProduct
import OddOrder.Mathlib.Subgroup
import OddOrder.Isaacs.Ch04_Commutators.Main.CommutatorIdentities

/-!
# Isaacs §4A — Thm 4.7/4.8: maximal class p-群, Ω_r (pp. 113-122)

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue 0103).
§4A 前半 (identities + Lem 4.5/4.6) は `CommutatorIdentities.lean` へ prefix-split 済 (issue 0122)。
-/


/-!
# OddOrder.Isaacs.Ch04 — Commutators

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 4
"Commutators" (pp. 113-146) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 4A | 交換子の基礎 + 下降中心列 + maximal class p-群 + Ω_r | 4.1 – 4.8 | 完成 |
| 4B | Hall-Witt + three-subgroups lemma + Mann | 4.9 – 4.19 | 4.9-4.13 完成; Mann 後回し |
| 4C | A acts on G via automorphisms | 4.20 – 4.27 | 完成 |
| 4D | Coprime action: Fitting + Thompson P×Q + Baer | 4.28 – 4.38 | 完成 |

## Mathlib direct correspondence (no wrapper)

| Isaacs | mathlib |
|---|---|
| `[g₁, g₂] = 1 ↔ g₁ g₂ = g₂ g₁` | `commutatorElement_eq_one_iff_mul_comm` |
| `⁅H, K⁆ = ⁅K, H⁆` | `Subgroup.commutator_comm` |
| **Lemma 4.2** quotient `f(⁅H,K⁆) = ⁅fH, fK⁆` | `Subgroup.map_commutator` |
| `⁅H,K⁆ = ⊥ ↔ H ⊆ Z_G(K)` | `Subgroup.commutator_eq_bot_iff_le_centralizer` |
| `⁅H₁, H₂⁆ ≤ H₂` (H₂ normal 仮定) | `Subgroup.commutator_le_right` |
| **Lemma 4.9 Three-subgroups** | `Subgroup.commutator_commutator_eq_bot_of_rotate` |
| 下降中心列 `G^k` | `Subgroup.lowerCentralSeries` (`(⊤ : Subgroup G).lowerCentralSeries`), `Subgroup.lowerCentralSeries_succ` |

注: mathlib `(⊤ : Subgroup G).lowerCentralSeries` の index 規約は Isaacs `G^k` と
**オフセット 1 ずれ** — mathlib `lcs 0 = ⊤ = G^1`, `lcs 1 = G' = G^2`, `lcs n = G^{n+1}`.

ノート: [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md)
-/


namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 4A: Thm 4.7/4.8 (pp. 113-122) -/

/-! ### Thm 4.7: maximal class p-群 (helpers + base case m = 1)

surjective `f` での `(lcs G n).map f = lcs H n` (旧自前 helper
`lowerCentralSeries_map_eq_of_surjective`) は mathlib `Subgroup.map_lowerCentralSeries`
(一般 `f` で等号) + `Subgroup.map_top_of_surjective` の合成で直接得る (wrapper 方針). -/

/-- **Thm 4.7, m = 1 case**: `A ⊴ P` abelian, `P` p-群, `|A| = p`, `P/A` cyclic,
`|A ⊓ Z(P)| = p` ⇒ `Group.nilpotencyClass P = 1` (i.e., P abelian, nontrivial).

`|A| = |A ⊓ Z(P)| = p` ⇒ `A ⊆ Z(P)` (両者 ⊆ A で等カード ⇒ 等). P/A cyclic +
`A ⊆ Z(P)` ⇒ P abelian (`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`). -/
theorem nilpotencyClass_eq_one_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] (hP : IsPGroup p P)
    {A : Subgroup P} [A.Normal]
    (_hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCyc : IsCyclic (P ⧸ A))
    (hAcard : Nat.card A = p)
    (hAZcard : Nat.card (A ⊓ Subgroup.center P : Subgroup P) = p) :
    Group.nilpotencyClass P = 1 := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  -- A ⊓ Z(P) ⊆ A, 等カード ⇒ A ⊓ Z(P) = A ⇒ A ⊆ Z(P)
  have hAZ_eq_A : A ⊓ Subgroup.center P = A :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAcard, hAZcard])
  have hA_le_Z : A ≤ Subgroup.center P := by
    rw [← hAZ_eq_A]; exact inf_le_right
  -- P abelian: G/A cyclic + A ⊆ Z(G)
  have hP_abelian : ∀ x y : P, x * y = y * x := by
    have hker_le : (QuotientGroup.mk' A).ker ≤ Subgroup.center P := by
      rw [QuotientGroup.ker_mk']; exact hA_le_Z
    exact ((QuotientGroup.mk' A).isMulCommutative_of_isCyclic_of_ker_le_center
      hker_le).is_comm.comm
  -- commutator P = ⊥ via center P = ⊤
  have hcomm_bot : _root_.commutator P = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top, Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact hP_abelian y x
  -- nilpotencyClass ≤ 1
  have h_class_le : Group.nilpotencyClass P ≤ 1 := by
    rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
      Subgroup.top_lowerCentralSeries_one]
    exact hcomm_bot
  -- P nontrivial (|A| = p ≥ 2)
  have hA_ne_bot : A ≠ ⊥ := by
    intro hA_bot
    rw [hA_bot, Subgroup.card_bot] at hAcard
    have := hp.out.one_lt
    omega
  have hP_nontrivial : Nontrivial P := by
    obtain ⟨x, hx_in_A, hx_ne⟩ : ∃ x : P, x ∈ A ∧ x ≠ 1 := by
      by_contra h
      push Not at h
      apply hA_ne_bot
      rw [Subgroup.eq_bot_iff_forall]
      exact h
    exact ⟨x, 1, hx_ne⟩
  -- nilpotencyClass ≠ 0
  have h_class_ne_zero : Group.nilpotencyClass P ≠ 0 := by
    intro h
    rw [Group.nilpotencyClass_zero_iff_subsingleton] at h
    exact not_subsingleton P h
  omega

/-- Helper: for `f : G →* G' = G/N` (`N` normal) surjective and `H ≤ G`,
`|H.map (mk' N)| · |H ⊓ N| = |H|`. First iso on `(mk' N).comp H.subtype` + Lagrange in `H`. -/
private lemma card_map_mk_mul_card_inf_eq_card {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (H : Subgroup G) :
    Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card (H ⊓ N : Subgroup G) = Nat.card H := by
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : f.ker = (H ⊓ N).subgroupOf H := by
    ext ⟨x, hx⟩
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    exact ⟨fun hxN => ⟨hx, hxN⟩, fun h => h.2⟩
  have hrange : f.range = H.map (QuotientGroup.mk' N) := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, f, MonoidHom.comp_apply,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    exact ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩
  have hSO : Nat.card ((H ⊓ N).subgroupOf H : Subgroup H) = Nat.card (H ⊓ N : Subgroup G) :=
    Nat.card_congr
      ⟨fun x => ⟨((x : H) : G), Subgroup.mem_subgroupOf.mp x.2⟩,
        fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩, Subgroup.mem_subgroupOf.mpr y.2⟩,
        fun _ => rfl, fun _ => rfl⟩
  have hLagr : Nat.card (H ⧸ f.ker) * Nat.card f.ker = Nat.card H :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker).symm
  have hQ : Nat.card (H ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hker, hSO] at hLagr
  rw [hker, hrange] at hQ
  rw [← hQ]; exact hLagr

/-- **Isaacs Thm 4.7** ⭐: Let `A ⊴ P` abelian, `P` a p-group, `|A| = p ^ m`, `P/A` cyclic,
`|A ⊓ Z(P)| = p`. Then `Group.nilpotencyClass P = m`.

**Proof** (Isaacs p.118-119): Induction on `m`.
- `m = 0` is impossible: `|A| = 1` but `|A ⊓ Z(P)| = p ≥ 2`, contradicting `A ⊓ Z(P) ≤ A`.
- `m = 1`: `nilpotencyClass_eq_one_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p`
  (`|A| = |A ⊓ Z(P)| = p` ⇒ `A ⊆ Z(P)` ⇒ `P` abelian).
- `m ≥ 2`: Let `Z = A ⊓ Z(P)`. By Lem 4.6 cardinality, `|commutator P| = p^(m-1)`.
  Since `m-1 ≥ 1`, `commutator P` is nontrivial; by Thm 1.19,
  `commutator P ⊓ Z(P) > ⊥`. Combined with `commutator P ⊓ Z(P) ⊆ A ⊓ Z(P) = Z`
  and `|Z| = p` prime, get `commutator P ⊓ Z(P) = Z`, so `Z ⊆ commutator P`.
  Apply IH to `P̄ = P/Z` and `Ā = A.map mk'`: class `P̄ = m-1`. Lift back via
  `Subgroup.map_lowerCentralSeries` (+ `Subgroup.map_top_of_surjective`). -/
theorem nilpotencyClass_eq_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p_pow
    (m : ℕ) {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCyc : IsCyclic (P ⧸ A))
    (hAcard : Nat.card A = p ^ m)
    (hAZcard : Nat.card (A ⊓ Subgroup.center P : Subgroup P) = p) :
    Group.nilpotencyClass P = m := by
  induction m generalizing P with
  | zero =>
    -- |A| = 1 but |A ⊓ Z(P)| = p ≥ 2, contradicting A ⊓ Z(P) ≤ A
    exfalso
    rw [pow_zero] at hAcard
    have hle : (A ⊓ Subgroup.center P : Subgroup P) ≤ A := inf_le_left
    have hcard_le := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    rw [hAcard, hAZcard] at hcard_le
    have := hp.out.one_lt
    omega
  | succ k ih =>
    haveI : Group.IsNilpotent P := hP.isNilpotent
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · -- k = 0, i.e., m = 1: use existing base case
      have hAcard' : Nat.card A = p := by rw [hAcard]; ring
      exact nilpotencyClass_eq_one_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p
        hP hAb hCyc hAcard' hAZcard
    -- k ≥ 1, i.e., m = k+1 ≥ 2
    have hp_prime : p.Prime := hp.out
    have hp_pos : 0 < p := hp_prime.pos
    have hp1 : 1 < p := hp_prime.one_lt
    -- Step 1: commutator P ≤ A (P/A cyclic ⇒ abelian)
    have hG'_le_A : _root_.commutator P ≤ A := by
      letI : CommGroup (P ⧸ A) := IsCyclic.commGroup
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨mul_comm⟩⟩
    -- Step 2: |commutator P| = p^k via Lem 4.6 cardinality
    have hG'_card : Nat.card (_root_.commutator P) = p^k := by
      have h := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
        hAb hCyc
      rw [hAcard, hAZcard, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right hp_pos h
    -- Step 3: commutator P is nontrivial (|commutator P| = p^k ≥ p > 1)
    have hG'_nontriv : Nontrivial (_root_.commutator P : Subgroup P) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hG'_card]
      exact one_lt_pow₀ hp1 hk_pos.ne'
    -- Step 4: Thm 1.19 ⇒ commutator P ⊓ Z(P) nontrivial
    haveI : Nontrivial ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hP
        (N := _root_.commutator P) hG'_nontriv
    -- Step 5: commutator P ⊓ Z(P) ⊆ A ⊓ Z(P), and |A ⊓ Z(P)| = p, so equality holds
    have h_inf_le : ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P)
        ≤ (A ⊓ Subgroup.center P : Subgroup P) :=
      inf_le_inf_right _ hG'_le_A
    have h_inf_eq : ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P)
        = (A ⊓ Subgroup.center P : Subgroup P) := by
      refine Subgroup.eq_of_le_of_card_ge h_inf_le ?_
      rw [hAZcard]
      have h_nontriv_card : 1 < Nat.card ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      -- Apply Lagrange: card H divides card K = p, with card H > 1 ⇒ card H = p
      have h_dvd : Nat.card ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P)
          ∣ Nat.card (A ⊓ Subgroup.center P : Subgroup P) :=
        Subgroup.card_dvd_of_le h_inf_le
      rw [hAZcard] at h_dvd
      rcases hp_prime.eq_one_or_self_of_dvd _ h_dvd with h_one | h_self
      · omega
      · exact h_self.symm.le
    -- Set Z := A ⊓ Z(P)
    set Z : Subgroup P := A ⊓ Subgroup.center P with hZ_def
    have hZ_card : Nat.card Z = p := hAZcard
    have hZ_le_A : Z ≤ A := inf_le_left
    have hZ_le_center : Z ≤ Subgroup.center P := inf_le_right
    -- Z ≤ commutator P
    have hZ_le_G' : Z ≤ _root_.commutator P := by
      intro x hx
      have hx_in_inf : x ∈ ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P) := by
        rw [h_inf_eq]; exact hx
      exact (Subgroup.mem_inf.mp hx_in_inf).1
    -- Z is normal in P (Z ≤ Z(P))
    haveI hZ_normal : Z.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxZ : x ∈ Subgroup.center P := hZ_le_center hx
      rw [Subgroup.mem_center_iff] at hxZ
      have : g * x * g⁻¹ = x := by rw [hxZ g]; group
      rw [this]; exact hx
    -- Step 6: Work in P̄ = P / Z
    let φ : P →* P ⧸ Z := QuotientGroup.mk' Z
    have hφ_surj : Function.Surjective φ := QuotientGroup.mk_surjective
    haveI : Finite (P ⧸ Z) := Finite.of_surjective φ hφ_surj
    have hφ_ker : φ.ker = Z := QuotientGroup.ker_mk' Z
    -- Ā := image of A
    let Abar : Subgroup (P ⧸ Z) := A.map φ
    haveI hAbar_normal : Abar.Normal := Subgroup.Normal.map ‹A.Normal› φ hφ_surj
    -- Ā abelian
    have hAbar_Ab : ∀ a ∈ Abar, ∀ b ∈ Abar, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha'A, rfl⟩ := ha
      obtain ⟨b', hb'A, rfl⟩ := hb
      rw [← map_mul, ← map_mul, hAb a' ha'A b' hb'A]
    -- P̄ / Ā ≃* P / A ⇒ cyclic
    have hAbar_quot_cyclic : IsCyclic ((P ⧸ Z) ⧸ Abar) := by
      let e : ((P ⧸ Z) ⧸ Abar) ≃* P ⧸ A :=
        QuotientGroup.quotientQuotientEquivQuotient (G := P) Z A hZ_le_A
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    -- IsPGroup p P̄
    have hPbar : IsPGroup p (P ⧸ Z) := hP.to_quotient Z
    -- |A ⊓ Z| = |Z| = p (since Z ≤ A ⇒ A ⊓ Z = Z)
    have hAZ_inter_eq : (A ⊓ Z : Subgroup P) = Z := inf_of_le_right hZ_le_A
    -- |Ā| = p^k via card_map_mk_mul_card_inf_eq_card
    have hAbar_card : Nat.card Abar = p^k := by
      have h := card_map_mk_mul_card_inf_eq_card (N := Z) A
      rw [hAZ_inter_eq, hZ_card, hAcard, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right hp_pos h
    -- |commutator P ⊓ Z| = |Z| = p (since Z ≤ commutator P)
    have hG'Z_inter_eq : ((_root_.commutator P) ⊓ Z : Subgroup P) = Z := inf_of_le_right hZ_le_G'
    -- commutator P̄ = (commutator P).map φ (by lcs_map at n=1)
    have h_lcs1 : Subgroup.map φ (_root_.commutator P) = _root_.commutator (P ⧸ Z) := by
      have := Subgroup.map_lowerCentralSeries (S := (⊤ : Subgroup P)) φ 1
      rwa [Subgroup.map_top_of_surjective φ hφ_surj, Subgroup.top_lowerCentralSeries_one,
        Subgroup.top_lowerCentralSeries_one] at this
    -- |commutator P̄| = p^(k-1)
    have hGbar'_card : Nat.card (_root_.commutator (P ⧸ Z)) = p^(k-1) := by
      have h := card_map_mk_mul_card_inf_eq_card (N := Z) (_root_.commutator P)
      rw [hG'Z_inter_eq, hZ_card, hG'_card] at h
      -- h: |(commutator P).map φ| * p = p^k
      rw [h_lcs1] at h
      have hk_succ : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
      rw [hk_succ, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right hp_pos h
    -- |Ā ⊓ Z(P̄)| = p (apply Lem 4.6 cardinality to P̄, Ā)
    have hAbarZbar_card : Nat.card (Abar ⊓ Subgroup.center (P ⧸ Z) : Subgroup (P ⧸ Z)) = p := by
      have h := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
        hAbar_Ab hAbar_quot_cyclic
      rw [hGbar'_card, hAbar_card] at h
      -- h: p^(k-1) * |Ā ⊓ Z(P̄)| = p^k
      have hk_succ : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
      rw [hk_succ, pow_succ] at h
      have hp_pow_pos : 0 < p^(k-1) := pow_pos hp_pos _
      exact Nat.eq_of_mul_eq_mul_left hp_pow_pos h
    -- Apply IH
    have h_class_Pbar : Group.nilpotencyClass (P ⧸ Z) = k :=
      ih hPbar hAbar_Ab hAbar_quot_cyclic hAbar_card hAbarZbar_card
    -- Translate to lcs: lcs P̄ k = ⊥ and lcs P̄ (k-1) ≠ ⊥
    have h_lcs_Pbar_k : (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries k = ⊥ :=
      Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h_class_Pbar.le
    have h_lcs_Pbar_km1_ne : (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries (k - 1) ≠ ⊥ := by
      intro h_eq
      have := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h_eq
      rw [h_class_Pbar] at this
      omega
    -- lcs P k ≤ Z (lift lcs P̄ k = ⊥ back)
    have h_lcs_P_k_le_Z : (⊤ : Subgroup P).lowerCentralSeries k ≤ Z := by
      have h_map : Subgroup.map φ ((⊤ : Subgroup P).lowerCentralSeries k)
          = (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries k := by
        rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective φ hφ_surj]
      rw [h_lcs_Pbar_k] at h_map
      have h_le_ker : (⊤ : Subgroup P).lowerCentralSeries k ≤ φ.ker :=
        (Subgroup.map_eq_bot_iff _).mp h_map
      rw [hφ_ker] at h_le_ker
      exact h_le_ker
    -- lcs P (k+1) = ⊥ (lcs P k ≤ Z ≤ Z(P))
    have h_lcs_P_kp1 : (⊤ : Subgroup P).lowerCentralSeries (k + 1) = ⊥ :=
      Subgroup.lowerCentralSeries_succ_eq_bot ⊤ (h_lcs_P_k_le_Z.trans hZ_le_center)
    -- lcs P k ≠ ⊥
    have h_lcs_P_k_ne : (⊤ : Subgroup P).lowerCentralSeries k ≠ ⊥ := by
      -- Case k = 1: lcs P 1 = commutator P ≠ ⊥
      -- Case k ≥ 2: lcs P (k-1) ⊆ commutator P ⊆ A, lcs P (k-1) ⊄ Z ⇒ ...
      by_cases hk1 : k = 1
      · -- k = 1
        subst hk1
        rw [Subgroup.top_lowerCentralSeries_one]
        intro h_bot
        rw [h_bot, Subgroup.card_bot] at hG'_card
        -- p^1 = 1 ⇒ p = 1, contradiction
        rw [pow_one] at hG'_card
        omega
      · -- k ≥ 2: lcs P (k-1) ⊆ commutator P ⊆ A,
        -- lcs P (k-1) ⊄ Z ⇒ lcs P (k-1) ⊄ Z(P) ⇒ lcs P k ≠ ⊥
        intro h_lcs_k_bot
        -- lcs P (k-1) maps to lcs P̄ (k-1) ≠ ⊥
        have h_map_km1 : Subgroup.map φ ((⊤ : Subgroup P).lowerCentralSeries (k - 1))
            = (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries (k - 1) := by
          rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective φ hφ_surj]
        -- lcs P (k-1) ⊄ Z (= φ.ker)
        have h_lcs_km1_nle_Z : ¬ (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ Z := by
          intro h_le
          have h_le_ker : (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ φ.ker := by
            rw [hφ_ker]; exact h_le
          have : Subgroup.map φ ((⊤ : Subgroup P).lowerCentralSeries (k - 1)) = ⊥ :=
            (Subgroup.map_eq_bot_iff _).mpr h_le_ker
          rw [h_map_km1] at this
          exact h_lcs_Pbar_km1_ne this
        -- lcs P (k-1) ⊆ commutator P ⊆ A (using k - 1 ≥ 1, lcs decreasing)
        have hk_one_le : 1 ≤ k - 1 := by omega
        have h_lcs_km1_le_G' :
            (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ _root_.commutator P := by
          rw [← Subgroup.top_lowerCentralSeries_one]
          exact (⊤ : Subgroup P).lowerCentralSeries_antitone hk_one_le
        have h_lcs_km1_le_A : (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ A :=
          h_lcs_km1_le_G'.trans hG'_le_A
        -- ∃ x ∈ lcs P (k-1), x ∉ Z
        rw [SetLike.not_le_iff_exists] at h_lcs_km1_nle_Z
        obtain ⟨x, hx_in, hx_notZ⟩ := h_lcs_km1_nle_Z
        -- x ∈ A but x ∉ Z = A ⊓ Z(P), so x ∉ Z(P) (since x ∈ A)
        have hx_in_A : x ∈ A := h_lcs_km1_le_A hx_in
        have hx_notZP : x ∉ Subgroup.center P := by
          intro hxZP
          exact hx_notZ (Subgroup.mem_inf.mpr ⟨hx_in_A, hxZP⟩)
        -- So ∃ y, [x, y] ≠ 1 (x not in center)
        rw [Subgroup.mem_center_iff] at hx_notZP
        push Not at hx_notZP
        obtain ⟨y, hxy⟩ := hx_notZP
        -- [x, y] ∈ ⁅lcs P (k-1), ⊤⁆ = lcs P k via lcs definition
        have h_xy_in_kp : ⁅x, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries ((k - 1) + 1) := by
          show ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P).lowerCentralSeries (k - 1), (⊤ : Subgroup P)⁆
          exact Subgroup.commutator_mem_commutator hx_in (Subgroup.mem_top y)
        have hk_succ : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
        rw [hk_succ] at h_xy_in_kp
        -- lcs P k = ⊥ ⇒ [x, y] = 1 ⇒ x*y = y*x, contradiction
        rw [h_lcs_k_bot, Subgroup.mem_bot] at h_xy_in_kp
        rw [commutatorElement_eq_one_iff_mul_comm] at h_xy_in_kp
        exact hxy h_xy_in_kp.symm
    -- Conclude: Group.nilpotencyClass P = k + 1
    refine Nat.le_antisymm ?_ ?_
    · -- ≤ : lcs P (k+1) = ⊥
      exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h_lcs_P_kp1
    · -- ≥ : NOT (nilpotencyClass ≤ k)
      by_contra h
      push Not at h
      have : (⊤ : Subgroup P).lowerCentralSeries k = ⊥ :=
        Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (Nat.lt_succ_iff.mp h)
      exact h_lcs_P_k_ne this

/-! ### Commutator collection in class ≤ 2 (Thm 4.8 の前段) -/

/-- General identity: `y * x = ⁅y, x⁆ * x * y` (no hypothesis). -/
private lemma mul_eq_commutator_mul (x y : G) :
    y * x = ⁅y, x⁆ * x * y := by
  simp only [commutatorElement_def]
  group

/-- In class ≤ 2 (`commutator G ≤ Z(G)`): `y * x = x * y * ⁅y, x⁆`.
`⁅y, x⁆` 中心で `y * x = ⁅y, x⁆ * (x * y) = (x * y) * ⁅y, x⁆`. -/
lemma mul_comm_commutator_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    y * x = x * y * ⁅y, x⁆ := by
  have hc : ⁅y, x⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  rw [mul_eq_commutator_mul, mul_assoc]
  exact (Subgroup.mem_center_iff.mp hc (x * y)).symm

/-- In class ≤ 2: `⁅y, x⁆` は中心で全ての元と可換. -/
private lemma commute_commutator_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    Commute ⁅y, x⁆ z := by
  have hc : ⁅y, x⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  exact (Subgroup.mem_center_iff.mp hc z).symm

/-- In class ≤ 2: `y^k * x = x * y^k * ⁅y, x⁆^k` (induction on `k`).
各回 `y` を `x` の右に passing で `⁅y, x⁆` が 1 個発生. -/
private lemma pow_mul_eq_mul_pow_commutator_pow_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) (k : ℕ) :
    y^k * x = x * y^k * ⁅y, x⁆^k := by
  induction k with
  | zero => simp
  | succ j ih =>
    -- ⁅y, x⁆^j commutes with y (central).
    have h_pow_y : ⁅y, x⁆^j * y = y * ⁅y, x⁆^j :=
      (commute_commutator_of_class_le_two hC x y y).pow_left j
    -- 計算 chain
    have step : y^(j+1) * x = x * y^(j+1) * ⁅y, x⁆^(j+1) := by
      rw [pow_succ y j, mul_assoc (y^j) y x,
          mul_comm_commutator_of_class_le_two hC x y]
      -- Goal: y^j * (x * y * ⁅y, x⁆) = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show y^j * (x * y * ⁅y, x⁆) = y^j * x * y * ⁅y, x⁆ by ac_rfl]
      rw [ih]
      -- Goal: x * y^j * ⁅y, x⁆^j * y * ⁅y, x⁆ = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show x * y^j * ⁅y, x⁆^j * y * ⁅y, x⁆ =
            x * y^j * (⁅y, x⁆^j * y) * ⁅y, x⁆ by ac_rfl, h_pow_y]
      -- Goal: x * y^j * (y * ⁅y, x⁆^j) * ⁅y, x⁆ = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show x * y^j * (y * ⁅y, x⁆^j) * ⁅y, x⁆ =
            x * (y^j * y) * (⁅y, x⁆^j * ⁅y, x⁆) by ac_rfl]
      rw [← pow_succ y j, ← pow_succ ⁅y, x⁆ j]
    exact step

/-- **Commutator collection formula in class ≤ 2**:
`(x * y)^n = x^n * y^n * ⁅y, x⁆^(n*(n-1)/2)`.

**証明** (Isaacs p.120): `n` についての induction. step:
`(xy)^(k+1) = (xy)^k · xy = x^k y^k ⁅y,x⁆^(k(k-1)/2) · xy`. 中心元と移動可換で
`y^k · x = x · y^k · ⁅y,x⁆^k` (上記 helper). 整理して指数加法 `k + k(k-1)/2 = k(k+1)/2`. -/
theorem mul_pow_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) (n : ℕ) :
    (x * y)^n = x^n * y^n * ⁅y, x⁆^(n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    -- Goal: x^k * y^k * ⁅y,x⁆^(k(k-1)/2) * (x*y) = x^(k+1) * y^(k+1) * ⁅y,x⁆^((k+1)k/2)
    -- ⁅y, x⁆^(k(k-1)/2) commutes with x and y separately.
    have h_xy : ⁅y, x⁆^(k * (k - 1) / 2) * (x * y) = (x * y) * ⁅y, x⁆^(k * (k - 1) / 2) :=
      ((commute_commutator_of_class_le_two hC x y (x * y)).pow_left _)
    -- ⁅y, x⁆^k commutes with y.
    have h_ky : ⁅y, x⁆^k * y = y * ⁅y, x⁆^k :=
      ((commute_commutator_of_class_le_two hC x y y).pow_left k)
    -- Re-associate to bring (y^k * x) together
    rw [show x^k * y^k * ⁅y, x⁆^(k * (k - 1) / 2) * (x * y) =
          x^k * y^k * (⁅y, x⁆^(k * (k - 1) / 2) * (x * y)) by ac_rfl, h_xy]
    -- Goal: x^k * y^k * ((x*y) * ⁅y,x⁆^(k(k-1)/2)) = ...
    rw [show x^k * y^k * (x * y * ⁅y, x⁆^(k * (k - 1) / 2)) =
          x^k * (y^k * x) * y * ⁅y, x⁆^(k * (k - 1) / 2) by ac_rfl,
        pow_mul_eq_mul_pow_commutator_pow_of_class_le_two hC x y k]
    -- Goal: x^k * (x * y^k * ⁅y,x⁆^k) * y * ⁅y,x⁆^(k(k-1)/2) = ...
    rw [show x^k * (x * y^k * ⁅y, x⁆^k) * y * ⁅y, x⁆^(k * (k - 1) / 2) =
          x^k * x * y^k * (⁅y, x⁆^k * y) * ⁅y, x⁆^(k * (k - 1) / 2) by ac_rfl,
        h_ky]
    -- Goal: x^k * x * y^k * (y * ⁅y,x⁆^k) * ⁅y,x⁆^(k(k-1)/2) = ...
    rw [show x^k * x * y^k * (y * ⁅y, x⁆^k) * ⁅y, x⁆^(k * (k - 1) / 2) =
          (x^k * x) * (y^k * y) * (⁅y, x⁆^k * ⁅y, x⁆^(k * (k - 1) / 2)) by ac_rfl]
    rw [← pow_succ x k, ← pow_succ y k, ← pow_add]
    -- Goal: x^(k+1) * y^(k+1) * ⁅y,x⁆^(k + k(k-1)/2) = x^(k+1) * y^(k+1) * ⁅y,x⁆^((k+1)k/2)
    congr 2
    -- k + k(k-1)/2 = (k+1)k/2 over Nat. Need that k*(k-1) is even.
    rcases k with _ | j
    · simp
    · -- k = j+1: (j+1) + (j+1)*j/2 = (j+2)*(j+1)/2
      simp only [Nat.add_succ_sub_one, Nat.add_zero]
      -- (j+1)*j and (j+2)*(j+1) are both even (consecutive integers)
      have h1 : 2 ∣ (j+1) * j := by
        rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd
      have h2 : 2 ∣ (j+1+1) * (j+1) := by
        rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self (j+1)).two_dvd
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      -- Eliminate quadratics: (j+2)(j+1) = (j+1)*j + 2*(j+1)
      have key : (j+1+1) * (j+1) = (j+1) * j + 2 * (j+1) := by ring
      rw [key, hm] at hn
      omega

/-! ### Isaacs Thm 4.8(a) -/

/-- **Isaacs Theorem 4.8(a)**: `p > 2`, `G` is a group with `commutator G ≤ Z(G)`
(class ≤ 2). Then `{x ∈ G : x^p = 1}` is a subgroup.

**証明**: 唯一の閉性 (mul_mem). `x^p = y^p = 1` ⇒
`(xy)^p = x^p y^p ⁅y, x⁆^(p(p-1)/2) = ⁅y, x⁆^(p(p-1)/2)` (collection).
`⁅·, x⁆` 左 hom + `y^p = 1` ⇒ `⁅y, x⁆^p = ⁅y^p, x⁆ = ⁅1, x⁆ = 1`.
`p > 2 odd` ⇒ `(p-1)/2 ∈ ℕ` ⇒ `p(p-1)/2 = p · (p-1)/2` で `p` の倍数 ⇒
`⁅y, x⁆^(p(p-1)/2) = (⁅y, x⁆^p)^((p-1)/2) = 1`. -/
def setOfPowEqOne (hC : _root_.commutator G ≤ Subgroup.center G) {p : ℕ}
    (hp : Odd p) : Subgroup G where
  carrier := {x | x^p = 1}
  one_mem' := by show (1 : G)^p = 1; exact one_pow p
  inv_mem' := by
    intro x (hx : x^p = 1)
    show x⁻¹^p = 1
    rw [inv_pow, hx, inv_one]
  mul_mem' := by
    intro x y (hx : x^p = 1) (hy : y^p = 1)
    show (x * y)^p = 1
    rw [mul_pow_of_class_le_two hC, hx, hy, one_mul, one_mul]
    -- Goal: ⁅y, x⁆^(p*(p-1)/2) = 1
    have hcom_p : ⁅y, x⁆^p = 1 := by
      rw [← commutatorElement_pow_left_of_class_le_two hC, hy, commutatorElement_one_left]
    -- p odd ⇒ p - 1 = 2k for some k ⇒ p*(p-1)/2 = p*k.
    obtain ⟨k, hk⟩ := hp
    have hdiv : p * (p - 1) / 2 = p * k := by
      subst hk
      have h1 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [h1, Nat.mul_div_assoc _ (Dvd.intro k rfl)]
      rw [show 2 * k / 2 = k from Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 2)]
    rw [hdiv, pow_mul, hcom_p, one_pow]

/-- **Isaacs Theorem 4.8(b)**: `p > 2` (odd), `commutator G ≤ Z(G)` (class ≤ 2),
全交換子の `p` 乗が `1` ⇒ `x ↦ x^p : G →* G` は (Monoid) 準同型.

**証明**: collection formula `(xy)^p = x^p · y^p · ⁅y, x⁆^(p(p-1)/2)`.
仮定で `⁅y, x⁆^p = 1` + `p` odd ⇒ `p ∣ p(p-1)/2` ⇒ `⁅y, x⁆^(p(p-1)/2) = 1`.
よって `(xy)^p = x^p · y^p`. `1^p = 1` は自明. -/
def powPHom (hC : _root_.commutator G ≤ Subgroup.center G) {p : ℕ} (hp : Odd p)
    (hcomp : ∀ c ∈ _root_.commutator G, c ^ p = 1) : G →* G where
  toFun x := x^p
  map_one' := one_pow p
  map_mul' x y := by
    show (x * y)^p = x^p * y^p
    rw [mul_pow_of_class_le_two hC]
    -- Goal: x^p * y^p * ⁅y, x⁆^(p*(p-1)/2) = x^p * y^p
    have hcom_p : ⁅y, x⁆^p = 1 := hcomp ⁅y, x⁆ (commutatorElement_mem_commutator_top y x)
    obtain ⟨k, hk⟩ := hp
    have hdiv : p * (p - 1) / 2 = p * k := by
      subst hk
      have h1 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [h1, Nat.mul_div_assoc _ (Dvd.intro k rfl)]
      rw [show 2 * k / 2 = k from Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 2)]
    rw [hdiv, pow_mul, hcom_p, one_pow, mul_one]

end -- 4A

end OddOrder.Isaacs.Ch04
