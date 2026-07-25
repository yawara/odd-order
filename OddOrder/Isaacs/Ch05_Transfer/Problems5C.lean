/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SchurZassenhaus
import OddOrder.GroupTheory.WeaklyClosed
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# Isaacs Chapter 5 — Problems 5C (transfer と非単純性)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 5C (書籍 pp. 162-164)。

現在の実装:

* **5C.1** `hasNormalPComplement_of_commutator_inf_sylow_eq_bot` — `G' ⊓ P = ⊥` なら
  正規 `p`-補群をもつ (Burnside を Thm 5.18 から導くときの実質的な段)。
* **5C.5** `exists_mem_normalizer_conj_eq_of_normal` — `P ∈ Syl_p(G)` の正規部分群 `A`, `B`
  が `G`-共役なら `N_G(P)`-共役。系として `A` が `P` の特性部分群なら `A = B`。

⚠ **5C.6 (weak closure) は hub レーンが `OddOrder/GroupTheory/WeaklyClosed.lean` で
着手中** (issue 9503; `IsWeaklyClosed` / `exists_mem_normalizer_conj_eq` 等) なので
本ファイルでは扱わない。
-/

open scoped commutatorElement

namespace OddOrder.Isaacs.Ch05

section /- 5C: Problems (pp. 162-164) -/

variable {G : Type*} [Group G]

/-! ### Problem 5C.1 -/

/-- `G' ⊓ P = ⊥` (`P ∈ Syl_p(G)`) なら `p ∤ |G'|`。

`G'` の位数 `p` の元 `x` を取ると `⟨x⟩` はある Sylow `Q` に入り, `Q` は `P` に共役。
`G'` は正規なので共役先でも `x^g ∈ G' ⊓ P = ⊥`, 矛盾。 -/
theorem not_dvd_card_commutator_of_inf_sylow_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (h : _root_.commutator G ⊓ (P : Subgroup G) = ⊥) :
    ¬ p ∣ Nat.card (_root_.commutator G) := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(_root_.commutator G)) p hdvd
  have hxord : orderOf (x : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hpg : IsPGroup p (Subgroup.zpowers (x : G)) :=
    IsPGroup.of_card ((Nat.card_zpowers _).trans (hxord.trans (pow_one p).symm))
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hxQ : (x : G) ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers _)
  have hxP : g * (x : G) * g⁻¹ ∈ (P : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨(x : G), hxQ, rfl⟩
  have hxC : g * (x : G) * g⁻¹ ∈ _root_.commutator G :=
    (inferInstance : (_root_.commutator G).Normal).conj_mem _ x.2 g
  have hone : g * (x : G) * g⁻¹ = 1 := by
    have : g * (x : G) * g⁻¹ ∈ _root_.commutator G ⊓ (P : Subgroup G) := ⟨hxC, hxP⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hx1 : (x : G) = 1 := by
    have := hone
    group at this ⊢
    calc (x : G) = g⁻¹ * (g * (x : G) * g⁻¹) * g := by group
      _ = 1 := by rw [hone]; group
  rw [hx1, orderOf_one] at hxord
  exact Nat.Prime.ne_one Fact.out hxord.symm

/-- **Isaacs Problem 5C.1 の鍵**: `G' ⊓ P = ⊥` (`P ∈ Syl_p(G)`) なら `G` は正規 `p`-補群をもつ。

Isaacs Thm 5.18 (強形) は `N_G(P) ≤ C_G(P)` の下で `G' ⊓ P = ⊥` を与えるので,
本補題と合わせると Burnside の正規 `p`-補群定理 (Thm 5.13) が Thm 5.18 の系として出る
(これが Problem 5C.1)。

**証明**: `p ∤ |G'|` (`not_dvd_card_commutator_of_inf_sylow_eq_bot`)。可換群
`Abelianization G` の Sylow `p` は正規なので Schur-Zassenhaus で補群 `K` を取り,
`N := (Abelianization.of)⁻¹(K)` とおく。`|G : N| = |K の補群| = |P|` で `|N|` は `p` と
互いに素なので, 任意の Sylow `Q` と位数条件 + 互いに素性から `IsComplement' N Q`。 -/
theorem hasNormalPComplement_of_commutator_inf_sylow_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (h : _root_.commutator G ⊓ (P : Subgroup G) = ⊥) :
    HasNormalPComplement p G := by
  classical
  have hp' := not_dvd_card_commutator_of_inf_sylow_eq_bot P h
  obtain ⟨PA⟩ : Nonempty (Sylow p (Abelianization G)) := inferInstance
  -- Schur-Zassenhaus で `Abelianization G` の `p`-補群を取る
  have hcop : Nat.Coprime (Nat.card (PA : Subgroup (Abelianization G)))
      (PA : Subgroup (Abelianization G)).index := by
    rw [PA.card_eq_multiplicity]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr PA.not_dvd_index)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set N : Subgroup G := K.comap (Abelianization.of : G →* Abelianization G) with hN
  -- `|G : N| = |PA|`
  have hsurj : Function.Surjective (Abelianization.of : G →* Abelianization G) := fun a =>
    QuotientGroup.induction_on a fun g => ⟨g, rfl⟩
  have hindexN : N.index = Nat.card (PA : Subgroup (Abelianization G)) := by
    rw [hN, Subgroup.index_comap_of_surjective _ hsurj]
    exact hK.index_eq_card
  -- `|PA| = |P|`
  have hfact : (Nat.card (Abelianization G)).factorization p = (Nat.card G).factorization p := by
    have hcm : Nat.card (_root_.commutator G) * Nat.card (Abelianization G) = Nat.card G := by
      have := Subgroup.card_mul_index (_root_.commutator G)
      rwa [Subgroup.index] at this
    have hne1 : Nat.card (_root_.commutator G) ≠ 0 := Nat.card_pos.ne'
    have hne2 : Nat.card (Abelianization G) ≠ 0 := Nat.card_pos.ne'
    rw [← hcm, Nat.factorization_mul hne1 hne2]
    simp [Nat.factorization_eq_zero_of_not_dvd hp']
  have hcardPA : Nat.card (PA : Subgroup (Abelianization G)) = Nat.card (P : Subgroup G) := by
    rw [PA.card_eq_multiplicity, P.card_eq_multiplicity, hfact]
  -- `p ∤ |N|`
  have hcardN : Nat.card N * Nat.card (P : Subgroup G) = Nat.card G := by
    have := Subgroup.card_mul_index N
    rwa [hindexN, hcardPA] at this
  have hpN : ¬ p ∣ Nat.card N := by
    intro hdvd
    have h1 : p ^ ((Nat.card G).factorization p) = Nat.card (P : Subgroup G) :=
      P.card_eq_multiplicity.symm
    have hpow : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G := by
      calc p ^ ((Nat.card G).factorization p + 1)
          = p * p ^ ((Nat.card G).factorization p) := by rw [pow_succ']
        _ ∣ Nat.card N * Nat.card (P : Subgroup G) := by
            rw [h1]
            exact Nat.mul_dvd_mul hdvd dvd_rfl
        _ = Nat.card G := hcardN
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hpow
    omega
  refine ⟨N, inferInstance, fun Q => ?_⟩
  have hQcard : Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) :=
    Nat.card_congr (Sylow.equiv Q P).toEquiv
  refine Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hQcard]; exact hcardN) ?_
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [hQcard, P.card_eq_multiplicity]
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm

/-! ### Problem 5C.2 の要 -/

/-- `U ≤ V` で `V` 可換, `|V : U| = 2` (2 つの `U` 外の元は `U` を法として一致),
`U`, `V` が `n` の共役で不変なら, `n` は `V/U` に自明に作用する。 -/
theorem inv_mul_conj_mem_of_index_two {U V : Subgroup G}
    (hUne : ∀ y ∈ V, ∀ z ∈ V, y ∉ U → z ∉ U → y⁻¹ * z ∈ U)
    {n : G} (hUinv : ∀ u ∈ U, n * u * n⁻¹ ∈ U) (hUinv' : ∀ u ∈ U, n⁻¹ * u * n ∈ U)
    (hVinv : ∀ y ∈ V, n * y * n⁻¹ ∈ V)
    {x : G} (hx : x ∈ V) : x⁻¹ * (n * x * n⁻¹) ∈ U := by
  by_cases hxU : x ∈ U
  · exact U.mul_mem (U.inv_mem hxU) (hUinv x hxU)
  · have hnx : n * x * n⁻¹ ∈ V := hVinv x hx
    have hnxU : n * x * n⁻¹ ∉ U := by
      intro hcon
      have hback : n⁻¹ * (n * x * n⁻¹) * n = x := by group
      exact hxU (hback ▸ hUinv' _ hcon)
    exact hUne x hx _ hnx hxU hnxU

/-- ⭐ **Problem 5C.2 の fusion 段**: `P` が可換 Sylow で `V ≤ P`, かつ `N_G(P)` が
`V/U` に自明作用するなら, `V` の元の `G`-共役で `P` に入るものは `U` を法として元と一致する。

`P` が可換なので `V ≤ P ≤ C_G(P)` で, Isaacs Lemma 5.12
(`normalizer_controls_centralizer_fusion`) により `G`-共役は `N_G(P)`-共役に置き換えられる。 -/
theorem inv_mul_conj_mem_of_fusion [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    {U V : Subgroup G} (hVP : V ≤ (P : Subgroup G))
    (hUV : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), ∀ x ∈ V,
      x⁻¹ * (n * x * n⁻¹) ∈ U)
    {x g : G} (hx : x ∈ V) (hgx : g * x * g⁻¹ ∈ (P : Subgroup G)) :
    x⁻¹ * (g * x * g⁻¹) ∈ U := by
  have hxC : x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hab q hq x (hVP hx)
  have hyC : g * x * g⁻¹ ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hab q hq _ hgx
  obtain ⟨n, hnN, hneq⟩ := normalizer_controls_centralizer_fusion P hxC hyC rfl
  rw [← hneq]
  exact hUV n hnN x hx

/-- ⭐ **Problem 5C.2 の transfer 段** (可換な target `A` を変数にした形):
`P` 可換 Sylow, `V ≤ P`, `N_G(P)` が `V/U` に自明作用するとき, 任意の可換群への
準同型 `ϕ : ↥P →* A` の transfer は `x ∈ V` 上で `ϕ(x)^{|G:P|}` と `ϕ(U)` を法として一致する。

⭐ **target を変数 `A` にすると `↥P` の `CommGroup` instance diamond を完全に回避できる**
(`↥P` 自身や `↥P ⧸ U` を target にすると `Subgroup.toGroup` と `CommGroup.toGroup` が
unify しない)。5C.2 では `A := Abelianization ↥P`, `ϕ := Abelianization.of` を取る
(`P` 可換なので `ϕ` は単射)。

軌道分解版の transfer 評価の各因子を fusion 段 (`inv_mul_conj_mem_of_fusion`) で
`ϕ(x^{n_q}) · ϕ(u_q)` (`u_q ∈ U`) に分解し, `A` 可換ゆえ積をまとめる。
⚠ mathlib の `MonoidHom.transfer_eq_pow` は「共役が元を厳密に固定する」ことを要求するので
使えない (法 `U` の弱い仮定しかない)。 -/
theorem transfer_inv_pow_mul_mem_map {A : Type*} [CommGroup A] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (ϕ : ↥(P : Subgroup G) →* A)
    (hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    {U V : Subgroup G} (hUP : U ≤ (P : Subgroup G)) (hVP : V ≤ (P : Subgroup G))
    (hUV : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), ∀ y ∈ V,
      y⁻¹ * (n * y * n⁻¹) ∈ U)
    {x : G} (hx : x ∈ V) :
    (ϕ ⟨x, hVP hx⟩ ^ (P : Subgroup G).index)⁻¹ * MonoidHom.transfer ϕ x ∈
      (U.subgroupOf (P : Subgroup G)).map ϕ := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers x) (G ⧸ (P : Subgroup G))) :=
    Fintype.ofFinite _
  set n : MulAction.orbitRel.Quotient (Subgroup.zpowers x) (G ⧸ (P : Subgroup G)) → ℕ :=
    fun q => Function.minimalPeriod (fun y : G ⧸ (P : Subgroup G) => x • y) q.out with hn
  have hu : ∀ q, ((x ^ n q)⁻¹ * (q.out.out⁻¹ * x ^ n q * q.out.out)) ∈ U := by
    intro q
    have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (P : Subgroup G) x q.out
    have hconj : q.out.out⁻¹ * (x ^ n q) * (q.out.out⁻¹)⁻¹ ∈ (P : Subgroup G) := by
      simpa using hmem
    simpa using inv_mul_conj_mem_of_fusion P hab hVP hUV (V.pow_mem hx (n q)) hconj
  have hsplit : ∀ q, ϕ ⟨q.out.out⁻¹ * x ^ n q * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem (P : Subgroup G) x q.out⟩
      = ϕ ⟨x, hVP hx⟩ ^ n q *
        ϕ ⟨(x ^ n q)⁻¹ * (q.out.out⁻¹ * x ^ n q * q.out.out), hUP (hu q)⟩ := by
    intro q
    rw [← map_pow, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, SubmonoidClass.coe_pow]
    group
  have hsum : ∑ q, n q = (P : Subgroup G).index := by
    have hcard := Nat.card_congr (Subgroup.quotientEquivSigmaZMod (P : Subgroup G) x)
    rw [Nat.card_sigma] at hcard
    simp only [Nat.card_zmod] at hcard
    exact hcard.symm
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot ϕ x,
    Finset.prod_congr rfl (fun q _ => hsplit q), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hsum, inv_mul_cancel_left]
  refine Subgroup.prod_mem _ fun q _ => ?_
  exact ⟨⟨(x ^ n q)⁻¹ * (q.out.out⁻¹ * x ^ n q * q.out.out), hUP (hu q)⟩,
    Subgroup.mem_subgroupOf.mpr (by simpa using hu q), rfl⟩

/-- ⭐ **Problem 5C.2 の核**: `G` が完全群 (`G' = G`) なら, 可換 Sylow-2 `P` の中に
`N_G(P)` 不変で「指数 2」の対 `U ≤ V` (`V` の元の 2 乗が `U` に入る) と `U` の外の元は
共存できない。

**証明**: `A := Abelianization ↥P`, `ϕ := Abelianization.of` (`P` 可換なので `ϕ` は単射)。
`transfer_inv_pow_mul_mem_map` より `(ϕ⟨x⟩^{|G:P|})⁻¹ · transfer ϕ x ∈ ϕ(U)`。
`G' = G` かつ `A` 可換なので `transfer ϕ x = 1`, ゆえに `ϕ⟨x^{|G:P|}⟩ ∈ ϕ(U)`,
`ϕ` 単射より `x^{|G:P|} ∈ U`。しかし `|G:P|` は奇数 (`Sylow.not_dvd_index`) で
`x ∉ U`, `y ∈ V ⇒ y² ∈ U` だから `x^{奇数} ∉ U` — 矛盾。 -/
theorem not_mem_of_commutator_eq_top [Finite G] (P : Sylow 2 G)
    (hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    (hperfect : _root_.commutator G = ⊤)
    {U V : Subgroup G} (hUP : U ≤ (P : Subgroup G)) (hVP : V ≤ (P : Subgroup G))
    (hUV : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), ∀ y ∈ V,
      y⁻¹ * (n * y * n⁻¹) ∈ U)
    (hsq : ∀ y ∈ V, y ^ 2 ∈ U)
    {x : G} (hx : x ∈ V) (hxU : x ∉ U) : False := by
  classical
  set ϕ : ↥(P : Subgroup G) →* Abelianization ↥(P : Subgroup G) := Abelianization.of with hϕ
  -- `ϕ` は単射 (`P` 可換ゆえ `commutator ↥P = ⊥`)
  have hcomm_bot : _root_.commutator ↥(P : Subgroup G) = ⊥ := by
    rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hab a a.2 b b.2)
  have hinj : Function.Injective ϕ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [hϕ]
    change (QuotientGroup.mk' (_root_.commutator ↥(P : Subgroup G))).ker = ⊥
    rw [QuotientGroup.ker_mk']
    exact hcomm_bot
  -- transfer は `G' = G` 上で自明
  have htriv : MonoidHom.transfer ϕ x = 1 := by
    have hle : _root_.commutator G ≤ (MonoidHom.transfer ϕ).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact MonoidHom.mem_ker.mp (hle (hperfect ▸ Subgroup.mem_top x))
  have hmem := transfer_inv_pow_mul_mem_map P ϕ hab hUP hVP hUV hx
  rw [htriv, mul_one] at hmem
  -- `x ^ |G:P| ∈ U`
  have hpowmem : x ^ (P : Subgroup G).index ∈ U := by
    have hmem' : ϕ ⟨x, hVP hx⟩ ^ (P : Subgroup G).index ∈
        (U.subgroupOf (P : Subgroup G)).map ϕ := by
      simpa using Subgroup.inv_mem _ hmem
    rw [← map_pow] at hmem'
    obtain ⟨u, hu, hueq⟩ := hmem'
    have hueq' : u = (⟨x, hVP hx⟩ : ↥(P : Subgroup G)) ^ (P : Subgroup G).index := hinj hueq
    have hu' : ((u : G)) ∈ U := hu
    rw [hueq'] at hu'
    simpa using hu'
  -- `|G:P|` は奇数
  have hodd : ¬ 2 ∣ (P : Subgroup G).index := P.not_dvd_index
  have hsplit : x ^ (P : Subgroup G).index
      = (x ^ 2) ^ ((P : Subgroup G).index / 2) * x := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  rw [hsplit] at hpowmem
  refine hxU ?_
  have hsqU : (x ^ 2) ^ ((P : Subgroup G).index / 2) ∈ U :=
    U.pow_mem (hsq x hx) _
  have := U.mul_mem (U.inv_mem hsqU) hpowmem
  simpa using this

/-- `H` の特性部分群 (`A : Subgroup ↥H`) を `G` 側に押し出したものは `N_G(H)` の共役で不変。

`Subgroup.normalizerMonoidHom : N(H) →* MulAut H` で共役を `↥H` の自己同型にし,
`A` の特性性 (`characteristic_iff_map_eq`) を適用する。 -/
theorem conj_mem_map_subtype_of_characteristic {H : Subgroup G} {A : Subgroup ↥H}
    [A.Characteristic] {n : G} (hn : n ∈ Subgroup.normalizer (H : Set G))
    {u : G} (hu : u ∈ A.map H.subtype) : n * u * n⁻¹ ∈ A.map H.subtype := by
  obtain ⟨a, ha, rfl⟩ := hu
  have hmap := (Subgroup.characteristic_iff_map_eq (H := A)).mp ‹_›
    (Subgroup.normalizerMonoidHom H ⟨n, hn⟩)
  exact ⟨Subgroup.normalizerMonoidHom H ⟨n, hn⟩ a, hmap ▸ ⟨a, ha, rfl⟩, rfl⟩

/-- `|V : U| = 2` かつ `V` 可換なら, `V` の `U` 外の 2 元は `U` を法として一致する。 -/
theorem inv_mul_mem_of_relIndex_eq_two {U V : Subgroup G}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hidx : U.relIndex V = 2)
    {y z : G} (hy : y ∈ V) (hz : z ∈ V) (hyU : y ∉ U) (hzU : z ∉ U) : y⁻¹ * z ∈ U := by
  obtain ⟨a, -, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp hidx
  have hya : y * a ∈ U := by
    rcases hxor y hy with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hyU
  have hza : z * a ∈ U := by
    rcases hxor z hz with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hzU
  have hyz : y * z⁻¹ ∈ U := by
    have := U.mul_mem hya (U.inv_mem hza)
    simpa [mul_assoc] using this
  have hcomm' : y⁻¹ * z = (y * z⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact hcomm y⁻¹ (V.inv_mem hy) z hz
  rw [hcomm']
  exact U.inv_mem hyz

/-- ⭐ **Isaacs Problem 5C.2**: `P` を `G` の可換な Sylow 2-部分群, `U ≤ V` を `P` の
特性部分群で `|V : U| = 2` とする。`G` が単純なら `|G| = 2`。

**証明**: `G' = G` (非可換単純) と仮定すると `not_mem_of_commutator_eq_top` が矛盾を出す
(transfer 評価 + `N_G(P)` の fusion 制御)。よって `G' = ⊥`, すなわち `G` は可換単純ゆえ
素数位数。`V \ U` の元は `P` の非自明元なので `2 ∣ |G|`, ゆえに `|G| = 2`。

⭐ 書籍の設定にある `U ⊆ V` は**不要** (`Subgroup.relIndex` = `|V : U ⊓ V|` の形で
`|V : U| = 2` を課せば十分)。`U ≤ V` を満たす呼び出し側はそのまま使える。 -/
theorem card_eq_two_of_characteristic_relIndex_eq_two [Finite G] [IsSimpleGroup G]
    (P : Sylow 2 G) (hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    {U V : Subgroup ↥(P : Subgroup G)} [U.Characteristic] [V.Characteristic]
    (hidx : U.relIndex V = 2) :
    Nat.card G = 2 := by
  classical
  set U₀ : Subgroup G := U.map (P : Subgroup G).subtype with hU₀
  set V₀ : Subgroup G := V.map (P : Subgroup G).subtype with hV₀
  have hUP : U₀ ≤ (P : Subgroup G) := Subgroup.map_subtype_le U
  have hVP : V₀ ≤ (P : Subgroup G) := Subgroup.map_subtype_le V
  -- `↥P` 側の relIndex 2 を `G` 側へ移す
  have hmem : ∀ a : ↥(P : Subgroup G), ((a : G) ∈ U₀ ↔ a ∈ U) ∧ ((a : G) ∈ V₀ ↔ a ∈ V) := fun a =>
    ⟨Subgroup.mem_map_iff_mem Subtype.coe_injective,
      Subgroup.mem_map_iff_mem Subtype.coe_injective⟩
  have hidx₀ : U₀.relIndex V₀ = 2 := by
    obtain ⟨a, haV, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp hidx
    refine Subgroup.relIndex_eq_two_iff.mpr ⟨(a : G), (hmem a).2.mpr haV, ?_⟩
    rintro - ⟨b, hb, rfl⟩
    have := hxor b hb
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(hmem (b * a)).1.mpr h1, fun hcon => h2 ((hmem b).1.mp hcon)⟩
    · exact Or.inr ⟨(hmem b).1.mpr h1, fun hcon => h2 ((hmem (b * a)).1.mp hcon)⟩
  have hVcomm : ∀ x ∈ V₀, ∀ y ∈ V₀, x * y = y * x := fun x hx y hy =>
    hab x (hVP hx) y (hVP hy)
  -- `U₀` 外の 2 元は法 `U₀` で一致
  have hUne : ∀ y ∈ V₀, ∀ z ∈ V₀, y ∉ U₀ → z ∉ U₀ → y⁻¹ * z ∈ U₀ :=
    fun y hy z hz hyU hzU => inv_mul_mem_of_relIndex_eq_two hVcomm hidx₀ hy hz hyU hzU
  have hsq : ∀ y ∈ V₀, y ^ 2 ∈ U₀ := by
    intro y hy
    by_cases hyU : y ∈ U₀
    · simpa [sq] using U₀.mul_mem hyU hyU
    · have := hUne y⁻¹ (V₀.inv_mem hy) y hy (fun hcon => hyU (by simpa using U₀.inv_mem hcon)) hyU
      simpa [sq] using this
  -- `N_G(P)` は `V₀/U₀` に自明作用
  have hfus : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), ∀ y ∈ V₀,
      y⁻¹ * (n * y * n⁻¹) ∈ U₀ := by
    intro n hn y hy
    have hn' : n⁻¹ ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := Subgroup.inv_mem _ hn
    refine inv_mul_conj_mem_of_index_two hUne (fun u hu => ?_) (fun u hu => ?_)
      (fun w hw => ?_) hy
    · exact conj_mem_map_subtype_of_characteristic hn hu
    · have h := conj_mem_map_subtype_of_characteristic hn' hu
      rwa [inv_inv] at h
    · exact conj_mem_map_subtype_of_characteristic hn hw
  -- `V₀ \ U₀` の元を取る
  obtain ⟨a, haV, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp hidx₀
  have haU : a ∉ U₀ := by
    have := hxor 1 V₀.one_mem
    rcases this with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd U₀.one_mem h2
    · intro hcon; exact h2 (by simpa using hcon)
  -- `G` は可換 (さもなくば `G' = ⊤` で矛盾)
  have hcomm : ∀ x y : G, x * y = y * x := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator G) inferInstance with
      hbot | htop
    · intro x y
      have hmem2 : ⁅x, y⁆ ∈ _root_.commutator G := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [hbot, Subgroup.mem_bot] at hmem2
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem2
    · exact absurd (not_mem_of_commutator_eq_top P hab htop hUP hVP hfus hsq haV haU)
        (by simp)
  -- 可換単純 ⇒ 素数位数, かつ `a ≠ 1` が 2-元なので `2 ∣ |G|`
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
  have ha1 : a ≠ 1 := fun hcon => haU (hcon ▸ U₀.one_mem)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.2 (⟨a, hVP haV⟩ : ↥(P : Subgroup G))
  have hord : orderOf a = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨a, hVP haV⟩ : ↥(P : Subgroup G))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hord
    exact ha1 hord
  have h2 : (2 : ℕ) ∣ Nat.card G := by
    refine dvd_trans ?_ (orderOf_dvd_natCard a)
    rw [hord]
    exact dvd_pow_self 2 hk0
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h2).symm

/-! ### Problem 5C.5 -/

/-- **Isaacs Problem 5C.5**: `P ∈ Syl_p(G)` の正規部分群 `A`, `B` が `G`-共役なら,
実は `N_G(P)`-共役である。

**証明** (書籍の標準論法): `B = A^g` とすると `A ⊴ P` から `B = A^g ⊴ P^g` なので,
`P` と `P^g` はどちらも `C := N_G(B)` の `p`-部分群。共通の `p`-部分群へ `C` の元 `c` で
共役でき (`GroupTheory.exists_mem_conj_le_common`), `P` は Sylow なのでその共通部分群は
`P` 自身。よって `(cg) P (cg)⁻¹ = P`, すなわち `cg ∈ N_G(P)` で
`A^{cg} = (A^g)^c = B^c = B`。 -/
theorem exists_mem_normalizer_conj_eq_of_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A B : Subgroup G}
    (hAP : ∀ x ∈ A, ∀ y ∈ (P : Subgroup G), y * x * y⁻¹ ∈ A)
    (hBP : ∀ x ∈ B, ∀ y ∈ (P : Subgroup G), y * x * y⁻¹ ∈ B)
    {g : G} (hAB : A.map (MulAut.conj g).toMonoidHom = B) :
    ∃ n : G, (P : Subgroup G).map (MulAut.conj n).toMonoidHom = (P : Subgroup G) ∧
      A.map (MulAut.conj n).toMonoidHom = B := by
  classical
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer B := fun y hy =>
    Subgroup.mem_normalizer_fintype (fun z hz => hBP z hz y hy)
  have hPgN : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer B := by
    rintro - ⟨y, hy, rfl⟩
    refine Subgroup.mem_normalizer_fintype (fun z hz => ?_)
    rw [← hAB] at hz ⊢
    obtain ⟨a, ha, rfl⟩ := hz
    refine ⟨y * a * y⁻¹, hAP a ha y hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hPgp : IsPGroup p ↥((P : Subgroup G).map (MulAut.conj g).toMonoidHom) :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective)
  obtain ⟨c, hcB, T, hTp, hPT, hPgT⟩ :=
    OddOrder.GroupTheory.exists_mem_conj_le_common hPN hPgN P.2 hPgp
  have hTP : T = (P : Subgroup G) := P.3 hTp hPT
  -- `(P^g)^c = P^{cg}`
  have hcomp : ∀ H : Subgroup G, (H.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj c).toMonoidHom = H.map (MulAut.conj (c * g)).toMonoidHom := by
    intro H
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hle : (P : Subgroup G).map (MulAut.conj (c * g)).toMonoidHom ≤ (P : Subgroup G) := by
    rw [← hcomp]
    exact le_trans hPgT (le_of_eq hTP)
  have hcard : Nat.card ((P : Subgroup G).map (MulAut.conj (c * g)).toMonoidHom)
      = Nat.card (P : Subgroup G) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (MulAut.conj (c * g)).injective).toEquiv).symm
  refine ⟨c * g, Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm), ?_⟩
  rw [← hcomp, hAB]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hcB

/-- **Isaacs Problem 5C.5 の系**: `A` が `P` の特性部分群なら, `A` に `G`-共役で `P` に
含まれる正規部分群は `A` 自身のみ。 -/
theorem eq_of_characteristic_of_conj [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A B : Subgroup G}
    (hAP : ∀ x ∈ A, ∀ y ∈ (P : Subgroup G), y * x * y⁻¹ ∈ A)
    (hBP : ∀ x ∈ B, ∀ y ∈ (P : Subgroup G), y * x * y⁻¹ ∈ B)
    (hchar : ∀ n : G, (P : Subgroup G).map (MulAut.conj n).toMonoidHom = (P : Subgroup G) →
      A.map (MulAut.conj n).toMonoidHom = A)
    {g : G} (hAB : A.map (MulAut.conj g).toMonoidHom = B) : A = B := by
  obtain ⟨n, hnP, hnA⟩ := exists_mem_normalizer_conj_eq_of_normal P hAP hBP hAB
  rw [← hnA, hchar n hnP]

end

end OddOrder.Isaacs.Ch05
