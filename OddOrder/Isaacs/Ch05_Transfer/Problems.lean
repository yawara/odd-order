/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer

/-!
# Isaacs Chapter 5 — Problems 5A (transfer の基本)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 5A (書籍 pp. 152-153)。

mathlib の transfer は `MonoidHom.transfer (ϕ : H →* A) : G →* A` (`A` は可換群) で,
Isaacs の `v : G → H/H'` は `A = H/H'`, `ϕ = 自然な射影` の場合にあたる。

* **5A.1** `transfer_id_eq_pow_index_of_commGroup` — `G` 可換, `|G : H| = n` なら
  `G → H` の transfer は `g ↦ g ^ n`。
* **5A.3(a)** `eq_of_mul_eq_mul_of_isComplement` — `ST` の元の `s * t` 表示は一意。
* **5A.3(b)** `isComplement_mul_of_transversal` — `ST` は `G` の中で `H` の右 transversal。
  ⚠ 指数の積 `|G:H| = |G:K|·|K:H|` は mathlib `Subgroup.relIndex_mul_index` が既に
  与えるのでラッパーは書かない。(c)(d) (pretransfer の合成) は未実装 (issue 1055 参照)。
* **5A.4(a)** `transfer_eq_pow_index_of_le_center` — `H ≤ Z(G)`, `|G : H| = n` なら
  transfer は `g ↦ ϕ ⟨g ^ n⟩` (`ϕ : ↥H →* A` は任意)。Isaacs の `v : G → H/H'` は
  `A = H/H'` の場合で, `H ≤ Z(G)` なら `H` は可換ゆえ `H' = 1`, `H/H' ≅ H` なので
  「`v(h) = h ^ n`」がそのまま読める。
  ⚠ 余域を `↥H` に取った版は `CommGroup ↥H` を statement 内 `letI` で供給する必要があり,
  その instance の `toGroup` が `Subgroup.toGroup` と構文的に一致しないため
  `MonoidHom.id ↥H` の型が合わない (diamond)。一般 `ϕ` 版で十分なので採らない。
-/

namespace OddOrder.Isaacs.Ch05

open MonoidHom

open scoped Pointwise

section /- Problems 5A (pp. 152-153) -/

/-- **Isaacs Problem 5A.1**: `G` が可換で `H ≤ G` の指数が `n` なら, `G` から `H` への
transfer は `g ↦ g ^ n`。

可換なので `transfer_eq_pow` の仮説 `g₀⁻¹ g^k g₀ = g^k` は自明に成り立つ。 -/
theorem transfer_id_eq_pow_index_of_commGroup {G : Type*} [CommGroup G] {H : Subgroup G}
    [H.FiniteIndex] (g : G) :
    transfer (MonoidHom.id H) g = ⟨g ^ H.index, transfer_eq_pow_aux g
      (fun k g₀ _ => by rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul])⟩ :=
  transfer_eq_pow (MonoidHom.id H) g
    (fun k g₀ _ => by rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul])

/-- **Isaacs Problem 5A.1** (値の形): `G` 可換なら transfer の値は `g ^ |G : H|`。 -/
theorem coe_transfer_id_of_commGroup {G : Type*} [CommGroup G] {H : Subgroup G}
    [H.FiniteIndex] (g : G) :
    ((transfer (MonoidHom.id H) g : H) : G) = g ^ H.index := by
  rw [transfer_id_eq_pow_index_of_commGroup]

/-- **Isaacs Problem 5A.4(a)** (一般の余域版): `H ≤ Z(G)` で `|G : H| = n` なら, 任意の
`ϕ : ↥H →* A` (`A` 可換) について transfer は `g ↦ ϕ ⟨g ^ n⟩`。

`transfer_eq_pow` の仮説は `g₀⁻¹ g^k g₀ ∈ H ≤ Z(G)` が中心的で `g₀` と可換なことから従う
(mathlib `transfer_center_eq_pow` と同じ議論を `H ≤ Z(G)` に一般化したもの)。 -/
theorem transfer_eq_pow_index_of_le_center {G A : Type*} [Group G] [CommGroup A]
    {H : Subgroup G} [H.FiniteIndex] (hH : H ≤ Subgroup.center G) (ϕ : H →* A) (g : G) :
    transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g
      (fun k g₀ hk => by rw [← mul_right_inj, ← (hH hk).comm, mul_inv_cancel_right])⟩ :=
  transfer_eq_pow ϕ g
    (fun k g₀ hk => by rw [← mul_right_inj, ← (hH hk).comm, mul_inv_cancel_right])

/-- `H ≤ Z(G)` なら `H ⊴ G`. -/
theorem normal_of_le_center {G : Type*} [Group G] {H : Subgroup G}
    (hH : H ≤ Subgroup.center G) : H.Normal :=
  ⟨fun n hn g => by
    have hc : g * n = n * g := Subgroup.mem_center_iff.mp (hH hn) g
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩

/-- **Isaacs Problem 5A.4(b)**: `H ≤ Z(G)`, `|G : H| = n`, `(|H|, n) = 1` なら
`G = H × ker v` (`v` = transfer)。ここでは補群条件 `H ⊓ ker v = 1` と `H ⊔ ker v = ⊤` の形で
述べる (`H ≤ Z(G)` なので直積になる)。

`v(h) = ϕ⟨h^n⟩` (5A.4(a)) と `ϕ` の単射性から `H ⊓ ker v` の元は `h^n = 1` を満たし,
位数が `|H|` と `n` の両方を割るので `1`。全射性は `H` 上で `h ↦ h^n` が単射 ⟹ 有限性から
全射なので, 任意の `g` に `h ∈ H` を `h^n = g^n` と取れば `g h⁻¹ ∈ ker v`。 -/
theorem inf_ker_transfer_eq_bot_of_le_center {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] (hH : H ≤ Subgroup.center G)
    (ϕ : H →* A) (hϕ : Function.Injective ϕ)
    (hcop : Nat.Coprime (Nat.card H) H.index) :
    H ⊓ (transfer ϕ).ker = ⊥ := by
  haveI := normal_of_le_center hH
  rw [eq_bot_iff]
  rintro h ⟨hhH, hker⟩
  rw [Subgroup.mem_bot]
  have hpow : h ^ H.index = 1 := by
    have h1 : ϕ ⟨h ^ H.index, Subgroup.pow_index_mem H h⟩ = 1 := by
      rw [← transfer_eq_pow_index_of_le_center hH ϕ h]
      exact hker
    have h2 : (⟨h ^ H.index, Subgroup.pow_index_mem H h⟩ : H) = 1 := hϕ (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have d1 : orderOf h ∣ H.index := orderOf_dvd_of_pow_eq_one hpow
  have d2 : orderOf h ∣ Nat.card H := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have := pow_card_eq_one' (G := H) (x := (⟨h, hhH⟩ : H))
    exact congrArg Subtype.val this
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd d2 d1))

/-- **Isaacs Problem 5A.4(b)** (生成側): `H ⊔ ker v = ⊤`。⚠ こちら側は `ϕ` の単射性を
使わない (`h ↦ h ^ n` の全射性だけで足りる)。 -/
theorem sup_ker_transfer_eq_top_of_le_center {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] (hH : H ≤ Subgroup.center G)
    (ϕ : H →* A) (hcop : Nat.Coprime (Nat.card H) H.index) :
    H ⊔ (transfer ϕ).ker = ⊤ := by
  haveI := normal_of_le_center hH
  -- `x ↦ x ^ n` は `↥H` 上で単射, したがって全射
  have hfinj : Function.Injective
      (fun x : H => (⟨(x : G) ^ H.index, H.pow_mem x.2 _⟩ : H)) := by
    intro x y hxy
    have hxy' : (x : G) ^ H.index = (y : G) ^ H.index := congrArg Subtype.val hxy
    have hxy0 : Commute (x : G) (y : G) := Subgroup.mem_center_iff.mp (hH y.2) (x : G)
    have hcomm : Commute (x : G) ((y : G)⁻¹) := hxy0.inv_right
    have hz : ((x : G) * (y : G)⁻¹) ^ H.index = 1 := by
      rw [hcomm.mul_pow, inv_pow, hxy', mul_inv_cancel]
    have hzH : (x : G) * (y : G)⁻¹ ∈ H := H.mul_mem x.2 (H.inv_mem y.2)
    have d1 : orderOf ((x : G) * (y : G)⁻¹) ∣ H.index := orderOf_dvd_of_pow_eq_one hz
    have d2 : orderOf ((x : G) * (y : G)⁻¹) ∣ Nat.card H := by
      refine orderOf_dvd_of_pow_eq_one ?_
      have := pow_card_eq_one' (G := H) (x := (⟨_, hzH⟩ : H))
      exact congrArg Subtype.val this
    have h1 : (x : G) * (y : G)⁻¹ = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd d2 d1))
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have hfsurj := Finite.injective_iff_surjective.mp hfinj
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, hh⟩ := hfsurj ⟨g ^ H.index, Subgroup.pow_index_mem H g⟩
  have hhpow : (h : G) ^ H.index = g ^ H.index := congrArg Subtype.val hh
  have hker : g * (h : G)⁻¹ ∈ (transfer ϕ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      transfer_eq_pow_index_of_le_center hH ϕ g,
      transfer_eq_pow_index_of_le_center hH ϕ (h : G), ← map_inv, ← map_mul]
    convert map_one ϕ using 2
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [hhpow, mul_inv_cancel]
  have : g = (g * (h : G)⁻¹) * (h : G) := by group
  rw [this]
  exact Subgroup.mul_mem _ ((le_sup_right : (transfer ϕ).ker ≤ _) hker)
    ((le_sup_left : H ≤ _) h.2)


/-- **Isaacs Problem 5A.2**: `H = ⊤` のときの transfer は `ϕ` そのもの。

Isaacs の `v : G → G/G'` は `A = G/G'`, `ϕ` = 自然な射影の場合なので, これがまさに
「transfer は自然な射影に他ならない」。

`G ⧸ ⊤` は 1 点なので `diff` の積は 1 項だけで, その項は `g` の**共役**の `ϕ`-像
(`Subgroup.smul_apply_eq_smul_apply_inv_smul`)。`A` が可換なので `ϕ ⟨g⟩` に等しい。
⚠ `transfer_eq_pow` は使えない (key 仮説「`g₀⁻¹ g^k g₀ = g^k`」は `H = ⊤` では偽)。 -/
theorem transfer_top_eq_apply {G A : Type*} [Group G] [CommGroup A]
    [(⊤ : Subgroup G).FiniteIndex] (ϕ : (⊤ : Subgroup G) →* A) (g : G) :
    transfer ϕ g = ϕ ⟨g, Subgroup.mem_top g⟩ := by
  classical
  haveI hss : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  letI hfin : Fintype (G ⧸ (⊤ : Subgroup G)) := Subgroup.fintypeQuotientOfFiniteIndex
  have hconj : ∀ x : G,
      ϕ ⟨x⁻¹ * (g * x), Subgroup.mem_top _⟩ = ϕ ⟨g, Subgroup.mem_top g⟩ := by
    intro x
    have hx : (⟨x⁻¹ * (g * x), Subgroup.mem_top _⟩ : (⊤ : Subgroup G))
        = (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup G))⁻¹ *
            ⟨g, Subgroup.mem_top g⟩ * ⟨x, Subgroup.mem_top x⟩ :=
      Subtype.ext (by simp [mul_assoc])
    rw [hx, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have hbeta : ∀ q : G ⧸ (⊤ : Subgroup G),
      (((g • (default : (⊤ : Subgroup G).LeftTransversal)).2.leftQuotientEquiv q : G))
        = g * ((default : (⊤ : Subgroup G).LeftTransversal).2.leftQuotientEquiv q : G) := by
    intro q
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul g default q,
      Subsingleton.elim (g⁻¹ • q) q]
    rfl
  rw [transfer_def ϕ (default : (⊤ : Subgroup G).LeftTransversal) g]
  simp only [Subgroup.leftTransversals.diff, hbeta, hconj]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    show Nat.card (G ⧸ (⊤ : Subgroup G)) = 1 from Subgroup.index_top, pow_one]


/-- **Isaacs Problem 5A.3(a)**: `S ⊆ K` で `T` が `K` の右 transversal なら, 積 `ST` の元は
`s * t` (`s ∈ S`, `t ∈ T`) の形に**一意に**書ける。

`IsComplement (K : Set G) T` の単射性を `(s, t)` と `(s', t')` に適用するだけ
(`s, s' ∈ K` が効く)。 -/
theorem eq_of_mul_eq_mul_of_isComplement {G : Type*} [Group G] {K : Subgroup G} {S T : Set G}
    (hS : S ⊆ K) (hT : Subgroup.IsComplement (K : Set G) T)
    {s s' : S} {t t' : T} (h : (s : G) * (t : G) = (s' : G) * (t' : G)) :
    (s : G) = (s' : G) ∧ (t : G) = (t' : G) := by
  have hpair := hT.1 (a₁ := (⟨(s : G), hS s.2⟩, t)) (a₂ := (⟨(s' : G), hS s'.2⟩, t')) h
  exact ⟨congrArg (fun p => ((p.1 : G))) hpair, congrArg (fun p => ((p.2 : G))) hpair⟩


/-- **Isaacs Problem 5A.3(b)**: `S ⊆ K` が `K` の中で `H` の右 transversal, `T` が `G` の中で
`K` の右 transversal なら, **積 `ST` は `G` の中で `H` の右 transversal**。

単射性: `h·s·t = h'·s'·t'` で `h·s, h'·s' ∈ K` なので `hT` の単射性から `h·s = h'·s'`,
`t = t'`。`hS` の一意性を `k := h·s` に使って `s = s'`, したがって `h = h'`。
全射性: `g = k·t` (`hT`) と `k = h·s` (`hS`) を合わせる。

⚠ 指数の積 `|G:H| = |G:K|·|K:H|` は mathlib `Subgroup.relIndex_mul_index` が既に与える。 -/
theorem isComplement_mul_of_transversal {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) {S T : Set G} (hSsub : S ⊆ (K : Set G))
    (hS : ∀ k ∈ K, ∃! s : ↥S, k * (s : G)⁻¹ ∈ H)
    (hT : Subgroup.IsComplement (K : Set G) T) :
    Subgroup.IsComplement (H : Set G) (S * T) := by
  constructor
  · rintro ⟨h, x⟩ ⟨h', x'⟩ heq
    obtain ⟨s, hs, t, ht, hst⟩ := x.2
    obtain ⟨s', hs', t', ht', hst'⟩ := x'.2
    simp only at heq
    rw [← hst, ← hst'] at heq
    have hk : ((h : G) * s) ∈ K := K.mul_mem (hHK h.2) (hSsub hs)
    have hk' : ((h' : G) * s') ∈ K := K.mul_mem (hHK h'.2) (hSsub hs')
    have hpair := hT.1 (a₁ := (⟨(h : G) * s, hk⟩, ⟨t, ht⟩))
      (a₂ := (⟨(h' : G) * s', hk'⟩, ⟨t', ht'⟩)) (by simpa [mul_assoc] using heq)
    have hks : (h : G) * s = (h' : G) * s' := congrArg (fun p => (p.1 : G)) hpair
    have htt : t = t' := congrArg (fun p => (p.2 : G)) hpair
    obtain ⟨s₀, -, huniq⟩ := hS ((h : G) * s) hk
    have e1 : (⟨s, hs⟩ : ↥S) = s₀ := huniq _ (by simp)
    have e2 : (⟨s', hs'⟩ : ↥S) = s₀ := huniq _ (by
      rw [hks]
      simp)
    have hss : s = s' := congrArg (fun z : ↥S => (z : G)) (e1.trans e2.symm)
    have hhh : (h : G) = (h' : G) := by
      have := hks
      rw [hss] at this
      exact mul_right_cancel this
    refine Prod.ext (Subtype.ext hhh) (Subtype.ext ?_)
    rw [← hst, ← hst', hss, htt]
  · intro g
    obtain ⟨⟨k, t⟩, hkt⟩ := hT.2 g
    obtain ⟨s, hsH, -⟩ := hS (k : G) k.2
    refine ⟨(⟨(k : G) * (s : G)⁻¹, hsH⟩, ⟨(s : G) * (t : G), ⟨(s : G), s.2, (t : G), t.2, rfl⟩⟩),
      ?_⟩
    simp only
    rw [← hkt]
    group


end


open scoped Pointwise in
/-- **Isaacs Problem 5A.3(b), 左 transversal 版**: `H ≤ K ≤ G` で `T` が `G` の中の `K` の
左 transversal, `S ⊆ K` が `K` の中の `H` の左 transversal なら `T * S` は `G` の中の
`H` の左 transversal。

書籍は右 transversal で述べるが (上の `isComplement_mul_of_transversal`), mathlib の
`MonoidHom.transfer` は**左** transversal (`Subgroup.LeftTransversal`) で定義されているので,
5A.3(c)(d) (transfer の推移律) にはこちらの向きが要る。

**証明**: `g = t·k` (`hT` の一意分解), `k = s·h` (`hS` の一意分解) から `g = (t·s)·h`。
一意性は逆向きに 2 段の一意性を使う。 -/
theorem isComplement_mul_of_transversal_left {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) {S T : Set G} (hSsub : S ⊆ (K : Set G))
    (hS : ∀ k ∈ K, ∃! s : ↥S, (s : G)⁻¹ * k ∈ H)
    (hT : Subgroup.IsComplement T (K : Set G)) :
    Subgroup.IsComplement (T * S) (H : Set G) := by
  rw [Subgroup.isComplement_iff_existsUnique]
  intro g
  obtain ⟨⟨t, k⟩, htk, huniq⟩ := Subgroup.isComplement_iff_existsUnique.mp hT g
  obtain ⟨s, hs, hsuniq⟩ := hS (k : G) k.2
  refine ⟨(⟨(t : G) * (s : G), Set.mul_mem_mul t.2 s.2⟩, ⟨(s : G)⁻¹ * (k : G), hs⟩), ?_, ?_⟩
  · change (t : G) * (s : G) * ((s : G)⁻¹ * (k : G)) = g
    calc (t : G) * (s : G) * ((s : G)⁻¹ * (k : G)) = (t : G) * (k : G) := by group
      _ = g := htk
  · rintro ⟨⟨x, hx⟩, ⟨h, hh⟩⟩ hxh
    have hxh' : x * h = g := hxh
    obtain ⟨t', ht', s', hs', hts'⟩ := Set.mem_mul.mp hx
    have hsK : s' ∈ K := hSsub hs'
    have hhK : h ∈ K := hHK hh
    have hpair := huniq (⟨t', ht'⟩, ⟨s' * h, K.mul_mem hsK hhK⟩) (by
      change t' * (s' * h) = g
      rw [← mul_assoc, hts']
      exact hxh')
    have ht'eq : t' = (t : G) := congrArg (fun p => ((p.1 : ↥T) : G)) hpair
    have hkeq : s' * h = (k : G) := congrArg (fun p => ((p.2 : ↥(K : Set G)) : G)) hpair
    have hs'mem : ((⟨s', hs'⟩ : ↥S) : G)⁻¹ * (k : G) ∈ H := by
      rw [← hkeq]
      simpa using hh
    have hs'eq : (⟨s', hs'⟩ : ↥S) = s := hsuniq _ hs'mem
    have hs'val : s' = (s : G) := congrArg Subtype.val hs'eq
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · calc x = t' * s' := hts'.symm
        _ = (t : G) * (s : G) := by rw [ht'eq, hs'val]
    · change h = (s : G)⁻¹ * (k : G)
      calc h = s'⁻¹ * (s' * h) := by group
        _ = (s : G)⁻¹ * (k : G) := by rw [hkeq, hs'val]


end OddOrder.Isaacs.Ch05
