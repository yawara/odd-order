/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini
import OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement
import OddOrder.Isaacs.Ch05_Transfer.Problems5C12

/-!
# Isaacs Problem 5C.13 (Navarro) — 自己正規化 Sylow と `N_G(P')` (p. 164)

**主張**: `P` が `G` の Sylow `p`-部分群で `P = N_G(P)` なら, `N_G(P')` は正規 `p`-補群をもつ
(`P' = ⁅P, P⁆`)。

**証明** (書籍 hint に沿う): `H := N_G(P')` に取り替えると `P ≤ H`, `P` は `H` の Sylow で
`N_H(P) = P`, かつ `P' ⊴ H`。よって次の**還元形**を示せばよい:

> `P ∈ Syl_p(G)`, `N_G(P) = P`, `⁅P,P⁆ ⊴ G` ⟹ `G` は正規 `p`-補群をもつ。

`L := ⁅P,P⁆` とおく。

1. `G/L` の Sylow `p`-部分群 `P̄ = PL/L = P/L` は**可換** (`L` は `P` の交換子群) で
   **自己正規化** (`π⁻¹(P̄) = P` と `N_G(P) = P`)。⟹ **Burnside** (Thm 5.13) で `G/L` は
   正規 `p`-補群 `K̄` をもつ。`K := π⁻¹(K̄)` は `L ≤ K ⊴ G`, `|K:L| = |K̄|` は `p` と素,
   `|G:K| = |P̄|` は `p`-冪。
2. `L` は `K` の正規 Hall `p`-部分群なので **Schur–Zassenhaus** で補群 `X` (`K = L ⋊ X`) を得る。
   `X` は `p'`-群。
3. **Frattini 論法** (補群の共役性、共役元は `L` の中に取れる = Ch.3 の
   `exists_conj_le_of_isComplement'_of_coprime'`) で **`G = L · N_G(X)`**。
4. **Dedekind**: `P ≤ G = L·N_G(X)` と `L ≤ P` から `P = L·(P ⊓ N_G(X))`。`L = ⁅P,P⁆ ⊆ Φ(P)`
   (Problem 1D.8) なので Frattini 部分群の非生成性より `P ⊆ N_G(X)`。
5. `L ≤ P ≤ N_G(X)` なので 3 と合わせて `N_G(X) = G`, すなわち `X ⊴ G`。`|X|` は `p` と素で
   `|G:X| = |L|·|G:K|` は `p`-冪 ⟹ `X` が正規 `p`-補群。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5C.13: 自己正規化 Sylow と `N_G(P')` (p. 164) -/

/-- 正規部分群 `X` の位数が `p` と素で指数が `p`-冪なら, それは正規 `p`-補群である。 -/
theorem hasNormalPComplement_of_normal_of_index_eq_pow [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} [X.Normal] (hpX : ¬ p ∣ Nat.card ↥X) {a : ℕ} (hidx : X.index = p ^ a) :
    HasNormalPComplement p G := by
  classical
  have hp : p.Prime := Fact.out
  have hcardG : Nat.card ↥X * X.index = Nat.card G := Subgroup.card_mul_index X
  have hfact : (Nat.card G).factorization p = a := by
    rw [← hcardG, hidx, Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero a hp.pos.ne')]
    simp [Nat.factorization_eq_zero_of_not_dvd hpX, Nat.Prime.factorization_self hp]
  refine ⟨X, inferInstance, fun Q => ?_⟩
  have hQcard : Nat.card ↥(Q : Subgroup G) = p ^ a := by rw [Q.card_eq_multiplicity, hfact]
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [hQcard, ← hidx, hcardG]
  · rw [disjoint_iff]
    refine Subgroup.card_eq_one.mp ?_
    by_contra hne
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : Nat.card ↥(X ⊓ (Q : Subgroup G)) ∣ Nat.card ↥X :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(X ⊓ (Q : Subgroup G)) ∣ p ^ a :=
      hQcard ▸ Subgroup.card_dvd_of_le (inf_le_right : _ ≤ (Q : Subgroup G))
    have hrp : r = p :=
      (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow (hrdvd.trans h2))
    exact hpX (hrp ▸ hrdvd.trans h1)

/-- **5C.13 / 5D.5 共通のエンジン**: `P ∈ Syl_p(G)`, `L := ⁅P,P⁆` とし, `K ⊴ G` が `L` を含み
`L` が `K` の**正規 Hall `p`-部分群** (`p ∤ |K : L|`) で `|G : K|` が `p`-冪なら,
`G` は正規 `p`-補群をもつ。

**証明**: Schur–Zassenhaus で `K` 内の `L` の補群 `X` を取り, **Frattini 論法** (補群の共役性、
共役元は `L` の中に取れる = Ch.3 の `exists_conj_le_of_isComplement'_of_coprime'`) で
`G = L · N_G(X)`。**Dedekind** 分解と `L = ⁅P,P⁆ ⊆ Φ(P)` (Problem 1D.8) の非生成性から
`P ≤ N_G(X)`, よって `N_G(X) = ⊤` すなわち `X ⊴ G`。`|X| = |K : L|` は `p` と素で
`|G : X| = |L| · |G : K|` は `p`-冪。 -/
theorem hasNormalPComplement_of_commutator_normalHall_in_normal
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) {K : Subgroup G} [K.Normal]
    (hLK : (⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G) ≤ K)
    (hMnorm : ((⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G).subgroupOf K).Normal)
    (hpM : ¬ p ∣ ((⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G).subgroupOf K).index)
    {a : ℕ} (hKidx : K.index = p ^ a) :
    HasNormalPComplement p G := by
  classical
  set L : Subgroup G := ⁅(P : Subgroup G), (P : Subgroup G)⁆ with hLdef
  have hLP : L ≤ (P : Subgroup G) := by
    rw [hLdef, ← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  have hLp : IsPGroup p ↥L := by
    intro g
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨(g : G), hLP g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hLp
  set M : Subgroup ↥K := L.subgroupOf K with hMdef
  have := hMnorm
  have hMcard : Nat.card ↥M = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥M) M.index := by
    rw [hMcard, hn]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM)
  obtain ⟨X', hX'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set X : Subgroup G := X'.map K.subtype with hXdef
  have hXK : X ≤ K := Subgroup.map_subtype_le _
  have hXcard : Nat.card ↥X = M.index := by
    rw [hXdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective K),
      ← hX'.symm.index_eq_card]
  have hpX : ¬ p ∣ Nat.card ↥X := fun h => hpM (hXcard ▸ h)
  have hXsub : X.subgroupOf K = X' := by
    rw [hXdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective K)]
  have hXidx : X.index = Nat.card ↥L * K.index := by
    have e : X.relIndex K * K.index = X.index := Subgroup.relIndex_mul_index hXK
    have e2 : X.relIndex K = Nat.card ↥L := by
      rw [Subgroup.relIndex, hXsub, hX'.index_eq_card, hMcard]
    rw [← e, e2]
  -- Frattini 論法: `G = L · N_G(X)`
  have hLnil : Group.IsNilpotent ↥L := hLp.isNilpotent
  have hMsolv : Group.IsSolvable ↥M :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLK).symm.surjective
  have hsmulcard : ∀ Y : Subgroup G, ∀ c : G,
      Nat.card ↥(MulAut.conj c • Y) = Nat.card ↥Y := fun Y c =>
    Nat.card_congr (Subgroup.equivSMul (MulAut.conj c) Y).toEquiv.symm
  have hfrat : ∀ g : G, ∃ y ∈ L, MulAut.conj g • X = MulAut.conj y • X := by
    intro g
    have hKfix : MulAut.conj g • K = K := by
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top g
    have hgK : MulAut.conj g • X ≤ K :=
      hKfix ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hXK
    have hUcard : Nat.card ↥((MulAut.conj g • X).subgroupOf K) = Nat.card ↥X := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hgK).toEquiv]
      exact hsmulcard X g
    have hcop2 : Nat.Coprime (Nat.card ↥((MulAut.conj g • X).subgroupOf K)) (Nat.card ↥M) := by
      rw [hUcard, hXcard, hMcard, hn]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM).symm
    obtain ⟨x, hxM, hxle⟩ :=
      Ch03.exists_conj_le_of_isComplement'_of_coprime' (Or.inl hMsolv) hX' hcop2
    refine ⟨(x : G), hxM, ?_⟩
    have hmapU : ((MulAut.conj g • X).subgroupOf K).map K.subtype = MulAut.conj g • X := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hgK]
    have hcoe : Subgroup.map (MulAut.conj x).toMonoidHom X' = MulAut.conj x • X' := rfl
    have hmapX' : (Subgroup.map (MulAut.conj x).toMonoidHom X').map K.subtype
        = MulAut.conj (x : G) • X := by
      rw [hcoe, Ch01.map_conj_smul, hXdef]
      rfl
    have hstep := Subgroup.map_mono (f := K.subtype) hxle
    rw [hmapU, hmapX'] at hstep
    refine Subgroup.eq_of_le_of_card_ge hstep ?_
    rw [hsmulcard X (x : G), hsmulcard X g]
  have hdecomp : ∀ g : G, ∃ y ∈ L, ∃ w ∈ Subgroup.normalizer (X : Set G), g = y * w := by
    intro g
    obtain ⟨y, hyL, hy⟩ := hfrat g
    refine ⟨y, hyL, y⁻¹ * g, ?_, by group⟩
    have key : MulAut.conj (y⁻¹ * g) • X = X := by
      rw [map_mul, map_inv, mul_smul, hy, ← mul_smul, inv_mul_cancel, one_smul]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key
  -- Dedekind + Frattini 部分群の非生成性: `P ≤ N_G(X)`
  have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hLsub : L.subgroupOf (P : Subgroup G) = _root_.commutator ↥(P : Subgroup G) := by
    rw [hLdef, ← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  have hPtop : (Subgroup.normalizer (X : Set G)).subgroupOf (P : Subgroup G)
      ⊔ frattini ↥(P : Subgroup G) = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨y, hyL, w, hw, hz⟩ := hdecomp (z : G)
    have hyP : y ∈ (P : Subgroup G) := hLP hyL
    have hwP : w ∈ (P : Subgroup G) := by
      have hw' : w = y⁻¹ * (z : G) := by rw [hz]; group
      rw [hw']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyP) z.2
    have hzsplit : z = (⟨y, hyP⟩ : ↥(P : Subgroup G)) * ⟨w, hwP⟩ :=
      Subtype.ext (by simpa using hz)
    rw [hzsplit]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hw)
    refine Ch01.commutator_le_frattini ?_
    rw [← hLsub]
    exact hyL
  have hPX : (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [← Subgroup.subgroupOf_eq_top]
    exact frattini_nongenerating hPtop
  have hXtop : Subgroup.normalizer (X : Set G) = ⊤ := by
    refine top_le_iff.mp fun g _ => ?_
    obtain ⟨y, hyL, w, hw, hz⟩ := hdecomp g
    rw [hz]
    exact Subgroup.mul_mem _ (hPX (hLP hyL)) hw
  have : X.Normal := Subgroup.normalizer_eq_top_iff.mp hXtop
  refine hasNormalPComplement_of_normal_of_index_eq_pow (a := n + a) hpX ?_
  rw [hXidx, hn, hKidx, pow_add]

/-- **5C.13 の還元形**: `P ∈ Syl_p(G)` が自己正規化で `⁅P,P⁆ ⊴ G` なら `G` は正規 `p`-補群をもつ。

書籍 hint の "Without loss of generality, `P' ⊴ G`" に対応する本体。 -/
theorem hasNormalPComplement_of_selfNormalizing_sylow_of_commutator_normal
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hself : Subgroup.normalizer ((P : Subgroup G) : Set G) = (P : Subgroup G))
    (hLnorm : (⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G).Normal) :
    HasNormalPComplement p G := by
  classical
  set L : Subgroup G := ⁅(P : Subgroup G), (P : Subgroup G)⁆ with hLdef
  have := hLnorm
  have hLP : L ≤ (P : Subgroup G) := by
    rw [hLdef, ← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  have hLp : IsPGroup p ↥L := by
    intro g
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨(g : G), hLP g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  set π : G →* G ⧸ L := QuotientGroup.mk' L with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective L
  -- (1) `P̄ := P L / L` は `G/L` の Sylow で可換かつ自己正規化
  obtain ⟨Pbar, hPbar⟩ := Ch01.exists_sylow_coe_eq_of_isHallSubgroup_singleton
    (Ch01.IsHallSubgroup.map_of_surjective hπsurj (Ch01.sylow_isHallSubgroup_singleton P))
  have hPbarComm : ∀ x y : ↥(Pbar : Subgroup (G ⧸ L)), x * y = y * x := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [hPbar] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    refine Subtype.ext ?_
    have hmem : a * b * (b * a)⁻¹ ∈ L := by
      have hcomm : a * b * (b * a)⁻¹ = ⁅a, b⁆ := by group
      rw [hcomm, hLdef]
      exact Subgroup.commutator_mem_commutator ha hb
    have hone : π (a * b * (b * a)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one] at hone
    exact hone
  have hcomapPbar : Subgroup.comap π (Pbar : Subgroup (G ⧸ L)) = (P : Subgroup G) := by
    rw [hPbar, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hLP]
  have hPbarSelf :
      Subgroup.normalizer ((Pbar : Subgroup (G ⧸ L)) : Set (G ⧸ L))
        = (Pbar : Subgroup (G ⧸ L)) := by
    refine le_antisymm (fun gbar hgbar => ?_) Subgroup.le_normalizer
    obtain ⟨g, rfl⟩ := hπsurj gbar
    have hle : MulAut.conj g • (P : Subgroup G) ≤ (P : Subgroup G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π x ∈ (Pbar : Subgroup (G ⧸ L)) := by
        rw [← Subgroup.mem_comap, hcomapPbar]; exact hx
      have hconj : π (MulAut.conj g x) ∈ (Pbar : Subgroup (G ⧸ L)) := by
        have hstep := (Subgroup.mem_normalizer_iff.mp hgbar (π x)).mp hx'
        simpa [MulAut.conj, map_mul, map_inv] using hstep
      rw [← hcomapPbar, Subgroup.mem_comap]
      exact hconj
    have hcard : Nat.card ↥(MulAut.conj g • (P : Subgroup G)) = Nat.card ↥(P : Subgroup G) :=
      Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) (P : Subgroup G)).toEquiv.symm
    have heq : MulAut.conj g • (P : Subgroup G) = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hle hcard.ge
    have hgP : g ∈ (P : Subgroup G) := hself ▸ Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    rw [hPbar]
    exact ⟨g, hgP, rfl⟩
  -- Burnside: `G/L` は正規 `p`-補群 `K̄` をもつ
  have hburn : HasNormalPComplement p (G ⧸ L) := by
    refine hasNormalPComplement_of_sylow_normalizer_le_centralizer Pbar (fun x hx => ?_)
    have hx' : x ∈ (Pbar : Subgroup (G ⧸ L)) := hPbarSelf.le hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hPbarComm ⟨y, hy⟩ ⟨x, hx'⟩)
  obtain ⟨Kbar, hKbarN, hKbarC⟩ := hburn
  have := hKbarN
  have hpKbar : ¬ p ∣ Nat.card ↥Kbar :=
    not_dvd_card_of_isComplement'_sylow Pbar (hKbarC Pbar)
  have hKbaridx : Kbar.index = Nat.card ↥(Pbar : Subgroup (G ⧸ L)) :=
    (hKbarC Pbar).symm.index_eq_card
  -- (2) `K := π⁻¹(K̄)`
  set K : Subgroup G := Subgroup.comap π Kbar with hKdef
  have : K.Normal := hKbarN.comap π
  have hLK : L ≤ K := by
    rw [hKdef, hπ]
    exact QuotientGroup.le_comap_mk' L Kbar
  have hKidx : K.index = Kbar.index :=
    Subgroup.index_comap_of_surjective (H := Kbar) (f := π) hπsurj
  have hKcard : Nat.card ↥K = Nat.card ↥Kbar * Nat.card ↥L := by
    have e1 : Nat.card ↥K * K.index = Nat.card G := Subgroup.card_mul_index K
    have e2 : Nat.card ↥Kbar * Kbar.index = Nat.card (G ⧸ L) := Subgroup.card_mul_index Kbar
    have e3 : Nat.card ↥L * L.index = Nat.card G := Subgroup.card_mul_index L
    have e4 : L.index = Nat.card (G ⧸ L) := Subgroup.index_eq_card L
    have hpos : 0 < Kbar.index := Nat.pos_of_ne_zero (by
      intro h; rw [h, mul_zero] at e2; exact Nat.card_pos.ne' e2.symm)
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc Nat.card ↥K * Kbar.index = Nat.card G := by rw [← hKidx]; exact e1
      _ = Nat.card ↥L * Nat.card (G ⧸ L) := by rw [← e4]; exact e3.symm
      _ = Nat.card ↥L * (Nat.card ↥Kbar * Kbar.index) := by rw [e2]
      _ = Nat.card ↥Kbar * Nat.card ↥L * Kbar.index := by ring
  have hMcard : Nat.card ↥(L.subgroupOf K) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv
  have hMidx : (L.subgroupOf K).index = Nat.card ↥Kbar := by
    have e : Nat.card ↥(L.subgroupOf K) * (L.subgroupOf K).index = Nat.card ↥K :=
      Subgroup.card_mul_index _
    rw [hMcard] at e
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥L)) ?_
    rw [e, hKcard, Nat.mul_comm]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp Pbar.isPGroup'
  refine hasNormalPComplement_of_commutator_normalHall_in_normal P (K := K) hLK
    (Subgroup.Normal.subgroupOf inferInstance K) (fun h => hpKbar (hMidx ▸ h)) (a := m) ?_
  rw [hKidx, hKbaridx, hm]

set_option backward.isDefEq.respectTransparency false in
/-- **Isaacs Problem 5C.13 (Navarro)** (p. 164) ⭐: `P` が `G` の Sylow `p`-部分群で
`P = N_G(P)` なら, `N_G(P')` (`P' = ⁅P,P⁆`) は正規 `p`-補群をもつ。 -/
theorem hasNormalPComplement_normalizer_commutator_of_selfNormalizing_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hself : Subgroup.normalizer ((P : Subgroup G) : Set G) = (P : Subgroup G)) :
    HasNormalPComplement p
      ↥(Subgroup.normalizer
        ((⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G) : Set G)) := by
  classical
  set L : Subgroup G := ⁅(P : Subgroup G), (P : Subgroup G)⁆ with hLdef
  set H : Subgroup G := Subgroup.normalizer (L : Set G) with hHdef
  have hLP : L ≤ (P : Subgroup G) := by
    rw [hLdef, ← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  -- `P ≤ H` (`P` は自分の交換子群を正規化する)
  have hPH : (P : Subgroup G) ≤ H := by
    intro x hx
    have hPfix : MulAut.conj x • (P : Subgroup G) = (P : Subgroup G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hself.ge hx)
    have key : MulAut.conj x • L = L := by
      rw [hLdef, Subgroup.pointwise_smul_def, Subgroup.map_commutator,
        ← Subgroup.pointwise_smul_def, hPfix]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key
  have hLH : L ≤ H := hLP.trans hPH
  -- `N_{↥H}(P.subtype) = P.subtype`
  have hselfH : Subgroup.normalizer (((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) : Set ↥H)
      = ((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) := by
    rw [Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hPH, hself]
  -- `⁅PH, PH⁆ = L.subgroupOf H` は `↥H` で正規
  have hcommH : (⁅((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H),
      ((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H)⁆ : Subgroup ↥H) = L.subgroupOf H := by
    refine Subgroup.map_injective (Subgroup.subtype_injective H) ?_
    rw [Subgroup.map_commutator, Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH, inf_eq_left.mpr hLH, hLdef]
  have hnormH : (⁅((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H),
      ((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H)⁆ : Subgroup ↥H).Normal := by
    rw [hcommH]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (le_of_eq hHdef)
  exact hasNormalPComplement_of_selfNormalizing_sylow_of_commutator_normal
    (P.subtype hPH) hselfH hnormH

end

end OddOrder.Isaacs.Ch05
