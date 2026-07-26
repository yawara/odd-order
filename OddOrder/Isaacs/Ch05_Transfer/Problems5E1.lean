/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5E

/-!
# Isaacs Problem 5E.1 (Itô) — 極小非 `p`-冪零群 (書籍 p. 175)

**主張**: 有限群 `G` の真部分群がすべて正規 `p`-補群をもつが `G` 自身は持たないとする。
このとき `G` は**正規 Sylow `p`-部分群**をもち, `|G|` の `p` 以外の素因数は**ちょうど 1 個**。

**証明** (⭐ 位数に関する帰納法は不要 — 補題 1 を `G` と `G/O_p(G)` の 2 つに使うだけ):

* **補題 1**: Frobenius Thm 5.26 の対偶より `N_G(X)` が正規 `p`-補群を持たない非自明
  `p`-部分群 `X` が存在し, 仮定から `N_G(X) = ⊤` すなわち `X ◁ G` ⟹ `O_p(G) ≠ 1`。
* **補題 2** ⭐: `M ◁ G` で `|G:M| = p` は起こらない。`M` は真部分群ゆえ `p`-冪零で,
  その正規 `p`-補群 `C` は一意性から `M` に characteristic ⟹ `C ◁ G`。
  `p ∤ |C|` かつ `|G:C| = p·|M:C|` が `p`-冪なので `C` が `G` の正規 `p`-補群になり矛盾。
* **補題 3**: `G/O_p(G)` は `p`-冪零。そうでなければ補題 1 が `G/O_p(G)` にも使えて
  `O_p(G)` の最大性に矛盾。
* **(a)**: 補題 3 の正規 `p`-補群の引き戻し `K` は `|G:K|` が `p`-冪。`K ≠ ⊤` なら `G/K` は
  非自明 `p`-群ゆえ指数 `p` の正規部分群をもち補題 2 に矛盾 ⟹ `K = ⊤` ⟹ `G/O_p(G)` は
  `p'`-群 ⟹ `O_p(G)` が正規 Sylow `p`-部分群。
* **(b)**: Schur–Zassenhaus の Hall `p'`-補群 `H` の各 Sylow `S` について `P·S` は真部分群
  ゆえ `p`-冪零で `[P,S] = 1`。`H` は Sylow たちで生成される (`iSup_sylow_eq_top`) ので
  `H ≤ C_G(P)` ⟹ `H` が正規 `p`-補群になり矛盾 ⟹ `|H|` は素数冪。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise

variable {G : Type*} [Group G]

section /- 5E.1: 極小非 `p`-冪零群 (Itô) (p. 175) -/

/-- `N ◁ G` が `p`-群のとき, 商 `G ⧸ N` の `p`-部分群の引き戻しは `p`-群。 -/
theorem isPGroup_comap_mk'_of_isPGroup {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p ↥N) {W : Subgroup (G ⧸ N)} (hW : IsPGroup p ↥W) :
    IsPGroup p ↥(W.comap (QuotientGroup.mk' N)) := by
  intro x
  obtain ⟨k, hk⟩ := hW ⟨QuotientGroup.mk' N (x : G), Subgroup.mem_comap.mp x.2⟩
  have hk' : ((QuotientGroup.mk' N) (x : G)) ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hmem : ((x : G) ^ p ^ k) ∈ N := by
    have h1 : (QuotientGroup.mk' N) ((x : G) ^ p ^ k) = 1 := by rw [map_pow]; exact hk'
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨j, hj⟩ := hN ⟨(x : G) ^ p ^ k, hmem⟩
  have hj' : (((x : G) ^ p ^ k)) ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  refine ⟨k + j, Subtype.ext ?_⟩
  push_cast
  rw [pow_add, pow_mul]
  exact hj'

/-- 正規部分群 `N` と交わらない部分群は, 商 `G ⧸ N` への像で位数を保つ。 -/
theorem card_map_mk'_of_inf_eq_bot {N C : Subgroup G} [N.Normal] (h : C ⊓ N = ⊥) :
    Nat.card ↥(C.map (QuotientGroup.mk' N)) = Nat.card ↥C := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : ((x : G)) ∈ (QuotientGroup.mk' N).ker := hx
    rw [QuotientGroup.ker_mk'] at hx'
    have hxinf : (x : G) ∈ C ⊓ N := ⟨x.2, hx'⟩
    rw [h, Subgroup.mem_bot] at hxinf
    exact Subtype.ext hxinf
  have hrange : ((QuotientGroup.mk' N).comp C.subtype).range = C.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hrange] at hcard
  exact hcard.symm

/-- 指数が `p`-冪の正規部分群は, 位数が `p` と素な部分群をすべて含む。

(正規 `p`-補群が `p'`-部分群をすべて含むことの一般形.) -/
theorem le_of_index_eq_pow_of_not_dvd_card [Finite G] {p : ℕ} [Fact p.Prime] {C U : Subgroup G}
    [C.Normal] {k : ℕ} (hidx : C.index = p ^ k) (hU : ¬ p ∣ Nat.card ↥U) : U ≤ C := by
  intro u hu
  have hordu : orderOf u = orderOf (⟨u, hu⟩ : ↥U) :=
    orderOf_injective U.subtype (Subgroup.subtype_injective U) ⟨u, hu⟩
  have h1 : orderOf ((QuotientGroup.mk' C) u) ∣ Nat.card ↥U :=
    (orderOf_map_dvd _ _).trans (hordu ▸ orderOf_dvd_natCard (⟨u, hu⟩ : ↥U))
  have h2 : orderOf ((QuotientGroup.mk' C) u) ∣ p ^ k := by
    rw [← hidx, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (Nat.card ↥U) (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hU).symm
  refine (QuotientGroup.eq_one_iff _).mp ?_
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

/-- 正規部分群の指数が `p^a` (`a ≥ 1`) なら, 指数がちょうど `p` の正規部分群が存在する。

`G ⧸ K` は非自明な `p`-群ゆえ極大部分群をもち, 冪零性からそれは正規で指数は素数 (Problem 1D.6),
その素数は `p` しかありえない。 -/
theorem exists_normal_index_eq_prime_of_index_eq_pow [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Subgroup G} [K.Normal] {a : ℕ} (ha : 0 < a) (hidx : K.index = p ^ a) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = p := by
  classical
  have hcard : Nat.card (G ⧸ K) = p ^ a := by rw [← Subgroup.index_eq_card]; exact hidx
  haveI hpq : IsPGroup p (G ⧸ K) := IsPGroup.of_card hcard
  haveI : Group.IsNilpotent (G ⧸ K) := hpq.isNilpotent
  have hne : (⊥ : Subgroup (G ⧸ K)) ≠ ⊤ := by
    intro h
    have h1 : Nat.card (G ⧸ K) = 1 := by
      rw [← Subgroup.card_top (G := G ⧸ K), ← h, Subgroup.card_bot]
    have h2 : 1 < p ^ a := Nat.one_lt_pow ha.ne' (Fact.out : p.Prime).one_lt
    rw [hcard] at h1
    omega
  obtain ⟨Mbar, hMco, _⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ K))).resolve_left hne
  haveI : Mbar.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom Mbar
      (Group.normalizerCondition_of_isNilpotent (G := G ⧸ K)) hMco
  have hMprime : Mbar.index.Prime := (Ch01.isCoatom_iff_index_prime Mbar).mp hMco
  have hMdvd : Mbar.index ∣ p ^ a := hcard ▸ Subgroup.index_dvd_card Mbar
  have hMp : Mbar.index = p :=
    (Nat.prime_dvd_prime_iff_eq hMprime Fact.out).mp (hMprime.dvd_of_dvd_pow hMdvd)
  refine ⟨Subgroup.comap (QuotientGroup.mk' K) Mbar, inferInstance, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K), hMp]

/-- 正規 `p`-補群の性質は**全射像**に遺伝する。 -/
theorem hasNormalPComplement_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    {p : ℕ} [Fact p.Prime] {f : A →* B} (hf : Function.Surjective f)
    (hA : HasNormalPComplement p A) : HasNormalPComplement p B := by
  classical
  haveI : Finite B := Finite.of_surjective f hf
  obtain ⟨N, hNnormal, hNcompl⟩ := hA
  haveI := hNnormal
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p A))
  have hpN : ¬ p ∣ Nat.card ↥N := not_dvd_card_of_isComplement'_sylow Q (hNcompl Q)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hNidx : N.index = p ^ a := by rw [(hNcompl Q).symm.index_eq_card, ha]
  haveI : (N.map f).Normal := hNnormal.map _ hf
  have hidxdvd : (N.map f).index ∣ p ^ a := hNidx ▸ N.index_map_dvd hf
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Fact.out).mp hidxdvd
  refine hasNormalPComplement_of_normal_of_index_eq_pow (X := N.map f) (a := b) ?_ hb
  intro hdvd
  exact hpN (hdvd.trans (Subgroup.card_map_dvd _ _))

/-- 真部分群がすべて正規 `p`-補群をもち `G` 自身は持たないとき, `O_p(G) ≠ 1`。

Frobenius Thm 5.26 の対偶で `N_G(X)` が正規 `p`-補群を持たない非自明 `p`-部分群が取れ,
仮定からそれは `⊤` すなわち `X ◁ G`。 -/
theorem opCore_ne_bot_of_minimal_non_pNilpotent [Finite G] {p : ℕ} [Fact p.Prime]
    (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) :
    Ch01.opCore p G ≠ ⊥ := by
  classical
  intro hbot
  refine hG (hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer.mpr ?_)
  refine isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement ?_
  intro X hXbot hXp
  by_cases htop : Subgroup.normalizer (X : Set G) = ⊤
  · haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    exact absurd (le_bot_iff.mp (hbot ▸ Ch01.normal_pgroup_le_opCore hXp)) hXbot
  · exact hproper _ htop

/-- 真部分群がすべて正規 `p`-補群をもち `G` 自身は持たないとき, 指数 `p` の正規部分群は無い。

⭐ Itô の定理の鍵。真部分群 `M` の正規 `p`-補群は一意性から `M` に characteristic なので
`G` でも正規になり, 指数が `p`-冪ゆえ `G` の正規 `p`-補群になってしまう。 -/
theorem not_exists_normal_index_eq_prime_of_minimal_non_pNilpotent [Finite G] {p : ℕ}
    [Fact p.Prime] (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) :
    ¬ ∃ M : Subgroup G, M.Normal ∧ M.index = p := by
  classical
  rintro ⟨M, hMnormal, hMidx⟩
  haveI := hMnormal
  have hMtop : M ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hMidx
    exact (Fact.out : p.Prime).one_lt.ne hMidx
  obtain ⟨C', hC'normal, hC'compl⟩ := hproper M hMtop
  haveI := hC'normal
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  haveI : C'.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro ψ
    exact map_mulAut_of_normal_pcomplement (hC'compl S) ψ
  haveI hCnormal : (C'.map M.subtype).Normal := Ch01.characteristic_map_subtype_normal C'
  have hpC : ¬ p ∣ Nat.card ↥(C'.map M.subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective M)]
    exact not_dvd_card_of_isComplement'_sylow S (hC'compl S)
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hrel : (C'.map M.subtype).relIndex M * M.index = (C'.map M.subtype).index :=
    Subgroup.relIndex_mul_index (Subgroup.map_subtype_le _)
  have hrel2 : (C'.map M.subtype).relIndex M = C'.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M)]
  refine hG (hasNormalPComplement_of_normal_of_index_eq_pow
    (X := C'.map M.subtype) (a := c + 1) hpC ?_)
  rw [← hrel, hrel2, (hC'compl S).symm.index_eq_card, hc, hMidx, pow_succ]

/-- **補題 3**: 真部分群がすべて正規 `p`-補群をもつなら, 商 `G ⧸ O_p(G)` は `p`-冪零。

そうでなければ `G ⧸ O_p(G)` もまた「真部分群はすべて `p`-冪零だが自身はそうでない」を満たす
(真部分群は `G` の真部分群の全射像) ので**補題 1** が使えて `O_p(G ⧸ O_p(G)) ≠ 1`。
その引き戻しは `G` の正規 `p`-部分群なので `O_p(G)` に含まれ, 像が `⊥` になって矛盾。

⚠ `G` 自身が `p`-冪零でないことは**不要** (その場合も商は `p`-冪零)。 -/
theorem hasNormalPComplement_quotient_opCore_of_forall_proper [Finite G] {p : ℕ}
    [Fact p.Prime] (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H) :
    HasNormalPComplement p (G ⧸ Ch01.opCore p G) := by
  classical
  set O : Subgroup G := Ch01.opCore p G with hOdef
  by_contra hQ
  -- `G ⧸ O` の真部分群はすべて `G` の真部分群の全射像ゆえ `p`-冪零
  have hproperQ : ∀ L : Subgroup (G ⧸ O), L ≠ ⊤ → HasNormalPComplement p ↥L := by
    intro L hL
    have hcomap : Subgroup.comap (QuotientGroup.mk' O) L ≠ ⊤ := by
      intro htop
      apply hL
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) L,
        htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)]
    refine hasNormalPComplement_of_surjective
      (f := ((QuotientGroup.mk' O).restrict (Subgroup.comap (QuotientGroup.mk' O) L)).codRestrict
        L (fun x => x.2)) ?_ (hproper _ hcomap)
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hne := opCore_ne_bot_of_minimal_non_pNilpotent hproperQ hQ
  -- `O_p(G ⧸ O)` の引き戻しは正規 `p`-部分群 ⟹ `O` に含まれる ⟹ 像は `⊥`
  set M : Subgroup G := (Ch01.opCore p (G ⧸ O)).comap (QuotientGroup.mk' O) with hMdef
  haveI : M.Normal := (Ch01.opCore.normal p (G ⧸ O)).comap _
  have hMp : IsPGroup p ↥M :=
    isPGroup_comap_mk'_of_isPGroup (Ch01.opCore_isPGroup p G) (Ch01.opCore_isPGroup p (G ⧸ O))
  have hMle : M ≤ O := Ch01.normal_pgroup_le_opCore hMp
  have hmap : Ch01.opCore p (G ⧸ O) = M.map (QuotientGroup.mk' O) := by
    rw [hMdef, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
  refine hne ?_
  rw [hmap]
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  rintro x ⟨g, hgM, rfl⟩
  rw [QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff _).mpr (hMle hgM)

/-- **Isaacs Problem 5E.1(a)** (p. 175) ⭐: 真部分群がすべて正規 `p`-補群をもつが `G` 自身は
持たないとき, `G` の Sylow `p`-部分群は `O_p(G)` に一致する — とくに**正規**である。

補題 3 の正規 `p`-補群の引き戻し `K` は指数が `p`-冪。`K ≠ ⊤` なら
`exists_normal_index_eq_prime_of_index_eq_pow` が指数 `p` の正規部分群を与えて**補題 2** に矛盾。
ゆえに `K = ⊤`, すなわち `G ⧸ O_p(G)` は `p'`-群で `O_p(G)` が Sylow `p`-部分群。 -/
theorem sylow_eq_opCore_of_minimal_non_pNilpotent [Finite G] {p : ℕ} [Fact p.Prime]
    (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) (P : Sylow p G) :
    (P : Subgroup G) = Ch01.opCore p G := by
  classical
  set O : Subgroup G := Ch01.opCore p G with hOdef
  obtain ⟨Kbar, hKbarN, hKbarC⟩ :=
    hasNormalPComplement_quotient_opCore_of_forall_proper hproper
  haveI := hKbarN
  obtain ⟨Qbar⟩ := (inferInstance : Nonempty (Sylow p (G ⧸ O)))
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp Qbar.isPGroup'
  have hKidx : Kbar.index = p ^ a := by rw [(hKbarC Qbar).symm.index_eq_card, ha]
  -- `a ≠ 0` なら指数 `p` の正規部分群ができて補題 2 に矛盾
  have ha0 : a = 0 := by
    by_contra hane
    haveI : (Kbar.comap (QuotientGroup.mk' O)).Normal := hKbarN.comap _
    have hKGidx : (Kbar.comap (QuotientGroup.mk' O)).index = p ^ a := by
      rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective O), hKidx]
    exact not_exists_normal_index_eq_prime_of_minimal_non_pNilpotent hproper hG
      (exists_normal_index_eq_prime_of_index_eq_pow (Nat.pos_of_ne_zero hane) hKGidx)
  -- ⟹ `G ⧸ O` の Sylow `p`-部分群は自明 ⟹ `p ∤ |G : O|`
  have hQcard : Nat.card ↥(Qbar : Subgroup (G ⧸ O)) = 1 := by rw [ha, ha0, pow_zero]
  have hfactQ : (Nat.card (G ⧸ O)).factorization p = 0 := by
    have := Qbar.card_eq_multiplicity
    rw [hQcard] at this
    exact (Nat.pow_eq_one.mp this.symm).resolve_left (Fact.out : p.Prime).one_lt.ne'
  have hpidx : ¬ p ∣ O.index := by
    rw [Subgroup.index_eq_card]
    intro hdvd
    have h1 : p ^ 1 ∣ Nat.card (G ⧸ O) := by simpa using hdvd
    have := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h1
    omega
  -- `|O|` は `|G|` の `p`-部分と一致するので `O` は Sylow
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (Ch01.opCore_isPGroup p G)
  have hfactG : (Nat.card G).factorization p = m := by
    rw [← Subgroup.card_mul_index O, hm,
      Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).pos.ne')
        Subgroup.index_ne_zero_of_finite]
    simp [Nat.factorization_eq_zero_of_not_dvd hpidx, (Fact.out : p.Prime).factorization_self]
  have hPcard : Nat.card ↥(P : Subgroup G) = Nat.card ↥O := by
    rw [P.card_eq_multiplicity, hfactG, hm]
  exact (Subgroup.eq_of_le_of_card_ge (Ch01.opCore_le P) hPcard.le).symm

/-- **Isaacs Problem 5E.1(a)**: 極小非 `p`-冪零群は**正規** Sylow `p`-部分群をもつ。 -/
theorem normal_sylow_of_minimal_non_pNilpotent [Finite G] {p : ℕ} [Fact p.Prime]
    (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  rw [sylow_eq_opCore_of_minimal_non_pNilpotent hproper hG P]
  infer_instance

end

end OddOrder.Isaacs.Ch05
