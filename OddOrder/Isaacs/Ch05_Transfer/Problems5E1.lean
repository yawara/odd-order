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

/-- **Isaacs Problem 5E.1(b)** (p. 175) ⭐: 真部分群がすべて正規 `p`-補群をもつが `G` 自身は
持たないとき, `|G|` は `p` 以外の素因数を**ちょうど 1 個**もつ (すなわち `|G| = p^a q^b`)。

(a) の正規 Sylow `p`-部分群 `P = O_p(G)` に Schur–Zassenhaus で Hall `p'`-補群 `H` を取る。
`|H|` が 2 個以上の素因数をもつと仮定すると, `H` の各 Sylow `q`-部分群 `T` について
`P ⊔ T` は**真部分群** (商 `G ⧸ P` に落として位数で見る) ゆえ `p`-冪零。その正規 `p`-補群は
位数計算から `T` 自身に一致するので `T ⊴ P ⊔ T`, したがって `⁅P, T⁆ ≤ P ⊓ T = 1`。
`H` は Sylow たちで生成される (5C.11 `iSup_sylow_eq_top`) ので `H ≤ C_G(P)`, ゆえに
`G = P·H ≤ N_G(H)` で `H ⊴ G` — これは `G` の正規 `p`-補群になり仮定に矛盾。 -/
theorem prime_dvd_card_of_not_hasNormalPComplement [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ HasNormalPComplement p G) : p ∣ Nat.card G := by
  by_contra hnd
  refine hG (hasNormalPComplement_of_normal_of_index_eq_pow
    (X := (⊤ : Subgroup G)) (a := 0) ?_ (by rw [Subgroup.index_top, pow_zero]))
  rwa [Subgroup.card_top]

theorem card_primeFactors_erase_eq_one_of_minimal_non_pNilpotent [Finite G] {p : ℕ}
    [Fact p.Prime] (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) :
    ((Nat.card G).primeFactors.erase p).card = 1 := by
  classical
  have hp : p.Prime := Fact.out
  set O : Subgroup G := Ch01.opCore p G with hOdef
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p G))
  have hPO : (P₀ : Subgroup G) = O := sylow_eq_opCore_of_minimal_non_pNilpotent hproper hG P₀
  have hpG : p ∣ Nat.card G := prime_dvd_card_of_not_hasNormalPComplement hG
  set m : ℕ := (Nat.card G).factorization p with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp (by simpa using hpG)
  have hOcard : Nat.card ↥O = p ^ m := by rw [← hPO, P₀.card_eq_multiplicity]
  -- Schur–Zassenhaus で Hall `p'`-補群 `H`
  have hcop : Nat.Coprime (Nat.card ↥O) O.index := by rw [← hPO]; exact P₀.card_coprime_index
  obtain ⟨H, hOH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : O.index = Nat.card ↥H := hOH.symm.index_eq_card
  have hpOidx : ¬ p ∣ O.index := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mp ?_
    exact Nat.Coprime.coprime_dvd_left (hOcard ▸ dvd_pow_self p (by omega)) hcop
  have hpH : ¬ p ∣ Nat.card ↥H := hHcard ▸ hpOidx
  -- `H ≠ 1` (さもなければ `G` が `p`-群で `⊥` が正規 `p`-補群)
  have hHne1 : Nat.card ↥H ≠ 1 := by
    intro h1
    have hidx1 : O.index = 1 := by rw [hHcard, h1]
    have hGcard : Nat.card G = p ^ m := by
      rw [← Subgroup.card_mul_index O, hidx1, mul_one, hOcard]
    refine hG (hasNormalPComplement_of_normal_of_index_eq_pow
      (X := (⊥ : Subgroup G)) (a := m) ?_ (by rw [Subgroup.index_bot, hGcard]))
    rw [Subgroup.card_bot]
    exact fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)
  -- ⭐ 主張: `|H|` は 2 個以上の素因数をもてない
  have hkey : (Nat.card ↥H).primeFactors.card ≤ 1 := by
    by_contra hcon
    push Not at hcon
    -- 各素因数 `q` の Sylow `q`-部分群 (を `G` に移したもの) は `O` を中心化する
    have hcent : ∀ q ∈ (Nat.card ↥H).primeFactors, ∀ S : Sylow q ↥H,
        ((S : Subgroup ↥H).map H.subtype) ≤ Subgroup.centralizer (O : Set G) := by
      intro q hq S
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      haveI : Fact q.Prime := ⟨hqprime⟩
      set T : Subgroup G := (S : Subgroup ↥H).map H.subtype with hTdef
      have hTle : T ≤ H := Subgroup.map_subtype_le _
      have hTcard : Nat.card ↥T = Nat.card ↥(S : Subgroup ↥H) := by
        rw [hTdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective H)]
      have hHO : H ⊓ O = ⊥ := by rw [inf_comm]; exact disjoint_iff.mp hOH.disjoint
      have hTO : T ⊓ O = ⊥ := le_bot_iff.mp (hHO ▸ inf_le_inf_right O hTle)
      have hpT : ¬ p ∣ Nat.card ↥T := fun h => hpH (h.trans (Subgroup.card_dvd_of_le hTle))
      -- `|H|` は 2 個以上の素因数をもつので `|T| ≠ |H|`
      obtain ⟨r, hrmem, hrne⟩ : ∃ r ∈ (Nat.card ↥H).primeFactors, r ≠ q := by
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcon
        by_cases haq : a = q
        · exact ⟨b, hb, fun h => hab (haq.trans h.symm)⟩
        · exact ⟨a, ha, haq⟩
      have hTne : Nat.card ↥T ≠ Nat.card ↥H := by
        rw [hTcard, S.card_eq_multiplicity]
        intro heq
        have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hrmem
        have hrdvd : r ∣ q ^ (Nat.card ↥H).factorization q := by
          rw [heq]; exact Nat.dvd_of_mem_primeFactors hrmem
        exact hrne ((Nat.prime_dvd_prime_iff_eq hrprime hqprime).mp
          (hrprime.dvd_of_dvd_pow hrdvd))
      -- `O ⊔ T` は真部分群 (商 `G ⧸ O` で見ると `T` の像しか無い)
      have hsupmap : (O ⊔ T).map (QuotientGroup.mk' O) = T.map (QuotientGroup.mk' O) := by
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
      have hOTne : O ⊔ T ≠ ⊤ := by
        intro htop
        have h2 : (O ⊔ T).map (QuotientGroup.mk' O) = ⊤ := by
          rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)]
        have h3 : Nat.card ↥(T.map (QuotientGroup.mk' O)) = Nat.card ↥T :=
          card_map_mk'_of_inf_eq_bot hTO
        rw [← hsupmap, h2, Subgroup.card_top, ← Subgroup.index_eq_card, hHcard] at h3
        exact hTne h3.symm
      obtain ⟨C, hCN, hCC⟩ := hproper (O ⊔ T) hOTne
      haveI := hCN
      -- `|O ⊔ T| = |O| · |T|`
      have hKcard : Nat.card ↥(O ⊔ T) = Nat.card ↥O * Nat.card ↥T := by
        have hcomapK :
            Subgroup.comap (QuotientGroup.mk' O) ((O ⊔ T).map (QuotientGroup.mk' O)) = O ⊔ T :=
          Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
        have hidxK : (Subgroup.comap (QuotientGroup.mk' O)
            ((O ⊔ T).map (QuotientGroup.mk' O))).index
            = ((O ⊔ T).map (QuotientGroup.mk' O)).index :=
          Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective O)
        rw [hcomapK] at hidxK
        have e1 : Nat.card ↥(O ⊔ T) * (O ⊔ T).index = Nat.card G := Subgroup.card_mul_index _
        have e2 : Nat.card ↥O * O.index = Nat.card G := Subgroup.card_mul_index _
        have e3 : Nat.card ↥((O ⊔ T).map (QuotientGroup.mk' O))
            * ((O ⊔ T).map (QuotientGroup.mk' O)).index = Nat.card (G ⧸ O) :=
          Subgroup.card_mul_index _
        have e4 : Nat.card ↥((O ⊔ T).map (QuotientGroup.mk' O)) = Nat.card ↥T := by
          rw [hsupmap]; exact card_map_mk'_of_inf_eq_bot hTO
        rw [e4, ← hidxK, ← Subgroup.index_eq_card] at e3
        have hpos : 0 < (O ⊔ T).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        refine Nat.eq_of_mul_eq_mul_right hpos ?_
        rw [e1, ← e2, ← e3]
        ring
      -- `O ⊔ T` の正規 `p`-補群 `C` は位数計算から `T` に一致
      obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p ↥(O ⊔ T)))
      have hfactK : (Nat.card ↥(O ⊔ T)).factorization p = m := by
        rw [hKcard, hOcard, Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') Nat.card_pos.ne']
        simp [Nat.factorization_eq_zero_of_not_dvd hpT, hp.factorization_pow]
      have hCidx : C.index = p ^ m := by
        rw [(hCC R).symm.index_eq_card, R.card_eq_multiplicity, hfactK]
      have hT'card : Nat.card ↥(T.subgroupOf (O ⊔ T)) = Nat.card ↥T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : T ≤ O ⊔ T)).toEquiv
      have hT'le : T.subgroupOf (O ⊔ T) ≤ C :=
        le_of_index_eq_pow_of_not_dvd_card hCidx (by rw [hT'card]; exact hpT)
      have hCcard : Nat.card ↥C = Nat.card ↥T := by
        have hCm := Subgroup.card_mul_index C
        rw [hCidx, hKcard, hOcard, mul_comm (p ^ m) (Nat.card ↥T)] at hCm
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos m) hCm
      have hT'eq : T.subgroupOf (O ⊔ T) = C :=
        Subgroup.eq_of_le_of_card_ge hT'le (by rw [hCcard, hT'card])
      -- ⟹ `T ⊴ O ⊔ T` ⟹ `⁅O, T⁆ ≤ O ⊓ T = 1`
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxK : x ∈ O ⊔ T := (le_sup_left : O ≤ O ⊔ T) hx
      have htK : t ∈ O ⊔ T := (le_sup_right : T ≤ O ⊔ T) ht
      have hconjT : x * t * x⁻¹ ∈ T := by
        have htmem : (⟨t, htK⟩ : ↥(O ⊔ T)) ∈ C := by rw [← hT'eq]; exact ht
        have hmemC : (⟨x, hxK⟩ : ↥(O ⊔ T)) * ⟨t, htK⟩ * (⟨x, hxK⟩ : ↥(O ⊔ T))⁻¹ ∈ C :=
          hCN.conj_mem _ htmem _
        rw [← hT'eq] at hmemC
        simpa [Subgroup.mem_subgroupOf] using hmemC
      have hone : x * t * x⁻¹ * t⁻¹ = 1 := by
        have hmemT : x * t * x⁻¹ * t⁻¹ ∈ T := Subgroup.mul_mem _ hconjT (Subgroup.inv_mem _ ht)
        have hmemO : x * t * x⁻¹ * t⁻¹ ∈ O := by
          have h1 : t * x⁻¹ * t⁻¹ ∈ O := (Ch01.opCore.normal p G).conj_mem _ (inv_mem hx) t
          have h2 : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
          rw [h2]
          exact Subgroup.mul_mem _ hx h1
        have hmem : x * t * x⁻¹ * t⁻¹ ∈ T ⊓ O := ⟨hmemT, hmemO⟩
        rwa [hTO, Subgroup.mem_bot] at hmem
      calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
        _ = 1 * (t * x) := by rw [hone]
        _ = t * x := one_mul _
    -- `H` は Sylow たちで生成されるので `H ≤ C_G(O)`
    have hHcent : H ≤ Subgroup.centralizer (O : Set G) := by
      have hsup : H = (⨆ (q : (Nat.card ↥H).primeFactors) (S : Sylow (q : ℕ) ↥H),
          (S : Subgroup ↥H)).map H.subtype := by
        rw [iSup_sylow_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [hsup]
      simp only [Subgroup.map_iSup]
      exact iSup_le fun q => iSup_le fun S => hcent q q.2 S
    -- `G = O·H ≤ N_G(H)` ⟹ `H ⊴ G` ⟹ `H` が正規 `p`-補群 — 矛盾
    have hHnormal : H.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      refine top_le_iff.mp ?_
      rw [← hOH.sup_eq_top]
      refine sup_le ?_ Subgroup.le_normalizer
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hcm := (Subgroup.mem_centralizer_iff.mp (hHcent hh)) x hx
        have heq : x * h * x⁻¹ = h := by rw [hcm]; group
        rw [heq]
        exact hh
      · intro hh
        have hcm := (Subgroup.mem_centralizer_iff.mp (hHcent hh)) x⁻¹ (inv_mem hx)
        have heq : h * x⁻¹ = (x * h * x⁻¹) * x⁻¹ := by rw [← hcm]; group
        rw [mul_right_cancel heq]
        exact hh
    haveI := hHnormal
    exact hG (hasNormalPComplement_of_normal_of_index_eq_pow (X := H) (a := m) hpH
      (by rw [hOH.index_eq_card, hOcard]))
  -- `|H|` の素因数はちょうど 1 個、そして `primeFactors |G| = {p} ∪ primeFactors |H|`
  have hHone : (Nat.card ↥H).primeFactors.card = 1 := by
    refine le_antisymm hkey (Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr ?_))
    have := Nat.card_pos (α := ↥H)
    omega
  have hGcard : Nat.card G = p ^ m * Nat.card ↥H := by
    rw [← Subgroup.card_mul_index O, hOcard, hHcard]
  have hpf : (Nat.card G).primeFactors = insert p (Nat.card ↥H).primeFactors := by
    rw [hGcard, Nat.primeFactors_mul (pow_ne_zero _ hp.pos.ne') Nat.card_pos.ne',
      Nat.primeFactors_pow p (by omega), hp.primeFactors, ← Finset.insert_eq]
  rw [hpf, Finset.erase_insert (fun h => hpH (Nat.dvd_of_mem_primeFactors h))]
  exact hHone

/-- **Isaacs Problem 5E.1** のまとめ (Itô): 真部分群がすべて正規 `p`-補群をもつが `G` 自身は
持たないとき, `|G| = p^a q^b` (`q ≠ p` は素数, `a, b ≥ 1`)。

正規 Sylow `p`-部分群の存在は `normal_sylow_of_minimal_non_pNilpotent`。 -/
theorem exists_prime_card_eq_pow_mul_pow_of_minimal_non_pNilpotent [Finite G] {p : ℕ}
    [Fact p.Prime] (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) :
    ∃ q a b : ℕ, q.Prime ∧ q ≠ p ∧ 1 ≤ a ∧ 1 ≤ b ∧ Nat.card G = p ^ a * q ^ b := by
  classical
  have hp : p.Prime := Fact.out
  have hcard0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨q, hqeq⟩ :=
    Finset.card_eq_one.mp (card_primeFactors_erase_eq_one_of_minimal_non_pNilpotent hproper hG)
  have hqmem : q ∈ (Nat.card G).primeFactors.erase p := by
    rw [hqeq]; exact Finset.mem_singleton_self q
  have hqne : q ≠ p := Finset.ne_of_mem_erase hqmem
  have hqpf : q ∈ (Nat.card G).primeFactors := Finset.mem_of_mem_erase hqmem
  have hppf : p ∈ (Nat.card G).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, prime_dvd_card_of_not_hasNormalPComplement hG, hcard0⟩
  have hpair : (Nat.card G).primeFactors = {p, q} := by
    conv_lhs => rw [← Finset.insert_erase hppf]
    rw [hqeq]
  refine ⟨q, (Nat.card G).factorization p, (Nat.card G).factorization q,
    Nat.prime_of_mem_primeFactors hqpf, hqne,
    hp.factorization_pos_of_dvd hcard0 (Nat.dvd_of_mem_primeFactors hppf),
    (Nat.prime_of_mem_primeFactors hqpf).factorization_pos_of_dvd hcard0
      (Nat.dvd_of_mem_primeFactors hqpf), ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hcard0]
  rw [Finsupp.prod, Nat.support_factorization, hpair, Finset.prod_pair (Ne.symm hqne)]

end

end OddOrder.Isaacs.Ch05
