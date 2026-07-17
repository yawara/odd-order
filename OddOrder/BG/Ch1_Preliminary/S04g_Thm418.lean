/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S04f_Blackburn
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.GroupTheory.OpResidual
import OddOrder.Mathlib.Subgroup

/-!
# BG §4H: Theorem 4.18 — rank-2 solvable structure

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §4, **Theorem 4.18** (printed p. 43, mmd
`references/bg/local-analysis.mmd` L1734-1752)。

`G` solvable odd, `p ∈ π(G)`, `r_p(G) ≤ 2` のとき:
(a) `p` は `|G/O_{p'}(G)|` の最大素因子, (b) `p = 3` または `p` が最小素因子なら normal
`p`-complement, (c) `G'` は normal `p`-complement を持つ, (d) `G'` の `p'`-部分群は
`O_{p'}(G')` に入る, (e) `G/O_{p',p}(G)` は abelian `p'`-群。

## 証明の骨格 (BG)

`O_{p'}(G) = 1` に帰着 (`core418`)。`R = O_p(G)`, `C = C_G(R)` とおくと
**G** Thm 6.3.2 (= repo `Ch03.hall_higman_1_2_3`) で `C ≤ R`。Lemma 4.17
(`isPGroup_commutator_of_mulAut_odd_of_pRank_le_two`) で `(G/C)'` は `p`-群、
`C` も `p`-群なので `G'` の引き戻しが normal `p`-部分群となり `O_p(G) = R` に入る。
`G/R` は abelian で `O_p(G/R) = 1` ゆえ `p'`-群。`SCN₃(R) = ∅` (rank ≤ 2) と
Lemma 4.13 (`dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty`) で
`q ≠ p` なる素因子は `q < p`。一般の場合は商 `Ḡ = G/O_{p'}(G)` に core を適用して
引き戻す (rank の転送は `pRank_quotient_le_of_coprime`: `p'`-核による商の `p`-rank は
増えない)。

## 下流

BG §5 Thm 5.6 / Thm 5.7 (`S05_NarrowPGroups`)、Cor 4.19 / Thm 4.20。

## 記法 (BG → repo)

- `O_{p'}(G)` = `Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G` (= `{r | r ≠ p}` 形と集合として
  等しい; `oPiPrimePiCore` の内部表現に合わせる)。`O_p(G)` = `Ch03.oPiCore {p} G`;
  `O_{p',p}(G)` = `Ch03.oPiPrimePiCore {p} G`。
- normal `p`-complement = `Ch05.HasNormalPComplement`。
- `p`-length one = `hasPLengthOne` (`PLength.lean`)。
- `r_p(G)` = `pRank G p` (`GroupTheory.PRank`)。
-/

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped commutatorElement

section Thm418

variable {G : Type*} [Group G] [Finite G]

/-- `{q | q ∉ ({p} : Set ℕ)} = {r | r ≠ p}` — `oPiPrimePiCore` の内部表現と
Thm 5.6 語彙の橋。S05 (Thm 5.6 narrow core) でも使う。 -/
theorem compl_singleton_eq {p : ℕ} :
    {q : ℕ | q ∉ ({p} : Set ℕ)} = {r : ℕ | r ≠ p} := by
  ext q
  simp [Set.mem_singleton_iff]

/-- π-glue: `p`-部分群は `{p}`-群。 -/
theorem isPiGroup_singleton_of_isPGroup {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPGroup p ↥H) : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := by
  intro q hq
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  rw [hk, Nat.mem_primeFactors] at hq
  have hq_eq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq.1 (Fact.out : p.Prime)).mp
      (hq.1.dvd_of_dvd_pow hq.2.1)
  simp [hq_eq]

/-- π-glue: `{p}`-群は `p`-部分群。 -/
theorem isPGroup_of_isPiGroup_singleton {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H) : IsPGroup p ↥H := by
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card ↥H).primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_
  intro q hq hq_dvd
  have hmem : q ∈ (Nat.card ↥H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, Nat.card_pos.ne'⟩
  exact Set.mem_singleton_iff.mp (hH q hmem)

/-- `p ∉ π` なら `p ∤ |O_π(G)|`。 -/
theorem not_dvd_card_oPiCore {p : ℕ} [Fact p.Prime] {π : Set ℕ}
    (hp_notin : p ∉ π) : ¬ p ∣ Nat.card ↥(Ch03.oPiCore π G) := by
  intro hdvd
  have hmem : p ∈ (Nat.card ↥(Ch03.oPiCore π G)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
  exact hp_notin (Ch03.oPiCore.isPiGroup π p hmem)

omit [Finite G] in
/-- **`MulAut.conjNormal` の核は中心化群**。S05 (Thm 5.6 narrow core) でも使う。 -/
theorem conjNormal_ker {N : Subgroup G} [N.Normal] :
    (MulAut.conjNormal (G := G) (H := N)).ker = Subgroup.centralizer (N : Set G) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h n hn
    have happ := congrArg (fun e : MulAut ↥N => ((e ⟨n, hn⟩ : ↥N) : G)) h
    simp only [MulAut.one_apply, MulAut.conjNormal_apply] at happ
    -- happ : a * n * a⁻¹ = n
    calc n * a = (a * n * a⁻¹) * a := by rw [happ]
      _ = a * n := by group
  · intro h
    ext n
    simp only [MulAut.one_apply, MulAut.conjNormal_apply]
    have hcomm := h (n : G) n.2
    calc a * (n : G) * a⁻¹ = ((n : G) * a) * a⁻¹ := by rw [← hcomm]
      _ = (n : G) := by group

/-- If a subgroup has `p`-group conjugation image on a minimal normal `p`-subgroup,
then it centralizes that subgroup. This is the fixed-point argument used in BG
Corollary 4.19: a nontrivial fixed-point subgroup is normal, hence all of the
chief factor. -/
theorem le_centralizer_of_isPGroup_conjNormal_image_minimalNormal
    {D N : Subgroup G} [D.Normal] [N.Normal] (hMin : Ch02.IsMinimalNormal N)
    {p : ℕ} [Fact p.Prime] (hN_pg : IsPGroup p ↥N)
    (hD_pg : IsPGroup p ↥(D.map (MulAut.conjNormal (H := N)))) :
    D ≤ Subgroup.centralizer (N : Set G) := by
  classical
  set α : G →* MulAut ↥N := MulAut.conjNormal with hα_def
  have hD_pgPrime : IsPGroup p ↥(D.map α) := by
    rw [hα_def]
    exact hD_pg
  haveI hN_nontriv : Nontrivial ↥N := by
    rcases Subgroup.bot_or_nontrivial N with h | h
    · exact absurd h hMin.2.1
    · exact h
  have hfix_ne : Subgroup.fixedPointsOfMulAut (D.map α).subtype ≠ ⊥ :=
    Ch04.fixedPoints_ne_bot_of_pgroup_action_pgroup hN_pg hD_pgPrime _
  set W : Subgroup G :=
    (Subgroup.fixedPointsOfMulAut (D.map α).subtype).map N.subtype with hW_def
  have hW_mem : ∀ x : G, x ∈ W ↔ x ∈ N ∧ ∀ d ∈ D, d * x * d⁻¹ = x := by
    intro x
    constructor
    · rintro ⟨⟨n, hn⟩, hfix, rfl⟩
      refine ⟨hn, fun d hd => ?_⟩
      have h1 := Subgroup.mem_fixedPointsOfMulAut.mp hfix
        ⟨α d, Subgroup.mem_map.mpr ⟨d, hd, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      calc d * (N.subtype ⟨n, hn⟩) * d⁻¹
          = (((α d) ⟨n, hn⟩ : ↥N) : G) :=
            (MulAut.conjNormal_apply d (⟨n, hn⟩ : ↥N)).symm
        _ = N.subtype ⟨n, hn⟩ := h2
    · rintro ⟨hxN, hxfix⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_fixedPointsOfMulAut]
      intro a
      obtain ⟨d, hd, ha⟩ := a.2
      have h3 : a.1 ⟨x, hxN⟩ = (⟨x, hxN⟩ : ↥N) := by
        rw [← ha]
        apply Subtype.ext
        calc (((α d) ⟨x, hxN⟩ : ↥N) : G)
            = d * x * d⁻¹ := MulAut.conjNormal_apply d (⟨x, hxN⟩ : ↥N)
          _ = x := hxfix d hd
      exact h3
  have hW_le : W ≤ N := by
    intro x hx
    exact ((hW_mem x).mp hx).1
  have hW_ne : W ≠ ⊥ := by
    intro h
    apply hfix_ne
    rw [hW_def, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at h
    exact h
  haveI hW_norm : W.Normal := by
    constructor
    intro n hn g
    obtain ⟨hnN, hnfix⟩ := (hW_mem n).mp hn
    refine (hW_mem _).mpr ⟨(inferInstance : N.Normal).conj_mem n hnN g, fun d hd => ?_⟩
    have hdPrime : g⁻¹ * d * g ∈ D := by
      simpa using (inferInstance : D.Normal).conj_mem d hd g⁻¹
    have hfix := hnfix _ hdPrime
    calc d * (g * n * g⁻¹) * d⁻¹
        = g * ((g⁻¹ * d * g) * n * (g⁻¹ * d * g)⁻¹) * g⁻¹ := by group
      _ = g * n * g⁻¹ := by rw [hfix]
  rcases hMin.2.2 W (inferInstance : W.Normal) hW_le with hW_bot | hW_top
  · exact absurd hW_bot hW_ne
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnW : n ∈ W := by rw [hW_top]; exact hn
    have hfix := ((hW_mem n).mp hnW).2 d hd
    calc n * d = (d * n * d⁻¹) * d := by rw [hfix]
      _ = d * n := by group

/-- Corollary 4.19 fixed-point endpoint for an arbitrary chief factor: if the
image of `D` acting by conjugation on the quotient chief factor `U/V` is a
`p`-group, then `D` centralizes `U/V`. -/
theorem le_chiefFactorCentralizer_of_isPGroup_conjNormal_image_chiefFactor
    {p : ℕ} [Fact p.Prime] {D U V : Subgroup G} [D.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal] (hChief : IsChiefFactor U V)
    (hUbar_pg : IsPGroup p ↥(U.map (QuotientGroup.mk' V)))
    (hDbar_pg : IsPGroup p
      ↥((D.map (QuotientGroup.mk' V)).map
        (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V))))) :
    D ≤ chiefFactorCentralizer U V := by
  haveI hDbar_normal : (D.map (QuotientGroup.mk' V)).Normal :=
    (inferInstance : D.Normal).map _ (QuotientGroup.mk'_surjective V)
  have hMin : Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
    hChief.isMinimalNormal_map_quotient
  have hcent :
      D.map (QuotientGroup.mk' V) ≤
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) :=
    le_centralizer_of_isPGroup_conjNormal_image_minimalNormal
      (G := G ⧸ V) (D := D.map (QuotientGroup.mk' V))
      (N := U.map (QuotientGroup.mk' V)) hMin hUbar_pg hDbar_pg
  exact chiefFactorCentralizer.le_of_map_le_centralizer hcent

omit [Finite G] in
/-- If a homomorphism `φ` kills `K`, then a `p`-group derived subgroup in
`G/K` gives a `p`-group image of `G'` under `φ`. This packages the quotient
map calculation used in Corollary 4.19 and the §5 rank/narrow variants. -/
theorem isPGroup_commutator_map_of_quotient_commutator_isPGroup
    {A : Type*} [Group A] {p : ℕ} {K : Subgroup G} [K.Normal] (φ : G →* A)
    (hK : K ≤ φ.ker) (hQ : IsPGroup p ↥(_root_.commutator (G ⧸ K))) :
    IsPGroup p ↥((_root_.commutator G).map φ) := by
  let φbar : G ⧸ K →* A :=
    QuotientGroup.lift K φ (fun k hk => MonoidHom.mem_ker.mp (hK hk))
  have hcomp : φbar.comp (QuotientGroup.mk' K) = φ := by
    ext g
    rfl
  have hmapK : (_root_.commutator G).map (QuotientGroup.mk' K) =
      _root_.commutator (G ⧸ K) := by
    rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  have hmap : (_root_.commutator G).map φ =
      (_root_.commutator (G ⧸ K)).map φbar := by
    rw [← hcomp, ← hmapK, Subgroup.map_map]
  rw [hmap]
  exact hQ.map φbar

omit [Finite G] in
/-- Lemma 4.17 in the quotient-action form used by Corollary 4.19: if a
normal `p`-subgroup has `p`-rank at most two, then the derived subgroup of the
quotient by its conjugation kernel is a `p`-group. -/
theorem isPGroup_commutator_quotient_conjNormal_ker_of_pRank_le_two
    [Finite G] (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R : Subgroup G} [R.Normal] (hR_pg : IsPGroup p ↥R)
    (hR_rank : pRank ↥R p ≤ 2) :
    IsPGroup p (_root_.commutator (G ⧸ (MulAut.conjNormal (H := R)).ker)) := by
  let ψ : G →* MulAut ↥R := MulAut.conjNormal
  change IsPGroup p (_root_.commutator (G ⧸ ψ.ker))
  have hquot_dvd : Nat.card (G ⧸ ψ.ker) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card ψ.ker
    simpa [Subgroup.index] using this
  have hquot_odd : Odd (Nat.card (G ⧸ ψ.ker)) := by
    rcases Nat.even_or_odd (Nat.card (G ⧸ ψ.ker)) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  exact isPGroup_commutator_of_mulAut_odd_of_pRank_le_two hp_odd hR_pg hR_rank
    (QuotientGroup.kerLift_injective ψ) hquot_odd

/-- Corollary 4.19 action-image bridge, modulo the lower factor: if a normal
`p`-subgroup `R` has `p`-rank at most two and the top `U` of a chief factor is
contained in `R ⊔ V`, then the image of `G'` acting on `U/V` is a `p`-group. -/
theorem isPGroup_commutator_chiefFactor_conjNormal_image_of_pRank_le_two_of_le_sup
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R U V : Subgroup G} [R.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal]
    (hR_pg : IsPGroup p ↥R) (hR_rank : pRank ↥R p ≤ 2) (hU_le_RV : U ≤ R ⊔ V) :
    IsPGroup p ↥(((_root_.commutator G).map (QuotientGroup.mk' V)).map
      (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))) := by
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let N : Subgroup (G ⧸ V) := U.map q
  let φ : G →* MulAut ↥N := (MulAut.conjNormal (H := N)).comp q
  let K : Subgroup G := (MulAut.conjNormal (H := R)).ker
  have hK_le : K ≤ φ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    ext x
    obtain ⟨u, huU, hxu⟩ := x.2
    obtain ⟨r, hrR, v, hvV, hru⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := R) (t := V)).mp (hU_le_RV huU)
    have hg_fix_r : g * r * g⁻¹ = r := by
      have happ := congrArg
        (fun e : MulAut ↥R => ((e ⟨r, hrR⟩ : ↥R) : G)) hg
      simpa only [MulAut.one_apply, MulAut.conjNormal_apply] using happ
    have hqv : q v = 1 := by
      change (QuotientGroup.mk' V) v = 1
      exact (QuotientGroup.eq_one_iff v).mpr hvV
    have hq_u : q u = q r := by
      rw [← hru, map_mul, hqv, mul_one]
    change ((MulAut.conjNormal (H := N) (q g)) x : G ⧸ V) = (x : G ⧸ V)
    rw [MulAut.conjNormal_apply, ← hxu]
    calc q g * q u * (q g)⁻¹ = q g * q r * (q g)⁻¹ := by rw [hq_u]
      _ = q (g * r * g⁻¹) := by simp [q, map_mul]
      _ = q r := by rw [hg_fix_r]
      _ = q u := hq_u.symm
  have hQ : IsPGroup p ↥(_root_.commutator (G ⧸ K)) := by
    dsimp [K]
    exact isPGroup_commutator_quotient_conjNormal_ker_of_pRank_le_two
      hodd hp_odd hR_pg hR_rank
  have himg : IsPGroup p ↥((_root_.commutator G).map φ) :=
    isPGroup_commutator_map_of_quotient_commutator_isPGroup
      (K := K) φ hK_le hQ
  change IsPGroup p ↥(((_root_.commutator G).map q).map
    (MulAut.conjNormal (H := N)))
  rw [Subgroup.map_map]
  exact himg

/-- Corollary 4.19 action-image bridge: if a normal `p`-subgroup `R` has
`p`-rank at most two and contains the top `U` of a chief factor, then the image
of `G'` acting on `U/V` is a `p`-group. -/
theorem isPGroup_commutator_chiefFactor_conjNormal_image_of_pRank_le_two
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R U V : Subgroup G} [R.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal]
    (hR_pg : IsPGroup p ↥R) (hR_rank : pRank ↥R p ≤ 2) (hU_le_R : U ≤ R) :
    IsPGroup p ↥(((_root_.commutator G).map (QuotientGroup.mk' V)).map
      (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))) :=
  isPGroup_commutator_chiefFactor_conjNormal_image_of_pRank_le_two_of_le_sup
    hodd hp_odd hR_pg hR_rank (hU_le_R.trans le_sup_left)

/-- Corollary 4.19 centralizer bridge modulo the lower factor: under the
rank-two normal `p`-subgroup hypothesis, `G'` centralizes every `p`-chief factor
whose top lies in `R ⊔ V`. -/
theorem commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R U V : Subgroup G} [R.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal]
    (hChief : IsChiefFactor U V)
    (hUbar_pg : IsPGroup p ↥(U.map (QuotientGroup.mk' V)))
    (hR_pg : IsPGroup p ↥R) (hR_rank : pRank ↥R p ≤ 2) (hU_le_RV : U ≤ R ⊔ V) :
    _root_.commutator G ≤ chiefFactorCentralizer U V := by
  have hDbar_pg : IsPGroup p ↥(((_root_.commutator G).map (QuotientGroup.mk' V)).map
      (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))) :=
    isPGroup_commutator_chiefFactor_conjNormal_image_of_pRank_le_two_of_le_sup
      hodd hp_odd hR_pg hR_rank hU_le_RV
  exact le_chiefFactorCentralizer_of_isPGroup_conjNormal_image_chiefFactor
    (D := _root_.commutator G) hChief hUbar_pg hDbar_pg

/-- Corollary 4.19 centralizer bridge for a single chief factor: under the
rank-two normal `p`-subgroup hypothesis, `G'` centralizes every `p`-chief factor
whose top lies in that subgroup. -/
theorem commutator_le_chiefFactorCentralizer_of_pRank_le_two
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R U V : Subgroup G} [R.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal]
    (hChief : IsChiefFactor U V)
    (hUbar_pg : IsPGroup p ↥(U.map (QuotientGroup.mk' V)))
    (hR_pg : IsPGroup p ↥R) (hR_rank : pRank ↥R p ≤ 2) (hU_le_R : U ≤ R) :
    _root_.commutator G ≤ chiefFactorCentralizer U V := by
  have hDbar_pg : IsPGroup p ↥(((_root_.commutator G).map (QuotientGroup.mk' V)).map
      (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))) :=
    isPGroup_commutator_chiefFactor_conjNormal_image_of_pRank_le_two
      hodd hp_odd hR_pg hR_rank hU_le_R
  exact le_chiefFactorCentralizer_of_isPGroup_conjNormal_image_chiefFactor
    (D := _root_.commutator G) hChief hUbar_pg hDbar_pg

/-- **`p'`-核による商で `p`-rank は増えない**: `N ⊴ G` with `p ∤ |N|` のとき
`r_p(G/N) ≤ r_p(G)`。商の elementary abelian `p`-部分群 `B` は、その逆像の
Sylow `p`-部分群 `P` と同型 (`p`-元は `p'`-核と交わらない) なので `G` 内で実現される。 -/
theorem pRank_quotient_le_of_coprime {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card ↥N) :
    pRank (G ⧸ N) p ≤ pRank G p := by
  classical
  rw [pRank_le_iff]
  intro B hB
  -- the preimage `H` of `B`
  set H : Subgroup G := B.comap (QuotientGroup.mk' N) with hH_def
  have hNH : N ≤ H := by
    intro x hx
    change QuotientGroup.mk' N x ∈ B
    have hx1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact B.one_mem
  -- the restriction of `mk'` to `H` has range `B` and kernel of card `|N|`
  set g : ↥H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype with hg_def
  have hg_mem : ∀ x : ↥H, g x ∈ B := fun x => x.2
  have hg_ker_card : Nat.card g.ker = Nat.card ↥N := by
    have hker_eq : g.ker = N.subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hg_def]
      exact QuotientGroup.eq_one_iff (x : G)
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  -- |H| = |N| * |B|
  have hH_card : Nat.card ↥H = Nat.card ↥N * Nat.card ↥B := by
    have h1 : Nat.card g.ker * g.ker.index = Nat.card ↥H := Subgroup.card_mul_index g.ker
    have h2 : g.ker.index = Nat.card g.range := by
      calc g.ker.index = Nat.card (↥H ⧸ g.ker) := rfl
        _ = Nat.card g.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
    have h3 : g.range = B := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact hg_mem x
      · intro b hb
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective b
        exact ⟨⟨x, hb⟩, rfl⟩
    rw [← h1, h2, h3, hg_ker_card]
  -- `B` is a `p`-group of order `p ^ m`
  have hB_pg : IsPGroup p ↥B := fun b => ⟨1, by
    rw [pow_one]
    exact hB.pow_eq_one b⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB_pg
  -- a Sylow `p`-subgroup of `H` has order `p ^ m`
  let P : Sylow p ↥H := default
  have hP_card : Nat.card ↥(P : Subgroup ↥H) = p ^ m := by
    rw [P.card_eq_multiplicity, hH_card, hm]
    congr 1
    rw [Nat.factorization_mul Nat.card_pos.ne'
        (pow_pos (Fact.out : p.Prime).pos m).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN,
      Nat.factorization_pow_self (Fact.out : p.Prime)]
    exact Nat.zero_add m
  -- the composite `P → G ⧸ N` is injective into `B`
  set f : ↥(P : Subgroup ↥H) →* G ⧸ N := g.comp (P : Subgroup ↥H).subtype with hf_def
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : ((x : ↥H) : G) ∈ N := (QuotientGroup.eq_one_iff ((x : ↥H) : G)).mp hx
    obtain ⟨k, hk⟩ := P.2 x
    have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf x ∣ Nat.card ↥N := by
      have he1 : orderOf ((x : ↥H) : G) = orderOf x :=
        orderOf_injective (H.subtype.comp (P : Subgroup ↥H).subtype)
          (H.subtype_injective.comp (Subgroup.subtype_injective _)) x
      have he2 : orderOf (N.subtype ⟨((x : ↥H) : G), hxN⟩) =
          orderOf (⟨((x : ↥H) : G), hxN⟩ : ↥N) :=
        orderOf_injective N.subtype N.subtype_injective _
      have he3 : orderOf ((x : ↥H) : G) = orderOf (⟨((x : ↥H) : G), hxN⟩ : ↥N) := he2
      calc orderOf x = orderOf (⟨((x : ↥H) : G), hxN⟩ : ↥N) := by
            rw [← he1]
            exact he3
        _ ∣ Nat.card ↥N := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) (Nat.card ↥N) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN)
    have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.mp h3
  -- realize `B` inside `G`: the image of `P` under the subtype tower
  set E : Subgroup G := ((P : Subgroup ↥H).map H.subtype) with hE_def
  have hE_card : Nat.card ↥E = p ^ m := by
    rw [hE_def, ← hP_card]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv).symm
  -- `E` is elementary abelian: it is isomorphic to a subgroup of `B`
  have hE_elem : E.IsElementaryAbelian p := by
    have hf_mem : ∀ x, f x ∈ B := fun x => hg_mem _
    set f' : ↥(P : Subgroup ↥H) →* ↥B := f.codRestrict B hf_mem with hf'_def
    have hf'_inj : Function.Injective f' := by
      intro x y hxy
      apply hf_inj
      exact congrArg Subtype.val hxy
    have hP_elem : OddOrder.GroupTheory.IsElementaryAbelian p ↥(P : Subgroup ↥H) := by
      have hrange_elem : (f'.range).IsElementaryAbelian p := hB.to_subgroup f'.range
      exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (MonoidHom.ofInjective hf'_inj).symm hrange_elem
    rw [hE_def]
    exact Subgroup.IsElementaryAbelian.map H.subtype_injective hP_elem
  -- conclude
  calc Nat.log p (Nat.card ↥B) = Nat.log p (Nat.card ↥E) := by rw [hm, hE_card]
    _ ≤ pRank G p := le_pRank E hE_elem

/-- **Thm 4.18 core** (`O_{p'}(G) = 1` の場合): `G' ≤ O_p(G)`, `p` 以外の素因子は
`p` 以下, `G/O_p(G)` は `p'`-群。

`R = O_p(G)`, `C = C_G(R)`: Hall–Higman 1.2.3 (= **G** Thm 6.3.2) で `C ≤ R`;
Lemma 4.17 で `(G/C)'` は `p`-群; `C` も `p`-群なので `G'` の引き戻しが normal
`p`-部分群となり `O_p(G)` に入る。素因子評価は Lemma 4.13。 -/
private theorem core418 {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hp : Odd p) (hodd : Odd (Nat.card G)) (hrank : pRank G p ≤ 2)
    (hredu : Ch03.oPiCore {r : ℕ | r ≠ p} G = ⊥) :
    _root_.commutator G ≤ Ch03.oPiCore ({p} : Set ℕ) G ∧
      (∀ q ∈ (Nat.card G).primeFactors, q ≤ p) ∧
      ¬ p ∣ Nat.card (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) := by
  classical
  have hprime : p.Prime := Fact.out
  set R : Subgroup G := Ch03.oPiCore ({p} : Set ℕ) G with hR_def
  haveI hR_normal : R.Normal := by rw [hR_def]; infer_instance
  -- `R` is a `p`-group of rank ≤ 2
  have hR_pg : IsPGroup p ↥R :=
    isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  have hR_rank : pRank ↥R p ≤ 2 :=
    le_trans (pRank_le_of_injective (f := R.subtype) R.subtype_injective) hrank
  -- Hall–Higman 1.2.3: `C := C_G(R) ≤ R`
  have hCR : Subgroup.centralizer (R : Set G) ≤ R := by
    refine Ch03.hall_higman_1_2_3 ({p} : Set ℕ) ?_
    rw [show {q : ℕ | q ∉ ({p} : Set ℕ)} = {r : ℕ | r ≠ p} from compl_singleton_eq]
    exact hredu
  have hC_pg : IsPGroup p ↥(Subgroup.centralizer (R : Set G)) := hR_pg.to_le hCR
  -- the conjugation action of `G` on `R`, with kernel `C`
  set ψ : G →* MulAut ↥R := MulAut.conjNormal with hψ_def
  have hker : ψ.ker = Subgroup.centralizer (R : Set G) := by
    rw [hψ_def]
    exact conjNormal_ker
  have hker_pg : IsPGroup p ↥ψ.ker := by
    rw [hker]
    exact hC_pg
  -- the quotient `G ⧸ ker ψ` acts faithfully; it is odd
  have hquot_dvd : Nat.card (G ⧸ ψ.ker) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card ψ.ker
    simpa [Subgroup.index] using this
  have hquot_odd : Odd (Nat.card (G ⧸ ψ.ker)) := by
    rcases Nat.even_or_odd (Nat.card (G ⧸ ψ.ker)) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  -- Lemma 4.17: `(G ⧸ C)'` is a `p`-group
  have hA' : IsPGroup p (_root_.commutator (G ⧸ ψ.ker)) :=
    isPGroup_commutator_of_mulAut_odd_of_pRank_le_two hp hR_pg hR_rank
      (QuotientGroup.kerLift_injective ψ) hquot_odd
  -- pull back: `G' ≤ W := comap mk' ((G ⧸ C)')`, a normal `p`-subgroup, hence `≤ R`
  have hG'R : _root_.commutator G ≤ R := by
    have hW_pg : IsPGroup p
        ↥((_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker)) := by
      refine IsPGroup.comap_of_ker_isPGroup hA' _ ?_
      rw [QuotientGroup.ker_mk']
      exact hker_pg
    haveI hW_norm :
        ((_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker)).Normal :=
      Subgroup.Normal.comap inferInstance _
    have hW_le_R :
        (_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker) ≤ R :=
      Ch03.Subgroup.IsPiGroup.le_oPiCore (isPiGroup_singleton_of_isPGroup hW_pg)
    refine le_trans ?_ hW_le_R
    have hmap : (_root_.commutator G).map (QuotientGroup.mk' ψ.ker) =
        _root_.commutator (G ⧸ ψ.ker) := by
      rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective ψ.ker)]
    rw [← hmap]
    exact Subgroup.le_comap_map _ _
  refine ⟨hG'R, ?_, ?_⟩
  · -- every prime factor `q ≠ p` of `|G|` satisfies `q < p` (Lemma 4.13)
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq_prime, hq_dvd, -⟩ := hq
    rcases eq_or_ne q p with rfl | hq_ne
    · exact le_rfl
    · have hSCN : ∀ B : Subgroup ↥R, ¬ OddOrder.GroupTheory.IsSCN₃ p B := by
        intro B hB
        have h3 : 3 ≤ pRank ↥B p := hB.le_pRank
        have hle : pRank ↥B p ≤ pRank ↥R p :=
          pRank_le_of_injective (f := B.subtype) B.subtype_injective
        omega
      have hq_dvd_quot : q ∣ Nat.card (G ⧸ ψ.ker) := by
        have hmul : Nat.card ↥ψ.ker * Nat.card (G ⧸ ψ.ker) = Nat.card G := by
          have := Subgroup.card_mul_index ψ.ker
          simpa [Subgroup.index] using this
        rcases (Nat.Prime.dvd_mul hq_prime).mp (hmul ▸ hq_dvd) with h | h
        · exfalso
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker_pg
          rw [hk] at h
          exact hq_ne ((Nat.prime_dvd_prime_iff_eq hq_prime hprime).mp
            (hq_prime.dvd_of_dvd_pow h))
        · exact h
      have hq_dvd_aut : q ∣ Nat.card (MulAut ↥R) := by
        have h1 : Nat.card (G ⧸ ψ.ker) = Nat.card (QuotientGroup.kerLift ψ).range :=
          Nat.card_congr (MonoidHom.ofInjective (QuotientGroup.kerLift_injective ψ)).toEquiv
        rw [h1] at hq_dvd_quot
        exact dvd_trans hq_dvd_quot
          (Subgroup.card_subgroup_dvd_card (QuotientGroup.kerLift ψ).range)
      exact le_of_lt (dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty
        hp hR_pg hSCN hq_prime hq_ne hq_dvd_aut).2
  · -- `G ⧸ R` is a `p'`-group: an order-`p` element of the abelian quotient pulls back
    intro hp_dvd
    have hcomm_quot : ∀ x y : G ⧸ R, x * y = y * x := by
      intro x y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hrw : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [hrw]
      exact hG'R (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (Subgroup.mem_top _))
    obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
    have hx_ne : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx_ord
      exact hprime.one_lt.ne' hx_ord.symm
    have hS_pg : IsPGroup p (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hx_ord, pow_one]
    haveI hS_norm : (Subgroup.zpowers x).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgn : g * n * g⁻¹ = n := by
        rw [hcomm_quot g n]
        group
      rwa [hgn]
    have hP_pg : IsPGroup p
        ↥((Subgroup.zpowers x).comap (QuotientGroup.mk' R)) := by
      refine IsPGroup.comap_of_ker_isPGroup hS_pg _ ?_
      rw [QuotientGroup.ker_mk']
      exact hR_pg
    haveI hP_norm :
        ((Subgroup.zpowers x).comap (QuotientGroup.mk' R)).Normal :=
      Subgroup.Normal.comap hS_norm _
    have hP_le : (Subgroup.zpowers x).comap (QuotientGroup.mk' R) ≤ R :=
      Ch03.Subgroup.IsPiGroup.le_oPiCore (isPiGroup_singleton_of_isPGroup hP_pg)
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective R x
    have ha_mem : a ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' R) := by
      rw [Subgroup.mem_comap, ha]
      exact Subgroup.mem_zpowers x
    have hx_one : x = 1 := by
      rw [← ha]
      exact (QuotientGroup.eq_one_iff a).mpr (hP_le ha_mem)
    exact hx_ne hx_one

omit [Finite G] in
/-- **第三同型 (card 版)**: `|G ⧸ O_{p',p}(G)| = |Ḡ ⧸ O_p(Ḡ)|` (`Ḡ = G/O_{p'}(G)`)。
`hasPLengthOne p G` を `Ḡ`-側の `¬ p ∣ |Ḡ/O_p(Ḡ)|` へ移送する橋 (Thm 4.18 (e) /
Thm 5.6 narrow core で使用)。`O_{p'}(G)` は `oPiPrimePiCore` の内部表現
`{q | q ∉ ({p} : Set ℕ)}` 形で書く。 -/
theorem card_quotient_oPiPrimePiCore {p : ℕ} :
    Nat.card (G ⧸ Ch03.oPiPrimePiCore {p} G) =
      Nat.card ((G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G) ⧸
        Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G)) := by
  classical
  set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
  haveI hN_norm : N.Normal := by rw [hN_def]; infer_instance
  have hOpp : Ch03.oPiPrimePiCore {p} G =
      (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N)).comap (QuotientGroup.mk' N) := by
    rw [Ch03.oPiPrimePiCore]
  haveI hOpp_norm : (Ch03.oPiPrimePiCore {p} G).Normal := inferInstance
  have hN_le_Opp : N ≤ Ch03.oPiPrimePiCore {p} G := by
    rw [hOpp]
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact Subgroup.one_mem _
  have hmap_Opp : (Ch03.oPiPrimePiCore {p} G).map (QuotientGroup.mk' N) =
      Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N) := by
    rw [hOpp]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  haveI : ((Ch03.oPiPrimePiCore {p} G).map (QuotientGroup.mk' N)).Normal := by
    rw [hmap_Opp]
    infer_instance
  have e := QuotientGroup.quotientQuotientEquivQuotient N
    (Ch03.oPiPrimePiCore {p} G) hN_le_Opp
  rw [← Nat.card_congr e.toEquiv, hmap_Opp]

/-- **Thm 4.18 / Thm 5.6 共通 assembly**: `Ḡ = G/O_{p'}(G)` 上の core data
((c)′ `Ḡ' ≤ O_p(Ḡ)`, (a)′ `p` が `|Ḡ|` の最大素因子, (e)′ `Ḡ/O_p(Ḡ)` が `p'`-群) から
結論 5 連 (a)-(e) を組み立てる。Thm 4.18 (`r_p(G) ≤ 2`, core = Lemma 4.17 経由) と
BG §5 Thm 5.6 (`S` narrow, `r(S) ≥ 3` + `p`-length one, core = Thm 5.5 経由;
`S05_NarrowPGroups`) の両分岐がここに合流する。solvability・rank 仮定は不要。 -/
theorem structure_of_quotient_commutator_le_opCore
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime]
    (hG'bar : _root_.commutator (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G) ≤
      Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G))
    (hlargest : ∀ q ∈ (Nat.card
      (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G)).primeFactors, q ≤ p)
    (hp'quot : ¬ p ∣ Nat.card ((G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G) ⧸
      Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G))) :
    (∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p) ∧
    ((p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) →
      Ch05.HasNormalPComplement p G) ∧
    Ch05.HasNormalPComplement p ↥(_root_.commutator G) ∧
    (∀ K : Subgroup ↥(_root_.commutator G), Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(_root_.commutator G)) ∧
    ((∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x) ∧ hasPLengthOne p G) := by
  classical
  have hprime : p.Prime := Fact.out
  -- the `p'`-residual quotient `Ḡ = G ⧸ N` (`oPiPrimePiCore` の内部表現の集合形を使う)
  set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
  haveI hN_norm : N.Normal := by rw [hN_def]; infer_instance
  have hN_p' : ¬ p ∣ Nat.card ↥N :=
    not_dvd_card_oPiCore (by simp)
  -- the two forms of `O_{p'}(G)` agree
  have hN_eq : Ch03.oPiCore {r : ℕ | r ≠ p} G = N := by
    rw [hN_def, compl_singleton_eq]
  have hquot_dvd_G : Nat.card (G ⧸ N) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card N
    simpa [Subgroup.index] using this
  -- `O_{p',p}(G)` is the preimage of `R̄ = O_p(Ḡ)` (definitional with this `N`)
  have hOpp : Ch03.oPiPrimePiCore {p} G =
      (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N)).comap (QuotientGroup.mk' N) := by
    rw [Ch03.oPiPrimePiCore]
  haveI hOpp_norm : (Ch03.oPiPrimePiCore {p} G).Normal := inferInstance
  -- `G' ≤ O_{p',p}(G)`
  have hmap_comm : (_root_.commutator G).map (QuotientGroup.mk' N) =
      _root_.commutator (G ⧸ N) := by
    rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hG'_le : _root_.commutator G ≤ Ch03.oPiPrimePiCore {p} G := by
    rw [hOpp]
    intro x hx
    rw [Subgroup.mem_comap]
    have hmem : (QuotientGroup.mk' N) x ∈
        (_root_.commutator G).map (QuotientGroup.mk' N) := ⟨x, hx, rfl⟩
    rw [hmap_comm] at hmem
    exact hG'bar hmem
  -- (e)
  have he_comm : ∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hrw : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hrw]
    exact hG'_le (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _))
  have he_pl : hasPLengthOne p G := by
    rw [hasPLengthOne, card_quotient_oPiPrimePiCore (G := G) (p := p)]
    exact hp'quot
  -- (a)
  have ha : ∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p := by
    have hcards : Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G) = Nat.card (G ⧸ N) := by
      rw [hN_eq]
    rw [hcards]
    exact hlargest
  -- (c): the normal `p`-complement `N'' = N ∩ G'` of `G'`
  set N'' : Subgroup ↥(_root_.commutator G) :=
    N.subgroupOf (_root_.commutator G) with hN''_def
  haveI hN''_norm : N''.Normal := by
    rw [hN''_def]
    exact hN_norm.subgroupOf _
  have hN''_card_dvd : Nat.card ↥N'' ∣ Nat.card ↥N := by
    have h1 : Nat.card ↥N'' = Nat.card ↥(N ⊓ _root_.commutator G) := by
      rw [hN''_def]
      have h2 := Subgroup.subgroupOf_map_subtype N (_root_.commutator G)
      calc Nat.card ↥(N.subgroupOf (_root_.commutator G))
          = Nat.card ↥((N.subgroupOf (_root_.commutator G)).map
              (_root_.commutator G).subtype) :=
            Nat.card_congr (Subgroup.equivMapOfInjective _ _
              (_root_.commutator G).subtype_injective).toEquiv
        _ = Nat.card ↥(N ⊓ _root_.commutator G) := by rw [h2]
    rw [h1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hN''_p' : ¬ p ∣ Nat.card ↥N'' := fun h => hN_p' (dvd_trans h hN''_card_dvd)
  -- the index of `N''` in `G'` is a power of `p`
  set g'' : ↥(_root_.commutator G) →* (G ⧸ N) :=
    (QuotientGroup.mk' N).comp (_root_.commutator G).subtype with hg''_def
  have hker'' : g''.ker = N'' := by
    ext x
    rw [MonoidHom.mem_ker, hN''_def, Subgroup.mem_subgroupOf, hg''_def]
    exact QuotientGroup.eq_one_iff (x : G)
  have hrange_pg : IsPGroup p ↥g''.range := by
    have hrange_le : g''.range ≤ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N) := by
      rintro _ ⟨x, rfl⟩
      refine hG'bar ?_
      have hmem : (g'' x : G ⧸ N) ∈ (_root_.commutator G).map (QuotientGroup.mk' N) :=
        ⟨(x : G), x.2, rfl⟩
      rwa [hmap_comm] at hmem
    exact (isPGroup_of_isPiGroup_singleton
      (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))).to_le hrange_le
  have hidx_eq : N''.index = Nat.card g''.range := by
    rw [← hker'']
    calc g''.ker.index = Nat.card (↥(_root_.commutator G) ⧸ g''.ker) := rfl
      _ = Nat.card g''.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g'').toEquiv
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hrange_pg
  have hj_idx : N''.index = p ^ j := by rw [hidx_eq, hj]
  have hc : Ch05.HasNormalPComplement p ↥(_root_.commutator G) := by
    refine ⟨N'', hN''_norm, ?_⟩
    intro P
    have hP_card : Nat.card ↥(P : Subgroup ↥(_root_.commutator G)) = p ^ j := by
      rw [P.card_eq_multiplicity]
      congr 1
      have h1 : Nat.card ↥N'' * N''.index = Nat.card ↥(_root_.commutator G) :=
        Subgroup.card_mul_index N''
      rw [← h1, hj_idx,
        Nat.factorization_mul Nat.card_pos.ne' (pow_pos hprime.pos j).ne',
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hN''_p',
        Nat.factorization_pow_self hprime]
      exact Nat.zero_add j
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hP_card, ← hj_idx]
      exact Subgroup.card_mul_index N''
    · rw [hP_card]
      exact Nat.Coprime.pow_right j
        ((hprime.coprime_iff_not_dvd.mpr hN''_p').symm)
  -- (d): a `p'`-subgroup of `G'` lies in `N'' ≤ O_{p'}(G')`
  have hd : ∀ K : Subgroup ↥(_root_.commutator G),
      Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(_root_.commutator G) := by
    intro K hK
    have hK_p' : ¬ p ∣ Nat.card ↥K := by
      intro h
      exact (hK p (Nat.mem_primeFactors.mpr ⟨hprime, h, Nat.card_pos.ne'⟩)) rfl
    have hK_le_N'' : K ≤ N'' := by
      intro k hk
      rw [← hker'', MonoidHom.mem_ker]
      have h1 : orderOf (g'' k) ∣ Nat.card ↥K := by
        have h2 : orderOf (g'' k) ∣ orderOf k := orderOf_map_dvd g'' k
        have h3 : orderOf k ∣ Nat.card ↥K := by
          have h4 : orderOf (K.subtype ⟨k, hk⟩) = orderOf (⟨k, hk⟩ : ↥K) :=
            orderOf_injective K.subtype K.subtype_injective _
          have h4' : orderOf k = orderOf (⟨k, hk⟩ : ↥K) := h4
          rw [h4']
          exact orderOf_dvd_natCard _
        exact dvd_trans h2 h3
      have h5 : orderOf (g'' k) ∣ p ^ j := by
        have h6 : g'' k ∈ g''.range := ⟨k, rfl⟩
        have h7 : orderOf (g''.range.subtype ⟨g'' k, h6⟩) =
            orderOf (⟨g'' k, h6⟩ : ↥g''.range) :=
          orderOf_injective g''.range.subtype g''.range.subtype_injective _
        have h7' : orderOf (g'' k) = orderOf (⟨g'' k, h6⟩ : ↥g''.range) := h7
        rw [h7', ← hj]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (Nat.card ↥K) (p ^ j) :=
        Nat.Coprime.pow_right j ((hprime.coprime_iff_not_dvd.mpr hK_p').symm)
      have h8 : orderOf (g'' k) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop h1 h5
      exact orderOf_eq_one_iff.mp h8
    refine le_trans hK_le_N'' ?_
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    intro hq_eq
    rw [hq_eq] at hq
    exact hN''_p' hq.2.1
  -- (b): when `p` is forced to be the only prime of `Ḡ`, the core `N` is a complement
  have hb : (p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) →
      Ch05.HasNormalPComplement p G := by
    intro hcase
    have hall_p : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card (G ⧸ N) → q = p := by
      intro q hq hq_dvd
      have h1 : q ≤ p := hlargest q
        (Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, Nat.card_pos.ne'⟩)
      have hq_dvd_G : q ∣ Nat.card G := dvd_trans hq_dvd hquot_dvd_G
      have h2 : q ≠ 2 := by
        intro h2
        rw [h2] at hq_dvd_G
        rw [Nat.odd_iff] at hodd
        omega
      rcases hcase with rfl | hmin
      · have := hq.two_le
        omega
      · have h3 := hmin q (Nat.mem_primeFactors.mpr ⟨hq, hq_dvd_G, Nat.card_pos.ne'⟩)
        omega
    have hk := Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_pos (α := G ⧸ N)).ne' hall_p
    refine ⟨N, hN_norm, ?_⟩
    intro P
    have hP_card : Nat.card ↥(P : Subgroup G) =
        p ^ (Nat.card (G ⧸ N)).primeFactorsList.length := by
      rw [P.card_eq_multiplicity]
      congr 1
      have h1 : Nat.card ↥N * Nat.card (G ⧸ N) = Nat.card G := by
        have := Subgroup.card_mul_index N
        simpa [Subgroup.index] using this
      have hfact : (Nat.card (G ⧸ N)).factorization p =
          (Nat.card (G ⧸ N)).primeFactorsList.length := by
        conv_lhs => rw [hk]
        exact Nat.factorization_pow_self hprime
      rw [← h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN_p', hfact]
      exact Nat.zero_add _
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hP_card, ← hk]
      have := Subgroup.card_mul_index N
      simpa [Subgroup.index] using this
    · rw [hP_card]
      exact Nat.Coprime.pow_right _
        ((hprime.coprime_iff_not_dvd.mpr hN_p').symm)
  exact ⟨ha, hb, hc, hd, he_comm, he_pl⟩

/-- **BG Theorem 4.18** (mmd L1734-1752): `G` solvable odd, `p ∣ |G|`, `r_p(G) ≤ 2`。
すると:

* (a) `p` は `|G/O_{p'}(G)|` の最大素因子;
* (b) `p = 3` または `p` が `|G|` の最小素因子なら、`G` は normal `p`-complement を持つ;
* (c) `G'` は normal `p`-complement を持つ;
* (d) `G'` の任意の `p'`-subgroup は `O_{p'}(G')` に含まれる;
* (e) `G/O_{p',p}(G)` は abelian `p'`-群。

結論の語彙は §5 Thm 5.6 (`narrow_sylow_solvable_structure`) と一致させている。
証明 = `core418` (`O_{p'} = 1` の場合; Hall–Higman + Lemma 4.17 + Lemma 4.13) を
商 `Ḡ = G/O_{p'}(G)` に適用し、`structure_of_quotient_commutator_le_opCore` で引き戻す。 -/
theorem solvable_structure_of_pRank_le_two [IsSolvable G]
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (hrank : pRank G p ≤ 2) :
    (∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p) ∧
    ((p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) →
      Ch05.HasNormalPComplement p G) ∧
    Ch05.HasNormalPComplement p ↥(_root_.commutator G) ∧
    (∀ K : Subgroup ↥(_root_.commutator G), Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(_root_.commutator G)) ∧
    ((∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x) ∧ hasPLengthOne p G) := by
  classical
  have hp_odd : Odd p := by
    rcases Nat.even_or_odd p with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hp_mem
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  -- the `p'`-residual quotient `Ḡ = G ⧸ N`
  set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
  haveI hN_norm : N.Normal := by rw [hN_def]; infer_instance
  have hN_p' : ¬ p ∣ Nat.card ↥N :=
    not_dvd_card_oPiCore (by simp)
  have hquot_dvd_G : Nat.card (G ⧸ N) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card N
    simpa [Subgroup.index] using this
  have hodd_bar : Odd (Nat.card (G ⧸ N)) := by
    rcases Nat.even_or_odd (Nat.card (G ⧸ N)) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd_G
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  have hrank_bar : pRank (G ⧸ N) p ≤ 2 :=
    le_trans (pRank_quotient_le_of_coprime hN_p') hrank
  have hredu_bar : Ch03.oPiCore {r : ℕ | r ≠ p} (G ⧸ N) = ⊥ := by
    rw [show {r : ℕ | r ≠ p} = {q : ℕ | q ∉ ({p} : Set ℕ)} from compl_singleton_eq.symm]
    exact Ch03.oPiCore_quotient_self_eq_bot _
  obtain ⟨hG'bar, hlargest, hp'quot⟩ := core418 hp_odd hodd_bar hrank_bar hredu_bar
  exact structure_of_quotient_commutator_le_opCore hodd hG'bar hlargest hp'quot

/-- If `K` is normal in `G`, then `F(K)` has rank at most `F(G)`.

This is the rank form of the BG Theorem 4.20(c) induction line `F(K) <= F(G)`. -/
theorem rank_fitting_le_of_normal_subgroup {K : Subgroup G} [K.Normal] :
    OddOrder.GroupTheory.rank ↥(Ch01.fitting ↥K) ≤
      OddOrder.GroupTheory.rank ↥(Ch01.fitting G) := by
  classical
  let f : ↥(Ch01.fitting ↥K) →* ↥(Ch01.fitting G) :=
    { toFun := fun x =>
        ⟨(x.1 : G),
          Ch01.fitting_map_subtype_le_fitting (M := K) ⟨x.1, x.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro _ _
        apply Subtype.ext
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Ch01.fitting G) => (z : G)) hxy
  exact OddOrder.GroupTheory.rank_le_of_injective (G := ↥(Ch01.fitting G)) hf

/-- If `K` is normal in `G` and `F(G)` has rank at most two, then so does `F(K)`. -/
theorem rank_fitting_le_two_of_normal_subgroup {K : Subgroup G} [K.Normal]
    (hrF : OddOrder.GroupTheory.rank ↥(Ch01.fitting G) ≤ 2) :
    OddOrder.GroupTheory.rank ↥(Ch01.fitting ↥K) ≤ 2 :=
  (rank_fitting_le_of_normal_subgroup (G := G) (K := K)).trans hrF

/-- The BG Theorem 4.20(c) induction hypothesis is inherited by a normal subgroup:
either the whole-group rank bound restricts to the subgroup, or the Fitting-rank
bound restricts via `F(K) <= F(G)`. -/
theorem rank_or_rank_fitting_le_two_of_normal_subgroup {K : Subgroup G} [K.Normal]
    (h : OddOrder.GroupTheory.rank G ≤ 2 ∨
      OddOrder.GroupTheory.rank ↥(Ch01.fitting G) ≤ 2) :
    OddOrder.GroupTheory.rank ↥K ≤ 2 ∨
      OddOrder.GroupTheory.rank ↥(Ch01.fitting ↥K) ≤ 2 := by
  rcases h with hG | hF
  · exact Or.inl ((OddOrder.GroupTheory.rank_mono_of_le K).trans hG)
  · exact Or.inr (rank_fitting_le_two_of_normal_subgroup (G := G) (K := K) hF)

/-- If a Sylow `p`-subgroup lies in `F(G)`, then its `p`-rank is bounded by the
rank of `F(G)`. -/
theorem pRank_sylow_le_two_of_le_fitting {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hPfit : (P : Subgroup G) ≤ Ch01.fitting G)
    (hrF : OddOrder.GroupTheory.rank ↥(Ch01.fitting G) ≤ 2) :
    pRank ↥(P : Subgroup G) p ≤ 2 := by
  have hP_le_F : pRank ↥(P : Subgroup G) p ≤ pRank ↥(Ch01.fitting G) p :=
    OddOrder.GroupTheory.pRank_le_of_injective
      (G := ↥(Ch01.fitting G)) (H := ↥(P : Subgroup G))
      (f := Subgroup.inclusion hPfit) (Subgroup.inclusion_injective hPfit)
  exact hP_le_F.trans ((OddOrder.GroupTheory.rank_le_iff.mp hrF) p (Fact.out : p.Prime))

/-- If some Sylow `p`-subgroup lies in `F(G)` and `F(G)` has rank at most two, then
`r_p(G) ≤ 2`. -/
theorem pRank_le_two_of_sylow_le_fitting {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hPfit : (P : Subgroup G) ≤ Ch01.fitting G)
    (hrF : OddOrder.GroupTheory.rank ↥(Ch01.fitting G) ≤ 2) :
    pRank G p ≤ 2 :=
  (OddOrder.GroupTheory.pRank_le_pRank_sylow P).trans
    (pRank_sylow_le_two_of_le_fitting P hPfit hrF)

/-- A normal `p`-complement is the canonical `{r | r != p}`-core.

This is the bridge needed in BG Thm 4.20(c): once Thm 4.18(b) produces a normal
`p`-complement, the complement can be taken to be the characteristic subgroup
`O_{r | r != p}(G)`. -/
theorem normalPComplement_eq_oPiCore_compl {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    [K.Normal] (hK : ∀ P : Sylow p G, Subgroup.IsComplement' K (P : Subgroup G)) :
    K = Ch03.oPiCore {r : ℕ | r ≠ p} G := by
  classical
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hKP := hK P
  have hK_pi : Ch03.Subgroup.IsPiGroup {r : ℕ | r ≠ p} K := by
    intro q hq hq_eq
    have hq_dvd_K : q ∣ Nat.card ↥K := Nat.dvd_of_mem_primeFactors hq
    have hp_dvd_index : p ∣ (P : Subgroup G).index := by
      rw [hKP.index_eq_card, ← hq_eq]
      exact hq_dvd_K
    exact P.not_dvd_index hp_dvd_index
  have hK_le : K ≤ Ch03.oPiCore {r : ℕ | r ≠ p} G :=
    Ch03.Subgroup.IsPiGroup.le_oPiCore hK_pi
  have hK_hall : Ch03.IsHallSubgroup {r : ℕ | r ≠ p} K := by
    refine ⟨hK_pi, ?_⟩
    intro q hq hq_ne_p
    have hidx : K.index = Nat.card ↥(P : Subgroup G) := hKP.symm.index_eq_card
    have hqP : q ∈ (Nat.card ↥(P : Subgroup G)).primeFactors := by
      simpa [hidx] using hq
    have hPp : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    rw [hk, Nat.mem_primeFactors] at hqP
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq hqP.1 (Fact.out : p.Prime)).mp
        (hqP.1.dvd_of_dvd_pow hqP.2.1)
    exact hq_ne_p hq_eq_p
  have hO_le : Ch03.oPiCore {r : ℕ | r ≠ p} G ≤ K :=
    Ch03.Subgroup.IsPiGroup.normal_le_hall
      (Ch03.oPiCore.isPiGroup {r : ℕ | r ≠ p}) hK_hall
  exact le_antisymm hK_le hO_le

/-- If `G` has a normal `p`-complement, then the canonical core is such a complement. -/
theorem oPiCore_isComplement_of_hasNormalPComplement {p : ℕ} [Fact p.Prime]
    (hG : Ch05.HasNormalPComplement p G) (P : Sylow p G) :
    Subgroup.IsComplement' (Ch03.oPiCore {r : ℕ | r ≠ p} G) (P : Subgroup G) := by
  rcases hG with ⟨K, hK_normal, hK_compl⟩
  haveI : K.Normal := hK_normal
  have hK_eq : K = Ch03.oPiCore {r : ℕ | r ≠ p} G :=
    normalPComplement_eq_oPiCore_compl (K := K) hK_compl
  rw [← hK_eq]
  exact hK_compl P

/-- The quotient by the canonical normal `p`-complement is isomorphic to any Sylow
`p`-subgroup. -/
noncomputable def quotient_oPiCore_mulEquiv_sylow_of_hasNormalPComplement {p : ℕ}
    [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) (P : Sylow p G) :
    G ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} G ≃* (P : Subgroup G) :=
  (oPiCore_isComplement_of_hasNormalPComplement hG P).symm.QuotientMulEquiv

/-- If `G` has a normal `p`-complement, then quotienting by the canonical complement
leaves a `p`-group. -/
theorem isPGroup_quotient_oPiCore_of_hasNormalPComplement {p : ℕ} [Fact p.Prime]
    (hG : Ch05.HasNormalPComplement p G) :
    IsPGroup p (G ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} G) := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  exact P.isPGroup'.of_equiv
    (quotient_oPiCore_mulEquiv_sylow_of_hasNormalPComplement hG P).symm

/-- The canonical normal `p`-complement quotient has the same cardinality as a Sylow
`p`-subgroup. -/
theorem card_quotient_oPiCore_eq_card_sylow_of_hasNormalPComplement {p : ℕ}
    [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) (P : Sylow p G) :
    Nat.card (G ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} G) = Nat.card ↥(P : Subgroup G) := by
  exact Nat.card_congr
    (quotient_oPiCore_mulEquiv_sylow_of_hasNormalPComplement hG P).toEquiv

/-- A normal `p`-free subgroup whose quotient is a `p`-group is a normal
`p`-complement.

This is the ambient lift used after applying BG Thm 4.20(c) inside a normal subgroup:
once the candidate kernel is normal in `G`, the remaining work is only to identify the
quotient as a `p`-group. -/
theorem hasNormalPComplement_of_normal_pPrime_of_quotient_isPGroup {p : ℕ}
    [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hNpPrime : ¬ p ∣ Nat.card ↥N) (hquot : IsPGroup p (G ⧸ N)) :
    Ch05.HasNormalPComplement p G := by
  classical
  obtain ⟨a, hquot_card⟩ := IsPGroup.iff_card.mp hquot
  have hquot_index : N.index = p ^ a := by
    rw [Subgroup.index_eq_card]
    exact hquot_card
  refine ⟨N, inferInstance, fun P => ?_⟩
  have h_fact_a : (Nat.card G).factorization p = a := by
    have hN_card_mul : Nat.card ↥N * N.index = Nat.card G :=
      Subgroup.card_mul_index N
    have h_total : Nat.card G = Nat.card ↥N * p ^ a := by
      rw [← hN_card_mul, hquot_index]
    have hN_card_ne : Nat.card ↥N ≠ 0 := ne_of_gt Nat.card_pos
    have hpa_ne : p ^ a ≠ 0 := ne_of_gt (pow_pos (Fact.out : p.Prime).pos a)
    rw [h_total, Nat.factorization_mul hN_card_ne hpa_ne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hNpPrime,
      Nat.factorization_pow_self (Fact.out : p.Prime), zero_add]
  have hP_card : Nat.card ↥(P : Subgroup G) = p ^ a := by
    rw [P.card_eq_multiplicity, h_fact_a]
  have h_card_mul : Nat.card ↥N * Nat.card ↥(P : Subgroup G) = Nat.card G := by
    rw [hP_card, ← hquot_index]
    exact Subgroup.card_mul_index N
  have h_coprime : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(P : Subgroup G)) := by
    rw [hP_card]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hNpPrime).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_card_mul h_coprime

/-- Characteristic subgroup variant of
`hasNormalPComplement_of_normal_pPrime_of_quotient_isPGroup`.

If `K char H` and `H ⊴ G`, then the image of `K` in `G` is normal, so a `p`-group
quotient by that image gives a normal `p`-complement in `G`. -/
theorem hasNormalPComplement_of_characteristic_subgroup_quotient_isPGroup {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} [H.Normal] {K : Subgroup H}
    (hK_char : K.Characteristic) (hKpPrime : ¬ p ∣ Nat.card ↥K)
    (hquot : IsPGroup p (G ⧸ K.map H.subtype)) :
    Ch05.HasNormalPComplement p G := by
  classical
  haveI : K.Characteristic := hK_char
  haveI : (K.map H.subtype).Normal := inferInstance
  refine hasNormalPComplement_of_normal_pPrime_of_quotient_isPGroup
    (N := K.map H.subtype) ?_ hquot
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact hKpPrime

/-- The canonical `O_{r | r != p}` specialization of the characteristic subgroup lift. -/
theorem hasNormalPComplement_of_oPiCore_quotient_isPGroup {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} [H.Normal]
    (hquot :
      IsPGroup p (G ⧸ (Ch03.oPiCore {r : ℕ | r ≠ p} ↥H).map H.subtype)) :
    Ch05.HasNormalPComplement p G :=
  hasNormalPComplement_of_characteristic_subgroup_quotient_isPGroup
    (H := H) (K := Ch03.oPiCore {r : ℕ | r ≠ p} ↥H)
    (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} ↥H)
    (not_dvd_card_oPiCore (G := ↥H) (p := p) (π := {r : ℕ | r ≠ p}) (by simp))
    hquot

/-- If both quotient layers `H/K` and `G/H` are `p`-groups, then the ambient quotient by
the image of `K` is a `p`-group. -/
theorem isPGroup_quotient_map_subtype_of_isPGroup_quotient_of_isPGroup_quotient {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} [H.Normal] {K : Subgroup H}
    [K.Normal] [(K.map H.subtype).Normal]
    (hHK : IsPGroup p (↥H ⧸ K)) (hGH : IsPGroup p (G ⧸ H)) :
    IsPGroup p (G ⧸ K.map H.subtype) := by
  classical
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hHK
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hGH
  refine IsPGroup.of_card (n := a + b) ?_
  rw [← Subgroup.index_eq_card, Subgroup.index_map_subtype,
    Subgroup.index_eq_card, Subgroup.index_eq_card, ha, hb, ← pow_add]

/-- Characteristic-subgroup version of the quotient-extension bridge for normal
`p`-complements. -/
theorem hasNormalPComplement_of_characteristic_subgroup_quotient_and_outer_quotient_isPGroup
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} [H.Normal] {K : Subgroup H}
    [K.Normal] (hK_char : K.Characteristic) (hKpPrime : ¬ p ∣ Nat.card ↥K)
    (hHK : IsPGroup p (↥H ⧸ K)) (hGH : IsPGroup p (G ⧸ H)) :
    Ch05.HasNormalPComplement p G := by
  classical
  haveI : K.Characteristic := hK_char
  haveI : (K.map H.subtype).Normal := inferInstance
  exact hasNormalPComplement_of_characteristic_subgroup_quotient_isPGroup
    (H := H) (K := K) hK_char hKpPrime
    (isPGroup_quotient_map_subtype_of_isPGroup_quotient_of_isPGroup_quotient
      (p := p) (H := H) (K := K) hHK hGH)

/-- The `O_{r | r != p}` version of the quotient-extension bridge. -/
theorem hasNormalPComplement_of_oPiCore_quotient_and_outer_quotient_isPGroup {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} [H.Normal]
    (hlocal : IsPGroup p (↥H ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} ↥H))
    (houter : IsPGroup p (G ⧸ H)) :
    Ch05.HasNormalPComplement p G :=
  hasNormalPComplement_of_characteristic_subgroup_quotient_and_outer_quotient_isPGroup
    (H := H) (K := Ch03.oPiCore {r : ℕ | r ≠ p} ↥H)
    (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} ↥H)
    (not_dvd_card_oPiCore (G := ↥H) (p := p) (π := {r : ℕ | r ≠ p}) (by simp))
    hlocal houter

/-- If a normal subgroup has a normal `p`-complement and the outer quotient is a
`p`-group, then the ambient group has a normal `p`-complement. -/
theorem hasNormalPComplement_of_normal_subgroup_hasNormalPComplement_of_quotient_isPGroup
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} [H.Normal]
    (hH : Ch05.HasNormalPComplement p ↥H) (houter : IsPGroup p (G ⧸ H)) :
    Ch05.HasNormalPComplement p G :=
  hasNormalPComplement_of_oPiCore_quotient_and_outer_quotient_isPGroup
    (H := H) (isPGroup_quotient_oPiCore_of_hasNormalPComplement hH) houter

/-- The canonical normal `p`-complement preserves the `q`-part of the group order
for `q != p`. -/
theorem factorization_card_oPiCore_eq_factorization_card_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G) :
    (Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).factorization q =
      (Nat.card G).factorization q := by
  classical
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hcomp : Subgroup.IsComplement' (Ch03.oPiCore {r : ℕ | r ≠ p} G)
      (P : Subgroup G) := oPiCore_isComplement_of_hasNormalPComplement hG P
  have hmul : Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G) *
      Nat.card ↥(P : Subgroup G) = Nat.card G := hcomp.card_mul
  have hP_q_zero : (Nat.card ↥(P : Subgroup G)).factorization q = 0 := by
    rw [P.card_eq_multiplicity]
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    intro hq_dvd
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp
        ((Fact.out : q.Prime).dvd_of_dvd_pow hq_dvd)
    exact hpq hq_eq_p
  have hfact : (Nat.card G).factorization q =
      (Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).factorization q := by
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, hP_q_zero, add_zero]
  exact hfact.symm

/-- For primes `q != p`, membership in the prime divisors of the canonical normal
`p`-complement is equivalent to membership in the prime divisors of the ambient group. -/
theorem mem_primeFactors_oPiCore_iff_mem_primeFactors_card_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G) :
    q ∈ (Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).primeFactors ↔
      q ∈ (Nat.card G).primeFactors := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  constructor
  · intro hqO
    exact Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card O) Nat.card_pos.ne' hqO
  · intro hqG
    have hfact :
        (Nat.card ↥O).factorization q = (Nat.card G).factorization q := by
      simpa [O] using
        factorization_card_oPiCore_eq_factorization_card_of_hasNormalPComplement_ne
          (G := G) hpq hG
    rw [← Nat.support_factorization] at hqG ⊢
    exact Finsupp.mem_support_iff.mpr (by
      rw [hfact]
      exact Finsupp.mem_support_iff.mp hqG)

/-- If `q` is a largest prime divisor of `G` and `q != p`, then it is also a
largest prime divisor of the canonical normal `p`-complement. -/
theorem largest_primeFactor_oPiCore_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (hqG : q ∈ (Nat.card G).primeFactors)
    (hlargest : ∀ r ∈ (Nat.card G).primeFactors, r ≤ q) :
    q ∈ (Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).primeFactors ∧
      ∀ r ∈ (Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).primeFactors, r ≤ q := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  refine ⟨?_, ?_⟩
  · exact
      (mem_primeFactors_oPiCore_iff_mem_primeFactors_card_of_hasNormalPComplement_ne
        (G := G) hpq hG).2 hqG
  · intro r hrO
    exact hlargest r (Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card O)
      Nat.card_pos.ne' (by simpa [O] using hrO))

/-- The canonical normal `p`-complement preserves the Sylow cardinalities for primes
`q != p`. -/
theorem card_sylow_oPiCore_eq_card_sylow_of_hasNormalPComplement_ne {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (QK : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) (QG : Sylow q G) :
    Nat.card ↥(QK : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) =
      Nat.card ↥(QG : Subgroup G) := by
  classical
  have hfact :=
    factorization_card_oPiCore_eq_factorization_card_of_hasNormalPComplement_ne
      (G := G) hpq hG
  rw [QK.card_eq_multiplicity, QG.card_eq_multiplicity]
  exact congrArg (fun n => q ^ n) hfact


/-- If the canonical normal `p`-complement has a characteristic subgroup with
the `q`-Sylow cardinality, then so does the ambient group, for `q != p`.

This is the characteristic-subgroup lift needed in BG Theorem 4.20(c) after
Theorem 4.18(b) replaces `H` by the canonical `O_{p-prime}(H)`. -/
theorem exists_characteristic_subgroup_card_sylow_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (hK :
      ∃ L : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G),
        L.Characteristic ∧
          Nat.card ↥L =
            Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
              Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))) :
    ∃ L : Subgroup G,
      L.Characteristic ∧ Nat.card ↥L = Nat.card ↥((default : Sylow q G) : Subgroup G) := by
  classical
  obtain ⟨L, hL_char, hL_card⟩ := hK
  refine ⟨L.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype, ?_, ?_⟩
  · exact OddOrder.GroupTheory.characteristic_map_subtype_of_characteristic
      (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} G) hL_char
  · calc
      Nat.card ↥(L.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype) = Nat.card ↥L := by
        exact Subgroup.card_map_of_injective
          (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype_injective
      _ =
          Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
            Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) := hL_card
      _ = Nat.card ↥((default : Sylow q G) : Subgroup G) :=
        card_sylow_oPiCore_eq_card_sylow_of_hasNormalPComplement_ne hpq hG
          (default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
          (default : Sylow q G)

/-- A characteristic subgroup with Sylow `q`-cardinality supplies a normal Sylow
`q`-subgroup.  This is the packaged extraction form used after BG Theorem 4.20(c)
has produced the last characteristic layer. -/
theorem exists_normal_sylow_of_exists_characteristic_subgroup_card_sylow
    {q : ℕ} [Fact q.Prime]
    (hK :
      ∃ L : Subgroup G,
        L.Characteristic ∧ Nat.card ↥L = Nat.card ↥((default : Sylow q G) : Subgroup G)) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  obtain ⟨L, hL_char, hL_card⟩ := hK
  exact Ch01.exists_normal_sylow_of_characteristic_card_eq_sylow hL_char
    (default : Sylow q G) hL_card

/-- If a characteristic subgroup has a bottom quotient with Sylow `q`-cardinality,
then it supplies a normal Sylow `q`-subgroup. -/
theorem exists_normal_sylow_of_characteristic_quotient_bot_card_eq_sylow
    {q : ℕ} [Fact q.Prime] {A : Subgroup G} (hA_char : A.Characteristic)
    (hcard :
      Nat.card (A ⧸ ((⊥ : Subgroup G).subgroupOf A)) =
        Nat.card ↥((default : Sylow q G) : Subgroup G)) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  exact exists_normal_sylow_of_exists_characteristic_subgroup_card_sylow
    ⟨A, hA_char,
      (Subgroup.nat_card_quotient_bot_subgroupOf_eq (H := A)).symm.trans hcard⟩

/-- If the canonical normal `p`-complement has a characteristic subgroup with
the `q`-Sylow cardinality, then the ambient group has a normal Sylow `q`-subgroup,
for `q != p`.

This is the normal-Sylow extraction form of the BG Theorem 4.20(c) induction lift. -/
theorem exists_normal_sylow_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (hK :
      ∃ L : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G),
        L.Characteristic ∧
          Nat.card ↥L =
            Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
              Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal :=
  exists_normal_sylow_of_exists_characteristic_subgroup_card_sylow
    (exists_characteristic_subgroup_card_sylow_of_hasNormalPComplement_ne hpq hG hK)

/-- If the canonical normal `p`-complement already has a normal Sylow
`q`-subgroup, then the ambient group has one, for `q != p`.

This is the induction-consumption form used in BG Theorem 4.20(c): the normal
Sylow in the complement is identified with `O_q` there, hence gives the
characteristic subgroup required by `exists_normal_sylow_of_hasNormalPComplement_ne`. -/
theorem exists_normal_sylow_of_hasNormalPComplement_ne_of_complement_normal_sylow
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (hK :
      ∃ QK : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G),
        (QK : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).Normal) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  obtain ⟨QK, hQK_norm⟩ := hK
  have hQK_eq : (QK : Subgroup O) = Ch01.opCore q O :=
    Ch01.Sylow.eq_opCore_of_normal QK hQK_norm
  refine exists_normal_sylow_of_hasNormalPComplement_ne hpq hG ?_
  refine ⟨Ch01.opCore q O, ?_, ?_⟩
  · exact Ch01.opCore.characteristic q O
  · calc
      Nat.card ↥(Ch01.opCore q O) = Nat.card ↥(QK : Subgroup O) := by
        rw [← hQK_eq]
      _ = Nat.card ↥((default : Sylow q O) : Subgroup O) := by
        rw [QK.card_eq_multiplicity, (default : Sylow q O).card_eq_multiplicity]

/-- Bottom-quotient version of `exists_normal_sylow_of_hasNormalPComplement_ne`,
matching the final layer of the characteristic series in BG Theorem 4.20(c). -/
theorem exists_normal_sylow_of_hasNormalPComplement_ne_of_characteristic_quotient_bot
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    {A : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)}
    (hA_char : A.Characteristic)
    (hcard :
      Nat.card (A ⧸
          ((⊥ : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).subgroupOf A)) =
        Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
          Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  exact exists_normal_sylow_of_hasNormalPComplement_ne hpq hG
    ⟨A, hA_char,
      (Subgroup.nat_card_quotient_bot_subgroupOf_eq (H := A)).symm.trans hcard⟩

/-- If a quotient layer inside the canonical normal `p`-complement has the
`q`-Sylow cardinality, then mapping the layer into the ambient group preserves
characteristic endpoints and the `q`-Sylow cardinality, for `q != p`.

This is the quotient-layer version of the BG Theorem 4.20(c) induction lift. -/
theorem characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    {A B : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)}
    (hBA : B ≤ A) (hA_char : A.Characteristic) (hB_char : B.Characteristic)
    (hcard :
      Nat.card (A ⧸ B.subgroupOf A) =
        Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
          Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))) :
    (A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).Characteristic ∧
      (B.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).Characteristic ∧
        Nat.card
            ((A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype) ⧸
              ((B.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).subgroupOf
                (A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype))) =
          Nat.card ↥((default : Sylow q G) : Subgroup G) := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  haveI : B.Characteristic := hB_char
  haveI : ((B.subgroupOf A) : Subgroup A).Normal :=
    (inferInstance : B.Normal).subgroupOf A
  refine ⟨?_, ?_, ?_⟩
  · exact OddOrder.GroupTheory.characteristic_map_subtype_of_characteristic
      (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} G) hA_char
  · exact OddOrder.GroupTheory.characteristic_map_subtype_of_characteristic
      (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} G) hB_char
  · calc
      Nat.card
          ((A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype) ⧸
            ((B.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).subgroupOf
              (A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype))) =
          Nat.card (A ⧸ B.subgroupOf A) := by
        simpa [O] using Subgroup.nat_card_quotient_subgroupOf_map_subtype_eq
          (H := O) hBA
      _ = Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
          Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) := hcard
      _ = Nat.card ↥((default : Sylow q G) : Subgroup G) :=
        card_sylow_oPiCore_eq_card_sylow_of_hasNormalPComplement_ne hpq hG
          (default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
          (default : Sylow q G)

/-- One factor of the characteristic Sylow series in BG Theorem 4.20(c).

The data records two characteristic subgroups `lower <= upper` whose quotient has
exactly the cardinality of a Sylow `q`-subgroup of the ambient group.  Keeping the
factor as data lets the 4.20(c) induction lift whole layers from the normal
`p`-complement before assembling the full series. -/
structure CharacteristicSylowLayer (G : Type*) [Group G] [Finite G]
    (q : ℕ) [Fact q.Prime] where
  upper : Subgroup G
  lower : Subgroup G
  lower_le_upper : lower ≤ upper
  upper_char : upper.Characteristic
  lower_char : lower.Characteristic
  card_quotient_eq_sylow :
    Nat.card (upper ⧸ lower.subgroupOf upper) =
      Nat.card ↥((default : Sylow q G) : Subgroup G)

namespace CharacteristicSylowLayer

/-- A bottom layer in the BG Theorem 4.20(c) characteristic Sylow series supplies
a normal Sylow subgroup. -/
theorem exists_normal_sylow_of_lower_eq_bot {q : ℕ} [Fact q.Prime]
    (L : CharacteristicSylowLayer G q) (hlower : L.lower = ⊥) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  refine exists_normal_sylow_of_characteristic_quotient_bot_card_eq_sylow
    L.upper_char ?_
  simpa [hlower] using L.card_quotient_eq_sylow

/-- The top layer `G/O_{p-prime}` associated to a normal `p`-complement.

This is the layer attached at the front of the BG Theorem 4.20(c) induction
series after Theorem 4.18(b) replaces the chosen complement by the canonical
`O_{p-prime}`. -/
noncomputable def top_of_hasNormalPComplement
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) :
    CharacteristicSylowLayer G p := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  haveI : O.Normal := by dsimp [O]; infer_instance
  haveI : (O.subgroupOf (⊤ : Subgroup G)).Normal :=
    (inferInstance : O.Normal).subgroupOf (⊤ : Subgroup G)
  have hquot_top :
      Nat.card ((⊤ : Subgroup G) ⧸ O.subgroupOf (⊤ : Subgroup G)) =
        Nat.card (G ⧸ O) := by
    let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    have hmap : (O.subgroupOf (⊤ : Subgroup G)).map e.toMonoidHom = O := by
      ext x
      constructor
      · rintro ⟨y, hyO, rfl⟩
        exact hyO
      · intro hx
        exact ⟨⟨x, trivial⟩, hx, rfl⟩
    exact Nat.card_congr
      (QuotientGroup.congr (O.subgroupOf (⊤ : Subgroup G)) O e hmap).toEquiv
  exact
    { upper := ⊤
      lower := O
      lower_le_upper := le_top
      upper_char := Subgroup.topCharacteristic
      lower_char := by
        dsimp [O]
        exact Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} G
      card_quotient_eq_sylow := by
        calc
          Nat.card ((⊤ : Subgroup G) ⧸ O.subgroupOf (⊤ : Subgroup G)) =
              Nat.card (G ⧸ O) := hquot_top
          _ = Nat.card ↥((default : Sylow p G) : Subgroup G) := by
            simpa [O] using
              card_quotient_oPiCore_eq_card_sylow_of_hasNormalPComplement
                (G := G) hG (default : Sylow p G) }

@[simp] theorem top_of_hasNormalPComplement_upper
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) :
    (top_of_hasNormalPComplement (G := G) hG).upper = ⊤ := rfl

@[simp] theorem top_of_hasNormalPComplement_lower
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) :
    (top_of_hasNormalPComplement (G := G) hG).lower =
      Ch03.oPiCore {r : ℕ | r ≠ p} G := rfl

/-- Apply BG Theorem 4.18(b) inside a normal subgroup and attach the resulting
normal `p`-complement as the ambient top Sylow layer. -/
noncomputable def top_of_normal_subgroup_pRank_le_two
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} [H.Normal] [IsSolvable ↥H]
    (hoddH : Odd (Nat.card ↥H)) (hpH : p ∣ Nat.card ↥H)
    (hpCaseH : p = 3 ∨ ∀ q ∈ (Nat.card ↥H).primeFactors, p ≤ q)
    (hrH : pRank ↥H p ≤ 2) (houter : IsPGroup p (G ⧸ H)) :
    CharacteristicSylowLayer G p := by
  classical
  have hH_compl : Ch05.HasNormalPComplement p ↥H :=
    (solvable_structure_of_pRank_le_two (G := ↥H) hoddH hpH hrH).2.1 hpCaseH
  exact top_of_hasNormalPComplement (G := G)
    (hasNormalPComplement_of_normal_subgroup_hasNormalPComplement_of_quotient_isPGroup
      (G := G) (H := H) hH_compl houter)

/-- Fitting-rank version of `top_of_normal_subgroup_pRank_le_two`: if a Sylow
`p`-subgroup of the normal subgroup lies in its Fitting subgroup and that Fitting
subgroup has rank at most two, then the same ambient top layer is available. -/
noncomputable def top_of_normal_subgroup_sylow_le_fitting
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} [H.Normal] [IsSolvable ↥H]
    (hoddH : Odd (Nat.card ↥H)) (hpH : p ∣ Nat.card ↥H)
    (hpCaseH : p = 3 ∨ ∀ q ∈ (Nat.card ↥H).primeFactors, p ≤ q)
    (P : Sylow p ↥H) (hPfit : (P : Subgroup ↥H) ≤ Ch01.fitting ↥H)
    (hrFH : OddOrder.GroupTheory.rank ↥(Ch01.fitting ↥H) ≤ 2)
    (houter : IsPGroup p (G ⧸ H)) :
    CharacteristicSylowLayer G p :=
  top_of_normal_subgroup_pRank_le_two (G := G) (H := H) hoddH hpH hpCaseH
    (pRank_le_two_of_sylow_le_fitting (G := ↥H) P hPfit hrFH) houter

/-- Lift a characteristic Sylow layer from the canonical normal `p`-complement to
the ambient group, for `q != p`. -/
noncomputable def lift_oPiCore_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (L : CharacteristicSylowLayer
      ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G) q) :
    CharacteristicSylowLayer G q :=
  let hlift := characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
    (G := G) hpq hG L.lower_le_upper L.upper_char L.lower_char
    L.card_quotient_eq_sylow
  { upper := L.upper.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype
    lower := L.lower.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype
    lower_le_upper := Subgroup.map_mono L.lower_le_upper
    upper_char := hlift.1
    lower_char := hlift.2.1
    card_quotient_eq_sylow := hlift.2.2 }

end CharacteristicSylowLayer

/-- One labelled factor in the BG Theorem 4.20(c) characteristic Sylow series. -/
structure CharacteristicSylowStep (G : Type*) [Group G] [Finite G] where
  q : ℕ
  q_prime : Fact q.Prime
  layer : @CharacteristicSylowLayer G _ _ q q_prime

namespace CharacteristicSylowStep

/-- Upper endpoint of a labelled characteristic Sylow step. -/
def upper (S : CharacteristicSylowStep G) : Subgroup G :=
  @CharacteristicSylowLayer.upper G _ _ S.q S.q_prime S.layer

/-- Lower endpoint of a labelled characteristic Sylow step. -/
def lower (S : CharacteristicSylowStep G) : Subgroup G :=
  @CharacteristicSylowLayer.lower G _ _ S.q S.q_prime S.layer

/-- Regard an unlabelled characteristic Sylow layer as a labelled step. -/
def ofLayer {q : ℕ} [Fact q.Prime] (L : CharacteristicSylowLayer G q) :
    CharacteristicSylowStep G :=
  { q := q
    q_prime := inferInstance
    layer := L }

@[simp] theorem upper_ofLayer {q : ℕ} [Fact q.Prime]
    (L : CharacteristicSylowLayer G q) :
    (ofLayer L).upper = L.upper := rfl

@[simp] theorem lower_ofLayer {q : ℕ} [Fact q.Prime]
    (L : CharacteristicSylowLayer G q) :
    (ofLayer L).lower = L.lower := rfl

/-- A labelled step whose lower endpoint is bottom supplies a normal Sylow
subgroup for its label. -/
theorem exists_normal_sylow_of_lower_eq_bot (S : CharacteristicSylowStep G)
    (hlower : S.lower = ⊥) : ∃ Q : Sylow S.q G, (Q : Subgroup G).Normal := by
  haveI : Fact S.q.Prime := S.q_prime
  exact CharacteristicSylowLayer.exists_normal_sylow_of_lower_eq_bot S.layer
    (by simpa [lower] using hlower)

end CharacteristicSylowStep

/-- A finite characteristic Sylow series in the form used by BG Theorem 4.20(c).

The terms are indexed as `G_0, ..., G_n`, with each step carrying the existing
`CharacteristicSylowLayer` payload for the quotient `G_i/G_{i+1}`.  The labels
are part of the step data; later theorem statements can impose that they enumerate
`Nat.card G` prime factors in increasing order. -/
structure CharacteristicSylowSeries (G : Type*) [Group G] [Finite G] where
  length : ℕ
  term : Fin (length + 1) → Subgroup G
  top_eq : term 0 = ⊤
  bot_eq : term (Fin.last length) = ⊥
  step : Fin length → CharacteristicSylowStep G
  upper_eq : ∀ i : Fin length, (step i).upper = term (Fin.castSucc i)
  lower_eq : ∀ i : Fin length, (step i).lower = term i.succ

/-- The downstream-facing package supplied by BG Theorem 4.20(c).

The raw `CharacteristicSylowSeries` records the characteristic factor data.  Consumers such
as §9 also need the series to have a terminal step and need that terminal label to be an
actual prime divisor of the ambient group.  Keeping those as explicit fields avoids baking
strictness assumptions into the raw series representation. -/
structure CharacteristicSylowSeriesPackage (G : Type*) [Group G] [Finite G] where
  series : CharacteristicSylowSeries G
  length_pos : 0 < series.length
  terminal_mem :
    ∀ i : Fin series.length,
      i.succ = Fin.last series.length → (series.step i).q ∈ (Nat.card G).primeFactors

/-- A finite characteristic Sylow segment with arbitrary endpoints.

This is the ambient image of the induction series inside the canonical normal
`p`-complement before the top `G/O_{p-prime}` layer is attached. -/
structure CharacteristicSylowSegment (G : Type*) [Group G] [Finite G] where
  length : ℕ
  term : Fin (length + 1) → Subgroup G
  step : Fin length → CharacteristicSylowStep G
  upper_eq : ∀ i : Fin length, (step i).upper = term (Fin.castSucc i)
  lower_eq : ∀ i : Fin length, (step i).lower = term i.succ

namespace CharacteristicSylowStep

/-- Lift a labelled step from the canonical normal `p`-complement to the ambient
group. -/
noncomputable def lift_oPiCore_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowStep ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : S.q ≠ p) : CharacteristicSylowStep G :=
  { q := S.q
    q_prime := S.q_prime
    layer := @CharacteristicSylowLayer.lift_oPiCore_of_hasNormalPComplement_ne
      G _ _ p S.q _ S.q_prime hpq hG S.layer }

@[simp] theorem upper_lift_oPiCore_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowStep ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : S.q ≠ p) :
    (S.lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG hpq).upper =
      S.upper.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
  haveI : Fact S.q.Prime := S.q_prime
  unfold lift_oPiCore_of_hasNormalPComplement_ne upper
  unfold CharacteristicSylowLayer.lift_oPiCore_of_hasNormalPComplement_ne
  rcases characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
      (G := G) hpq hG S.layer.lower_le_upper S.layer.upper_char
      S.layer.lower_char S.layer.card_quotient_eq_sylow with
    ⟨hupper, hlower, hcard⟩
  rfl

@[simp] theorem lower_lift_oPiCore_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowStep ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : S.q ≠ p) :
    (S.lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG hpq).lower =
      S.lower.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
  haveI : Fact S.q.Prime := S.q_prime
  unfold lift_oPiCore_of_hasNormalPComplement_ne lower
  unfold CharacteristicSylowLayer.lift_oPiCore_of_hasNormalPComplement_ne
  rcases characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
      (G := G) hpq hG S.layer.lower_le_upper S.layer.upper_char
      S.layer.lower_char S.layer.card_quotient_eq_sylow with
    ⟨hupper, hlower, hcard⟩
  rfl

end CharacteristicSylowStep

namespace CharacteristicSylowSegment

/-- Attach a top characteristic Sylow layer to a segment whose top endpoint is
that layer's lower endpoint, producing a full characteristic Sylow series. -/
def consTop (seg : CharacteristicSylowSegment G) {q : ℕ} [Fact q.Prime]
    (topLayer : CharacteristicSylowLayer G q) (hupper : topLayer.upper = ⊤)
    (hlink : topLayer.lower = seg.term 0)
    (hbot : seg.term (Fin.last seg.length) = ⊥) : CharacteristicSylowSeries G :=
  { length := seg.length + 1
    term := Fin.cons (⊤ : Subgroup G) seg.term
    top_eq := by
      simp [Fin.cons_zero]
    bot_eq := by
      simpa [Fin.cons_last] using hbot
    step := Fin.cons (CharacteristicSylowStep.ofLayer topLayer) seg.step
    upper_eq := by
      intro i
      cases i using Fin.cases
      · simp [CharacteristicSylowStep.upper_ofLayer, hupper]
      · rename_i i
        have hidx : Fin.castSucc i.succ = (Fin.castSucc i).succ := by
          ext
          rfl
        rw [hidx, Fin.cons_succ]
        exact seg.upper_eq i
    lower_eq := by
      intro i
      cases i using Fin.cases
      · simp [CharacteristicSylowStep.lower_ofLayer, hlink]
      · rename_i i
        simpa [Fin.cons_succ] using seg.lower_eq i }

end CharacteristicSylowSegment

namespace CharacteristicSylowSeries

/-- Forget the endpoint conditions of a full characteristic Sylow series. -/
def toSegment (S : CharacteristicSylowSeries G) : CharacteristicSylowSegment G :=
  { length := S.length
    term := S.term
    step := S.step
    upper_eq := S.upper_eq
    lower_eq := S.lower_eq }

/-- Any step of a characteristic Sylow series whose lower endpoint is bottom
supplies a normal Sylow subgroup for that step's label. -/
theorem exists_normal_sylow_of_step_lower_eq_bot
    (S : CharacteristicSylowSeries G) (i : Fin S.length)
    (hlower : (S.step i).lower = ⊥) :
    ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal :=
  CharacteristicSylowStep.exists_normal_sylow_of_lower_eq_bot (S.step i) hlower

/-- A step whose lower series term is bottom supplies a normal Sylow subgroup. -/
theorem exists_normal_sylow_of_step_term_eq_bot
    (S : CharacteristicSylowSeries G) (i : Fin S.length)
    (hterm : S.term i.succ = ⊥) :
    ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal :=
  exists_normal_sylow_of_step_lower_eq_bot S i ((S.lower_eq i).trans hterm)

/-- The terminal step of a characteristic Sylow series supplies a normal Sylow
subgroup for its label. -/
theorem exists_normal_sylow_of_terminal_step
    (S : CharacteristicSylowSeries G) (i : Fin S.length)
    (hi : i.succ = Fin.last S.length) :
    ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal :=
  exists_normal_sylow_of_step_term_eq_bot S i (by rw [hi, S.bot_eq])

/-- A positive-length characteristic Sylow series has a terminal step. -/
theorem exists_terminal_step_of_length_pos (S : CharacteristicSylowSeries G)
    (hpos : 0 < S.length) :
    ∃ i : Fin S.length, i.succ = Fin.last S.length := by
  obtain ⟨n, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  refine ⟨Fin.cast hlen.symm (Fin.last n), ?_⟩
  apply Fin.ext
  simp [Fin.val_succ, Fin.val_last, hlen]

/-- A positive-length characteristic Sylow series supplies a normal Sylow subgroup
from its terminal step. -/
theorem exists_normal_sylow_of_length_pos (S : CharacteristicSylowSeries G)
    (hpos : 0 < S.length) :
    ∃ i : Fin S.length,
      i.succ = Fin.last S.length ∧
        ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal := by
  obtain ⟨i, hi⟩ := exists_terminal_step_of_length_pos S hpos
  exact ⟨i, hi, exists_normal_sylow_of_terminal_step S i hi⟩

/-- Lift the induction series inside the canonical normal `p`-complement to an
ambient segment in `G`.  Its top endpoint is `O_{p-prime}(G)`, not `G`; the top
layer is attached separately by `CharacteristicSylowLayer.top_of_hasNormalPComplement`. -/
noncomputable def lift_oPiCore_segment_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    CharacteristicSylowSegment G :=
  { length := S.length
    term := fun i => (S.term i).map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype
    step := fun i => (S.step i).lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG (hpq i)
    upper_eq := by
      intro i
      calc
        ((S.step i).lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG (hpq i)).upper =
            (S.step i).upper.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [CharacteristicSylowStep.upper_lift_oPiCore_of_hasNormalPComplement_ne]
        _ = (S.term (Fin.castSucc i)).map
              (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [S.upper_eq i]
    lower_eq := by
      intro i
      calc
        ((S.step i).lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG (hpq i)).lower =
            (S.step i).lower.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [CharacteristicSylowStep.lower_lift_oPiCore_of_hasNormalPComplement_ne]
        _ = (S.term i.succ).map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [S.lower_eq i] }

/-- The lifted complement segment starts at the canonical normal `p`-complement. -/
theorem lift_oPiCore_segment_top_eq
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    (lift_oPiCore_segment_of_hasNormalPComplement_ne (G := G) hG S hpq).term 0 =
      Ch03.oPiCore {r : ℕ | r ≠ p} G := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  change (S.term 0).map O.subtype = O
  rw [S.top_eq]
  ext x
  constructor
  · rintro ⟨y, _hy, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

/-- The lifted complement segment still ends at the ambient bottom subgroup. -/
theorem lift_oPiCore_segment_bot_eq
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    (lift_oPiCore_segment_of_hasNormalPComplement_ne (G := G) hG S hpq).term
        (Fin.last S.length) = ⊥ := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  change (S.term (Fin.last S.length)).map O.subtype = ⊥
  rw [S.bot_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Subgroup.mem_bot] using congrArg O.subtype hy
  · intro hx
    rw [Subgroup.mem_bot] at hx
    subst x
    exact ⟨1, by simp, rfl⟩

/-- Lift the induction series inside the canonical normal `p`-complement and
attach the top `G/O_{p-prime}` layer, producing the ambient characteristic Sylow
series used in BG Theorem 4.20(c). -/
noncomputable def lift_oPiCore_series_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    CharacteristicSylowSeries G :=
  (lift_oPiCore_segment_of_hasNormalPComplement_ne (G := G) hG S hpq).consTop
    (CharacteristicSylowLayer.top_of_hasNormalPComplement (G := G) hG)
    (by simp)
    (by
      rw [CharacteristicSylowLayer.top_of_hasNormalPComplement_lower]
      exact (lift_oPiCore_segment_top_eq (G := G) hG S hpq).symm)
    (lift_oPiCore_segment_bot_eq (G := G) hG S hpq)

@[simp] theorem lift_oPiCore_series_length_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    (lift_oPiCore_series_of_hasNormalPComplement_ne (G := G) hG S hpq).length =
      S.length + 1 := rfl

end CharacteristicSylowSeries

namespace CharacteristicSylowSeriesPackage

/-- A packaged BG Theorem 4.20(c) characteristic Sylow series supplies the terminal
normal Sylow subgroup together with the fact that its label lies in `π(G)`. -/
theorem exists_terminal_normal_sylow (P : CharacteristicSylowSeriesPackage G) :
    ∃ i : Fin P.series.length,
      i.succ = Fin.last P.series.length ∧
        (P.series.step i).q ∈ (Nat.card G).primeFactors ∧
          ∃ Q : Sylow (P.series.step i).q G, (Q : Subgroup G).Normal := by
  obtain ⟨i, hi, hQ⟩ :=
    CharacteristicSylowSeries.exists_normal_sylow_of_length_pos P.series P.length_pos
  exact ⟨i, hi, P.terminal_mem i hi, hQ⟩

end CharacteristicSylowSeriesPackage

/-- For a finite group `B` whose elements pairwise commute (i.e. abelian), the quotient by its
`p'`-core `O_{p'}(B) = oPiCore {r ≠ p} B` is a `p`-group.

In an abelian — more generally nilpotent — group `B ≅ Sylow_p(B) × O_{p'}(B)`, so `B/O_{p'}(B)`
is the Sylow `p`-subgroup.  This is the BG Theorem 4.20(c) step "`G/F` is abelian, hence
`(G/F)/O_{p₁'}(G/F)` is a `p₁`-group". -/
theorem isPGroup_quotient_oPiCore_of_comm {B : Type*} [Group B] [Finite B] {p : ℕ}
    [Fact p.Prime] (hcomm : ∀ x y : B, x * y = y * x) :
    IsPGroup p (B ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} B) := by
  classical
  set O : Subgroup B := Ch03.oPiCore {r : ℕ | r ≠ p} B with hOdef
  set C := B ⧸ O with hCdef
  -- the quotient is abelian and has trivial `p'`-core
  have hcommC : ∀ x y : C, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective O x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul, hcomm a b]
  have hcoreC : Ch03.oPiCore {r : ℕ | r ≠ p} C = ⊥ :=
    Ch03.oPiCore_quotient_self_eq_bot _
  -- every prime dividing `|C|` equals `p`
  have huniq : ∀ q : ℕ, q.Prime → q ∣ Nat.card C → q = p := by
    intro q hq hqdvd
    by_contra hqp
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := Ch01.cauchy (G := C) hqdvd
    -- `⟨x⟩` is a normal `{r ≠ p}`-subgroup, hence trivial — contradicting `|⟨x⟩| = q > 1`.
    haveI hnorm : (Subgroup.zpowers x).Normal :=
      { conj_mem := fun n hn g => by
          have hgn : g * n * g⁻¹ = n := by
            rw [hcommC g n, mul_assoc, mul_inv_cancel, mul_one]
          rw [hgn]; exact hn }
    have hcard : Nat.card (Subgroup.zpowers x) = q := by
      rw [Nat.card_zpowers, hx]
    have hpi : Ch03.Subgroup.IsPiGroup {r : ℕ | r ≠ p} (Subgroup.zpowers x) := by
      intro q' hq'
      rw [hcard, hq.primeFactors, Finset.mem_singleton] at hq'
      change q' ≠ p
      rw [hq']; exact hqp
    have hbot : Subgroup.zpowers x = ⊥ :=
      Ch03.eq_bot_of_isPiGroup_of_oPiCore_eq_bot {r : ℕ | r ≠ p} hpi hcoreC
    have hx1 : x = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [hx1, orderOf_one] at hx
    exact hq.ne_one hx.symm
  -- a number all of whose prime divisors equal `p` is a power of `p`
  have hcard_eq : Nat.card C = p ^ (Nat.card C).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdvd => huniq d hd hdvd)
  exact IsPGroup.iff_card.mpr ⟨_, hcard_eq⟩

/-- If `X` has a nilpotent normal subgroup `M` whose index is coprime to `p` (so `M` contains a
full Sylow `p`-subgroup of `X`), then some Sylow `p`-subgroup of `X` lies in the Fitting subgroup
`F(X)`.

BG Theorem 4.20(c) applies this with `X = H`, `M = F(G)` viewed inside `H`: since `H/F` is a
`p₁'`-group, `p₁ ∤ [H:F]`, and `F ≤ F(H)` is nilpotent and normal. -/
theorem exists_sylow_le_fitting_of_nilpotent_normal_index_coprime
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {M : Subgroup X} [M.Normal] [Group.IsNilpotent ↥M] (hidx : ¬ p ∣ M.index) :
    ∃ P : Sylow p X, (P : Subgroup X) ≤ Ch01.fitting X := by
  classical
  have hM_le : M ≤ Ch01.fitting X := Ch01.nilpotent_normal_le_fitting
  -- `p`-part of `|X|` equals `p`-part of `|M|`, since `p ∤ [X:M]`.
  have hfactX : (Nat.card X).factorization p = (Nat.card ↥M).factorization p := by
    have hmul : Nat.card ↥M * M.index = Nat.card X := Subgroup.card_mul_index M
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  -- a Sylow `p` of `M`, pushed into `X`, has full `p`-order, hence is Sylow in `X`.
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  set Rmap : Subgroup X := (R : Subgroup ↥M).map M.subtype with hRmap
  have hRmap_pg : IsPGroup p ↥Rmap := R.isPGroup'.map M.subtype
  have hRmap_le : Rmap ≤ Ch01.fitting X := (Subgroup.map_subtype_le _).trans hM_le
  have hRmap_card : Nat.card ↥Rmap = p ^ (Nat.card X).factorization p := by
    rw [hRmap, Subgroup.card_map_of_injective M.subtype_injective, R.card_eq_multiplicity,
      ← hfactX]
  obtain ⟨P, hP_le⟩ := IsPGroup.exists_le_sylow hRmap_pg
  have hRmap_eq : Rmap = (P : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hP_le
      (le_of_eq (P.card_eq_multiplicity.trans hRmap_card.symm))
  exact ⟨P, hRmap_eq ▸ hRmap_le⟩

/-! The BG Theorem 4.20(c) producer
`exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two` lives in
`S05_NarrowPGroups` (`section Thm420c`): its strong induction requires `G' ≤ F(G)`
(BG Theorem 4.20(a)), which the repository derives via Theorem 5.7
(`derived_le_fitting_of_centralizer_rank_le_two`), and `S05` is downstream of this file. -/

end Thm418

end OddOrder.BG.Ch1.S04
