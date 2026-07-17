/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Frattini
import OddOrder.Isaacs.Ch09_MoreSubnormality.NilpotentResidual

/-!
# Isaacs Ch. 9 — §9B: Schenkman's theorem (Lemmas 9.19–9.20, Theorems 9.21–9.22, p. 282)

Wielandt automorphism tower theorem (Thm 9.10) の最終ピース. Schenkman の定理
(`C_G(S^∞) ≤ S^∞` for `S ◁ G` with `C_G(S) = 1`) と, それを支える 2 本の Frattini
補題からなる.

- **Lemma 9.19** (`isNilpotent_of_frattini_le_of_quotient_nilpotent`): `N ◁ G`,
  `N ≤ Φ(G)`, `G/N` nilpotent ⇒ `G` nilpotent.
- **Lemma 9.20** (`exists_nilpotent_sup_eq_top`): `N ◁ G`, `G/N` nilpotent ⇒
  nilpotent `H ≤ G` で `N ⊔ H = ⊤`.
- **Theorem 9.22** (`centralizer_nilpotentResidual_le_of_center_eq_bot`): `Z(G) = 1`
  ⇒ `C_G(G^∞) ≤ G^∞`.
- **Theorem 9.21** (Schenkman, `centralizer_nilpotentResidual_le_of_centralizer_eq_bot`):
  `S ◁ G`, `C_G(S) = 1` ⇒ `C_G(S^∞) ≤ S^∞`.

## 実装ノート

- 9.19: mathlib の `Group.isNilpotent_of_finite_tfae` の同値 (3)「全 coatom が normal」
  ⇒ (1)「nilpotent」を使う. 任意の coatom `M` について `N ≤ Φ(G) ≤ M`
  (`frattini_le_coatom`) ゆえ像 `M̄ = M.map (mk' N)` は `Ḡ = G/N` の coatom
  (`isCoatom_map_of_ker_le`; mathlib は `comap` 方向しか持たないので本ファイルで
  `map` 方向を補う). `Ḡ` nilpotent ⇒ `M̄ ◁ Ḡ` (`NormalizerCondition.normal_of_coatom`),
  `M = comap (mk' N) M̄` (`N ≤ M`) より `M ◁ G`.
- ⚠ mmd 抽出 (L5091, L5095) は 9.19/9.20 の仮定を正しく `N ◁ G` と抽出.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

section /- 9B: coatom transport 補助 (mathlib の map 方向補完) -/

/-- `IsCoatom` の `map` 方向 (kernel が coatom 以下): 全射 `φ` と coatom `M ⊇ ker φ`
に対し像 `M.map φ` も coatom. mathlib は `isCoatom_comap_of_surjective` (comap 方向) と
`MulEquiv` 版 `isCoatom_map` しか持たないため, 非同型全射に対する map 方向を補う. -/
theorem isCoatom_map_of_ker_le {H : Type*} [Group H] {φ : G →* H}
    (hφ : Function.Surjective φ) {M : Subgroup G} (hM : IsCoatom M) (hker : φ.ker ≤ M) :
    IsCoatom (M.map φ) := by
  refine ⟨?_, ?_⟩
  · intro htop
    refine hM.1 ?_
    have h : Subgroup.comap φ (M.map φ) = M := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
    rw [htop, Subgroup.comap_top] at h
    exact h.symm
  · intro K' hK'
    rw [← Subgroup.comap_lt_comap_of_surjective hφ, Subgroup.comap_map_eq,
      sup_eq_left.mpr hker] at hK'
    have hcomapK : Subgroup.comap φ K' = ⊤ := hM.2 _ hK'
    calc K' = φ.range ⊓ K' := by
              rw [MonoidHom.range_eq_top_of_surjective φ hφ, top_inf_eq]
      _ = Subgroup.map φ (Subgroup.comap φ K') := (Subgroup.map_comap_eq φ K').symm
      _ = Subgroup.map φ ⊤ := by rw [hcomapK]
      _ = ⊤ := Subgroup.map_top_of_surjective φ hφ

end

section /- 9B: Lemma 9.19 (p. 282) -/

/-- **Isaacs Lemma 9.19** (p. 282): `N ◁ G`, `N ≤ Φ(G)`, `G/N` nilpotent ならば
`G` nilpotent. -/
theorem isNilpotent_of_frattini_le_of_quotient_nilpotent [Finite G] {N : Subgroup G}
    [hN : N.Normal] (hle : N ≤ frattini G) (hquot : Group.IsNilpotent (G ⧸ N)) :
    Group.IsNilpotent G := by
  haveI := hquot
  have hnc : NormalizerCondition (G ⧸ N) := Group.normalizerCondition_of_isNilpotent
  refine ((Group.isNilpotent_of_finite_tfae (G := G)).out 2 0).mp ?_
  intro M hM
  have hNM : N ≤ M := hle.trans (frattini_le_coatom hM)
  have hcoatom : IsCoatom (M.map (QuotientGroup.mk' N)) :=
    isCoatom_map_of_ker_le (QuotientGroup.mk'_surjective N) hM
      (by rw [QuotientGroup.ker_mk']; exact hNM)
  haveI hmapnormal : (M.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom _ hnc hcoatom
  have hMeq : M = Subgroup.comap (QuotientGroup.mk' N) (M.map (QuotientGroup.mk' N)) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNM]
  rw [hMeq]
  infer_instance

end

section /- 9B: Lemma 9.20 (p. 282) -/

/-- **Isaacs Lemma 9.20** (p. 282): `N ◁ G`, `G/N` nilpotent ならば nilpotent な
`H ≤ G` で `N ⊔ H = ⊤` (`NH = G`) が存在する.

証明: `{H | N ⊔ H = ⊤}` の極小元 `E` を取る (`⊤` が属すので非空; 有限). `E` が
nilpotent なことを Lemma 9.19 で示せばよい. `N' = N ⊓ E` について:
- `↥E ⧸ N' ≅ (E の G/N での像) ≤ G/N` は nilpotent (subgroup of nilpotent).
- `N' ≤ Φ(↥E)`: さもなくば coatom `M'` で `N' ⊄ M'`, すると `N' ⊔ M' = ⊤` を
  `G` に押し戻して `N ⊔ (M'.map subtype) = ⊤` かつ `M'.map subtype < E`, 極小性に矛盾. -/
theorem exists_nilpotent_sup_eq_top [Finite G] {N : Subgroup G} [hN : N.Normal]
    (hquot : Group.IsNilpotent (G ⧸ N)) :
    ∃ H : Subgroup G, Group.IsNilpotent ↥H ∧ N ⊔ H = ⊤ := by
  obtain ⟨E, hEmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun H : Subgroup G => N ⊔ H = ⊤) ⟨⊤, by simp⟩
  refine ⟨E, ?_, hEmin.1⟩
  haveI hN'normal : (N.subgroupOf E).Normal := hN.subgroupOf E
  -- `↥E ⧸ N'` は G/N の部分群と同型 ⇒ nilpotent
  have hquotE : Group.IsNilpotent (↥E ⧸ N.subgroupOf E) := by
    set φ := (QuotientGroup.mk' N).comp E.subtype with hφ
    have hker : φ.ker = N.subgroupOf E := by
      rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
    have e : (↥E ⧸ N.subgroupOf E) ≃* ↥φ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivRange φ)
    haveI := hquot
    exact Group.nilpotent_of_mulEquiv e.symm
  -- `N' ≤ Φ(↥E)`
  have hNfrat : N.subgroupOf E ≤ frattini (↥E) := by
    simp only [frattini, Order.radical, le_iInf_iff, Set.mem_setOf_eq]
    intro M' hM'
    by_contra hnle
    -- `N' ⊔ M' = ⊤` (M' coatom, N' ⊄ M')
    have hlt : M' < N.subgroupOf E ⊔ M' :=
      lt_of_le_of_ne le_sup_right fun heq => hnle (le_sup_left.trans_eq heq.symm)
    have hsuptop : N.subgroupOf E ⊔ M' = ⊤ := hM'.2 _ hlt
    -- `G` に押し戻し: `(N ⊓ E) ⊔ (M'.map subtype) = E`
    have hmapsup : N ⊓ E ⊔ M'.map E.subtype = E := by
      have h := congrArg (Subgroup.map E.subtype) hsuptop
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
    -- `N ⊔ (M'.map subtype) = ⊤`
    have hNMtop : N ⊔ M'.map E.subtype = ⊤ := by
      have key : N ⊔ M'.map E.subtype = N ⊔ E := by
        conv_rhs => rw [← hmapsup]
        rw [← sup_assoc, sup_eq_left.mpr (inf_le_left : N ⊓ E ≤ N)]
      rw [key, hEmin.1]
    -- `M'.map subtype < E`
    have hMltE : M'.map E.subtype < E := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le M') fun heq => hM'.1 ?_
      apply Subgroup.map_injective E.subtype_injective
      rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact absurd (hEmin.2 hNMtop hMltE.le) (not_le_of_gt hMltE)
  exact isNilpotent_of_frattini_le_of_quotient_nilpotent hNfrat hquotE

end

end OddOrder.Isaacs.Ch09
