/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.WeaklyClosed

/-!
# Isaacs Chapter 5 — Problems 5C (transfer と非単純性)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 5C (書籍 pp. 162-164)。

現在の実装:

* **5C.5** `exists_mem_normalizer_conj_eq_of_normal` — `P ∈ Syl_p(G)` の正規部分群 `A`, `B`
  が `G`-共役なら `N_G(P)`-共役。系として `A` が `P` の特性部分群なら `A = B`。

⚠ **5C.6 (weak closure) は hub レーンが `OddOrder/GroupTheory/WeaklyClosed.lean` で
着手中** (issue 9503; `IsWeaklyClosed` / `exists_mem_normalizer_conj_eq` 等) なので
本ファイルでは扱わない。
-/

namespace OddOrder.Isaacs.Ch05

section /- 5C: Problems (pp. 162-164) -/

variable {G : Type*} [Group G]

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
