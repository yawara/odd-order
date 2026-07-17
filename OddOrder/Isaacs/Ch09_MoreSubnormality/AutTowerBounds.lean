/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Group

/-!
# Isaacs Ch. 9 — §9B: Lemma 9.12 / Lemma 9.14 (tower の bounding 補題, pp. 278-279)

Wielandt automorphism tower theorem (Thm 9.10) の 2 本の一般補題:

- **Lemma 9.12** (`centralizer_inf_eq_bot_of_chain`): 部分群鎖
  `S = S_0 ◁ S_1 ◁ ⋯ ◁ S_r` で各段 `C_{S_{i+1}}(S_i) = 1` なら `C_{S_r}(S) = 1`.
  (書籍は `S_r = G` ambient で述べるが, ここでは相対形 `C(S_0) ⊓ S_r = ⊥` で
  形式化 — 帰納で鎖の切片に適用するのに都合が良く, ambient 形は `S r = ⊤` の特殊化.)
- **Lemma 9.14**: `N ◁ G`, `C_G(N) ≤ N` なら
  - (`card_dvd_card_center_mul_card_mulAut`) `|G| ∣ |Z(N)| · |Aut(N)|`,
  - (`card_dvd_factorial_card_of_centralizer_le`) `|G| ∣ |N|!`.

Lemma 9.14 の後半は `Aut(N)` が `N ∖ {1}` に忠実に作用することから
`|Aut(N)| ∣ (|N| − 1)!` (`card_mulAut_dvd_factorial_pred`) を経由する.

9.13 (order bound) / 9.10 (tower theorem) 本体は Schenkman (9.21) の後の leaf.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open scoped Nat

section /- 9B: Lemma 9.12 (p. 278) -/

variable {G : Type*} [Group G]

/-- 部分群鎖の単調性: 隣接包含から `S i ≤ S j` (`i ≤ j ≤ r`). -/
private theorem chain_le {r : ℕ} {S : ℕ → Subgroup G}
    (hle : ∀ i < r, S i ≤ S (i + 1)) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ r → S i ≤ S j := by
  intro i j hij
  induction hij with
  | refl => intro _; exact le_rfl
  | @step m _ IHstep =>
    intro hm1r
    exact (IHstep (le_trans (Nat.le_succ m) hm1r)).trans (hle m (Nat.lt_of_succ_le hm1r))

/-- 正規化する元による共役は centralizer を保つ: `g ∈ N_G(H)`, `c ∈ C_G(H)` なら
`g c g⁻¹ ∈ C_G(H)`. -/
theorem conj_mem_centralizer_of_mem_normalizer {H : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hc : c ∈ Subgroup.centralizer (H : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g⁻¹ * x * g ∈ H := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa using h
  have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hx'
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * c * g⁻¹) * x := by group

/-- **Isaacs Lemma 9.12** (相対形): 鎖 `S 0 ≤ S 1 ≤ ⋯ ≤ S r` で各 `S (i+1)` が `S i` を
正規化し `C(S i) ⊓ S (i+1) = ⊥` (各段の相対 centralizer が自明) なら
`C(S 0) ⊓ S r = ⊥`.

書籍証明そのまま (`|r|` 帰納): `C := C(S 0)` について `C ⊓ S r = ⊥` (鎖の切片への帰納) と,
`c ∈ C ⊓ S (r+1)`, `s ∈ S 1` の交換子が `C ⊓ S r` に落ちること
(`s` は `C` を正規化, `c` は `S r` を正規化) から `C ⊓ S (r+1) ≤ C(S 1)`, 最後に
shifted 鎖 `i ↦ S (i+1)` への帰納で `C(S 1) ⊓ S (r+1) = ⊥`. -/
theorem centralizer_inf_eq_bot_of_chain :
    ∀ r : ℕ, 0 < r → ∀ S : ℕ → Subgroup G,
      (∀ i < r, S i ≤ S (i + 1)) →
      (∀ i < r, S (i + 1) ≤ Subgroup.normalizer (S i : Set G)) →
      (∀ i < r, Subgroup.centralizer (S i : Set G) ⊓ S (i + 1) = ⊥) →
      Subgroup.centralizer (S 0 : Set G) ⊓ S r = ⊥ := by
  intro r
  induction r with
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | succ r IH =>
    intro _ S hle hnorm hcent
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact hcent 0 Nat.zero_lt_one
    -- 帰納 1: 鎖の先頭切片 `S 0 … S r` に適用
    have IH1 := IH hr S (fun i hi => hle i (Nat.lt_succ_of_lt hi))
      (fun i hi => hnorm i (Nat.lt_succ_of_lt hi))
      (fun i hi => hcent i (Nat.lt_succ_of_lt hi))
    -- 帰納 2: shifted 鎖 `S 1 … S (r+1)` に適用
    have IH2 := IH hr (fun i => S (i + 1))
      (fun i hi => hle (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hnorm (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hcent (i + 1) (Nat.succ_lt_succ hi))
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcC, hcS⟩ := Subgroup.mem_inf.mp hc
    -- `c` は `S 1` を中心化: 交換子 `s c s⁻¹ c⁻¹ ∈ C ⊓ S r = ⊥`
    have hcS1 : c ∈ Subgroup.centralizer (S 1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs_r : s ∈ S r := chain_le hle hr (Nat.le_succ r) hs
      have hcomm_mem : s * c * s⁻¹ * c⁻¹
          ∈ Subgroup.centralizer (S 0 : Set G) ⊓ S r := by
        rw [Subgroup.mem_inf]
        constructor
        · -- `s ∈ S 1 ≤ N(S 0)` は `C` を保つ
          have hsC : s * c * s⁻¹ ∈ Subgroup.centralizer (S 0 : Set G) :=
            conj_mem_centralizer_of_mem_normalizer
              (hnorm 0 (Nat.succ_pos r) hs) hcC
          exact mul_mem hsC (inv_mem hcC)
        · -- `c ∈ S (r+1) ≤ N(S r)` と `s ∈ S r`
          have hconj : c * s⁻¹ * c⁻¹ ∈ S r :=
            (Subgroup.mem_normalizer_iff.mp
              (hnorm r (Nat.lt_succ_self r) hcS) s⁻¹).mp (inv_mem hs_r)
          have h := mul_mem hs_r hconj
          have heq : s * (c * s⁻¹ * c⁻¹) = s * c * s⁻¹ * c⁻¹ := by group
          rwa [heq] at h
      rw [IH1, Subgroup.mem_bot] at hcomm_mem
      have h2 : s * c * s⁻¹ = c := by
        have h := mul_eq_one_iff_eq_inv.mp hcomm_mem
        simpa using h
      calc s * c = (s * c * s⁻¹) * s := by group
        _ = c * s := by rw [h2]
    rw [← IH2]
    exact Subgroup.mem_inf.mpr ⟨hcS1, hcS⟩

/-- **Isaacs Lemma 9.12** (ambient 形, 書籍の表現): 鎖の頂上が `G` 全体なら
`C_G(S 0) = ⊥`. -/
theorem centralizer_eq_bot_of_chain {r : ℕ} (hr : 0 < r) (S : ℕ → Subgroup G)
    (hle : ∀ i < r, S i ≤ S (i + 1))
    (hnorm : ∀ i < r, S (i + 1) ≤ Subgroup.normalizer (S i : Set G))
    (hcent : ∀ i < r, Subgroup.centralizer (S i : Set G) ⊓ S (i + 1) = ⊥)
    (htop : S r = ⊤) :
    Subgroup.centralizer (S 0 : Set G) = ⊥ := by
  have h := centralizer_inf_eq_bot_of_chain r hr S hle hnorm hcent
  rwa [htop, inf_top_eq] at h

end

section /- 9B: Lemma 9.14 (p. 279) -/

variable {G : Type*} [Group G]

/-- `Aut(M)` の `M ∖ {1}` 上の忠実置換表現 (Isaacs p. 279: "`Aut(N)` acts faithfully on
the set of nonidentity elements of `N`"). -/
def mulAutPermNeOne (M : Type*) [Group M] : MulAut M →* Equiv.Perm {x : M // x ≠ 1} where
  toFun α := Equiv.subtypeEquiv α.toEquiv fun a => by
    have hiff : α a = 1 ↔ a = 1 :=
      ⟨fun ha => α.injective (by rw [ha, map_one]), fun ha => by rw [ha, map_one]⟩
    exact not_congr hiff.symm
  map_one' := by ext x; rfl
  map_mul' α β := by ext x; rfl

theorem mulAutPermNeOne_injective (M : Type*) [Group M] :
    Function.Injective (mulAutPermNeOne M) := by
  intro α β h
  ext x
  by_cases hx : x = 1
  · rw [hx, map_one, map_one]
  · exact congrArg Subtype.val
      (congrArg (fun p : Equiv.Perm {y : M // y ≠ 1} => p ⟨x, hx⟩) h)

/-- `|Aut(M)| ∣ (|M| − 1)!` (`M ∖ {1}` への忠実作用 + Lagrange). -/
theorem card_mulAut_dvd_factorial_pred (M : Type*) [Group M] [Finite M] :
    Nat.card (MulAut M) ∣ (Nat.card M - 1)! := by
  classical
  haveI := Fintype.ofFinite M
  have hcard_range : Nat.card ↥(mulAutPermNeOne M).range = Nat.card (MulAut M) :=
    Nat.card_congr (MonoidHom.ofInjective (mulAutPermNeOne_injective M)).toEquiv.symm
  have hdvd : Nat.card ↥(mulAutPermNeOne M).range
      ∣ Nat.card (Equiv.Perm {x : M // x ≠ 1}) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hcard_range] at hdvd
  have hperm : Nat.card (Equiv.Perm {x : M // x ≠ 1}) = (Nat.card M - 1)! := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]
    congr 1
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rwa [hperm] at hdvd

/-- 共役表現 `G →* Aut(N)` (`MulAut.conjNormal`) の核は `C_G(N)`. -/
theorem conjNormal_ker {N : Subgroup G} [N.Normal] :
    (MulAut.conjNormal (H := N) : G →* MulAut ↥N).ker
      = Subgroup.centralizer (N : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h n hn
    have happ : g * n * g⁻¹ = n := by
      have h2 := congrArg (fun α : MulAut ↥N => ((α ⟨n, hn⟩ : ↥N) : G)) h
      simpa using h2
    calc n * g = (g * n * g⁻¹) * g := by rw [happ]
      _ = g * n := by group
  · intro h
    ext n
    -- `ext` は元の値レベル `↑(conjNormal g n) = ↑((1 : MulAut ↥N) n)` まで降ろす
    have hcomm := h n n.2
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← hcomm, mul_assoc,
      mul_inv_cancel, mul_one]

/-- **Isaacs Lemma 9.14 (前半)**: `N ◁ G`, `C_G(N) ≤ N` なら
`|G| ∣ |Z(N)| · |Aut(N)|`. 共役表現 `G → Aut(N)` の核が `C_G(N) = Z(N)` で,
像は Lagrange で `|Aut(N)|` を割る. -/
theorem card_dvd_card_center_mul_card_mulAut [Finite G] {N : Subgroup G} [N.Normal]
    (h : Subgroup.centralizer (N : Set G) ≤ N) :
    Nat.card G ∣ Nat.card (Subgroup.center ↥N) * Nat.card (MulAut ↥N) := by
  set κ := (MulAut.conjNormal (H := N) : G →* MulAut ↥N) with hκdef
  -- `C_G(N) = Z(N)` (`C_G(N) ≤ N` から)
  have hcent_eq : Subgroup.centralizer (N : Set G)
      = (Subgroup.center ↥N).map N.subtype := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, h hx⟩, Subgroup.mem_center_iff.mpr fun m => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hx m m.2
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨n, hn⟩)
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup κ.ker
  have hker_card : Nat.card ↥κ.ker = Nat.card (Subgroup.center ↥N) := by
    rw [hκdef, conjNormal_ker, hcent_eq]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ N.subtype_injective).toEquiv.symm
  have hquot : Nat.card (G ⧸ κ.ker) ∣ Nat.card (MulAut ↥N) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange κ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hsplit, hker_card,
    mul_comm (Nat.card (Subgroup.center ↥N)) (Nat.card (MulAut ↥N))]
  exact mul_dvd_mul hquot dvd_rfl

/-- **Isaacs Lemma 9.14 (後半)**: `N ◁ G`, `C_G(N) ≤ N` なら `|G| ∣ |N|!`
(`|Z(N)| ∣ |N|`, `|Aut(N)| ∣ (|N|−1)!`, `|N| · (|N|−1)! = |N|!`). -/
theorem card_dvd_factorial_card_of_centralizer_le [Finite G] {N : Subgroup G} [N.Normal]
    (h : Subgroup.centralizer (N : Set G) ≤ N) :
    Nat.card G ∣ (Nat.card ↥N)! :=
  calc Nat.card G
      ∣ Nat.card (Subgroup.center ↥N) * Nat.card (MulAut ↥N) :=
        card_dvd_card_center_mul_card_mulAut h
    _ ∣ Nat.card ↥N * (Nat.card ↥N - 1)! :=
        mul_dvd_mul (Subgroup.card_subgroup_dvd_card _)
          (card_mulAut_dvd_factorial_pred ↥N)
    _ = (Nat.card ↥N)! := Nat.mul_factorial_pred Nat.card_pos.ne'

end

end OddOrder.Isaacs.Ch09
