/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.FieldTheory.Finite.Basic
import OddOrder.Mathlib.Subgroup

/-!
# p-Group Fixed Vector on a char-p Vector Space

`OddOrder.GroupTheory` shared module: **BG §2 Thm 2.6** および **BG §3
(L1255 周辺)** で使われる「`p`-群 `G` が char `p` の体 `F` 上の有限次元
ベクトル空間 `V` に representation として作用するとき、非零固定 vector が
存在する」(= `ρ.invariants ≠ ⊥`) の基本補題.

## Gorenstein (G) ↔ Isaacs FGT / mathlib / shared module 読み替え

CLAUDE.md L20 方針 (BG 中の "G, Thm X.Y.Z" 引用は Isaacs FGT に読み替え) を
本 module で扱う Gorenstein 引用に適用:

- **G Lem 2.6.3** (p-group on char-p F-vector ⇒ 非零 fixed vector 存在)
  → **Isaacs FGT 不在** (Isaacs FGT は群論本で representation theory
  章なし; mmd で `Clifford` `Jacobson` 共に 0 hit, Ch.6 は Frobenius
  Actions であって表現論章ではない).
  → **mathlib partial**: `Representation.Invariants` (`invariants ρ`,
  `mem_invariants`) は基盤として既存. しかし「char p で p-group ⇒
  invariants ≠ ⊥」直接ステートメントは未収載.
  → **本 module**: 上記基盤の上に, |G| 帰納 + p-群 center 非自明 +
  char p で `(ρ z - 1)^{p^k} = 0` (Frobenius 二項展開) 経由で構築.

詳細 mapping: `notes/meta/phase2_cross_refs.md` §5.

## Main results

* `IsPGroup.invariants_ne_bot`:
  `[Fact p.Prime]`, `[Finite G]`, `IsPGroup p G`, `[Field F]`,
  `CharP F p`, `[Module.Finite F V]`, `V ≠ 0` の下で
  `Representation F G V` の `invariants` 部分加群は `⊥` でない.

* `IsPGroup.exists_fixed_vector_ne_zero`:
  上の言い換え `∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v`.

## Proof strategy

|G| 帰納 (well-founded on `Nat.card G`):
1. **base** `Nat.card G = 1` ⇒ 全 `g = 1`, `ρ g = id`, 任意 `v ≠ 0` が fixed.
2. **step** `Nat.card G > 1` ⇒ `IsPGroup.center_nontrivial` (mathlib 既存)
   で `Z(G) ≠ ⊥`. 非自明 `z ∈ Z(G)`. `orderOf z = p^k` (k ≥ 1).
   - `ρ z : V →ₗ[F] V` で `(ρ z)^{p^k} = ρ (z^{p^k}) = ρ 1 = 1`.
   - `CharP F p` ⇒ `(ρ z - 1)^{p^k} = (ρ z)^{p^k} - 1 = 0` (Frobenius
     binomial / `add_pow_char` 等経由).
   - `ρ z - 1` は nilpotent + `V ≠ ⊥` ⇒ `ker (ρ z - 1) ≠ ⊥`
     (= `z`-fixed subspace `W` ≠ ⊥).
3. `W = LinearMap.ker (ρ z - 1)` は `G`-invariant (z ∈ Z(G) で全 g と可換).
4. `G/⟨z⟩` (Z(G) 内の z の zpowers で商) は p-群で位数 `< |G|`. 帰納仮定で
   `W` 上の表現に非零 fixed vector が存在. これが `G` 全体での fixed vector.
-/

/-! 既存 `OddOrder/GroupTheory/ChermakDelgado.lean` / `ElementaryAbelian.lean`
の `Subgroup` namespace 拡張流儀に倣い, 本 module は mathlib `IsPGroup`
namespace を直接拡張する (dot-notation `hG.invariants_ne_bot` が効くため).
ファイル位置 `OddOrder/GroupTheory/RepresentationTheory/` が
"OddOrder の shared module" であることを示す. -/

namespace IsPGroup

open Representation

universe uG uF uV

variable {p : ℕ} [Fact p.Prime]
variable {G : Type uG} [Group G] [Finite G]
variable {F : Type uF} [Field F] [CharP F p]
variable {V : Type uV} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-! ### Helper lemmas (sorry-free) -/

omit [Finite G] [Module.Finite F V] [CharP F p] in
/-- `(ρ g)^(orderOf g) = 1` as an endomorphism of `V`. Used in
`invariants_ne_bot` proof: `ρ g` の order は `orderOf g` を割る. -/
theorem map_pow_orderOf_eq_one (ρ : Representation F G V) (g : G) :
    (ρ g) ^ orderOf g = (1 : Module.End F V) := by
  rw [← map_pow, pow_orderOf_eq_one, map_one]

omit [Finite G] [Module.Finite F V] [CharP F p] in
/-- For a `p`-group element `g`, `(ρ g)^(p^k) = 1` for some `k`
(specifically, `k` such that `orderOf g = p^k`). -/
theorem exists_map_pow_prime_pow_eq_one
    (hG : IsPGroup p G) (ρ : Representation F G V) (g : G) :
    ∃ k : ℕ, (ρ g) ^ (p ^ k) = (1 : Module.End F V) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hG g
  exact ⟨k, hk ▸ map_pow_orderOf_eq_one ρ g⟩

omit [Fact p.Prime] [Finite G] [Module.Finite F V] in
/-- `Module.End F V` inherits `CharP _ p` from `F` whenever `V` is nontrivial.
Proof: `algebraMap F (Module.End F V)` is injective on a nontrivial vector space
(picks up an `a • v = b • v` test on some `v ≠ 0`, then `smul_left_injective`),
so `charP_of_injective_algebraMap` transfers `CharP F p` to the endomorphism ring. -/
theorem charP_End_of_field [Nontrivial V] : CharP (Module.End F V) p := by
  refine charP_of_injective_algebraMap (R := F) (A := Module.End F V) ?_ p
  intro a b hab
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply smul_left_injective F hv
  have h_apply := DFunLike.congr_fun hab v
  simpa [Algebra.algebraMap_eq_smul_one, Module.End.one_apply] using h_apply

omit [Finite G] [Module.Finite F V] in
/-- For a `p`-group element `g` acting on a nontrivial `F`-vector space `V` with
`CharP F p`, `(ρ g - 1)^(p^k) = 0` in `Module.End F V` for some `k`
(specifically, `k` such that `orderOf g = p^k`).

Proof: `(ρ g)^(p^k) = 1` by `exists_map_pow_prime_pow_eq_one`. Then Frobenius
binomial (`sub_pow_char_pow_of_commute`, applicable since `ρ g` and `1` commute
and `Module.End F V` inherits `CharP _ p` from `F`) gives
`(ρ g - 1)^(p^k) = (ρ g)^(p^k) - 1^(p^k) = 1 - 1 = 0`. -/
theorem exists_pow_sub_one_eq_zero
    [Nontrivial V]
    (hG : IsPGroup p G) (ρ : Representation F G V) (g : G) :
    ∃ k : ℕ, ((ρ g : Module.End F V) - 1) ^ (p ^ k) = 0 := by
  haveI : CharP (Module.End F V) p := charP_End_of_field
  obtain ⟨k, hk⟩ := exists_map_pow_prime_pow_eq_one hG ρ g
  refine ⟨k, ?_⟩
  rw [sub_pow_char_pow_of_commute _ _ (Commute.one_right _), hk, one_pow, sub_self]

omit [Fact p.Prime] [Finite G] [Module.Finite F V] [CharP F p] in
/-- An `F`-endomorphism `f` of `V` with `f^N = 0` for some `N` has nontrivial
kernel whenever `V` is nontrivial.

Proof by contradiction: if `ker f = ⊥` then `f` is injective, hence `f^N` is
injective (composition of injections). But `f^N = 0` sends any `v ≠ 0` to `0`,
contradicting injectivity. -/
theorem ker_ne_bot_of_pow_eq_zero
    [Nontrivial V] {f : Module.End F V} {N : ℕ} (hf : f ^ N = 0) :
    LinearMap.ker f ≠ ⊥ := by
  intro h_bot
  rw [LinearMap.ker_eq_bot] at h_bot
  have h_pow_inj : Function.Injective (⇑(f ^ N) : V → V) := by
    clear hf
    induction N with
    | zero =>
      intro a b hab
      simpa using hab
    | succ k ih =>
      intro a b hab
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply] at hab
      exact h_bot (ih hab)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply h_pow_inj
  rw [hf, LinearMap.zero_apply, map_zero]

/-! ### Helpers for the strong induction on `Nat.card G` -/

omit [Fact p.Prime] [Finite G] [Module.Finite F V] [CharP F p] in
/-- A subgroup generated by a central element is normal. Used to form the
quotient `G ⧸ ⟨z⟩` in the induction step of `invariants_ne_bot`. -/
private theorem zpowers_normal_of_mem_center
    {z : G} (hz : z ∈ Subgroup.center G) :
    (Subgroup.zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hgz : Commute g z := Subgroup.mem_center_iff.mp hz g
  rw [(hgz.zpow_right k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

omit [Fact p.Prime] [Finite G] [Module.Finite F V] [CharP F p] in
/-- A nonzero submodule is a nonzero module when viewed as a type. -/
private theorem top_ne_bot_of_submodule_ne_bot
    {W : Submodule F V} (hW : W ≠ ⊥) :
    (⊤ : Submodule F W) ≠ ⊥ := by
  obtain ⟨v, hvW, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro htop_bot
  have hv_bot : (⟨v, hvW⟩ : W) ∈ (⊥ : Submodule F W) := by
    simpa [htop_bot] using (Submodule.mem_top : (⟨v, hvW⟩ : W) ∈ (⊤ : Submodule F W))
  have hv_zero : (⟨v, hvW⟩ : W) = 0 := by
    simpa using hv_bot
  exact hv_ne (congrArg Subtype.val hv_zero)

/-! ### Main result -/

/-- **Gorenstein Lemma 2.6.3** (Isaacs FGT 不在): `p`-群 `G` が char `p`
の体 `F` 上の有限次元 vector space `V` に表現として作用するとき, `V` が
非零なら固定 vector の部分加群は `⊥` でない.

Proof: `Nat.card G` の強帰納. 非自明な中心元 `z` に対し
`ker (ρ z - 1)` を非零にし, `Z = ⟨z⟩` 上の invariants から
`G ⧸ Z` の `quotientToInvariants` 表現へ帰納仮定を適用する. -/
theorem invariants_ne_bot
    (hG : IsPGroup p G) (ρ : Representation F G V)
    (hV : (⊤ : Submodule F V) ≠ ⊥) :
    ρ.invariants ≠ ⊥ := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ {G' : Type uG} [Group G'] [Finite G'], Nat.card G' = n →
      ∀ {F' : Type uF} [Field F'] [CharP F' p]
        {V' : Type uV} [AddCommGroup V'] [Module F' V'] [Module.Finite F' V'],
        (hG : IsPGroup p G') → (ρ : Representation F' G' V') →
          (⊤ : Submodule F' V') ≠ ⊥ → ρ.invariants ≠ ⊥
  refine (Nat.strongRecOn (motive := motive) (Nat.card G) ?_) rfl hG ρ hV
  intro n ih G _ _ hcard F _ _ V _ _ _ hG ρ hV
  by_cases hNontriv : Nontrivial G
  · -- Step: Nontrivial G
    haveI := hNontriv
    haveI := hG.center_nontrivial
    haveI : Nontrivial V := by
      obtain ⟨v, _, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
      exact ⟨v, 0, hv⟩
    -- 非自明 z ∈ Z(G) を取得
    obtain ⟨z, hz_ne⟩ := exists_ne (1 : Subgroup.center G)
    let Z : Subgroup G := Subgroup.zpowers (z : G)
    have hz_ne_coe : (z : G) ≠ 1 := fun hz => hz_ne (Subtype.ext hz)
    haveI hZ_normal : Z.Normal := zpowers_normal_of_mem_center z.2
    have hZ_ne_bot : Z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz_ne_coe
    have _hZ_card_lt : Nat.card (G ⧸ Z) < Nat.card G :=
      Subgroup.card_quotient_lt_of_ne_bot hZ_ne_bot
    -- (ρ z - 1)^(p^k) = 0
    obtain ⟨k, hk_pow⟩ := exists_pow_sub_one_eq_zero hG ρ (z : G)
    -- W := ker (ρ z - 1) は ⊥ でない
    have hker_ne_bot : LinearMap.ker ((ρ (z : G) : Module.End F V) - 1) ≠ ⊥ :=
      ker_ne_bot_of_pow_eq_zero hk_pow
    have hz_fixed_ne_bot :
        Representation.invariants (ρ.comp Z.subtype : Representation F Z V) ≠ ⊥ := by
      obtain ⟨v, hvker, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne_bot
      have hvz : ρ (z : G) v = v := by
        change (((ρ (z : G) : Module.End F V) - 1) v = 0) at hvker
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hvker
        exact hvker
      let zZ : Z := ⟨z, Subgroup.mem_zpowers (z : G)⟩
      have hZ_cyclic : ∀ x : Z, x ∈ Subgroup.zpowers zZ := by
        intro x
        rw [Subgroup.mem_zpowers_iff]
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
        refine ⟨j, ?_⟩
        ext
        simpa [zZ] using hj
      have hv_inv :
          v ∈ Representation.invariants (ρ.comp Z.subtype : Representation F Z V) := by
        rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
          (ρ := (ρ.comp Z.subtype : Representation F Z V)) zZ hZ_cyclic]
        simpa [zZ] using hvz
      intro hbot
      have hv_bot : v ∈ (⊥ : Submodule F V) := by
        simpa [hbot] using hv_inv
      exact hv_ne (by simpa using hv_bot)
    have hquot_inv_ne_bot :
        Representation.invariants (Representation.quotientToInvariants ρ Z) ≠ ⊥ := by
      have hlt : Nat.card (G ⧸ Z) < n := by
        simpa [hcard] using _hZ_card_lt
      exact ih (Nat.card (G ⧸ Z)) hlt rfl (hG.to_quotient Z)
        (Representation.quotientToInvariants ρ Z) (top_ne_bot_of_submodule_ne_bot hz_fixed_ne_bot)
    obtain ⟨w, hw_inv, hw_ne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hquot_inv_ne_bot
    have hwV_inv : (w : V) ∈ ρ.invariants := by
      rw [Representation.mem_invariants]
      intro g
      have hwg := (Representation.mem_invariants (Representation.quotientToInvariants ρ Z) w).mp
        hw_inv (QuotientGroup.mk' Z g)
      simpa using congrArg Subtype.val hwg
    intro hbot
    have hw_bot : (w : V) ∈ (⊥ : Submodule F V) := by
      simpa [hbot] using hwV_inv
    apply hw_ne
    ext
    simpa using hw_bot
  · -- Base: G subsingleton ⇒ ρ g = 1 for all g ⇒ invariants = ⊤
    haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hNontriv
    have h_eq_top : ρ.invariants = ⊤ := by
      rw [eq_top_iff]
      intro v _ g
      have hg : g = 1 := Subsingleton.elim g 1
      rw [hg, map_one, Module.End.one_apply]
    intro h_inv_bot
    apply hV
    calc (⊤ : Submodule F V)
        = ρ.invariants := h_eq_top.symm
      _ = ⊥ := h_inv_bot

/-- **言い換え**: 非零固定 vector の存在形 (BG §2 Thm 2.6 / BG §3 で
直接使う形). `IsPGroup.invariants_ne_bot` の corollary. -/
theorem exists_fixed_vector_ne_zero
    (hG : IsPGroup p G) (ρ : Representation F G V)
    (hV : (⊤ : Submodule F V) ≠ ⊥) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (hG.invariants_ne_bot ρ hV)
  refine ⟨v, hv_ne, ?_⟩
  intro g
  exact (Representation.mem_invariants ρ v).mp hv_mem g

end IsPGroup
