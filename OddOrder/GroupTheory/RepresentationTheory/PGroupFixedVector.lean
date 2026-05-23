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
import Mathlib.FieldTheory.Finite.Basic

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

* `IsPGroup.invariants_ne_bot` (※ stub, 次セッションで proof):
  `[Fact p.Prime]`, `[Finite G]`, `IsPGroup p G`, `[Field F]`,
  `CharP F p`, `[Module.Finite F V]`, `V ≠ 0` の下で
  `Representation F G V` の `invariants` 部分加群は `⊥` でない.

* `IsPGroup.exists_fixed_vector_ne_zero` (※ stub):
  上の言い換え `∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v`.

## Proof strategy (将来 sorry-free 化のために)

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

**未確定の細部** (次セッション):
- `LinearMap.IsNilpotent` (or `IsNilpotent (ρ z - 1)`) の mathlib 名,
  `kernel ≠ ⊥` への帰着.
- `G/⟨z⟩` 上 `W` への restricted representation 構築 (mathlib
  `Representation.subrepresentation` 系? 要 grep).
- 帰納の well-founded structure (`Nat.card`).
-/

/-! 既存 `OddOrder/GroupTheory/ChermakDelgado.lean` / `ElementaryAbelian.lean`
の `Subgroup` namespace 拡張流儀に倣い, 本 module は mathlib `IsPGroup`
namespace を直接拡張する (dot-notation `hG.invariants_ne_bot` が効くため).
ファイル位置 `OddOrder/GroupTheory/RepresentationTheory/` が
"OddOrder の shared module" であることを示す. -/

namespace IsPGroup

open Representation

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [CharP F p]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- **Gorenstein Lemma 2.6.3** (Isaacs FGT 不在): `p`-群 `G` が char `p`
の体 `F` 上の有限次元 vector space `V` に表現として作用するとき, `V` が
非零なら固定 vector の部分加群は `⊥` でない.

stub: 詳細 proof は本ファイル冒頭 docstring の "Proof strategy" 参照. -/
theorem invariants_ne_bot
    (_hG : IsPGroup p G) (ρ : Representation F G V)
    (_hV : (⊤ : Submodule F V) ≠ ⊥) :
    ρ.invariants ≠ ⊥ := by
  sorry

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
