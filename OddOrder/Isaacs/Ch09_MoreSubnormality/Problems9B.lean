/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import OddOrder.Isaacs.Ch09_MoreSubnormality.AutTower
import OddOrder.Isaacs.Ch09_MoreSubnormality.Problems9A
import OddOrder.Isaacs.Ch09_MoreSubnormality.NilpotentResidual
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalSocle

/-!
# Isaacs §9B の演習 (書籍 pp. 284-285)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9B
(Wielandt の automorphism tower 周辺)。

* **9B.1** `exists_normal_isComplement_of_isCompleteGroup` — `S ⊴ G` で `S` が
  **complete** (中心自明かつ自己同型がすべて内部) なら `G = S × T`。
* **9B.2** `isCompleteGroup_autTowerType_one_of_normal_range` — `Z(G) = 1` で `G` の像が
  `G₃ = Aut(Aut(G))` で正規なら `Aut(G)` は complete (= tower は `G₂` で止まる)。
  ⚠ 書籍の「`i ≤ 2`」はこの形に**再解釈**して形式化した (issue 1055 参照)。
* **9B.3** `isCompleteGroup_mulAut_of_isSemisimpleGroup` — `G` semisimple なら `Aut(G)` は
  complete (`E(Aut G) = Inn(G)` が characteristic なので 9B.2 が使える)。
* **9B.5** `nilpotentResidual_top_eq_sup_of_isSubnormal` — `G = AB` で `A, B ⊲⊲ G` なら
  `G^∞ = A^∞ B^∞`。⚠ 仮説は join でなく**積** (`(A : Set G) * B = Set.univ`);
  帰納段の Dedekind が積の恒等式なので join では回らない。

書籍の statement はページ画像 `references/isaacs/pages/isaacs-p284-297.png` /
`isaacs-p285-298.png` で確定 (⚠ 9B.5 の `A, B ⊲⊲ G` は **subnormal**)。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

section /- 9B.1: complete な正規部分群は直積因子 (p. 284) -/

/-- **Complete group** (Isaacs p. 278): 中心が自明で, 自己同型がすべて内部。 -/
def IsCompleteGroup (G : Type*) [Group G] : Prop :=
  center G = ⊥ ∧ innAut G = ⊤

/-- `Z(↥N) = 1` なら `N ⊓ C_G(N) = 1` (`N ⊓ C_G(N)` の元は `↥N` の中心元)。 -/
theorem inf_centralizer_eq_bot_of_center_eq_bot {N : Subgroup G} (h : center ↥N = ⊥) :
    N ⊓ Subgroup.centralizer (N : Set G) = ⊥ := by
  refine le_bot_iff.mp fun x hx => ?_
  have hmem : (⟨x, hx.1⟩ : ↥N) ∈ center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2)
  rw [h, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

/-- **Isaacs Problem 9B.1** (書籍 p. 284) ⭐: `S ⊴ G` で `S` が complete なら
`G = S × T`, ここで `T = C_G(S)`。

**証明**: `T := C_G(S)` は `S ◁ G` ゆえ正規。`S ⊓ T` は `Z(S) = 1` なので自明。
`g ∈ G` に対し `g` が `S` に誘導する自己同型 (`MulAut.conjNormal g`) は内部, つまり
ある `s ∈ S` の共役に等しいので `s⁻¹ g ∈ C_G(S)`, したがって `g ∈ S T`。 -/
theorem exists_normal_isComplement_of_isCompleteGroup {S : Subgroup G} [S.Normal]
    (h : IsCompleteGroup ↥S) :
    ∃ T : Subgroup G, T.Normal ∧ S ⊓ T = ⊥ ∧ S ⊔ T = ⊤ := by
  refine ⟨Subgroup.centralizer (S : Set G), inferInstance,
    inf_centralizer_eq_bot_of_center_eq_bot h.1, ?_⟩
  refine top_le_iff.mp fun g _ => ?_
  -- `g` の誘導する自己同型は内部。
  have hmem : MulAut.conjNormal (H := S) g ∈ innAut ↥S := by
    rw [h.2]
    exact Subgroup.mem_top _
  obtain ⟨s, hs⟩ := hmem
  -- `s⁻¹ g` は `S` を中心化する。
  have hcent : (s : G)⁻¹ * g ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hval : (s : G) * x * (s : G)⁻¹ = g * x * g⁻¹ := by
      have hap := congrArg (fun t : ↥S => (t : G))
        (congrArg (fun f : MulAut ↥S => f ⟨x, hx⟩) hs)
      simpa [MulAut.conjNormal_apply] using hap
    have hyx : ((s : G)⁻¹ * g) * x * ((s : G)⁻¹ * g)⁻¹ = x := by
      rw [mul_inv_rev, inv_inv]
      calc (s : G)⁻¹ * g * x * (g⁻¹ * (s : G))
          = (s : G)⁻¹ * (g * x * g⁻¹) * (s : G) := by group
        _ = (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * (s : G) := by rw [hval]
        _ = x := by group
    calc x * ((s : G)⁻¹ * g)
        = (((s : G)⁻¹ * g) * x * ((s : G)⁻¹ * g)⁻¹) * ((s : G)⁻¹ * g) := by rw [hyx]
      _ = ((s : G)⁻¹ * g) * x := by group
  have hg : g = (s : G) * ((s : G)⁻¹ * g) := by group
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right hcent)

end -- 9B.1

section /- 9B.2: G ⊴ G₃ なら Aut(G) は complete (p. 285) -/

/-- **`C_K(A) = 1` の押し上げ**: `A`, `B` がともに `K` で正規で `C_K(A) ⊓ B = 1`,
`C_K(B) = 1` なら `C_K(A) = 1`。

`C_K(A)` も `B` も `K`-正規なので `⁅C_K(A), B⁆ ≤ C_K(A) ⊓ B = 1`,
すなわち `C_K(A) ≤ C_K(B) = 1`。

9B.2 で `A` = `G` の像, `B` = `Aut(G)` の像, `K = Aut(Aut(G))` として使う。 -/
theorem centralizer_eq_bot_of_inf_eq_bot_of_centralizer_eq_bot {K : Type*} [Group K]
    {A B : Subgroup K} [A.Normal] [B.Normal]
    (hinf : Subgroup.centralizer (A : Set K) ⊓ B = ⊥)
    (hCB : Subgroup.centralizer (B : Set K) = ⊥) :
    Subgroup.centralizer (A : Set K) = ⊥ := by
  have hcomm : ⁅Subgroup.centralizer (A : Set K), B⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hinf]
    exact le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
  refine le_bot_iff.mp ?_
  rw [← hCB]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

/-- `A ⊴ K` への共役作用の核は `C_K(A)`。 -/
theorem ker_conjNormal {K : Type*} [Group K] (A : Subgroup K) [A.Normal] :
    (MulAut.conjNormal (H := A)).ker = Subgroup.centralizer (A : Set K) := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx a ha
    have h1 : ((MulAut.conjNormal (H := A) x ⟨a, ha⟩ : ↥A) : K)
        = ((1 : MulAut ↥A) ⟨a, ha⟩ : K) := by rw [hx]
    rw [MulAut.conjNormal_apply] at h1
    simp only [MulAut.one_apply] at h1
    calc a * x = (x * a * x⁻¹) * x := by rw [h1]
      _ = x * a := by group
  · intro hx
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    simp only [MulAut.one_apply]
    calc x * (a : K) * x⁻¹ = ((a : K) * x) * x⁻¹ := by rw [hx (a : K) a.2]
      _ = (a : K) := by group

/-- **忠実な共役作用は `K ↪ Aut(A)`**: `A ⊴ K` で `C_K(A) = 1` なら `|K| ≤ |Aut(A)|`。 -/
theorem card_le_card_mulAut_of_centralizer_eq_bot {K : Type*} [Group K] [Finite K]
    {A : Subgroup K} [A.Normal] (h : Subgroup.centralizer (A : Set K) = ⊥) :
    Nat.card K ≤ Nat.card (MulAut ↥A) := by
  refine Nat.card_le_card_of_injective (MulAut.conjNormal (H := A)) ?_
  rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal, h]

/-- 群同型に沿った `Aut` の個数の一致 (`MulAut` の functor 性は mathlib に無いので自前)。 -/
theorem card_mulAut_congr {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card (MulAut H) = Nat.card (MulAut K) :=
  Nat.card_congr
    ⟨fun φ => e.symm.trans (φ.trans e), fun ψ => e.trans (ψ.trans e.symm),
      fun φ => MulEquiv.ext fun x => by simp, fun ψ => MulEquiv.ext fun x => by simp⟩

/-- `G` の `G₃ = Aut(Aut(G))` での像は `Inn(G)` の `autTowerStep G 1` による像。 -/
theorem range_autTowerEmb_two.{u} (G : Type u) [Group G] :
    (autTowerEmb G 0 2).range = (innAut G).map (autTowerStep G 1) := by
  rw [autTowerEmb_succ, MonoidHom.range_comp, autTowerEmb_succ, MonoidHom.range_comp,
    autTowerEmb_zero, MonoidHom.range_eq_top.mpr Function.surjective_id,
    ← MonoidHom.range_eq_map, range_autTowerStep]
  rfl

/-- **Isaacs Problem 9B.2** (書籍 p. 285) ⭐ — **再解釈版** (issue 1055 参照):
`Z(G) = 1` で `G` の像が `G₃ = Aut(Aut(G))` で正規なら, `Aut(G)` は **complete**。
すなわち automorphism tower は `G₂ = Aut(G)` で止まり, 相異なる群は高々 2 個。

⚠ 書籍の「`G ⊲ Gᵢ` なら `i ≤ 2`」は tower が定常な場合 (`G` complete 等) には
そのままでは成り立たず, 上の形が実際の内容 (9B.3 / 9B.4 の
"contains at most two different groups" と同じ言い回し)。

**証明**: `A` = `G` の `G₃` での像, `B` = `G₂` の `G₃` での像 (= `Inn(G₂)`) とする。
`C_{G₃}(B) = 1` と `C_{G₃}(A) ⊓ B = 1` (どちらも Lemma 9.11(c)) から
`C_{G₃}(A) = 1`。すると `G₃` は `A ≅ G` に忠実に共役作用するので
`|G₃| ≤ |Aut(G)| = |G₂| = |B|`, 有限性から `B = ⊤`。 -/
theorem isCompleteGroup_autTowerType_one_of_normal_range.{u} {G : Type u} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) (hnormal : ((autTowerEmb G 0 2).range).Normal) :
    IsCompleteGroup (autTowerType G 1) := by
  refine ⟨center_autTowerType_eq_bot hZ 1, ?_⟩
  haveI := hnormal
  -- `B` = `G₂` の像 = `Inn(G₂)`。
  have hCB : Subgroup.centralizer (((autTowerStep G 1).range : Subgroup (autTowerType G 2)) :
      Set (autTowerType G 2)) = ⊥ := by
    rw [range_autTowerStep]
    exact centralizer_innAut_eq_bot (center_autTowerType_eq_bot hZ 1)
  -- `A = (Inn G).map (autTowerStep G 1)`。
  have hA : (autTowerEmb G 0 2).range = (innAut G).map (autTowerStep G 1) :=
    range_autTowerEmb_two G
  -- `C_{G₃}(A) ⊓ B = 1` (Lemma 9.11(c) を `autTowerStep G 1` で押し出す)。
  have hinf : Subgroup.centralizer (((autTowerEmb G 0 2).range :
        Subgroup (autTowerType G 2)) : Set (autTowerType G 2))
      ⊓ (autTowerStep G 1).range = ⊥ := by
    have hbase : Subgroup.centralizer ((innAut G : Subgroup (MulAut G)) :
        Set (MulAut G)) ⊓ ⊤ = ⊥ := by
      rw [inf_top_eq]
      exact centralizer_innAut_eq_bot hZ
    have hpush := centralizer_map_inf_map_eq_bot (f := autTowerStep G 1)
      (autTowerStep_injective hZ 1) hbase
    rw [hA, MonoidHom.range_eq_map]
    exact hpush
  haveI hBnorm : ((autTowerStep G 1).range : Subgroup (autTowerType G 2)).Normal := by
    rw [range_autTowerStep]
    exact innAut.normal
  have hCA : Subgroup.centralizer (((autTowerEmb G 0 2).range :
      Subgroup (autTowerType G 2)) : Set (autTowerType G 2)) = ⊥ :=
    centralizer_eq_bot_of_inf_eq_bot_of_centralizer_eq_bot hinf hCB
  -- 数え上げ: `|G₃| ≤ |Aut(A)| = |Aut(G)| = |B|`。
  have hAG : G ≃* ↥((autTowerEmb G 0 2).range) :=
    MonoidHom.ofInjective (autTowerEmb_injective hZ 0 2)
  have hle : Nat.card (autTowerType G 2) ≤ Nat.card (autTowerType G 1) := by
    calc Nat.card (autTowerType G 2)
        ≤ Nat.card (MulAut ↥((autTowerEmb G 0 2).range)) :=
          card_le_card_mulAut_of_centralizer_eq_bot hCA
      _ = Nat.card (MulAut G) := (card_mulAut_congr hAG).symm
  have hBcard : Nat.card ↥((autTowerStep G 1).range) = Nat.card (autTowerType G 1) :=
    (Nat.card_congr (MonoidHom.ofInjective (autTowerStep_injective hZ 1)).toEquiv).symm
  have hBtop : ((autTowerStep G 1).range : Subgroup (autTowerType G 2)) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
    rw [hBcard]
    exact hle
  rwa [range_autTowerStep] at hBtop

end -- 9B.2

section /- 9B.3: G semisimple なら Aut(G) は complete (p. 285) -/

/-- `K` が `H` のすべての自己同型で保たれる (= characteristic) なら, `K` の `Aut(H)` での像
`{τ_k | k ∈ K}` は `Aut(H)` で**正規**。`α τ_k α⁻¹ = τ_{α k}` (Lemma 9.11 の計算) から。

9B.3 で `K = Inn(G) = E(Aut G)` に使う (layer は characteristic)。 -/
theorem normal_map_conj_of_map_le {H : Type*} [Group H] {K : Subgroup H}
    (hK : ∀ α : MulAut H, K.map (α : H →* H) ≤ K) :
    (K.map (MulAut.conj : H →* MulAut H)).Normal := by
  refine ⟨fun n hn α => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hn
  exact ⟨α k, hK α ⟨k, hk, rfl⟩, (mulAut_conj_conj α k).symm⟩

/-- **`Z(G) = 1` なら `E(Aut G) ≤ Inn(G)`** — 9A.6 (`C_H(H') ≤ H'` ⟹ `E(H) ≤ H'`) を
`H' = Inn(G)` に当てるだけ (`C_{Aut G}(Inn G) = 1` は Lemma 9.11(c))。 -/
theorem layer_mulAut_le_innAut [Finite G] (hZ : Subgroup.center G = ⊥) :
    layer (MulAut G) ≤ innAut G := by
  refine layer_le_of_centralizer_le ?_
  rw [centralizer_innAut_eq_bot hZ]
  exact bot_le

/-- `S ⊴ G` なら `S.map conj` は `Inn(G)` に正規化される
(`τ_{g} τ_s τ_{g}⁻¹ = τ_{g s g⁻¹}` と `S` の正規性)。 -/
theorem innAut_le_normalizer_map_conj {S : Subgroup G} [S.Normal] :
    innAut G ≤ Subgroup.normalizer ((S.map (MulAut.conj : G →* MulAut G) :
      Subgroup (MulAut G)) : Set (MulAut G)) := by
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
  have hcomp : ((MulAut.conj (MulAut.conj g : MulAut G)).toMonoidHom.comp
      (MulAut.conj : G →* MulAut G))
      = (MulAut.conj : G →* MulAut G).comp (MulAut.conj g).toMonoidHom :=
    MonoidHom.ext fun s => mulAut_conj_conj (MulAut.conj g) s
  rw [show ((MulAut.conj (MulAut.conj g : MulAut G)) : MulAut G →* MulAut G)
      = (MulAut.conj (MulAut.conj g : MulAut G)).toMonoidHom from rfl, hcomp,
    ← Subgroup.map_map, map_conj_eq_self_of_normal]

/-- **`G` semisimple なら `Inn(G) ≤ E(Aut G)`**: `G` の単純正規因子 `S` の像
`S.map conj` は `S ⊴ Inn G ⊴ Aut G` で subnormal かつ quasisimple, すなわち
`Aut(G)` の component。 -/
theorem innAut_le_layer_mulAut [Finite G] (hss : IsSemisimpleGroup G) :
    innAut G ≤ layer (MulAut G) := by
  obtain ⟨𝒳, h𝒳, hsup⟩ := hss
  have hZ : Subgroup.center G = ⊥ := center_eq_bot_of_semisimpleFamily h𝒳 hsup
  have hIm : innAut G = (sSup 𝒳).map (MulAut.conj : G →* MulAut G) := by
    rw [hsup, ← MonoidHom.range_eq_map]
    rfl
  rw [hIm, (Subgroup.gc_map_comap (MulAut.conj : G →* MulAut G)).l_sSup]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSnorm, hSsimple, hSnab⟩ := h𝒳 S hS
  haveI := hSnorm
  have hle : S.map (MulAut.conj : G →* MulAut G) ≤ innAut G := Subgroup.map_le_range _ _
  have e : ↥S ≃* ↥(S.map (MulAut.conj : G →* MulAut G)) :=
    Subgroup.equivMapOfInjective S _ (conj_injective hZ)
  refine IsComponent.le_layer ⟨?_, ?_⟩
  · refine Subgroup.IsSubnormal.trans hle ?_ (innAut.normal (G := G)).isSubnormal
    exact Subgroup.Normal.isSubnormal
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr innAut_le_normalizer_map_conj)
  · haveI := hSsimple
    refine isQuasisimple_of_isSimpleGroup_not_isMulCommutative e.symm.isSimpleGroup ?_
    exact fun _ => hSnab (isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.surjective)

/-- **Isaacs Problem 9B.3** (書籍 p. 285) ⭐: `G` が semisimple なら `Aut(G)` は
**complete**, したがって `G` の automorphism tower は高々 2 種類の群しか含まない。

`E(Aut G) = Inn(G)` (`≤` は 9A.6, `≥` は各単純正規因子が component) で `Inn(G)` は
layer ゆえ characteristic, すると `G` の像が `G₃` で正規になり 9B.2 が使える。 -/
theorem isCompleteGroup_mulAut_of_isSemisimpleGroup [Finite G] (hss : IsSemisimpleGroup G) :
    IsCompleteGroup (MulAut G) := by
  have hZ : Subgroup.center G = ⊥ := hss.center_eq_bot
  have hEq : layer (MulAut G) = innAut G :=
    le_antisymm (layer_mulAut_le_innAut hZ) (innAut_le_layer_mulAut hss)
  have hchar : ∀ α : MulAut (MulAut G),
      (innAut G).map (α : MulAut G →* MulAut G) ≤ innAut G := by
    intro α
    rw [← hEq]
    exact le_of_eq (map_layer_mulEquiv α)
  have hnormal : ((autTowerEmb G 0 2).range).Normal := by
    rw [range_autTowerEmb_two]
    exact normal_map_conj_of_map_le hchar
  exact isCompleteGroup_autTowerType_one_of_normal_range hZ hnormal

end -- 9B.3

section /- 9B.5: G = AB (A, B subnormal) なら G^∞ = A^∞ B^∞ (p. 285) -/

/-- **9B.5 の base case** (書籍 hint の第 1 段): `A, B ⊴ G` で `G = AB` なら
`G^∞ = A^∞ B^∞`。

`N := A^∞ ⊔ B^∞` は正規で, `G/N` は正規冪零部分群 2 つ (`A`, `B` の像) の積なので
どちらも `F(G/N)` に入り `F(G/N) = ⊤`, すなわち `G/N` は冪零。ゆえに `G^∞ ≤ N`。
逆の包含は `nilpotentResidual_mono`。 -/
theorem nilpotentResidual_top_eq_sup_of_normal [Finite G] {A B : Subgroup G}
    [A.Normal] [B.Normal] (hAB : A ⊔ B = ⊤) :
    nilpotentResidual (⊤ : Subgroup G) = nilpotentResidual A ⊔ nilpotentResidual B := by
  refine le_antisymm ?_
    (sup_le (nilpotentResidual_mono le_top) (nilpotentResidual_mono le_top))
  set N := nilpotentResidual A ⊔ nilpotentResidual B with hNdef
  rw [nilpotentResidual_le_iff_isNilpotent_map,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  -- `A`, `B` の像は正規冪零。
  haveI hAnil : Group.IsNilpotent ↥(A.map (QuotientGroup.mk' N)) :=
    nilpotentResidual_le_iff_isNilpotent_map.mp le_sup_left
  haveI hBnil : Group.IsNilpotent ↥(B.map (QuotientGroup.mk' N)) :=
    nilpotentResidual_le_iff_isNilpotent_map.mp le_sup_right
  haveI : (A.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  haveI : (B.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  -- 両方 `F(G/N)` に入り, 生成するので `F(G/N) = ⊤`。
  have htop : (⊤ : Subgroup (G ⧸ N)) ≤ Ch01.fitting (G ⧸ N) := by
    rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N), ← hAB, Subgroup.map_sup]
    exact sup_le Ch01.nilpotent_normal_le_fitting Ch01.nilpotent_normal_le_fitting
  haveI := Ch01.fitting.isNilpotent (G := G ⧸ N)
  exact Group.nilpotent_of_mulEquiv (MulEquiv.subgroupCongr (top_le_iff.mp htop))

/-- 9B.5 の帰納核: `Nat.card G ≤ n` の有限群で `A, B ◁◁ G`, `G = AB` ⟹
`G^∞ ≤ A^∞ ⊔ B^∞`。`∀ G` を内側に量化して `n` で帰納 (Lemma 9.15 の核と同型)。 -/
private theorem nilpotentResidual_sup_aux.{u} (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ {A B : Subgroup G}, A.IsSubnormal → B.IsSubnormal →
        (A : Set G) * (B : Set G) = Set.univ →
        nilpotentResidual (⊤ : Subgroup G) ≤ nilpotentResidual A ⊔ nilpotentResidual B := by
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro G _ _ hcard A B hA hB hprod
    have hjoin : A ⊔ B = ⊤ := by
      refine top_le_iff.mp fun g _ => ?_
      have hg : g ∈ (A : Set G) * (B : Set G) := by rw [hprod]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    rcases hA.lt_normal with rfl | ⟨A₁, hA₁norm, hAA₁, hA₁lt⟩
    · exact le_sup_of_le_left (nilpotentResidual_mono le_top)
    rcases hB.lt_normal with rfl | ⟨B₁, hB₁norm, hBB₁, hB₁lt⟩
    · exact le_sup_of_le_right (nilpotentResidual_mono le_top)
    haveI := hA₁norm
    haveI := hB₁norm
    have hA₁B₁ : A₁ ⊔ B₁ = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hjoin]
      exact sup_le_sup hAA₁ hBB₁
    rw [nilpotentResidual_top_eq_sup_of_normal hA₁B₁]
    -- `X₁ < ⊤` なら `|X₁| ≤ n`。
    have hcard_lt : ∀ {X : Subgroup G}, X < ⊤ → Nat.card ↥X ≤ n := by
      intro X hX
      have hne : Nat.card ↥X ≠ Nat.card G := fun h => hX.ne (Subgroup.eq_top_of_card_eq _ h)
      have hle := Subgroup.card_le_card_group X
      omega
    -- `X ≤ X₁` のとき `X₁ = X (Y ⊓ X₁)` (Dedekind) を `↥X₁` の積として持ち上げる。
    have hprod_sub : ∀ {X Y X₁ : Subgroup G}, X ≤ X₁ →
        (X : Set G) * (Y : Set G) = Set.univ →
        ((X.subgroupOf X₁ : Subgroup ↥X₁) : Set ↥X₁) *
          (((Y ⊓ X₁).subgroupOf X₁ : Subgroup ↥X₁) : Set ↥X₁) = Set.univ := by
      intro X Y X₁ hXX₁ hXY
      ext x
      simp only [Set.mem_univ, iff_true]
      have hx : (x : G) ∈ (X : Set G) * (Y : Set G) := by rw [hXY]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      have haX₁ : a ∈ X₁ := hXX₁ ha
      have hbX₁ : b ∈ X₁ := by
        have hbe : b = a⁻¹ * (x : G) := by rw [← hab]; group
        rw [hbe]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haX₁) x.2
      exact ⟨⟨a, haX₁⟩, ha, ⟨b, hbX₁⟩, ⟨hb, hbX₁⟩, Subtype.ext hab⟩
    refine sup_le ?_ ?_
    · -- `A₁^∞ ≤ A^∞ ⊔ (B ⊓ A₁)^∞ ≤ A^∞ ⊔ B^∞`
      have hIHA := IH ↥A₁ (hcard_lt hA₁lt) hA.subgroupOf
        (hB.inf hA₁norm.isSubnormal).subgroupOf (hprod_sub hAA₁ hprod)
      have hm := Subgroup.map_mono (f := A₁.subtype) hIHA
      rw [map_subtype_nilpotentResidual_top, Subgroup.map_sup,
        map_subtype_nilpotentResidual_subgroupOf hAA₁,
        map_subtype_nilpotentResidual_subgroupOf (inf_le_right : B ⊓ A₁ ≤ A₁)] at hm
      exact hm.trans (sup_le le_sup_left
        ((nilpotentResidual_mono inf_le_left).trans le_sup_right))
    · -- 対称
      have hprodBA : (B : Set G) * (A : Set G) = Set.univ := by
        ext g
        simp only [Set.mem_univ, iff_true]
        have hg : g⁻¹ ∈ (A : Set G) * (B : Set G) := by rw [hprod]; trivial
        obtain ⟨a, ha, b, hb, hab⟩ := hg
        have hab' : a * b = g⁻¹ := hab
        refine ⟨b⁻¹, Subgroup.inv_mem _ hb, a⁻¹, Subgroup.inv_mem _ ha, ?_⟩
        change b⁻¹ * a⁻¹ = g
        rw [← mul_inv_rev, hab', inv_inv]
      have hIHB := IH ↥B₁ (hcard_lt hB₁lt) hB.subgroupOf
        (hA.inf hB₁norm.isSubnormal).subgroupOf (hprod_sub hBB₁ hprodBA)
      have hm := Subgroup.map_mono (f := B₁.subtype) hIHB
      rw [map_subtype_nilpotentResidual_top, Subgroup.map_sup,
        map_subtype_nilpotentResidual_subgroupOf hBB₁,
        map_subtype_nilpotentResidual_subgroupOf (inf_le_right : A ⊓ B₁ ≤ B₁)] at hm
      exact hm.trans (sup_le le_sup_right
        ((nilpotentResidual_mono inf_le_left).trans le_sup_left))

/-- **Isaacs Problem 9B.5** (書籍 p. 285) ⭐: `G = AB` で `A, B ⊲⊲ G` (**subnormal**)
なら `G^∞ = A^∞ B^∞`。

書籍 hint どおり「まず両方 normal の場合 (`nilpotentResidual_top_eq_sup_of_normal`)、
次に `|G|` の帰納法」。帰納段は `A ≤ A₁ ◁ G`, `A₁ < ⊤` (subnormal 性) を取って
base case で `G^∞ = A₁^∞ ⊔ B₁^∞` とし、Dedekind (`A₁ = A (B ⊓ A₁)`) で `A₁` に帰納法を
当てる。⚠ 仮説は join でなく**積** `(A : Set G) * B = Set.univ` — Dedekind が
積の恒等式なので join では回らない (部分群束は一般に modular でない)。 -/
theorem nilpotentResidual_top_eq_sup_of_isSubnormal [Finite G] {A B : Subgroup G}
    (hA : A.IsSubnormal) (hB : B.IsSubnormal)
    (hprod : (A : Set G) * (B : Set G) = Set.univ) :
    nilpotentResidual (⊤ : Subgroup G) = nilpotentResidual A ⊔ nilpotentResidual B :=
  le_antisymm (nilpotentResidual_sup_aux (Nat.card G) G le_rfl hA hB hprod)
    (sup_le (nilpotentResidual_mono le_top) (nilpotentResidual_mono le_top))

end -- 9B.5

section /- 9B.4 の部品: D_{2n} (n 奇数) の回転部分群 (p. 285) -/

/-- **`n` 奇数なら `D_{2n}` で `x ^ n = 1` ⟺ `x` は回転** (`r i` の形)。

回転は `(r i)^n = r (n • i) = r 0 = 1`、鏡映は位数 2 で `n` が奇数なので
`(sr i)^n = sr i ≠ 1`。これで「回転全体」= `{x | x ^ n = 1}` は自己同型で保たれる
(= characteristic) ことが分かり、`Aut(D_{2n}) → Aut(Z/n)` を作る足場になる。 -/
theorem dihedral_pow_eq_one_iff_exists_r {n : ℕ} (hodd : Odd n) (x : DihedralGroup n) :
    x ^ n = 1 ↔ ∃ i : ZMod n, x = DihedralGroup.r i := by
  cases x with
  | r i =>
    refine ⟨fun _ => ⟨i, rfl⟩, fun _ => ?_⟩
    rw [DihedralGroup.r_pow]
    simp
  | sr i =>
    constructor
    · intro hx
      exfalso
      have h2 : (2 : ℕ) ∣ n := by
        have hdvd := orderOf_dvd_of_pow_eq_one hx
        rwa [DihedralGroup.orderOf_sr] at hdvd
      obtain ⟨k, hk⟩ := hodd
      omega
    · rintro ⟨j, hj⟩
      simp at hj

end -- 9B.4 の部品

end OddOrder.Isaacs.Ch09
