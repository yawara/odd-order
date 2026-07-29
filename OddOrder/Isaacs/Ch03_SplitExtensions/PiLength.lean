/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# `π`-length (upper `π`-series)

Isaacs Problem 3D.1(b) (`G` の `p`-length ≤ Sylow `p`-部分群の冪零類) のための基盤。

`G` の **upper `π`-series** は
`O_{π'}(G) ≤ O_{π',π}(G) ≤ O_{π',π,π'}(G) ≤ …`
で, `π`-因子を `k` 個積んだ段が `⊤` に達するとき `π`-length ≤ `k` という。

実装では「正規部分群 `N` の上の `π`-core」`oPiCoreOver π N`
(= `O_π(G/N)` の `G` における逆像) を `dite` で全域化し, それを交互に適用して
`piUpperSeries` を定義する。`N` が正規でないときの値は使わない (`⊤` にしておく)。

* `piUpperSeries π G 0 = O_{π'}(G)`
* `piUpperSeries π G 1 = O_{π',π,π'}(G)` (= BG の `oPiPrimePiPiPrimeCore`)

したがって `HasPiLengthLE π G 1` は BG の `HasPiLengthOne` と同値
(BG は Ch03 の下流なのでここでは参照しない)。

## Main definitions

- `oPiCoreOver` — 正規部分群の上の `π`-core。
- `piUpperSeries` — upper `π`-series。
- `HasPiLengthLE` — `π`-length ≤ `k`。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup

section /- 3D: π-length -/

variable {G : Type*} [Group G]

open Classical in
/-- **正規部分群 `N` の上の `π`-core**: `O_π(G/N)` の `G` における逆像。

`N` が正規でないときは `⊤` (この値は使わない)。 -/
noncomputable def oPiCoreOver (π : Set ℕ) (N : Subgroup G) : Subgroup G :=
  if h : N.Normal then
    haveI := h
    Subgroup.comap (QuotientGroup.mk' N) (oPiCore π (G ⧸ N))
  else ⊤

theorem oPiCoreOver_of_normal (π : Set ℕ) (N : Subgroup G) [hN : N.Normal] :
    oPiCoreOver π N = Subgroup.comap (QuotientGroup.mk' N) (oPiCore π (G ⧸ N)) := by
  classical
  rw [oPiCoreOver, dif_pos hN]

instance oPiCoreOver.normal (π : Set ℕ) (N : Subgroup G) : (oPiCoreOver π N).Normal := by
  classical
  rw [oPiCoreOver]
  split
  · rename_i h
    haveI := h
    infer_instance
  · infer_instance

/-- `N ≤ O_π(G/N)` の逆像。 -/
theorem le_oPiCoreOver (π : Set ℕ) (N : Subgroup G) [N.Normal] : N ≤ oPiCoreOver π N := by
  rw [oPiCoreOver_of_normal]
  intro x hx
  rw [Subgroup.mem_comap, show (QuotientGroup.mk' N) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

/-- **upper `π`-series**: `piUpperSeries π G k` は `π`-因子を `k` 個積んだ段。

`piUpperSeries π G 0 = O_{π'}(G)`, `piUpperSeries π G (k+1)` は 1 段の
`O_π` と `O_{π'}` を積んだもの。 -/
noncomputable def piUpperSeries (π : Set ℕ) (G : Type*) [Group G] : ℕ → Subgroup G
  | 0 => oPiCore {q | q ∉ π} G
  | k + 1 => oPiCoreOver {q | q ∉ π} (oPiCoreOver π (piUpperSeries π G k))

instance piUpperSeries.normal (π : Set ℕ) (G : Type*) [Group G] (k : ℕ) :
    (piUpperSeries π G k).Normal := by
  cases k with
  | zero => rw [piUpperSeries]; infer_instance
  | succ n => rw [piUpperSeries]; infer_instance

theorem piUpperSeries_zero (π : Set ℕ) (G : Type*) [Group G] :
    piUpperSeries π G 0 = oPiCore {q | q ∉ π} G := rfl

theorem piUpperSeries_succ (π : Set ℕ) (G : Type*) [Group G] (k : ℕ) :
    piUpperSeries π G (k + 1)
      = oPiCoreOver {q | q ∉ π} (oPiCoreOver π (piUpperSeries π G k)) := rfl

/-- `O_π` を `O_{π'}(G)` の上に積むと `O_{π',π}(G)`。 -/
theorem oPiCoreOver_oPiCore_compl (π : Set ℕ) (G : Type*) [Group G] :
    oPiCoreOver π (oPiCore {q | q ∉ π} G) = oPiPrimePiCore π G := by
  rw [oPiCoreOver_of_normal, oPiPrimePiCore]

/-- `piUpperSeries π G 1 = O_{π',π,π'}(G)` (BG の `oPiPrimePiPiPrimeCore` と一致)。 -/
theorem piUpperSeries_one (π : Set ℕ) (G : Type*) [Group G] :
    piUpperSeries π G 1
      = oPiCoreOver {q | q ∉ π} (oPiPrimePiCore π G) := by
  rw [piUpperSeries_succ, piUpperSeries_zero, oPiCoreOver_oPiCore_compl]

/-- upper `π`-series は単調増加。 -/
theorem piUpperSeries_monotone (π : Set ℕ) (G : Type*) [Group G] :
    Monotone (piUpperSeries π G) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [piUpperSeries_succ]
  exact (le_oPiCoreOver π _).trans (le_oPiCoreOver {q | q ∉ π} _)

/-- **`π`-length ≤ `k`**: upper `π`-series の第 `k` 段が `⊤` に達する。 -/
def HasPiLengthLE (π : Set ℕ) (G : Type*) [Group G] (k : ℕ) : Prop :=
  piUpperSeries π G k = ⊤

theorem HasPiLengthLE.mono {π : Set ℕ} {G : Type*} [Group G] {j k : ℕ} (hjk : j ≤ k)
    (h : HasPiLengthLE π G j) : HasPiLengthLE π G k :=
  eq_top_iff.mpr (h ▸ piUpperSeries_monotone π G hjk)

/-- `π'`-群は `π`-length `0`。 -/
theorem hasPiLengthLE_zero_of_isPiGroup [Finite G] {π : Set ℕ}
    (h : IsPiGroup {q | q ∉ π} G) : HasPiLengthLE π G 0 := by
  rw [HasPiLengthLE, piUpperSeries_zero, eq_top_iff]
  have htop : Subgroup.IsPiGroup {q | q ∉ π} (⊤ : Subgroup G) := by
    intro q hq
    refine h q ?_
    rwa [Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv] at hq
  exact Subgroup.IsPiGroup.le_oPiCore htop

/-! ### 商への shift (`π`-length の帰納の要) -/

/-- **`oPiCoreOver` は商と可換**: `M ≤ N` (ともに `G` に正規) のとき
`O_π(G/N)` の逆像は `G/M` の中で `O_π((G/M)/(N/M))` の逆像に一致する。

Noether 第三同型 (`QuotientGroup.quotientQuotientEquivQuotient`) と
`oPiCore.map_eq_of_mulEquiv` による。 -/
theorem oPiCoreOver_eq_comap_map (π : Set ℕ) {M N : Subgroup G} [M.Normal] [N.Normal]
    (hMN : M ≤ N) :
    oPiCoreOver π N
      = (oPiCoreOver π (N.map (QuotientGroup.mk' M))).comap (QuotientGroup.mk' M) := by
  haveI hNbar : (N.map (QuotientGroup.mk' M)).Normal :=
    (inferInstance : N.Normal).map _ (QuotientGroup.mk'_surjective M)
  set e := QuotientGroup.quotientQuotientEquivQuotient M N hMN with he
  have hoPi : (oPiCore π (G ⧸ N)).comap
      (e : ((G ⧸ M) ⧸ N.map (QuotientGroup.mk' M)) →* G ⧸ N)
      = oPiCore π ((G ⧸ M) ⧸ N.map (QuotientGroup.mk' M)) := by
    rw [← oPiCore.map_eq_of_mulEquiv π e]
    exact Subgroup.comap_map_eq_self_of_injective e.injective _
  have hcomp : (e : ((G ⧸ M) ⧸ N.map (QuotientGroup.mk' M)) →* G ⧸ N).comp
      ((QuotientGroup.mk' (N.map (QuotientGroup.mk' M))).comp (QuotientGroup.mk' M))
      = QuotientGroup.mk' N := by
    ext x
    exact QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk M N hMN x
  rw [oPiCoreOver_of_normal, oPiCoreOver_of_normal, ← hoPi, Subgroup.comap_comap,
    Subgroup.comap_comap, hcomp]

/-- `O_{π',π}(G)` は upper `π`-series の第 `k+1` 段に含まれる。 -/
theorem oPiPrimePiCore_le_piUpperSeries_succ (π : Set ℕ) (G : Type*) [Group G] (k : ℕ) :
    oPiPrimePiCore π G ≤ piUpperSeries π G (k + 1) := by
  refine le_trans ?_ (piUpperSeries_monotone π G (Nat.succ_le_succ (Nat.zero_le k)))
  rw [piUpperSeries_one]
  exact le_oPiCoreOver _ _

/-- **upper `π`-series の shift**: `M := O_{π',π}(G)` とおくと
`piUpperSeries π G (k+1)` は `G/M` の第 `k` 段の逆像。

これが「`π`-length は `G/O_{π',π}(G)` に移ると 1 減る」の形式化。 -/
theorem piUpperSeries_succ_eq_comap (π : Set ℕ) (G : Type*) [Group G] (k : ℕ) :
    piUpperSeries π G (k + 1)
      = (piUpperSeries π (G ⧸ oPiPrimePiCore π G) k).comap
          (QuotientGroup.mk' (oPiPrimePiCore π G)) := by
  induction k with
  | zero =>
    rw [piUpperSeries_succ, piUpperSeries_zero, piUpperSeries_zero, oPiCoreOver_oPiCore_compl,
      oPiCoreOver_of_normal]
  | succ n ih =>
    have hMle : oPiPrimePiCore π G ≤ piUpperSeries π G (n + 1) :=
      oPiPrimePiCore_le_piUpperSeries_succ π G n
    have hmap : (piUpperSeries π G (n + 1)).map
        (QuotientGroup.mk' (oPiPrimePiCore π G)) = piUpperSeries π (G ⧸ oPiPrimePiCore π G) n := by
      rw [ih]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective _) _
    have hinner : oPiCoreOver π (piUpperSeries π G (n + 1))
        = (oPiCoreOver π (piUpperSeries π (G ⧸ oPiPrimePiCore π G) n)).comap
            (QuotientGroup.mk' (oPiPrimePiCore π G)) := by
      rw [oPiCoreOver_eq_comap_map π hMle, hmap]
    have hMle' : oPiPrimePiCore π G ≤ oPiCoreOver π (piUpperSeries π G (n + 1)) :=
      hMle.trans (le_oPiCoreOver π _)
    have hmap' : (oPiCoreOver π (piUpperSeries π G (n + 1))).map
        (QuotientGroup.mk' (oPiPrimePiCore π G))
        = oPiCoreOver π (piUpperSeries π (G ⧸ oPiPrimePiCore π G) n) := by
      rw [hinner]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    rw [piUpperSeries_succ π G (n + 1), piUpperSeries_succ π (G ⧸ oPiPrimePiCore π G) n,
      oPiCoreOver_eq_comap_map {q | q ∉ π} hMle', hmap']

end -- 3D: π-length

end OddOrder.Isaacs.Ch03
