/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.PiParts
import OddOrder.GroupTheory.FittingSelfCentralizing

/-!
# Isaacs Problem 3C.8 — nilpotent injector の定義と `C(p)`

Isaacs, *Finite Group Theory*, Problem 3C.8 (書籍 p. 91):

> Let `G` be solvable. A nilpotent injector of `G` is a nilpotent subgroup `I` containing
> the Fitting subgroup `F(G)`, and maximal with this property. Prove that all nilpotent
> injectors of `G` are conjugate in `G`.

書籍は証明を与えない (3C.7 と同じ challenge problem)。証明は **Mann の構造定理**の経路を採る:
素数 `p` ごとに `F_{p'} :=` `F(G)` の `{p}ᶜ`-部分 (`fittingPPrimePart`) と
`C(p) := C_G(F_{p'})` (`pCentralizer`) を置くと,

* `F_{p'}` と `C(p)` はともに `G` に正規,
* `F(G)` を含む任意の冪零部分群 `K` の `{p}`-部分は `C(p)` に入り,
  実は `C(p)` の Sylow `p`-部分群になる,
* `p ≠ q` なら `[C(p), C(q)] ≤ Z(F(G))`,

が成り立ち、これらから injector は「各 `p` で `C(p)` の Sylow `p`-部分群を選ぶ」ことに
対応し、共役性が素数ごとの Sylow 共役性に帰着する。

本ファイルは定義と、上記のうち**正規性**および `[C(p), C(q)] ≤ Z(F)` の土台
(`fitting_le_sup_fittingPPrimePart` / `pCentralizer_inf_le_centralizer_fitting`) を置く。

## Main results

- `IsNilpotentInjector` — 定義。
- `fittingPPrimePart` / `pCentralizer` — Mann の `F_{p'}` と `C(p)`。
- `fittingPPrimePart_normal` / `pCentralizer_normal` — ともに `G` に正規。
- `fitting_le_sup_fittingPPrimePart` — `p ≠ q` なら `F(G) ≤ F_{p'} ⊔ F_{q'}`。
- `nilPiPart_singleton_le_pCentralizer` — `F(G)` を含む冪零部分群の `{p}`-部分は `C(p)` に入る。
- `pCentralizer_inf_le_centralizer_fitting` — `p ≠ q` なら `C(p) ⊓ C(q) ≤ C_G(F(G))`。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C.8: nilpotent injector -/

variable {G : Type*} [Group G]

/-- **Nilpotent injector** (Isaacs Problem 3C.8, 書籍 p. 91): `F(G)` を含む冪零部分群で,
その性質について極大なもの。

`I` を含む冪零部分群は自動的に `F(G)` を含むので、極大性の条件は
「`I` を含む冪零部分群は `I` のみ」でよい。 -/
def IsNilpotentInjector (I : Subgroup G) : Prop :=
  Group.IsNilpotent ↥I ∧ Ch01.fitting G ≤ I ∧
    ∀ J : Subgroup G, I ≤ J → Group.IsNilpotent ↥J → J = I

theorem IsNilpotentInjector.isNilpotent {I : Subgroup G} (h : IsNilpotentInjector I) :
    Group.IsNilpotent ↥I := h.1

theorem IsNilpotentInjector.fitting_le {I : Subgroup G} (h : IsNilpotentInjector I) :
    Ch01.fitting G ≤ I := h.2.1

theorem IsNilpotentInjector.eq_of_le {I J : Subgroup G} (h : IsNilpotentInjector I)
    (hIJ : I ≤ J) (hJ : Group.IsNilpotent ↥J) : J = I := h.2.2 J hIJ hJ

/-- **Mann の `F_{p'}`**: Fitting 部分群 `F(G)` の `{p}ᶜ`-部分。 -/
def fittingPPrimePart (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  nilPiPart (Ch01.fitting G) ({p}ᶜ)

/-- **Mann の `C(p)`**: `C_G(F_{p'})`。 -/
def pCentralizer (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  Subgroup.centralizer ((fittingPPrimePart G p : Subgroup G) : Set G)

theorem isNilpotentPiPart_fittingPPrimePart [Finite G] [IsSolvable G] (p : ℕ) :
    IsNilpotentPiPart (Ch01.fitting G) (fittingPPrimePart G p) ({p}ᶜ) :=
  isNilpotentPiPart_nilPiPart _ inferInstance

theorem fittingPPrimePart_le [Finite G] [IsSolvable G] (p : ℕ) :
    fittingPPrimePart G p ≤ Ch01.fitting G := (isNilpotentPiPart_fittingPPrimePart p).le

/-- `F_{p'}` は共役で不変 (`F(G)` が正規で `π`-部分が一意だから)。 -/
theorem fittingPPrimePart_map_conj [Finite G] [IsSolvable G] (p : ℕ) (g : G) :
    (fittingPPrimePart G p).map (MulAut.conj g).toMonoidHom = fittingPPrimePart G p := by
  have hconj : (Ch01.fitting G).map (MulAut.conj g).toMonoidHom = Ch01.fitting G :=
    Subgroup.Normal.map_conj_eq (Ch01.fitting G) g
  have := nilPiPart_map_conj (N := Ch01.fitting G) ({p}ᶜ) inferInstance g
  rw [hconj] at this
  exact this.symm

instance fittingPPrimePart_normal [Finite G] [IsSolvable G] (p : ℕ) :
    (fittingPPrimePart G p).Normal :=
  Subgroup.normal_iff_map_conj_eq.mpr fun g => fittingPPrimePart_map_conj p g

/-- 正規部分群の中心化群は正規。 -/
theorem normal_centralizer {N : Subgroup G} (hN : N.Normal) :
    (Subgroup.centralizer (N : Set G)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have hg : g⁻¹ * h * g ∈ N := by simpa using hN.conj_mem h hh g⁻¹
  have := hx _ hg
  calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
    _ = (g * x * g⁻¹) * h := by group

instance pCentralizer_normal [Finite G] [IsSolvable G] (p : ℕ) : (pCentralizer G p).Normal :=
  normal_centralizer inferInstance

/-- `p ≠ q` なら `F(G)` の `{p}`-部分は `F_{q'}` に入る (`{p}`-群は `{q}ᶜ`-群)。 -/
theorem nilPiPart_singleton_le_fittingPPrimePart [Finite G] [IsSolvable G] {p q : ℕ}
    (hpq : p ≠ q) : nilPiPart (Ch01.fitting G) ({p} : Set ℕ) ≤ fittingPPrimePart G q := by
  have hp := isNilpotentPiPart_nilPiPart (N := Ch01.fitting G) ({p} : Set ℕ) inferInstance
  refine le_nilPiPart_of_isPiGroup inferInstance hp.1 (fun r hr => ?_)
  have hrp : r = p := by simpa using hp.isPiGroup r hr
  simpa [hrp] using hpq

/-- `p ≠ q` なら `F(G) ≤ F_{p'} ⊔ F_{q'}`。

`F(G) = F_p ⊔ F_{p'}` (`IsNilpotentPiPart.sup_eq`) で `F_p ≤ F_{q'}`。 -/
theorem fitting_le_sup_fittingPPrimePart [Finite G] [IsSolvable G] {p q : ℕ} (hpq : p ≠ q) :
    Ch01.fitting G ≤ fittingPPrimePart G p ⊔ fittingPPrimePart G q := by
  have hsup : nilPiPart (Ch01.fitting G) ({p} : Set ℕ) ⊔ fittingPPrimePart G p
      = Ch01.fitting G :=
    IsNilpotentPiPart.sup_eq (isNilpotentPiPart_nilPiPart _ inferInstance)
      (isNilpotentPiPart_fittingPPrimePart p)
  rw [← hsup]
  exact sup_le ((nilPiPart_singleton_le_fittingPPrimePart hpq).trans le_sup_right) le_sup_left

/-- **Mann**: `F(G)` を含む冪零部分群 `K` の `{p}`-部分は `C(p)` に入る。

`F_{p'}` は `K` の `{p}ᶜ`-部分 `B` に含まれ (`le_nilPiPart_of_isPiGroup`)、`K` が冪零なので
`{p}`-部分は `B` と元ごとに可換 (`IsNilpotentPiPart.commute`)。よって `{p}`-部分は
`F_{p'}` を中心化する。 -/
theorem nilPiPart_singleton_le_pCentralizer [Finite G] [IsSolvable G] {K : Subgroup G}
    (hK : Group.IsNilpotent ↥K) (hFK : Ch01.fitting G ≤ K) (p : ℕ) :
    nilPiPart K ({p} : Set ℕ) ≤ pCentralizer G p := by
  have hA := isNilpotentPiPart_nilPiPart (N := K) ({p} : Set ℕ) hK
  have hB := isNilpotentPiPart_nilPiPart (N := K) (({p} : Set ℕ)ᶜ) hK
  have hFB : fittingPPrimePart G p ≤ nilPiPart K (({p} : Set ℕ)ᶜ) :=
    le_nilPiPart_of_isPiGroup hK ((fittingPPrimePart_le p).trans hFK)
      (isNilpotentPiPart_fittingPPrimePart p).isPiGroup
  intro x hx
  rw [pCentralizer, Subgroup.mem_centralizer_iff]
  intro h hh
  exact (IsNilpotentPiPart.commute hK hA hB x hx h (hFB hh)).symm

/-- 2 つの部分群の中心化群の交わりは、それらの生成する部分群の中心化群。 -/
theorem centralizer_inf_le_centralizer_sup (A B : Subgroup G) :
    Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G)
      ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_iff] at hxA hxB ⊢
  -- `A ⊔ B` は `x` を中心化する元からなる部分群に含まれる。
  have key : (A ⊔ B : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr (by rintro y rfl; exact (hxA a ha).symm))
      (fun b hb => Subgroup.mem_centralizer_iff.mpr (by rintro y rfl; exact (hxB b hb).symm))
  intro h hh
  exact (Subgroup.mem_centralizer_iff.mp (key hh) x rfl).symm

/-- `p ≠ q` なら `C(p) ⊓ C(q) ≤ C_G(F(G))`。 -/
theorem pCentralizer_inf_le_centralizer_fitting [Finite G] [IsSolvable G] {p q : ℕ}
    (hpq : p ≠ q) :
    pCentralizer G p ⊓ pCentralizer G q
      ≤ Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G) :=
  le_trans (centralizer_inf_le_centralizer_sup _ _)
    (Subgroup.centralizer_le (by
      exact_mod_cast (fitting_le_sup_fittingPPrimePart hpq :
        Ch01.fitting G ≤ fittingPPrimePart G p ⊔ fittingPPrimePart G q)))

end -- 3C.8

end OddOrder.Isaacs.Ch03
