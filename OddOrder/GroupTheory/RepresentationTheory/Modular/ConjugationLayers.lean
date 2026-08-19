/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import OddOrder.Algebra.GroupAlgebraConjugation
import OddOrder.GroupTheory.PRegularElement
import OddOrder.Mathlib.MonoidAlgebra

/-!
# Splitting an `h`-invariant element into `p` cyclically permuted layers

**Navarro (5.7), the combinatorial half.**  In the proof of (5.7) one has an element `w ∈ 𝒪G`
which is centralised by `h` and whose support misses `C_G(h_p)` (there, because `supp w ⊆ G ∖ H`
and `C_G(h_p) ⊆ H`).  Navarro produces `w_1, …, w_p` with

`w = ∑_i w_i`  and  `(w_i)^h = w_{i+1}`  (subscripts mod `p`),

by observing that every `⟨h⟩`-orbit on `supp w` has size divisible by `p`, so that each orbit is a
disjoint union of `p` blocks cyclically permuted by `h`.

Here is the same argument, organised around a **level function** instead of coset bookkeeping.
The point is:

> if `h^k` centralises `x` and `p ∤ k`, then `h_p` centralises `x`.

Indeed `d = gcd(k, ord h)` is prime to `p`, hence divides the `p'`-part `m` of `ord h`, hence
divides the exponent `m·B` defining `h_p`; Bézout then writes that exponent inside `kℤ + (ord h)ℤ`,
so `h_p` is a power of `h^k` (`pPart_mem_zpowers_zpow`).  For `x` in the support this is excluded,
so the stabiliser of `x` in `⟨h⟩` consists of the `h^k` with `p ∣ k`.  Writing
`x = h^k · r · h^{-k}` for the chosen representative `r` of the `⟨h⟩`-conjugacy orbit of `x`, the
class `k mod p` is therefore independent of the choice of `k`: that class is `conjLevel p h x`, and
it visibly increases by `1` under conjugation by `h`.  The layers are the level sets.

## Main results

* `OddOrder.GroupTheory.pPart_mem_zpowers_zpow` — `p ∤ k` makes `h_p` a power of `h^k`
* `OddOrder.GroupTheory.dvd_of_commute_zpow` — the stabiliser lies in `⟨h^p⟩`
* `OddOrder.GroupTheory.conjLevel_conj` — the level increases by `1`
* `OddOrder.GroupTheory.sum_conjLayer` — `∑_i w_i = w`
* `OddOrder.GroupTheory.conjLayer_conj_smul` — `h • w_i = w_{i+1}`
-/

namespace OddOrder.GroupTheory

open scoped OddOrder.Conjugation

variable {G : Type*} [Group G] {p : ℕ}

/-! ### The stabiliser of a point off `C_G(h_p)` -/

section Stabilizer

theorem commute_pPart_zpow (h : G) (k : ℤ) : Commute (pPart p h) (h ^ k) := by
  rw [pPart]
  exact (Commute.refl h).zpow_zpow _ _

/-- **The `p`-part is a power of `h^k` whenever `p ∤ k`.**  `d = gcd(k, ord h)` is prime to `p`,
so it divides the `p'`-part of `ord h`, and hence the exponent `m·B` that defines `h_p`; Bézout
puts that exponent into `kℤ + (ord h)ℤ`. -/
theorem pPart_mem_zpowers_zpow (hp : p.Prime) {h : G} (hh : IsOfFinOrder h) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) : pPart p h ∈ Subgroup.zpowers (h ^ k) := by
  classical
  have hn0 : orderOf h ≠ 0 := (orderOf_pos_iff.mpr hh).ne'
  have hdk : ((Int.gcd k (orderOf h : ℤ) : ℕ) : ℤ) ∣ k := Int.gcd_dvd_left k _
  have hdn : ((Int.gcd k (orderOf h : ℤ) : ℕ) : ℤ) ∣ (orderOf h : ℤ) := Int.gcd_dvd_right k _
  have hpd : ¬ p ∣ Int.gcd k (orderOf h : ℤ) := fun hcon =>
    hk ((Int.natCast_dvd_natCast.mpr hcon).trans hdk)
  have hdm : Int.gcd k (orderOf h : ℤ) ∣ ordCompl[p] (orderOf h) :=
    Nat.Coprime.dvd_of_dvd_mul_left
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).pow_left
        ((orderOf h).factorization p)).symm
      (by rw [Nat.ordProj_mul_ordCompl_eq_self]; exact Int.natCast_dvd_natCast.mp hdn)
  obtain ⟨c, hc⟩ : ((Int.gcd k (orderOf h : ℤ) : ℕ) : ℤ)
      ∣ ((ordCompl[p] (orderOf h) : ℕ) : ℤ)
        * Nat.gcdB (ordProj[p] (orderOf h)) (ordCompl[p] (orderOf h)) :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hdm) _
  have hab := Int.gcd_eq_gcd_ab k (orderOf h : ℤ)
  have hexp : ((ordCompl[p] (orderOf h) : ℕ) : ℤ)
        * Nat.gcdB (ordProj[p] (orderOf h)) (ordCompl[p] (orderOf h))
      = k * (Int.gcdA k (orderOf h : ℤ) * c)
        + (orderOf h : ℤ) * (Int.gcdB k (orderOf h : ℤ) * c) := by
    rw [hc, hab]; ring
  have hkill : h ^ ((orderOf h : ℤ) * (Int.gcdB k (orderOf h : ℤ) * c)) = 1 := by
    rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨Int.gcdA k (orderOf h : ℤ) * c, ?_⟩
  rw [pPart, hexp, zpow_add, hkill, mul_one]
  exact (zpow_mul h k _).symm

/-- **The stabiliser of a point off `C_G(h_p)` sits inside `⟨h^p⟩`.** -/
theorem dvd_of_commute_zpow (hp : p.Prime) {h : G} (hh : IsOfFinOrder h) {x : G}
    (hx : ¬ Commute (pPart p h) x) {k : ℤ} (hcomm : Commute (h ^ k) x) : (p : ℤ) ∣ k := by
  by_contra hk
  obtain ⟨j, hj⟩ := pPart_mem_zpowers_zpow hp hh hk
  exact hx (hj ▸ hcomm.zpow_left j)

/-- Being centralised by `h_p` is invariant under conjugation by powers of `h`. -/
theorem commute_pPart_conj_iff (h : G) (k : ℤ) (x : G) :
    Commute (pPart p h) (h ^ k * x * (h ^ k)⁻¹) ↔ Commute (pPart p h) x := by
  have hzu : Commute (pPart p h) (h ^ k) := commute_pPart_zpow h k
  constructor
  · intro hcon
    have hx := (hzu.inv_right.mul_right hcon).mul_right hzu
    rwa [show (h ^ k)⁻¹ * (h ^ k * x * (h ^ k)⁻¹) * h ^ k = x from by group] at hx
  · exact fun hcon => (hzu.mul_right hcon).mul_right hzu.inv_right

end Stabilizer

/-! ### The level function -/

section Level

variable (h : G)

/-- Conjugacy under the powers of `h`. -/
def conjBySetoid : Setoid G where
  r x y := ∃ k : ℤ, y = h ^ k * x * (h ^ k)⁻¹
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := fun ⟨k, hk⟩ => ⟨-k, by rw [hk]; group⟩
      trans := fun ⟨k, hk⟩ ⟨l, hl⟩ => ⟨l + k, by rw [hl, hk]; group⟩ }

/-- The chosen representative of the `⟨h⟩`-conjugacy orbit of `x`. -/
noncomputable def conjRep (x : G) : G := (Quotient.mk (conjBySetoid h) x).out

theorem exists_conjRep (x : G) : ∃ k : ℤ, x = h ^ k * conjRep h x * (h ^ k)⁻¹ :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (conjBySetoid h) x))

theorem conjRep_conj (x : G) : conjRep h (h * x * h⁻¹) = conjRep h x := by
  refine congrArg Quotient.out ?_
  exact (Quotient.sound (⟨1, by group⟩ : (conjBySetoid h).r x (h * x * h⁻¹))).symm

variable (p)

/-- **The level of `x`**: the exponent, modulo `p`, of the power of `h` conjugating the chosen
representative of the orbit of `x` to `x`.  It is well defined precisely when the stabiliser of
the representative lies in `⟨h^p⟩` (`conjLevel_eq`). -/
noncomputable def conjLevel (x : G) : ZMod p := ((exists_conjRep h x).choose : ZMod p)

variable {h p}

/-- **Well-definedness of the level**: any exponent conjugating the representative to `x` computes
it, provided `x` is not centralised by `h_p`. -/
theorem conjLevel_eq (hp : p.Prime) (hh : IsOfFinOrder h) {x : G}
    (hx : ¬ Commute (pPart p h) x) {k : ℤ} (hk : x = h ^ k * conjRep h x * (h ^ k)⁻¹) :
    conjLevel p h x = (k : ZMod p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set r : G := conjRep h x with hrdef
  set k₀ : ℤ := (exists_conjRep h x).choose with hk₀def
  have hk₀ : x = h ^ k₀ * r * (h ^ k₀)⁻¹ := (exists_conjRep h x).choose_spec
  have hxr : ¬ Commute (pPart p h) r := fun hcon =>
    hx (hk₀ ▸ (commute_pPart_conj_iff h k₀ r).mpr hcon)
  have key : h ^ k * r * (h ^ k)⁻¹ = h ^ k₀ * r * (h ^ k₀)⁻¹ := hk.symm.trans hk₀
  have hstep : ((h ^ k₀)⁻¹ * h ^ k) * r = r * ((h ^ k₀)⁻¹ * h ^ k) := by
    calc ((h ^ k₀)⁻¹ * h ^ k) * r
        = (h ^ k₀)⁻¹ * (h ^ k * r * (h ^ k)⁻¹) * h ^ k := by group
      _ = (h ^ k₀)⁻¹ * (h ^ k₀ * r * (h ^ k₀)⁻¹) * h ^ k := by rw [key]
      _ = r * ((h ^ k₀)⁻¹ * h ^ k) := by group
  have hcomm : Commute (h ^ (k - k₀)) r := by
    have hrw : h ^ (k - k₀) = (h ^ k₀)⁻¹ * h ^ k := by group
    rw [hrw]; exact hstep
  have hdvd : (p : ℤ) ∣ k - k₀ := dvd_of_commute_zpow hp hh hxr hcomm
  have hzero : ((k - k₀ : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  rw [conjLevel, ← hk₀def]
  push_cast at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- **The level increases by `1` under conjugation by `h`.** -/
theorem conjLevel_conj (hp : p.Prime) (hh : IsOfFinOrder h) {x : G}
    (hx : ¬ Commute (pPart p h) x) :
    conjLevel p h (h * x * h⁻¹) = conjLevel p h x + 1 := by
  obtain ⟨k, hk⟩ := exists_conjRep h x
  have hx' : ¬ Commute (pPart p h) (h * x * h⁻¹) := fun hcon =>
    hx ((commute_pPart_conj_iff h 1 x).mp (by simpa using hcon))
  have hk' : h * x * h⁻¹ = h ^ (k + 1) * conjRep h (h * x * h⁻¹) * (h ^ (k + 1))⁻¹ := by
    rw [conjRep_conj, zpow_add, zpow_one]
    rw [show h * x * h⁻¹ = h * (h ^ k * conjRep h x * (h ^ k)⁻¹) * h⁻¹ from by rw [← hk]]
    group
  rw [conjLevel_eq hp hh hx' hk', conjLevel_eq hp hh hx hk]
  push_cast
  ring

end Level

/-! ### The layers -/

section Layers

variable {R : Type*} [CommRing R] [Fintype G]

/-- **The `i`-th layer of `w`**: the part of `w` supported on the level set `conjLevel = i`. -/
noncomputable def conjLayer (p : ℕ) (h : G) (w : MonoidAlgebra R G) (i : ZMod p) :
    MonoidAlgebra R G :=
  ∑ x : G, if conjLevel p h x = i then MonoidAlgebra.single x (w.coeff x) else 0

theorem coeff_conjLayer (h : G) (w : MonoidAlgebra R G) (i : ZMod p) (y : G) :
    (conjLayer p h w i).coeff y = if conjLevel p h y = i then w.coeff y else 0 := by
  classical
  have hsum : (conjLayer p h w i).coeff y
      = ∑ x : G, (if conjLevel p h x = i then MonoidAlgebra.single x (w.coeff x)
          else 0).coeff y := by
    rw [conjLayer]; exact MonoidAlgebra.coeff_finsetSum _ _ _
  have hzero : ((0 : MonoidAlgebra R G)).coeff y = 0 := rfl
  have hterm : ∀ x : G,
      (if conjLevel p h x = i then MonoidAlgebra.single x (w.coeff x) else 0).coeff y
        = if x = y then (if conjLevel p h x = i then w.coeff x else 0) else 0 := by
    intro x
    rw [apply_ite (fun f : MonoidAlgebra R G => f.coeff y), MonoidAlgebra.coeff_single,
      Finsupp.single_apply, hzero]
    by_cases hx : x = y
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx, ite_self]
  rw [hsum, Finset.sum_congr rfl (fun x _ => hterm x),
    Finset.sum_ite_eq' Finset.univ y
      (fun x : G => if conjLevel p h x = i then w.coeff x else 0)]
  simp

/-- **The layers add up to `w`.** -/
theorem sum_conjLayer [NeZero p] (h : G) (w : MonoidAlgebra R G) :
    ∑ i : ZMod p, conjLayer p h w i = w := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun y => ?_)
  rw [MonoidAlgebra.coeff_finsetSum]
  simp only [coeff_conjLayer]
  rw [Finset.sum_ite_eq Finset.univ (conjLevel p h y) (fun _ => w.coeff y)]
  simp

/-- **Conjugation by `h` shifts the layers.**  This is Navarro's `(w_i)^h = w_{i+1}`. -/
theorem conjLayer_conj_smul (hp : p.Prime) {h : G} (hh : IsOfFinOrder h)
    {w : MonoidAlgebra R G} (hw : h • w = w)
    (hsupp : ∀ x : G, w.coeff x ≠ 0 → ¬ Commute (pPart p h) x) (i : ZMod p) :
    h • conjLayer p h w i = conjLayer p h w (i + 1) := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun y => ?_)
  rw [OddOrder.GroupAlgebra.coeff_conj_smul, coeff_conjLayer, coeff_conjLayer]
  have hcoeff : w.coeff (h⁻¹ * y * h) = w.coeff y := by
    conv_rhs => rw [← hw]
    rw [OddOrder.GroupAlgebra.coeff_conj_smul]
  by_cases hy : w.coeff y = 0
  · rw [hy, hcoeff, hy, ite_self, ite_self]
  · have hxne : w.coeff (h⁻¹ * y * h) ≠ 0 := by rwa [hcoeff]
    have hlev : conjLevel p h y = conjLevel p h (h⁻¹ * y * h) + 1 := by
      have := conjLevel_conj hp hh (hsupp _ hxne)
      rwa [show h * (h⁻¹ * y * h) * h⁻¹ = y from by group] at this
    rw [hcoeff]
    by_cases hi : conjLevel p h (h⁻¹ * y * h) = i
    · rw [if_pos hi, if_pos (by rw [hlev, hi])]
    · rw [if_neg hi, if_neg (fun hcon => hi (by
        have := hlev.symm.trans hcon
        exact add_right_cancel this))]

end Layers

end OddOrder.GroupTheory
