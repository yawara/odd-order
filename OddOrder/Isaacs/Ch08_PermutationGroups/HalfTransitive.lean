/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI

/-!
# Isaacs, Finite Group Theory — Ch. 8: half-transitive actions (Thm 8.9, Lem 8.10)

Formalizes the Passman–Isaacs half-transitivity theorem and its partition
lemma (Isaacs pp. 230–232):

* **Lem 8.10** (`isElementaryAbelian_of_partition_normal`): a finite group
  covered by a collection of proper normal subgroups with pairwise trivial
  intersections is an elementary abelian `p`-group for some prime `p`;
* **Thm 8.9** (`isFrobeniusAction_or_isElementaryAbelian_of_half_transitive`):
  if a finite group `A` acts faithfully via automorphisms on a finite group
  `N` and all `A`-orbits of nonidentity elements have equal size
  (*half-transitivity*), then either the action is Frobenius, or `N` is an
  elementary abelian `p`-group admitting no `A`-invariant subgroup other
  than `⊥` and `⊤`.

The common core of the two counting steps of Thm 8.9 (an `N`-conjugacy class,
resp. a right coset of an invariant subgroup, cannot contain two distinct
members of one `A`-orbit) is `smul_eq_of_fiber_eq`, a coprimality argument
for the fibers of a map constant on `A`-orbit unions.
-/

namespace OddOrder.Isaacs.Ch08

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- A group covered by two subgroups is one of them. -/
private lemma eq_top_or_eq_top_of_cover {H K : Subgroup G}
    (hcov : ∀ g : G, g ∈ H ∨ g ∈ K) : H = ⊤ ∨ K = ⊤ := by
  rcases Classical.em (H = ⊤) with h | hH
  · exact Or.inl h
  right
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, haH⟩ : ∃ a : G, a ∉ H := by
    by_contra hc
    exact hH (eq_top_iff.mpr fun a _ => not_exists_not.mp hc a)
  have haK : a ∈ K := (hcov a).resolve_left haH
  rcases hcov g with hgH | hgK
  · rcases hcov (a * g) with hH' | hK'
    · exact absurd (by simpa using H.mul_mem hH' (H.inv_mem hgH)) haH
    · simpa using K.mul_mem (K.inv_mem haK) hK'
  · exact hgK

/-- **Isaacs Lem 8.10** — a finite group that is the union of a collection of
proper normal subgroups intersecting pairwise trivially is an elementary
abelian `p`-group for some prime `p`. -/
theorem isElementaryAbelian_of_partition_normal [Finite G] {P : Set (Subgroup G)}
    (hproper : ∀ X ∈ P, X ≠ ⊤)
    (hnormal : ∀ X ∈ P, (X : Subgroup G).Normal)
    (hcover : ∀ g : G, ∃ X ∈ P, g ∈ X)
    (htriv : ∀ X ∈ P, ∀ Y ∈ P, X ≠ Y → X ⊓ Y = ⊥) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p G := by
  -- the hypotheses force `G` nontrivial
  rcases subsingleton_or_nontrivial G with hs | hnt
  · obtain ⟨X, hX, hmem⟩ := hcover 1
    exact absurd (eq_top_iff.mpr fun g _ => (hs.elim g 1) ▸ hmem)
      (hproper X hX)
  -- elements of distinct members commute (their commutator lies in `X ⊓ Y`)
  have hcomm : ∀ X ∈ P, ∀ Y ∈ P, X ≠ Y → ∀ x ∈ X, ∀ y ∈ Y, Commute x y := by
    intro X hX Y hY hXY x hx y hy
    have hc1 : x * y * x⁻¹ * y⁻¹ ∈ X := by
      have := X.mul_mem hx ((hnormal X hX).conj_mem x⁻¹ (X.inv_mem hx) y)
      simpa [mul_assoc] using this
    have hc2 : x * y * x⁻¹ * y⁻¹ ∈ Y := by
      exact Y.mul_mem ((hnormal Y hY).conj_mem y hy x) (Y.inv_mem hy)
    have hbot : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Y := ⟨hc1, hc2⟩
    rw [htriv X hX Y hY hXY, Subgroup.mem_bot] at hbot
    exact commutatorElement_eq_one_iff_commute.mp
      (by simpa [commutatorElement_def] using hbot)
  -- every member is central: `G ⊆ X ∪ C_G(X)`, and `G` is not the union of
  -- two proper subgroups
  have hcentral : ∀ X ∈ P, ∀ x ∈ X, x ∈ Subgroup.center G := by
    intro X hX
    have hcov2 : ∀ g : G, g ∈ X ∨ g ∈ Subgroup.centralizer (X : Set G) := by
      intro g
      obtain ⟨W, hW, hgW⟩ := hcover g
      rcases eq_or_ne W X with rfl | hWX
      · exact Or.inl hgW
      · exact Or.inr (Subgroup.mem_centralizer_iff.mpr fun x hx =>
          hcomm X hX W hW (Ne.symm hWX) x hx g hgW)
    rcases eq_top_or_eq_top_of_cover hcov2 with h | h
    · exact absurd h (hproper X hX)
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp (h ▸ Subgroup.mem_top g) x hx).symm
  -- hence `G` is abelian
  have hab : ∀ u v : G, u * v = v * u := fun u v => by
    obtain ⟨W, hW, hu⟩ := hcover u
    exact (Subgroup.mem_center_iff.mp (hcentral W hW u hu) v).symm
  -- elements of different orders lie in a common member
  have haux : ∀ x y : G, orderOf y < orderOf x → ∃ W ∈ P, x ∈ W ∧ y ∈ W := by
    intro x y hlt
    have hxo : (x * y) ^ orderOf y = x ^ orderOf y := by
      rw [Commute.mul_pow (show Commute x y from hab x y),
        pow_orderOf_eq_one, mul_one]
    have hne : x ^ orderOf y ≠ 1 := by
      intro h
      exact absurd (Nat.le_of_dvd (orderOf_pos y) (orderOf_dvd_of_pow_eq_one h))
        (by omega)
    obtain ⟨X, hX, hxX⟩ := hcover x
    obtain ⟨Z, hZ, hxyZ⟩ := hcover (x * y)
    have hXZ : X = Z := by
      by_contra hne'
      have hmem : x ^ orderOf y ∈ X ⊓ Z :=
        ⟨X.pow_mem hxX _, by rw [← hxo]; exact Z.pow_mem hxyZ _⟩
      rw [htriv X hX Z hZ hne', Subgroup.mem_bot] at hmem
      exact hne hmem
    refine ⟨X, hX, hxX, ?_⟩
    have := X.mul_mem (X.inv_mem hxX) (hXZ ▸ hxyZ)
    simpa using this
  -- elements sharing no member have equal orders
  have hkey : ∀ x y : G, (¬ ∃ W ∈ P, x ∈ W ∧ y ∈ W) → orderOf x = orderOf y := by
    intro x y hno
    rcases lt_trichotomy (orderOf x) (orderOf y) with h | h | h
    · obtain ⟨W, hW, hyW, hxW⟩ := haux y x h
      exact absurd ⟨W, hW, hxW, hyW⟩ hno
    · exact h
    · exact absurd (haux x y h) hno
  -- an element `x` of prime order `p`
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hgord : orderOf g ≠ 1 := by simpa [orderOf_eq_one_iff] using hg
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpp : (orderOf g).minFac.Prime := Nat.minFac_prime hgord
  set p := (orderOf g).minFac with hpdef
  set x := g ^ (orderOf g / p) with hxdef
  have hxord : orderOf x = p := orderOf_pow_orderOf_div hg0 (Nat.minFac_dvd _)
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    exact hpp.one_lt.ne' hxord.symm
  -- elements on opposite sides of the member containing `x` share no member
  obtain ⟨X, hX, hxX⟩ := hcover x
  obtain ⟨w, hwX⟩ : ∃ w : G, w ∉ X := by
    by_contra hc
    exact hproper X hX (eq_top_iff.mpr fun a _ => not_exists_not.mp hc a)
  have hsep : ∀ u ∈ X, u ≠ 1 → ∀ v, v ∉ X → ¬ ∃ W ∈ P, u ∈ W ∧ v ∈ W := by
    rintro u hu hu1 v hv ⟨W, hW, huW, hvW⟩
    rcases eq_or_ne W X with rfl | hWX
    · exact hv hvW
    · have hmem : u ∈ W ⊓ X := ⟨huW, hu⟩
      rw [htriv W hW X hX hWX, Subgroup.mem_bot] at hmem
      exact hu1 hmem
  -- every nonidentity element has order `p`
  have hordall : ∀ y : G, y ≠ 1 → orderOf y = p := by
    intro y hy1
    by_cases hyX : y ∈ X
    · have hyw : orderOf y = orderOf w := hkey y w (hsep y hyX hy1 w hwX)
      have hxw : orderOf x = orderOf w := hkey x w (hsep x hxX hx1 w hwX)
      rw [hyw, ← hxw, hxord]
    · exact ((hkey x y (hsep x hxX hx1 y hyX)).symm).trans hxord
  refine ⟨p, hpp, hab, fun u => ?_⟩
  rcases eq_or_ne u 1 with rfl | hu
  · exact one_pow p
  · rw [← hordall u hu]
    exact pow_orderOf_eq_one u

/-! ### Counting infrastructure for Thm 8.9 -/

section Counting

open MulAction

/-- A finset partitioned into fibers of constant size `c` has cardinality
`(number of fibers) * c`. -/
private lemma card_eq_card_image_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) {c : ℕ}
    (hfib : ∀ v ∈ s, {w ∈ s | f w = f v}.card = c) :
    s.card = (s.image f).card * c := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem f hx)]
  rw [Finset.sum_congr rfl (fun b hb => ?_), Finset.sum_const, smul_eq_mul]
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  exact hfib v hv

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

/-- If all `A`-orbits of nonidentity elements of `N` have size `r`, then `r`
divides the cardinality of every `A`-invariant set of nonidentity elements. -/
private lemma card_dvd_card_invariant [Finite N] {r : ℕ}
    (hr : ∀ x : N, x ≠ 1 → Nat.card (orbit A x) = r)
    {S : Set N} (hSinv : ∀ a : A, ∀ n ∈ S, a • n ∈ S) (hS1 : (1 : N) ∉ S) :
    r ∣ Nat.card S := by
  classical
  haveI := Fintype.ofFinite N
  have horbsub : ∀ v ∈ S, orbit A v ⊆ S := by
    rintro v hv _ ⟨a, rfl⟩
    exact hSinv a v hv
  have hfib : ∀ v ∈ S.toFinset,
      {w ∈ S.toFinset | orbit A w = orbit A v}.card = r := by
    intro v hv
    rw [Set.mem_toFinset] at hv
    have : {w ∈ S.toFinset | orbit A w = orbit A v} = (orbit A v).toFinset := by
      ext w
      simp only [Finset.mem_filter, Set.mem_toFinset]
      constructor
      · rintro ⟨_, hw⟩
        exact hw ▸ mem_orbit_self w
      · intro hw
        exact ⟨horbsub v hv hw, orbit_eq_iff.mpr hw⟩
    rw [this, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hr v fun h => hS1 (h ▸ hv)
  have := card_eq_card_image_mul S.toFinset (fun w => orbit A w) hfib
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card, this]
  exact dvd_mul_left r _

/-- Core counting argument of **Isaacs Thm 8.9**: suppose all `A`-orbits of
nonidentity elements of `N` have size `r`, with `r` coprime to `|N|`, and let
`f : N → β` be a map whose fibers over the `A`-orbit of `x ≠ 1` all have size
`c` dividing `|N|`, are permuted by `A`, and avoid `1`.  Since the union `U`
of these fibers is `A`-invariant and `1`-free, `r ∣ |U| = m * c` with
`m ≤ r` fiber values, so by coprimality `m = r` and `f` is injective on the
orbit: an orbit element in the fiber of `x` equals `x`. -/
private lemma smul_eq_of_fiber_eq [Finite N] {r : ℕ}
    (hr : ∀ x : N, x ≠ 1 → Nat.card (orbit A x) = r)
    (hrcop : Nat.Coprime r (Nat.card N))
    {β : Type*} (f : N → β) {x : N} (hx1 : x ≠ 1) {c : ℕ}
    (hcdvd : c ∣ Nat.card N)
    (hfib : ∀ v ∈ orbit A x, Nat.card {w : N // f w = f v} = c)
    (hinv : ∀ a : A, ∀ v w : N, f v = f w → f (a • v) = f (a • w))
    (hne1 : ∀ v ∈ orbit A x, f 1 ≠ f v)
    {a : A} (hfa : f (a • x) = f x) : a • x = x := by
  classical
  haveI := Fintype.ofFinite N
  set U : Set N := {w : N | ∃ v ∈ orbit A x, f w = f v} with hUdef
  -- fibers within `U` have size `c`
  have hfibU : ∀ w ∈ U.toFinset, {w' ∈ U.toFinset | f w' = f w}.card = c := by
    intro w hw
    rw [Set.mem_toFinset] at hw
    obtain ⟨v, hv, hfw⟩ := hw
    have hUfull : {w' ∈ U.toFinset | f w' = f w} =
        {w' ∈ (Finset.univ : Finset N) | f w' = f w} := by
      ext w'
      simp only [Finset.mem_filter, Set.mem_toFinset, Finset.mem_univ, true_and,
        and_iff_right_iff_imp]
      exact fun h => ⟨v, hv, h.trans hfw⟩
    rw [hUfull]
    have := hfib v hv
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    rw [← this]
    congr 1
    ext w'
    simp only [Finset.mem_filter, hfw]
  -- `r` divides `|U|`
  have hUinv : ∀ a' : A, ∀ n ∈ U, a' • n ∈ U := by
    rintro a' n ⟨v, ⟨b, rfl⟩, hfn⟩
    exact ⟨(a' * b) • x, mem_orbit x _, by
      rw [mul_smul]; exact hinv a' n (b • x) hfn⟩
  have hU1 : (1 : N) ∉ U := fun ⟨v, hv, hf1⟩ => hne1 v hv hf1
  have hrU : r ∣ U.toFinset.card := by
    have := card_dvd_card_invariant hr hUinv hU1
    rwa [Nat.card_eq_fintype_card, ← Set.toFinset_card] at this
  -- `|U| = m * c` with `m` the number of fiber values
  have hUcard := card_eq_card_image_mul U.toFinset f hfibU
  -- the fiber values are exactly those of the orbit
  have himage : U.toFinset.image f = (orbit A x).toFinset.image f := by
    ext b
    simp only [Finset.mem_image, Set.mem_toFinset]
    constructor
    · rintro ⟨w, ⟨v, hv, hfw⟩, rfl⟩
      exact ⟨v, hv, hfw.symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, ⟨v, hv, rfl⟩, rfl⟩
  have hOcard : (orbit A x).toFinset.card = r := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hr x hx1
  have hUm : U.toFinset.card = ((orbit A x).toFinset.image f).card * c := by
    rw [hUcard, himage]
  have hmr : ((orbit A x).toFinset.image f).card ≤ r :=
    hOcard ▸ Finset.card_image_le
  have hm0 : 0 < ((orbit A x).toFinset.image f).card := by
    refine Finset.card_pos.mpr ⟨f x, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
    rw [Set.mem_toFinset]
    exact mem_orbit_self x
  -- coprimality forces the number of fiber values to be `r`
  have hrm : r ∣ ((orbit A x).toFinset.image f).card :=
    (Nat.Coprime.coprime_dvd_right hcdvd hrcop).dvd_of_dvd_mul_right
      (hUm ▸ hrU)
  -- hence `f` is injective on the orbit
  have hinj : Set.InjOn f ((orbit A x).toFinset : Set N) := by
    apply Finset.injOn_of_card_image_eq
    rw [hOcard]
    exact le_antisymm hmr (Nat.le_of_dvd hm0 hrm)
  have hax : a • x ∈ ((orbit A x).toFinset : Set N) := by
    simp only [Finset.mem_coe, Set.mem_toFinset]
    exact mem_orbit x a
  have hxx : x ∈ ((orbit A x).toFinset : Set N) := by
    simp only [Finset.mem_coe, Set.mem_toFinset]
    exact mem_orbit_self x
  exact hinj hax hxx hfa

end Counting

/-! ### Isaacs Thm 8.9 -/

section PassmanIsaacs

open MulAction

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

/-- Automorphisms transport conjugacy. -/
private lemma isConj_smul (a : A) {u w : N} (h : IsConj u w) :
    IsConj (a • u) (a • w) := by
  rw [isConj_iff] at h ⊢
  obtain ⟨g, hg⟩ := h
  exact ⟨a • g, by rw [← smul_inv', ← smul_mul', ← smul_mul', hg]⟩

/-- **Isaacs Thm 8.9, step 1** — under half-transitivity (with `r` coprime to
`|N|`), a conjugacy class of `N` cannot contain two distinct members of an
`A`-orbit. -/
private lemma smul_eq_of_isConj [Finite N] {r : ℕ}
    (hr : ∀ x : N, x ≠ 1 → Nat.card (orbit A x) = r)
    (hrcop : Nat.Coprime r (Nat.card N))
    {x : N} (hx1 : x ≠ 1) {a : A} (hconj : IsConj x (a • x)) : a • x = x := by
  classical
  have hfeq : ∀ v w : N,
      {z : N | IsConj v z} = {z : N | IsConj w z} ↔ IsConj v w := by
    intro v w
    constructor
    · intro h
      have hw : w ∈ {z : N | IsConj w z} := IsConj.refl w
      rw [← h] at hw
      exact hw
    · intro hc
      ext z
      exact ⟨fun h => hc.symm.trans h, fun h => hc.trans h⟩
  refine smul_eq_of_fiber_eq hr hrcop (fun v => {z : N | IsConj v z}) hx1
    (c := Nat.card {w : N // IsConj w x}) ?_ ?_ ?_ ?_ ?_
  · -- the class of `x` is the `ConjAct`-orbit of `x`, whose size divides `|N|`
    have he : {w : N // IsConj w x} ≃ ConjAct N ⧸ stabilizer (ConjAct N) x :=
      (Equiv.subtypeEquivRight fun w => ConjAct.mem_orbit_conjAct.symm).trans
        (orbitEquivQuotientStabilizer (ConjAct N) x)
    rw [Nat.card_congr he]
    calc Nat.card (ConjAct N ⧸ stabilizer (ConjAct N) x)
        ∣ Nat.card (ConjAct N) := (stabilizer (ConjAct N) x).index_dvd_card
      _ = Nat.card N := Nat.card_congr ConjAct.ofConjAct.toEquiv
  · -- fibers over the orbit all have the size of the class of `x`
    rintro v ⟨b, rfl⟩
    have e1 : {w : N // (fun v => {z : N | IsConj v z}) w =
        (fun v => {z : N | IsConj v z}) (b • x)} ≃ {w : N // IsConj w (b • x)} :=
      Equiv.subtypeEquivRight fun w => hfeq w (b • x)
    have e2 : {w : N // IsConj w x} ≃ {w : N // IsConj w (b • x)} :=
      ⟨fun w => ⟨b • w.1, isConj_smul b w.2⟩,
       fun w => ⟨b⁻¹ • w.1, by simpa using isConj_smul b⁻¹ w.2⟩,
       fun w => by ext; simp, fun w => by ext; simp⟩
    exact (Nat.card_congr e1).trans (Nat.card_congr e2).symm
  · -- `A` permutes the fibers
    intro a' v w hvw
    rw [hfeq] at hvw ⊢
    exact isConj_smul a' hvw
  · -- fibers over the orbit avoid `1`
    rintro v ⟨b, rfl⟩ hf1
    rw [hfeq] at hf1
    obtain ⟨g, hg⟩ := isConj_iff.mp hf1
    have hbx : b • x = 1 := by simpa using hg.symm
    exact hx1 (by simpa using congrArg (b⁻¹ • ·) hbx)
  · rw [hfeq]
    exact hconj.symm

/-- **Isaacs Thm 8.9, step 2** — under half-transitivity (with `r` coprime to
`|N|`), a right coset of an `A`-invariant subgroup cannot contain two
distinct members of an `A`-orbit. -/
private lemma smul_eq_of_rightCoset [Finite N] {r : ℕ}
    (hr : ∀ x : N, x ≠ 1 → Nat.card (orbit A x) = r)
    (hrcop : Nat.Coprime r (Nat.card N))
    {H : Subgroup N} (hHinv : ∀ a : A, ∀ n ∈ H, a • n ∈ H)
    {x : N} (hx : x ∉ H) {a : A} (hcos : (a • x) * x⁻¹ ∈ H) : a • x = x := by
  classical
  have hx1 : x ≠ 1 := fun h => hx (h ▸ H.one_mem)
  have hfeq : ∀ v w : N, ({u : N | u * v⁻¹ ∈ H} = {u : N | u * w⁻¹ ∈ H}) ↔
      v * w⁻¹ ∈ H := by
    intro v w
    constructor
    · intro h
      have hv : v ∈ {u : N | u * v⁻¹ ∈ H} := by simp
      rw [h] at hv
      exact hv
    · intro h
      ext u
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hu
        simpa [mul_assoc] using H.mul_mem hu h
      · intro hu
        have := H.mul_mem hu (H.inv_mem h)
        simpa [mul_assoc] using this
  refine smul_eq_of_fiber_eq hr hrcop (fun v => {u : N | u * v⁻¹ ∈ H}) hx1
    (c := Nat.card H) H.card_subgroup_dvd_card ?_ ?_ ?_ ?_
  · -- each fiber is a right coset, of size `|H|`
    intro v _
    refine Nat.card_congr ⟨fun w => ⟨w.1 * v⁻¹, (hfeq w.1 v).mp w.2⟩,
      fun h => ⟨h.1 * v, ?_⟩, fun w => ?_, fun h => ?_⟩
    · rw [hfeq]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
      exact h.2
    · ext
      simp [mul_assoc]
    · ext
      simp [mul_assoc]
  · -- `A` permutes the cosets
    intro a' v w hvw
    rw [hfeq] at hvw ⊢
    have := hHinv a' _ hvw
    rwa [smul_mul', smul_inv'] at this
  · -- cosets over the orbit avoid `1`
    rintro v ⟨b, rfl⟩ hf
    rw [hfeq] at hf
    have hbx : b • x ∈ H := by
      have := H.inv_mem hf
      simpa using this
    have := hHinv b⁻¹ _ hbx
    rw [inv_smul_smul] at this
    exact hx this
  · rw [hfeq]
    exact hcos

/-- `C_N(C_A(x))` of Isaacs Thm 8.9 — the elements of `N` fixed by the
stabilizer of `x` in `A`. -/
private def stabFixed (A : Type*) {N : Type*} [Group A] [Group N]
    [MulDistribMulAction A N] (x : N) : Subgroup N where
  carrier := {n | ∀ a : A, a • x = x → a • n = n}
  one_mem' := fun a _ => smul_one a
  mul_mem' := fun {u v} hu hv a ha => by rw [smul_mul', hu a ha, hv a ha]
  inv_mem' := fun {u} hu a ha => by rw [smul_inv', hu a ha]

private lemma mem_stabFixed {x n : N} :
    n ∈ stabFixed A x ↔ ∀ a : A, a • x = x → a • n = n :=
  Iff.rfl

/-- **Isaacs Thm 8.9** (Passman–Isaacs) — if a finite group `A` acts
faithfully via automorphisms on a finite group `N` and all `A`-orbits of
nonidentity elements of `N` have equal size (*half-transitive* action on the
nonidentity elements), then either the action is Frobenius, or `N` is an
elementary abelian `p`-group for some prime `p` and admits no `A`-invariant
subgroup other than `⊥` and `⊤`. -/
theorem isFrobeniusAction_or_isElementaryAbelian_of_half_transitive
    (A N : Type*) [Group A] [Group N] [MulDistribMulAction A N]
    [Finite A] [Finite N] [FaithfulSMul A N]
    (hhalf : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      Nat.card (orbit A x) = Nat.card (orbit A y)) :
    Ch06.IsFrobeniusAction A N ∨
      ((∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p N) ∧
        ∀ H : Subgroup N, H ≠ ⊤ → (∀ a : A, ∀ n ∈ H, a • n ∈ H) → H = ⊥) := by
  classical
  by_cases hfrob : Ch06.IsFrobeniusAction A N
  · exact Or.inl hfrob
  right
  -- a nonidentity element `a₀` fixing a nonidentity element `n₀`
  obtain ⟨a₀, ha₀1, n₀, hn₀1, hfix₀⟩ :
      ∃ a : A, a ≠ 1 ∧ ∃ n : N, n ≠ 1 ∧ a • n = n := by
    by_contra hc
    exact hfrob fun a ha n hn hsmul => hc ⟨a, ha, n, hn, hsmul⟩
  haveI : Nontrivial N := ⟨n₀, 1, hn₀1⟩
  set r := Nat.card (orbit A n₀) with hrdef
  have hr : ∀ x : N, x ≠ 1 → Nat.card (orbit A x) = r :=
    fun x hx => hhalf x n₀ hx hn₀1
  have hrpos : 0 < r := by
    haveI : Nonempty (orbit A n₀) := ⟨⟨n₀, mem_orbit_self n₀⟩⟩
    exact hrdef ▸ Nat.card_pos
  -- `r` divides `|N| - 1`, hence is coprime to `|N|`
  have hrdvd : r ∣ Nat.card N - 1 := by
    have h := card_dvd_card_invariant hr (S := {n : N | n ≠ 1})
      (fun a n hn h1 => hn (by simpa using congrArg (a⁻¹ • ·) h1))
      (by simp)
    haveI := Fintype.ofFinite N
    rwa [Nat.card_eq_fintype_card, Set.card_ne_eq, ← Nat.card_eq_fintype_card]
      at h
  have hrcop : Nat.Coprime r (Nat.card N) := by
    have hpos : 1 ≤ Nat.card N := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    have h1 : Nat.Coprime (Nat.card N - 1) (Nat.card N) := by
      have h2 : Nat.Coprime (Nat.card N - 1) ((Nat.card N - 1) + 1) := by
        rw [Nat.coprime_self_add_right]
        exact Nat.coprime_one_right _
      rwa [Nat.sub_add_cancel hpos] at h2
    exact Nat.Coprime.coprime_dvd_left hrdvd h1
  -- all stabilizers of nonidentity elements share the cardinality of
  -- `stab n₀`, which exceeds `1`
  have hstabcard : ∀ x : N, x ≠ 1 →
      Nat.card (stabilizer A x) = Nat.card (stabilizer A n₀) := by
    intro x hx
    have hprod : ∀ y : N, y ≠ 1 →
        r * Nat.card (stabilizer A y) = Nat.card A := by
      intro y hy
      rw [← hr y hy, Nat.card_congr (orbitEquivQuotientStabilizer A y)]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
    exact Nat.eq_of_mul_eq_mul_left hrpos
      ((hprod x hx).trans (hprod n₀ hn₀1).symm)
  have hstabne : ∀ x : N, x ≠ 1 → ∃ a : A, a ≠ 1 ∧ a • x = x := by
    intro x hx
    have h1 : 1 < Nat.card (stabilizer A x) := by
      rw [hstabcard x hx]
      exact Finite.one_lt_card_iff_nontrivial.mpr
        ⟨⟨a₀, mem_stabilizer_iff.mpr hfix₀⟩, 1, fun h => ha₀1 (congrArg Subtype.val h)⟩
    haveI := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨s, hs⟩ := exists_ne (1 : stabilizer A x)
    exact ⟨s.1, fun h => hs (Subtype.ext h), s.2⟩
  -- basic properties of `C x := stabFixed A x`
  have hxC : ∀ x : N, x ∈ stabFixed A x := fun x a ha => ha
  have hCC : ∀ {x y : N}, x ≠ 1 → y ≠ 1 → y ∈ stabFixed A x →
      stabFixed A y = stabFixed A x := by
    intro x y hx hy hyC
    have hle : stabilizer A x ≤ stabilizer A y :=
      fun a ha => mem_stabilizer_iff.mpr (hyC a (mem_stabilizer_iff.mp ha))
    have heq : stabilizer A x = stabilizer A y := by
      apply SetLike.ext'
      apply Set.eq_of_subset_of_ncard_le hle
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      have hbridge : ∀ z : N, Nat.card (stabilizer A z : Set A) =
          Nat.card (stabilizer A z) := fun z => rfl
      rw [hbridge, hbridge, hstabcard x hx, hstabcard y hy]
    ext n
    rw [mem_stabFixed, mem_stabFixed]
    constructor
    · intro h a hax
      exact h a (mem_stabilizer_iff.mp (heq ▸ mem_stabilizer_iff.mpr hax))
    · intro h a hay
      exact h a (mem_stabilizer_iff.mp (heq.symm ▸ mem_stabilizer_iff.mpr hay))
  have hCproper : ∀ x : N, x ≠ 1 → stabFixed A x ≠ ⊤ := by
    intro x hx htop
    obtain ⟨a, ha1, hax⟩ := hstabne x hx
    refine ha1 (FaithfulSMul.eq_of_smul_eq_smul (α := N) (m₁ := a) (m₂ := 1)
      fun n => ?_)
    rw [one_smul]
    exact (htop ▸ Subgroup.mem_top n : n ∈ stabFixed A x) a hax
  -- conjugacy classes are contained in members: `class x ⊆ C x`
  have hclassC : ∀ x : N, x ≠ 1 → ∀ v : N, IsConj x v → v ∈ stabFixed A x := by
    intro x hx v hconj a hax
    have hv1 : v ≠ 1 := by
      rintro rfl
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      refine hx ?_
      have h2 := congrArg (fun z => g⁻¹ * z * g) hg
      simpa [mul_assoc] using h2
    refine smul_eq_of_isConj hr hrcop hv1 ?_
    exact hconj.symm.trans (hax ▸ isConj_smul a hconj)
  have hCnormal : ∀ x : N, x ≠ 1 → (stabFixed A x).Normal := by
    intro x hx
    constructor
    intro w hw g
    rcases eq_or_ne w 1 with rfl | hw1
    · simp only [mul_one, mul_inv_cancel]
      exact (stabFixed A x).one_mem
    · have hcls : g * w * g⁻¹ ∈ stabFixed A w :=
        hclassC w hw1 _ (isConj_iff.mpr ⟨g, rfl⟩)
      rwa [hCC hx hw1 hw] at hcls
  -- Lem 8.10 gives the elementary abelian conclusion
  refine ⟨isElementaryAbelian_of_partition_normal
    (P := {S | ∃ x : N, x ≠ 1 ∧ S = stabFixed A x}) ?_ ?_ ?_ ?_, ?_⟩
  · rintro X ⟨x, hx, rfl⟩
    exact hCproper x hx
  · rintro X ⟨x, hx, rfl⟩
    exact hCnormal x hx
  · intro g
    rcases eq_or_ne g 1 with rfl | hg
    · exact ⟨stabFixed A n₀, ⟨n₀, hn₀1, rfl⟩, (stabFixed A n₀).one_mem⟩
    · exact ⟨stabFixed A g, ⟨g, hg, rfl⟩, hxC g⟩
  · rintro X ⟨x, hx, rfl⟩ Y ⟨y, hy, rfl⟩ hne
    rw [eq_bot_iff]
    rintro z ⟨hzx, hzy⟩
    rcases eq_or_ne z 1 with rfl | hz1
    · exact Subgroup.one_mem ⊥
    · exact absurd ((hCC hx hz1 hzx).symm.trans (hCC hy hz1 hzy)) hne
  -- no `A`-invariant subgroup other than `⊥` and `⊤`
  intro H hHtop hHinv
  by_contra hHbot
  obtain ⟨h₀, hh₀H, hh₀1⟩ : ∃ h ∈ H, h ≠ 1 := by
    by_contra hc
    exact hHbot ((Subgroup.eq_bot_iff_forall H).mpr (by
      intro h hh
      by_contra h1
      exact hc ⟨h, hh, h1⟩))
  -- `H ≤ C y` for every `y ∉ H`
  have hHC : ∀ y : N, y ∉ H → H ≤ stabFixed A y := by
    intro y hy h hh a hay
    -- the coset element `h * y` is fixed by `a`, hence so is `h`
    have hcos : (a • (h * y)) * (h * y)⁻¹ ∈ H := by
      rw [smul_mul', hay, mul_inv_rev, ← mul_assoc, mul_assoc (a • h),
        mul_inv_cancel, mul_one]
      exact H.mul_mem (hHinv a h hh) (H.inv_mem hh)
    have hvH : h * y ∉ H :=
      fun hmem => hy (by simpa using H.mul_mem (H.inv_mem hh) hmem)
    have hveq : a • (h * y) = h * y :=
      smul_eq_of_rightCoset hr hrcop hHinv hvH hcos
    rw [smul_mul', hay] at hveq
    exact mul_right_cancel hveq
  obtain ⟨y₀, hy₀⟩ : ∃ y : N, y ∉ H := by
    by_contra hc
    exact hHtop (eq_top_iff.mpr fun y _ => not_exists_not.mp hc y)
  have hy₀1 : y₀ ≠ 1 := fun h => hy₀ (h ▸ H.one_mem)
  -- `C h₀ = ⊤`, contradicting properness
  refine hCproper h₀ hh₀1 (eq_top_iff.mpr fun n _ => ?_)
  by_cases hnH : n ∈ H
  · have h2 : stabFixed A h₀ = stabFixed A y₀ :=
      hCC hy₀1 hh₀1 (hHC y₀ hy₀ hh₀H)
    exact h2 ▸ hHC y₀ hy₀ hnH
  · have hn1 : n ≠ 1 := fun h => hnH (h ▸ H.one_mem)
    have h2 : stabFixed A h₀ = stabFixed A n :=
      hCC hn1 hh₀1 (hHC n hnH hh₀H)
    exact h2 ▸ hxC n

end PassmanIsaacs

end OddOrder.Isaacs.Ch08
