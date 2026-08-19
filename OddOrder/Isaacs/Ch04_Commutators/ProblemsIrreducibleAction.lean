/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch04_Commutators.Main.BaerTrick

/-!
# Isaacs Chapter 4 — Problem 4D.3 (真の `A`-不変部分群に自明な coprime 作用)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4D.3 (書籍 p. 145)。

`A` が `G` に coprime に作用し (`A` か `G` の一方は可解), **すべての真の `A`-不変部分群には
自明に作用するが `G` 全体には非自明に作用する**とき (`IsIrreducibleCoprimeAction`),
`G` の構造は強く制限される:

* **(a)** `G` は `p`-群 (`exists_isPGroup`)
* **(b)** `G' ⊆ Z(G)` (`commutator_le_center`)
* **(c)** `G' < H < G` なる `A`-不変 `H` は無い (`eq_commutator_or_eq_top_of_isAInvariant`;
  核は `C_G(A) = G'` = `fixedPoints_eq_commutator`)
* **(d)** `G/G'` は基本アーベル (`pow_mem_commutator` / `pow_eq_one_quotient_commutator`)
* **(e)** `G'` は基本アーベル (`pow_eq_one_of_mem_commutator`)
* **(f)** `p > 2` なら `x ^ p = 1` (`pow_eq_one_of_ne_two`)
* **(g)** `p = 2` なら `x ^ 4 = 1` (`pow_four_eq_one_of_two`)

さらに応用として **Problem 4D.4** (`actionCommutator_eq_bot_of_isPGroup_two_of_fixes_pow_four`):
奇数位数の `A` が `2`-群 `G` に作用し `x ^ 4 = 1` なる元をすべて固定するなら作用は自明。

## 基本構造

仮説から直ちに `⁅G, A⁆ = G` (`actionCommutator_eq_top`) と,
**`C_G(A)` が唯一の極大 `A`-不変部分群** (`le_fixedPoints_of_ne_top` +
`fixedPoints_ne_top`) が従う。(a) は各素数の `A`-不変 Sylow (Isaacs Thm 3.23(a),
`exists_aInvariant_sylow`) がすべて真部分群だとすると `|G|` が `|C_G(A)|` を割って
しまうことから, (b) は Problem 4C.3 の作用版
(`actionCommutator_le_centralizer_of_trivial_on_normal`) から従う。

(c) は hint どおり **Fitting の定理** (Thm 4.34) を `G/G'` への作用に適用する。(d) は
`Φ(G) = G'` (`frattini_eq_commutator`) + Problem 1D.8, (e) は class `≤ 2` の双線形性,
(f) は `x ↦ x ^ p` が準同型になること + `⁅G,A⁆ = G`, (g) は (d)+(e) から。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4D.3 (p. 145) -/

variable {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}

/-! ### Problem 4C.3 の作用版 -/

/-- **Problem 4C.3 (作用版)**: `A` が `N ⊴ G` に自明に作用するなら `⁅G, A⁆` は `N` を中心化する。

`u := g⁻¹ · (φ a) g` に対し, `g n g⁻¹ ∈ N` の `A`-不変性から
`(φ a) g · n · ((φ a) g)⁻¹ = g n g⁻¹`, すなわち `u n u⁻¹ = n`。`⁅G, A⁆` はこの形の元で
生成される (`actionCommutator_le_iff_left`)。 -/
theorem actionCommutator_le_centralizer_of_trivial_on_normal
    {N : Subgroup G} [N.Normal]
    (htriv : ∀ a : A, ∀ n ∈ N, (φ a) n = n) :
    actionCommutator φ ≤ Subgroup.centralizer (N : Set G) := by
  rw [actionCommutator_le_iff_left]
  intro a g
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hgn : g * n * g⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn g
  have h1 : (φ a) g * n * ((φ a) g)⁻¹ = g * n * g⁻¹ := by
    have h := htriv a _ hgn
    rwa [map_mul, map_mul, map_inv, htriv a n hn] at h
  have hconj : (g⁻¹ * (φ a) g) * n * (g⁻¹ * (φ a) g)⁻¹ = n := by
    rw [mul_inv_rev, inv_inv]
    calc g⁻¹ * (φ a) g * n * (((φ a) g)⁻¹ * g)
        = g⁻¹ * ((φ a) g * n * ((φ a) g)⁻¹) * g := by group
      _ = g⁻¹ * (g * n * g⁻¹) * g := by rw [h1]
      _ = n := by group
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

/-! ### 仮説束 -/

/-- **Problem 4D.3 の仮説**: coprime 作用で「すべての真の `A`-不変部分群には自明に作用するが
`G` 全体には非自明に作用する」。 -/
structure IsIrreducibleCoprimeAction {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) : Prop where
  /-- `(|A|, |G|) = 1`. -/
  coprime : Nat.Coprime (Nat.card A) (Nat.card G)
  /-- `A` か `G` の一方は可解 (Glauberman の補題を使うため). -/
  solvable : Group.IsSolvable A ∨ Group.IsSolvable G
  /-- 真の `A`-不変部分群には自明に作用する. -/
  trivial_on_proper : ∀ H : Subgroup G, Ch03.IsAInvariant φ H → H ≠ ⊤ →
    ∀ a : A, ∀ h ∈ H, (φ a) h = h
  /-- `G` 全体への作用は非自明. -/
  nontrivial : actionCommutator φ ≠ ⊥

namespace IsIrreducibleCoprimeAction

/-- 真の `A`-不変部分群はすべて `C_G(A)` に含まれる. -/
theorem le_fixedPoints_of_ne_top (h : IsIrreducibleCoprimeAction φ) {H : Subgroup G}
    (hinv : Ch03.IsAInvariant φ H) (hne : H ≠ ⊤) :
    H ≤ Subgroup.fixedPointsOfMulAut φ := fun _ hx =>
  Subgroup.mem_fixedPointsOfMulAut.mpr fun a => h.trivial_on_proper H hinv hne a _ hx

/-- `C_G(A) ≠ G` (さもなくば作用が自明になる). -/
theorem fixedPoints_ne_top (h : IsIrreducibleCoprimeAction φ) :
    Subgroup.fixedPointsOfMulAut φ ≠ ⊤ := by
  intro htop
  refine h.nontrivial ((actionCommutator_eq_bot_iff_acts_trivially φ).mpr fun a g => ?_)
  have hg : g ∈ Subgroup.fixedPointsOfMulAut φ := htop ▸ Subgroup.mem_top g
  exact Subgroup.mem_fixedPointsOfMulAut.mp hg a

/-- `G` は非自明 (自明なら作用も自明). -/
theorem nontrivial_group (h : IsIrreducibleCoprimeAction φ) : Nontrivial G := by
  by_contra hcon
  have : Subsingleton G := not_nontrivial_iff_subsingleton.mp hcon
  exact h.nontrivial ((actionCommutator_eq_bot_iff_acts_trivially φ).mpr fun _ _ =>
    Subsingleton.elim _ _)

variable [Finite A] [Finite G]

/-- **`⁅G, A⁆ = G`**: `⁅G, A⁆` は `A`-不変なので, 真部分群なら `A` はその上で自明に作用し,
Lemma 4.28 の系から `⁅G, A⁆ = 1` となって仮定に反する。 -/
theorem actionCommutator_eq_top (h : IsIrreducibleCoprimeAction φ) :
    actionCommutator φ = ⊤ := by
  by_contra hne
  refine h.nontrivial ?_
  refine actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime h.coprime h.solvable ?_
  exact h.trivial_on_proper _ (Ch03.IsAInvariant.actionCommutator φ) hne

/-- **Isaacs Problem 4D.3(a)**: `G` は `p`-群。

各素数 `p` の `A`-不変 Sylow `p`-部分群 (Thm 3.23(a)) が真部分群なら `C_G(A)` に含まれるので,
すべての素数でそうだとすると `|G|` の各素数冪が `|C_G(A)|` を割り `C_G(A) = G` となって
`fixedPoints_ne_top` に反する。 -/
theorem exists_isPGroup (h : IsIrreducibleCoprimeAction φ) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p G := by
  by_contra hcon
  push Not at hcon
  set F : Subgroup G := Subgroup.fixedPointsOfMulAut φ with hF
  have hpow : ∀ p : ℕ, p.Prime → p ^ (Nat.card G).factorization p ∣ Nat.card ↥F := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hPinv⟩ := exists_aInvariant_sylow (φ := φ) h.coprime h.solvable p
    have hPne : (P : Subgroup G) ≠ ⊤ := by
      intro htop
      refine hcon p hp fun g => ?_
      have hg : g ∈ (P : Subgroup G) := htop ▸ Subgroup.mem_top g
      obtain ⟨k, hk⟩ := P.2 (⟨g, hg⟩ : ↥(P : Subgroup G))
      exact ⟨k, congrArg Subtype.val hk⟩
    have hcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
      P.card_eq_multiplicity
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (h.le_fixedPoints_of_ne_top hPinv hPne)
  have hdvd : Nat.card G ∣ Nat.card ↥F := by
    refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr fun p k hp hpk => ?_
    refine dvd_trans (pow_dvd_pow p ?_) (hpow p hp)
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hpk
  have heq : Nat.card ↥F = Nat.card G :=
    Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card F) hdvd
  exact h.fixedPoints_ne_top (Subgroup.eq_top_of_card_eq F heq)

/-- `G` は冪零 ((a) より `p`-群). -/
theorem isNilpotent_group (h : IsIrreducibleCoprimeAction φ) : Group.IsNilpotent G := by
  obtain ⟨p, hp, hpG⟩ := h.exists_isPGroup
  have : Fact p.Prime := ⟨hp⟩
  exact hpG.isNilpotent

/-- `G' ≠ G` (非自明な冪零群だから). -/
theorem commutator_ne_top (h : IsIrreducibleCoprimeAction φ) :
    _root_.commutator G ≠ ⊤ := by
  have := h.nontrivial_group
  have := h.isNilpotent_group
  intro htop
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent G›
  have hall : ∀ m : ℕ, (⊤ : Subgroup G).lowerCentralSeries m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Subgroup.lowerCentralSeries_succ, ih]; exact htop
  exact (top_ne_bot : (⊤ : Subgroup G) ≠ ⊥) (by rw [← hall n, hn])

omit [Finite A] [Finite G] in
/-- `G'` は `A`-不変 (特性部分群). -/
theorem isAInvariant_commutator (_h : IsIrreducibleCoprimeAction φ) :
    Ch03.IsAInvariant φ (_root_.commutator G) := Ch03.IsAInvariant.of_characteristic φ

/-- `A` は `G'` 上で自明に作用する. -/
theorem trivial_on_commutator (h : IsIrreducibleCoprimeAction φ) :
    ∀ a : A, ∀ c ∈ _root_.commutator G, (φ a) c = c :=
  h.trivial_on_proper _ h.isAInvariant_commutator h.commutator_ne_top

/-- **Isaacs Problem 4D.3(b)**: `G' ⊆ Z(G)`, すなわち `G` の冪零類は `2` 以下。

`G` は (a) より `p`-群なので冪零, したがって `G' ≠ G`。`G'` は特性部分群ゆえ `A`-不変で,
真部分群なので `A` は `G'` 上で自明に作用する。Problem 4C.3 の作用版より
`⁅G, A⁆ ≤ C_G(G')` で, `⁅G, A⁆ = G` (`actionCommutator_eq_top`) だから `G' ≤ Z(G)`。 -/
theorem commutator_le_center (h : IsIrreducibleCoprimeAction φ) :
    _root_.commutator G ≤ Subgroup.center G := by
  have htriv := h.trivial_on_commutator
  have hle := actionCommutator_le_centralizer_of_trivial_on_normal (φ := φ)
    (N := _root_.commutator G) htriv
  rw [h.actionCommutator_eq_top, top_le_iff] at hle
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer ((_root_.commutator G : Subgroup G) : Set G) := by
    rw [hle]; exact Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm

/-- **Isaacs Problem 4D.3(c)** (核): `C_G(A) = G'`。

`Ḡ := G/G'` は可換で `A` の作用は coprime, かつ `⁅Ḡ, A⁆ = Ḡ` (`⁅G,A⁆ = G` の像) なので
**Fitting の定理** (Thm 4.34, `fixedPoints_inf_actionCommutator_eq_bot_of_abelian`) より
`C_Ḡ(A) = C_Ḡ(A) ⊓ ⁅Ḡ,A⁆ = 1`。coprime 作用では `C_Ḡ(A)` は `C_G(A)` の像 (Cor 3.28) なので
`C_G(A) ≤ G'`。逆向きは `G'` が真の `A`-不変部分群であることから。 -/
theorem fixedPoints_eq_commutator (h : IsIrreducibleCoprimeAction φ) :
    Subgroup.fixedPointsOfMulAut φ = _root_.commutator G := by
  have hinv := h.isAInvariant_commutator
  refine le_antisymm ?_ (h.le_fixedPoints_of_ne_top hinv h.commutator_ne_top)
  let : CommGroup (G ⧸ _root_.commutator G) :=
    { (inferInstance : Group (G ⧸ _root_.commutator G)) with
      mul_comm := (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        (le_refl (_root_.commutator G))).is_comm.comm }
  have hac : actionCommutator (Ch03.IsAInvariant.quotientMulAutHom hinv) = ⊤ := by
    rw [actionCommutator_quotient_eq_map hinv, h.actionCommutator_eq_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (G ⧸ _root_.commutator G)) :=
    Nat.Coprime.coprime_dvd_right
      ⟨Nat.card ↥(_root_.commutator G),
        Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩ h.coprime
  have hfix := fixedPoints_inf_actionCommutator_eq_bot_of_abelian
    (Ch03.IsAInvariant.quotientMulAutHom hinv) hcop
  rw [hac, inf_top_eq] at hfix
  have hmap := fixedPointsOfMulAut_quotientMulAutHom_eq_map h.coprime h.solvable hinv
  rw [hfix] at hmap
  have hle : Subgroup.fixedPointsOfMulAut φ ≤ (QuotientGroup.mk' (_root_.commutator G)).ker :=
    (Subgroup.map_eq_bot_iff _).mp hmap.symm
  rwa [QuotientGroup.ker_mk'] at hle

/-- **Isaacs Problem 4D.3(c)**: `G' < H < G` なる `A`-不変部分群 `H` は存在しない。 -/
theorem eq_commutator_or_eq_top_of_isAInvariant (h : IsIrreducibleCoprimeAction φ)
    {H : Subgroup G} (hinv : Ch03.IsAInvariant φ H) (hle : _root_.commutator G ≤ H) :
    H = _root_.commutator G ∨ H = ⊤ := by
  by_cases htop : H = ⊤
  · exact Or.inr htop
  · exact Or.inl (le_antisymm
      ((h.le_fixedPoints_of_ne_top hinv htop).trans h.fixedPoints_eq_commutator.le) hle)

/-- `Φ(G) = G'` (この状況では Frattini 部分群と導来部分群が一致する). -/
theorem frattini_eq_commutator (h : IsIrreducibleCoprimeAction φ) :
    frattini G = _root_.commutator G := by
  have := h.nontrivial_group
  have hfrne : frattini G ≠ ⊤ := by
    intro htop
    exact absurd (frattini_nongenerating (K := (⊥ : Subgroup G)) (by rw [htop, bot_sup_eq]))
      bot_ne_top
  exact le_antisymm
    ((h.le_fixedPoints_of_ne_top (Ch03.IsAInvariant.of_characteristic φ) hfrne).trans
      h.fixedPoints_eq_commutator.le)
    (haveI := h.isNilpotent_group; Ch01.commutator_le_frattini)

/-- **Isaacs Problem 4D.3(d)**: `G/G'` は基本アーベル — 指数の部分 (`x ^ p ∈ G'`)。

可換性は `commutator` による商だから自明。指数は `x ^ p ∈ Φ(G)` (Problem 1D.8) と
`Φ(G) = G'` (`frattini_eq_commutator`) から。 -/
theorem pow_mem_commutator (h : IsIrreducibleCoprimeAction φ) {p : ℕ} (hp : p.Prime)
    (hpG : IsPGroup p G) (x : G) : x ^ p ∈ _root_.commutator G := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← h.frattini_eq_commutator]
  exact Ch01.pow_mem_frattini_of_isPGroup hpG x

/-- Problem 4D.3(d) の商の形: `G/G'` の指数は `p` を割る. -/
theorem pow_eq_one_quotient_commutator (h : IsIrreducibleCoprimeAction φ) {p : ℕ}
    (hp : p.Prime) (hpG : IsPGroup p G) (q : G ⧸ _root_.commutator G) : q ^ p = 1 := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h.pow_mem_commutator hp hpG x

/-- **Isaacs Problem 4D.3(e)**: `G'` は基本アーベル (自明でもよい)。

`G' ≤ Z(G)` ((b)) より可換。指数は class `≤ 2` の双線形性
`⁅x, y⁆ ^ p = ⁅x ^ p, y⁆` と (d) の `x ^ p ∈ G' ≤ Z(G)` から `= 1`。 -/
theorem pow_eq_one_of_mem_commutator (h : IsIrreducibleCoprimeAction φ) {p : ℕ}
    (hp : p.Prime) (hpG : IsPGroup p G) {c : G} (hc : c ∈ _root_.commutator G) :
    c ^ p = 1 := by
  have hcen := h.commutator_le_center
  -- `Z(G)` の中の `p`-捻れ元全体は部分群
  let T : Subgroup G :=
    { carrier := {z : G | z ∈ Subgroup.center G ∧ z ^ p = 1}
      one_mem' := ⟨Subgroup.one_mem _, one_pow p⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
        have hab : Commute a b := (Subgroup.mem_center_iff.mp ha.1 b).symm
        rw [hab.mul_pow, ha.2, hb.2, one_mul]
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hle : _root_.commutator G ≤ T := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine ⟨hcen (commutatorElement_mem_commutator_top x y), ?_⟩
    rw [← commutatorElement_pow_left_of_class_le_two hcen x y p]
    refine commutatorElement_eq_one_iff_commute.mpr ?_
    exact Subgroup.mem_center_iff.mp (hcen (h.pow_mem_commutator hp hpG x)) y |>.symm
  exact (hle hc).2

/-- **Isaacs Problem 4D.3(f)**: `p > 2` なら `G` の指数は `p` (`x ^ p = 1`)。

class `≤ 2` + `G'` の指数 `p` ((e)) + `p` 奇 から `x ↦ x ^ p` は準同型
(`mul_pow_of_class_le_two` の補正項 `⁅y,x⁆ ^ (p(p-1)/2)` が `1` になる)。この準同型は
`A`-同変で像が `G'` に入り ((d)), `A` は `G'` 上自明に作用するので
`g⁻¹ · (φ a) g` はすべて核に入る。`⁅G, A⁆ = G` (`actionCommutator_eq_top`) より核は `G` 全体。 -/
theorem pow_eq_one_of_ne_two (h : IsIrreducibleCoprimeAction φ) {p : ℕ}
    (hp : p.Prime) (hpG : IsPGroup p G) (hp2 : p ≠ 2) (x : G) : x ^ p = 1 := by
  have hcen := h.commutator_le_center
  have hexp : ∀ c ∈ _root_.commutator G, c ^ p = 1 := fun _ hc =>
    h.pow_eq_one_of_mem_commutator hp hpG hc
  -- 補正項が消える: `p ∣ p * (p-1) / 2`
  have hdvd : p ∣ p * (p - 1) / 2 := by
    have h2 : 2 ∣ p - 1 := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · exact absurd h2 hp2
      · obtain ⟨k, hk⟩ := hodd
        exact ⟨k, by omega⟩
    rw [Nat.mul_div_assoc p h2]
    exact Dvd.intro _ rfl
  have hmul : ∀ x y : G, (x * y) ^ p = x ^ p * y ^ p := by
    intro x y
    rw [mul_pow_of_class_le_two hcen x y p]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, hexp _ (commutatorElement_mem_commutator_top y x), one_pow, mul_one]
  let f : G →* G :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := hmul }
  -- `⁅G, A⁆ ≤ ker f`
  have hker : actionCommutator φ ≤ f.ker := by
    rw [actionCommutator_le_iff_left]
    intro a g
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have hfa : f ((φ a) g) = f g := by
      change ((φ a) g) ^ p = g ^ p
      rw [← map_pow]
      exact h.trivial_on_commutator a _ (h.pow_mem_commutator hp hpG g)
    rw [hfa, inv_mul_cancel]
  rw [h.actionCommutator_eq_top, top_le_iff] at hker
  have hx : x ∈ f.ker := hker ▸ Subgroup.mem_top x
  exact hx

/-- **Isaacs Problem 4D.3(g)**: `p = 2` なら `x ^ 4 = 1`。

(d) で `x ^ 2 ∈ G'`, (e) で `G'` の指数は `2`。 -/
theorem pow_four_eq_one_of_two (h : IsIrreducibleCoprimeAction φ) (hpG : IsPGroup 2 G)
    (x : G) : x ^ 4 = 1 := by
  have h2 : (2 : ℕ).Prime := Nat.prime_two
  have hsq : x ^ 2 ∈ _root_.commutator G := h.pow_mem_commutator h2 hpG x
  have := h.pow_eq_one_of_mem_commutator h2 hpG hsq
  rwa [← pow_mul] at this

end IsIrreducibleCoprimeAction

/-! ### Problem 4D.4 -/

private lemma card_lt_card_of_lt {X : Type*} [Group X] [Finite X] {H₁ H₂ : Subgroup X}
    (hlt : H₁ < H₂) : Nat.card ↥H₁ < Nat.card ↥H₂ :=
  Set.Finite.card_lt_card (Set.toFinite _) (SetLike.coe_ssubset_coe.mpr hlt)

/-- `A`-不変部分群 `H` への制限作用で `A`-不変な `K ≤ H` は, `G` へ押し出しても `A`-不変. -/
theorem isAInvariant_map_subtype_of_isAInvariant {H : Subgroup G}
    (hH : Ch03.IsAInvariant φ H) {K : Subgroup ↥H}
    (hK : Ch03.IsAInvariant (OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH) K) :
    Ch03.IsAInvariant φ (K.map H.subtype) := by
  rw [Ch03.isAInvariant_iff_smul_mem]
  rintro a _ ⟨k, hk, rfl⟩
  exact ⟨_, hK.smul_mem a hk, rfl⟩

/-- **Isaacs Problem 4D.4**: 奇数位数の `A` が `2`-群 `G` に自己同型で作用し, `x ^ 4 = 1` を
満たす元をすべて固定するなら, `G` への作用は自明。

`|H|` についての強い帰納法。`A`-不変部分群 `H` への制限作用が非自明なら, 帰納法の仮定より
`A` は `H` の真の `A`-不変部分群すべてに自明に作用するので `IsIrreducibleCoprimeAction` が
成立し, **Problem 4D.3(g)** から `H` の全元が `y ^ 4 = 1` を満たす。すると仮定より `A` は
`H` を固定するので, いずれにせよ `A` は `H` 上で自明に作用する。

⚠ `p` が奇素数のときの対応物は Isaacs **Theorem 4.36** (`x ^ p = 1` を固定すれば自明) で,
そちらは Baer trick を使う。`p = 2` では `x ^ 2 = 1` では足りず `x ^ 4 = 1` が要る
(4D.3(g) が与える上界がちょうど `4`)。 -/
theorem actionCommutator_eq_bot_of_isPGroup_two_of_fixes_pow_four
    [Finite A] [Finite G] (hG : IsPGroup 2 G) (hA : Odd (Nat.card A))
    (hfix : ∀ x : G, x ^ 4 = 1 → ∀ a : A, (φ a) x = x) :
    actionCommutator φ = ⊥ := by
  have hmod : Nat.card A % 2 = 1 := Nat.odd_iff.mp hA
  have hnd : ¬ (2 ∣ Nat.card A) := by
    rintro ⟨k, hk⟩
    omega
  have hcop2 : Nat.Coprime (Nat.card A) 2 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd)
  have key : ∀ n : ℕ, ∀ H : Subgroup G, Nat.card ↥H ≤ n → Ch03.IsAInvariant φ H →
      ∀ a : A, ∀ x ∈ H, (φ a) x = x := by
    intro n
    induction n with
    | zero =>
      intro H hcard _ _ _ _
      have hpos : 0 < Nat.card ↥H := Nat.card_pos
      omega
    | succ n ih =>
      intro H hcard hHinv a x hx
      by_cases hbot : actionCommutator (OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hHinv) = ⊥
      · exact congrArg Subtype.val
          ((actionCommutator_eq_bot_iff_acts_trivially _).mp hbot a ⟨x, hx⟩)
      · have hHp : IsPGroup 2 ↥H := hG.to_subgroup H
        have : Group.IsNilpotent ↥H := hHp.isNilpotent
        have hcop : Nat.Coprime (Nat.card A) (Nat.card ↥H) := by
          obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥H)).mp hHp
          rw [hk]
          exact Nat.Coprime.pow_right k hcop2
        have hirr : IsIrreducibleCoprimeAction
            (OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hHinv) :=
          { coprime := hcop
            solvable := Or.inr inferInstance
            trivial_on_proper := by
              intro K hKinv hKne b y hy
              refine Subtype.ext (ih _ ?_ (isAInvariant_map_subtype_of_isAInvariant hHinv hKinv)
                b (y : G) ⟨y, hy, rfl⟩)
              rw [Subgroup.card_subtype]
              have h1 : Nat.card ↥K < Nat.card ↥(⊤ : Subgroup ↥H) :=
                card_lt_card_of_lt (lt_top_iff_ne_top.mpr hKne)
              rw [Subgroup.card_top] at h1
              omega
            nontrivial := hbot }
        exact hfix x (congrArg Subtype.val (hirr.pow_four_eq_one_of_two hHp ⟨x, hx⟩)) a
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  exact key (Nat.card ↥(⊤ : Subgroup G)) ⊤ le_rfl
    (Ch03.isAInvariant_iff_smul_mem.mpr fun _ _ _ => Subgroup.mem_top _) a g (Subgroup.mem_top g)

end

end OddOrder.Isaacs.Ch04
