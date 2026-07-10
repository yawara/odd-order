/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116
import OddOrder.BG.Ch1_Preliminary.S03_FrobeniusActions
import OddOrder.BG.Ch1_Preliminary.S03f_OrbitParity
import OddOrder.BG.Ch1_Preliminary.S03f_Prelim
import OddOrder.BG.Ch1_Preliminary.S03d_Thm34
import OddOrder.BG.Ch1_Preliminary.S03e_Thm35
import OddOrder.BG.Ch1_Preliminary.PLengthTransfer
import OddOrder.BG.Ch1_Preliminary.OperatorQuotientAction
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke
import OddOrder.GroupTheory.ZGroup


/-!
# BG §3: Theorem 3.6 (the p-length-one subprogram, mmd L955)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §3, mmd `references/bg/local-analysis.mmd` L955-1194.

**BG Theorem 3.6**: Let `G` be a solvable group of odd order, `H ◁ G` a normal Hall subgroup,
`R` a complement of `H`, and `R₀ ≤ R` of prime order such that `C_H(R₀)` is a `Z`-group.  Then for
every prime `p`, the commutator `[H, R]` has `p`-length one.

This is the **vertex of the §3 subprogram** and the engine of BG Theorem 10.6 (the `r_p ≥ 3` case);
it consumes the rest of §3: Lemma 1.21, Theorem 3.4 (`S03d`, ✅), Theorem 3.5 (`S03e`, ✅), Lemma 3.1,
Gorenstein 5.3.7 (`S04e`, ✅), and a long list of §1 propositions.

## 証明構造 (minimal counterexample, equations (3.6)–(3.38), ~4 pages)

Strong induction on `|G|`; let `G` be a counterexample of minimal order, `r = |R₀|`, so `[H, R]`
does **not** have `p`-length one and `p ≠ r`.

* **Phase A — 還元** (3.6)–(3.11):
  - (3.6) `H = [H, R]` — else `[H,R]R < G` and IH + Prop 1.6(b) (`[[H,R],R] = [H,R]`) contradict.
  - (3.7) `H/X` has `p`-length one for any `1 ≠ X ◁ H` with `Xᴿ = X` — IH on `H/X`, Prop 1.5(d).
  - (3.8) `O_{p'}(H) = 1` — else Lem 1.21(b) on `H/O_{p'}(H)`.
  - (3.9) `V := F(H) = O_p(H)` is elementary abelian — `O_{p'}(H)=1` ⟹ `F(H)` a `p`-group; the
    preimage of `O_{p'}(H/Φ(V))` is a `p`-group (Thm 1.8 + Prop 1.3), so if `Φ(V)≠1` then
    Lem 1.21(c) on `H/Φ(V)` gives a contradiction; `Φ(V)=1` + Lem 1.7 ⟹ `V` elementary abelian.
  - (3.10) `C_H(V) = V` — Prop 1.3.
  - (3.11) `V` contains a **unique** minimal normal subgroup of `G` — else Lem 1.21(e).
* **Phase B — 補群 `K`** (3.12)–(3.16): `U =` preimage of `F(H/V)`, `K` an `R`-invariant complement
  to `V` in `U` (Prop 1.5(a) + Schur–Zassenhaus); Frattini `H = VN_H(K)` (3.12); `[K,P]≠1` (3.13);
  `[V,K]=V`, `C_V(K)=1` (3.14, Prop 1.6(d) + (3.11)); `K = F(N_H(K))` (3.15); `C_H(K) ⊆ K` (3.16).
* **Phase C — `R₀` の作用** (3.17)–(3.21): `[K,R₀]≠1` (3.17, Prop 1.4); `C_{KR₀}(V)=1` (3.18);
  `|C_V(R₀)|=p` ⟸ **Thm 3.4** + `Z`-group (3.18→3.19); `C_P(R₀)=1` (3.20);
  `P=[P,R₀]` (3.21, Prop 1.6a).
* **Phase D — `G` の構造** (3.22)–(3.31): `[X,P]=1` for `X=Xᴾᴿ⊊K` (3.22, minimality); `G=VKPR₀`,
  `H=VKP`, `R=R₀` (3.23); `K=[K,P]` (3.24); `K` special `q`-group (3.25, **Gor 5.3.7**) of exponent
  `q` (3.26, Thm 1.13); `C_{PR}(K)=1` (3.28); `C_{PR}(K/K')=1` (3.29, Thm 1.8); `C_{K/K'}(R)≠1`
  (3.30, **Thm 3.4**); `|C_K(R)|=q`, `C_K(R)∩K'=1` (3.31, `Z`-group).
* **Phase E — `K` elementary abelian** (3.32)–(3.37): `K≠[K,R]` (3.32); `C_{[K,R]}(R)=1` (3.33);
  `[K,R]R` Frobenius (Lem 3.1); **Thm 3.5** ⟹ `[K,R]` abelian (3.34); `[K,R]` not `P`-invariant
  (3.35); `|K:Z(K)|≤q` ⟸ **Thm 2.6(a)** ⟹ `K` elementary abelian (3.36); `|K|>q²` (3.37, Thm 2.6).
* **Phase F — 最終矛盾** (3.38–): `V = ⊕ Vᵢ` (`Vᵢ = C_V(Kᵢ) ≠ 1`, index-`q` `Kᵢ`; **Prop 1.16**);
  `RP` transitive on `{Vᵢ}` (3.11); orbit-length analysis + `|V₁| = p` (3.19) + parity (`n` odd vs
  even from the orbit structure) yields the final contradiction.  IH-free, hence split off to
  `S03f_OrbitParity.orbit_parity_contradiction`.

## 依存 (全て✅、`notes/bg/s03_thm36_plan.md` 参照)

Lemma 1.21(a)(b)(c)(e) (`PLengthTransfer`), Theorem 3.4 (`S03d.thm34`), Theorem 3.5 (`S03e.thm35`),
Lemma 3.1/3.3 (`S03`/`S03b`), Gorenstein 5.3.7 (`S04e`), Prop 1.3/1.4/1.5/1.6/1.16 (`S01`/`S01b`/
`OperatorQuotientAction`), Theorem 1.8/1.13 (`S01`/`CriticalSubgroup`), Theorem 2.6 (`S02`/`S04`).

**状態 (2026-06-10)**: ✅ **COMPLETE** — Phase A–F すべて sorry-free.  詳細経緯 =
`notes/bg/s03_thm36_plan.md`.
-/

-- 単一の巨大宣言 (thm36_aux, ~3.7k 行) のため分割不能 — CLAUDE.md の明示例外
set_option linter.style.longFile 4000

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement Pointwise IsMulCommutative
open OddOrder.GroupTheory OddOrder.Isaacs.Ch04 OddOrder.BG.Ch1.OperatorQuotientAction

set_option maxHeartbeats 2400000 in
-- the `IsMulCommutative` scoped instances (priority 50) cycle with `CommMagma.to_isCommutative`;
-- failing class searches on `↥KG ⧸ commutator ↥KG` (Phase D, (3.29)–(3.30)) must exhaust that
-- branch, which overflows the default 20000 budget (results are cached per goal, so this is a
-- one-time cost per distinct search)
set_option synthInstance.maxHeartbeats 400000 in
/-- **BG Theorem 3.6, minimal-counterexample core** (strong induction on `|G|`, mmd L955).

The hypotheses are exactly those of `thm36`, with an extra `Nat.card G = n` so the strong induction
can apply the IH to proper subgroups (`⁅H,R⁆R` at (3.6), `VXPR₀` at (3.22)) and quotients (`G/X` at
(3.7)).  The proof opens with `by_contra hcounter` (the counterexample assumption
`¬ hasPLengthOne p ↥⁅H,R⁆`) and derives the chain (3.6)–(3.38); each place that proves "`H` has
`p`-length one" contradicts `hcounter` (via `H = ⁅H,R⁆` from (3.6)), and the orbit-parity argument
(3.38) is the final contradiction.

**状態**: ✅ Phase A–F ((3.6)–(3.38)) すべて完了, sorry-free.
消費済み大物: Thm 3.4 ×2 ((3.19),(3.30)), Thm 3.5 ((3.34)), Gor 5.3.7 ((3.25)),
**Thm 2.6(a) ×2 ((3.36) の `|K:Z|=q²` 枝, (3.37) の dim-2 枝)**, Prop 1.16(2) ((3.38)).
Phase F ((3.38), IH-free) は `S03f_OrbitParity.orbit_parity_contradiction` に分離 —
ここでは (3.36)/(3.37) までの確立事実を渡して `False` を受け取るだけ.

(`maxHeartbeats`: equations (3.6)–(3.37) を 1 つの minimal-counterexample 証明で運ぶため宣言が
巨大で、既定の 200000 を超える。IH を消費する Phase A–E は誘導の内側から切り出せないため、
これ以上の分割は IH 自体の仮説化が要る。) -/
private theorem thm36_aux : ∀ (n : ℕ)
    {G : Type*} [Group G] [Finite G] [IsSolvable G],
    Odd (Nat.card G) →
    ∀ {H R : Subgroup G} [H.Normal],
    Subgroup.IsComplement' H R →
    Nat.Coprime (Nat.card ↥H) (Nat.card ↥R) →
    ∀ {R₀ : Subgroup G}, R₀ ≤ R → (∃ r : ℕ, r.Prime ∧ Nat.card ↥R₀ = r) →
    OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) →
    ∀ {p : ℕ}, p.Prime →
    Nat.card G = n →
    hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ _ hodd H R _ hcompl hHall R₀ hR₀R hR₀p hZ p hp hn
    haveI : Fact p.Prime := ⟨hp⟩
    by_contra hcounter
    -- `⁅H,R⁆ ≤ H` (H normal).
    have hHR_le_H : (⁅H, R⁆ : Subgroup G) ≤ H := Subgroup.commutator_le_left H R
    -- **(3.6)** `H = ⁅H, R⁆`.  Suppose not; then `⁅H,R⁆R < G` and IH gives `⁅⁅H,R⁆,R⁆` `p`-length
    -- one, but `⁅⁅H,R⁆,R⁆ = ⁅H,R⁆` (Prop 1.6(b)), contradicting `hcounter`.
    have h36 : (⁅H, R⁆ : Subgroup G) = H := by
      by_contra h36ne
      have hHRlt : (⁅H, R⁆ : Subgroup G) < H := lt_of_le_of_ne hHR_le_H h36ne
      set S : Subgroup G := ⁅H, R⁆ ⊔ R with hS
      have hHR_le_S : (⁅H, R⁆ : Subgroup G) ≤ S := le_sup_left
      have hR_le_S : R ≤ S := le_sup_right
      -- `S ≤ N_G(⁅H,R⁆)`: `⁅H,R⁆` self-normalizes, `R` normalizes `⁅R,H⁆ = ⁅H,R⁆` (Isaacs Lem 4.1).
      have hSnorm : S ≤ Subgroup.normalizer (⁅H, R⁆ : Subgroup G) :=
        sup_le Subgroup.le_normalizer
          (Subgroup.commutator_comm R H ▸ subgroup_le_normalizer_commutator_self R H)
      haveI hH'normal : ((⁅H, R⁆ : Subgroup G).subgroupOf S).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hSnorm
      -- card transport: `|⁅H,R⁆.subgroupOf S| = |⁅H,R⁆|`, `|R.subgroupOf S| = |R|`.
      have hHRcard : Nat.card ↥((⁅H, R⁆ : Subgroup G).subgroupOf S)
          = Nat.card ↥(⁅H, R⁆ : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHR_le_S).toEquiv
      have hRcard : Nat.card ↥(R.subgroupOf S) = Nat.card ↥R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le_S).toEquiv
      have hSdvd : Nat.card ↥S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
      -- complement `⁅H,R⁆.subgroupOf S` ⋈ `R.subgroupOf S` inside `S`.
      have hcompl' :
          Subgroup.IsComplement' ((⁅H, R⁆ : Subgroup G).subgroupOf S) (R.subgroupOf S) := by
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
        · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
          rw [Subgroup.mem_inf] at hx
          simp only [Subgroup.mem_subgroupOf] at hx
          have hmem : (x : G) ∈ (⁅H, R⁆ : Subgroup G) ⊓ R := ⟨hx.1, hx.2⟩
          have hdisj : Disjoint (⁅H, R⁆ : Subgroup G) R := hcompl.disjoint.mono_left hHR_le_H
          rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]; exact Subtype.ext (by simpa using hmem)
        · have hsup : ((⁅H, R⁆ : Subgroup G).subgroupOf S) ⊔ (R.subgroupOf S) = ⊤ := by
            rw [← Subgroup.subgroupOf_sup hHR_le_S hR_le_S, Subgroup.subgroupOf_self]
          have hmul := Subgroup.normal_mul ((⁅H, R⁆ : Subgroup G).subgroupOf S) (R.subgroupOf S)
          rw [hsup, Subgroup.coe_top] at hmul
          exact hmul.symm
      have hHall' : Nat.Coprime (Nat.card ↥((⁅H, R⁆ : Subgroup G).subgroupOf S))
          (Nat.card ↥(R.subgroupOf S)) := by
        rw [hHRcard, hRcard]
        exact hHall.coprime_dvd_left (Subgroup.card_dvd_of_le hHR_le_H)
      have hodd' : Odd (Nat.card ↥S) := by
        obtain ⟨m, hm⟩ := hSdvd; rw [hm, Nat.odd_mul] at hodd; exact hodd.1
      -- `R₀ ≤ R ≤ S`; transport `R₀` into `S`.
      have hR₀S : R₀ ≤ S := hR₀R.trans hR_le_S
      have hR₀R' : R₀.subgroupOf S ≤ R.subgroupOf S := Subgroup.subgroupOf_mono S hR₀R
      have hR₀card : Nat.card ↥(R₀.subgroupOf S) = Nat.card ↥R₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀S).toEquiv
      have hR₀p' : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R₀.subgroupOf S) = r := by
        obtain ⟨r, hr, hrc⟩ := hR₀p; exact ⟨r, hr, hR₀card.trans hrc⟩
      -- **Z-group transport** (subgroup case): `C_S(R₀') ↪ C_H(R₀)` via `S.subtype`, then
      -- `IsZGroup.of_injective`.  `(C_S(R₀')).map S.subtype ≤ ⁅H,R⁆ ⊓ C_G(R₀) ≤ H ⊓ C_G(R₀)`.
      have hZ' : OddOrder.GroupTheory.IsZGroup
          ↥((⁅H, R⁆ : Subgroup G).subgroupOf S
            ⊓ Subgroup.centralizer (R₀.subgroupOf S : Set ↥S)) := by
        set A : Subgroup ↥S :=
          (⁅H, R⁆ : Subgroup G).subgroupOf S
            ⊓ Subgroup.centralizer (R₀.subgroupOf S : Set ↥S) with hA
        have hle : A.map S.subtype ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) := by
          rintro _ ⟨a, ha, rfl⟩
          obtain ⟨haHR, hacent⟩ := Subgroup.mem_inf.mp ha
          rw [Subgroup.mem_subgroupOf] at haHR
          refine Subgroup.mem_inf.mpr
            ⟨hHR_le_H haHR, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
          have hgS : g ∈ S := hR₀S hg
          have hcomm := (Subgroup.mem_centralizer_iff.mp hacent) (⟨g, hgS⟩ : ↥S)
            (Subgroup.mem_subgroupOf.mpr hg)
          exact congrArg (Subtype.val) hcomm
        haveI : _root_.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) :=
          isZGroup_iff_mathlib.mp hZ
        haveI : _root_.IsZGroup ↥(A.map S.subtype) :=
          IsZGroup.of_injective (Subgroup.inclusion_injective hle)
        have e := Subgroup.equivMapOfInjective A S.subtype (Subgroup.subtype_injective S)
        haveI : _root_.IsZGroup ↥A := IsZGroup.of_injective (f := e.toMonoidHom) e.injective
        exact isZGroup_iff_mathlib.mpr ‹_root_.IsZGroup ↥A›
      have hScard : Nat.card ↥S < n := by
        have e1 : Nat.card ↥((⁅H, R⁆ : Subgroup G).subgroupOf S) * Nat.card ↥(R.subgroupOf S)
            = Nat.card ↥S := hcompl'.card_mul
        have e2 : Nat.card ↥H * Nat.card ↥R = Nat.card G := hcompl.card_mul
        rw [hHRcard, hRcard] at e1
        have hHRltcard : Nat.card ↥(⁅H, R⁆ : Subgroup G) < Nat.card ↥H := by
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hHR_le_H))
            (fun heq => (ne_of_lt hHRlt) (Subgroup.eq_of_le_of_card_ge hHR_le_H heq.ge))
        rw [← hn, ← e2, ← e1]
        exact mul_lt_mul_of_pos_right hHRltcard Nat.card_pos
      -- apply IH to `S` with `(⁅H,R⁆.subgroupOf S, R.subgroupOf S, R₀.subgroupOf S)`.
      have hIH := IH (Nat.card ↥S) hScard hodd' hcompl' hHall' hR₀R' hR₀p' hZ' hp rfl
      -- conclusion bridge: `⁅H',R'⁆` in `S` ≅ `⁅⁅H,R⁆,R⁆` in `G` (map S.subtype), then Prop 1.6(b).
      have hmapeq : (⁅(⁅H, R⁆ : Subgroup G).subgroupOf S, R.subgroupOf S⁆ : Subgroup ↥S).map
          S.subtype = ⁅(⁅H, R⁆ : Subgroup G), R⁆ := by
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hHR_le_S, inf_eq_left.mpr hR_le_S]
      have hiso := Subgroup.equivMapOfInjective
        (⁅(⁅H, R⁆ : Subgroup G).subgroupOf S, R.subgroupOf S⁆) S.subtype
        (Subgroup.subtype_injective S)
      have hpl := hasPLengthOne_of_mulEquiv (p := p) hiso hIH
      rw [hmapeq, commutator_commutator_right_eq H R hHall] at hpl
      exact hcounter hpl
    -- **(3.7)** `H/X` has `p`-length one for nontrivial `X ⊴ G` with `X ≤ H` (`R`-invariance is
    -- automatic from `X ⊴ G`).  Apply IH to `G ⧸ X`; the quotient `Z`-group hypothesis is
    -- Prop 1.5(d) (`coprime_fixedPoints_quotient`), and `⁅HQ,RQ⁆ = H.map(mk' X)` by (3.6).
    have h37 : ∀ (X : Subgroup G) [X.Normal], X ≠ ⊥ → X ≤ H →
        hasPLengthOne p (↥H ⧸ X.subgroupOf H) := by
      intro X _ hXne hXH
      have hcardX : 1 < Nat.card ↥X := by
        have hne1 : Nat.card ↥X ≠ 1 := fun h => hXne (Subgroup.eq_bot_of_card_eq X h)
        have hpos : 0 < Nat.card ↥X := Nat.card_pos
        omega
      have hcardG : Nat.card G = Nat.card (G ⧸ X) * Nat.card ↥X :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup X
      have hcardQ : Nat.card (G ⧸ X) < n := by
        rw [← hn, hcardG]
        exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr hcardX
      have hoddQ : Odd (Nat.card (G ⧸ X)) := by
        rw [hcardG, Nat.odd_mul] at hodd; exact hodd.1
      haveI hHQnorm : (H.map (QuotientGroup.mk' X)).Normal :=
        (inferInstance : H.Normal).map (QuotientGroup.mk' X) (QuotientGroup.mk'_surjective X)
      have hcomplQ : Subgroup.IsComplement' (H.map (QuotientGroup.mk' X))
          (R.map (QuotientGroup.mk' X)) :=
        OddOrder.BG.Ch1.S03.quotient_complement_of_normal_le_kernel hcompl hXH
      have hHallQ : Nat.Coprime (Nat.card ↥(H.map (QuotientGroup.mk' X)))
          (Nat.card ↥(R.map (QuotientGroup.mk' X))) := by
        refine (hHall.coprime_dvd_left ?_).coprime_dvd_right ?_
        · exact Subgroup.card_map_dvd _ _
        · exact Subgroup.card_map_dvd _ _
      have hR₀RQ : R₀.map (QuotientGroup.mk' X) ≤ R.map (QuotientGroup.mk' X) :=
        Subgroup.map_mono hR₀R
      have hR₀pQ : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R₀.map (QuotientGroup.mk' X)) = r := by
        obtain ⟨r, hr, hrc⟩ := hR₀p
        refine ⟨r, hr, ?_⟩
        -- `mk' X` is injective on `R₀` since `R₀ ⊓ X ≤ R ⊓ H = ⊥`.
        have hdisj : Disjoint R₀ X := hcompl.disjoint.symm.mono hR₀R hXH
        have hinj : Function.Injective ⇑((QuotientGroup.mk' X).comp R₀.subtype) := by
          rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
          intro x hx
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
            QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
          have hmem : (x : G) ∈ R₀ ⊓ X := ⟨x.2, hx⟩
          rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]; exact Subtype.ext hmem
        have hrange : ((QuotientGroup.mk' X).comp R₀.subtype).range
            = R₀.map (QuotientGroup.mk' X) := by
          rw [MonoidHom.range_comp, R₀.range_subtype]
        rw [← hrc, ← hrange]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hZQ : OddOrder.GroupTheory.IsZGroup ↥((H.map (QuotientGroup.mk' X)) ⊓
          Subgroup.centralizer
            ((R₀.map (QuotientGroup.mk' X) : Subgroup (G ⧸ X)) : Set (G ⧸ X))) := by
        -- **Prop 1.5(d) transport**: `C_{H/X}(R₀) ≤ (H ⊓ C_G(R₀)).map (mk' X)` (image of the
        -- `Z`-group), via `coprime_fixedPoints_quotient` on the conjugation action of `R₀` on `H`.
        set φ : ↥R₀ →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R₀.subtype with hφ
        have hval : ∀ (a : ↥R₀) (k : ↥H), (((φ a) k : ↥H) : G) = (a : G) * (k : G) * (a : G)⁻¹ := by
          intro a k
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
        have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (X.subgroupOf H) := by
          rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
          intro a k hk
          rw [Subgroup.mem_subgroupOf] at hk ⊢
          rw [hval]
          exact (inferInstance : X.Normal).conj_mem (k : G) hk (a : G)
        have hCopR₀ : Nat.Coprime (Nat.card ↥R₀) (Nat.card ↥H) :=
          (hHall.coprime_dvd_right (Subgroup.card_dvd_of_le hR₀R)).symm
        have hle : (H.map (QuotientGroup.mk' X)) ⊓ Subgroup.centralizer
            ((R₀.map (QuotientGroup.mk' X) : Subgroup (G ⧸ X)) : Set (G ⧸ X))
            ≤ (H ⊓ Subgroup.centralizer (R₀ : Set G)).map (QuotientGroup.mk' X) := by
          rintro _ hq
          obtain ⟨hqH, hqcent⟩ := Subgroup.mem_inf.mp hq
          obtain ⟨h, hhH, rfl⟩ := hqH
          have hcomm : ∀ a : ↥R₀, (QuotientGroup.mk' X) (a : G) * (QuotientGroup.mk' X) h
              = (QuotientGroup.mk' X) h * (QuotientGroup.mk' X) (a : G) :=
            fun a => (Subgroup.mem_centralizer_iff.mp hqcent) _ ⟨(a : G), a.2, rfl⟩
          have hg_fix : ∀ a : ↥R₀, ∃ nn ∈ X.subgroupOf H, (φ a) ⟨h, hhH⟩ = ⟨h, hhH⟩ * nn := by
            intro a
            refine ⟨⟨h, hhH⟩⁻¹ * (φ a) ⟨h, hhH⟩, ?_, by group⟩
            have hnnval : ((⟨h, hhH⟩⁻¹ * (φ a) ⟨h, hhH⟩ : ↥H) : G)
                = h⁻¹ * ((a : G) * h * (a : G)⁻¹) := by
              rw [Subgroup.coe_mul, Subgroup.coe_inv, hval]
            rw [Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
              hnnval]
            simp only [map_mul, map_inv]
            rw [hcomm a]
            group
          obtain ⟨c, hc_fix, nn, hnnN, hcnn⟩ :=
            OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hCopR₀ (Or.inr inferInstance)
              hN_inv hg_fix
          refine ⟨(c : G), Subgroup.mem_inf.mpr ⟨c.2, ?_⟩, ?_⟩
          · rw [Subgroup.mem_centralizer_iff]
            intro g hg
            have hcc : (g : G) * (c : G) * (g : G)⁻¹ = (c : G) := by
              have hh := congrArg (Subtype.val) (hc_fix ⟨g, hg⟩)
              rwa [hval] at hh
            exact mul_inv_eq_iff_eq_mul.mp hcc
          · have hcval : (c : G) = h * (nn : G) := by
              have hh := congrArg (Subtype.val) hcnn
              rwa [Subgroup.coe_mul] at hh
            rw [hcval, map_mul, show (QuotientGroup.mk' X) (nn : G) = 1 from
              (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mp hnnN), mul_one]
        haveI : _root_.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) :=
          isZGroup_iff_mathlib.mp hZ
        haveI : _root_.IsZGroup
            ↥((H ⊓ Subgroup.centralizer (R₀ : Set G)).map (QuotientGroup.mk' X)) :=
          IsZGroup.of_surjective (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' X) _)
        exact isZGroup_iff_mathlib.mpr (IsZGroup.of_injective (Subgroup.inclusion_injective hle))
      have hIH := IH (Nat.card (G ⧸ X)) hcardQ hoddQ hcomplQ hHallQ hR₀RQ hR₀pQ hZQ hp rfl
      -- bridge: `⁅HQ,RQ⁆ = ⁅H,R⁆.map(mk' X) = H.map(mk' X)` by (3.6).
      have hbridge : (⁅H.map (QuotientGroup.mk' X), R.map (QuotientGroup.mk' X)⁆ : Subgroup (G ⧸ X))
          = H.map (QuotientGroup.mk' X) := by
        rw [← Subgroup.map_commutator, h36]
      rw [hbridge] at hIH
      -- iso `↥H ⧸ X.subgroupOf H ≃* ↥(H.map (mk' X))`, transport `p`-length one.
      have hker : ((QuotientGroup.mk' X).comp H.subtype).ker = X.subgroupOf H := by
        ext x
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hrange : ((QuotientGroup.mk' X).comp H.subtype).range = H.map (QuotientGroup.mk' X) := by
        rw [MonoidHom.range_comp, H.range_subtype]
      have hiso : (↥H ⧸ X.subgroupOf H) ≃* ↥(H.map (QuotientGroup.mk' X)) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange))
      exact hasPLengthOne_of_mulEquiv (p := p) hiso.symm hIH
    -- **(3.8)** `O_{p'}(H) = ⊥`.  Else `X := O_{p'}(H)` lifted to `G` feeds (3.7) + Lemma 1.21(b)
    -- to make `H = ⁅H,R⁆` have `p`-length one, contradicting `hcounter`.
    have h38 : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥H = ⊥ := by
      by_contra h38ne
      -- capture the `oPiCore` instances, then make `N` opaque (avoids `set`+`rw` motive errors).
      set N : Subgroup ↥H := OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥H with hN
      haveI hNnormal : N.Normal := OddOrder.Isaacs.Ch03.oPiCore.normal ({p}ᶜ : Set ℕ) ↥H
      haveI hNchar : N.Characteristic := OddOrder.Isaacs.Ch03.oPiCore.characteristic ({p}ᶜ) ↥H
      have hNpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p}ᶜ : Set ℕ) N :=
        OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥H) ({p}ᶜ : Set ℕ)
      clear_value N
      have hkerbot : (H.subtype).ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
      have hXH : N.map H.subtype ≤ H := Subgroup.map_subtype_le N
      have hsubgroupOf : (N.map H.subtype).subgroupOf H = N :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
      -- `N.map H.subtype ⊴ G`: characteristic in the normal `H` (conjugation = `conjNormal`).
      haveI hXnormal : (N.map H.subtype).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hnH : n ∈ H := hXH hn
        have hmemN : (⟨n, hnH⟩ : ↥H) ∈ N := by
          have hm : (⟨n, hnH⟩ : ↥H) ∈ (N.map H.subtype).subgroupOf H := by
            rw [Subgroup.mem_subgroupOf]; exact hn
          rwa [hsubgroupOf] at hm
        have hfix : N.map (MulAut.conjNormal g).toMonoidHom = N :=
          Subgroup.characteristic_iff_map_eq.mp hNchar (MulAut.conjNormal g)
        have himg : MulAut.conjNormal g (⟨n, hnH⟩ : ↥H) ∈ N := by
          rw [← hfix]; exact Subgroup.mem_map_of_mem _ hmemN
        exact ⟨MulAut.conjNormal g ⟨n, hnH⟩, himg, by
          rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]⟩
      have hXne : N.map H.subtype ≠ ⊥ := by
        intro h
        rw [Subgroup.map_eq_bot_iff, hkerbot, le_bot_iff] at h
        exact h38ne h
      have h37N := h37 (N.map H.subtype) hXne hXH
      replace h37N := hasPLengthOne_of_mulEquiv (p := p)
        (QuotientGroup.quotientMulEquivOfEq hsubgroupOf) h37N
      have hNp' : ¬ p ∣ Nat.card ↥N := by
        intro hdvd
        have hpmem := hNpi p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
        simp at hpmem
      apply hcounter
      rw [h36]
      exact hasPLengthOne_of_isPiPrime_normal_quotient hNp' h37N
    -- **(3.9)** `V := F(H) = O_p(H)` is an elementary abelian `p`-group.
    -- Part 1: `F(H) = O_p(H)` — since `O_{p'}(H) = ⊥` (3.8), every `O_q(H)` (`q ≠ p`) is `⊥`.
    have hfit : OddOrder.Isaacs.Ch01.fitting ↥H = OddOrder.Isaacs.Ch01.opCore p ↥H :=
      fitting_eq_opCore_of_oPiCore_compl_eq_bot hp h38
    have hVp : IsPGroup p ↥(OddOrder.Isaacs.Ch01.fitting ↥H) := by
      rw [hfit]; exact OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥H
    -- `Φ(V)` lifted to `↥H` is characteristic (hence normal, and its further `G`-lift is normal).
    haveI hPhiChar :
        ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting ↥H)).map
          (OddOrder.Isaacs.Ch01.fitting ↥H).subtype).Characteristic :=
      frattini_fitting_map_characteristic
    -- **(3.9) Part 2-4**: `Φ(V) = ⊥`, hence (Lemma 1.7(c)) `V` is elementary abelian.  If
    -- `Φ(V) ≠ ⊥`, its `G`-lift `X` feeds (3.7) + Lemma 1.21(c) (`O_{p'}(H/Φ(V)) = ⊥` from
    -- `S03f_Prelim`) to make `H` have `p`-length one, contradicting `hcounter` via (3.6).
    have hΦbot : _root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting ↥H) = ⊥ := by
      by_contra hΦne
      set Phi : Subgroup ↥H := (_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting ↥H)).map
        (OddOrder.Isaacs.Ch01.fitting ↥H).subtype with hPhidef
      have hPhi_le_V : Phi ≤ OddOrder.Isaacs.Ch01.fitting ↥H := Subgroup.map_subtype_le _
      have hPhiP : IsPGroup p ↥Phi :=
        hVp.of_injective (Subgroup.inclusion hPhi_le_V) (Subgroup.inclusion_injective hPhi_le_V)
      have hkerbotV : ((OddOrder.Isaacs.Ch01.fitting ↥H).subtype).ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)
      have hPhi_ne : Phi ≠ ⊥ := by
        intro h
        rw [hPhidef, Subgroup.map_eq_bot_iff, hkerbotV, le_bot_iff] at h
        exact hΦne h
      -- lift `Phi` to `G`: `X := Phi.map H.subtype` — normal (char-in-normal), `≤ H`, `≠ ⊥`.
      set X : Subgroup G := Phi.map H.subtype with hXdef
      have hX_le_H : X ≤ H := Subgroup.map_subtype_le _
      have hkerbot : (H.subtype).ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
      have hX_ne : X ≠ ⊥ := by
        intro h
        rw [hXdef, Subgroup.map_eq_bot_iff, hkerbot, le_bot_iff] at h
        exact hPhi_ne h
      have hX_subgroupOf : X.subgroupOf H = Phi :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective Phi
      have h37X := h37 X hX_ne hX_le_H
      replace h37X := hasPLengthOne_of_mulEquiv (p := p)
        (QuotientGroup.quotientMulEquivOfEq hX_subgroupOf) h37X
      have hOp' : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ)
          (↥H ⧸ Phi) = ⊥ := oPiCore_compl_quotient_frattini_fitting_eq_bot hVp
      have hHpl : hasPLengthOne p ↥H :=
        hasPLengthOne_of_isPGroup_normal_quotient hPhiP hOp' h37X
      apply hcounter
      rw [h36]; exact hHpl
    -- **(3.9)** `V` is elementary abelian.
    have hVelem : OddOrder.GroupTheory.IsElementaryAbelian p ↥(OddOrder.Isaacs.Ch01.fitting ↥H) :=
      (OddOrder.BG.Ch1.S01.frattini_eq_bot_iff_isElementaryAbelian hVp).mp hΦbot
    -- **(3.10)** `C_H(V) = V` (Proposition 1.3 `centralizer_fitting_le_fitting` + `V` abelian).
    have hCHV : Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting ↥H : Subgroup ↥H) : Set ↥H)
        = OddOrder.Isaacs.Ch01.fitting ↥H := by
      refine le_antisymm OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting ?_
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      simpa using congrArg (Subtype.val) (hVelem.1 ⟨w, hw⟩ ⟨v, hv⟩)
    -- **(3.11)** `V` contains a unique minimal normal subgroup of `G`.  In the form needed
    -- downstream (3.14, Phase F): two normal subgroups of `G` inside `H` that intersect trivially
    -- cannot both be nontrivial — else (3.7) on each quotient + Lemma 1.21(e) make `H` have
    -- `p`-length one.
    have h311 : ∀ (A B : Subgroup G) [A.Normal] [B.Normal], A ≤ H → B ≤ H →
        A ⊓ B = ⊥ → A = ⊥ ∨ B = ⊥ := by
      intro A B _ _ hAH hBH hAB
      by_contra hcon
      push Not at hcon
      have hplA := h37 A hcon.1 hAH
      have hplB := h37 B hcon.2 hBH
      have hinf : (A.subgroupOf H) ⊓ (B.subgroupOf H) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        simp only [Subgroup.mem_subgroupOf] at hx
        have hmem : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
        rw [hAB, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]; exact Subtype.ext (by simpa using hmem)
      have hHpl : hasPLengthOne p ↥H := hasPLengthOne_of_inf_eq_bot hinf hplA hplB
      apply hcounter; rw [h36]; exact hHpl
    -- ===== Phase B (3.12)–(3.16): the complement `K` =====
    -- Abbreviate `V := F(H)` (folding the (3.9)/(3.10) facts) and record `V = O_p(H)`.
    set V : Subgroup ↥H := OddOrder.Isaacs.Ch01.fitting ↥H with hVdef
    haveI hVnorm : V.Normal := by rw [hVdef]; infer_instance
    have hVoPi : V = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H := by
      rw [hfit, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
    -- `F(H/V)` is a `p'`-group (so `V` is a normal Hall `p`-subgroup of the preimage `U` of
    -- `F(H/V)`).  Proved with the denominator kept as a variable to avoid dependent rewriting
    -- through `hVoPi`.
    have hFQ_compl : ∀ (N : Subgroup ↥H) [N.Normal],
        N = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H →
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p}ᶜ : Set ℕ)
          (OddOrder.Isaacs.Ch01.fitting (↥H ⧸ N)) := by
      intro N _ hN
      subst hN
      set Q : Type _ := ↥H ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H with hQ
      intro q hqF hqπ
      have hq_prime : q.Prime := (Nat.mem_primeFactors.mp hqF).1
      haveI : Fact q.Prime := ⟨hq_prime⟩
      have hq_dvd : q ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting Q) :=
        (Nat.mem_primeFactors.mp hqF).2.1
      obtain ⟨P⟩ : Nonempty (Sylow q ↥(OddOrder.Isaacs.Ch01.fitting Q)) := inferInstance
      -- `Pbar` = the Sylow-`q` of `F(Q)` pushed into `Q`; it is a nontrivial normal `q`-subgroup.
      set Pbar : Subgroup Q :=
        (P : Subgroup ↥(OddOrder.Isaacs.Ch01.fitting Q)).map
          (OddOrder.Isaacs.Ch01.fitting Q).subtype with hPbar
      have hPbar_pg : IsPGroup q ↥Pbar := P.2.map _
      have hPnorm : (P : Subgroup ↥(OddOrder.Isaacs.Ch01.fitting Q)).Normal :=
        OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
      haveI : (P : Subgroup ↥(OddOrder.Isaacs.Ch01.fitting Q)).Characteristic :=
        Sylow.characteristic_of_normal P hPnorm
      haveI : Pbar.Normal := hPbar ▸ inferInstance
      have hPbar_le_op : Pbar ≤ OddOrder.Isaacs.Ch01.opCore q Q :=
        OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hPbar_pg
      have hPbar_ne : Pbar ≠ ⊥ := by
        have hcard_gt : 1 < Nat.card ↥Pbar := by
          rw [hPbar,
            Subgroup.card_map_of_injective (OddOrder.Isaacs.Ch01.fitting Q).subtype_injective,
            P.card_eq_multiplicity]
          exact Nat.one_lt_pow
            (hq_prime.factorization_pos_of_dvd Nat.card_pos.ne' hq_dvd).ne' hq_prime.one_lt
        intro hbot; rw [hbot, Subgroup.card_bot] at hcard_gt; exact lt_irrefl 1 hcard_gt
      -- `O_q(Q) ≤ O_{p}(Q)` only when `q = p`; but `O_p(Q) = O_p(H/O_p H) = ⊥`.
      have hop_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
          (OddOrder.Isaacs.Ch01.opCore q Q) := by
        intro r hr
        obtain ⟨n, hn⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup q Q).exists_card_eq
        rw [hn] at hr
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hrp hq_prime).mp
          (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
        -- `O_q(Q)` is a `q`-group and `q = p` (from `hqπ : q ∈ {p}`), so it is a `{p}`-group
        rw [Set.mem_singleton_iff, hrq]
        exact Set.mem_singleton_iff.mp hqπ
      have hoPi_bot : OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) Q = ⊥ :=
        OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot ({p} : Set ℕ)
      exact hPbar_ne (le_bot_iff.mp ((hPbar_le_op.trans
        (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore hop_pi)).trans_eq hoPi_bot))
    have hp_ndvd : ¬ p ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) := by
      intro hdvd
      have := hFQ_compl V hVoPi p
        (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
      simp at this
    -- `U := preimage of F(↥H/V)` in `↥H`: characteristic (hence `R`-invariant), and contains `V`.
    haveI hVchar : V.Characteristic := by rw [hVdef]; infer_instance
    set U : Subgroup ↥H :=
      (OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)).comap (QuotientGroup.mk' V) with hUdef
    haveI hUchar : U.Characteristic := Subgroup.Characteristic.comap_quotient_mk inferInstance
    have hVU : V ≤ U := by
      rw [hUdef]
      intro v hv
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff v).mpr hv]
      exact one_mem _
    -- `R`-action on `↥U` (restriction of the conjugation action; `U` characteristic ⟹
    -- `R`-invariant).
    set φ : ↥R →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R.subtype with hφ
    have hU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ U :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
    set φU : ↥R →* MulAut ↥U := hU_inv.restrict with hφU
    -- **`R`-invariant complement `K` to `V` in `U`** (Proposition 1.5(a)): an `R`-invariant Hall
    -- `p'`-subgroup of `U`.  Coprimality from `|U| ∣ |H|` and `hHall`; `U` solvable as a
    -- subgroup of `H`.
    have hCopU : Nat.Coprime (Nat.card ↥R) (Nat.card ↥U) :=
      hHall.symm.coprime_dvd_right (Subgroup.card_subgroup_dvd_card U)
    obtain ⟨K', hK'_hall, hK'_inv⟩ :=
      OddOrder.BG.Ch1.S01.exists_aInvariant_hall (G := ↥U) (φ := φU) hCopU ({p}ᶜ : Set ℕ)
    -- `K := K'` pushed into `↥H`: `R`-invariant, and a complement to `V` in `U` (card bookkeeping).
    set K : Subgroup ↥H := K'.map U.subtype with hKdef
    have hK_le_U : K ≤ U := Subgroup.map_subtype_le K'
    have hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K :=
      isAInvariant_map_subtype_of_restrict hU_inv hK'_inv
    have hKcard : Nat.card ↥K = Nat.card ↥K' :=
      Subgroup.card_map_of_injective U.subtype_injective
    have hK'p' : ¬ p ∣ Nat.card ↥K' := by
      intro hdvd
      have := hK'_hall.1 p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
      simp at this
    obtain ⟨a, hVa⟩ := hVp.exists_card_eq
    -- `|U| = |F(H/V)| · |V|` (the restriction of `mk' V` to `U` has kernel `V`, range `F(H/V)`).
    have hψker : ((QuotientGroup.mk' V).comp U.subtype).ker = V.subgroupOf U := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hψrange : ((QuotientGroup.mk' V).comp U.subtype).range
        = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
      rw [MonoidHom.range_comp, U.range_subtype, hUdef]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) _
    have hUcard : Nat.card ↥U
        = Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) * Nat.card ↥V := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (((QuotientGroup.mk' V).comp U.subtype).ker)]
      congr 1
      · exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange _).trans
          (MulEquiv.subgroupCongr hψrange)).toEquiv
      · rw [hψker]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv
    -- `|K'| = |F(H/V)|`: both are the `p'`-part of `|U| = |F(H/V)| · p^a`.
    have hCop_mFidx : Nat.Coprime (Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V))) K'.index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hq_dvd
      have hqp : q = p := by
        have := hK'_hall.2 q (Nat.mem_primeFactors.mpr
          ⟨hq_prime, hq_dvd.2, Subgroup.index_ne_zero_of_finite⟩)
        simpa using this
      exact hp_ndvd (hqp ▸ hq_dvd.1)
    have hK'm : Nat.card ↥K' = Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) := by
      have hKidx : Nat.card ↥K' * K'.index = Nat.card ↥U := Subgroup.card_mul_index K'
      refine Nat.dvd_antisymm ?_ ?_
      · have h1 : Nat.card ↥K' ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) * Nat.card ↥V :=
          hUcard ▸ Subgroup.card_subgroup_dvd_card K'
        refine Nat.Coprime.dvd_of_dvd_mul_right ?_ h1
        rw [hVa]
        exact Nat.Coprime.pow_right a (hp.coprime_iff_not_dvd.mpr hK'p').symm
      · have h2 : Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V))
            ∣ Nat.card ↥K' * K'.index := by
          rw [hKidx, hUcard]; exact dvd_mul_right _ _
        exact Nat.Coprime.dvd_of_dvd_mul_right hCop_mFidx h2
    -- `IsComplement' (V.subgroupOf U) K'`, hence `V ⊔ K = U` and `V ⊓ K = ⊥` in `↥H`.
    have hVU_card : Nat.card ↥(V.subgroupOf U) = Nat.card ↥V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv
    have hcomplVK : Subgroup.IsComplement' (V.subgroupOf U) K' := by
      refine Subgroup.isComplement'_of_coprime ?_ ?_
      · rw [hVU_card, hK'm, hUcard]; exact mul_comm _ _
      · rw [hVU_card, hVa]
        exact Nat.Coprime.pow_left a (hp.coprime_iff_not_dvd.mpr hK'p')
    have hVK_sup : V ⊔ K = U := by
      have h1 := congrArg (Subgroup.map U.subtype) hcomplVK.sup_eq_top
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVU, ← hKdef,
        ← MonoidHom.range_eq_map, U.range_subtype] at h1
    have hVK_inf : V ⊓ K = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime (by
        rw [hVa, hKcard]
        exact Nat.Coprime.pow_left a (hp.coprime_iff_not_dvd.mpr hK'p'))
    -- `N := N_{↥H}(K)` is `R`-invariant; pick an `R`-invariant Sylow `p`-subgroup `P` of `N`
    -- (Theorem 3.23(a) = `exists_aInvariant_sylow`).
    set N : Subgroup ↥H := Subgroup.normalizer (K : Set ↥H) with hNdef
    have hK_le_N : K ≤ N := Subgroup.le_normalizer
    have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := hK_inv.normalizer
    have hCopN : Nat.Coprime (Nat.card ↥R) (Nat.card ↥N) :=
      hHall.symm.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
    obtain ⟨P', hP'_inv⟩ := OddOrder.Isaacs.Ch04.exists_aInvariant_sylow
      (G := ↥N) (φ := hN_inv.restrict) hCopN (Or.inr inferInstance) p
    set P : Subgroup ↥H := (P' : Subgroup ↥N).map N.subtype with hPdef
    have hP_le_N : P ≤ N := Subgroup.map_subtype_le _
    have hP_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ P :=
      isAInvariant_map_subtype_of_restrict hN_inv hP'_inv
    have hPp : IsPGroup p ↥P := P'.2.map _
    -- **(3.12)** Frattini argument: `↥H = U·N = V·N`, i.e. `V ⊔ N = ⊤`.  Conjugates of `K'` are
    -- Hall `{p}ᶜ`-subgroups of `↥U`, hence `U`-conjugate to `K'` (`hall_C`).
    have h312 : V ⊔ N = ⊤ := by
      -- commuting squares: conjugation inside `↥U` vs conjugation in `↥H` after `U.subtype`.
      have hsq : ∀ (g : ↥H) (X : Subgroup ↥U),
          (X.map (MulAut.conjNormal (G := ↥H) (H := U) g).toMonoidHom).map U.subtype
            = (X.map U.subtype).map (MulAut.conj g).toMonoidHom := by
        intro g X
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      have hsq' : ∀ (u : ↥U) (X : Subgroup ↥U),
          (X.map (MulAut.conj u).toMonoidHom).map U.subtype
            = (X.map U.subtype).map (MulAut.conj (u : ↥H)).toMonoidHom := by
        intro u X
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      have hUN : ∀ hh : ↥H, hh ∈ U ⊔ N := by
        intro hh
        have hKh_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup ({p}ᶜ : Set ℕ)
            (K'.map (MulAut.conjNormal (G := ↥H) (H := U) hh).toMonoidHom) :=
          isHallSubgroup_map_of_mulEquiv _ hK'_hall
        obtain ⟨u, hu⟩ := OddOrder.Isaacs.Ch03.hall_C hKh_hall hK'_hall
        have h1 := congrArg (Subgroup.map U.subtype) hu
        rw [hsq', hsq, ← hKdef, Subgroup.map_map] at h1
        have hKK : K.map (MulAut.conj ((u : ↥H) * hh)).toMonoidHom = K := by
          have hcomp : (MulAut.conj ((u : ↥H) * hh)).toMonoidHom
              = (MulAut.conj (u : ↥H)).toMonoidHom.comp (MulAut.conj hh).toMonoidHom := by
            ext x
            simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply]
            group
          rw [hcomp]
          exact h1
        have huh_norm : (u : ↥H) * hh ∈ N := by
          rw [hNdef, Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            have hmem : ((u : ↥H) * hh) * x * ((u : ↥H) * hh)⁻¹
                ∈ K.map (MulAut.conj ((u : ↥H) * hh)).toMonoidHom :=
              ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
            rwa [hKK] at hmem
          · intro hx
            rw [← hKK] at hx
            obtain ⟨y, hy, hyeq⟩ := hx
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
            have hxy : y = x := by
              have := hyeq
              group at this
              exact mul_left_cancel (mul_right_cancel (mul_right_cancel this))
            exact hxy ▸ hy
        have hdec : hh = (u : ↥H)⁻¹ * ((u : ↥H) * hh) := by group
        rw [hdec]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (U.inv_mem u.2))
          (Subgroup.mem_sup_right huh_norm)
      have hUN_top : U ⊔ N = ⊤ := by
        rw [eq_top_iff]
        exact fun hh _ => hUN hh
      rw [eq_top_iff, ← hUN_top, ← hVK_sup]
      exact sup_le (sup_le le_sup_left (hK_le_N.trans le_sup_right)) le_sup_right
    -- The image of `N` covers the quotient `↥H ⧸ V` (used at (3.13) and (3.15)).
    have hVmap_bot : V.map (QuotientGroup.mk' V) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hv
    have hNmap_top : N.map (QuotientGroup.mk' V) = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' V)) h312
      rwa [Subgroup.map_sup, hVmap_bot, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective V)] at h1
    -- `U` covers `F(H/V)` and so does `K` (`U = V·K` and `V` dies in the quotient).
    have hUmap : U.map (QuotientGroup.mk' V) = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
      rw [hUdef]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) _
    have hKmap : K.map (QuotientGroup.mk' V) = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' V)) hVK_sup
      rwa [Subgroup.map_sup, hVmap_bot, bot_sup_eq, hUmap] at h1
    -- shared ending: `p ∤ |H/V|` makes `H` have `p`-length one ((3.8): `O_{p',p}(H) = O_p(H) = V`),
    -- contradicting `hcounter` via (3.6).  Used at (3.13) and (3.17).
    have hfalse_of_pndvd : ¬ p ∣ Nat.card (↥H ⧸ V) → False := by
      intro hnd
      apply hcounter
      have hcard_eq : Nat.card (↥H ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H)
          = Nat.card (↥H ⧸ V) :=
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hVoPi.symm).toEquiv
      rw [h36, hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot h38, hcard_eq]
      exact hnd
    -- **(3.13)** `⁅K, P⁆ ≠ ⊥`.  Otherwise the image of `P` in `H/V` centralizes
    -- `F(H/V) = KV/V`, hence lies in it (Prop 1.3); a `p`-group inside the `p'`-group `F(H/V)`
    -- is trivial, so `P ≤ V`.  Then the Sylow `p`-subgroup `P` of `N` dies in the image of `N`,
    -- which is all of `H/V` (3.12); so `p ∤ |H/V|` and `H` has `p`-length one — contradiction.
    have h313 : (⁅K, P⁆ : Subgroup ↥H) ≠ ⊥ := by
      intro hKP
      have hPV : P ≤ V := by
        have hPQ_le : P.map (QuotientGroup.mk' V) ≤ Subgroup.centralizer
            ((OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) : Subgroup (↥H ⧸ V)) : Set (↥H ⧸ V)) := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Subgroup.mem_centralizer_iff]
          rintro _ hfq
          rw [← hKmap] at hfq
          obtain ⟨k, hk, rfl⟩ := hfq
          have hcomm : (x : ↥H) * k = k * x :=
            (Subgroup.mem_centralizer_iff.mp
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKP hk)) x hx
          simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hcomm]
        have hPQ_le_F : P.map (QuotientGroup.mk' V)
            ≤ OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) :=
          hPQ_le.trans OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting
        have hPQ_p : IsPGroup p ↥(P.map (QuotientGroup.mk' V)) := hPp.map _
        obtain ⟨k, hk⟩ := hPQ_p.exists_card_eq
        have hk0 : k = 0 := by
          by_contra hk0
          exact hp_ndvd ((hk ▸ dvd_pow_self p hk0).trans (Subgroup.card_dvd_of_le hPQ_le_F))
        have hPQbot : P.map (QuotientGroup.mk' V) = ⊥ :=
          Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
        rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hPQbot
      -- `p ∤ |H/V|`: the image of the Sylow `P'` of `N` under `↥N ↠ H/V` is trivial.
      apply hfalse_of_pndvd
      intro hdvd
      set ψ : ↥N →* ↥H ⧸ V := (QuotientGroup.mk' V).comp N.subtype with hψ
      have hψsurj : Function.Surjective ψ := by
        rw [← MonoidHom.range_eq_top, hψ, MonoidHom.range_comp, N.range_subtype]
        exact hNmap_top
      have hkerP : (P' : Subgroup ↥N) ≤ ψ.ker := by
        intro x hx
        rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hPV (Subgroup.mem_map_of_mem N.subtype hx)
      have hNcard : Nat.card ↥N = Nat.card (↥H ⧸ V) * Nat.card ↥ψ.ker := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv]
        exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      have hdvd2 : p ^ (Nat.card ↥N).factorization p ∣ Nat.card ↥ψ.ker := by
        rw [← P'.card_eq_multiplicity]
        exact Subgroup.card_dvd_of_le hkerP
      have hcontra : p ^ ((Nat.card ↥N).factorization p + 1) ∣ Nat.card ↥N := by
        rw [pow_succ]
        calc p ^ (Nat.card ↥N).factorization p * p
            ∣ Nat.card ↥ψ.ker * Nat.card (↥H ⧸ V) := mul_dvd_mul hdvd2 hdvd
          _ = Nat.card ↥N := by rw [hNcard, mul_comm]
      exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp hcontra
    -- **(3.14)** `[V,K] = V` and `C_V(K) = ⊥` (hence `V ⊓ N = ⊥`).  Proposition 1.6(d) splits
    -- `V = C_V(K) × [V,K]`; both factors are normal in `↥H` (they are normalized by `V` — abelian
    -- — and by `N`, and `↥H = VN` by (3.12)) and `R`-invariant, so their `G`-lifts are normal in
    -- `G`, and (3.11) kills one of them.  `[V,K] = ⊥` would give `K ≤ C_H(V) = V` ((3.10)), so
    -- `K = ⊥` and `⁅K,P⁆ = ⊥`, contradicting (3.13).
    letI : CommGroup ↥V := { (inferInstance : Group ↥V) with mul_comm := fun a b => hVelem.1 a b }
    set φKV : ↥K →* MulAut ↥V := (MulAut.conjNormal (G := ↥H) (H := V)).comp K.subtype with hφKV
    have hφKV_val : ∀ (k : ↥K) (v : ↥V),
        ((φKV k v : ↥V) : ↥H) = (k : ↥H) * v * (k : ↥H)⁻¹ := by
      intro k v
      simp only [hφKV, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
    have hCopKV : Nat.Coprime (Nat.card ↥K) (Nat.card ↥V) := by
      rw [hVa, hKcard]
      exact (Nat.Coprime.pow_left a (hp.coprime_iff_not_dvd.mpr hK'p')).symm
    -- Proposition 1.6(d): `IsComplement' C_V(K) [V,K]` inside `↥V`.
    have hcompl14 : Subgroup.IsComplement' (Subgroup.fixedPointsOfMulAut φKV)
        (OddOrder.Isaacs.Ch04.actionCommutator φKV) :=
      OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian hCopKV
    -- bridges to `↥H`: the two factors are `V ⊓ C_{↥H}(K)` and `⁅V, K⁆`.
    have hAC : (OddOrder.Isaacs.Ch04.actionCommutator φKV).map V.subtype = ⁅V, K⁆ :=
      actionCommutator_conjNormal_map_subtype_eq V K
    have hFP : (Subgroup.fixedPointsOfMulAut φKV).map V.subtype
        = V ⊓ Subgroup.centralizer (K : Set ↥H) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have h1 := congrArg Subtype.val (Subgroup.mem_fixedPointsOfMulAut.mp hv ⟨k, hk⟩)
        rw [hφKV_val] at h1
        exact mul_inv_eq_iff_eq_mul.mp h1
      · rintro ⟨hxV, hxc⟩
        refine ⟨⟨x, hxV⟩, Subgroup.mem_fixedPointsOfMulAut.mpr fun k => ?_, rfl⟩
        apply Subtype.ext
        rw [hφKV_val]
        have h2 := Subgroup.mem_centralizer_iff.mp hxc (k : ↥H) k.2
        rw [h2]
        group
    have hker_subtype : (H.subtype).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
    -- conjugation by elements of `N` preserves `K` and `C_{↥H}(K)`.
    have hconjK : ∀ x : ↥H, x ∈ N → K.map (MulAut.conj x).toMonoidHom = K := by
      intro x hx
      have hx' := Subgroup.mem_normalizer_iff.mp hx
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hx' z).mp hz
      · intro hy
        have h1 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
        exact ⟨x⁻¹ * y * x, (hx' _).mpr (h1.symm ▸ hy), by group⟩
    have hconjC : ∀ x : ↥H, x ∈ N →
        (Subgroup.centralizer (K : Set ↥H)).map (MulAut.conj x).toMonoidHom
          = Subgroup.centralizer (K : Set ↥H) := by
      intro x hx
      have hx' := Subgroup.mem_normalizer_iff.mp hx
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Subgroup.mem_centralizer_iff] at hz ⊢
        intro k hk
        have hk' : x⁻¹ * k * x ∈ K := by
          refine (hx' (x⁻¹ * k * x)).mpr ?_
          have h1 : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
          rwa [h1]
        have hcz := hz _ hk'
        calc k * (x * z * x⁻¹) = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by group
          _ = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by rw [hcz]
          _ = (x * z * x⁻¹) * k := by group
      · intro hy
        refine ⟨x⁻¹ * y * x, ?_, by group⟩
        rw [Subgroup.mem_centralizer_iff] at hy ⊢
        intro k hk
        have hk' : x * k * x⁻¹ ∈ K := (hx' k).mp hk
        have hcy := hy _ hk'
        calc k * (x⁻¹ * y * x) = x⁻¹ * ((x * k * x⁻¹) * y) * x := by group
          _ = x⁻¹ * (y * (x * k * x⁻¹)) * x := by rw [hcy]
          _ = (x⁻¹ * y * x) * k := by group
    -- a subgroup of `V` normalized by all of `N` is normal in `↥H` (by (3.12), `↥H = VN`,
    -- and `V` centralizes subgroups of itself since `V` is abelian).
    have hnormal_of_VN : ∀ (X : Subgroup ↥H), X ≤ V →
        (∀ x : ↥H, x ∈ N → X.map (MulAut.conj x).toMonoidHom = X) → X.Normal := by
      intro X hXV hXN
      constructor
      intro nn hnn g
      have hg : g ∈ (V : Set ↥H) * (N : Set ↥H) := by
        rw [← Subgroup.normal_mul, h312, Subgroup.coe_top]
        trivial
      obtain ⟨v, hv, x, hx, rfl⟩ := hg
      have h1 : x * nn * x⁻¹ ∈ X := by
        rw [← hXN x hx]
        exact ⟨nn, hnn, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      have hcomm : v * (x * nn * x⁻¹) = (x * nn * x⁻¹) * v := by
        simpa using congrArg Subtype.val (hVelem.1 ⟨v, hv⟩ ⟨x * nn * x⁻¹, hXV h1⟩)
      have h2 : (v * x) * nn * (v * x)⁻¹ = v * (x * nn * x⁻¹) * v⁻¹ := by group
      rw [h2, hcomm]
      simpa using h1
    haveI hBnorm : (⁅V, K⁆ : Subgroup ↥H).Normal := by
      refine hnormal_of_VN _ (Subgroup.commutator_le_left V K) fun x hx => ?_
      rw [Subgroup.map_commutator, Subgroup.characteristic_iff_map_eq.mp hVchar (MulAut.conj x),
        hconjK x hx]
    haveI hCnorm : (V ⊓ Subgroup.centralizer (K : Set ↥H)).Normal := by
      refine hnormal_of_VN _ inf_le_left fun x hx => ?_
      rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
        Subgroup.characteristic_iff_map_eq.mp hVchar (MulAut.conj x), hconjC x hx]
    -- both factors are `R`-invariant (`V` characteristic, `K` `R`-invariant).
    have hV_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ V :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
    have hB_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (⁅V, K⁆ : Subgroup ↥H) := by
      intro r
      change (⁅V, K⁆ : Subgroup ↥H).map (φ r).toMonoidHom = ⁅V, K⁆
      have h1 : V.map (φ r).toMonoidHom = V := hV_inv r
      have h2 : K.map (φ r).toMonoidHom = K := hK_inv r
      rw [Subgroup.map_commutator, h1, h2]
    have hC_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ
        (V ⊓ Subgroup.centralizer (K : Set ↥H)) := by
      rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
      intro r y hy
      obtain ⟨hyV, hyc⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨hV_inv.smul_mem r hyV, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hyc ⊢
      intro k hk
      have hk' : (φ r)⁻¹ k ∈ K := hK_inv.inv_smul_mem r hk
      calc k * (φ r) y = (φ r) ((φ r)⁻¹ k * y) := by
            rw [map_mul, MulAut.apply_inv_self]
        _ = (φ r) (y * (φ r)⁻¹ k) := by rw [hyc _ hk']
        _ = (φ r) y * k := by rw [map_mul, MulAut.apply_inv_self]
    -- the `G`-lifts are normal in `G` (normal in `↥H` + `R`-invariant + `G = HR`).
    haveI hBnormG : ((⁅V, K⁆ : Subgroup ↥H).map H.subtype).Normal :=
      normal_map_subtype_of_isAInvariant_conjNormal hcompl.sup_eq_top hB_inv
    haveI hCnormG : ((V ⊓ Subgroup.centralizer (K : Set ↥H)).map H.subtype).Normal :=
      normal_map_subtype_of_isAInvariant_conjNormal hcompl.sup_eq_top hC_inv
    -- the two factors intersect trivially and generate `V` (image of `IsComplement'`).
    have hCB_inf : (V ⊓ Subgroup.centralizer (K : Set ↥H)) ⊓ (⁅V, K⁆ : Subgroup ↥H) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxC, hxB⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxV, hxc⟩ := Subgroup.mem_inf.mp hxC
      have hxFP : (⟨x, hxV⟩ : ↥V) ∈ Subgroup.fixedPointsOfMulAut φKV := by
        have h1 : x ∈ (Subgroup.fixedPointsOfMulAut φKV).map V.subtype := by
          rw [hFP]
          exact Subgroup.mem_inf.mpr ⟨hxV, hxc⟩
        obtain ⟨z, hz, hzx⟩ := h1
        rwa [show z = (⟨x, hxV⟩ : ↥V) from Subtype.ext hzx] at hz
      have hxAC : (⟨x, hxV⟩ : ↥V) ∈ OddOrder.Isaacs.Ch04.actionCommutator φKV := by
        have h1 : x ∈ (OddOrder.Isaacs.Ch04.actionCommutator φKV).map V.subtype := by
          rw [hAC]
          exact hxB
        obtain ⟨z, hz, hzx⟩ := h1
        rwa [show z = (⟨x, hxV⟩ : ↥V) from Subtype.ext hzx] at hz
      have hbot : (⟨x, hxV⟩ : ↥V) ∈ Subgroup.fixedPointsOfMulAut φKV
          ⊓ OddOrder.Isaacs.Ch04.actionCommutator φKV := ⟨hxFP, hxAC⟩
      rw [hcompl14.disjoint.eq_bot, Subgroup.mem_bot] at hbot
      rw [Subgroup.mem_bot]
      simpa using congrArg Subtype.val hbot
    have hCB_sup : (V ⊓ Subgroup.centralizer (K : Set ↥H)) ⊔ (⁅V, K⁆ : Subgroup ↥H) = V := by
      have h2 := congrArg (Subgroup.map V.subtype) hcompl14.sup_eq_top
      rwa [Subgroup.map_sup, hFP, hAC, ← MonoidHom.range_eq_map, V.range_subtype] at h2
    -- **(3.11) dichotomy**: the `C_V(K)` factor dies (else `K = ⊥`, contradicting (3.13)).
    have h314C : V ⊓ Subgroup.centralizer (K : Set ↥H) = ⊥ := by
      have hinfG : ((V ⊓ Subgroup.centralizer (K : Set ↥H)).map H.subtype)
          ⊓ ((⁅V, K⁆ : Subgroup ↥H).map H.subtype) = ⊥ := by
        rw [← Subgroup.map_inf _ _ H.subtype H.subtype_injective, hCB_inf, Subgroup.map_bot]
      rcases h311 _ _ (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hinfG with hc | hb
      · rwa [Subgroup.map_eq_bot_iff, hker_subtype, le_bot_iff] at hc
      · exfalso
        rw [Subgroup.map_eq_bot_iff, hker_subtype, le_bot_iff] at hb
        have hKle : K ≤ Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) :=
          Subgroup.le_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb)
        have hKbot : K = ⊥ := by
          rw [eq_bot_iff]
          intro k hk
          have hkV : k ∈ V ⊓ K := ⟨hCHV ▸ hKle hk, hk⟩
          rwa [hVK_inf] at hkV
        exact h313 (by rw [hKbot, Subgroup.commutator_bot_left])
    -- **(3.14)**: `[V,K] = V`, and `V ⊓ N = ⊥`.
    have h314B : (⁅V, K⁆ : Subgroup ↥H) = V := by
      have h1 := hCB_sup
      rwa [h314C, bot_sup_eq] at h1
    have hVN_inf : V ⊓ N = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hvV, hvN⟩ := Subgroup.mem_inf.mp hv
      have hvc : v ∈ Subgroup.centralizer (K : Set ↥H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have h1 : v * k * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hvN k).mp hk
        have h2 : v * k * v⁻¹ * k⁻¹ ∈ V := by
          have h3 : k * v⁻¹ * k⁻¹ ∈ V := hVnorm.conj_mem _ (V.inv_mem hvV) k
          have hcomb : v * k * v⁻¹ * k⁻¹ = v * (k * v⁻¹ * k⁻¹) := by group
          rw [hcomb]
          exact V.mul_mem hvV h3
        have h4 : v * k * v⁻¹ * k⁻¹ ∈ V ⊓ K := ⟨h2, K.mul_mem h1 (K.inv_mem hk)⟩
        rw [hVK_inf, Subgroup.mem_bot] at h4
        rw [mul_inv_eq_one] at h4
        exact (mul_inv_eq_iff_eq_mul.mp h4).symm
      have hvmem : v ∈ V ⊓ Subgroup.centralizer (K : Set ↥H) := ⟨hvV, hvc⟩
      rwa [h314C] at hvmem
    -- **(3.15)** `K = F(N)`: by (3.12) and `V ⊓ N = ⊥` the map `mk' V ∘ N.subtype` is an
    -- isomorphism `↥N ≃* ↥H ⧸ V` carrying `K.subgroupOf N` to `F(H/V)`; the Fitting subgroup
    -- transports along isomorphisms.
    set ψN : ↥N →* ↥H ⧸ V := (QuotientGroup.mk' V).comp N.subtype with hψN
    have hψNinj : Function.Injective ψN := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, hψN, MonoidHom.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      have hxVN : (x : ↥H) ∈ V ⊓ N := ⟨hx, x.2⟩
      rw [hVN_inf, Subgroup.mem_bot] at hxVN
      rw [Subgroup.mem_bot]
      exact Subtype.ext hxVN
    have hψNsurj : Function.Surjective ψN := by
      rw [← MonoidHom.range_eq_top, hψN, MonoidHom.range_comp, N.range_subtype]
      exact hNmap_top
    set eN : ↥N ≃* (↥H ⧸ V) := MulEquiv.ofBijective ψN ⟨hψNinj, hψNsurj⟩ with heN
    have heN_hom : eN.toMonoidHom = ψN := by
      ext x
      rfl
    have hKN_fit : K.subgroupOf N = OddOrder.Isaacs.Ch01.fitting ↥N := by
      have h1 : (K.subgroupOf N).map eN.toMonoidHom
          = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
        rw [heN_hom, hψN, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hK_le_N]
        exact hKmap
      have h2 : (OddOrder.Isaacs.Ch01.fitting ↥N).map eN.toMonoidHom
          = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := fitting_map_eq_of_mulEquiv eN
      exact Subgroup.map_injective eN.injective (h1.trans h2.symm)
    have h315 : (OddOrder.Isaacs.Ch01.fitting ↥N).map N.subtype = K := by
      rw [← hKN_fit, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hK_le_N
    -- **(3.16)** `C_{↥H}(K) ≤ K`: a centralizing element lies in `N`, and inside `↥N`
    -- Proposition 1.3 gives `C_N(K) ≤ C_N(F(N)) ≤ F(N) = K`.
    have h316 : Subgroup.centralizer (K : Set ↥H) ≤ K := by
      intro c hc
      have hcN : c ∈ N := Subgroup.centralizer_le_normalizer (K : Set ↥H) hc
      have hcC : (⟨c, hcN⟩ : ↥N) ∈ Subgroup.centralizer
          ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact Subgroup.mem_centralizer_iff.mp hc (k : ↥H) (Subgroup.mem_subgroupOf.mp hk)
      have hcF : (⟨c, hcN⟩ : ↥N) ∈ OddOrder.Isaacs.Ch01.fitting ↥N :=
        OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting (hKN_fit ▸ hcC)
      rw [← hKN_fit] at hcF
      exact Subgroup.mem_subgroupOf.mp hcF
    -- ===== Phase C (3.17)–(3.21): the action of `R₀` =====
    -- **(3.17)** `K` does not centralize `R₀`.  Otherwise `K` (lifted to `G`) lies in the
    -- `Z`-group `H ⊓ C_G(R₀)`; being nilpotent (`K ≅ F(N)`, (3.15)), `K` is cyclic, hence so is
    -- `F(H/V) = KV/V`.  The `R`-action on `H/V` then has its action commutator inside
    -- `C_{H/V}(F(H/V)) ≤ F(H/V)` (cyclic normal invariant + Prop 1.3); but by (3.6) the action
    -- commutator is everything, so `H/V = F(H/V)` is a `p'`-group — contradiction (as in (3.13)).
    have h317 : ¬ ((K.map H.subtype : Subgroup G) ≤ Subgroup.centralizer (R₀ : Set G)) := by
      intro hKcent
      -- `K` is a nilpotent `Z`-group, hence cyclic.
      haveI hKG_Z : _root_.IsZGroup ↥(K.map H.subtype) := by
        have hle : K.map H.subtype ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) :=
          le_inf (Subgroup.map_subtype_le K) hKcent
        haveI := isZGroup_iff_mathlib.mp hZ
        exact IsZGroup.of_injective (Subgroup.inclusion_injective hle)
      haveI hK_nilp : Group.IsNilpotent ↥(K.map H.subtype) := by
        have e1 := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
        have e2 := Subgroup.subgroupOfEquivOfLe hK_le_N
        haveI : Group.IsNilpotent ↥(K.subgroupOf N) := by
          rw [hKN_fit]
          infer_instance
        refine Group.nilpotent_of_surjective (e1.toMonoidHom.comp e2.toMonoidHom) ?_
        rw [MonoidHom.coe_comp]
        exact e1.surjective.comp e2.surjective
      haveI hKG_cyc : IsCyclic ↥(K.map H.subtype) := inferInstance
      haveI hK_cyc : IsCyclic ↥K := by
        have e1 := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
        exact isCyclic_of_surjective e1.symm e1.symm.surjective
      -- hence `F(H/V) ≅ K` is cyclic (`mk' V` is injective on `K` since `V ⊓ K = ⊥`).
      haveI hFQ_cyc : IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) := by
        have hinj : Function.Injective ((QuotientGroup.mk' V).comp K.subtype) := by
          rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
          intro x hx
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
            QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
          have hxm : (x : ↥H) ∈ V ⊓ K := ⟨hx, x.2⟩
          rw [hVK_inf, Subgroup.mem_bot] at hxm
          rw [Subgroup.mem_bot]
          exact Subtype.ext hxm
        have hrange : ((QuotientGroup.mk' V).comp K.subtype).range
            = K.map (QuotientGroup.mk' V) := by
          rw [MonoidHom.range_comp, K.range_subtype]
        have e3 : ↥K ≃* ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) :=
          (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hrange.trans hKmap))
        exact isCyclic_of_surjective e3 e3.surjective
      -- the induced `R`-action on `Q = ↥H ⧸ V` has full action commutator ((3.6)).
      set φQ : ↥R →* MulAut (↥H ⧸ V) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hV_inv with hφQ
      have hACH : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ := by
        have hb := actionCommutator_conjNormal_map_subtype_eq H R
        rw [h36] at hb
        rw [eq_top_iff]
        intro x _
        have hx : (x : G) ∈ (OddOrder.Isaacs.Ch04.actionCommutator φ).map H.subtype := by
          rw [hb]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        rwa [show y = x from Subtype.ext hyx] at hy
      have hACQ : OddOrder.Isaacs.Ch04.actionCommutator φQ = ⊤ := by
        have hmap_le : (OddOrder.Isaacs.Ch04.actionCommutator φ).map (QuotientGroup.mk' V)
            ≤ OddOrder.Isaacs.Ch04.actionCommutator φQ := by
          rw [Subgroup.map_le_iff_le_comap, OddOrder.Isaacs.Ch04.actionCommutator,
            Subgroup.closure_le]
          rintro _ ⟨g, r, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap]
          have hgen : (QuotientGroup.mk' V) (g * (φ r) g⁻¹)
              = (QuotientGroup.mk' V g) * (φQ r) ((QuotientGroup.mk' V g)⁻¹) := by
            rw [map_mul, hφQ, ← map_inv,
              OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
          rw [hgen]
          exact Subgroup.subset_closure ⟨_, _, rfl⟩
        rw [eq_top_iff]
        calc (⊤ : Subgroup (↥H ⧸ V))
            = (⊤ : Subgroup ↥H).map (QuotientGroup.mk' V) :=
              (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective V)).symm
          _ = (OddOrder.Isaacs.Ch04.actionCommutator φ).map (QuotientGroup.mk' V) := by
              rw [hACH]
          _ ≤ OddOrder.Isaacs.Ch04.actionCommutator φQ := hmap_le
      -- cyclic + normal + invariant: the action commutator centralizes `F(Q)`; with (3.6) and
      -- Prop 1.3, `F(Q) = ⊤`, so `p ∤ |Q|` (`F(Q)` is a `p'`-group) — contradiction.
      have hFQ_inv : OddOrder.Isaacs.Ch03.IsAInvariant φQ
          (OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φQ
      have hAC_le := actionCommutator_le_centralizer_of_isCyclic_isAInvariant
        (OddOrder.Isaacs.Ch01.fitting.normal (↥H ⧸ V)) hFQ_inv
      rw [hACQ, top_le_iff] at hAC_le
      have hFQ_top : OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) = ⊤ := by
        rw [eq_top_iff, ← hAC_le]
        exact OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting
      apply hfalse_of_pndvd
      intro hdvd
      apply hp_ndvd
      have hcardtop : Nat.card ↥(⊤ : Subgroup (↥H ⧸ V)) = Nat.card (↥H ⧸ V) :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      rw [hFQ_top, hcardtop]
      exact hdvd
    -- **(3.18)** `C_{KR₀}(V) = ⊥` (at the `G` level).  The `K`-part dies by (3.10)+(3.14)
    -- (`C_K(V) ≤ K ⊓ C_H(V) = K ⊓ V = ⊥`); so `C := C_{KR₀}(V)` is a normal subgroup of `KR₀`
    -- meeting `K` trivially, hence of order dividing `r = |R₀|`.  If `C ≠ ⊥` then `|C| = r`;
    -- a second order-`r` subgroup (`R₀` itself) distinct from the normal `C` would force
    -- `r² ∣ |KR₀| = |K|·r`, impossible; so `C = R₀ ⊴ KR₀`, making `⁅K,R₀⁆ ≤ K ⊓ R₀ = ⊥`,
    -- contradicting (3.17).
    obtain ⟨r, hr_prime, hr_card⟩ := hR₀p
    -- ===== Phase C ambient: `S₁ := K_G·R₀ ≤ G`, complement structure, `V_G ⊴ G` =====
    set KG : Subgroup G := K.map H.subtype with hKG
    set VG : Subgroup G := V.map H.subtype with hVG
    set KG : Subgroup G := K.map H.subtype with hKG
    set S₁ : Subgroup G := KG ⊔ R₀ with hS₁
    have hKG_le_S₁ : KG ≤ S₁ := le_sup_left
    have hR₀_le_S₁ : R₀ ≤ S₁ := le_sup_right
    have hKG_le_H : KG ≤ H := Subgroup.map_subtype_le K
    -- `S₁ ≤ N_G(KG)` (`K` is `R`-invariant), so `KG.subgroupOf S₁` is normal.
    have hS₁norm : S₁ ≤ Subgroup.normalizer (KG : Set G) := by
      refine sup_le Subgroup.le_normalizer ?_
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨φ ⟨g, hR₀R hg⟩ k, hK_inv.smul_mem _ hk, ?_⟩
        simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
      · rintro hgx
        obtain ⟨k, hk, hkeq⟩ := hgx
        refine ⟨(φ ⟨g, hR₀R hg⟩)⁻¹ k, hK_inv.inv_smul_mem _ hk, ?_⟩
        have hv2 : ((φ ⟨g, hR₀R hg⟩ ((φ ⟨g, hR₀R hg⟩)⁻¹ k) : ↥H) : G)
            = g * (((φ ⟨g, hR₀R hg⟩)⁻¹ k : ↥H) : G) * g⁻¹ := by
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
        rw [MulAut.apply_inv_self] at hv2
        have h3 := hv2.symm.trans hkeq
        exact mul_left_cancel (mul_right_cancel h3)
    haveI hKG'norm : ((KG.subgroupOf S₁) : Subgroup ↥S₁).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hS₁norm
    -- complement `KG' ⋊ R₀'` inside `S₁`, and the resulting cardinalities.
    have hdisjKR : Disjoint KG R₀ :=
      (hcompl.disjoint.mono hKG_le_H hR₀R)
    have hcompl₁ : Subgroup.IsComplement' (KG.subgroupOf S₁) (R₀.subgroupOf S₁) := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
        rw [Subgroup.mem_inf] at hx
        simp only [Subgroup.mem_subgroupOf] at hx
        have hmem : (x : G) ∈ KG ⊓ R₀ := ⟨hx.1, hx.2⟩
        rw [hdisjKR.eq_bot, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]
        exact Subtype.ext (by simpa using hmem)
      · have hsup : ((KG.subgroupOf S₁) : Subgroup ↥S₁) ⊔ (R₀.subgroupOf S₁) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hKG_le_S₁ hR₀_le_S₁, Subgroup.subgroupOf_self]
        have hmul := Subgroup.normal_mul ((KG.subgroupOf S₁) : Subgroup ↥S₁) (R₀.subgroupOf S₁)
        rw [hsup, Subgroup.coe_top] at hmul
        exact hmul.symm
    have hR₀'card : Nat.card ↥(R₀.subgroupOf S₁) = r :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_S₁).toEquiv).trans hr_card
    have hKG'card : Nat.card ↥(KG.subgroupOf S₁) = Nat.card ↥K :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG_le_S₁).toEquiv).trans
        (Subgroup.card_map_of_injective H.subtype_injective)
    have hr_ndvd_K : ¬ r ∣ Nat.card ↥K := by
      intro hdvd
      have h1 : r ∣ Nat.card ↥H :=
        hdvd.trans (Subgroup.card_subgroup_dvd_card K)
      have h2 : r ∣ Nat.card ↥R := hr_card ▸ Subgroup.card_dvd_of_le hR₀R
      have := Nat.Coprime.eq_one_of_dvd (hHall.coprime_dvd_left h1) h2
      exact hr_prime.one_lt.ne' this
    haveI hVGnorm : VG.Normal := by
      constructor
      intro n hn gg
      obtain ⟨v, hv, rfl⟩ := hn
      have hvH : gg * (v : G) * gg⁻¹ ∈ H := (inferInstance : H.Normal).conj_mem _ v.2 gg
      have hfix : V.map (MulAut.conjNormal gg).toMonoidHom = V :=
        Subgroup.characteristic_iff_map_eq.mp hVchar (MulAut.conjNormal gg)
      have hmem : MulAut.conjNormal gg v ∈ V := by
        rw [← hfix]
        exact Subgroup.mem_map_of_mem _ hv
      exact ⟨MulAut.conjNormal gg v, hmem, by
        rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]⟩
    have h318 : S₁ ⊓ Subgroup.centralizer (VG : Set G) = ⊥ := by
      -- main step: the centralizer part `C` is `⊥`.
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨hgS₁, hgc⟩ := Subgroup.mem_inf.mp hg
      set C : Subgroup G := S₁ ⊓ Subgroup.centralizer (VG : Set G) with hC
      by_contra hgne
      rw [Subgroup.mem_bot] at hgne
      -- `C ⊓ KG = ⊥` ((3.10) + (3.14): a `K`-element centralizing `V` lies in `V ⊓ K = ⊥`).
      have hCK : C ⊓ KG = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨_, hxc⟩, hxK⟩
        obtain ⟨k, hk, rfl⟩ := hxK
        have hkcent : k ∈ Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) := by
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact Subgroup.mem_centralizer_iff.mp hxc (w : G) ⟨w, hw, rfl⟩
        rw [hCHV] at hkcent
        have hkb : k ∈ V ⊓ K := ⟨hkcent, hk⟩
        rw [hVK_inf, Subgroup.mem_bot] at hkb
        rw [Subgroup.mem_bot, hkb]
        simp
      -- `C.subgroupOf S₁` is normal (`C_G(V_G) ⊴ G` since `V_G ⊴ G`).
      haveI hC'norm : ((C.subgroupOf S₁) : Subgroup ↥S₁).Normal := by
        constructor
        intro c hc s
        rw [Subgroup.mem_subgroupOf] at hc ⊢
        obtain ⟨hcS₁, hcc⟩ := Subgroup.mem_inf.mp hc
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ s.2 hcS₁)
          (Subgroup.inv_mem _ s.2), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : (s : G)⁻¹ * y * (s : G) ∈ VG := by
          have := hVGnorm.conj_mem y hy (s : G)⁻¹
          simpa using this
        have hcy := Subgroup.mem_centralizer_iff.mp hcc _ hy'
        calc y * ((s : G) * (c : G) * (s : G)⁻¹)
            = (s : G) * (((s : G)⁻¹ * y * (s : G)) * (c : G)) * (s : G)⁻¹ := by group
          _ = (s : G) * ((c : G) * ((s : G)⁻¹ * y * (s : G))) * (s : G)⁻¹ := by rw [hcy]
          _ = ((s : G) * (c : G) * (s : G)⁻¹) * y := by group
      -- `|C'| ∣ r`: `C'` embeds into `S₁/KG'`, which has order `r`.
      have hquot_card : Nat.card (↥S₁ ⧸ ((KG.subgroupOf S₁) : Subgroup ↥S₁)) = r := by
        have h1 : Nat.card ↥S₁ = Nat.card (↥S₁ ⧸ ((KG.subgroupOf S₁) : Subgroup ↥S₁))
            * Nat.card ↥(KG.subgroupOf S₁) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup _
        have h2 : Nat.card ↥(KG.subgroupOf S₁) * Nat.card ↥(R₀.subgroupOf S₁)
            = Nat.card ↥S₁ := hcompl₁.card_mul
        rw [← h2, mul_comm (Nat.card ↥(KG.subgroupOf S₁))] at h1
        have h3 := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(KG.subgroupOf S₁))) h1
        rw [← h3]
        exact hR₀'card
      have hCcard_dvd : Nat.card ↥(C.subgroupOf S₁) ∣ r := by
        rw [← hquot_card]
        refine Subgroup.card_dvd_of_injective
          ((QuotientGroup.mk' ((KG.subgroupOf S₁) : Subgroup ↥S₁)).comp
            (C.subgroupOf S₁).subtype) ?_
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
        have hxC : ((x : ↥S₁) : G) ∈ C := Subgroup.mem_subgroupOf.mp x.2
        have hxb : ((x : ↥S₁) : G) ∈ C ⊓ KG := ⟨hxC, hx⟩
        rw [hCK, Subgroup.mem_bot] at hxb
        rw [Subgroup.mem_bot]
        exact Subtype.ext (Subtype.ext hxb)
      rcases (Nat.dvd_prime hr_prime).mp hCcard_dvd with h1card | hCr
      · -- `|C'| = 1` ⟹ `C = ⊥` ⟹ `g = 1`, contradiction with `hgne`.
        have hC'bot : (C.subgroupOf S₁ : Subgroup ↥S₁) = ⊥ :=
          Subgroup.eq_bot_of_card_eq _ h1card
        have hgC' : (⟨g, hgS₁⟩ : ↥S₁) ∈ C.subgroupOf S₁ :=
          Subgroup.mem_subgroupOf.mpr ⟨hgS₁, hgc⟩
        rw [hC'bot, Subgroup.mem_bot] at hgC'
        exact hgne (by simpa using congrArg Subtype.val hgC')
      · -- `|C'| = r`: then `C' = R₀'` (else `r² ∣ |S₁| = |K|·r`), so `R₀'` is normal in `S₁`,
        -- `⁅KG',R₀'⁆ ≤ KG' ⊓ R₀' = ⊥`, and `K` centralizes `R₀` — contradicting (3.17).
        exfalso
        have hCR₀ : (C.subgroupOf S₁ : Subgroup ↥S₁) = R₀.subgroupOf S₁ := by
          by_contra hne
          have hinf_bot : (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁) = ⊥ := by
            by_contra hinfne
            have hle1 : Nat.card ↥((C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁)) ∣ r := by
              rw [← hCr]
              exact Subgroup.card_dvd_of_le inf_le_left
            rcases (Nat.dvd_prime hr_prime).mp hle1 with hi1 | hir
            · exact hinfne (Subgroup.eq_bot_of_card_eq _ hi1)
            · have he1 : (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁)
                  = C.subgroupOf S₁ :=
                Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (hCr.trans hir.symm))
              have he2 : (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁)
                  = R₀.subgroupOf S₁ :=
                Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (hR₀'card.trans hir.symm))
              exact hne (he1.symm.trans he2)
          -- the image of `R₀'` in `S₁/C'` is injective, so `r ∣ |S₁/C'|` and `r² ∣ |S₁|`.
          have hrdvd_quot : r ∣ Nat.card (↥S₁ ⧸ (C.subgroupOf S₁ : Subgroup ↥S₁)) := by
            have hinj : Function.Injective
                ((QuotientGroup.mk' (C.subgroupOf S₁ : Subgroup ↥S₁)).comp
                  (R₀.subgroupOf S₁).subtype) := by
              rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
              intro x hx
              rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
                QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
              have hxm : (x : ↥S₁) ∈ (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁) :=
                ⟨hx, x.2⟩
              rw [hinf_bot, Subgroup.mem_bot] at hxm
              rw [Subgroup.mem_bot]
              exact Subtype.ext hxm
            rw [← hR₀'card]
            exact Subgroup.card_dvd_of_injective _ hinj
          have hr2 : r * r ∣ Nat.card ↥S₁ := by
            rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
              (C.subgroupOf S₁ : Subgroup ↥S₁)]
            exact mul_dvd_mul hrdvd_quot (dvd_of_eq hCr.symm)
          have hS₁card : Nat.card ↥S₁ = Nat.card ↥K * r := by
            rw [← hcompl₁.card_mul, hKG'card, hR₀'card]
          rw [hS₁card] at hr2
          exact hr_ndvd_K ((Nat.mul_dvd_mul_iff_right hr_prime.pos).mp hr2)
        haveI hR₀'norm : ((R₀.subgroupOf S₁) : Subgroup ↥S₁).Normal := hCR₀ ▸ hC'norm
        have hcomm_bot :
            (⁅(KG.subgroupOf S₁ : Subgroup ↥S₁), R₀.subgroupOf S₁⁆ : Subgroup ↥S₁) = ⊥ := by
          rw [eq_bot_iff, ← hcompl₁.disjoint.eq_bot]
          exact le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
        apply h317
        intro x hxK
        rw [Subgroup.mem_centralizer_iff]
        intro y hyR₀
        have hx' : (⟨x, hKG_le_S₁ hxK⟩ : ↥S₁) ∈ KG.subgroupOf S₁ :=
          Subgroup.mem_subgroupOf.mpr hxK
        have hy' : (⟨y, hR₀_le_S₁ hyR₀⟩ : ↥S₁) ∈ R₀.subgroupOf S₁ :=
          Subgroup.mem_subgroupOf.mpr hyR₀
        have hcomm1 : ⁅(⟨x, hKG_le_S₁ hxK⟩ : ↥S₁), (⟨y, hR₀_le_S₁ hyR₀⟩ : ↥S₁)⁆ = 1 := by
          have hm := Subgroup.commutator_mem_commutator hx' hy'
          rwa [hcomm_bot, Subgroup.mem_bot] at hm
        have hc2 := commutatorElement_eq_one_iff_commute.mp hcomm1
        have hval := congrArg Subtype.val hc2.eq
        simp only [Subgroup.coe_mul] at hval
        exact hval.symm
    -- **(3.19)** `|C_{V_G}(R₀)| = p`.  First `H ≠ ⊥` (else `⁅H,R⁆ = ⊥` has `p`-length one), so
    -- `V = F(H) ≠ ⊥`, `p ∣ |V|`, `p ≠ r`, and `p ∤ |S₁|`.
    have hH_ne_bot : H ≠ ⊥ := by
      intro hHbot
      apply hcounter
      rw [hasPLengthOne]
      intro hdvd
      have h1 : Nat.card (↥(⁅H, R⁆ : Subgroup G) ⧸
          OddOrder.Isaacs.Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥(⁅H, R⁆ : Subgroup G)) ∣
          Nat.card ↥(⁅H, R⁆ : Subgroup G) :=
        ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
      have h2 : Nat.card ↥(⁅H, R⁆ : Subgroup G) = 1 := by
        rw [h36, hHbot, Subgroup.card_bot]
      rw [h2, Nat.dvd_one] at h1
      rw [h1, Nat.dvd_one] at hdvd
      exact hp.ne_one hdvd
    have hV_ne_bot : V ≠ ⊥ := by
      haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH_ne_bot
      exact OddOrder.Isaacs.Ch01.fitting_ne_bot_of_solvable_nontrivial ↥H
    have ha0 : a ≠ 0 := by
      intro h0
      exact hV_ne_bot (Subgroup.eq_bot_of_card_eq _ (by rw [hVa, h0, pow_zero]))
    have hpr : p ≠ r := by
      intro hpr_eq
      have h1 : p ∣ Nat.card ↥H :=
        (show p ∣ Nat.card ↥V by rw [hVa]; exact dvd_pow_self p ha0).trans
          (Subgroup.card_subgroup_dvd_card V)
      have h2 : p ∣ Nat.card ↥R := by
        rw [hpr_eq, ← hr_card]
        exact Subgroup.card_dvd_of_le hR₀R
      exact hp.ne_one (Nat.Coprime.eq_one_of_dvd (hHall.coprime_dvd_left h1) h2)
    have hS₁card : Nat.card ↥S₁ = Nat.card ↥K * r := by
      rw [← hcompl₁.card_mul, hKG'card, hR₀'card]
    have hp_ndvd_S₁ : ¬ p ∣ Nat.card ↥S₁ := by
      rw [hS₁card]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · rw [hKcard] at h
        exact hK'p' h
      · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp h)
    -- `V_G` is elementary abelian (transport along `↥V ≃* ↥V_G`).
    have hVGelem : OddOrder.GroupTheory.IsElementaryAbelian p ↥VG := by
      have e := Subgroup.equivMapOfInjective V H.subtype H.subtype_injective
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · have h1 := congrArg e (hVelem.1 (e.symm x) (e.symm y))
        rwa [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h1
      · have h1 := congrArg e (hVelem.2 (e.symm x))
        rwa [map_pow, map_one, e.apply_symm_apply] at h1
    -- Part 1: `C_{V_G}(R₀) ≠ ⊥`.  Otherwise Theorem 3.4, applied to the conjugation
    -- representation of `S₁ = K_G·R₀` on the `𝔽_p`-vector space `V_G`, makes `⁅R₀,K_G⁆` act
    -- trivially on `V_G`; by (3.18) it is then trivial, contradicting (3.17).
    have h319a : VG ⊓ Subgroup.centralizer (R₀ : Set G) ≠ ⊥ := by
      intro hCVbot
      haveI hVGcomm : IsMulCommutative ↥VG := ⟨⟨fun a b => hVGelem.1 a b⟩⟩
      have hpsmul : ∀ x : Additive ↥VG, (p : ℕ) • x = 0 := by
        intro x
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact hVGelem.2 x.toMul
      haveI hVGmod : Module (ZMod p) (Additive ↥VG) := AddCommGroup.zmodModule hpsmul
      haveI : Module.Finite (ZMod p) (Additive ↥VG) := Module.Finite.of_finite
      set ρ : Representation (ZMod p) ↥S₁ (Additive ↥VG) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥VG p).comp
          ((MulAut.conjNormal (G := G) (H := VG)).comp S₁.subtype) with hρdef
      have hρ_apply : ∀ (g : ↥S₁) (x : Additive ↥VG),
          ρ g x = Additive.ofMul (MulAut.conjNormal (H := VG) (g : G) (Additive.toMul x)) := by
        intro g x
        rfl
      have hodd_S₁ : Odd (Nat.card ↥S₁) := by
        obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card S₁
        rw [hm, Nat.odd_mul] at hodd
        exact hodd.1
      have hchar : (Nat.card ↥S₁ : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact hp_ndvd_S₁
      have hHall34 : Nat.Coprime (Nat.card ↥(KG.subgroupOf S₁))
          (Nat.card ↥(R₀.subgroupOf S₁)) := by
        rw [hKG'card, hR₀'card]
        exact (hr_prime.coprime_iff_not_dvd.mpr hr_ndvd_K).symm
      have hCV : ∀ v : Additive ↥VG,
          (∀ rr : ↥(R₀.subgroupOf S₁), ρ ((rr : ↥S₁)) v = v) → v = 0 := by
        intro v hv
        have hmem : ((Additive.toMul v : ↥VG) : G)
            ∈ VG ⊓ Subgroup.centralizer (R₀ : Set G) := by
          refine Subgroup.mem_inf.mpr
            ⟨(Additive.toMul v).2, Subgroup.mem_centralizer_iff.mpr fun gr hgr => ?_⟩
          have h1 := hv ⟨⟨gr, hR₀_le_S₁ hgr⟩, Subgroup.mem_subgroupOf.mpr hgr⟩
          rw [hρ_apply] at h1
          have h2 := congrArg Additive.toMul h1
          rw [toMul_ofMul] at h2
          have h3 := congrArg Subtype.val h2
          rw [MulAut.conjNormal_apply] at h3
          exact mul_inv_eq_iff_eq_mul.mp h3
        rw [hCVbot, Subgroup.mem_bot] at hmem
        have hw : (Additive.toMul v : ↥VG) = 1 := Subtype.ext hmem
        rw [← ofMul_toMul v, hw, ofMul_one]
      have hthm34 := S03d.thm34 ρ (KG.subgroupOf S₁) (R₀.subgroupOf S₁)
        hcompl₁ hHall34 ⟨r, hr_prime, hR₀'card⟩ hodd_S₁ hchar hCV
      -- every element of `⁅R₀, K_G⁆` therefore centralizes `V_G`, hence dies by (3.18).
      have hcomm_bot : (⁅R₀, KG⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hsub : (⁅R₀, KG⁆ : Subgroup G) ≤ S₁ := by
          rw [Subgroup.commutator_le]
          intro g₁ hg₁ g₂ hg₂
          have h1 : g₁ ∈ S₁ := hR₀_le_S₁ hg₁
          have h2 : g₂ ∈ S₁ := hKG_le_S₁ hg₂
          rw [commutatorElement_def]
          exact S₁.mul_mem (S₁.mul_mem (S₁.mul_mem h1 h2) (S₁.inv_mem h1)) (S₁.inv_mem h2)
        have hxS₁ : x ∈ S₁ := hsub hx
        have hmapeq : (⁅(R₀.subgroupOf S₁ : Subgroup ↥S₁), KG.subgroupOf S₁⁆
            : Subgroup ↥S₁).map S₁.subtype = ⁅R₀, KG⁆ := by
          rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR₀_le_S₁,
            inf_eq_left.mpr hKG_le_S₁]
        have hx' : (⟨x, hxS₁⟩ : ↥S₁)
            ∈ (⁅(R₀.subgroupOf S₁ : Subgroup ↥S₁), KG.subgroupOf S₁⁆ : Subgroup ↥S₁) := by
          have hmem : x ∈ (⁅(R₀.subgroupOf S₁ : Subgroup ↥S₁), KG.subgroupOf S₁⁆
              : Subgroup ↥S₁).map S₁.subtype := hmapeq.symm ▸ hx
          obtain ⟨z, hz, hzx⟩ := hmem
          rwa [show z = ⟨x, hxS₁⟩ from Subtype.ext hzx] at hz
        have hρ1 : ρ ⟨x, hxS₁⟩ = 1 := hthm34 _ hx'
        have hxc : x ∈ Subgroup.centralizer (VG : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hx1 := DFunLike.congr_fun hρ1 (Additive.ofMul (⟨y, hy⟩ : ↥VG))
          rw [hρ_apply, Module.End.one_apply] at hx1
          have hcoe := congrArg Subtype.val (Additive.ofMul.injective hx1)
          rw [MulAut.conjNormal_apply] at hcoe
          exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
        have hfin : x ∈ S₁ ⊓ Subgroup.centralizer (VG : Set G) := ⟨hxS₁, hxc⟩
        rwa [h318] at hfin
      apply h317
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm_bot
    -- Part 2: `C_{V_G}(R₀)` is a nontrivial subgroup of exponent `p` inside the `Z`-group
    -- `H ⊓ C_G(R₀)`, hence has order exactly `p`.
    have hA_exp : ∀ x ∈ VG ⊓ Subgroup.centralizer (R₀ : Set G), x ^ p = (1 : G) := by
      intro x hx
      obtain ⟨hxV, _⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨w, hw, rfl⟩ := hxV
      have h1 : w ^ p = (1 : ↥H) := by
        have h2 := congrArg Subtype.val (hVelem.2 ⟨w, hw⟩)
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
      have h4 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h4
    have h319 : Nat.card ↥(VG ⊓ Subgroup.centralizer (R₀ : Set G)) = p :=
      card_eq_prime_of_le_isZGroup hZ
        (inf_le_inf_right _ (Subgroup.map_subtype_le V)) hp hA_exp h319a
    -- **(3.20)** `C_{P_G}(R₀) = ⊥`.  Otherwise pick `y` of order `p` in `P_G ⊓ C_G(R₀)`
    -- (Cauchy); `y` normalizes `A := C_{V_G}(R₀)` (it centralizes `R₀` and `V_G ⊴ G`), so
    -- `T := A·⟨y⟩` is a `p`-subgroup of the `Z`-group `H ⊓ C_G(R₀)`, hence cyclic; a cyclic
    -- group has at most `p` solutions of `t^p = 1`, so `y ∈ A ≤ V_G`; but `P_G ⊓ V_G = ⊥`.
    have hPV_inf : (P.map H.subtype : Subgroup G) ⊓ VG = ⊥ := by
      have h1 : P ⊓ V = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h2 : x ∈ V ⊓ N := ⟨hx.2, hP_le_N hx.1⟩
        rwa [hVN_inf] at h2
      rw [← Subgroup.map_inf _ _ H.subtype H.subtype_injective, h1, Subgroup.map_bot]
    have h320 : (P.map H.subtype : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) = ⊥ := by
      by_contra hne
      -- a `p`-element `y` of order `p` in `W := P_G ⊓ C_G(R₀)` (Cauchy).
      set W : Subgroup G := (P.map H.subtype) ⊓ Subgroup.centralizer (R₀ : Set G) with hW
      have hWp : IsPGroup p ↥W :=
        (hPp.map H.subtype).to_le inf_le_left
      have hpdvdW : p ∣ Nat.card ↥W := by
        obtain ⟨m, hm⟩ := hWp.exists_card_eq
        rw [hm]
        refine dvd_pow_self p ?_
        intro h0
        exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hm, h0, pow_zero]))
      obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card' p hpdvdW
      have hy_ordG : orderOf ((y : G)) = p := by
        rw [← hy_ord]
        exact orderOf_injective W.subtype W.subtype_injective y
      have hyP : (y : G) ∈ P.map H.subtype := y.2.1
      have hyC : (y : G) ∈ Subgroup.centralizer (R₀ : Set G) := y.2.2
      -- conjugation by anything centralizing `R₀` preserves `C_G(R₀)`.
      have hCnorm : ∀ z ∈ Subgroup.centralizer (R₀ : Set G),
          ∀ c ∈ Subgroup.centralizer (R₀ : Set G),
          z * c * z⁻¹ ∈ Subgroup.centralizer (R₀ : Set G) := by
        intro z hz c hc
        rw [Subgroup.mem_centralizer_iff] at hz hc ⊢
        intro g hg
        have h1 := hz g hg
        have h2 := hc g hg
        have h3 : g * z⁻¹ = z⁻¹ * g := (Commute.inv_right (h1 : Commute g z) : Commute g z⁻¹)
        calc g * (z * c * z⁻¹)
            = (g * z) * c * z⁻¹ := by group
          _ = (z * g) * c * z⁻¹ := by rw [h1]
          _ = z * (g * c) * z⁻¹ := by group
          _ = z * (c * g) * z⁻¹ := by rw [h2]
          _ = z * c * (g * z⁻¹) := by group
          _ = z * c * (z⁻¹ * g) := by rw [h3]
          _ = (z * c * z⁻¹) * g := by group
      -- `↑y` normalizes `A := C_{V_G}(R₀)`.
      obtain ⟨A, hA⟩ : ∃ A : Subgroup G, A = VG ⊓ Subgroup.centralizer (R₀ : Set G) := ⟨_, rfl⟩
      have hy_normA : (y : G) ∈ Subgroup.normalizer (A : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [hA]
        constructor
        · intro hx1
          obtain ⟨hxV, hxc⟩ := Subgroup.mem_inf.mp hx1
          exact Subgroup.mem_inf.mpr ⟨hVGnorm.conj_mem x hxV (y : G), hCnorm _ hyC x hxc⟩
        · intro hx1
          obtain ⟨hxV, hxc⟩ := Subgroup.mem_inf.mp hx1
          have h1 : (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * ((y : G)⁻¹)⁻¹ = x := by group
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h2 := hVGnorm.conj_mem _ hxV (y : G)⁻¹
            rwa [h1] at h2
          · have h2 := hCnorm _ (Subgroup.inv_mem _ hyC) _ hxc
            rwa [h1] at h2
      -- `T := A ⊔ ⟨y⟩` is a `p`-group inside the `Z`-group `H ⊓ C_G(R₀)`, hence cyclic.
      set Y : Subgroup G := Subgroup.zpowers (y : G) with hY
      set T : Subgroup G := A ⊔ Y with hT
      have hAT : A ≤ T := le_sup_left
      have hYT : Y ≤ T := le_sup_right
      have hyT : (y : G) ∈ T := hYT (Subgroup.mem_zpowers _)
      have hT_norm : T ≤ Subgroup.normalizer (A : Set G) :=
        sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hy_normA)
      haveI hA''norm : ((A.subgroupOf T) : Subgroup ↥T).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hT_norm
      have hA''card : Nat.card ↥(A.subgroupOf T) = p :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv).trans (by rw [hA]; exact h319)
      -- the product decomposition `T = A·Y` and the quotient `T/A` generated by `mk y`.
      have hTset : (T : Set G) = (A : Set G) * (Y : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left A Y
          (Subgroup.zpowers_le.mpr hy_normA)
      have hquot_gen : ∀ q : (↥T ⧸ (A.subgroupOf T : Subgroup ↥T)),
          q ∈ Subgroup.zpowers ((QuotientGroup.mk' (A.subgroupOf T)) ⟨(y : G), hyT⟩) := by
        intro q
        obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ q
        have htm : (t : G) ∈ (A : Set G) * (Y : Set G) := by
          rw [← hTset]
          exact t.2
        obtain ⟨av, hav, yv, hyv, heq⟩ := htm
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyv
        have ht_eq : t = (⟨av, hAT hav⟩ : ↥T) * (⟨(y : G), hyT⟩ : ↥T) ^ k := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_zpow]
          rw [← heq, hk]
        rw [ht_eq, map_mul, map_zpow]
        have hav1 : (QuotientGroup.mk' (A.subgroupOf T : Subgroup ↥T)) ⟨av, hAT hav⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hav
        rw [hav1, one_mul]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
      have hquot_card : Nat.card (↥T ⧸ (A.subgroupOf T : Subgroup ↥T)) ∣ p := by
        have htop : Subgroup.zpowers ((QuotientGroup.mk' (A.subgroupOf T : Subgroup ↥T))
            ⟨(y : G), hyT⟩) = ⊤ := by
          rw [eq_top_iff]
          exact fun q _ => hquot_gen q
        have h1 : Nat.card (↥T ⧸ (A.subgroupOf T : Subgroup ↥T))
            = orderOf ((QuotientGroup.mk' (A.subgroupOf T : Subgroup ↥T)) ⟨(y : G), hyT⟩) := by
          rw [← Nat.card_zpowers, htop]
          exact Nat.card_congr Subgroup.topEquiv.symm.toEquiv
        rw [h1, ← hy_ordG]
        have h2 : orderOf (⟨(y : G), hyT⟩ : ↥T) = orderOf (y : G) :=
          (orderOf_injective T.subtype T.subtype_injective ⟨(y : G), hyT⟩).symm
        rw [← h2]
        exact orderOf_map_dvd _ _
      have hTp : IsPGroup p ↥T := by
        have h1 : Nat.card ↥T ∣ p * p := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
            (A.subgroupOf T : Subgroup ↥T), hA''card]
          exact mul_dvd_mul hquot_card dvd_rfl
        have h1' : Nat.card ↥T ∣ p ^ 2 := by rwa [← pow_two] at h1
        rcases (Nat.dvd_prime_pow hp).mp h1' with ⟨k, _, hcard⟩
        exact IsPGroup.of_card hcard
      have hT_le_Z : T ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) := by
        refine sup_le ?_ ?_
        · rw [hA]
          exact le_inf (inf_le_left.trans (Subgroup.map_subtype_le V)) inf_le_right
        rw [Subgroup.zpowers_le]
        exact ⟨Subgroup.map_subtype_le P hyP, hyC⟩
      -- `T` is cyclic (`p`-subgroup of a `Z`-group).
      haveI hTZ : _root_.IsZGroup ↥T := by
        haveI := isZGroup_iff_mathlib.mp hZ
        exact IsZGroup.of_injective (Subgroup.inclusion_injective hT_le_Z)
      haveI hTcyc : IsCyclic ↥T := by
        have h1 : IsPGroup p ↥(⊤ : Subgroup ↥T) :=
          hTp.of_injective (⊤ : Subgroup ↥T).subtype (⊤ : Subgroup ↥T).subtype_injective
        haveI := IsPGroup.isCyclic_of_isZGroup h1
        exact isCyclic_of_surjective _ (Subgroup.topEquiv (G := ↥T)).surjective
      -- the `p`-torsion of the cyclic `T` has at most `p` elements, and `A` already fills it;
      -- so `y ∈ A ≤ V_G`, contradicting `P_G ⊓ V_G = ⊥`.
      classical
      haveI := Fintype.ofFinite ↥T
      have hle : (Finset.univ.filter (fun a : ↥T => a ^ p = 1)).card ≤ p := by
        convert IsCyclic.card_pow_eq_one_le (α := ↥T) (n := p) hp.pos using 2
      have hsubset : Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T)
          ⊆ Finset.univ.filter (fun a : ↥T => a ^ p = 1) := by
        intro t ht
        rw [Set.mem_toFinset] at ht
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hA_exp _ (hA ▸ Subgroup.mem_subgroupOf.mp ht)
      have hcard_eq : (Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T)).card = p := by
        rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
        exact hA''card
      have hy_filter : (⟨(y : G), hyT⟩ : ↥T)
          ∈ Finset.univ.filter (fun a : ↥T => a ^ p = 1) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy_ordG]
        exact pow_orderOf_eq_one _
      have hyA : (y : G) ∈ A := by
        by_contra hnot
        have hnotfin : (⟨(y : G), hyT⟩ : ↥T)
            ∉ Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T) := by
          rw [Set.mem_toFinset]
          intro hmem
          exact hnot (Subgroup.mem_subgroupOf.mp hmem)
        have hsub2 : insert (⟨(y : G), hyT⟩ : ↥T)
            (Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T))
            ⊆ Finset.univ.filter (fun a : ↥T => a ^ p = 1) :=
          Finset.insert_subset hy_filter hsubset
        have hcard2 := Finset.card_le_card hsub2
        rw [Finset.card_insert_of_notMem hnotfin, hcard_eq] at hcard2
        omega
      have hybot : (y : G) ∈ (P.map H.subtype : Subgroup G) ⊓ VG := ⟨hyP, (hA ▸ hyA).1⟩
      rw [hPV_inf, Subgroup.mem_bot] at hybot
      rw [hybot, orderOf_one] at hy_ordG
      exact hp.one_lt.ne hy_ordG
    -- **(3.21)** `P = ⁅P, R₀⁆` (action-commutator form): the `R₀`-action on `P` has trivial
    -- fixed points by (3.20), so Prop 1.6(a) makes its action commutator all of `P`.
    have hP₀_inv : OddOrder.Isaacs.Ch03.IsAInvariant
        (φ.comp (Subgroup.inclusion hR₀R)) P :=
      fun a => hP_inv (Subgroup.inclusion hR₀R a)
    have h321 : OddOrder.Isaacs.Ch04.actionCommutator hP₀_inv.restrict = ⊤ := by
      have hCopP : Nat.Coprime (Nat.card ↥R₀) (Nat.card ↥P) :=
        (hHall.symm.coprime_dvd_left (Subgroup.card_dvd_of_le hR₀R)).coprime_dvd_right
          (Subgroup.card_subgroup_dvd_card P)
      have hsup := OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
        (φ := hP₀_inv.restrict) hCopP (Or.inr inferInstance)
      have hfix_bot : Subgroup.fixedPointsOfMulAut hP₀_inv.restrict = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_fixedPointsOfMulAut] at hx
        have hmem : ((x : ↥H) : G) ∈ (P.map H.subtype : Subgroup G)
            ⊓ Subgroup.centralizer (R₀ : Set G) := by
          refine ⟨⟨(x : ↥H), x.2, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
          have h1 := hx ⟨g, hg⟩
          have h2 := congrArg Subtype.val h1
          rw [OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val] at h2
          have h3 := congrArg Subtype.val h2
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype,
            MulAut.conjNormal_apply, Subgroup.coe_inclusion] at h3
          exact mul_inv_eq_iff_eq_mul.mp h3
        rw [h320, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]
        exact Subtype.ext (Subtype.ext (by simpa using hmem))
      rw [hfix_bot, bot_sup_eq] at hsup
      exact hsup
    -- `G`-level form of (3.21): `⁅P_G, R₀⁆ = P_G` (push the action commutator through the two
    -- subtype levels `↥P → ↥H → G`).  Used at (3.22) (`P = [P,R₀] ≤ [VXP,R₀]`).
    have h321G : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = P.map H.subtype := by
      apply le_antisymm
      · rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        obtain ⟨ph, hph, rfl⟩ := hg₁
        have h2 : g₂ * (ph : G)⁻¹ * g₂⁻¹ ∈ (P.map H.subtype : Subgroup G) := by
          refine ⟨_, hP_inv.smul_mem ⟨g₂, hR₀R hg₂⟩ (P.inv_mem hph), ?_⟩
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
            Subgroup.coe_inv]
        have heq : ⁅(ph : G), g₂⁆ = (ph : G) * (g₂ * (ph : G)⁻¹ * g₂⁻¹) := by
          rw [commutatorElement_def]
          group
        show ⁅(ph : G), g₂⁆ ∈ (P.map H.subtype : Subgroup G)
        rw [heq]
        exact Subgroup.mul_mem _ ⟨ph, hph, rfl⟩ h2
      · rintro _ ⟨pp, hpp, rfl⟩
        have hmem : (⟨pp, hpp⟩ : ↥P) ∈ OddOrder.Isaacs.Ch04.actionCommutator hP₀_inv.restrict := by
          rw [h321]
          trivial
        have key : ∀ x ∈ OddOrder.Isaacs.Ch04.actionCommutator hP₀_inv.restrict,
            ((x : ↥H) : G) ∈ (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) := by
          intro x hx
          rw [OddOrder.Isaacs.Ch04.actionCommutator] at hx
          induction hx using Subgroup.closure_induction with
          | mem y hy =>
            obtain ⟨g, a, rfl⟩ := hy
            have h1 := congrArg Subtype.val
              (OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val hP₀_inv a g⁻¹)
            simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype,
              MulAut.conjNormal_apply, Subgroup.coe_inclusion] at h1
            have hval : (((g * (hP₀_inv.restrict a) g⁻¹ : ↥P) : ↥H) : G)
                = ⁅((g : ↥H) : G), (a : G)⁆ := by
              rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, commutatorElement_def]
              simp only [Subgroup.coe_inv]
              group
            rw [hval]
            exact Subgroup.commutator_mem_commutator ⟨(g : ↥H), g.2, rfl⟩ a.2
          | one => simpa using Subgroup.one_mem _
          | mul y z hy hz ihy ihz =>
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            exact Subgroup.mul_mem _ ihy ihz
          | inv y hy ihy =>
            rw [Subgroup.coe_inv, Subgroup.coe_inv]
            exact Subgroup.inv_mem _ ihy
        exact key _ hmem
    -- ===== Phase D (3.22)–(3.31): the structure of `G` =====
    -- **(3.22)** `[X, P] = ⊥` for every `PR₀`-invariant `X ≤ K` with `VXPR₀ ≠ G`.  Set
    -- `HX := VXP` and `S₂ := HX·R₀ < G`.  By minimality (IH on `S₂`), `[HX, R₀]` has `p`-length
    -- one.  `O_{p'}(HX) = ⊥` since `V ≤ HX` is a self-centralizing ((3.10)) normal `p`-subgroup;
    -- `O_{p'}([HX,R₀]) char [HX,R₀] ⊴ HX` forces `O_{p'}([HX,R₀]) = ⊥`, so `p`-subgroups of
    -- `[HX,R₀]` lie in `O_p([HX,R₀])`.  By (3.21), `P = [P,R₀] ≤ [HX,R₀]`, so
    -- `[X,P] ≤ [X, O_p([HX,R₀])] ≤ X ⊓ O_p([HX,R₀]) = ⊥` (`X` is a `p'`-group).
    have h322 : ∀ X : Subgroup G, X ≤ KG →
        R₀ ≤ Subgroup.normalizer (X : Set G) →
        (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        VG ⊔ X ⊔ (P.map H.subtype) ⊔ R₀ ≠ ⊤ →
        (⁅X, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = ⊥ := by
      intro X hXK hXR₀ hXP hne
      set HX : Subgroup G := VG ⊔ X ⊔ P.map H.subtype with hHXdef
      set S₂ : Subgroup G := HX ⊔ R₀ with hS₂def
      set WG : Subgroup G := ⁅HX, R₀⁆ with hWGdef
      -- basic inclusions
      have hX_le_H : X ≤ H := hXK.trans hKG_le_H
      have hHX_le_H : HX ≤ H := by
        rw [hHXdef]
        exact sup_le (sup_le (Subgroup.map_subtype_le V) hX_le_H) (Subgroup.map_subtype_le P)
      have hHX_le_S₂ : HX ≤ S₂ := by rw [hS₂def]; exact le_sup_left
      have hR₀_le_S₂ : R₀ ≤ S₂ := by rw [hS₂def]; exact le_sup_right
      have hVG_le_HX : VG ≤ HX := by rw [hHXdef]; exact le_sup_left.trans le_sup_left
      have hX_le_HX : X ≤ HX := by rw [hHXdef]; exact le_sup_right.trans le_sup_left
      have hPG_le_HX : (P.map H.subtype : Subgroup G) ≤ HX := by
        rw [hHXdef]; exact le_sup_right
      have hX_le_S₂ : X ≤ S₂ := hX_le_HX.trans hHX_le_S₂
      -- `S₂ ≤ N_G(HX)`: `R₀` normalizes `V` (normal in `G`), `X` (hypothesis), `P` (`R`-invariant)
      have hS₂_le_NHX : S₂ ≤ Subgroup.normalizer (HX : Set G) := by
        rw [hS₂def]
        refine sup_le Subgroup.le_normalizer ?_
        intro g hg
        have hgV : g ∈ Subgroup.normalizer (VG : Set G) := by
          rw [Subgroup.normalizer_eq_top]
          trivial
        have hgX : g ∈ Subgroup.normalizer (X : Set G) := hXR₀ hg
        have hgP : g ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) :=
          mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hP_inv) (hR₀R hg)
        rw [hHXdef]
        exact mem_normalizer_sup (mem_normalizer_sup hgV hgX) hgP
      haveI hHX'normal : ((HX.subgroupOf S₂) : Subgroup ↥S₂).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hS₂_le_NHX
      -- complement/Hall/odd/Z-group transports for the IH on `S₂` (the (3.6) battery)
      have hdisjHX : Disjoint HX R₀ := hcompl.disjoint.mono hHX_le_H hR₀R
      have hcompl₂ : Subgroup.IsComplement' (HX.subgroupOf S₂) (R₀.subgroupOf S₂) := by
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
        · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
          rw [Subgroup.mem_inf] at hx
          simp only [Subgroup.mem_subgroupOf] at hx
          have hmem : (x : G) ∈ HX ⊓ R₀ := ⟨hx.1, hx.2⟩
          rw [hdisjHX.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]
          exact Subtype.ext (by simpa using hmem)
        · have hsup : ((HX.subgroupOf S₂) : Subgroup ↥S₂) ⊔ (R₀.subgroupOf S₂) = ⊤ := by
            rw [← Subgroup.subgroupOf_sup hHX_le_S₂ hR₀_le_S₂, Subgroup.subgroupOf_self]
          have hmul := Subgroup.normal_mul ((HX.subgroupOf S₂) : Subgroup ↥S₂)
            (R₀.subgroupOf S₂)
          rw [hsup, Subgroup.coe_top] at hmul
          exact hmul.symm
      have hHXcard : Nat.card ↥(HX.subgroupOf S₂) = Nat.card ↥HX :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX_le_S₂).toEquiv
      have hR₀card₂ : Nat.card ↥(R₀.subgroupOf S₂) = Nat.card ↥R₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_S₂).toEquiv
      have hHall₂ : Nat.Coprime (Nat.card ↥(HX.subgroupOf S₂))
          (Nat.card ↥(R₀.subgroupOf S₂)) := by
        rw [hHXcard, hR₀card₂]
        exact (hHall.coprime_dvd_left (Subgroup.card_dvd_of_le hHX_le_H)).coprime_dvd_right
          (Subgroup.card_dvd_of_le hR₀R)
      have hodd₂ : Odd (Nat.card ↥S₂) := by
        obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card S₂
        rw [hm, Nat.odd_mul] at hodd
        exact hodd.1
      have hR₀p₂ : ∃ r' : ℕ, r'.Prime ∧ Nat.card ↥(R₀.subgroupOf S₂) = r' :=
        ⟨r, hr_prime, hR₀card₂.trans hr_card⟩
      have hZ₂ : OddOrder.GroupTheory.IsZGroup
          ↥(HX.subgroupOf S₂ ⊓ Subgroup.centralizer (R₀.subgroupOf S₂ : Set ↥S₂)) := by
        set A : Subgroup ↥S₂ :=
          HX.subgroupOf S₂ ⊓ Subgroup.centralizer (R₀.subgroupOf S₂ : Set ↥S₂) with hA
        have hle : A.map S₂.subtype ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) := by
          rintro _ ⟨a, ha, rfl⟩
          obtain ⟨haHX, hacent⟩ := Subgroup.mem_inf.mp ha
          rw [Subgroup.mem_subgroupOf] at haHX
          refine Subgroup.mem_inf.mpr
            ⟨hHX_le_H haHX, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
          have hgS : g ∈ S₂ := hR₀_le_S₂ hg
          have hcomm := (Subgroup.mem_centralizer_iff.mp hacent) (⟨g, hgS⟩ : ↥S₂)
            (Subgroup.mem_subgroupOf.mpr hg)
          exact congrArg (Subtype.val) hcomm
        haveI : _root_.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) :=
          isZGroup_iff_mathlib.mp hZ
        haveI : _root_.IsZGroup ↥(A.map S₂.subtype) :=
          IsZGroup.of_injective (Subgroup.inclusion_injective hle)
        have e := Subgroup.equivMapOfInjective A S₂.subtype (Subgroup.subtype_injective S₂)
        haveI : _root_.IsZGroup ↥A := IsZGroup.of_injective (f := e.toMonoidHom) e.injective
        exact isZGroup_iff_mathlib.mpr ‹_root_.IsZGroup ↥A›
      have hcard₂ : Nat.card ↥S₂ < n := by
        have hdvd : Nat.card ↥S₂ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S₂
        rw [← hn]
        exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd)
          (fun heq => hne (Subgroup.eq_top_of_card_eq S₂ heq))
      -- IH on `S₂` and the bridge down to `WG = [HX, R₀] ≤ G`
      have hIH := IH (Nat.card ↥S₂) hcard₂ hodd₂ hcompl₂ hHall₂
        (le_refl (R₀.subgroupOf S₂)) hR₀p₂ hZ₂ hp rfl
      have hmapeq : (⁅HX.subgroupOf S₂, R₀.subgroupOf S₂⁆ : Subgroup ↥S₂).map S₂.subtype
          = WG := by
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHX_le_S₂,
          inf_eq_left.mpr hR₀_le_S₂, hWGdef]
      have hiso := Subgroup.equivMapOfInjective
        (⁅HX.subgroupOf S₂, R₀.subgroupOf S₂⁆) S₂.subtype (Subgroup.subtype_injective S₂)
      have hplWG : hasPLengthOne p ↥WG := by
        have hpl := hasPLengthOne_of_mulEquiv (p := p) hiso hIH
        rwa [hmapeq] at hpl
      -- `S₂ ≤ N_G(WG)` (Isaacs Lemma 4.1 on both factors) and `WG ≤ HX`
      have hS₂_le_NWG : S₂ ≤ Subgroup.normalizer (WG : Set G) := by
        rw [hS₂def, hWGdef]
        exact sup_le (subgroup_le_normalizer_commutator_self HX R₀)
          (subgroup_le_normalizer_commutator_self_right HX R₀)
      have hWG_le_HX : WG ≤ HX := by
        rw [hWGdef, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hg₂n : g₂ ∈ Subgroup.normalizer (HX : Set G) := hS₂_le_NHX (hR₀_le_S₂ hg₂)
        rw [Subgroup.mem_normalizer_iff] at hg₂n
        have h2 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ HX := (hg₂n g₁⁻¹).mp (HX.inv_mem hg₁)
        have heq : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact HX.mul_mem hg₁ h2
      -- `O_{p'}(HX) = ⊥`: `V ≤ HX` is a self-centralizing ((3.10)) normal `p`-subgroup
      have hOp'HX : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥HX = ⊥ := by
        have hVHXp : IsPGroup p ↥(VG.subgroupOf HX) :=
          (hVp.map H.subtype).of_injective (Subgroup.subgroupOfEquivOfLe hVG_le_HX).toMonoidHom
            (Subgroup.subgroupOfEquivOfLe hVG_le_HX).injective
        have hCent : Subgroup.centralizer ((VG.subgroupOf HX : Subgroup ↥HX) : Set ↥HX)
            ≤ VG.subgroupOf HX := by
          intro w hw
          rw [Subgroup.mem_subgroupOf]
          have hwH : (w : G) ∈ H := hHX_le_H w.2
          have hwC : (⟨(w : G), hwH⟩ : ↥H)
              ∈ Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) := by
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            have hvVG : (v : G) ∈ VG := by rw [hVG]; exact ⟨v, hv, rfl⟩
            have h1 := Subgroup.mem_centralizer_iff.mp hw (⟨(v : G), hVG_le_HX hvVG⟩ : ↥HX)
              (Subgroup.mem_subgroupOf.mpr hvVG)
            have h2 := congrArg Subtype.val h1
            simp only [Subgroup.coe_mul] at h2
            exact Subtype.ext (by simpa using h2)
          rw [hCHV] at hwC
          rw [hVG]
          exact ⟨⟨(w : G), hwH⟩, hwC, rfl⟩
        exact oPiCore_compl_eq_bot_of_isPGroup_centralizer_le hVHXp hCent
      -- `O_{p'}(WG) = ⊥` (`WG ⊴ HX` in context, characteristic-in-normal transfer)
      have hOp'WG : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥WG = ⊥ := by
        have hWGnorm : ((WG.subgroupOf HX) : Subgroup ↥HX).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer (hHX_le_S₂.trans hS₂_le_NWG)
        exact oPiCore_eq_bot_of_subgroupOf_normal hWG_le_HX hWGnorm hOp'HX
      -- `P ≤ O_p(WG)` (kernel argument; `P = [P,R₀] ≤ WG` by (3.21))
      have hPG_le_WG : (P.map H.subtype : Subgroup G) ≤ WG := by
        rw [hWGdef]
        calc (P.map H.subtype : Subgroup G) = ⁅P.map H.subtype, R₀⁆ := h321G.symm
          _ ≤ ⁅HX, R₀⁆ := Subgroup.commutator_mono hPG_le_HX le_rfl
      have hQp : IsPGroup p ↥((P.map H.subtype).subgroupOf WG) :=
        (hPp.map H.subtype).of_injective (Subgroup.subgroupOfEquivOfLe hPG_le_WG).toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hPG_le_WG).injective
      have hPG_le_Op : (P.map H.subtype).subgroupOf WG ≤ OddOrder.Isaacs.Ch01.opCore p ↥WG :=
        le_opCore_of_hasPLengthOne_of_oPiCore_compl_eq_bot hplWG hOp'WG hQp
      -- `[X, P] ≤ X ⊓ O_p(WG)-lift = ⊥`
      set OpG : Subgroup G := (OddOrder.Isaacs.Ch01.opCore p ↥WG).map WG.subtype with hOpGdef
      have hPG_le_OpG : (P.map H.subtype : Subgroup G) ≤ OpG := by
        rw [hOpGdef]
        intro x hx
        exact ⟨⟨x, hPG_le_WG hx⟩, hPG_le_Op (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      have hOpGp : IsPGroup p ↥OpG := by
        rw [hOpGdef]
        exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥WG).map WG.subtype
      have hcomm_le : (⁅X, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≤ X ⊓ OpG := by
        rw [Subgroup.commutator_le]
        intro x hx q hq
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have hqn := hXP hq
          rw [Subgroup.mem_normalizer_iff] at hqn
          have h2 : q * x⁻¹ * q⁻¹ ∈ X := (hqn x⁻¹).mp (X.inv_mem hx)
          have heq : ⁅x, q⁆ = x * (q * x⁻¹ * q⁻¹) := by
            rw [commutatorElement_def]; group
          rw [heq]
          exact X.mul_mem hx h2
        · have hxn : x ∈ Subgroup.normalizer (OpG : Set G) := by
            rw [hOpGdef]
            exact mem_normalizer_map_subtype_of_characteristic (hS₂_le_NWG (hX_le_S₂ hx))
          rw [Subgroup.mem_normalizer_iff] at hxn
          have h2 : x * q * x⁻¹ ∈ OpG := (hxn q).mp (hPG_le_OpG hq)
          have heq : ⁅x, q⁆ = (x * q * x⁻¹) * q⁻¹ := by
            rw [commutatorElement_def]
          rw [heq]
          exact OpG.mul_mem h2 (OpG.inv_mem (hPG_le_OpG hq))
      have hXp' : ¬ p ∣ Nat.card ↥X := by
        intro hd
        have h2 : Nat.card ↥X ∣ Nat.card ↥KG := Subgroup.card_dvd_of_le hXK
        rw [hKG, Subgroup.card_map_of_injective H.subtype_injective, hKcard] at h2
        exact hK'p' (hd.trans h2)
      have hinf_bot : X ⊓ OpG = ⊥ := by
        refine Subgroup.inf_eq_bot_of_coprime ?_
        obtain ⟨k, hk⟩ := hOpGp.exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hXp').symm
      rw [eq_bot_iff, ← hinf_bot]
      exact hcomm_le
    -- **(3.23)** `G = VKPR₀` (else (3.22) with `X = K` gives `[K,P] = ⊥`, contrary to (3.13));
    -- hence `H = VKP` (Dedekind: the `R₀`-part of `h = a·r₀` lies in `H ⊓ R = ⊥`) and `R = R₀`
    -- (the `VKP`-part of `r = a·r₀` lies in `H ⊓ R = ⊥`).
    have hR₀_le_NKG : R₀ ≤ Subgroup.normalizer (KG : Set G) := fun g hg =>
      mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hK_inv) (hR₀R hg)
    have hPG_le_NKG : (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (KG : Set G) := by
      rintro _ ⟨x, hxP, rfl⟩
      have hxN : x ∈ N := hP_le_N hxP
      rw [hNdef] at hxN
      have h2 : H.subtype x ∈ (Subgroup.normalizer (K : Set ↥H)).map H.subtype :=
        Subgroup.mem_map_of_mem _ hxN
      rw [hKG]
      exact Subgroup.le_normalizer_map H.subtype h2
    -- `G`-level form of (3.13): `[K_G, P_G] ≠ ⊥`
    have h313G : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≠ ⊥ := by
      intro hbot
      apply h313
      have hmap : (⁅K, P⁆ : Subgroup ↥H).map H.subtype
          = ⁅KG, (P.map H.subtype : Subgroup G)⁆ := by
        rw [Subgroup.map_commutator, hKG]
      have h3 : (⁅K, P⁆ : Subgroup ↥H).map H.subtype = (⊥ : Subgroup ↥H).map H.subtype := by
        rw [Subgroup.map_bot, hmap]
        exact hbot
      exact Subgroup.map_injective (Subgroup.subtype_injective H) h3
    have h323G : VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ = ⊤ := by
      by_contra hne
      exact h313G (h322 KG (le_refl KG) hR₀_le_NKG hPG_le_NKG hne)
    -- Dedekind step: for `R₀`-normalized `Y ≤ K_G`, `VYPR₀ = G` forces `H = VYP`
    have hDedekind : ∀ Y : Subgroup G, Y ≤ KG → R₀ ≤ Subgroup.normalizer (Y : Set G) →
        VG ⊔ Y ⊔ (P.map H.subtype) ⊔ R₀ = ⊤ → VG ⊔ Y ⊔ (P.map H.subtype) = H := by
      intro Y hYK hYR₀ htop
      have hVYP_le_H : VG ⊔ Y ⊔ (P.map H.subtype) ≤ H :=
        sup_le (sup_le (Subgroup.map_subtype_le V) (hYK.trans hKG_le_H))
          (Subgroup.map_subtype_le P)
      have hR₀_le_NVYP : R₀ ≤ Subgroup.normalizer
          ((VG ⊔ Y ⊔ (P.map H.subtype) : Subgroup G) : Set G) := by
        intro g hg
        have hgV : g ∈ Subgroup.normalizer (VG : Set G) := by
          rw [Subgroup.normalizer_eq_top]; trivial
        have hgP : g ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) :=
          mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hP_inv) (hR₀R hg)
        exact mem_normalizer_sup (mem_normalizer_sup hgV (hYR₀ hg)) hgP
      have hVYPset : ((VG ⊔ Y ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G)
          = ((VG ⊔ Y ⊔ (P.map H.subtype) : Subgroup G) : Set G) * (R₀ : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left _ _ hR₀_le_NVYP
      refine le_antisymm hVYP_le_H ?_
      intro h hh
      have hmem : h ∈ ((VG ⊔ Y ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G) := by
        rw [htop]; trivial
      rw [hVYPset] at hmem
      obtain ⟨a, ha, r₀, hr₀, heq⟩ := hmem
      have hr₀H : r₀ ∈ H := by
        have h1 : r₀ = a⁻¹ * h := by rw [← heq]; group
        rw [h1]
        exact H.mul_mem (H.inv_mem (hVYP_le_H ha)) hh
      have hr₀bot : r₀ ∈ H ⊓ R := ⟨hr₀H, hR₀R hr₀⟩
      rw [hcompl.disjoint.eq_bot, Subgroup.mem_bot] at hr₀bot
      rw [hr₀bot] at heq
      simp only [mul_one] at heq
      rwa [← heq]
    have h323H : VG ⊔ KG ⊔ (P.map H.subtype) = H :=
      hDedekind KG (le_refl KG) hR₀_le_NKG h323G
    have hHXK_le_H : VG ⊔ KG ⊔ (P.map H.subtype) ≤ H := le_of_eq h323H
    have h323R : R = R₀ := by
      refine le_antisymm ?_ hR₀R
      intro x hx
      have hR₀_le_NVKP : R₀ ≤ Subgroup.normalizer
          ((VG ⊔ KG ⊔ (P.map H.subtype) : Subgroup G) : Set G) := by
        intro g hg
        have hgV : g ∈ Subgroup.normalizer (VG : Set G) := by
          rw [Subgroup.normalizer_eq_top]; trivial
        have hgP : g ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) :=
          mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hP_inv) (hR₀R hg)
        exact mem_normalizer_sup (mem_normalizer_sup hgV (hR₀_le_NKG hg)) hgP
      have hVKPset : ((VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G)
          = ((VG ⊔ KG ⊔ (P.map H.subtype) : Subgroup G) : Set G) * (R₀ : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left _ _ hR₀_le_NVKP
      have hmem : x ∈ ((VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G) := by
        rw [h323G]; trivial
      rw [hVKPset] at hmem
      obtain ⟨a, ha, r₀, hr₀, heq⟩ := hmem
      have habot : a ∈ H ⊓ R := by
        refine ⟨hHXK_le_H ha, ?_⟩
        have h1 : a = x * r₀⁻¹ := by rw [← heq]; group
        rw [h1]
        exact R.mul_mem hx (R.inv_mem (hR₀R hr₀))
      rw [hcompl.disjoint.eq_bot, Subgroup.mem_bot] at habot
      rw [habot] at heq
      simp only [one_mul] at heq
      rwa [← heq]
    -- **(3.22), unconditional form**: `[X, P] = ⊥` for `PR₀`-invariant `X` **properly** below `K`
    -- (if `VXPR₀ = G` then `H = VXP` by Dedekind, and `|VXP| = |V|·|X|·|P|` against
    -- `|H| = |V|·|K|·|P|` forces `X = K`).
    have hcop_KG_PG : ∀ Y : Subgroup G, Y ≤ KG →
        Nat.Coprime (Nat.card ↥Y) (Nat.card ↥(P.map H.subtype : Subgroup G)) := by
      intro Y hYK
      obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
      rw [hk]
      refine Nat.Coprime.pow_right k (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr ?_))
      intro hd
      have h3 : Nat.card ↥Y ∣ Nat.card ↥K' := by
        have h4 : Nat.card ↥Y ∣ Nat.card ↥KG := Subgroup.card_dvd_of_le hYK
        rwa [hKG, Subgroup.card_map_of_injective H.subtype_injective, hKcard] at h4
      exact hK'p' (hd.trans h3)
    have hPG_p'_disj : ∀ Y : Subgroup G, Y ≤ KG →
        Disjoint Y (P.map H.subtype : Subgroup G) := fun Y hYK =>
      disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime (hcop_KG_PG Y hYK))
    have hVG_disj : ∀ Y : Subgroup G, Y ≤ KG →
        Disjoint VG (Y ⊔ (P.map H.subtype) : Subgroup G) := by
      intro Y hYK
      have hNG : Y ⊔ (P.map H.subtype) ≤ N.map H.subtype :=
        sup_le (hYK.trans (by rw [hKG]; exact Subgroup.map_mono hK_le_N))
          (Subgroup.map_mono hP_le_N)
      have hVN : VG ⊓ N.map H.subtype = ⊥ := by
        rw [hVG, ← Subgroup.map_inf _ _ H.subtype H.subtype_injective, hVN_inf,
          Subgroup.map_bot]
      exact (disjoint_iff.mpr hVN).mono_right hNG
    have hcard_VYP : ∀ Y : Subgroup G, Y ≤ KG →
        (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (Y : Set G) →
        Nat.card ↥(VG ⊔ Y ⊔ (P.map H.subtype) : Subgroup G)
          = Nat.card ↥VG * (Nat.card ↥Y * Nat.card ↥(P.map H.subtype : Subgroup G)) := by
      intro Y hYK hYP
      rw [sup_assoc, card_sup_of_le_normalizer_of_disjoint
          (by rw [Subgroup.normalizer_eq_top]; exact le_top) (hVG_disj Y hYK),
        card_sup_of_le_normalizer_of_disjoint hYP (hPG_p'_disj Y hYK)]
    have h322' : ∀ X : Subgroup G, X ≤ KG → X ≠ KG →
        R₀ ≤ Subgroup.normalizer (X : Set G) →
        (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        (⁅X, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = ⊥ := by
      intro X hXK hXne hXR₀ hXP
      refine h322 X hXK hXR₀ hXP ?_
      intro htop
      apply hXne
      have hH_eq := hDedekind X hXK hXR₀ htop
      have h1 := hcard_VYP X hXK hXP
      have h2 := hcard_VYP KG (le_refl KG) hPG_le_NKG
      rw [hH_eq] at h1
      rw [h323H] at h2
      have h3 := h1.symm.trans h2
      have h4 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
      have hX_eq := Nat.eq_of_mul_eq_mul_right Nat.card_pos h4
      exact Subgroup.eq_of_le_of_card_ge hXK hX_eq.ge
    -- **(3.24)** `K = [K, P]` (at the `G` level).  Else `[K,P]` is a proper `PR₀`-invariant
    -- subgroup of `K`, so the unconditional (3.22) gives `[[K,P],P] = ⊥`; but
    -- `[[K,P],P] = [K,P]` (Prop 1.6(b), applied inside `KP = K·P` where `K` is normal),
    -- contradicting (3.13).
    have h16bKP : (⁅⁅KG, (P.map H.subtype : Subgroup G)⁆, P.map H.subtype⁆ : Subgroup G)
        = ⁅KG, (P.map H.subtype : Subgroup G)⁆ := by
      set KP : Subgroup G := KG ⊔ (P.map H.subtype) with hKPdef
      have hKG_le_KP : KG ≤ KP := by rw [hKPdef]; exact le_sup_left
      have hPG_le_KP : (P.map H.subtype : Subgroup G) ≤ KP := by
        rw [hKPdef]; exact le_sup_right
      have hKPnorm : KP ≤ Subgroup.normalizer (KG : Set G) := by
        rw [hKPdef]
        exact sup_le Subgroup.le_normalizer hPG_le_NKG
      haveI : ((KG.subgroupOf KP) : Subgroup ↥KP).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hKPnorm
      have hcop : Nat.Coprime (Nat.card ↥(KG.subgroupOf KP))
          (Nat.card ↥((P.map H.subtype).subgroupOf KP)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG_le_KP).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_KP).toEquiv]
        exact hcop_KG_PG KG (le_refl KG)
      have h2 := commutator_commutator_right_eq (KG.subgroupOf KP)
        ((P.map H.subtype).subgroupOf KP) hcop
      have hKmap : (KG.subgroupOf KP).map KP.subtype = KG := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKG_le_KP]
      have hPmap : ((P.map H.subtype).subgroupOf KP).map KP.subtype = P.map H.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPG_le_KP]
      have h3 := congrArg (Subgroup.map KP.subtype) h2
      simp only [Subgroup.map_commutator] at h3
      rw [hKmap, hPmap] at h3
      exact h3
    have h324 : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = KG := by
      by_contra hne24
      have hle : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≤ KG := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hg₂n := hPG_le_NKG hg₂
        rw [Subgroup.mem_normalizer_iff] at hg₂n
        have h2 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ KG := (hg₂n g₁⁻¹).mp (KG.inv_mem hg₁)
        have heq : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact KG.mul_mem hg₁ h2
      have hR₀inv : R₀ ≤ Subgroup.normalizer
          ((⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) : Set G) := fun g hg =>
        mem_normalizer_commutator (hR₀_le_NKG hg)
          (mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hP_inv) (hR₀R hg))
      have hPinv : (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer
          ((⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) : Set G) :=
        subgroup_le_normalizer_commutator_self_right KG (P.map H.subtype)
      have hbot := h322' _ hle hne24 hR₀inv hPinv
      rw [h16bKP] at hbot
      exact h313G hbot
    -- **(3.25), first half**: `K` is a `q`-group for a prime `q ∉ {p, r}`.  `K ≅ F(N)` is
    -- nilpotent, so `K = ⨆_ℓ O_ℓ(K)`; if no single prime carries all of `K`, every `O_ℓ(K)` is a
    -- proper characteristic (hence `PR₀`-invariant) subgroup of `K`, centralized by `P` by the
    -- unconditional (3.22) — so `[K,P] = ⊥`, contradicting (3.13).
    haveI hKG_nilp : Group.IsNilpotent ↥KG := by
      have e1 := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
      have e2 := Subgroup.subgroupOfEquivOfLe hK_le_N
      haveI : Group.IsNilpotent ↥(K.subgroupOf N) := by
        rw [hKN_fit]
        infer_instance
      refine Group.nilpotent_of_surjective (e1.toMonoidHom.comp e2.toMonoidHom) ?_
      rw [MonoidHom.coe_comp]
      exact e1.surjective.comp e2.surjective
    obtain ⟨q, hq_prime, hq_ne_p, hq_ne_r, hKGq⟩ :
        ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ≠ r ∧ IsPGroup q ↥KG := by
      have hKG_ne_bot : KG ≠ ⊥ := by
        intro hbot
        apply h313G
        rw [hbot, Subgroup.commutator_bot_left]
      have hcard_ne : Nat.card ↥KG ≠ 1 := fun h =>
        hKG_ne_bot (Subgroup.eq_bot_of_card_eq _ h)
      obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hcard_ne
      haveI : Fact q.Prime := ⟨hq_prime⟩
      have hKGK : Nat.card ↥KG = Nat.card ↥K := by
        rw [hKG, Subgroup.card_map_of_injective H.subtype_injective]
      refine ⟨q, hq_prime, ?_, ?_, ?_⟩
      · intro hqp
        have h2 : q ∣ Nat.card ↥K' := (hKGK.trans hKcard) ▸ hq_dvd
        exact hK'p' (hqp ▸ h2)
      · intro hqr
        have h2 : q ∣ Nat.card ↥K := hKGK ▸ hq_dvd
        exact hr_ndvd_K (hqr ▸ h2)
      · by_contra hnotq
        apply h313G
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        -- every `O_ℓ(K)`-lift is proper (else `K` is an `ℓ`-group with `q ∣ |K|`, so `ℓ = q`)
        have hproper : ∀ ℓ : (Nat.card ↥KG).primeFactors,
            (OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG).map KG.subtype ≠ KG := by
          intro ℓ heq
          haveI : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
          have h2 : Nat.card ↥((OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG).map KG.subtype)
              = Nat.card ↥(OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG) :=
            Subgroup.card_map_of_injective (Subgroup.subtype_injective KG)
          rw [heq] at h2
          obtain ⟨m, hm⟩ :=
            (OddOrder.Isaacs.Ch01.opCore_isPGroup (ℓ : ℕ) ↥KG).exists_card_eq
          have hKℓ : IsPGroup (ℓ : ℕ) ↥KG := IsPGroup.of_card (h2.trans hm)
          obtain ⟨m', hm'⟩ := hKℓ.exists_card_eq
          have hq_eq : q = (ℓ : ℕ) :=
            (Nat.prime_dvd_prime_iff_eq hq_prime (Nat.prime_of_mem_primeFactors ℓ.2)).mp
              (hq_prime.dvd_of_dvd_pow (hm' ▸ hq_dvd))
          exact hnotq (hq_eq ▸ hKℓ)
        -- hence every `O_ℓ(K)`-lift is centralized by `P` ((3.22), unconditional form)
        have hOl_cent : ∀ ℓ : (Nat.card ↥KG).primeFactors,
            (OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG).map KG.subtype
              ≤ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
          intro ℓ
          haveI : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_
          refine h322' _ (Subgroup.map_subtype_le _) (hproper ℓ) ?_ ?_
          · exact fun g hg => mem_normalizer_map_subtype_of_characteristic (hR₀_le_NKG hg)
          · exact fun g hg => mem_normalizer_map_subtype_of_characteristic (hPG_le_NKG hg)
        -- nilpotency: `F(K) = ⊤`, so `K = ⨆_ℓ O_ℓ(K)` and the centralizer absorbs all of `K`
        have hfit_top : OddOrder.Isaacs.Ch01.fitting ↥KG = ⊤ := by
          refine le_antisymm le_top ?_
          haveI : Group.IsNilpotent ↥(⊤ : Subgroup ↥KG) :=
            Group.nilpotent_of_surjective (Subgroup.topEquiv (G := ↥KG)).symm.toMonoidHom
              (Subgroup.topEquiv (G := ↥KG)).symm.surjective
          exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
        have hC : ∀ y : ↥KG, y ∈ (⨆ ℓ : (Nat.card ↥KG).primeFactors,
            OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG : Subgroup ↥KG) →
            (y : G) ∈ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
          intro y hy
          exact Subgroup.iSup_induction
            (C := fun w : ↥KG => (w : G) ∈ Subgroup.centralizer
              ((P.map H.subtype : Subgroup G) : Set G))
            (fun ℓ : (Nat.card ↥KG).primeFactors => OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG)
            hy (fun ℓ z hz => hOl_cent ℓ ⟨z, hz, rfl⟩)
            (by simpa using Subgroup.one_mem _)
            (fun z w hz hw => by
              show (z : G) * (w : G) ∈ _
              exact Subgroup.mul_mem _ hz hw)
        intro x hx
        refine hC ⟨x, hx⟩ ?_
        rw [← OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors, hfit_top]
        trivial
    -- **(3.25)+(3.26)** `K` is a **special `q`-group of exponent `q`**.  Apply Gorenstein 5.3.7
    -- (`S04e`) to the conjugation action of `A := P·R₀ ≤ N_G(K)` on `K`: there is a minimal
    -- `A`-invariant `Q ≤ K` on which some `ψ ∈ P` acts nontrivially, and `Q` is special of
    -- exponent `q`.  If `Q` were proper, the unconditional (3.22) would make `P` centralize it,
    -- contradicting the nontrivial `ψ`-action; so `Q = K`.
    -- the conjugation action of `A := P·R₀ ≤ N_G(K)` on `K` (used at (3.25), (3.28), (3.29))
    have hA_le_N : (P.map H.subtype : Subgroup G) ⊔ R₀ ≤ Subgroup.normalizer (KG : Set G) :=
      sup_le hPG_le_NKG hR₀_le_NKG
    set A : Subgroup G := (P.map H.subtype) ⊔ R₀ with hAdef
    set φA : ↥A →* MulAut ↥KG :=
      KG.normalizerMonoidHom.comp (Subgroup.inclusion hA_le_N) with hφA
    have hφA_val : ∀ (a : ↥A) (k : ↥KG),
        ((φA a k : ↥KG) : G) = (a : G) * (k : G) * (a : G)⁻¹ := fun a k => rfl
    have hAcard : Nat.card ↥A
        = Nat.card ↥(P.map H.subtype : Subgroup G) * Nat.card ↥R₀ := by
      rw [hAdef]
      exact card_sup_of_le_normalizer_of_disjoint
        (fun g hg => mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hP_inv) (hR₀R hg))
        (hcompl.disjoint.mono (Subgroup.map_subtype_le P) hR₀R)
    obtain ⟨hK_special, hK_exp⟩ : IsSpecial q ↥KG ∧ Monoid.exponent ↥KG = q := by
      haveI : Fact q.Prime := ⟨hq_prime⟩
      -- `q` is odd (`q ∣ |K| ∣ |G|` and `|G|` is odd)
      have hKG_ne_bot : KG ≠ ⊥ := by
        intro hbot
        apply h313G
        rw [hbot, Subgroup.commutator_bot_left]
      have hq_dvd_KG : q ∣ Nat.card ↥KG := by
        obtain ⟨m, hm⟩ := hKGq.exists_card_eq
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hm, hm0, pow_zero])) hKG_ne_bot
        · rw [hm]
          exact dvd_pow_self q hmpos.ne'
      have hq_odd : Odd q := by
        rcases hq_prime.eq_two_or_odd' with h2 | hodd_q
        · exfalso
          have h3 : (2 : ℕ) ∣ Nat.card G :=
            (h2 ▸ hq_dvd_KG).trans (Subgroup.card_subgroup_dvd_card KG)
          rcases hodd with ⟨t, ht⟩
          omega
        · exact hodd_q
      -- `|A| = |P|·|R₀|` is coprime to `|K|`
      have hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥KG) := by
        rw [hAcard]
        refine Nat.coprime_mul_iff_left.mpr ⟨?_, ?_⟩
        · exact (hcop_KG_PG KG (le_refl KG)).symm
        · rw [hr_card]
          refine (Nat.Prime.coprime_iff_not_dvd hr_prime).mpr ?_
          intro hd
          apply hr_ndvd_K
          have hKGK : Nat.card ↥KG = Nat.card ↥K := by
            rw [hKG, Subgroup.card_map_of_injective H.subtype_injective]
          exact hKGK ▸ hd
      -- some `ψ₀ ∈ P` acts nontrivially on `K` ((3.13))
      obtain ⟨ψ₀, hψ₀P, k₀, hk₀K, hψ₀k₀⟩ :
          ∃ ψ₀ ∈ (P.map H.subtype : Subgroup G), ∃ k₀ ∈ KG, ψ₀ * k₀ * ψ₀⁻¹ ≠ k₀ := by
        by_contra hall
        push Not at hall
        apply h313G
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        rw [Subgroup.mem_bot]
        have h2 := hall g₂ hg₂ g₁ hg₁
        have h3 : g₂ * g₁ = g₁ * g₂ := by
          calc g₂ * g₁ = (g₂ * g₁ * g₂⁻¹) * g₂ := by group
            _ = g₁ * g₂ := by rw [h2]
        rw [commutatorElement_def,
          show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = (g₁ * g₂) * (g₂ * g₁)⁻¹ by group, ← h3]
        group
      have hψ₀A : ψ₀ ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_left hψ₀P
      have hψ_nt : ¬ ∀ g : ↥KG, φA ⟨ψ₀, hψ₀A⟩ g = g := by
        intro hall
        apply hψ₀k₀
        have h2 := congrArg Subtype.val (hall ⟨k₀, hk₀K⟩)
        rw [hφA_val] at h2
        exact h2
      -- Gorenstein 5.3.7 with minimality
      obtain ⟨Q, hQ_inv, hQ_nt, hQ_special, hQ_exp, _⟩ :=
        OddOrder.BG.Ch1.S04.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality
          hq_odd φA hKGq hCop hψ_nt
      -- `Q = ⊤`: a proper lift would be `PR₀`-invariant below `K`, hence `P`-central by (3.22)
      have hQ_top : Q = ⊤ := by
        by_contra hQne
        have hQlift_ne : Q.map KG.subtype ≠ KG := by
          intro heq
          apply hQne
          have h2 : Q.map KG.subtype = (⊤ : Subgroup ↥KG).map KG.subtype := by
            rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
          exact Subgroup.map_injective (Subgroup.subtype_injective KG) h2
        have hQR₀ : R₀ ≤ Subgroup.normalizer ((Q.map KG.subtype : Subgroup G) : Set G) := by
          intro g hg
          have hgA : g ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_right hg
          exact mem_normalizer_map_subtype_of_smul_val hQ_inv (hφA_val ⟨g, hgA⟩)
        have hQP : (P.map H.subtype : Subgroup G)
            ≤ Subgroup.normalizer ((Q.map KG.subtype : Subgroup G) : Set G) := by
          intro g hg
          have hgA : g ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_left hg
          exact mem_normalizer_map_subtype_of_smul_val hQ_inv (hφA_val ⟨g, hgA⟩)
        have hbot := h322' (Q.map KG.subtype) (Subgroup.map_subtype_le Q) hQlift_ne hQR₀ hQP
        obtain ⟨g0, hg0Q, hg0ne⟩ := hQ_nt
        apply hg0ne
        have hcent : (Q.map KG.subtype : Subgroup G)
            ≤ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
        have h2 := Subgroup.mem_centralizer_iff.mp (hcent ⟨g0, hg0Q, rfl⟩) ψ₀ hψ₀P
        apply Subtype.ext
        rw [hφA_val]
        show ψ₀ * (KG.subtype g0) * ψ₀⁻¹ = KG.subtype g0
        rw [mul_inv_eq_iff_eq_mul]
        exact h2
      constructor
      · exact IsSpecial.of_mulEquiv (Subgroup.topEquiv (G := ↥KG)) (hQ_top ▸ hQ_special)
      · exact (Monoid.exponent_eq_of_mulEquiv (Subgroup.topEquiv (G := ↥KG))).symm.trans
          (hQ_top ▸ hQ_exp)
    -- **(3.27)** `C_P(K) = ⊥`: a `P`-element centralizing `K` lies in `C_H(K) ≤ K` ((3.16)),
    -- and `P ⊓ K = ⊥` (`p` vs `p'`).
    have h327 : (P.map H.subtype : Subgroup G) ⊓ Subgroup.centralizer (KG : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxP, hxC⟩
      obtain ⟨xh, hxhP, rfl⟩ := hxP
      have hxhC : xh ∈ Subgroup.centralizer (K : Set ↥H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hkKG : (H.subtype k) ∈ KG := by
          rw [hKG]
          exact ⟨k, hk, rfl⟩
        have h2 := Subgroup.mem_centralizer_iff.mp hxC (H.subtype k) hkKG
        exact Subtype.ext (by simpa using h2)
      have hmem : (H.subtype xh) ∈ KG ⊓ (P.map H.subtype : Subgroup G) :=
        ⟨by rw [hKG]; exact ⟨xh, h316 hxhC, rfl⟩, ⟨xh, hxhP, rfl⟩⟩
      rw [(hPG_p'_disj KG (le_refl KG)).eq_bot] at hmem
      exact hmem
    -- **(3.28)** `C_{PR₀}(K) = ⊥`: a `p`-element of the centralizer lies in the normal Sylow
    -- `P` of `A = P·R₀`, hence in `C_P(K) = ⊥` ((3.27)); an `r`-element generates a Sylow
    -- `r`-subgroup of `A` conjugate to `R₀` (Sylow II), and its `K`-centralizing property
    -- transfers to `R₀` — contrary to (3.17).
    have h328 : A ⊓ Subgroup.centralizer (KG : Set G) = ⊥ := by
      by_contra hne
      obtain ⟨ℓ, hℓ_prime, hℓ_dvd⟩ := Nat.exists_prime_and_dvd
        (fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
      haveI : Fact ℓ.Prime := ⟨hℓ_prime⟩
      obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card' ℓ hℓ_dvd
      have hyMem := Subgroup.mem_inf.mp y.2
      have hy_ordG : orderOf ((y : G)) = ℓ := by
        rw [← hy_ord]
        exact orderOf_injective (A ⊓ Subgroup.centralizer (KG : Set G)).subtype
          (Subgroup.subtype_injective _) y
      have hℓ_pr : ℓ = p ∨ ℓ = r := by
        have h3 : ℓ ∣ Nat.card ↥A :=
          hℓ_dvd.trans (Subgroup.card_dvd_of_le inf_le_left)
        rw [hAcard] at h3
        rcases (Nat.Prime.dvd_mul hℓ_prime).mp h3 with h4 | h4
        · left
          obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
          rw [hk] at h4
          exact (Nat.prime_dvd_prime_iff_eq hℓ_prime hp).mp (hℓ_prime.dvd_of_dvd_pow h4)
        · right
          rw [hr_card] at h4
          exact (Nat.prime_dvd_prime_iff_eq hℓ_prime hr_prime).mp h4
      have hPG_le_A : (P.map H.subtype : Subgroup G) ≤ A := by
        rw [hAdef]; exact le_sup_left
      have hR₀_le_A : R₀ ≤ A := by
        rw [hAdef]; exact le_sup_right
      rcases hℓ_pr with hℓeq | hℓeq <;> rw [hℓeq] at hy_ordG
      · -- `ℓ = p`: `y ∈ P` via the normal Sylow `P ⊴ A`, then `(3.27)` kills it
        have hA_le_NPG : A ≤ Subgroup.normalizer
            ((P.map H.subtype : Subgroup G) : Set G) := by
          rw [hAdef]
          exact sup_le Subgroup.le_normalizer
            (fun g hg => mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hP_inv) (hR₀R hg))
        haveI hPGnormA : (((P.map H.subtype).subgroupOf A) : Subgroup ↥A).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer hA_le_NPG
        have hPGpos : 0 < Nat.card ↥(P.map H.subtype : Subgroup G) := Nat.card_pos
        have hquot_card : Nat.card
            (↥A ⧸ (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) = r := by
          have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
            (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_A).toEquiv] at h2
          have h3 : Nat.card (↥A ⧸ (((P.map H.subtype).subgroupOf A) : Subgroup ↥A))
              * Nat.card ↥(P.map H.subtype : Subgroup G)
              = r * Nat.card ↥(P.map H.subtype : Subgroup G) := by
            rw [← h2, hAcard, hr_card, mul_comm]
          exact Nat.eq_of_mul_eq_mul_right hPGpos h3
        set yA : ↥A := ⟨(y : G), hyMem.1⟩ with hyAdef
        have hyA_ord : orderOf yA = p := by
          rw [← hy_ordG]
          exact (orderOf_injective A.subtype (Subgroup.subtype_injective A) yA).symm
        have himg : (QuotientGroup.mk' (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) yA
            = 1 := by
          have h4 : orderOf ((QuotientGroup.mk'
              (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) yA) ∣ p := by
            rw [← hyA_ord]
            exact orderOf_map_dvd _ _
          have h5 : orderOf ((QuotientGroup.mk'
              (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) yA) ∣ r := by
            rw [← hquot_card]
            exact orderOf_dvd_natCard _
          rcases (Nat.dvd_prime hp).mp h4 with h6 | h6
          · exact orderOf_eq_one_iff.mp h6
          · exfalso
            rw [h6] at h5
            exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp h5)
        have hyPG : (y : G) ∈ (P.map H.subtype : Subgroup G) := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at himg
          exact Subgroup.mem_subgroupOf.mp himg
        have hybot : (y : G) ∈ (P.map H.subtype : Subgroup G)
            ⊓ Subgroup.centralizer (KG : Set G) := ⟨hyPG, hyMem.2⟩
        rw [h327, Subgroup.mem_bot] at hybot
        rw [hybot, orderOf_one] at hy_ordG
        exact hp.one_lt.ne' hy_ordG.symm
      · -- `ℓ = r`: Sylow II inside `A` transfers `K`-centralizing from `⟨y⟩` to `R₀`
        haveI : Fact r.Prime := ⟨hr_prime⟩
        set yA : ↥A := ⟨(y : G), hyMem.1⟩ with hyAdef
        have hyA_ord : orderOf yA = r := by
          rw [← hy_ordG]
          exact (orderOf_injective A.subtype (Subgroup.subtype_injective A) yA).symm
        -- the `r`-part of `|A| = |P|·r` is `r¹`
        have hfact : (Nat.card ↥A).factorization r = 1 := by
          obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
          rw [hAcard, hk, hr_card, Nat.factorization_mul (pow_ne_zero k hp.ne_zero)
            hr_prime.ne_zero, Finsupp.add_apply, hp.factorization_pow,
            Finsupp.single_apply, if_neg hpr, hr_prime.factorization_self]
        have hYcard : Nat.card ↥(Subgroup.zpowers yA)
            = r ^ (Nat.card ↥A).factorization r := by
          rw [hfact, pow_one, Nat.card_zpowers, hyA_ord]
        have hRcard' : Nat.card ↥(R₀.subgroupOf A)
            = r ^ (Nat.card ↥A).factorization r := by
          rw [hfact, pow_one]
          exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_A).toEquiv).trans hr_card
        obtain ⟨a, ha⟩ := MulAction.exists_smul_eq ↥A
          (Sylow.ofCard (Subgroup.zpowers yA) hYcard)
          (Sylow.ofCard (R₀.subgroupOf A) hRcard')
        have ha2 : MulAut.conj a • (Subgroup.zpowers yA) = R₀.subgroupOf A := by
          have h2 := congrArg (fun S : Sylow r ↥A => (S : Subgroup ↥A)) ha
          simpa [Sylow.smul_def, Sylow.pointwise_smul_def, Sylow.coe_ofCard] using h2
        have hR₀cent : R₀ ≤ Subgroup.centralizer (KG : Set G) := by
          intro r₀ hr₀
          have hr₀A : r₀ ∈ A := hR₀_le_A hr₀
          have hr₀mem : (⟨r₀, hr₀A⟩ : ↥A) ∈ MulAut.conj a • (Subgroup.zpowers yA) := by
            rw [ha2]
            exact Subgroup.mem_subgroupOf.mpr hr₀
          rw [Subgroup.mem_smul_pointwise_iff_exists] at hr₀mem
          obtain ⟨s, hs, hseq⟩ := hr₀mem
          have hsC : (s : G) ∈ Subgroup.centralizer (KG : Set G) := by
            obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hs
            have h3 : (s : G) = (y : G) ^ n := by
              rw [← hn, Subgroup.coe_zpow]
            rw [h3]
            exact Subgroup.zpow_mem _ hyMem.2 n
          have hseq2 : r₀ = (a : G) * (s : G) * (a : G)⁻¹ := by
            have h4 := congrArg Subtype.val hseq
            simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul,
              Subgroup.coe_inv] at h4
            exact h4.symm
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          have hk2 : (a : G)⁻¹ * k * (a : G) ∈ KG := by
            have h5 : (a : G)⁻¹ ∈ Subgroup.normalizer (KG : Set G) :=
              hA_le_N (A.inv_mem a.2)
            rw [Subgroup.mem_normalizer_iff] at h5
            have h6 := (h5 k).mp hk
            rwa [inv_inv] at h6
          have h7 := Subgroup.mem_centralizer_iff.mp hsC _ hk2
          rw [hseq2]
          calc k * ((a : G) * (s : G) * (a : G)⁻¹)
              = (a : G) * ((a : G)⁻¹ * k * (a : G) * (s : G)) * (a : G)⁻¹ := by group
            _ = (a : G) * ((s : G) * ((a : G)⁻¹ * k * (a : G))) * (a : G)⁻¹ := by rw [h7]
            _ = ((a : G) * (s : G) * (a : G)⁻¹) * k := by group
        apply h317
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (Subgroup.mem_centralizer_iff.mp (hR₀cent hg) k hk).symm
    -- ===== (3.29) `C_A(K/K') = ⊥` =====
    -- `K' := [K,K]` is characteristic in `K`, so the conjugation action of `A = P·R₀`
    -- descends to `K/K'`.  If `a ∈ A` acts trivially there then — since `K' = Φ(K)` (`K` is
    -- special, (3.25)) — Theorem 1.8 upgrades this to trivial action on `K` itself, and
    -- (3.28) gives `a = 1`.
    haveI : Fact q.Prime := ⟨hq_prime⟩
    have hq_ndvd_A : ¬ q ∣ Nat.card ↥A := by
      rw [hAcard]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hq_prime).mp hdvd with h4 | h4
      · obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
        rw [hk] at h4
        exact hq_ne_p
          ((Nat.prime_dvd_prime_iff_eq hq_prime hp).mp (hq_prime.dvd_of_dvd_pow h4))
      · rw [hr_card] at h4
        exact hq_ne_r ((Nat.prime_dvd_prime_iff_eq hq_prime hr_prime).mp h4)
    -- `K` special ⟹ `K' = Φ(K)` (in the elementary abelian branch both are `⊥`)
    have hK'Φ : commutator ↥KG = _root_.frattini ↥KG := by
      rcases hK_special.2 with hEA | ⟨hcomm, hfrat, _⟩
      · have hc : commutator ↥KG = ⊥ := by
          rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x _
          rw [Subgroup.mem_centralizer_iff]
          intro m _
          exact hEA.1 m x
        have hf : _root_.frattini ↥KG = ⊥ :=
          (OddOrder.BG.Ch1.S01.frattini_eq_bot_iff_isElementaryAbelian hKGq).mpr hEA
        rw [hc, hf]
      · rw [hcomm, hfrat]
    -- pin the `Normal` instance locally: with `IsMulCommutative (K/K')` in scope below, the
    -- bare search wanders into `Subgroup.normal_of_comm` (`CommGroup ↥KG`) and times out
    haveI hK'norm : (commutator ↥KG).Normal := inferInstance
    have hK'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φA (commutator ↥KG) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φA
    set φAQ : ↥A →* MulAut (↥KG ⧸ commutator ↥KG) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hK'_inv
      with hφAQ
    have h329 : ∀ a : ↥A,
        (∀ kq : ↥KG ⧸ commutator ↥KG, φAQ a kq = kq) → a = 1 := by
      intro a ha
      have ha1 : φAQ a = 1 := by
        ext kq
        exact ha kq
      have hcop : Nat.Coprime (orderOf (φA a)) q := by
        have h1 : orderOf (φA a) ∣ Nat.card ↥A :=
          (orderOf_map_dvd φA a).trans (orderOf_dvd_natCard a)
        exact (hq_prime.coprime_iff_not_dvd.mpr fun hdvd => hq_ndvd_A (hdvd.trans h1)).symm
      have htriv : ∀ z : ℤ, ∀ k : ↥KG,
          ∃ x ∈ _root_.frattini ↥KG, ((φA a) ^ z) k = k * x := by
        intro z k
        have h1 : φAQ (a ^ z) = 1 := by rw [map_zpow, ha1, one_zpow]
        have h2 : ((φA (a ^ z) k : ↥KG) : ↥KG ⧸ commutator ↥KG)
            = ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by
          have h3 := DFunLike.congr_fun h1 ((k : ↥KG) : ↥KG ⧸ commutator ↥KG)
          rw [MulAut.one_apply, hφAQ,
            OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply] at h3
          exact h3
        have h4 : k⁻¹ * (φA (a ^ z)) k ∈ commutator ↥KG := QuotientGroup.eq.mp h2.symm
        refine ⟨k⁻¹ * (φA (a ^ z)) k, hK'Φ ▸ h4, ?_⟩
        rw [← map_zpow]
        exact (mul_inv_cancel_left _ _).symm
      have hφA1 : φA a = 1 :=
        OddOrder.BG.Ch1.S01.mulAut_eq_one_of_coprime_orderOf_of_frattini hKGq (φA a)
          hcop htriv
      have haC : (a : G) ∈ Subgroup.centralizer (KG : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 := DFunLike.congr_fun hφA1 ⟨m, hm⟩
        rw [MulAut.one_apply] at h1
        have h2 : (a : G) * m * (a : G)⁻¹ = m := congrArg Subtype.val h1
        exact (mul_inv_eq_iff_eq_mul.mp h2).symm
      have habot : (a : G) ∈ A ⊓ Subgroup.centralizer (KG : Set G) := ⟨a.2, haC⟩
      rw [h328, Subgroup.mem_bot] at habot
      exact Subtype.ext habot
    -- ===== (3.30) `C_{K/K'}(R₀) ≠ 1`, i.e. `C_K(R₀) ⊄ K'` =====
    -- Otherwise `A = P·R₀` acts faithfully ((3.29)) on the `𝔽_q`-vector space `K/K'` with
    -- `C_{K/K'}(R₀) = 0`, so Theorem 3.4 (second use) makes `⁅R₀,P⁆ = ⊥`; but `⁅P,R₀⁆ = P`
    -- ((3.21)) then forces `P = ⊥`, contradicting `⁅K,P⁆ ≠ ⊥` ((3.13)).
    have hPG_le_A : (P.map H.subtype : Subgroup G) ≤ A := by
      rw [hAdef]; exact le_sup_left
    have hR₀_le_A : R₀ ≤ A := by
      rw [hAdef]; exact le_sup_right
    have hR₀cardA : Nat.card ↥(R₀.subgroupOf A) = r :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_A).toEquiv).trans hr_card
    -- `K/K'` is abelian (shared by (3.30) and the Proposition 1.6(d) step at (3.32))
    have hQbar_mul_comm : ∀ a b : ↥KG ⧸ commutator ↥KG, a * b = b * a := by
      intro a b
      refine QuotientGroup.induction_on a fun x => ?_
      refine QuotientGroup.induction_on b fun y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hc : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def, mul_inv_rev, inv_inv, inv_inv]
        exact (mul_assoc _ y x).symm
      rw [hc, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h330 : ¬ ((KG ⊓ Subgroup.centralizer (R₀ : Set G)) ≤ ⁅KG, KG⁆) := by
      intro hsub
      -- `K/K'` as a `ZMod q`-module
      haveI hQbar_comm : IsMulCommutative (↥KG ⧸ commutator ↥KG) := ⟨⟨hQbar_mul_comm⟩⟩
      have hexpQ : ∀ g : ↥KG ⧸ commutator ↥KG, g ^ q = 1 := by
        intro g
        refine QuotientGroup.induction_on g fun k => ?_
        have hk : k ^ q = 1 := by
          rw [← hK_exp]
          exact Monoid.pow_exponent_eq_one k
        rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
      have hqsmul : ∀ x : Additive (↥KG ⧸ commutator ↥KG), (q : ℕ) • x = 0 := by
        intro x
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact hexpQ x.toMul
      haveI hQmod : Module (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        AddCommGroup.zmodModule hqsmul
      haveI : Module.Finite (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        Module.Finite.of_finite
      set ρ : Representation (ZMod q) ↥A (Additive (↥KG ⧸ commutator ↥KG)) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd (↥KG ⧸ commutator ↥KG) q).comp φAQ
        with hρdef
      have hρ_apply : ∀ (g : ↥A) (x : Additive (↥KG ⧸ commutator ↥KG)),
          ρ g x = Additive.ofMul (φAQ g (Additive.toMul x)) := by
        intro g x
        rfl
      -- `P_G` is a normal Hall subgroup of `A` with complement `R₀`
      have hA_le_NPG : A ≤ Subgroup.normalizer
          ((P.map H.subtype : Subgroup G) : Set G) := by
        rw [hAdef]
        exact sup_le Subgroup.le_normalizer
          (fun g hg => mem_normalizer_map_subtype_of_isAInvariant (hφ ▸ hP_inv) (hR₀R hg))
      haveI hPGnormA : (((P.map H.subtype).subgroupOf A) : Subgroup ↥A).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hA_le_NPG
      have hPGcardA : Nat.card ↥((P.map H.subtype).subgroupOf A)
          = Nat.card ↥(P.map H.subtype : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_A).toEquiv
      have hdisjPR : Disjoint (P.map H.subtype : Subgroup G) R₀ :=
        hcompl.disjoint.mono (Subgroup.map_subtype_le P) hR₀R
      have hcomplA : Subgroup.IsComplement'
          ((P.map H.subtype).subgroupOf A) (R₀.subgroupOf A) := by
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
        · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
          rw [Subgroup.mem_inf] at hx
          simp only [Subgroup.mem_subgroupOf] at hx
          have hmem : (x : G) ∈ (P.map H.subtype : Subgroup G) ⊓ R₀ := ⟨hx.1, hx.2⟩
          rw [hdisjPR.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]
          exact Subtype.ext (by simpa using hmem)
        · have hsup : (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)
              ⊔ (R₀.subgroupOf A) = ⊤ := by
            rw [← Subgroup.subgroupOf_sup hPG_le_A hR₀_le_A, ← hAdef,
              Subgroup.subgroupOf_self]
          have hmul := Subgroup.normal_mul
            (((P.map H.subtype).subgroupOf A) : Subgroup ↥A) (R₀.subgroupOf A)
          rw [hsup, Subgroup.coe_top] at hmul
          exact hmul.symm
      have hHallA : Nat.Coprime (Nat.card ↥((P.map H.subtype).subgroupOf A))
          (Nat.card ↥(R₀.subgroupOf A)) := by
        rw [hPGcardA, hR₀cardA]
        obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_left k ((Nat.coprime_primes hp hr_prime).mpr hpr)
      have hodd_A : Odd (Nat.card ↥A) := by
        obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card A
        rw [hm, Nat.odd_mul] at hodd
        exact hodd.1
      have hcharA : (Nat.card ↥A : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact hq_ndvd_A
      -- `C_{K/K'}(R₀) = 0`: a fixed vector lifts to `C_K(R₀)` (coprime action), lands in
      -- `K'` by `hsub`, hence dies in the quotient
      have hCV : ∀ v : Additive (↥KG ⧸ commutator ↥KG),
          (∀ rr : ↥(R₀.subgroupOf A), ρ ((rr : ↥A)) v = v) → v = 0 := by
        intro v hv
        obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
        have hfix : ∀ rr : ↥(R₀.subgroupOf A), ∃ n ∈ commutator ↥KG,
            (φA.comp (R₀.subgroupOf A).subtype) rr k = k * n := by
          intro rr
          have h1 := hv rr
          rw [hρ_apply] at h1
          have h2 : φAQ (rr : ↥A) (Additive.toMul v) = Additive.toMul v := by
            have h3 := congrArg Additive.toMul h1
            rwa [toMul_ofMul] at h3
          rw [← hk, hφAQ,
            OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply] at h2
          refine ⟨k⁻¹ * (φA (rr : ↥A)) k, QuotientGroup.eq.mp h2.symm, ?_⟩
          exact (mul_inv_cancel_left _ _).symm
        have hcopRK : Nat.Coprime (Nat.card ↥(R₀.subgroupOf A)) (Nat.card ↥KG) := by
          rw [hR₀cardA]
          obtain ⟨m, hm⟩ := hKGq.exists_card_eq
          rw [hm]
          exact Nat.Coprime.pow_right m
            ((Nat.coprime_primes hr_prime hq_prime).mpr (Ne.symm hq_ne_r))
        have hN_inv' : OddOrder.Isaacs.Ch03.IsAInvariant
            (φA.comp (R₀.subgroupOf A).subtype) (commutator ↥KG) :=
          OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic _
        obtain ⟨c, hc_fix, n, hn, hceq⟩ :=
          OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hcopRK (Or.inr inferInstance)
            hN_inv' hfix
        -- `c ∈ C_K(R₀)`, so `c ∈ K'` by `hsub`; but `c ≡ k mod K'`, so `v = 0`
        have hcC : (c : G) ∈ KG ⊓ Subgroup.centralizer (R₀ : Set G) := by
          refine Subgroup.mem_inf.mpr
            ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
          have hmA : m ∈ A := hR₀_le_A hm
          have h5 := hc_fix ⟨⟨m, hmA⟩, Subgroup.mem_subgroupOf.mpr hm⟩
          have h6 : m * (c : G) * m⁻¹ = (c : G) := congrArg Subtype.val h5
          exact mul_inv_eq_iff_eq_mul.mp h6
        have hcK' : c ∈ commutator ↥KG := by
          have h7 : (c : G) ∈ ⁅KG, KG⁆ := hsub hcC
          have hKGder : (commutator ↥KG).map KG.subtype = ⁅KG, KG⁆ := by
            rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
              Subgroup.range_subtype]
          have h8 : (c : G) ∈ (commutator ↥KG).map KG.subtype := hKGder.symm ▸ h7
          obtain ⟨c', hc', heq⟩ := h8
          rwa [show c' = c from Subtype.ext heq] at hc'
        have hmkc : ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 := by
          have h9 : ((k : ↥KG) : ↥KG ⧸ commutator ↥KG)
              = ((c : ↥KG) : ↥KG ⧸ commutator ↥KG) := by
            rw [QuotientGroup.eq, hceq, inv_mul_cancel_left]
            exact hn
          rw [h9, QuotientGroup.eq_one_iff]
          exact hcK'
        rw [← ofMul_toMul v, ← hk, hmkc, ofMul_one]
      have hthm34 := S03d.thm34 ρ ((P.map H.subtype).subgroupOf A) (R₀.subgroupOf A)
        hcomplA hHallA ⟨r, hr_prime, hR₀cardA⟩ hodd_A hcharA hCV
      -- `⁅R₀,P⁆` acts trivially on `K/K'`, hence is trivial by (3.29)
      have hcomm_bot : (⁅R₀, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hsub2 : (⁅R₀, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≤ A := by
          rw [Subgroup.commutator_le]
          intro g₁ hg₁ g₂ hg₂
          have h1 : g₁ ∈ A := hR₀_le_A hg₁
          have h2 : g₂ ∈ A := hPG_le_A hg₂
          rw [commutatorElement_def]
          exact A.mul_mem (A.mul_mem (A.mul_mem h1 h2) (A.inv_mem h1)) (A.inv_mem h2)
        have hxA : x ∈ A := hsub2 hx
        have hmapeq : (⁅(R₀.subgroupOf A : Subgroup ↥A), (P.map H.subtype).subgroupOf A⁆
            : Subgroup ↥A).map A.subtype = ⁅R₀, (P.map H.subtype : Subgroup G)⁆ := by
          rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR₀_le_A,
            inf_eq_left.mpr hPG_le_A]
        have hx' : (⟨x, hxA⟩ : ↥A) ∈ (⁅(R₀.subgroupOf A : Subgroup ↥A),
            (P.map H.subtype).subgroupOf A⁆ : Subgroup ↥A) := by
          have hmem : x ∈ (⁅(R₀.subgroupOf A : Subgroup ↥A),
              (P.map H.subtype).subgroupOf A⁆ : Subgroup ↥A).map A.subtype :=
            hmapeq.symm ▸ hx
          obtain ⟨z, hz, hzx⟩ := hmem
          rwa [show z = ⟨x, hxA⟩ from Subtype.ext hzx] at hz
        have hρ1 : ρ ⟨x, hxA⟩ = 1 := hthm34 _ hx'
        have hone : (⟨x, hxA⟩ : ↥A) = 1 := by
          refine h329 _ fun kq => ?_
          have h1 := DFunLike.congr_fun hρ1 (Additive.ofMul kq)
          rw [hρ_apply, Module.End.one_apply] at h1
          exact Additive.ofMul.injective h1
        rw [Subgroup.mem_bot]
        have h10 := congrArg Subtype.val hone
        simpa using h10
      have hPGbot : (P.map H.subtype : Subgroup G) = ⊥ := by
        rw [← h321G, Subgroup.commutator_comm]
        exact hcomm_bot
      apply h313G
      rw [hPGbot, Subgroup.commutator_bot_right]
    -- ===== (3.31) `|C_K(R₀)| = q` and `C_K(R₀) ⊓ K' = ⊥` =====
    -- `C_K(R₀)` is a nontrivial ((3.30)) subgroup of exponent `q` ((3.26)) inside the
    -- `Z`-group `C_H(R₀)`, hence has order exactly `q`; being of prime order and not
    -- contained in `K'`, it meets `K'` trivially.
    have hCKR_ne_bot : KG ⊓ Subgroup.centralizer (R₀ : Set G) ≠ ⊥ := by
      intro hbot
      apply h330
      rw [hbot]
      exact bot_le
    have h331a : Nat.card ↥(KG ⊓ Subgroup.centralizer (R₀ : Set G)) = q := by
      refine card_eq_prime_of_le_isZGroup hZ
        (inf_le_inf_right _ (Subgroup.map_subtype_le K)) hq_prime ?_ hCKR_ne_bot
      intro x hx
      obtain ⟨hxK, _⟩ := Subgroup.mem_inf.mp hx
      have h1 : (⟨x, hxK⟩ : ↥KG) ^ q = 1 := by
        rw [← hK_exp]
        exact Monoid.pow_exponent_eq_one _
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    have h331b : (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆ = ⊥ := by
      by_contra hne
      have hdvd : Nat.card ↥((KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆) ∣ q :=
        h331a ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hq_prime).mp hdvd with h1 | h1
      · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
      · refine h330 ?_
        have heq : (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆
            = KG ⊓ Subgroup.centralizer (R₀ : Set G) :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (h331a.trans h1.symm))
        exact heq ▸ inf_le_right
    -- ===== (3.32)+(3.33) `K ≠ ⁅K,R₀⁆` and `C_{⁅K,R₀⁆}(R₀) = ⊥` =====
    -- Proposition 1.6(d) on the abelian quotient `K/K'`: the `R₀`-fixed points and the
    -- action commutator intersect trivially, so `C_K(R₀) ∩ ⁅K,R₀⁆ ≤ K'`.  With (3.31) the
    -- intersection is then trivial; and `⁅K,R₀⁆ = K` would put the whole order-`q` group
    -- `C_K(R₀)` inside `K'`, contradicting (3.30).
    have hbridge : ∀ x ∈ (⁅KG, R₀⁆ : Subgroup G), ∃ hxK : x ∈ KG,
        ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) ∈
          OddOrder.Isaacs.Ch04.actionCommutator
            (φAQ.comp (R₀.subgroupOf A).subtype) := by
      intro x hx
      rw [Subgroup.commutator_def] at hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy
        have hg₂A : g₂ ∈ A := hR₀_le_A hg₂
        have hyK : ⁅g₁, g₂⁆ ∈ KG := by
          rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
          refine KG.mul_mem hg₁ ?_
          exact (Subgroup.mem_normalizer_iff.mp (hR₀_le_NKG hg₂) g₁⁻¹).mp (KG.inv_mem hg₁)
        refine ⟨hyK, Subgroup.subset_closure ?_⟩
        refine ⟨((⟨g₁, hg₁⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG),
          ⟨⟨g₂, hg₂A⟩, Subgroup.mem_subgroupOf.mpr hg₂⟩, ?_⟩
        have hval : (⟨⁅g₁, g₂⁆, hyK⟩ : ↥KG)
            = ⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ := by
          apply Subtype.ext
          have h1 : ((φA ⟨g₂, hg₂A⟩ ((⟨g₁, hg₁⟩ : ↥KG)⁻¹) : ↥KG) : G)
              = g₂ * g₁⁻¹ * g₂⁻¹ := hφA_val _ _
          show ⁅g₁, g₂⁆
            = ((⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ : ↥KG) : G)
          rw [Subgroup.coe_mul, h1, commutatorElement_def,
            mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
        rw [hval]
        rfl
      | one =>
        exact ⟨KG.one_mem, by
          rw [show (⟨(1 : G), KG.one_mem⟩ : ↥KG) = 1 from rfl, QuotientGroup.mk_one]
          exact Subgroup.one_mem _⟩
      | mul y z hy hz ihy ihz =>
        obtain ⟨hyK, hyAC⟩ := ihy
        obtain ⟨hzK, hzAC⟩ := ihz
        refine ⟨KG.mul_mem hyK hzK, ?_⟩
        rw [show (⟨y * z, KG.mul_mem hyK hzK⟩ : ↥KG) = ⟨y, hyK⟩ * ⟨z, hzK⟩ from rfl,
          QuotientGroup.mk_mul]
        exact Subgroup.mul_mem _ hyAC hzAC
      | inv y hy ihy =>
        obtain ⟨hyK, hyAC⟩ := ihy
        refine ⟨KG.inv_mem hyK, ?_⟩
        rw [show (⟨y⁻¹, KG.inv_mem hyK⟩ : ↥KG) = (⟨y, hyK⟩ : ↥KG)⁻¹ from rfl,
          QuotientGroup.mk_inv]
        exact Subgroup.inv_mem _ hyAC
    -- Proposition 1.6(d) core: `C_K(R₀) ∩ ⁅K,R₀⁆ ≤ K'`
    have hCcap : (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ (⁅KG, R₀⁆ : Subgroup G)
        ≤ ⁅KG, KG⁆ := by
      letI : CommGroup (↥KG ⧸ commutator ↥KG) :=
        { (inferInstance : Group (↥KG ⧸ commutator ↥KG)) with mul_comm := hQbar_mul_comm }
      have hCop16 : Nat.Coprime (Nat.card ↥(R₀.subgroupOf A))
          (Nat.card (↥KG ⧸ commutator ↥KG)) := by
        rw [hR₀cardA]
        have hdvd : Nat.card (↥KG ⧸ commutator ↥KG) ∣ Nat.card ↥KG :=
          ⟨Nat.card ↥(commutator ↥KG),
            Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥KG)⟩
        refine Nat.Coprime.coprime_dvd_right hdvd ?_
        obtain ⟨m, hm⟩ := hKGq.exists_card_eq
        rw [hm]
        exact Nat.Coprime.pow_right m
          ((Nat.coprime_primes hr_prime hq_prime).mpr (Ne.symm hq_ne_r))
      have hcompl16 :=
        OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian
          (φ := φAQ.comp (R₀.subgroupOf A).subtype) hCop16
      intro x hx
      obtain ⟨hxKC, hxKR⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxKG, hxC⟩ := Subgroup.mem_inf.mp hxKC
      obtain ⟨hxK, hxAC⟩ := hbridge x hxKR
      have hxFP : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
          ∈ Subgroup.fixedPointsOfMulAut (φAQ.comp (R₀.subgroupOf A).subtype) := by
        rw [Subgroup.mem_fixedPointsOfMulAut]
        intro rr
        have h2 := Subgroup.mem_centralizer_iff.mp hxC ((rr : ↥A) : G)
          (Subgroup.mem_subgroupOf.mp rr.2)
        have h1 : φA (rr : ↥A) ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
          apply Subtype.ext
          have h1val : ((φA (rr : ↥A) ⟨x, hxK⟩ : ↥KG) : G)
              = ((rr : ↥A) : G) * x * ((rr : ↥A) : G)⁻¹ := hφA_val _ _
          rw [h1val]
          exact mul_inv_eq_iff_eq_mul.mpr h2
        show ((φA (rr : ↥A) ⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
          = ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
        rw [h1]
      have h3 : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 := by
        have h4 : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
            ∈ Subgroup.fixedPointsOfMulAut (φAQ.comp (R₀.subgroupOf A).subtype)
              ⊓ OddOrder.Isaacs.Ch04.actionCommutator
                (φAQ.comp (R₀.subgroupOf A).subtype) := ⟨hxFP, hxAC⟩
        rwa [hcompl16.disjoint.eq_bot, Subgroup.mem_bot] at h4
      have hxK' : (⟨x, hxK⟩ : ↥KG) ∈ commutator ↥KG := by
        rwa [QuotientGroup.eq_one_iff] at h3
      have hKGder : (commutator ↥KG).map KG.subtype = ⁅KG, KG⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      exact hKGder ▸ ⟨⟨x, hxK⟩, hxK', rfl⟩
    -- **(3.32)** `⁅K,R₀⁆ ≠ K`
    have h332 : (⁅KG, R₀⁆ : Subgroup G) ≠ KG := by
      intro heq
      apply h330
      intro x hx
      refine hCcap (Subgroup.mem_inf.mpr ⟨hx, ?_⟩)
      rw [heq]
      exact (Subgroup.mem_inf.mp hx).1
    -- **(3.33)** `C_{⁅K,R₀⁆}(R₀) = ⊥`
    have h333 : (⁅KG, R₀⁆ : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxKR, hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxK, _⟩ := hbridge x hxKR
      have h1 : x ∈ (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆ :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxK, hxC⟩,
          hCcap (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxK, hxC⟩, hxKR⟩)⟩
      rwa [h331b] at h1
    -- ===== (3.34) `⁅K,R₀⁆` is abelian (Lemma 3.1 + **Theorem 3.5**) =====
    -- `T := ⁅K,R₀⁆·R₀` is a Frobenius group: the prime-order complement `R₀` acts without
    -- nontrivial fixed points on the kernel ((3.33)).  `T ≤ S₁` acts faithfully on `V`
    -- ((3.18)) and `dim C_V(R₀) = 1` ((3.19)), so Theorem 3.5 makes the derived subgroup
    -- of `⁅K,R₀⁆` act trivially on `V`, hence vanish.
    have hKR_le_KG : (⁅KG, R₀⁆ : Subgroup G) ≤ KG := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
      exact KG.mul_mem hg₁
        ((Subgroup.mem_normalizer_iff.mp (hR₀_le_NKG hg₂) g₁⁻¹).mp (KG.inv_mem hg₁))
    set T : Subgroup G := (⁅KG, R₀⁆ : Subgroup G) ⊔ R₀ with hTdef
    have hKR_le_T : (⁅KG, R₀⁆ : Subgroup G) ≤ T := le_sup_left
    have hR₀_le_T : R₀ ≤ T := le_sup_right
    have hT_le_NKR : T ≤ Subgroup.normalizer ((⁅KG, R₀⁆ : Subgroup G) : Set G) := by
      rw [hTdef]
      exact sup_le Subgroup.le_normalizer
        (OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self_right KG R₀)
    haveI hKRnormT : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hT_le_NKR
    have hT_le_S₁ : T ≤ S₁ := by
      rw [hTdef]
      exact sup_le (hKR_le_KG.trans hKG_le_S₁) hR₀_le_S₁
    have hdisjT : Disjoint (⁅KG, R₀⁆ : Subgroup G) R₀ := hdisjKR.mono_left hKR_le_KG
    have hR₀cardT : Nat.card ↥(R₀.subgroupOf T) = r :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_T).toEquiv).trans hr_card
    have hcomplT : Subgroup.IsComplement'
        ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) (R₀.subgroupOf T) := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
        rw [Subgroup.mem_inf] at hx
        simp only [Subgroup.mem_subgroupOf] at hx
        have hmem : (x : G) ∈ (⁅KG, R₀⁆ : Subgroup G) ⊓ R₀ := ⟨hx.1, hx.2⟩
        rw [hdisjT.eq_bot, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]
        exact Subtype.ext (by simpa using hmem)
      · have hsup : (((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) : Subgroup ↥T)
            ⊔ (R₀.subgroupOf T) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hKR_le_T hR₀_le_T, ← hTdef,
            Subgroup.subgroupOf_self]
        have hmul := Subgroup.normal_mul
          (((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) : Subgroup ↥T) (R₀.subgroupOf T)
        rw [hsup, Subgroup.coe_top] at hmul
        exact hmul.symm
    have hKR_ne_bot : (⁅KG, R₀⁆ : Subgroup G) ≠ ⊥ := by
      intro hbot
      exact h317 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hKRT_ne_bot : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) ≠ ⊥ := by
      intro hbot
      have h2 : (⁅KG, R₀⁆ : Subgroup G) ⊓ T = ⊥ := by
        rw [← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
      rw [inf_eq_left.mpr hKR_le_T] at h2
      exact hKR_ne_bot h2
    have hFixT : ∀ k ∈ ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T),
        (∀ s ∈ R₀.subgroupOf T, s * k * s⁻¹ = k) → k = 1 := by
      intro k hk hfix
      have hkKR : (k : G) ∈ (⁅KG, R₀⁆ : Subgroup G) := Subgroup.mem_subgroupOf.mp hk
      have hkC : (k : G) ∈ Subgroup.centralizer (R₀ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 := hfix ⟨m, hR₀_le_T hm⟩ (Subgroup.mem_subgroupOf.mpr hm)
        have h2 : m * (k : G) * m⁻¹ = (k : G) := congrArg Subtype.val h1
        exact mul_inv_eq_iff_eq_mul.mp h2
      have h3 : (k : G) ∈ (⁅KG, R₀⁆ : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) :=
        ⟨hkKR, hkC⟩
      rw [h333, Subgroup.mem_bot] at h3
      exact Subtype.ext h3
    have hrTprime : (Nat.card ↥(R₀.subgroupOf T)).Prime := by
      rw [hR₀cardT]
      exact hr_prime
    have hFrobT := S03d.isFrobeniusGroup_of_prime_complement_fixedFree
      hcomplT hrTprime hKRT_ne_bot hFixT
    -- the conjugation representation of `T` on the `𝔽_p`-space `V_G` ((3.19) pattern)
    haveI hVGcommT : IsMulCommutative ↥VG := ⟨⟨fun a b => hVGelem.1 a b⟩⟩
    have hpsmulT : ∀ x : Additive ↥VG, (p : ℕ) • x = 0 := by
      intro x
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact hVGelem.2 x.toMul
    haveI hVGmodT : Module (ZMod p) (Additive ↥VG) := AddCommGroup.zmodModule hpsmulT
    haveI : Module.Finite (ZMod p) (Additive ↥VG) := Module.Finite.of_finite
    set ρT : Representation (ZMod p) ↥T (Additive ↥VG) :=
      (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥VG p).comp
        ((MulAut.conjNormal (G := G) (H := VG)).comp T.subtype) with hρT
    have hρT_apply : ∀ (g : ↥T) (x : Additive ↥VG),
        ρT g x = Additive.ofMul (MulAut.conjNormal (H := VG) (g : G) (Additive.toMul x)) := by
      intro g x
      rfl
    -- the `R₀`-invariants of `ρT` are exactly `C_{V_G}(R₀)`, of order `p` ((3.19)),
    -- hence one-dimensional
    have hmemiffT : ∀ v : Additive ↥VG,
        v ∈ Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)
          ↔ ((Additive.toMul v : ↥VG) : G) ∈ Subgroup.centralizer (R₀ : Set G) := by
      intro v
      rw [Representation.mem_invariants]
      constructor
      · intro hv
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 : Additive.ofMul (MulAut.conjNormal (H := VG) m (Additive.toMul v)) = v :=
          hv ⟨⟨m, hR₀_le_T hm⟩, Subgroup.mem_subgroupOf.mpr hm⟩
        have h2 := congrArg Additive.toMul h1
        rw [toMul_ofMul] at h2
        have h3 := congrArg Subtype.val h2
        rw [MulAut.conjNormal_apply] at h3
        exact mul_inv_eq_iff_eq_mul.mp h3
      · intro hc rr
        have h2 := Subgroup.mem_centralizer_iff.mp hc ((rr : ↥T) : G)
          (Subgroup.mem_subgroupOf.mp rr.2)
        show ρT ((rr : ↥T)) v = v
        rw [hρT_apply]
        apply Additive.toMul.injective
        rw [toMul_ofMul]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        exact mul_inv_eq_iff_eq_mul.mpr h2
    have hinv_card : Nat.card
        ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) = p := by
      refine (Nat.card_congr ((Equiv.subtypeEquiv (Additive.toMul (α := ↥VG))
        (q := fun w : ↥VG => (w : G) ∈ Subgroup.centralizer (R₀ : Set G))
        fun v => hmemiffT v).trans ?_)).trans h319
      exact ⟨fun w => ⟨(w.1 : G), Subgroup.mem_inf.mpr ⟨w.1.2, w.2⟩⟩,
        fun z => ⟨⟨(z : G), (Subgroup.mem_inf.mp z.2).1⟩, (Subgroup.mem_inf.mp z.2).2⟩,
        fun w => by apply Subtype.ext; apply Subtype.ext; rfl,
        fun z => by apply Subtype.ext; rfl⟩
    have hCV1T : Module.finrank (ZMod p)
        ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) = 1 := by
      haveI : Fintype ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) :=
        Fintype.ofFinite _
      have h2 : Nat.card
          ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype))
          = p ^ Module.finrank (ZMod p)
            ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) := by
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
      rw [hinv_card] at h2
      have h3 : p ^ 1 = p ^ Module.finrank (ZMod p)
          ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) := by
        rw [pow_one]
        exact h2
      exact (Nat.pow_right_injective hp.two_le h3).symm
    have hcharT : (Nat.card ↥T : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hcardT : Nat.card ↥T
          = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) * Nat.card ↥R₀ := by
        rw [hTdef]
        exact card_sup_of_le_normalizer_of_disjoint
          (fun g hg =>
            OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self_right KG R₀ hg)
          hdisjT
      rw [hcardT, hr_card] at hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h4 | h4
      · obtain ⟨m, hm⟩ := hKGq.exists_card_eq
        have h5 : p ∣ q ^ m := by
          rw [← hm]
          exact h4.trans (Subgroup.card_dvd_of_le hKR_le_KG)
        exact hq_ne_p
          ((Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow h5)).symm
      · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp h4)
    have hthm35 := S03e.thm35 ρT ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T)
      (R₀.subgroupOf T) hFrobT inferInstance ⟨r, hr_prime, hR₀cardT⟩ hcharT hCV1T
    -- push the conclusion down to `G`: `⁅⁅K,R₀⁆,⁅K,R₀⁆⁆` centralises `V`, hence dies ((3.18))
    have h334 : (⁅(⁅KG, R₀⁆ : Subgroup G), (⁅KG, R₀⁆ : Subgroup G)⁆ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hsubT : (⁅(⁅KG, R₀⁆ : Subgroup G), (⁅KG, R₀⁆ : Subgroup G)⁆ : Subgroup G)
          ≤ T := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h1 : g₁ ∈ T := hKR_le_T hg₁
        have h2 : g₂ ∈ T := hKR_le_T hg₂
        rw [commutatorElement_def]
        exact T.mul_mem (T.mul_mem (T.mul_mem h1 h2) (T.inv_mem h1)) (T.inv_mem h2)
      have hxT : x ∈ T := hsubT hx
      have hmapeqT : (⁅((⁅KG, R₀⁆ : Subgroup G).subgroupOf T : Subgroup ↥T),
          (⁅KG, R₀⁆ : Subgroup G).subgroupOf T⁆ : Subgroup ↥T).map T.subtype
          = ⁅(⁅KG, R₀⁆ : Subgroup G), (⁅KG, R₀⁆ : Subgroup G)⁆ := by
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hKR_le_T]
      have hx' : (⟨x, hxT⟩ : ↥T) ∈ (⁅((⁅KG, R₀⁆ : Subgroup G).subgroupOf T : Subgroup ↥T),
          (⁅KG, R₀⁆ : Subgroup G).subgroupOf T⁆ : Subgroup ↥T) := by
        have hmem : x ∈ (⁅((⁅KG, R₀⁆ : Subgroup G).subgroupOf T : Subgroup ↥T),
            (⁅KG, R₀⁆ : Subgroup G).subgroupOf T⁆ : Subgroup ↥T).map T.subtype :=
          hmapeqT.symm ▸ hx
        obtain ⟨z, hz, hzx⟩ := hmem
        rwa [show z = ⟨x, hxT⟩ from Subtype.ext hzx] at hz
      have hρ1 : ρT ⟨x, hxT⟩ = 1 := hthm35 _ hx'
      have hxc : x ∈ Subgroup.centralizer (VG : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hx1 := DFunLike.congr_fun hρ1 (Additive.ofMul (⟨y, hy⟩ : ↥VG))
        rw [hρT_apply, Module.End.one_apply] at hx1
        have hcoe := congrArg Subtype.val (Additive.ofMul.injective hx1)
        rw [MulAut.conjNormal_apply] at hcoe
        exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
      have hfin : x ∈ S₁ ⊓ Subgroup.centralizer (VG : Set G) := ⟨hT_le_S₁ hxT, hxc⟩
      rwa [h318] at hfin
    -- ===== (3.35) some `x ∈ P` moves `⁅K,R₀⁆` =====
    -- Otherwise `⁅K,R₀⁆` is a proper ((3.32)) `PR₀`-invariant subgroup of `K`, so `P`
    -- centralises it ((3.22)').  Its image in `K/K'` then lies in `C_{K/K'}(P)`, which is
    -- trivial: `K = ⁅K,P⁆` ((3.24)) makes the `P`-action commutator on `K/K'` everything,
    -- and Proposition 1.6(d) complements it against the fixed points.  Hence
    -- `⁅K,R₀⁆ ≤ K'`, so `R₀` acts trivially on `K/K'` and (3.29) kills `R₀` — absurd.
    -- (This route replaces BG's appeal to the second statement of (3.25) and Theorem 1.8.)
    have h335 : ∃ x ∈ (P.map H.subtype : Subgroup G),
        (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom ≠ ⁅KG, R₀⁆ := by
      by_contra hcon
      push Not at hcon
      have hPG_le_NKR : (P.map H.subtype : Subgroup G)
          ≤ Subgroup.normalizer ((⁅KG, R₀⁆ : Subgroup G) : Set G) := fun x hx =>
        mem_normalizer_of_map_conj_eq (hcon x hx)
      -- `P` centralises `⁅K,R₀⁆` by the unconditional (3.22)
      have hKRP_bot : (⁅(⁅KG, R₀⁆ : Subgroup G), (P.map H.subtype : Subgroup G)⁆
          : Subgroup G) = ⊥ :=
        h322' _ hKR_le_KG h332
          (fun g hg =>
            OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self_right KG R₀ hg)
          hPG_le_NKR
      -- the `P`-action commutator on `K/K'` is everything (`K = ⁅K,P⁆`, (3.24))
      have hbridgeP : ∀ x ∈ (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G),
          ∃ hxK : x ∈ KG,
          ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) ∈
            OddOrder.Isaacs.Ch04.actionCommutator
              (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) := by
        intro x hx
        rw [Subgroup.commutator_def] at hx
        induction hx using Subgroup.closure_induction with
        | mem y hy =>
          obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy
          have hg₂A : g₂ ∈ A := hPG_le_A hg₂
          have hyK : ⁅g₁, g₂⁆ ∈ KG := by
            rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
            refine KG.mul_mem hg₁ ?_
            exact (Subgroup.mem_normalizer_iff.mp (hPG_le_NKG hg₂) g₁⁻¹).mp
              (KG.inv_mem hg₁)
          refine ⟨hyK, Subgroup.subset_closure ?_⟩
          refine ⟨((⟨g₁, hg₁⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG),
            ⟨⟨g₂, hg₂A⟩, Subgroup.mem_subgroupOf.mpr hg₂⟩, ?_⟩
          have hval : (⟨⁅g₁, g₂⁆, hyK⟩ : ↥KG)
              = ⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ := by
            apply Subtype.ext
            have h1 : ((φA ⟨g₂, hg₂A⟩ ((⟨g₁, hg₁⟩ : ↥KG)⁻¹) : ↥KG) : G)
                = g₂ * g₁⁻¹ * g₂⁻¹ := hφA_val _ _
            show ⁅g₁, g₂⁆
              = ((⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ : ↥KG) : G)
            rw [Subgroup.coe_mul, h1, commutatorElement_def,
              mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
          rw [hval]
          rfl
        | one =>
          exact ⟨KG.one_mem, by
            rw [show (⟨(1 : G), KG.one_mem⟩ : ↥KG) = 1 from rfl, QuotientGroup.mk_one]
            exact Subgroup.one_mem _⟩
        | mul y z hy hz ihy ihz =>
          obtain ⟨hyK, hyAC⟩ := ihy
          obtain ⟨hzK, hzAC⟩ := ihz
          refine ⟨KG.mul_mem hyK hzK, ?_⟩
          rw [show (⟨y * z, KG.mul_mem hyK hzK⟩ : ↥KG) = ⟨y, hyK⟩ * ⟨z, hzK⟩ from rfl,
            QuotientGroup.mk_mul]
          exact Subgroup.mul_mem _ hyAC hzAC
        | inv y hy ihy =>
          obtain ⟨hyK, hyAC⟩ := ihy
          refine ⟨KG.inv_mem hyK, ?_⟩
          rw [show (⟨y⁻¹, KG.inv_mem hyK⟩ : ↥KG) = (⟨y, hyK⟩ : ↥KG)⁻¹ from rfl,
            QuotientGroup.mk_inv]
          exact Subgroup.inv_mem _ hyAC
      have hACP_top : OddOrder.Isaacs.Ch04.actionCommutator
          (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) = ⊤ := by
        rw [eq_top_iff]
        intro kq _
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kq
        have hkKR : (k : G) ∈ (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) := by
          rw [h324]
          exact k.2
        obtain ⟨hxK, hAC⟩ := hbridgeP _ hkKR
        rwa [show (⟨(k : G), hxK⟩ : ↥KG) = k from Subtype.ext rfl] at hAC
      have hFPP_bot : Subgroup.fixedPointsOfMulAut
          (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) = ⊥ := by
        letI : CommGroup (↥KG ⧸ commutator ↥KG) :=
          { (inferInstance : Group (↥KG ⧸ commutator ↥KG)) with
            mul_comm := hQbar_mul_comm }
        have hCopP : Nat.Coprime (Nat.card ↥((P.map H.subtype).subgroupOf A))
            (Nat.card (↥KG ⧸ commutator ↥KG)) := by
          have hdvd : Nat.card (↥KG ⧸ commutator ↥KG) ∣ Nat.card ↥KG :=
            ⟨Nat.card ↥(commutator ↥KG),
              Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥KG)⟩
          refine Nat.Coprime.coprime_dvd_right hdvd ?_
          have hPGcardA' : Nat.card ↥((P.map H.subtype).subgroupOf A)
              = Nat.card ↥(P.map H.subtype : Subgroup G) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_A).toEquiv
          obtain ⟨m, hm⟩ := hKGq.exists_card_eq
          obtain ⟨k2, hk2⟩ := (hPp.map H.subtype).exists_card_eq
          rw [hm, hPGcardA', hk2]
          exact Nat.Coprime.pow_left k2 (Nat.Coprime.pow_right m
            ((Nat.coprime_primes hp hq_prime).mpr (Ne.symm hq_ne_p)))
        have hcomplP :=
          OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian
            (φ := φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) hCopP
        rw [hACP_top] at hcomplP
        exact Subgroup.isComplement'_top_right.mp hcomplP
      -- `⁅K,R₀⁆` maps to `1` in `K/K'`
      have hKR_mk_one : ∀ x (_ : x ∈ (⁅KG, R₀⁆ : Subgroup G)) (hxK : x ∈ KG),
          ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 := by
        intro x hxKR hxK
        have hxcent : x ∈ Subgroup.centralizer
            ((P.map H.subtype : Subgroup G) : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKRP_bot hxKR
        have hxFPP : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
            ∈ Subgroup.fixedPointsOfMulAut
              (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) := by
          rw [Subgroup.mem_fixedPointsOfMulAut]
          intro pp
          have h2 := Subgroup.mem_centralizer_iff.mp hxcent ((pp : ↥A) : G)
            (Subgroup.mem_subgroupOf.mp pp.2)
          have h1 : φA (pp : ↥A) ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
            apply Subtype.ext
            have h1val : ((φA (pp : ↥A) ⟨x, hxK⟩ : ↥KG) : G)
                = ((pp : ↥A) : G) * x * ((pp : ↥A) : G)⁻¹ := hφA_val _ _
            rw [h1val]
            exact mul_inv_eq_iff_eq_mul.mpr h2
          show ((φA (pp : ↥A) ⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
            = ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
          rw [h1]
        have h3 : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) ∈ (⊥ : Subgroup _) := by
          rw [← hFPP_bot]
          exact hxFPP
        rwa [Subgroup.mem_bot] at h3
      -- `R₀` acts trivially on `K/K'`; (3.29) then forces `R₀ = ⊥`, absurd
      have hR₀bot : R₀ = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        rw [Subgroup.mem_bot]
        have haA : a ∈ A := hR₀_le_A ha
        have h1 : (⟨a, haA⟩ : ↥A) = 1 := by
          refine h329 _ fun kq => ?_
          obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kq
          have hwmem : ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : G) ∈ (⁅KG, R₀⁆ : Subgroup G) := by
            have hval2 : ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : G) = ⁅a, (k : G)⁆ := by
              rw [Subgroup.coe_mul]
              have h4 : ((φA ⟨a, haA⟩ k : ↥KG) : G) = a * (k : G) * a⁻¹ := hφA_val _ _
              rw [h4, Subgroup.coe_inv, commutatorElement_def]
            rw [hval2, Subgroup.commutator_comm]
            exact Subgroup.commutator_mem_commutator ha k.2
          have hw_one : ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 :=
            hKR_mk_one _ hwmem (φA ⟨a, haA⟩ k * k⁻¹ : ↥KG).2
          show ((φA ⟨a, haA⟩ k : ↥KG) : ↥KG ⧸ commutator ↥KG)
            = ((k : ↥KG) : ↥KG ⧸ commutator ↥KG)
          calc ((φA ⟨a, haA⟩ k : ↥KG) : ↥KG ⧸ commutator ↥KG)
              = (((φA ⟨a, haA⟩ k * k⁻¹) * k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by
                rw [inv_mul_cancel_right]
            _ = ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : ↥KG ⧸ commutator ↥KG)
                * ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by rw [QuotientGroup.mk_mul]
            _ = ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by rw [hw_one, one_mul]
        exact congrArg Subtype.val h1
      rw [hR₀bot, Subgroup.card_bot] at hr_card
      exact hr_prime.one_lt.ne' hr_card.symm
    -- ===== (3.36) `K` is elementary abelian =====
    -- Step 1: `|K| = |⁅K,R₀⁆|·q`.  Proposition 1.6(a) (the general coprime form
    -- `K = C_K(R₀)·⁅K,R₀⁆`) with the two factors intersecting trivially ((3.33));
    -- `|C_K(R₀)| = q` by (3.31).
    obtain ⟨x, hxPG, hx_ne⟩ := h335
    set φAR : ↥(R₀.subgroupOf A) →* MulAut ↥KG := φA.comp (R₀.subgroupOf A).subtype
      with hφARdef
    have hcopRK36 : Nat.Coprime (Nat.card ↥(R₀.subgroupOf A)) (Nat.card ↥KG) := by
      rw [hR₀cardA]
      obtain ⟨m, hm⟩ := hKGq.exists_card_eq
      rw [hm]
      exact Nat.Coprime.pow_right m
        ((Nat.coprime_primes hr_prime hq_prime).mpr (Ne.symm hq_ne_r))
    have hsupK : Subgroup.fixedPointsOfMulAut φAR
        ⊔ OddOrder.Isaacs.Ch04.actionCommutator φAR = ⊤ :=
      OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top hcopRK36
        (Or.inr inferInstance)
    -- the fixed points are `C_K(R₀)`
    have hFPval : Subgroup.fixedPointsOfMulAut φAR
        = (KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG := by
      ext w
      rw [Subgroup.mem_fixedPointsOfMulAut, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hw
        refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
        have hmA : m ∈ A := hR₀_le_A hm
        have h1 := hw ⟨⟨m, hmA⟩, Subgroup.mem_subgroupOf.mpr hm⟩
        have h2 : m * (w : G) * m⁻¹ = (w : G) := congrArg Subtype.val h1
        exact mul_inv_eq_iff_eq_mul.mp h2
      · rintro ⟨-, hwC⟩
        intro rr
        have h2 := Subgroup.mem_centralizer_iff.mp hwC ((rr : ↥A) : G)
          (Subgroup.mem_subgroupOf.mp rr.2)
        apply Subtype.ext
        have h1val : ((φAR rr w : ↥KG) : G)
            = ((rr : ↥A) : G) * (w : G) * ((rr : ↥A) : G)⁻¹ := hφA_val _ _
        rw [h1val]
        exact mul_inv_eq_iff_eq_mul.mpr h2
    -- the action commutator is `⁅K,R₀⁆`
    have hbridgeK : ∀ y ∈ (⁅KG, R₀⁆ : Subgroup G), ∃ hyK : y ∈ KG,
        (⟨y, hyK⟩ : ↥KG) ∈ OddOrder.Isaacs.Ch04.actionCommutator φAR := by
      intro y hy
      rw [Subgroup.commutator_def] at hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hz
        have hg₂A : g₂ ∈ A := hR₀_le_A hg₂
        have hzK : ⁅g₁, g₂⁆ ∈ KG := by
          rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
          refine KG.mul_mem hg₁ ?_
          exact (Subgroup.mem_normalizer_iff.mp (hR₀_le_NKG hg₂) g₁⁻¹).mp
            (KG.inv_mem hg₁)
        refine ⟨hzK, Subgroup.subset_closure ?_⟩
        refine ⟨⟨g₁, hg₁⟩, ⟨⟨g₂, hg₂A⟩, Subgroup.mem_subgroupOf.mpr hg₂⟩, ?_⟩
        apply Subtype.ext
        have h1 : ((φA ⟨g₂, hg₂A⟩ ((⟨g₁, hg₁⟩ : ↥KG)⁻¹) : ↥KG) : G)
            = g₂ * g₁⁻¹ * g₂⁻¹ := hφA_val _ _
        show ⁅g₁, g₂⁆
          = ((⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ : ↥KG) : G)
        rw [Subgroup.coe_mul, h1, commutatorElement_def,
          mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
      | one =>
        exact ⟨KG.one_mem, by
          rw [show (⟨(1 : G), KG.one_mem⟩ : ↥KG) = 1 from rfl]
          exact Subgroup.one_mem _⟩
      | mul y z hy hz ihy ihz =>
        obtain ⟨hyK, hyAC⟩ := ihy
        obtain ⟨hzK, hzAC⟩ := ihz
        refine ⟨KG.mul_mem hyK hzK, ?_⟩
        rw [show (⟨y * z, KG.mul_mem hyK hzK⟩ : ↥KG) = ⟨y, hyK⟩ * ⟨z, hzK⟩ from rfl]
        exact Subgroup.mul_mem _ hyAC hzAC
      | inv y hy ihy =>
        obtain ⟨hyK, hyAC⟩ := ihy
        refine ⟨KG.inv_mem hyK, ?_⟩
        rw [show (⟨y⁻¹, KG.inv_mem hyK⟩ : ↥KG) = (⟨y, hyK⟩ : ↥KG)⁻¹ from rfl]
        exact Subgroup.inv_mem _ hyAC
    have hACval : OddOrder.Isaacs.Ch04.actionCommutator φAR
        = (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG := by
      apply le_antisymm
      · rw [OddOrder.Isaacs.Ch04.actionCommutator, Subgroup.closure_le]
        rintro _ ⟨g, rr, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        have hval : ((g * (φAR rr) g⁻¹ : ↥KG) : G)
            = ⁅(g : G), ((rr : ↥A) : G)⁆ := by
          have h1 : (((φAR rr) g⁻¹ : ↥KG) : G)
              = ((rr : ↥A) : G) * (g : G)⁻¹ * ((rr : ↥A) : G)⁻¹ := hφA_val _ _
          rw [Subgroup.coe_mul, h1, commutatorElement_def,
            mul_assoc (g : G) (((rr : ↥A) : G)) (g : G)⁻¹, mul_assoc (g : G)]
        rw [hval]
        exact Subgroup.commutator_mem_commutator g.2 (Subgroup.mem_subgroupOf.mp rr.2)
      · intro w hw
        obtain ⟨hxK, hin⟩ := hbridgeK (w : G) (Subgroup.mem_subgroupOf.mp hw)
        rwa [show (⟨(w : G), hxK⟩ : ↥KG) = w from Subtype.ext rfl] at hin
    rw [hFPval, hACval, sup_comm] at hsupK
    -- the two factors intersect trivially ((3.33))
    have hdisjCK : Disjoint ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        ((KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG) := by
      rw [disjoint_iff, eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hw
      have h1 : (w : G) ∈ (⁅KG, R₀⁆ : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) :=
        ⟨hw.1, (Subgroup.mem_inf.mp hw.2).2⟩
      rw [h333, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact Subtype.ext h1
    -- `⁅K,R₀⁆ ⊴ K`
    have hKG_le_NKR : KG ≤ Subgroup.normalizer ((⁅KG, R₀⁆ : Subgroup G) : Set G) :=
      OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self KG R₀
    haveI hKRsnorm : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKG_le_NKR
    -- `|K| = |⁅K,R₀⁆|·q`
    have hCs_card : Nat.card ↥((KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG)
        = q :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans h331a
    have hKRs_card : Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKR_le_KG).toEquiv
    have hKGcard36 : Nat.card ↥KG
        = Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) * q := by
      have h2 := card_sup_of_le_normalizer_of_disjoint
        (A := (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        (B := (KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG)
        (by
          intro g _
          rw [Subgroup.normalizer_eq_top]
          trivial)
        hdisjCK
      rw [hsupK, hCs_card] at h2
      calc Nat.card ↥KG = Nat.card ↥(⊤ : Subgroup ↥KG) :=
            (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
        _ = _ := h2
    have hKRs_index : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG).index = q := by
      have h3 := Subgroup.index_mul_card ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
      rw [hKGcard36, mul_comm (Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)) q]
        at h3
      have hpos : 0 < Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos h3
    -- Step 2: the conjugate `⁅K,R₀⁆ˣ` is a second abelian normal subgroup of index `q`,
    -- distinct from `⁅K,R₀⁆` ((3.35)); together they generate `K` and their intersection
    -- is central, so `|K : Z(K)| ≤ q²`.
    set KRx : Subgroup G := (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom
      with hKRxdef
    have hKRx_le_KG : KRx ≤ KG := by
      rw [hKRxdef]
      have h1 : (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom
          ≤ KG.map (MulAut.conj x).toMonoidHom := Subgroup.map_mono hKR_le_KG
      rwa [map_conj_eq_self_of_mem_normalizer (hPG_le_NKG hxPG)] at h1
    have hKRx_card : Nat.card ↥KRx = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) := by
      rw [hKRxdef]
      exact Subgroup.card_map_of_injective (MulAut.conj x).injective
    have h334x : (⁅KRx, KRx⁆ : Subgroup G) = ⊥ := by
      rw [hKRxdef, ← Subgroup.map_commutator, h334, Subgroup.map_bot]
    -- composition law for conjugation maps
    have hcomp : ∀ a b : G,
        ((⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj b).toMonoidHom).map
          (MulAut.conj a).toMonoidHom
        = (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj (a * b)).toMonoidHom := by
      intro a b
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hKG_le_NKRx : KG ≤ Subgroup.normalizer (KRx : Set G) := by
      intro g hg
      have hy : x⁻¹ * g * x ∈ KG := by
        refine (Subgroup.mem_normalizer_iff.mp (hPG_le_NKG hxPG) (x⁻¹ * g * x)).mpr ?_
        have h2 : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rwa [h2]
      refine mem_normalizer_of_map_conj_eq ?_
      have hgx : g * x = x * (x⁻¹ * g * x) := by group
      calc KRx.map (MulAut.conj g).toMonoidHom
          = (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj (g * x)).toMonoidHom := by
            rw [hKRxdef, hcomp]
        _ = ((⁅KG, R₀⁆ : Subgroup G).map
              (MulAut.conj (x⁻¹ * g * x)).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
            rw [hgx, hcomp]
        _ = (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom := by
            rw [map_conj_eq_self_of_mem_normalizer (hKG_le_NKR hy)]
        _ = KRx := hKRxdef.symm
    haveI hKRxsnorm : (KRx.subgroupOf KG).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKG_le_NKRx
    have hKRxs_card : Nat.card ↥(KRx.subgroupOf KG)
        = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKRx_le_KG).toEquiv).trans hKRx_card
    have hKRxs_index : (KRx.subgroupOf KG).index = q := by
      have h3 := Subgroup.index_mul_card (KRx.subgroupOf KG)
      rw [hKRxs_card, ← hKRs_card, hKGcard36,
        mul_comm (Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)) q] at h3
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3
    have hKRs_ne : (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG ≠ KRx.subgroupOf KG := by
      intro heq
      apply hx_ne
      have h1 := congrArg (fun S : Subgroup ↥KG => S.map KG.subtype) heq
      simp only [Subgroup.subgroupOf_map_subtype] at h1
      rw [inf_eq_left.mpr hKR_le_KG, inf_eq_left.mpr hKRx_le_KG] at h1
      exact h1.symm
    -- the two index-`q` normal subgroups generate `K`
    have hsupKK : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG) = ⊤ := by
      by_contra hne
      have hdvd : (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG)).index
          ∣ q := by
        rw [← hKRs_index]
        exact Subgroup.index_dvd_of_le le_sup_left
      rcases (Nat.dvd_prime hq_prime).mp hdvd with h1 | h1
      · exact hne (Subgroup.index_eq_one.mp h1)
      · have h2 := Subgroup.index_mul_card (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
          ⊔ (KRx.subgroupOf KG))
        have h3 := Subgroup.index_mul_card ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        rw [h1] at h2
        rw [hKRs_index] at h3
        have h4 : Nat.card ↥(((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
            ⊔ (KRx.subgroupOf KG))
            = Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) :=
          Nat.eq_of_mul_eq_mul_left hq_prime.pos (h2.trans h3.symm)
        have h5 : (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG
            = ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG) :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq h4)
        have h6 : KRx.subgroupOf KG ≤ (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG := by
          rw [h5]
          exact le_sup_right
        have h7 : KRx.subgroupOf KG = (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG :=
          Subgroup.eq_of_le_of_card_ge h6 (le_of_eq (hKRs_card.trans hKRxs_card.symm))
        exact hKRs_ne h7.symm
    -- their intersection is central in `K`
    have hZle : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊓ (KRx.subgroupOf KG)
        ≤ Subgroup.center ↥KG := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro k
      have hk : k ∈ ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG) := by
        rw [hsupKK]
        trivial
      have hmul := Subgroup.normal_mul ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        (KRx.subgroupOf KG)
      have hkset : k ∈ (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG : Subgroup ↥KG) : Set ↥KG)
          * ((KRx.subgroupOf KG : Subgroup ↥KG) : Set ↥KG) := by
        rw [← hmul]
        exact hk
      obtain ⟨k₁, hk₁, k₂, hk₂, hkeq⟩ := hkset
      simp only at hkeq
      have hcomm1 : (z : ↥KG) * k₁ = k₁ * z := by
        have h8 : ⁅(z : G), (k₁ : G)⁆ = 1 := by
          have h9 : ⁅(z : G), (k₁ : G)⁆ ∈ (⁅(⁅KG, R₀⁆ : Subgroup G),
              (⁅KG, R₀⁆ : Subgroup G)⁆ : Subgroup G) :=
            Subgroup.commutator_mem_commutator
              (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hz).1)
              (Subgroup.mem_subgroupOf.mp hk₁)
          rwa [h334, Subgroup.mem_bot] at h9
        exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h8)
      have hcomm2 : (z : ↥KG) * k₂ = k₂ * z := by
        have h8 : ⁅(z : G), (k₂ : G)⁆ = 1 := by
          have h9 : ⁅(z : G), (k₂ : G)⁆ ∈ (⁅KRx, KRx⁆ : Subgroup G) :=
            Subgroup.commutator_mem_commutator
              (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hz).2)
              (Subgroup.mem_subgroupOf.mp hk₂)
          rwa [h334x, Subgroup.mem_bot] at h9
        exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h8)
      calc k * z = (k₁ * k₂) * z := by rw [hkeq]
        _ = k₁ * (k₂ * z) := mul_assoc _ _ _
        _ = k₁ * (z * k₂) := by rw [← hcomm2]
        _ = (k₁ * z) * k₂ := (mul_assoc _ _ _).symm
        _ = (z * k₁) * k₂ := by rw [← hcomm1]
        _ = z * (k₁ * k₂) := mul_assoc _ _ _
        _ = z * k := by rw [hkeq]
    -- `|K : Z(K)| = qʲ` with `j ≤ 2`
    have hZind_le : (Subgroup.center ↥KG).index ≤ q * q := by
      have hpos : 0 < (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
          ⊓ (KRx.subgroupOf KG)).index := by
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have h1 := Subgroup.index_mul_card (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
          ⊓ (KRx.subgroupOf KG))
        rw [h0, zero_mul] at h1
        exact Nat.card_pos.ne' h1.symm
      calc (Subgroup.center ↥KG).index
          ≤ (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊓ (KRx.subgroupOf KG)).index :=
            Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hZle)
        _ ≤ ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG).index * (KRx.subgroupOf KG).index :=
            Subgroup.index_inf_le
        _ = q * q := by rw [hKRs_index, hKRxs_index]
    obtain ⟨j, hjle2, hj⟩ : ∃ j ≤ 2, (Subgroup.center ↥KG).index = q ^ j := by
      obtain ⟨m, hm⟩ := hKGq.exists_card_eq
      obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hq_prime).mp
        (show (Subgroup.center ↥KG).index ∣ q ^ m by
          rw [← hm]
          exact Subgroup.index_dvd_card _)
      refine ⟨j, ?_, hj⟩
      by_contra hgt
      push Not at hgt
      have h1 : q ^ 3 ≤ q ^ j := Nat.pow_le_pow_right hq_prime.pos (by omega)
      have h2 : q * q < q ^ 3 := by
        have h3 : q * q = q ^ 2 := (pow_two q).symm
        have h4 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq_prime.one_lt (by omega)
        omega
      rw [hj] at hZind_le
      omega
    -- the value `j = 2` is impossible: `PR₀` would act faithfully on the 2-dimensional
    -- `𝔽_q`-space `K/K'` and be abelian (**Theorem 2.6(a)**), contradicting (3.21)/(3.13)
    have hj2 : j = 2 → False := by
      intro hj2
      have hZne : Subgroup.center ↥KG ≠ ⊤ := by
        intro htop
        rw [htop, Subgroup.index_top, hj2] at hj
        have h3 : 2 ^ 2 ≤ q ^ 2 :=
          Nat.pow_le_pow_left (Nat.succ_le_of_lt hq_prime.one_lt) 2
        omega
      have hcomm_eq : commutator ↥KG = Subgroup.center ↥KG := by
        rcases hK_special.2 with hEA | ⟨hc, _, _⟩
        · exfalso
          apply hZne
          rw [eq_top_iff]
          intro a _
          rw [Subgroup.mem_center_iff]
          intro b
          exact hEA.1 b a
        · exact hc
      have hQcard : Nat.card (↥KG ⧸ commutator ↥KG) = q ^ 2 := by
        rw [← Subgroup.index_eq_card, hcomm_eq, hj, hj2]
      haveI hQbar_comm36 : IsMulCommutative (↥KG ⧸ commutator ↥KG) := ⟨⟨hQbar_mul_comm⟩⟩
      have hexpQ36 : ∀ g : ↥KG ⧸ commutator ↥KG, g ^ q = 1 := by
        intro g
        refine QuotientGroup.induction_on g fun k => ?_
        have hk : k ^ q = 1 := by
          rw [← hK_exp]
          exact Monoid.pow_exponent_eq_one k
        rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
      have hqsmul36 : ∀ v : Additive (↥KG ⧸ commutator ↥KG), (q : ℕ) • v = 0 := by
        intro v
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact hexpQ36 v.toMul
      haveI hQmod36 : Module (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        AddCommGroup.zmodModule hqsmul36
      haveI : Module.Finite (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        Module.Finite.of_finite
      have hdim2 : Module.finrank (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) = 2 := by
        haveI : Fintype (Additive (↥KG ⧸ commutator ↥KG)) := Fintype.ofFinite _
        have h2 : Nat.card (Additive (↥KG ⧸ commutator ↥KG))
            = q ^ Module.finrank (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) := by
          rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q),
            ZMod.card]
        have h3 : Nat.card (Additive (↥KG ⧸ commutator ↥KG))
            = Nat.card (↥KG ⧸ commutator ↥KG) := rfl
        rw [h3, hQcard] at h2
        exact Nat.pow_right_injective hq_prime.two_le h2.symm
      set ρ2 : Representation (ZMod q) ↥A (Additive (↥KG ⧸ commutator ↥KG)) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd (↥KG ⧸ commutator ↥KG) q).comp φAQ
        with hρ2
      have hρ2_apply : ∀ (g : ↥A) (v : Additive (↥KG ⧸ commutator ↥KG)),
          ρ2 g v = Additive.ofMul (φAQ g (Additive.toMul v)) := fun g v => rfl
      have hfaith2 : Function.Injective ρ2 := by
        intro a b hab
        have h1 : ρ2 (a * b⁻¹) = 1 := by
          rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
        have h2 : a * b⁻¹ = 1 := by
          refine h329 _ fun kq => ?_
          have h3 := DFunLike.congr_fun h1 (Additive.ofMul kq)
          rw [hρ2_apply, Module.End.one_apply] at h3
          exact Additive.ofMul.injective h3
        exact mul_inv_eq_one.mp h2
      have hodd_A36 : Odd (Nat.card ↥A) := by
        obtain ⟨m2, hm2⟩ := Subgroup.card_subgroup_dvd_card A
        rw [hm2, Nat.odd_mul] at hodd
        exact hodd.1
      have hchar36 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥A → ¬ CharP (ZMod q) ℓ := by
        intro ℓ hℓ hdvd hcharP
        have hℓq : ℓ = q := CharP.eq (ZMod q) hcharP (ZMod.charP q)
        have hℓpr : ℓ = p ∨ ℓ = r := by
          have h3 : ℓ ∣ Nat.card ↥(P.map H.subtype : Subgroup G) * Nat.card ↥R₀ := by
            rw [← hAcard]
            exact hdvd
          rcases (Nat.Prime.dvd_mul hℓ).mp h3 with h4 | h4
          · left
            obtain ⟨k2, hk2⟩ := (hPp.map H.subtype).exists_card_eq
            rw [hk2] at h4
            exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h4)
          · right
            rw [hr_card] at h4
            exact (Nat.prime_dvd_prime_iff_eq hℓ hr_prime).mp h4
        rcases hℓpr with h5 | h5
        · exact hq_ne_p (by rw [← hℓq]; exact h5)
        · exact hq_ne_r (by rw [← hℓq]; exact h5)
      have hAcomm := OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd_A36 hdim2 ρ2
        hfaith2 hchar36
      have hPGR₀bot : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h6 := hAcomm.comm (⟨g₁, hPG_le_A hg₁⟩ : ↥A) ⟨g₂, hR₀_le_A hg₂⟩
        have h7 : g₁ * g₂ = g₂ * g₁ := congrArg Subtype.val h6
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr h7
      have hPGbot36 : (P.map H.subtype : Subgroup G) = ⊥ := h321G ▸ hPGR₀bot
      apply h313G
      rw [hPGbot36, Subgroup.commutator_bot_right]
    -- so `K/Z(K)` is cyclic and `K` is abelian, hence elementary abelian ((3.26))
    have hj01 : Nat.card (↥KG ⧸ Subgroup.center ↥KG) = q ^ j := by
      rw [← Subgroup.index_eq_card, hj]
    haveI hcyc : IsCyclic (↥KG ⧸ Subgroup.center ↥KG) := by
      rcases j with _ | _ | _ | j4
      · haveI : Subsingleton (↥KG ⧸ Subgroup.center ↥KG) := by
          rw [pow_zero] at hj01
          exact (Nat.card_eq_one_iff_unique.mp hj01).1
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hj01
        exact isCyclic_of_prime_card hj01
      · exact absurd rfl (fun h => hj2 h)
      · exact absurd hjle2 (by omega)
    have hKcomm : ∀ a b : ↥KG, a * b = b * a := by
      refine commutative_of_cyclic_center_quotient
        (QuotientGroup.mk' (Subgroup.center ↥KG)) ?_
      rw [QuotientGroup.ker_mk']
    have h336 : (⁅KG, KG⁆ : Subgroup G) = ⊥ := by
      have hc : commutator ↥KG = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        exact hKcomm b a
      have hKGder36 : (commutator ↥KG).map KG.subtype = ⁅KG, KG⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [← hKGder36, hc, Subgroup.map_bot]
    have h336ea : OddOrder.GroupTheory.IsElementaryAbelian q ↥KG :=
      ⟨hKcomm, fun k => by rw [← hK_exp]; exact Monoid.pow_exponent_eq_one k⟩
    -- ===== (3.37) `|K| > q²` =====
    -- `A = PR₀` acts faithfully on `K` itself ((3.28)); were `|K| ≤ q²`, the elementary
    -- abelian `K` would be an `𝔽_q`-space of dimension ≤ 2 and `A` would be abelian in
    -- every case (dim 2: **Theorem 2.6(a)** again; dim 1: endomorphisms of a line commute;
    -- dim 0: `K = ⊥` contradicts (3.13)) — against (3.21)/(3.13).
    have h337 : q ^ 2 < Nat.card ↥KG := by
      by_contra hle
      push Not at hle
      haveI hKGcommM : IsMulCommutative ↥KG := ⟨⟨hKcomm⟩⟩
      have hqsmulK : ∀ v : Additive ↥KG, (q : ℕ) • v = 0 := by
        intro v
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact h336ea.2 v.toMul
      haveI hKmod : Module (ZMod q) (Additive ↥KG) := AddCommGroup.zmodModule hqsmulK
      haveI : Module.Finite (ZMod q) (Additive ↥KG) := Module.Finite.of_finite
      set ρ3 : Representation (ZMod q) ↥A (Additive ↥KG) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥KG q).comp φA with hρ3
      have hρ3_apply : ∀ (g : ↥A) (v : Additive ↥KG),
          ρ3 g v = Additive.ofMul (φA g (Additive.toMul v)) := fun g v => rfl
      -- faithfulness from (3.28)
      have hker3 : ∀ a : ↥A, ρ3 a = 1 → a = 1 := by
        intro a ha
        have haC : (a : G) ∈ Subgroup.centralizer (KG : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          have h1 := DFunLike.congr_fun ha (Additive.ofMul (⟨m, hm⟩ : ↥KG))
          rw [hρ3_apply, Module.End.one_apply] at h1
          have h2 : (a : G) * m * (a : G)⁻¹ = m :=
            congrArg Subtype.val (Additive.ofMul.injective h1)
          exact (mul_inv_eq_iff_eq_mul.mp h2).symm
        have habot : (a : G) ∈ A ⊓ Subgroup.centralizer (KG : Set G) := ⟨a.2, haC⟩
        rw [h328, Subgroup.mem_bot] at habot
        exact Subtype.ext habot
      have hKG_ne_bot37 : KG ≠ ⊥ := by
        intro hbot
        apply h313G
        rw [hbot, Subgroup.commutator_bot_left]
      -- `A` is abelian whatever the dimension (≤ 2) — contradiction with (3.21)/(3.13)
      have hAcomm37 : ∀ a b : ↥A, a * b = b * a := by
        haveI : Fintype (Additive ↥KG) := Fintype.ofFinite _
        have hcardK : Nat.card (Additive ↥KG)
            = q ^ Module.finrank (ZMod q) (Additive ↥KG) := by
          rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q),
            ZMod.card]
        have hcardK' : Nat.card (Additive ↥KG) = Nat.card ↥KG := rfl
        have hfrle : Module.finrank (ZMod q) (Additive ↥KG) ≤ 2 := by
          by_contra hgt
          push Not at hgt
          have h1 : q ^ 3 ≤ q ^ Module.finrank (ZMod q) (Additive ↥KG) :=
            Nat.pow_le_pow_right hq_prime.pos (by omega)
          have h3 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq_prime.one_lt (by omega)
          omega
        rcases hfr : Module.finrank (ZMod q) (Additive ↥KG) with _ | _ | _ | fr4
        · -- dim 0: `K = ⊥`
          exfalso
          rw [hfr, pow_zero] at hcardK
          exact hKG_ne_bot37 (Subgroup.eq_bot_of_card_eq _ (hcardK'.symm.trans hcardK))
        · -- dim 1: all endomorphisms of a line are scalars, hence commute
          intro a b
          have htriv := S03e.trivial_on_commutator_of_finrank_eq_one ρ3
            (by rw [hfr]) (⊤ : Subgroup ↥A)
          have h1 : ρ3 ⁅a, b⁆ = 1 := htriv _
            (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
          have h2 : ⁅a, b⁆ = 1 := hker3 _ h1
          exact commutatorElement_eq_one_iff_mul_comm.mp h2
        · -- dim 2: Theorem 2.6(a)
          have hfaith3 : Function.Injective ρ3 := by
            intro a b hab
            have h1 : ρ3 (a * b⁻¹) = 1 := by
              rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
            exact mul_inv_eq_one.mp (hker3 _ h1)
          have hodd_A37 : Odd (Nat.card ↥A) := by
            obtain ⟨m2, hm2⟩ := Subgroup.card_subgroup_dvd_card A
            rw [hm2, Nat.odd_mul] at hodd
            exact hodd.1
          have hchar37 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥A → ¬ CharP (ZMod q) ℓ := by
            intro ℓ hℓ hdvd hcharP
            have hℓq : ℓ = q := CharP.eq (ZMod q) hcharP (ZMod.charP q)
            have hℓpr : ℓ = p ∨ ℓ = r := by
              have h3 : ℓ ∣ Nat.card ↥(P.map H.subtype : Subgroup G) * Nat.card ↥R₀ := by
                rw [← hAcard]
                exact hdvd
              rcases (Nat.Prime.dvd_mul hℓ).mp h3 with h4 | h4
              · left
                obtain ⟨k2, hk2⟩ := (hPp.map H.subtype).exists_card_eq
                rw [hk2] at h4
                exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h4)
              · right
                rw [hr_card] at h4
                exact (Nat.prime_dvd_prime_iff_eq hℓ hr_prime).mp h4
            rcases hℓpr with h5 | h5
            · exact hq_ne_p (by rw [← hℓq]; exact h5)
            · exact hq_ne_r (by rw [← hℓq]; exact h5)
          have hAcomm := OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd_A37
            (by rw [hfr]) ρ3 hfaith3 hchar37
          exact hAcomm.comm
        · exact absurd hfrle (by omega)
      have hPGR₀bot37 : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h6 := hAcomm37 (⟨g₁, hPG_le_A hg₁⟩ : ↥A) ⟨g₂, hR₀_le_A hg₂⟩
        have h7 : g₁ * g₂ = g₂ * g₁ := congrArg Subtype.val h6
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr h7
      have hPGbot37 : (P.map H.subtype : Subgroup G) = ⊥ := h321G ▸ hPGR₀bot37
      apply h313G
      rw [hPGbot37, Subgroup.commutator_bot_right]
    -- ===== Phase F ((3.38)): the orbit-parity contradiction =====
    -- Split off to `S03f_OrbitParity.orbit_parity_contradiction` (it consumes no induction
    -- hypothesis — only the facts established above — and carries the whole counting argument).
    exact orbit_parity_contradiction hp hq_prime hr_prime hq_ne_p hpr hodd hVG hKG
      hVGelem hV_ne_bot hKcomm hK_exp hKGq h337 h314C hVK_inf hCHV hPp hr_card hAdef
      hA_le_N h311 h313G h319 h321G h323G h324 hKRs_index

/-- **BG Theorem 3.6** (mmd L955).  `G` solvable of odd order, `H ◁ G` a normal Hall subgroup, `R` a
complement of `H`, `R₀ ≤ R` of prime order with `C_H(R₀)` a `Z`-group.  Then `[H, R]` has `p`-length
one, for every prime `p`.

The vertex of the §3 subprogram (engine of BG Theorem 10.6); proved by a minimal-counterexample
argument (equations (3.6)–(3.38)) that consumes Lemma 1.21, Theorems 3.4 and 3.5, Gorenstein 5.3.7,
and many §1 propositions.  See `notes/bg/s03_thm36_plan.md` for the phase-by-phase plan. -/
theorem thm36
    {G : Type*} [Group G] [Finite G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {H R : Subgroup G} [H.Normal] (hcompl : Subgroup.IsComplement' H R)
    (hHall : Nat.Coprime (Nat.card ↥H) (Nat.card ↥R))
    {R₀ : Subgroup G} (hR₀R : R₀ ≤ R) (hR₀p : ∃ r : ℕ, r.Prime ∧ Nat.card ↥R₀ = r)
    (hZ : OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)))
    {p : ℕ} (hp : p.Prime) :
    hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G) :=
  thm36_aux (Nat.card G) hodd hcompl hHall hR₀R hR₀p hZ hp rfl

end OddOrder.BG.Ch1.S03f
