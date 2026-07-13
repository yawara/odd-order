---
id: 31
slug: isaacs-ch07-thm-7-1-thompson-pcomplement
title: "Isaacs Thm 7.1 Thompson normal p-complement"
created: 2026-05-26
---

# Isaacs Thm 7.1 Thompson normal p-complement

## 背景

**Isaacs Thm 7.1** (Thompson, mmd L3721):

> p ≠ 2, P ∈ Syl_p(G), C_G(Z(P)) and N_G(J(P)) both have normal p-complements
> ⇒ G has a normal p-complement.

7-step counterexample-minimum proof using Thm 7.6 normal-J + Thm 5.26 Frobenius
normal p-complement + Lem 7.7 (N/C `p'`-quotient).

`HasNormalPComplement p G` already defined in
`OddOrder/Isaacs/Ch05_Transfer/Main.lean:310`.  Lem 7.7 both halves already proved in
`OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean:2515-2643`.

## やること

- [x] Resolve Thm 7.6 first (issue #30).  ← **DONE** (0030 closed; `normal_J` landed・axiom-clean. 下記 2026-05-30 update)
- [ ] Implement 7-step proof (mmd L3913-L3949):
  1. Reduce to minimum counterexample.
  2. Use Lem 7.7 to pass through O_{p'}(G).
  3. Apply normal-J theorem 7.6 in reduced group.
  4. Combine with N_G(J(P)) normal p-complement hypothesis.
  5. Combine with C_G(Z(P)) normal p-complement hypothesis (via Thm 5.26).
  6. Derive contradiction in minimum counterexample.
- [ ] Add top-level theorem `OddOrder.Isaacs.Ch07.thompson_normal_p_complement…`.

## 2026-05-26 update — sub-agent feasibility analysis

**Feasible AFTER Thm 7.6 (#30) lands**. Medium effort ~300-450 LOC. All other dependencies sorry-free:

- **Thm 5.26 Frobenius normal p-complement**:
  `OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer`
  at `Ch05_Transfer/Main.lean:2533` (both directions sorry-free).
- **Lem 7.7 (a)(b)**: `normalizer_and_centralizer_map_of_coprime_kernel` at L2623 (sorry-free).
- **`HasNormalPComplement` subgroup inheritance**: `hasNormalPComplement_of_subgroup` (Lem 5.27 Part 1) at L1983 (sorry-free).
- **`lt_normalizer_of_pgroup_of_lt_top`** : 既存 Ch.5.

Step breakdown:
- Step 1 (U = O_p(G), "normalizers grow"): ~60 LOC
- Step 2 (G/U has normal p-complement): ~50 LOC (needs new `HasNormalPComplement` **quotient inheritance** helper, ~30 LOC standalone — not yet present)
- Step 3 (O_{p'}(G) = 1): ~40 LOC (uses Lem 7.7)
- Step 4 (P maximal via Hall-Higman 1.2.3): ~30 LOC
- Step 5 (`C_G(Z(P)) = P`): ~15 LOC
- Step 6 (G/U's complement abelian): ~50 LOC
- Step 7 (apply normal-J 7.6 → contradiction): ~30 LOC
- +1 helper (quotient inheritance): ~30-50 LOC

候補識別子: `thompson_normal_p_complement` (no existing definition).

## 完了条件

- Top-level theorem matching goal-grep `^theorem thompson_normal_p_complement…`.
- Proof sorry/axiom-free.

## 参照

- `notes/isaacs/ch07_thompson.md` — section §7C
- `references/isaacs/finite-group-theory.mmd` L3721, L3913-L3949
- Issue #30 (Thm 7.6 — prerequisite)

## 2026-05-30 update — 前提クリア、着手可能 (READY)

**この issue が「Thm 7.1 の本物の §7C 7 ステップ証明」を追跡する正本** (重複 issue は作らない方針).
唯一のブロッカーだった **Thm 7.6 (normal-J) が landed 済み**になり、本 issue は **blocked → ready** に昇格.

### 前提の確定状況 (2026-05-30 検証)

- **Thm 7.6 `normal_J`** (`Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean:1416`): 無条件・sorry-free.
  `#print axioms OddOrder.Isaacs.Ch07.normal_J` → `{propext, Classical.choice, Quot.sound}` のみ
  (AxiomsCheck.lean:504 でガード). issue **0030 は closed**.
  - ⚠ doc 注意: `normal_J` の docstring は「Remaining local axioms: `step4_5_normal_J_hypotheses` /
    `step8_normal_J_closure`」と書くが **これは stale** — `#print axioms` 上それらは依存に出ない
    (= discharge 済み). 実装時に docstring を信用して二重に証明しないこと (docstring 修正は別途).
- **Thm 5.26** `hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer`
  (`Ch05_Transfer/Main.lean:2533`) — 両方向 sorry-free.
- **Lem 7.7 (a)(b)** `normalizer_and_centralizer_map_of_coprime_kernel` (Main.lean:2623) — sorry-free.
- **Lem 5.27 Part 1** `hasNormalPComplement_of_subgroup` (Main.lean:1983) — sorry-free.

### 現状の scaffold (これを置換/超克する)

`thompson_normal_p_complement` (`S7B2_NormalJ_PComplement.lean:1667`) は **forward 仮説版**:
`(hJ_normal : (thompsonJ P p).Normal)` を仮定として取る 4 行 reduction (= J(P) が正規な退化ケースのみ).
axiom-clean だが**本定理ではない**. 本 issue の 7 ステップ証明は `hJ_normal` を仮定せず、最小反例論法で
本来の Thm 7.1 を確立する (mmd L3913-L3949). 命名は既存の `thompson_normal_p_complement` を本物の
証明に差し替えるか、別名 + 旧 scaffold 廃止のいずれか (実装時に判断).

### 残りの新規インフラ (2026-05-26 分析のまま有効)

- **`HasNormalPComplement` quotient inheritance** helper (~30-50 LOC, 未実装) — Step 2 で要.
  他の step (1,3,4,5,6,7) は上記 landed 補題で賄える. 全体 ~300-450 LOC.

### 位置づけ

Peterfalvi 指標理論ラインとは**別系統 (Isaacs/BG 側)**. flagship かつ既知スキャフォールド解消なので価値は高い.
完成すると §6C (Thm 6.22-6.24 Frobenius 核冪零, 未形式化) の `6.23 → 7.1 → 6.24` ラインも前進可能になる.


## 2026-06-02 update — lane I1 Step 7 + quotient inheritance landed

Lane `codex/isaacs-ch07-pcomp` replaced the public scaffold surface around
`thompson_normal_p_complement`: it no longer assumes raw
`hJ_normal : (thompsonJ P p).Normal`.  The old final observation is now the private helper
`thompson_normal_p_complement_of_thompsonJ_normal`, and the public theorem proves Step 7
from the actual `normal_J` hypotheses:

- `hp2 : p ≠ 2`
- `h_pSolvable : IsPiSeparable ({p} : Set ℕ) G`
- abelian Sylow `2`-subgroups
- `O_{p'}(G) = 1`
- `C_G(Z(P)) = P`
- plus the original `N_G(J(P))` normal `p`-complement hypothesis

Also landed the missing generic helper `hasNormalPComplement_quotient`: normal
`p`-complements pass to quotient groups.  This discharges the "homomorphic images"
inheritance infrastructure explicitly invoked in §7C and needed in Step 2/Step 3.

Remaining work toward the full Isaacs Thm 7.1 statement:

1. Formalize the minimum-counterexample setup and bad-subgroup choice used before Step 1.
2. Step 1: prove the chosen bad subgroup `U` equals `O_p(G)` using normalizers-grow in
   `p`-groups and the maximality conditions on `|N_G(U)|_p` and `|U|`.
3. Step 2: prove `G/U` has a normal `p`-complement by showing the quotient hypotheses for
   `N_{G/U}(J(P/U))` and `C_{G/U}(Z(P/U))`; use the new quotient inheritance helper for
   the homomorphic-image part.
4. Step 3: prove `O_{p'}(G)=1` using Lemma 7.7 and quotient inheritance for the images of
   `N_G(J(P))` and `C_G(Z(P))`.
5. Step 4: prove `P` is maximal in `G` using Step 2 p-solvability, Step 3, and the
   Hall-Higman centralizer bound.
6. Step 5: derive `C_G(Z(P)) = P` from maximality and the centralizer normal
   `p`-complement hypothesis.
7. Step 6: prove the normal `p`-complement of `G/U` is abelian, then derive the abelian
   Sylow-2 hypothesis for `G`.
8. Assemble the full theorem surface with the textbook hypotheses
   `p ≠ 2`, `P : Sylow p G`, `HasNormalPComplement p C_G(Z(P))`, and
   `HasNormalPComplement p N_G(J(P))`, feeding Steps 2-6 into the new Step 7 theorem.


## 2026-06-02 update — subgroup image inheritance for Steps 2/3

Landed the next inheritance bridge in lane `codex/isaacs-ch07-pcomp`:

- `hasNormalPComplement_subgroup_map`: normal `p`-complements pass from a subgroup
  to its homomorphic image.  This is the subgroup-image form of the "homomorphic
  images" inheritance invoked before the seven-step proof.
- `hasNormalPComplement_normalizer_map_of_coprime_kernel`: combines the above with
  Lemma 7.7(a), so a normal `p`-complement in `N_G(X)` pushes to one in
  `N_{G/N}(Xbar)` when `N` is a normal `p'`-subgroup and `X` is a nontrivial
  `p`-subgroup.
- `hasNormalPComplement_centralizer_map_of_coprime_kernel`: same for centralizers,
  using Lemma 7.7(b).

This makes the Step 3 quotient-hypothesis transfer explicit: once the eventual proof
identifies `J(Pbar)` and `Z(Pbar)` with the quotient images of `J(P)` and `Z(P)`,
the existing hypotheses on `N_G(J(P))` and `C_G(Z(P))` can be pushed to the quotient
normalizer and centralizer.  Step 2 still needs the separate `U ≤ X ≤ P` lift and
bad-subgroup maximality argument for `J(P/U)` and `Z(P/U)`.


## 2026-06-02 update — Thompson J quotient identification

Landed the Step 3 `J(P)` quotient bridge:

- `thompsonJ_map_of_coprime_kernel`: if `N ⊴ G` is a normal `p'`-subgroup and
  `P` is a `p`-subgroup, then
  `J(P.map (QuotientGroup.mk' N)) = (J(P)).map (QuotientGroup.mk' N)`.

The proof uses coprimality to get `P ∩ N = 1`, restricts the quotient map to an
injective homomorphism on `P`, applies the existing injective-image theorem for
Thompson `J` to `⊤ ≤ P`, and transports the result back to ambient subgroups.
Together with the normalizer image inheritance already landed, this removes the
missing `J(Pbar)` identification needed to push the `N_G(J(P))` hypothesis through
`p'`-quotients in Step 3.  The analogous center/`Z(Pbar)` quotient identification
remains open for the centralizer half.

## 2026-07-14 update — Step 3 center quotient identification landed

Added the dedicated §7C leaf
`OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean` and proved
`center_map_subtype_map_of_coprime_kernel`.  For a normal `p′`-kernel `N`, the
quotient map is injective on a `p`-subgroup `P`; the theorem uses this to identify
the ambient image of `Z(P̄)` with the quotient image of the ambient `Z(P)`.

Together with `thompsonJ_map_of_coprime_kernel` and the normalizer/centralizer
image inheritance lemmas in `S7B2_NormalJ_PComplement`, both Step 3 local
hypotheses can now be transported through `G/O_{p′}(G)`.  Remaining frontier is
the minimum-counterexample carrier and Steps 1–6 assembly of the full Theorem 7.1.

## 2026-07-14 update — conjugacy-invariant hypothesis carrier landed

The §7C leaf now packages the two textbook local hypotheses as
`HasThompsonLocalPComplements p P` and proves their honest transport across any
group isomorphism.  The proof uses the public normal-`p`-complement `MulEquiv`
transport, injective-image formulas for `Z(P)` and `J(P)`, and exact image formulas
for centralizers and normalizers.

Sylow conjugacy then proves that the hypotheses at the chosen textbook Sylow
subgroup are equivalent to `HasThompsonPComplementHypothesis p G`, the intrinsic
all-Sylow form needed by strong induction.  The next frontier is Step 1: construct
the lexicographically maximal bad `p`-subgroup and prove that it is `O_p(G)`.

## 2026-07-14 update — Step 1 maximal bad-subgroup selection landed

Frobenius' normal-complement criterion now constructs a nontrivial `p`-subgroup
whose normalizer has no normal `p`-complement.  A second theorem selects such a
subgroup `U` lexicographically, first maximizing the intrinsic `p`-part of
`|N_G(U)|`, then `|U|` among ties.  Both maxima are selected from the finite type
`Subgroup G`; no choice field is postulated.

The `normalizerPPart` API identifies that weight with the order of every Sylow
`p`-subgroup of `N_G(U)` and bounds all `p`-subgroups of the normalizer.  The next
proof obligation is the mathematical core of Step 1: use induction plus the
normalizer-growth argument to force `N_G(U)=G`, then maximality to show `U=O_p(G)`.

## 2026-07-14 update — subgroup descent for the induction step landed

A normal `p`-complement now descends along an inclusion of finite subgroups, and
homomorphic images of normalizers are controlled by the ambient normalizer.  Using
these two facts together with the exact injective-image formulas for centers and
Thompson subgroups, `HasThompsonLocalPComplements.of_subgroup` proves that the
ambient local hypotheses at a `p`-subgroup descend to any containing subgroup.

This supplies the induction bridge needed when the selected bad normalizer is
proper.  The remaining Step 1 core is to turn a failed local hypothesis inside
that normalizer into a strictly larger bad normalizer `p`-part, contradicting the
lexicographic choice of `U`.

## 2026-07-14 update — Step 1 maximal bad subgroup identified with `O_p(G)`

The normalizer-growth core of Step 1 is now complete.  If the selected bad
subgroup `U` has proper normalizer `N`, strong induction makes the Thompson local
hypothesis fail in `N`.  The failed center-or-`J` condition constructs a bad
ambient `p`-subgroup `X`; growing a Sylow subgroup of `N` inside an ambient Sylow
subgroup gives a strictly larger `p`-subgroup of `N_G(X)`, contradicting the first
lexicographic maximality coordinate.  Hence `N_G(U) = G`.

Normality then gives `U ≤ O_p(G)`.  Since `O_p(G)` has the same full normalizer
and is itself bad, the second maximality coordinate forces equal finite orders,
so `U = O_p(G)`.  The generic normalizer-growth lemma was moved upstream from
`Basic.lean` into the §7C leaf so this proof remains acyclic and downstream users
retain the same public theorem name.  The next frontier is Step 2: prove that
`G / O_p(G)` has a normal `p`-complement.
