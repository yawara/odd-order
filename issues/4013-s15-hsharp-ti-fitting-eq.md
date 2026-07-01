---
id: 4013
slug: s15-hsharp-ti-fitting-eq
title: "S15 §8 TI-subset: H_sharp_isTISubset/S_normalizes_H_sharp = hyp.H = fittingInG S (Pf 8.5.a crux)"
created: 2026-07-01
---

# S15 §8 TI-subset: `H_sharp_isTISubset` / `S_normalizes_H_sharp` は `hyp.H = fittingInG S` に帰着

## 対象 (lane d, S15_SAndT_Setup.lean の 2 sorry)

- `H_sharp_isTISubset` (~969): `IsTISubset (S04.sharp (hyp.H:Set G)) hyp.S` = Pf (8.6.a)「F(S)^# は TI」。
- `S_normalizes_H_sharp` (~974): `∀ l∈S, a∈H^# → lal⁻¹∈H^#` = S が H^# を正規化 (Pf (8.5.a) S-side)。

`hyp.H = P ⊔ C` で `P = maxNilpotentNormalHall S` (=M_F)、`C = U ⊓ centralizer P` (=C_U(M_F))。
Pf (8.5.a): `F(S) = M_F · C_U(M_F) = P·C`。ゆえ **`hyp.H = fittingInG S` (= F(S))** が両 sorry の crux。

## 全機構は在庫確認済 (2026-07-01 lane d 精査) — 残 crux は 1 つ

`hyp.H = fittingInG S`(TI 側は `hyp.H ≤ fittingInG S` で十分)さえ出れば両 sorry は closes:

- **FittingIsTI = (8.6.a)**: `S15.FittingIsTI M := IsTISubset (sharpSubgroup (fittingInG M)) (normalizer (fittingInG M))`
  (`BG/Ch4/S15_MF.lean:527`)。type-P2 M で `S15.fittingIsTI_of_isTypeP2 hG hM hP2 : FittingIsTI M`
  (`S15_MF.lean:8960`, BG Thm 15.7(a))。`hyp.S_typeP2` + `hyp.S_maximal` で即取得。
- **normalizer = S**: `S16.normalizer_fittingInAmbient_eq_self hG hM : normalizer (fittingInAmbient M) = M`
  (`S16_MainResults.lean:1923`)。`fittingInAmbient = fittingInG` (abbrev)。⟹ FittingIsTI の bound を S に rewrite。
- **P ≤ F(S)**: `S15.maxNilpotentNormalHall_le_fittingInG M` (`S16_MainResults.lean:1954`)。
- **sharp 一致**: `S04.sharp (X:Set) = X\{1} = sharpSubgroup (X:Subgroup)` (両定義 identical)。
- **TI transfer**: `IsTISubset.subset` (A'⊆A) / `.mono` (L≤L') (`TISubset.lean:122/127`)。

## crux = `C = C_U(M_F) ≤ fittingInG S` (= Pf (8.5.a) 本体)

`P ≤ F(S)` は在庫だが **`C ≤ F(S)` が唯一の gap**。検討した route は不可:
- `centralizer_fittingInG_inf_le_fittingInG` (`S08_FittingOfMaximal.lean:119`, `C_S(F(S))⊓S ≤ F(S)`)
  は **C が F(S) 全体を中心化**する必要。C は M_F=P のみ中心化 (U abelian でも F(S)⊋P の残り
  C_U(M_F) 部分の中心化は言えない) ⟹ 不可。
- `S12_Theorem127.fitting_eq_sup_of_canonical_line` の `A₀ = A⊓C(M_σ)` は **tau2 の rank-2 el-ab 特殊
  ケース**で hyp.C=C_U(M_F) と別物 ⟹ 一致しない。
- ⟹ 一般 (8.5.a) `F(M)=M_F·C_U(M_F)` (mmd `04.10:63` の M'=HU + coprime-order 論法; (8.4.c) 依存) が
  repo 未整備。これを形式化するのが本 issue の本丸。

## 次手 (Pf (8.5.a) 形式化 = bounded §8 piece)

`fittingInG S = maxNilpotentNormalHall S ⊔ (U ⊓ centralizer (maxNilpotentNormalHall S))` を type-P S で
証明 (⊇ は M_F, C_U(M_F) 共に nilpotent normal ⟹ ⊆ F(S); ⊆ は g∈C_M(M_F)⟹g∈M'=HU⟹coprime-order で
u∈C_U(M_F))。(8.4.c) `C_M(M_F) ≤ M'` と M'=P⊔U (`S_deriv_eq_PU`) を使う。着地後 `hyp.H = fittingInG S`
→ 両 sorry closes。carrier reconciliation (Sdata) は不要 (P/C は Hypothesis field 直取り)。

## 状態
- [x] 全 TI 機構の在庫確認 + crux 特定 (2026-07-01 lane d)
- [ ] Pf (8.5.a) `fittingInG S = P ⊔ C_U(P)` 形式化
- [ ] `H_sharp_isTISubset` / `S_normalizes_H_sharp` を assemble
