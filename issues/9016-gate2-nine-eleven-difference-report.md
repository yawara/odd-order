---
id: 9016
slug: gate2-nine-eleven-difference-report
title: "gate-2 (11.8.6) coherent_Sset blocked on (9.11) difference-coherence re-port (spine, §14)"
created: 2026-07-06
---

# gate-2 (11.8.6) `coherent_Sset` blocked on (9.11) difference-coherence re-port

> 発信 = lane-a (/loop, gate-2 carrier-bridge 精査後)。宛先 = hub + lane-b/§14 coordination。
> 技術詳細の正本 = `notes/peterfalvi/s13_11_8_orthogonality.md` update²⁶ + 「致命傷 1-3」。

## 背景 / 要点

`feitThompson` の唯一 bare sorry (`card_kappaHall_lt_of_isTypeIIIorIV`) は
`exists_zeta_residual_not_orthogonal` (assembled) → **gate-2**
`Hypothesis.coherent_Sset_of_column_identities` (`S12_MaximalIII_IV_V.lean:~3833`, sorry) に還元済。
gate-2 の carrier bridge を精査した結果、**(9.11) を sorried-cite するだけでは gate-2 は閉じない**
ことが判明 (従来 roadmap の「(9.11) を signature-contract で cite」想定は**誤り**)。

## 診断 (3 mismatch; 正本 = note update²⁶)

gate-2 は gluing engine に `hY : IsCoherent hyp.tau (hyp.Sset \ hyp.SHCSet) hyp.A0` (= S₂ coherence)
を要する。唯一の source = (9.11) `coherent_H0C_commutator` (`S11:8292`) だが triple `(τ,S,A)` のうち:

1. **τ**: 一致 (defeq, `mkSection11CharacterData.tau = hyp.tau`)。
2. **support A: 破綻** — `mkSection11CharacterData` は `H0CprimeSupport := ∅`。`zSupportedSpan S ∅ = {0}`
   ゆえ `IsCoherent.nonzero` が support ∅ で unconstructible。gate-2 の `hyp.A0` に整形不可。
3. **family S: 二重破綻** — (i) `chars.S = sSet data` (§9 `xiSet` induce) ↔ `hyp.Sset \ hyp.SHCSet`
   (§10 `inducedFamily` の差) の bridge が repo 不在 (grep 0)。(ii) **mmd 04.13 L67 で確認: Pf (9.11) は
   差 `𝒮(H₀C')−𝒮(HC')` の coherence であって full 𝒮 ではない** が、repo の `coherent_H0C_commutator` は
   `chars.S = sSet data` = **full 𝒮** を結論する (over-strong・型非互換)。

## やること (正しい close path、未実装・substantial)

- [ ] **(9.11) を difference coherence として再 port**: `IsCoherent τ (𝒮(H₀C')−𝒮(HC')) A` — S11 の
  `coherent_H0C_commutator` を差分版に再 state (現 full-𝒮 版は consumer 確認の上 signature 調整 or 別名)。
  core coherence 自体は `sibleyTarget_H0C` (S11:6353 sorry) 経由で **§14-gated** (issue 7001 系)。
- [ ] **(11.7) collapse + set-algebra**: `𝒮(H₀C')−𝒮(HC') = 𝒮(C)−𝒮(HC) = 𝒮₂` (H₀=1; `sOf`-difference 代数、未形式化)。
- [ ] **world bridge**: `𝒮₂ = hyp.Sset \ hyp.SHCSet` (§9 `sOf`/`sSet` ↔ §10 `inducedFamily`、未形式化)。
  ← S13 `SOf`-filtration (`SOf_secondDerived_eq` S13:882) が `SHCSet = SOf(M'')` を既に与えるので、
  (9.11) を `SOf(C)\SOf(HC)` の世界へ port するのが clean。
- [ ] gluing: `coherentUnion_of_glued_withDiagonal` (S07:4628; S₂ は orthonormal でないので
  `_of_orthonormal` 版は不可、`hcol` から `hDτ` を供給)。

## ★ update (skeleton 執行で判明): gate-2 は **2 obligation** — §14 だけでない

gated-endpoint skeleton を実際に組んで判明した decisive な追加 blocker:
**S07 の gluing engine は全て glued map `ν` を _input_ で取り、唯一の `ν` _constructor_
(`coherentImageMapGlue`/`exists_integralCharacterMap_glue_of_orthonormal`) は両 family orthonormal を要求する。**
gate-2 の `S₂` は **non-orthonormal** (reducible/degree-`qu` の induced `μ_j`) ゆえ **`ν` を構成する術が
repo に無い**。⟹ gate-2 は single §14 sorry に還元 **不可能**。obligation は 2 本:

1. **`hY` = S₂ coherence** (§14/§9-gated, 上記「診断」)。
2. **non-orthonormal `S₂` 用の `τ₃` glue-map constructor** = **genuinely-missing S07 infra**
   (Pf (5.3.b)/(5.5)/(6.8.1)-style; 「非 orthonormal な Y-side をもつ 2 coherence extension を貼り合わせ、
   共有 supported lattice 上で `τ` に restrict する `ν` を作る」)。**これが (11.8.6) の deep char 本体**。
   S07 は lane-b carve-out だがこの constructor は不在 → **lane-b coherence infra として要 build**。

## landed this session (lane-a, build-green)

- `dc7a7792` set-decomposition primitives `SHCSet_subset_Sset` / `Sset_eq_SHCSet_union_diff`
  (gluing engine の set-level 入力、reusable) + carrier-bridge map (note update²⁶)。
- `3cab3822` note refinement (致命傷 3 = difference vs full 𝒮)。
- `40919f42` **`coherent_Sset_of_glued`** (sorry-free glue wrapper: `coh`+`hY`+τ₃-data → gate-2 goal;
  gluing engine が (11.8.6) union で compose することを実証) + **`coherent_Sset_diff_SHCSet`**
  (correctly-typed §14-gated `hY` obligation, 唯一の新 sorry, false-hoist でない)。gate-2 body は
  `ν` 未構成ゆえ依然 sorried (reduction path を comment 化)。
- `4dd6f3c8` note update²⁷。
- full build green (feitThompson single sorry 不変、新 axiom 無)。

## 完了条件

gate-2 `coherent_Sset_of_column_identities` の sorry が `coherent_Sset_of_glued coh hY ν …` で閉じる
= **両 obligation** landing: (1) `hY` (§14/sibleyTarget で sorried skeleton 可) + (2) `ν` constructor
(non-orthonormal glue, missing S07 infra、lane-b coherence 領域)。片方だけでは閉じない。

## 参照

- 正本 note: `notes/peterfalvi/s13_11_8_orthogonality.md` (update²⁶ + 致命傷 1-3 + update²⁷)。
- 関連: 7001 (sibleyTarget §14 gate)、2030 (S9 carrier keystone)、9014 (lane-b prime-TI, 別 gate 10.7/10.8)、
  1017 (lane-b coherence infra)。
- **hub 含意**: gate-2 の 2 obligation は共に **cross-lane** — (1) §14 sibleyTarget (lane-c/§14)、
  (2) non-orthonormal glue-map constructor (**lane-b の S07 coherence carve-out**)。lane-a の on-path
  frontier (群論 + gluing wrapper + obligation 分離) は**完遂**。次は lane-b/§14 の 2 obligation build 待ち、
  または hub が (2) の non-orthonormal glue constructor を lane-b にアサイン。
