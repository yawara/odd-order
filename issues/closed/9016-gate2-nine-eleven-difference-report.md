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

## ⚖️ HUB RULING (2026-07-06 夕, レーン分担監査 + ユーザー裁可) — obligation-2 (`τ₃` glue-map constructor) を **lane a に carve-out**

レーン分担監査で、a の gate-2 は真の carrier gate に collapse (obligation-1 hY は §14-gated、obligation-2 の
`ν`-constructor は repo 不在) = **a に正面から進められる ungated work が無い**状態と確定。同時に lane b は
BG §15/§16 (9017) の owner を追認され負荷過多。⟹ **負荷分散 + a の idling 防止**のため、obligation-2 を
当初案 (b へ carve) から **lane a への temporary S07 carve-out** に変更 (hub 裁定、ユーザー裁可):

1. **obligation-2 = non-orthonormal `S₂` 用 `τ₃`/`ν` glue-map constructor** を **lane a が build**。
   `OddOrder/Peterfalvi/S07_*` へ新規 coherence 宣言を追加する **temporary carve-out を a に付与**
   (b の active S07 領域 = orthonormal glue `S07:3196/3229` 系には非接触、additive のみ)。
   これは a 自身の gate-2 obligation で context も a が最も持つ。**genuinely-missing infra を規模を問わず
   正面から build** (CLAUDE.md「コスト/規模は非基準」)。
2. **obligation-1 hY** (`coherent_Sset_diff_SHCSet`、S₂ difference-coherence) は **b の `S07_Subcoherent`
   (9.11) squeeze chain** が producer (signature-contract、a は sorried-cite で待たない)。核 coherence は
   BG §15 (9017、b 所有) に bottom out。
3. ⟹ a は「fold して idle」でなく **ν-constructor を head-on ungated target** として持つ。carrier 2 本
   (a の ν-constructor + b の hY/BG§15) が landing 次第、a が `coherent_Sset_of_glued` 経由で
   `exists_zeta_residual_not_orthogonal` を cite-assembly (唯一 bare feitThompson sorry を close)。

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

## ✅ obligation-2 LANDED (2026-07-06, lane-a, commit a39e2934) — non-orthonormal `ν` constructor DONE

HUB RULING の obligation-2 (a への S07 carve-out) を **sorry-free で完遂**。教科書 Peterfalvi (6.8.1)
+ mathcomp `bridge_coherent` (PFsection5.v `Zisometry_of_cfnorm`) で **2 route 裏取り済み**: τ₃ は
「X 上 τ₂ / Y 上 τ₁ に一致する ℤ-線形写像」で、族は **pairwise-orthogonal だが orthonormal 不要**
(norm > 1 可)。∴ 当初「deep char 本体」framing は **過大評価**で、実体は orthonormal→orthogonal の
線形代数一般化 (各 Fourier 係数を squared-norm `⟨χⱼ,χⱼ⟩` で割る) だった。

**landed (additive、b の orthonormal glue S07:3196/3229 非接触)**:
- `S07.IntegralCharacterMap.coherentImageMap_apply_eq_of_orthogonal` — 正規化再構成 χₖ↦Xₖ。
- `S07.IntegralCharacterMap.coherentImageMapGlueOrthogonal` (+ `_apply_left`/`_right`) — τ₃ 本体。
- `S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthogonal` — 集合版存在
  (`ν` + hagreeX/hagreeY、orthonormality 落とす)。
- `S12_Core.inducedFamily_finite` / `inducedFamily_inner_self_ne_zero` — call-site prereq (ungated)。
- `S12.Hypothesis.exists_glue_nu` — **obligation-2 を gate-2 世界で discharge**: coh + hY から
  (11.8.6) `ν` を直接構成 (S₁,S₂ ⊆ pairwise-orth 𝒮 of nonzero norm, S₁⊥S₂)。honest doneness =
  constructor が dead でなく実際に使えることを実証。

**gate-2 residual の更新**: `coherent_Sset_of_column_identities` は今や
`coherent_Sset_of_glued coh hY (exists_glue_nu coh hY).choose …` で ν 部分を discharge 可能。
残るは **(1) hY** (§9/§14-gated = `coherent_Sset_diff_SHCSet`、b/§14) + **(2) (6.8.1) `b≡0` char
content** = `hmixed` (image-side ⊥) / `D`/`hDτ`/`hgen` (`hcol` column identities driven)。
**ν-construction obligation は residual から消えた**。(2) は hcol→these の (6.8.1) 導出で、これは
deep char body だが hcol は capstone の hypothesis ゆえ call-site で利用可 (未導出)。

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


## ✅ HUB CLOSE (2026-07-08 監視 tick): 裁定実行済 → 後継 tracker へ移譲

9016 HUB RULING の両 obligation は実行完了:
- **obligation-2** (non-orthonormal τ₃/ν glue-map constructor, lane-a S07 carve-out) = commit `a39e2934` で sorry-free landing (merge `77c410b8`)、merge_monitor.md 記録。
- **obligation-1** (hY producer = lane-b / S07_Subcoherent) = 専用 carve-out issue **0101** (2026-07-08) に fork・実施。

残る FT math (hY = `coherent_Sset_diff_SHCSet` / (6.8.1) capstone / `feitThompson` bare sorry) は生きているが、**9016 は既にその live tracker でない**: 本 issue の uniform-degree roadmap は issue **1019** (2026-07-07) が「非 Galois で偽」と反証し、(11.8.6) redesign を 1019、(9.11) 実行を 0101、§14 gate を 7001 が所有。⟹ 9016 は redundant historical ruling record。**後継 tracker = 1019 / 0101 / 7001**。close。
