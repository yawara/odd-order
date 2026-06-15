---
id: 7001
slug: sibley-target-witnesses
title: "SibleyTarget witnesses for the wired §10-16 coherence riders (endpoint A residual)"
created: 2026-06-15
---

# SibleyTarget witnesses for the wired §10-16 coherence riders (endpoint A residual)

## 背景

FT-path policy の **endpoint A**(`notes/meta/ft_path_policy.md` §4)= Pf §10-16 spine の
coherence rider を (6.8) `S08.sibleySetup_is_coherent` への cite に置換する wiring。
engine + 最初の 3 rider は landing 済(commit `5b95fdb8`, `fec51141`):

- engine leaf `OddOrder/Peterfalvi/S10_CoherenceWiring.lean`(sorry-free):
  `coherent_of_sibley` / `nonempty_coherent_of_sibley` / `SibleyTarget`(carrier)/
  `coherent_of_sibleyTarget`(Nonempty 形)/ `cohereOfSibleyTarget`(unwrapped 形)。
- wired riders(各 body は engine cite で sorry-free、gap は `sibleyTarget_*` producer に局在):
  - S15 `S_coherent`(13.2.d) ← `sibleyTarget_S`
  - S11 `coherent_H0C_commutator`(9.11) ← `sibleyTarget_H0C`(下流 S12 `typeII_section11_coherence` も自動 decouple)
  - S14 `frobenius_typeI_coherent`(12.6) ← `sibleyTarget_frobI`(Frobenius = case-c1 で最構成容易)

各 rider は B が (6.8) proof body を埋めれば自動 unconditional 化する(engine 経由)。
**残る gap = 各 `sibleyTarget_*` producer**(現在 `sorry`)= 極大部分群が Sibley Dade
hypothesis (6.8)(a)/(b)/(c) を満たすことを exhibit する **§14 構造 obligation**。
これは Peterfalvi が (13.2.d) 等で「(6.8) applies to S」と読み下す箇所そのもの。

## やること

各 producer `noncomputable def sibleyTarget_* : CoherenceWiring.SibleyTarget τ S A0` を構成する。
返すべきは `SibleyTarget` の field 群:
- `H : Subgroup ↥L`(極大部分群 L = M/S の Sibley kernel、典型 = M_σ / nilpotent normal Hall)
- `invH : Invertible (Nat.card ↥H : ℂ)`(有限性から導出可)
- `sib : SibleyDadeHypothesis G L H`(6.8 の (a) H◁L nilpotent + L=H⋊W₁ split / (b) S=Ind 族 /
  (c) Frobenius ∨ Hypothesis46)
- `tau_eq : sib.tau = τ` / `S_eq : sib.S = S` / `A0_eq : supportInSubgroup (sharpImage H) L = A0`

- [ ] `sibleyTarget_frobI`(S14, **最優先**): Frobenius 枝 = `cases := Or.inl`。`hfrob` が
      `IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C` を供給するので (c1) は直接。残 = H nilpotent /
      split / H^# TI / §4 dade datum の構成(§14 type-F 構造)。
- [ ] `sibleyTarget_S`(S15, 13.2.d): type II/III。(c) は Hypothesis46 (c2) 枝(W₂ prime + (4.6))
      ⟹ §14 type-P 構造 + §6 (4.6) carrier 要。
- [ ] `sibleyTarget_H0C`(S11, 9.11): type II/III/IV の S(H₀C')。chief factor 構造依存。

## 完了条件

各 `sibleyTarget_*` の `sorry` が消える(= `SibleyTarget` を実構成)。これにより、対応 rider は
(6.8) のみに gate される状態へ移行(B 完成で完全 unconditional)。3 つ全ては §14/§6 構造の
landing に gate されるので、段階的に close 可。

## 参照

- `notes/meta/ft_path_policy.md` §4(endpoint A)
- `notes/peterfalvi/s10_13_maximal_structure.md`(§10-13 gate 分類)
- engine: `OddOrder/Peterfalvi/S10_CoherenceWiring.lean`
- (6.8) supplier: `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean:46` `sibleySetup_is_coherent`
  / `SibleyDadeHypothesis` = `S08_CoherenceCorePart1.lean:3265`
- commits `5b95fdb8`(engine + S15), `fec51141`(S11 + S14)
- 関連: issue 7000(§14 Prop 14.2 support, H 所有)= §14 type-P 構造の隣接
