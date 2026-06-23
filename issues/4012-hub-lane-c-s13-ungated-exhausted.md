---
id: 4012
slug: hub-lane-c-s13-ungated-exhausted
title: "HUB: lane-c §13 ungated 群論枯渇 — (11.6) conjunct 2 landing 後の再配置判断"
created: 2026-06-23
---

# HUB: lane-c §13 ungated 群論枯渇 — (11.6) conjunct 2 landing 後の再配置判断

> 宛先 = hub / ユーザー。発信 = lane-c (relane #6, char ボトルネック支援)。
> issue 4011 → relane #6 と同じ「lane 枯渇 flag → 再配置」パターン。

## 背景

relane #6 (issue 4011) で lane-c = char ボトルネック支援 (Pf §13 `S13_MaximalIII_IV` [issue 2018] +
`card_kappaHall_lt_of_isTypeP1` [issue 2020, POLE-1])。2026-06-23 セッションで **§13 の唯一の ungated
群論 win を完遂**し、lane-c 単独で閉じられる §13 work が枯渇した。

### 本セッション landing (commit `a2bd962a`、full build green + AxiomsCheck OK)

**Pf (11.6) conjunct 2「U centralizes H₀」を character 入力なしで実証明** (sorry-free + axiom-clean):
- `chief_W2_inf_H0_eq_bot` = 連鎖因子核 `W₂ ⊓ H₀ = ⊥`。`|W₂|=p` prime (`typeIII_IV_p_eq_W2`) ⟹
  `W₂⊓H₀ ∈ {⊥, W₂}`; 連鎖因子位数 `|C_{H̄}(W₁)| = |W̄₂| = p` (`coprimeFrobeniusChiefFactor_card .2`) で
  像 nontrivial ⟹ `W₂ ⊄ H₀` ⟹ `=⊥`。= Pf (9.6) の fpf 入力 `C_{H₀}(W₁)=1` の honest 群論核。
- `U_centralizes_H0` = 上記を既存 Wielandt `U_centralizes_H0_of_W2_inf_H0_bot` に与え無条件締結。
- `core_structure` (11.6) を de-opacify (conjunct 2 = `U_centralizes_H0 hyp`、残 3 = IsPGroup/H₀=H'/
  C⊆U'-reverse のみ (11.5)-gated sorry)。`Hypothesis` に忠実性 field `setup_typeP_eq` 追加。
- 全て proven S11 補題 (chief-factor / Wielandt / Cor 3.28) の cite、新 axiom なし。

### 残 §13 + card_kappaHall = 全て char/未形式化 gated (lane-c 単独 closable work 無し)

- **(11.3) `coherent_S_of_coherent_SH0C` / (11.4) `coherent_quotient_bound`** ← lane-h relane #7 の
  standalone Pf (6.2)/(6.3) producer 待ち (issue 2021、未 landing を本セッション確認)。landing したら
  lane-c が cite するのみ。
- **(11.5) `HC_le_secondDerived`** ← Pf **(5.7)「M'/M'' abelian ⟹ S(M'') coherent」が未形式化**
  (S01 notes「(5.7)-(5.9) 完全欠落」) + (11.4) cite + (8.4.d) fpf + index arithmetic。(5.7) なしには
  honest に組めない。
- **(11.6) 残 (IsPGroup / H₀=H') / (11.7)** ← 全て (11.5) `secondDerived_eq_HC`-gated。
- **(11.8)/(11.9) (orthogonality / final_typeIII / q>p)** ← σ/τ/ω character API (gate #3) = lane-b、
  未 export ゆえ structure すら cite 不能 (deepest char gate)。
- **`card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson.lean:426, POLE-1 残バレ sorry, issue 2020)**
  ← (11.9) `final_typeIII_conclusions` (q>p) 経由で上記 §13 char にボトムアウト。pair-level bridge も
  char-gated ゆえ fresh sorry 維持が clean (issue 2020 既定)。

⟹ lane-c の §13/card_kappaHall は **1 つの char-gated クラスタ**で、ungated 群論は (11.6) conjunct 2 が
最後だった。

## やること (hub / ユーザーの方針判断)

lanes 等価 ([[lanes-are-equivalent-no-specialty]])、基準 = 価値 + 独立性。以下から選択:

1. **lane-c を別 FT-path セグメントへ再配置** (issue 4011→relane #6 と同様)。lane-b char 支援の別ファイル
   or 別 § の non-gated endpoint。**ユーザーが本 issue で選択した方針**。
2. **lane-c が Pf (5.7) を新規形式化** — abelian quotient ⟹ S coherent (§13 (11.5) + 下流が cite、
   §5 は lane-b 非 active で非衝突)。char 大物だが §13 を実 unblock。
3. **await gates + self-resume monitor** — lane-h (6.2)/(6.3) [issue 2021] + lane-b char API の landing を
   監視し自動再開。lane-c は当面 idle。

## 完了条件

hub が方針を決定し、(a) LAUNCH.md (lane-c) を更新、または (b) 本 issue を `issues/closed/` へ移動。
lane-c は self-resume monitor で解決を検知し自動再開する。

## 参照

- 本セッション commit: `a2bd962a` (Pf (11.6) conjunct 2)
- 関連 issue: 4011 (§15 枯渇→relane #6, CLOSED), 2018 (§13 char gate map), 2020 (card_kappaHall POLE-1),
  2021 (lane-h §6 (6.2)/(6.3) producer), 4009 (carrier wiring gate, CLOSED)
- ファイル: `OddOrder/Peterfalvi/S13_MaximalIII_IV.lean`,
  `OddOrder/FeitThompson.lean:426` (`card_kappaHall_lt_of_isTypeIIIorIV`)
- 原典: Pf §13 (11.x) = `references/peterfalvi/04.13_pp_64_68_*.mmd`; (5.7) = §5 (`04.3`/`04.7`)
- notes: `notes/peterfalvi/s10_13_maximal_structure.md` (§13 gate map)
