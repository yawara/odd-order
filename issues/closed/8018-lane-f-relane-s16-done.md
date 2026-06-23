---
id: 8018
slug: lane-f-relane-s16-done
title: "HUB: lane-f relane — §16 構造 frontier 完了 or deep-gated, hP2II 還元済"
created: 2026-06-23
---

# HUB: lane-f relane — §16 構造 frontier 完了 or deep-gated, hP2II 還元済

> 宛先 = hub (merge monitor / 分担設計)。発信 = lane-f (BG §9/§14/§16 + POLE-1 構造側)。
> ユーザー裁可 (2026-06-23「HUB に lane 再配置を相談」) を受けて起票。批判でなく分担更新の依頼。

## 背景: lane-f の §16 構造 frontier は本質的に「完了 or deep-gated」

lane-f は 2026-06-23 セッションで POLE-1 構造側 + Prop 16.1 forward bridge を frontier
限界まで進めた。**残りは全て deep 未形式化 (lane-f 大物) か cross-lane gate** で、
新規に着手可能な「clean な lane-f 上流タスク」が枯渇した。

### 本セッション成果 (全 sorry-free + axiom-clean、AxiomsCheck 登録、main 合流済 or 合流待ち)

- **`typeP2_mf_internal_fitting_decomposition` (S15)** — BG Cor 15.5 の M_F-internal 分解 (type-P2)。
- **`typePData_of_isTypeP2` (S16)** — TypePData carrier が全 type-P2 maximal から構成可能 (doneness マイルストーン)。
- **`isTypeII_of_isTypeP2_of_derived_typeF` (S16)** — **Prop 16.1 forward bridge hP2II を {hderF, hderfit} のみに還元**。`hcommon` 全体が lane-f-local と判明 (Prop 14.2(g))、stale な「lane-b 10.11 gated」を訂正。

### lane-f §16 frontier の現況 (各項目の gate)

| 項目 | 状態 |
|---|---|
| **POLE-1 tp producer** `section16TypePStructure_of_isMinimalSimpleOdd` | ✅ **inline sorry 0 (assembly-complete)**。残 sorryAx = cite される **lane-b (10.11)** `theorem88_caseB_prime_orders` のみ (`exists_kappaHall_invariant_complement_to_MF`/`typeP_pair_W_structure` は clean) |
| **POLE-1 mp producer** `section16MaximalPair` | ✅ 完成 |
| **Prop 16.1 `hP2II`** (type-P2→II) | ✅ **{hderF, hderfit} に還元済**。残 = `hderF` (下記) |
| **`hderF`** (= `IsTypeF (derivedInG M)`) | ⛔ **deep 未形式化 §15/§16 補題**。唯一の gate = `maxNilpotentNormalHall M' = M_σ` (= F(M)=M_σ = Y:=O_{σ'}(F(M))=⊥)。subtle な τ₂/C_U(M_σ) 数論的 fact。Peterfalvi 版 (10.7) は sorried+char-gated+弱 carrier ゆえ cite 不可。multi-session、lane-f 所有可だが大物 (詳細 issue 7007 cont.⁹) |
| Prop 16.1 他 bridge (hFI alternative / reverse hIIP2 等 / type-P1 hP1neIIIIV·hP1eqV) | ⛔ deep (8.3/8.8 trichotomy) or carrier-gated (W1=κ-Hall) or M'/M_F nilpotent deferred |
| Thm 15.8/15.9 (`tau2_transfer_constraint`/`centralizer_escape_final_local`) | consumer 0 の下流 endpoint (upstream-first で defer) |

## 判断を仰ぎたいこと

**lane-f を (a) 現領域で deep 投資 (hderF) を続けるか、(b) 別領域へ再配置するか。**

- **(a) hderF deep 投資**: 唯一の clean な残 gate。`maxNilpotentNormalHall M' = M_σ` (F(M)=M_σ, Y=⊥) を BG §15 (Cor 15.9/Thm 15.8 周辺の τ₂(M) 構造) 精読 or ChatGPT 相談で de-risk → Lean 構築。閉じれば hP2II 完成。multi-session。
- **(b) 再配置候補**: lane-f の真の bottleneck は **lane-b (10.11 + §13 char/Dade `section16CharacterData`)**。POLE-1 tp は lane-b 10.11 待ちで本質完了。下流 (POLE-1 cd / final contradiction) も lane-b char gate。**∴ lane-b 領域の増援** (10.11 `theorem88_caseB_prime_orders` or §10-13 char-grid) が FT spine 全体には効く可能性。ただし char theory は lane-f の専門外 (BG 構造側が本籍)。
  - 代替: BG §14-15 の残 honest 構造 (もしあれば) / lane-h (Pf §14_MaximalI) との境界調整。

**lane-f の比較優位は BG 構造 (§9/§14/§16)** ゆえ、(a) hderF or BG §14-15 残務が自然。char theory 増援 (b) は専門外で効率落ちる可能性。hub の分担設計で裁定願う。

## 完了条件

hub が lane-f の次タスク (hderF 続行 or 再配置先) を裁定し、LAUNCH.md / merge_monitor.md を更新。

## 参照

- issue 7007 (cont.⁸⁻⁹ 進捗ログ + hderF deep-dive characterization)
- 本セッション commits: `c3fbf4a8` (分解+TypePData) / `8f1d897f` (hP2II 還元) / docs
- memory [[ft-endgame-two-poles]] (cont.⁸⁻⁹ entry)
- 関連 hub issue: 4002 (lane-allocation feedback) / 4007 (lane-c relane)

---

## 解決 (2026-06-23, ユーザー裁可)

**ユーザー裁可 = (a) hderF を deep 投資 (推奨)**。lane-f は §16 構造 frontier の唯一の clean on-path gate
`hderF` (= `IsTypeF (derivedInG M)`、gate=`maxNilpotentNormalHall M'=M_σ` = F(M)=M_σ / Y=⊥) に
deep 投資して続行。閉じれば Prop 16.1 hP2II 完成 → (12.9)[H] も unblock。multi-session ゆえ **まず
ChatGPT 相談 (最強モデル) + BG §15 (Cor 15.9/Thm 15.8 周辺 τ₂(M) 構造) 精読で de-risk** してから Lean。
詰まったら sorry 退避せず STOP+報告。真に上流 prereq (Cor 15.9 等) に bottom-out したらそこを先に
(上流優先)。lane-f LAUNCH.md に hub 裁定ブロック追記済。CLOSED。
