---
id: 9405
slug: lane-c-bs-complete-next-frontier
title: "lane c: BS |S|≥16 完成 — 次 frontier 裁定要請 (territory 完済)"
created: 2026-07-22
---

# lane c: BS |S|≥16 完成 — 次 frontier 裁定要請

## 報告: issue 9318 Brauer–Suzuki の主キャンペーン完了 (2026-07-22, lane c)

`brauerSuzuki_of_quaternionSylow` (`GroupTheory/BrauerSuzukiEndgame.lean`) 完成:
**`oPiCore {p | p ≠ 2} G ⊔ centralizer {z} = ⊤`** (= `G = O_{2'}(G)·C_G(z)`)、
一般化四元数 Sylow-2 (`|S| ≥ 16`)。cyclic case (`brauerSuzuki_of_isCyclic_sylowTwo`) と合わせ、
BS 定理は cyclic + 一般化四元数 |S|≥16 で完成。全 axiom-clean [propext, Classical.choice,
Quot.sound] + AxiomsCheck 登録済。endgame (M 2-nilpotent / Q=S∩M cyclic / z̄ 中心 / Frattini)
は全て今 session (2026-07-22) 内で完成。

## 現状: lane c territory は ungated clean frontier が枯渇

hub 実測 (merge_monitor 2026-07-22) + 本 session の proper sorry census (multiline comment
strip) で確認:

- **BG/** = sorry-clean** (雑 census の 35 in S01 は docstring "sorry-free" の誤検出だった)。
  `formalized_specialized` code marker = **0**。
- **`Appendices/{Huppert,SemilinearField}` = sorry-clean**。
- **NearFields:786 (`rankOne_affine_nearField`)** = 9204 で **lane a へ carve-out 済**。残 sorry の
  内容 = near-field transport (Pf p.137) で、**BS 以外に transport が残り、full quaternion には
  Q₈ BS も要る**。ownership は a。
- **Suzuki2Groups / StepFive / StepSix (実 sorry 6)** = **lane b 領域** (Ch.8+Suzuki 系)。
- issue 3017 (BG Thm 6.2 J(S) 一般形) = **close 済**。

⟹ lane c は lane a と同じ **「territory 完済・非 gated frontier 無」** の境界に到達。

## 残る genuine lane-c work (いずれも即着手には難あり)

1. **Q₈ BS case (|S| = 8)** — BS の残 gap。Gorenstein は「all known proofs require the theory
   of modular characters」と明記。ordinary character 経路 (Lem 1.4〜1.9) は |S|≥16 専用で Q₈ に
   使えない。**repo に modular character theory 基盤が無い** + どの証明 (Glauberman block-free 等)
   を形式化するか literature 判断が要る = 真の research-adjacent gap (policy: 低優先繰延)。
2. **NearFields near-field transport** — genuine math だが ownership が a (carve-out)。BS が済んだ
   今 a が着手可能になったが、c がやると a と衝突。hub 調整領域。

## hub への裁定要請 (user でなく hub、方針どおり)

lane a の再配分 (9205、退役 A / NearFields skeleton B / cross-assign C / 新 E-scope) が既に
user escalation 中。**lane c も同じ完済境界ゆえ、a の再配分と bundle して裁定願う**。候補:

- (A) lane c 退役 (a と同時、lane d 退役の前例)。
- (B) NearFields transport の ownership を a→c 再割当 (BS 済ませた c が文脈を持つ) + Q₈ を別 gap issue。
- (C) cross-assign: 他レーンの重い frontier (b の Theorem B 組立 等) に c を投入。
- (D) shared infra / scope survey の残 Isaacs/Pf 未形式化結果を c に割当。

hub は自ら調査して裁定 (AskUserQuestion 不可; user escalation が要れば hub 判断で 9500 へ)。

## 完了条件

hub が lane c の次 frontier (上記 A–D いずれか、or 新規) を裁定し issue/notes に記録。

## 参照

- `GroupTheory/BrauerSuzukiEndgame.lean` (`brauerSuzuki_of_quaternionSylow`)
- issue 9318 (BS campaign、本 session で主要部完了)
- `notes/meta/merge_monitor.md` (hub 実測、a/c 完済境界)
- issue 9205 (lane a 再配分、user escalation 中)
