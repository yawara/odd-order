---
id: 9048
slug: fitting-map-mulequiv
title: "Fitting subgroup transport across group isomorphisms"
created: 2026-07-06
---

# Fitting subgroup transport across group isomorphisms

## 背景

BG S03h に局所的に置かれていた Fitting の MulEquiv 移送補題を、
Fitting 本体を持つ Isaacs Ch01 API として公開する。これは BG 固有でなく、
subconfiguration / conjugation transport で再利用される shared-infra。

## やること

- [x] open 9000 issue と既存 Fitting API を確認する
- [x] `fitting_map_mulEquiv_le` と `fitting_map_mulEquiv` を Ch01 に追加する
- [x] `lake build OddOrder.Isaacs.Ch01_Sylow.Main` を通す

## 完了条件

Ch01 leaf build が通り、BG/Peterfalvi S-file に触らず Fitting の isomorphism transport API が利用可能になる。

## 参照

- `OddOrder/Isaacs/Ch01_Sylow/Main.lean`
- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
