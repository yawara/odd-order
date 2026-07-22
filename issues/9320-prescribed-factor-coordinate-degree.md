---
id: 9320
slug: prescribed-factor-coordinate-degree
title: "Prescribed factor coordinates: field degree を explicit parameter 化"
created: 2026-07-23
---

# Prescribed factor coordinates: field degree を explicit parameter 化

## claim

- owner: lane b
- claimed: 2026-07-23
- consumer: Higman Lemma 13 p.92 common `Φ(P)²` coordinates for restricted factors
- shared target:
  `OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/PrescribedFactorCoordinates.lean`
- downstream compatibility check:
  `OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/Assembly.lean`

## 背景

既存の prescribed-factor constructors は field degree `n` を ambient group の
`finrank Φ(P)` に definitionally 固定している。Lemma 13 では honest な linear
equivalence `Φ(S) ≃ₗ Φ(P)²` を通して共通座標を各 restricted factor に移送するため、
degree は propositionally 一致するが同じ定義式ではない。座標 `ePhi` が既に degree を
決めるので、constructor 側で arbitrary implicit `n` を受けるのが自然な API。

## やること

- [ ] noncommutative prescribed-factor constructor を `{n : Nat}` 化
- [ ] commutative prescribed-factor constructor を `{n : Nat}` 化
- [ ] inclusive dispatcher を `{n : Nat}` 化
- [ ] 既存 caller の implicit inference を targeted build で確認
- [ ] warning ratchet を確認
- [ ] issue を closed に移す

## 完了条件

新規 sorry/axiom なし。prescribed-factor leaf と Assembly の targeted build green。
