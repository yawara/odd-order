---
id: 9085
slug: galois-inner-transport-shared-leaf
title: "shared leaf: ZIrr-Galois 内積 transport (GaloisInnerTransport) — TGapGalois generic 部の hoist + hub dedup"
created: 2026-07-12
---

# shared leaf: ZIrr-Galois 内積 transport — TGapGalois generic 部の hoist

## CLAIM (lane a, 2026-07-12, issue 1024 G2)

lane a が新 shared leaf `OddOrder/GroupTheory/RepresentationTheory/GaloisInnerTransport.lean`
を作成する。内容 = lane c の `S16_NonExistenceG/TGapGalois.lean` 冒頭 2 定理の **generic 部の
hoist** (group 変数 L で完全 generic、S16 依存なし):

- `ClassFunction.inner_mapRingEquiv_eq_of_mem_ZIrr` — ⟨νφ, νη⟩ = ⟨φ,η⟩ (φ,η ∈ ZIrr):
  mapRingEquiv は ZIrr 上 ℤ-等長 (star-可換仮定不要 — `apply_inv_eq_star_of_mem_ZIrr` +
  `inner_mem_ZIrr_int` 経由)。
- `ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add` — Galois transport が φ を
  ⊥-補正のみで動かすなら整係数不変 (a_aut 定数性 engine)。

**動機**: lane a の (11.9.a) M-side 行0射影 (issue 1024 P2) が S13 leaf からこれらを要するが、
TGapGalois は `S16_NonExistenceG.TGapProjectionResidual` を import する S16-deep leaf ゆえ
S13 から import 不可 (層違反+閉包肥大)。既存の
`ClassFunction.mapRingEquiv_inner` (GaloisCharacter.lean:147) は star-可換仮定付きで ZIrr 版でない。

## hub への dedup 依頼

hoist 後、lane c の `TGapGalois.lean` の同名 2 定理は shared leaf を cite する thin 化
(または削除+call-site 置換) が可能。**c 所有 file ゆえ lane a は触らない** — hub 裁定で
c に振るか hub が実施。それまで両立 (同名だが別 namespace: c 版は S16 namespace 下、
shared 版は `OddOrder.RepresentationTheory.ClassFunction`)。

## 完了条件

- [x] leaf 作成 + 2 定理 sorry-free + AxiomsCheck 登録 (lane a)
- [ ] c 側 dedup (hub 裁定待ち)
