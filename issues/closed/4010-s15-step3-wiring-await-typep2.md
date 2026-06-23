---
id: 4010
slug: s15-step3-wiring-await-typep2
title: "lane-c step-3 wiring unblock 待ち — lane-h (13.2.a) IsTypeP2 mp.S 着地で close 依頼 (self-resume trigger)"
created: 2026-06-23
---

# lane-c step-3 wiring unblock 待ち — lane-h (13.2.a) IsTypeP2 mp.S 着地で close 依頼 (self-resume trigger)

## 背景

relane #4 (issue 4009 CLOSED, ユーザー裁可) で carrier wiring の唯一 gate `IsTypeP2 mp.S` (Pf (13.2.a)
「q<p ⟹ mp.S は type-P2」) は **lane-h** が担当と確定。lane-c は carrier 機構
(`exists_typePData_W1_eq_of_isTypeP2` 他、sorry-free, main 済) を完成させ、残るは step-3 wiring
(producer に `IsTypeP2 mp.S` を適用 → `Section16TypePStructure.Sdata` → `S15.Hypothesis` → `basic_structure`)。

2026-06-23 lane-c 再開時に **ユーザー裁可 option 1「§15 (13.2) 深掘り」**を実施 → Pf (13.2) 証明本文 +
signature 追跡で **(13.2.b,c,e) は完全 carrier-gated** と厳密確認 (notes `s15_s_and_t.md` 該当節 +
commit `b487a888`)。(11.7)=`S13.H_elementaryAbelian` は rich な `S13.Hypothesis` を入力に要し、
`typePData_of_isTypeNonI` の intrinsic `.U`/`.W1` が `hyp.U`/`hyp.W1` と一致する保証が bare Hypothesis に
無い (reconciliation wall)。⟹ **§15 に lane-c が今 sorry-free に閉じられる work は無い**。

ユーザー裁可 (2026-06-23, option「self-resume で lane-h 待ち」) → lane-c は self-resume monitor を arm して
lane-h の (13.2.a) 着地を待つ。本 issue はその **self-resume トリガ** (trigger b: issue closed) 兼
hub への close 依頼。

## やること

- [ ] (lane-h) Pf (13.2.a)「q<p ⟹ mp.S は type-P2」を証明し、`FeitThompson.lean` で `IsTypeP2 mp.S`
      (or `Section16MaximalPair` の field / 専用 lemma) として main に供給。
- [ ] (lane-c, 自動) self-resume monitor が本 issue の closed/ 移動 (or main の `IsTypeP2 mp.S` 供給) を
      検知 → `git merge main` + step-3 wiring (`exists_typePData_W1_eq_of_isTypeP2` を mp.S に適用 →
      `Section16TypePStructure.Sdata`/`Tdata` → `S15.Hypothesis` enrich → `basic_structure` 他 carrier-gated
      sorry を実証明)。

## 完了条件

**hub or lane-h**: lane-h の (13.2.a) (= main の `FeitThompson.lean` に `IsTypeP2 mp.S` 供給) が merge
されたら、**本 issue を `issues/closed/` へ移動** (`git mv`)。これで lane-c の self-resume monitor
(cron, trigger b) が検知して step-3 wiring を自動再開する。

(lane-c 側のフォールバック検知: main の `FeitThompson.lean` に `IsTypeP2 mp.S` を CONCLUDE する非コメント
宣言が現れたら着地とみなす。)

## 参照

- relane #4: `issues/closed/4009-hub-s16-pair-typep2-determination.md`, `notes/meta/merge_monitor.md` (relane #4 note)
- carrier 機構: `OddOrder/FeitThompson.lean` (`exists_typePData_W1_eq_of_isTypeP2` 他)
- deep dive 確定: `notes/peterfalvi/s15_s_and_t.md`「確定 (2026-06-23 続)」節, commit `b487a888`
- self-resume 手順: `notes/meta/lane_self_resume.md`

---

## 解決 (2026-06-23, hub — self-resume トリガ release)

lane-h の Pf (13.2.a) が **main に landing 済** (commit `6ba0bce5`、relane #4): `isTypeP2_of_typeP_kappaHall_lt`
proved + `Section16MaximalPair.S_typeP2` field + producer fill ⟹ **`mp.S_typeP2` (IsTypeP2 mp.S) が
FeitThompson.lean で available**。トリガ条件 (mp の IsTypeP2 mp.S 供給) 達成。

**hub が本 issue を `issues/closed/` へ移動** → lane-c の self-resume monitor (cron, trigger b = issue closed)
が検知して `git merge main` + **step-3 wiring** (`exists_typePData_W1_eq_of_isTypeP2` を mp.S に適用 →
`Section16TypePStructure.Sdata`/`Tdata` → `S15.Hypothesis` → `basic_structure` 他 carrier-gated sorry を実証明)
を自動再開する。CLOSED。
