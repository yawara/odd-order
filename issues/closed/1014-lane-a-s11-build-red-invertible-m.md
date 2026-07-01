---
id: 1014
slug: lane-a-s11-build-red-invertible-m
title: "lane a S11 build-red: hcZeta_induceHU_irreducible に Invertible (Nat.card M) 欠落"
created: 2026-07-01
---

# lane a S11 build-red: hcZeta_induceHU_irreducible に Invertible (Nat.card M) 欠落

## 背景

hub 監視 tick (2026-07-01 ~06:43) で lane a の合流を trial merge → `lake build` が **build-red**:

```
error: OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean:6462:8: failed to synthesize instance of type class
  Invertible ↑(Nat.card ↥M)
```

該当宣言は lane a commit `40eaba00 feat(Pf 9.8.c): M-level induceHU ζ irreducible — I_M=HU skeleton (hIM-gated)`
で追加された `theorem hcZeta_induceHU_irreducible` (S11:6429-)。結論は
`IsIrreducibleCharacter (induceHU data (...))` で **huSub → M** への誘導。
`isIrreducibleCharacter_induce_of_inertia_eq` (または `induceHU` の構成) が
`Invertible (Nat.card ↥M : ℂ)` を要求するが、proof 本体は

```lean
  haveI : Fintype ↥M := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
```

で **huSub 版の `Invertible` haveI しか置いておらず、M 版が欠落**している。

おそらく leaf build (S11 単独) で stale-green を踏んだ (cf. memory `leaf-build-stale-green`):
M の `Invertible` instance が prior elaboration 状態でキャッシュされていて leaf build では通り、
full build (fresh elaboration) で露見した。hub は trial merge を `git merge --abort` し、
main は前 tick green (`781194c7`) に復帰済。

## やること

- [ ] S11:6429 `hcZeta_induceHU_irreducible` の proof 冒頭 (`haveI : Fintype ↥M` の直後) に
      `haveI : Invertible (Nat.card ↥M : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`
      を追加 (huSub 版と同形)。
- [ ] **full build で確認**: `lake build OddOrder OddOrder.AxiomsCheck` が exit 0
      (leaf build だけで green 判定しない — stale-green 再発防止)。
- [ ] 必要なら同 commit 群 (`4bbbef61` `Ind_{HU}^M ζ ∈ 𝒮(H₀C)` / `bb5868ec` degree qu /
      `9e3f095d` M-level 3 pieces) の他宣言も M-level instance 不足がないか full build で総点検。

## 完了条件

- main に対し lane a を trial merge → `lake build OddOrder OddOrder.AxiomsCheck` exit 0 +
  "Build completed successfully" + AxiomsCheck OK。hub が通常 tick で自動合流できる状態。

## 参照

- lane a commit `40eaba00` (build-red 導入)
- main green 復帰点 `781194c7`
- memory `leaf-build-stale-green` (leaf build の stale-green 罠 — full build で節目確認)
- `notes/meta/merge_monitor.md` ⛔ STOP プロトコル (build 失敗 → abort + cron 停止 + 報告)


## RESOLVED (2026-07-01, commit 96e9c0a8)

lane a 自身が修正済。原因は報告通りの (1) `Invertible (Nat.card M)` 欠落 **に加え**、
(2) `induceHU` (letI 焼込) vs `ClassFunction.induce` (ambient) の **letI/haveI instance desync**
(haveI=opaque だと defeq せず exact 不成立)。修正 = 全 instance を **letI** で供給 →
`isIrreducibleCharacter_induce_of_inertia_eq` が exact 一発。clean rebuild (rm olean) +
full build (3889 jobs, AxiomsCheck OK) で green 確認。正本 = issue 1012 + memory
lean-induce-transport-instance-desync。stale-green leaf build が build-red を隠していた点に注意。
