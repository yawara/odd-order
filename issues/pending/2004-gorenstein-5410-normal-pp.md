---
id: 2004
slug: gorenstein-5410-normal-pp
title: "BG S04: Gorenstein 5.4.10 normal type-(p,p) for cyclic-center odd p-groups (blocks Pf App.B Lemma)"
created: 2026-06-14
---

# BG S04: Gorenstein 5.4.10 normal type-(p,p) for cyclic-center odd p-groups (blocks Pf App.B Lemma)

## 背景

Peterfalvi Appendix B (`OddOrder/Peterfalvi/Appendices/Huppert.lean`) の Lemma
`pGroup_cyclic_fixedPointFree` は唯一の sorry を残す = **irreducible non-cyclic case** (p.136)。
Peterfalvi の証明は冒頭で **[H] Kapitel III, Hilfssatz 7.5** を引く:

> 「p-group `P` が non-cyclic なら, `P` は type `(p,p)` の **normal** subgroup `R ⊴ P` を含む」

これは **Gorenstein 5.4.10** に対応し, 本リポジトリの BG では **明示的に deferred** されている:
`BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` ≈ line 911:

> "The remaining (nonabelian, cyclic-center) case of the *normal* refinement is exactly
> Gorenstein 5.4.10's substance and is deferred."

現状 S04 が提供するのは **abelian-center case** のみ:
`exists_normal_isElementaryAbelian_card_prime_sq_of_prime_sq_dvd_card_omega1Center`
(`p² ∣ |Ω₁(Z(R))|` を要求)。

**致命的な噛み合わせ**: Appendix B の文脈では Schur ([Is] 1.5) で `End_{𝔽_q[P]}(E)` が有限体になり,
`Z(P)` がその単元群の部分群ゆえ **cyclic**。よって `Ω₁(Z(P))` は位数 `p` で `p² ∤ |Ω₁(Z(P))|`,
repo の available lemma は **適用不可** = まさに deferred な cyclic-center case に落ちる。

## やること

- [ ] `S04_PGroupsSmallRank.lean` に Gorenstein 5.4.10 の **cyclic-center (nonabelian) case** を追加:
      `p` odd, `R` finite non-cyclic `p`-group ⟹ `∃ E ⊴ R, E.IsElementaryAbelian p ∧ Nat.card E = p²`
      (abelian-center case と統合して「p odd + non-cyclic ⟹ normal type-(p,p)」の無条件版を出す)。
- [ ] 証明方針: Gorenstein 5.4.10 (cyclic-center の場合, `Z₂(R)`/critical subgroup 経由) を原文参照
      ([[bg-gorenstein-reread-as-isaacs]]: まず Isaacs/mathlib に対応がないか grep — おそらく無し)。

## 完了条件

BG S04 に「p odd 非cyclic ⟹ normal type-(p,p)」の無条件版が landing し,
`Huppert.lean` の `pGroup_cyclic_fixedPointFree` の non-cyclic sorry を解消できる
(残りは Schur⟹field⟹Z(P) cyclic + coprime `Z_p×Z_p` 分解 `E = ⊕ C_E(Tᵢ)`, これは App.B 側で対応)。

## 参照

- `OddOrder/Peterfalvi/Appendices/Huppert.lean` `pGroup_cyclic_fixedPointFree` (non-cyclic sorry)
- `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` ≈L911 (deferral note), L983
  (`exists_normal_isElementaryAbelian_card_prime_sq_of_prime_sq_dvd_card_omega1Center`, abelian-center)
- `references/peterfalvi/06.0_pp_135_136_*.mmd` (Appendix I 原文; p.136 は note `appendices.md` session 2 で復元)
- `notes/peterfalvi/appendices.md` (Lane H 正本)
- **所有権注意**: S04 は BG lane の owner zone。Lane H (Appendices) は編集不可ゆえ本 issue で hub/BG lane に委譲。

## 🧾 pending 移行 (2026-07-02 hub 全体レビュー)

**off-FT-path (App B 経由のみ、consumer 0)** — 唯一の下流 = `Huppert.lean`
`pGroup_cyclic_fixedPointFree` の non-cyclic sorry で、これを cite する Lean consumer は
現状 0 (2026-07-02 grep 確認)。**σ-theory near-field が App B/C を cite する時に再開**。
それまで `issues/pending/` で保留。
