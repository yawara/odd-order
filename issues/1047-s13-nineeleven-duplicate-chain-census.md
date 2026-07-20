---
id: 1047
slug: s13-nineeleven-duplicate-chain-census
title: "§13 の (9.11) 重複チェーン (~3.8k 行) の棚卸し"
created: 2026-07-20
---

# §13 の (9.11) 重複チェーン (~3.8k 行) の棚卸し

issue 1045 (close 済) で `S13.coherent_sOf_H0Cprime` が
`S11.nineEleven_coherent_A0` の系になった (`coherent_sOf_H0Cprime_of_section9`)。
その結果、旧 §13 チェーンは**同じ命題の 2 本目の証明**になった。

## 対象 (旧 §13 チェーン)

| 宣言 | 場所 | 規模 |
|---|---|---|
| `coherent_sOf_H0Cprime_of_sevenEightRefutation` | `S13_Orthogonality.lean` | 小 |
| `coherent_sOf_H0Cprime_of_equality_refutation` | 同 | 小 |
| `nineElevenSevenEightRefutation` + `NineElevenSevenEightRefutation` | `S11_NineElevenPairAdjoin.lean` | ~420 行 |
| `nineElevenEqualityRefutation_of_sevenEightRefutation` / `nineElevenNormBound_of_sevenEightRefutation` | `S11_NineElevenAlphaBound.lean` | ~310 行 |
| `nineElevenPairBound` / `caseA_sTwo_subset_degreeQaCut` / `caseA_nineElevenThree_count_inputs` / `caseA_nineElevenFour_norm_inputs` / `caseA_nineElevenTwo_tiWitness` ほか | `S11_NineElevenCaseA.lean` | ~1.3k 行 |
| `coherent_extension_eq_sum_memberRFamily` / `coherent_extension_cross_orthogonal` | `S11_NineElevenPairAdjoin.lean` | ~200 行 |

いずれも §9 側に型仮定ゼロの対応物が在る (`S11.caseA_*` / `S11.sOf_coherent_extension_*`)。

## やること — ⚠ **宣言ごとに consumer を実測してから**

1. 各宣言について `grep -rn "<name>"` で **docstring 参照でない実引用**を数える。
   特に §15 の S/T ミラー (`S15_NineElevenSevenEight{,T}.lean` / `S15_CaseACoherence{,T}.lean`) は
   §13 版を**名前で cite しているだけ**か、実際に呼んでいるかを区別すること。
2. 実引用ゼロの宣言のみ削除。AxiomsCheck の該当エントリも同時に外す。
3. §15 ミラーが §13 版を実際に呼んでいる場合は、§9 版へ差し替えられるかを別途判断
   (S/T 側は `sSet` 上で、M 側の `sOf` とは族が違うので自動ではない)。
4. 削除のたびに full build + AxiomsCheck。

## 判断の根拠 (削除してよい理由)

CLAUDE.md「ラッパー方針」の同じ原則: 同じ事実の証明が 2 本あると mathlib API 変更時に
追従が分裂する。§9 版は**厳密に一般** (型仮定ゼロ・型 II を含む) なので、§13 版を残す理由は
「§13 の packaging から直接読める」という可読性だけ。その可読性は
`coherent_sOf_H0Cprime_of_section9` の docstring が担う。

⚠ ただし**これは genuine な形式化の削除ではなく重複の解消**である点を混同しないこと。
迷ったら残す (削除は可逆だが、誤って live な chain を切ると下流が壊れる)。

## 完了条件

実引用ゼロと確認された宣言が削除され、full build green + AxiomsCheck OK + sorry 非退行。
残す判断をした宣言は、その理由を本 issue に記録する。

## 参照

- `issues/closed/1045-pf-9-11-section9-level.md`
- `OddOrder/Peterfalvi/S13_Orthogonality.lean` (`coherent_sOf_H0Cprime_of_section9`)
