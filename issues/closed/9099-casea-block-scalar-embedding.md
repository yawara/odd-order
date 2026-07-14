---
id: 9099
slug: casea-block-scalar-embedding
title: "SHARED: expose the case-(9.7.a) block-scalar ratio embedding"
created: 2026-07-14
---

# SHARED: expose the case-(9.7.a) block-scalar ratio embedding

## 背景

Peterfalvi (9.7.a) は `U/C_U(H̄)` を `q - 1` 個の巡回スカラー因子の積へ埋め込む。
issue 9098 では同じ比写像を `card_dvd_pow_of_block_scalars` の証明内部に構成し、
位数の divisibility だけを公開した。しかし (14.6) は Sylow 部分群の質的構造を使うため、
cardinality 結論ではなく injective group homomorphism 自体が必要である。

**CLAIM (lane a, 2026-07-14)**: 汎用 block-scalar ratio hom と injectivity を公開し、
実 `CliffordCaseAData` から得る §9 の埋め込みへ接続する。他レーンは同じ比写像を再構築しない。

## やること

- [x] `SemilinearImprimitiveBound` に比準同型と injectivity theorem を公開する。
- [x] 既存の cardinality / divisibility theorem を公開準同型経由へ再配線する。
- [x] `S11_ImprimitiveUBound` に `CliffordCaseAData` 由来の injective hom を公開する。
- [x] target build / AxiomsCheck / full build を通す。

## 完了条件

構造体の署名変更や新しい opaque data を導入せず、(9.7.a) の質的な積埋め込みを
downstream の (14.6) が直接 cite できること。

## 参照

- `issues/closed/9098-casea-block-scalar-divisibility.md`
- `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`, (14.6)
- `coq/theories/PFsection9.v`, `typeP_Galois_Pn`

## 完了報告 (2026-07-14, lane a)

- `blockScalarRatioHom` と injectivity を公開し、cardinality / divisibility 系を同じ写像へ
  再配線した。
- `caseA_exists_blockScalarRatioEmbedding` は実 `CliffordCaseAData` の `q` 個の order-`p`
  summands と Frobenius fixed-point-free 論証から
  `range (uActionHom) ↪ Fin (q - 1) → (ZMod p)ˣ` を構成する。
- `caseA_u_dvd_pred_pow` は公開 embedding の位数整除系になった。構造体署名・opaque data・
  新 axiom の追加はない。
- target build (S11→S15→S16) 4174 jobs、`OddOrder.AxiomsCheck` 4198 jobs、
  `lake build OddOrder` 4213 jobs がすべて成功した。
