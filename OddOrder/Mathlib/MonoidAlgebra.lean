/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# `MonoidAlgebra` の穴埋め補題

mathlib v4.32 で `MonoidAlgebra R M` は `M →₀ R` の透明な別名でなく、係数を
`MonoidAlgebra.coeff : R[M] → M →₀ R` フィールドに持つ **structure** になった。そのため
「有限和の係数を 1 点で読む」だけで 2 段階かかる:

* `MonoidAlgebra.coeff_sum` で `coeff` を和の内側へ (これは `M →₀ R` の等式)
* `Finsupp.finsetSum_apply` で点に適用

この組み合わせが block 理論のファイル群で頻出するのでここに束ねる。mathlib には片方ずつしか
無く、合成版が欠けている。

* `MonoidAlgebra.coeff_finsetSum`: `(∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m`

将来 mathlib 本体へ寄与する際の配置候補: `Mathlib/Algebra/MonoidAlgebra/Defs.lean`
(`coeff_sum` の直後)。
-/

namespace MonoidAlgebra

variable {R M ι : Type*} [Semiring R]

/-- **有限和の係数は係数の有限和.**

`MonoidAlgebra.coeff_sum` は `M →₀ R` の等式として同じことを述べるが、こちらは既に 1 点で
評価した形 — 単一の係数を計算するときに必要になるのは常にこの形。 -/
theorem coeff_finsetSum (s : Finset ι) (f : ι → MonoidAlgebra R M) (m : M) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  rw [coeff_sum]
  exact Finsupp.finsetSum_apply _ _ _

/-- **`mapDomain` は全射写像に対し全射.**

mathlib には対応する `MonoidAlgebra.mapDomain_injective` が在るが全射版が無い
(`Finsupp.mapDomain_surjective` は `Finsupp` 側だけ)。`MonoidAlgebra` が `Finsupp` の別名で
なくなったので、`Finsupp` 版をそのまま流用することはできない。 -/
theorem mapDomain_surjective {N : Type*} {f : M → N} (hf : Function.Surjective f) :
    Function.Surjective (mapDomain (R := R) f) := fun y => by
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  exact ⟨.ofCoeff x, by rw [mapDomain, coeff_ofCoeff, hx, ofCoeff_coeff]⟩

/-- **`mapDomain` は合成を合成に送る.**

mathlib は束ねた準同型版 (`mapDomainNonUnitalRingHom_comp` 等) しか持たず、素の関数の合成に
対する版が無い。 -/
theorem mapDomain_comp {N O : Type*} {f : M → N} {g : N → O} (x : MonoidAlgebra R M) :
    mapDomain (g ∘ f) x = mapDomain g (mapDomain f x) :=
  congrArg ofCoeff Finsupp.mapDomain_comp

end MonoidAlgebra
