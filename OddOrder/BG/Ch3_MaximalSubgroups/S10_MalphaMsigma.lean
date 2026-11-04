/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module -- shake: keep-all

public import OddOrder.BG.Ch3_MaximalSubgroups.S10_HallStructure
public import OddOrder.BG.Ch3_MaximalSubgroups.S10_LocalLemmas
public import OddOrder.BG.Ch3_MaximalSubgroups.S10_BetaRadical
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity.Finset

/-!
# BG §10: M_α / M_σ / M_β (hub)

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994), §10。
入口 hub: Hall 構造 base (`S10_HallStructure`) + 局所補題 (`S10_LocalLemmas`) +
β-radical spine (`S10_BetaRadical`) を束ねる。下流 (§11–) はこの hub を import する。
-/

