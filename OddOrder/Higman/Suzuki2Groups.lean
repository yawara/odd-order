/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import OddOrder.GroupTheory.SpecificGroups.Suzuki2Group.Basic
public import OddOrder.Higman.Suzuki2Groups.AgemoLayers
public import OddOrder.Higman.Suzuki2Groups.HigmanAbelian
public import OddOrder.Higman.Suzuki2Groups.HigmanNormalAbelian
public import OddOrder.Higman.Suzuki2Groups.HigmanNormalCover
public import OddOrder.Higman.Suzuki2Groups.HigmanFrattiniConsequences
public import OddOrder.Higman.Suzuki2Groups.HigmanEndomorphismLift
public import OddOrder.Higman.Suzuki2Groups.HigmanIdempotents
public import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentAction
public import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentFamily
public import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentCovariance
public import OddOrder.Higman.Suzuki2Groups.HigmanKernel
public import OddOrder.Higman.Suzuki2Groups.HigmanImageOrder
public import OddOrder.Higman.Suzuki2Groups.HigmanFinalCase
public import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralGraded
public import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralTransport
public import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralSpectrum
public import OddOrder.Higman.Suzuki2Groups.HigmanSquareMap
public import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralDegreeThree
public import OddOrder.Higman.Suzuki2Groups.HigmanLemmaSix
public import OddOrder.Higman.Suzuki2Groups.HigmanTripleBracketContradiction
public import OddOrder.Higman.Suzuki2Groups.HigmanCoverAbelian
public import OddOrder.Higman.Suzuki2Groups.HigmanCoverPowerOverlap
public import OddOrder.Higman.Suzuki2Groups.HigmanCoverDerivedSeries
public import OddOrder.Higman.Suzuki2Groups.HigmanMaximalNormalAbelian
public import OddOrder.Higman.Suzuki2Groups.HigmanFiniteFieldTrace
public import OddOrder.Higman.Suzuki2Groups.HigmanXiLengthTwo
public import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven
public import OddOrder.Higman.Suzuki2Groups.HigmanTypesCD
public import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve
public import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen
public import OddOrder.Higman.Suzuki2Groups.Classification
public import OddOrder.Higman.Suzuki2Groups.ExponentFour
public import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
public import OddOrder.Higman.Suzuki2Groups.CenterHomocyclic

/-!
# Higman: Suzuki 2-groups

Graham Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
79--96.

This module contains the proof from Higman’s original paper. Peterfalvi,
Appendix III, restates the resulting classification theorem but explicitly
takes its proof from Higman; Peterfalvi-specific restatement and application
data remain under `OddOrder.Peterfalvi.Appendices.Suzuki2Groups`.

Source-neutral definitions and reusable group/representation APIs live under
`OddOrder.GroupTheory` or `OddOrder.Algebra`; paper-specific Lemmas 1--13 and
the classification argument live here.
-/
