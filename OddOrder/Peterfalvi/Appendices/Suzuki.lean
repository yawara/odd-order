/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import OddOrder.Peterfalvi.Appendices.Suzuki.Basic
public import OddOrder.Peterfalvi.Appendices.Suzuki.InvolutionClass
public import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm
public import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
public import OddOrder.Peterfalvi.Appendices.Suzuki.InvertedProduct
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerStructure
public import OddOrder.Peterfalvi.Appendices.Suzuki.FixedPointCentralizer
public import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure
public import OddOrder.Peterfalvi.Appendices.Suzuki.SylowDecomposition
public import OddOrder.Peterfalvi.Appendices.Suzuki.KCyclic
public import OddOrder.Peterfalvi.Appendices.Suzuki.SylowTwo
public import OddOrder.Peterfalvi.Appendices.Suzuki.ActualKActor
public import OddOrder.Peterfalvi.Appendices.Suzuki.ActualCenter
public import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearModel
public import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearIdentification
public import OddOrder.Peterfalvi.Appendices.Suzuki.SemidirectReassociation
public import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearRealization
public import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesis
public import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisPSL
public import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisSuzuki
public import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisPSU
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInduction
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerNormalizer
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerResidual
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerQuotient
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInductionBridge
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerDistinguishedBridge
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSLRoot
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSLDistinguished
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerSuzukiRoot
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerSuzukiDistinguished
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSURoot
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSUDistinguished
public import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
public import OddOrder.Peterfalvi.Appendices.Suzuki.InductionNonSimple
public import OddOrder.Peterfalvi.Appendices.Suzuki.ConjugacyInV
public import OddOrder.Peterfalvi.Appendices.Suzuki.StronglyReal
public import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreePSL
public import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreePSLInduction
public import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreeSuzukiCentralizer
public import OddOrder.Peterfalvi.Appendices.Suzuki.TypeBFromW
public import OddOrder.Peterfalvi.Appendices.Suzuki.WCyclicDivides
public import OddOrder.Peterfalvi.Appendices.Suzuki.Q1MinimalInvariant
public import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.Basic
public import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.FieldAction
public import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepOne

/-!
# Peterfalvi Part II: A Theorem of Suzuki (hub)

Pure re-export hub for the Part II formalization (pp. 97–134): the
topic leaves live in `OddOrder/Peterfalvi/Appendices/Suzuki/`.
-/
