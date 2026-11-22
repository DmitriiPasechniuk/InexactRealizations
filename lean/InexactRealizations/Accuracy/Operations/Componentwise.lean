import InexactRealizations.Accuracy.Execution.Stage

/-! Literal componentwise error records and the proved conversion to
normwise operation bounds. Each individual operation is quantified;
there is no premise about a local residual or terminal error. 
-/
namespace InexactRealizations.Accuracy.Componentwise
noncomputable section
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

structure QueryStep (x average : V) (prepared u : ℝ) where
  start : V
  difference : V
  product : V
  result : V
  start_error : ∀ i, |start i - (average) i| ≤ u * |(average) i|
  difference_error : ∀ i, |difference i - (x - start) i| ≤ u * |(x - start) i|
  product_error : ∀ i, |product i - (prepared • difference) i| ≤ u * |(prepared • difference) i|
  result_error : ∀ i, |result i - (start + product) i| ≤ u * |(start + product) i|

def QueryStep.toNormed {x average : V} {prepared u : ℝ}
    (v : QueryStep x average prepared u) (hu : 0 ≤ u) :
    InexactRealizations.Accuracy.QueryStep x average prepared u where
  start := v.start
  difference := v.difference
  product := v.product
  result := v.result
  start_error := componentwise_relative_norm _ _ hu v.start_error
  difference_error := componentwise_relative_norm _ _ hu v.difference_error
  product_error := componentwise_relative_norm _ _ hu v.product_error
  result_error := componentwise_relative_norm _ _ hu v.result_error

structure RecoveryStep (g previous : V) (prepared u : ℝ) where
  difference : V
  quotient : V
  result : V
  difference_error : ∀ i, |difference i - (g - previous) i| ≤ u * |(g - previous) i|
  quotient_error : ∀ i, |quotient i - (prepared⁻¹ • difference) i| ≤ u * |(prepared⁻¹ • difference) i|
  result_error : ∀ i, |result i - (previous + quotient) i| ≤ u * |(previous + quotient) i|

def RecoveryStep.toNormed {g previous : V} {prepared u : ℝ}
    (v : RecoveryStep g previous prepared u) (hu : 0 ≤ u) :
    InexactRealizations.Accuracy.RecoveryStep g previous prepared u where
  difference := v.difference
  quotient := v.quotient
  result := v.result
  difference_error := componentwise_relative_norm _ _ hu v.difference_error
  quotient_error := componentwise_relative_norm _ _ hu v.quotient_error
  result_error := componentwise_relative_norm _ _ hu v.result_error

structure BlendStep (x previous : V) (prepared u : ℝ) where
  difference : V
  product : V
  result : V
  difference_error : ∀ i, |difference i - (x - previous) i| ≤ u * |(x - previous) i|
  product_error : ∀ i, |product i - (prepared • difference) i| ≤ u * |(prepared • difference) i|
  result_error : ∀ i, |result i - (previous + product) i| ≤ u * |(previous + product) i|

def BlendStep.toNormed {x previous : V} {prepared u : ℝ}
    (v : BlendStep x previous prepared u) (hu : 0 ≤ u) :
    InexactRealizations.Accuracy.BlendStep x previous prepared u where
  difference := v.difference
  product := v.product
  result := v.result
  difference_error := componentwise_relative_norm _ _ hu v.difference_error
  product_error := componentwise_relative_norm _ _ hu v.product_error
  result_error := componentwise_relative_norm _ _ hu v.result_error

structure CompensatedStep (x average correction : V) (phi prepared u : ℝ) where
  difference : V
  corrected : V
  product : V
  a : V
  c : V
  d : V
  nextCorrection : V
  difference_error : ∀ i, |difference i - (x - average) i| ≤ u * |(x - average) i|
  corrected_error : ∀ i, |corrected i - (difference - correction) i| ≤ u * |(difference - correction) i|
  product_error : ∀ i, |product i - (prepared • corrected) i| ≤ u * |(prepared • corrected) i|
  a_error : ∀ i, |a i - (correction + product) i| ≤ u * |(correction + product) i|
  c_error : ∀ i, |c i - (average + a) i| ≤ u * |(average + a) i|
  d_error : ∀ i, |d i - (c - average) i| ≤ u * |(c - average) i|
  correction_error : ∀ i, |nextCorrection i - (a - d) i| ≤ u * |(a - d) i|

def CompensatedStep.toNormed {x average correction : V} {phi prepared u : ℝ}
    (v : CompensatedStep x average correction phi prepared u) (hu : 0 ≤ u) :
    InexactRealizations.Accuracy.CompensatedStep x average correction phi prepared u where
  difference := v.difference
  corrected := v.corrected
  product := v.product
  a := v.a
  c := v.c
  d := v.d
  nextCorrection := v.nextCorrection
  difference_error := componentwise_relative_norm _ _ hu v.difference_error
  corrected_error := componentwise_relative_norm _ _ hu v.corrected_error
  product_error := componentwise_relative_norm _ _ hu v.product_error
  a_error := componentwise_relative_norm _ _ hu v.a_error
  c_error := componentwise_relative_norm _ _ hu v.c_error
  d_error := componentwise_relative_norm _ _ hu v.d_error
  correction_error := componentwise_relative_norm _ _ hu v.correction_error

structure PrefixStep (x previous gradient : V) (alphaHat betaHat u : ℝ) where
  onePlusBeta : ℝ
  currentProduct : V
  previousProduct : V
  difference : V
  gradientProduct : V
  result : V
  one_error : |onePlusBeta - (1 + betaHat)| ≤ u * |1 + betaHat|
  current_error : ∀ i, |currentProduct i - (onePlusBeta • x) i| ≤ u * |(onePlusBeta • x) i|
  previous_error : ∀ i, |previousProduct i - (betaHat • previous) i| ≤ u * |(betaHat • previous) i|
  difference_error : ∀ i, |difference i - (currentProduct - previousProduct) i| ≤ u * |(currentProduct - previousProduct) i|
  gradient_error : ∀ i, |gradientProduct i - (alphaHat • gradient) i| ≤ u * |(alphaHat • gradient) i|
  result_error : ∀ i, |result i - (difference - gradientProduct) i| ≤ u * |(difference - gradientProduct) i|

def PrefixStep.toNormed {x previous gradient : V} {alphaHat betaHat u : ℝ}
    (v : PrefixStep x previous gradient alphaHat betaHat u) (hu : 0 ≤ u) :
    InexactRealizations.Accuracy.PrefixStep x previous gradient alphaHat betaHat u where
  onePlusBeta := v.onePlusBeta
  currentProduct := v.currentProduct
  previousProduct := v.previousProduct
  difference := v.difference
  gradientProduct := v.gradientProduct
  result := v.result
  one_error := v.one_error
  current_error := componentwise_relative_norm _ _ hu v.current_error
  previous_error := componentwise_relative_norm _ _ hu v.previous_error
  difference_error := componentwise_relative_norm _ _ hu v.difference_error
  gradient_error := componentwise_relative_norm _ _ hu v.gradient_error
  result_error := componentwise_relative_norm _ _ hu v.result_error

end
end InexactRealizations.Accuracy.Componentwise
