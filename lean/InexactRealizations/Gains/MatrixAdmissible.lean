import InexactRealizations.Gains.Matrix
import Mathlib.Analysis.Matrix.Spectrum

namespace InexactRealizations.Analysis
noncomputable section

end
end InexactRealizations.Analysis

namespace InexactRealizations.History
noncomputable section
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual matrix action equals the standard Euclidean linear representation.
Use: transfers matrix symmetry and spectrum to the physical oracle Hessian. 
-/
theorem matrixEnd_eq_toEuclideanLin (H : Matrix d d ℝ) :
    matrixEnd H = Matrix.toEuclideanLin H := rfl

end
end InexactRealizations.History
