import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import DifferentialGeometry.External.DeGiorgi.WholeSpaceSobolev
import DifferentialGeometry.External.DeGiorgi.Poincare
import DifferentialGeometry.External.DeGiorgi.SobolevPoincare
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximation
import DifferentialGeometry.External.DeGiorgi.Holder.PublicEstimate
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients
import DifferentialGeometry.External.DeGiorgi.WeakFormulation
import DifferentialGeometry.External.DeGiorgi.SobolevChainRule

namespace DifferentialGeometry.Sobolev.Euclidean

export DeGiorgi (HasWeakPartialDeriv HasWeakGrad HasWeakDiv)

export DeGiorgi (MemW1p MemW1pWitness MemW01p)

export DeGiorgi (sobolev_smooth sobolev_of_approx C_gns)

export DeGiorgi (C_poinc_val poincare_unitBall_W1p_public)

export DeGiorgi (sobolev_poincare_unitBall)

export DeGiorgi (holder_Moser_of_homogeneousWeakSolution)

export DeGiorgi (EllipticCoeff)

export DeGiorgi (IsHomogeneousWeakSolution IsSolution)

export DeGiorgi (sobolev_chain_rule_unitBall sobolev_chain_rule)

end DifferentialGeometry.Sobolev.Euclidean
