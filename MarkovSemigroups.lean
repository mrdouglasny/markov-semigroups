-- Abstract functional inequalities (no geometry)
import MarkovSemigroups.Abstract.DirichletForm
import MarkovSemigroups.Abstract.Poincare
import MarkovSemigroups.Abstract.LogSobolev
import MarkovSemigroups.Abstract.HolleyStroock
import MarkovSemigroups.Abstract.Hypercontractivity

-- Diffusion semigroups (Riemannian structure)
import MarkovSemigroups.Diffusion.CarreDuChamp
import MarkovSemigroups.Diffusion.BakryEmery
import MarkovSemigroups.Diffusion.OrnsteinUhlenbeck
import MarkovSemigroups.Diffusion.InvariantMeasure

-- Concrete instances
import MarkovSemigroups.Instances.Euclidean
import MarkovSemigroups.Instances.Torus
import MarkovSemigroups.Instances.GFFIdentification
import MarkovSemigroups.Instances.BrascampLieb

-- Matrix semigroup theory (diamagnetic inequality)
import MarkovSemigroups.Matrix.HeatKernel
import MarkovSemigroups.Matrix.LaplaceTransform
import MarkovSemigroups.Matrix.Trotter
import MarkovSemigroups.Matrix.Diamagnetic

-- Coupling theory
import MarkovSemigroups.Coupling.TVCoupling

-- Dobrushin uniqueness for lattice spin systems
import MarkovSemigroups.Dobrushin.Specification
import MarkovSemigroups.Dobrushin.Uniqueness
import MarkovSemigroups.Dobrushin.StrongCoupling
import MarkovSemigroups.Dobrushin.FiniteLattice

-- Consequences
import MarkovSemigroups.Convergence.SpectralGap
import MarkovSemigroups.Convergence.RelativeEntropy
import MarkovSemigroups.Convergence.Ergodicity
import MarkovSemigroups.Convergence.IntegralBounds
import MarkovSemigroups.Convergence.Doeblin
