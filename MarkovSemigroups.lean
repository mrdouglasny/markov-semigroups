-- Abstract functional inequalities (no geometry)
import MarkovSemigroups.Abstract.DirichletForm
import MarkovSemigroups.Abstract.Poincare
import MarkovSemigroups.Abstract.LogSobolev
import MarkovSemigroups.Abstract.HolleyStroock
import MarkovSemigroups.Abstract.Hypercontractivity
import MarkovSemigroups.Abstract.Concentration

-- Diffusion semigroups (Riemannian structure)
import MarkovSemigroups.Diffusion.CarreDuChamp
import MarkovSemigroups.Diffusion.BakryEmery
import MarkovSemigroups.Diffusion.OrnsteinUhlenbeck
import MarkovSemigroups.Diffusion.InvariantMeasure

-- Concrete instances (sorry-free)
import MarkovSemigroups.Instances.Torus
import MarkovSemigroups.Instances.GFFIdentification
import MarkovSemigroups.Instances.BrascampLieb

-- Work-in-progress instances (contain sorries — see README)
import MarkovSemigroups.Instances.WorkInProgress.Euclidean
import MarkovSemigroups.Instances.WorkInProgress.TwoPoint

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
import MarkovSemigroups.Dobrushin.NeumannSeries

-- Dobrushin–Zegarlinski for continuous spin systems (gradient interaction)
import MarkovSemigroups.DobrushinZegarlinski.AbstractInfluence
import MarkovSemigroups.DobrushinZegarlinski.EntropyChainRule
import MarkovSemigroups.DobrushinZegarlinski.EuclideanTransport
import MarkovSemigroups.DobrushinZegarlinski.InteractionMatrix
import MarkovSemigroups.DobrushinZegarlinski.LocalLSI
import MarkovSemigroups.DobrushinZegarlinski.GlobalLSI
import MarkovSemigroups.DobrushinZegarlinski.EntrywiseCovariance
import MarkovSemigroups.DobrushinZegarlinski.Concentration

-- (Wiener chaos / multivariate Hermite / OU eigenfunctions /
-- polynomial-chaos concentration moved to gaussian-hilbert as
-- GaussianHilbert.* on 2026-05-10. Downstream consumers should
-- import that library directly. See README + docs/AXIOM_AUDIT.md
-- for context.)

-- Consequences
import MarkovSemigroups.Convergence.SpectralGap
import MarkovSemigroups.Convergence.RelativeEntropy
import MarkovSemigroups.Convergence.Ergodicity
import MarkovSemigroups.Convergence.IntegralBounds
import MarkovSemigroups.Convergence.Doeblin
