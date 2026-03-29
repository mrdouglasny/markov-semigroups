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

-- Consequences
import MarkovSemigroups.Convergence.SpectralGap
import MarkovSemigroups.Convergence.RelativeEntropy
import MarkovSemigroups.Convergence.Ergodicity
