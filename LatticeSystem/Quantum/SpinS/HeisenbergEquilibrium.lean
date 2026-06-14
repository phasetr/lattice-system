import LatticeSystem.Quantum.SpinS.AndersonTower
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Order.LiminfLimsup

/-!
# Tasaki §4.4: equilibrium states of the Heisenberg model — disorder in one dimension (Theorem 4.22)

For the standard spin-`S` Heisenberg model on the `d`-dimensional hypercubic torus we study the
finite-temperature equilibrium (Gibbs) state.  With the field Hamiltonians (eqs. (4.4.1), (4.4.2))

* ferromagnetic: `Ĥ_h = −Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y − h Σ_x Ŝ_x^{(3)}`  (uniform field `h ∈ ℝ`),
* antiferromagnetic: `Ĥ_h = Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y − h Σ_x (−1)^x Ŝ_x^{(3)}`  (staggered field `h`),

the canonical average at inverse temperature `β = (k_B T)^{-1} ∈ [0, ∞)` is (eq. (4.4.3))
`⟨Â⟩_{β,h}^L = Tr[Â e^{−β Ĥ_h}] / Z_L(β, h)`, `Z_L(β, h) = Tr[e^{−β Ĥ_h}]`.

**Theorem 4.22** says the one-dimensional models are *disordered at any nonzero temperature*:

* (4.4.5) the magnetization vanishes in the iterated limit
  `lim_{h↓0} lim_{L↑∞} ⟨Ŝ_x^{(3)}⟩_{β,h}^L = 0` (no spontaneous symmetry breaking; the order of
  the two limits is essential), for any `β ∈ [0, ∞)`;
* (4.4.6) there exist `ξ(β), C(β) ∈ (0, ∞)` (depending on `S`) with exponential clustering
  `|⟨Ŝ_x^{(α)} Ŝ_y^{(α)}⟩_{β,0}^∞| ≤ C(β) exp(−|x − y| / ξ(β))`, for any `β ∈ [0, ∞)`,
  `α = 1, 2, 3`, `x, y ∈ ℤ`, so the model is in the disordered phase (`ξ(β)` bounds the
  correlation length).

These are proved by standard high-temperature / one-dimensional cluster-expansion (analyticity)
methods (Tasaki [4]); following the project's policy for infinite-volume / finite-temperature
results, we record Theorem 4.22 as two **documented axioms** over the established torus family.  The
finite-temperature framework (`thermalAverageReS`, the two field Hamiltonians) is *defined* here;
per footnote 41 the `L↑∞` limit is taken in the sound `liminf` / subsequence sense (the existence
of the genuine limit is not asserted).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.4, §4.4.1, Theorem 4.22, eqs. (4.4.1)–(4.4.6), pp. 117–119 (footnote 41: rigorously
`liminf` / a suitable subsequence of `L`).
-/

namespace LatticeSystem.Quantum

open Matrix Filter

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## The finite-temperature canonical (Gibbs) average -/

/-- The **Gibbs operator** `e^{−β Ĥ}` at inverse temperature `β : ℝ` for a many-body Hamiltonian
`H : ManyBodyOpS Λ N`, via the matrix exponential. -/
noncomputable def thermalGibbsOpS (β : ℝ) (H : ManyBodyOpS Λ N) : ManyBodyOpS Λ N :=
  NormedSpace.exp ((-(β : ℂ)) • H)

/-- The **partition function** `Z(β) = Tr[e^{−β Ĥ}]` (eq. (4.4.3)). -/
noncomputable def thermalPartitionFnS (β : ℝ) (H : ManyBodyOpS Λ N) : ℂ :=
  (thermalGibbsOpS β H).trace

/-- The **real canonical (Gibbs) average** `⟨Â⟩_{β} = Re Tr[Â e^{−β Ĥ}] / Re Z(β)` (eq. (4.4.3)).
For a Hermitian Hamiltonian `H` the partition function `Z(β) = Tr[e^{−β Ĥ}] > 0` (the exponential of
a Hermitian matrix is positive definite), and for a Hermitian observable `Â` the trace
`Tr[Â e^{−β Ĥ}]` is real, so this real ratio is the genuine quantum-statistical expectation; the
total-function division (`x / 0 = 0`) is harmless since `Z(β) ≠ 0`. -/
noncomputable def thermalAverageReS (β : ℝ) (H A : ManyBodyOpS Λ N) : ℝ :=
  (A * thermalGibbsOpS β H).trace.re / (thermalPartitionFnS β H).re

/-! ## The §4.4 field Hamiltonians (eqs. (4.4.1), (4.4.2)) -/

/-- The **§4.4 field Hamiltonian** on the `d`-dimensional hypercubic torus: when `ferro = true` the
ferromagnetic model with a uniform field (eq. (4.4.1))
`Ĥ_h = −Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y − h Σ_x Ŝ_x^{(3)}`; when `ferro = false` the antiferromagnetic model
with a staggered field (eq. (4.4.2)) `Ĥ_h = Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y − h Σ_x (−1)^x Ŝ_x^{(3)}`, where
`(−1)^x` is the parity sublattice sign. -/
noncomputable def heisenbergFieldHamiltonianS (ferro : Bool) (d L N : ℕ) [NeZero L] (h : ℝ) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  if ferro then
    heisenbergHamiltonianS (fun x y => -torusNNCoupling d L x y) N -
      (h : ℂ) • ∑ x : HypercubicTorus d L, spinSSiteOp3 x N
  else
    heisenbergHamiltonianS (torusNNCoupling d L) N -
      (h : ℂ) • staggeredOrderOpS (torusParitySublattice d L) N

/-! ## Sites, distance, and even-side volume sequence -/

/-- The **canonical embedding** `ℤ^d → (ZMod L)^d` of an infinite-lattice site `x ∈ ℤ^d` into the
torus, coordinatewise by reduction modulo `L`. -/
def torusEmbed (d L : ℕ) (x : Fin d → ℤ) : HypercubicTorus d L := fun i => ((x i : ℤ) : ZMod L)

/-- The **`ℓ¹` lattice distance** `|x − y| = Σ_i |x_i − y_i|` on `ℤ^d` (a real number), the distance
appearing in the exponential clustering bound (4.4.6). -/
def intL1Dist {d : ℕ} (x y : Fin d → ℤ) : ℝ := ∑ i, |((x i - y i : ℤ) : ℝ)|

/-- The **even torus side** `L = 2(n + 1)` indexed by `n : ℕ`: even and `≥ 2`, so the parity (Néel)
sublattice bipartitions consistently (including the wrap-around bonds) and `NeZero L` holds.  The
`L↑∞` limit is taken along this even sequence (a suitable subsequence, footnote 41). -/
def evenSide (n : ℕ) : ℕ := 2 * (n + 1)

/-- The even side `L = 2(n + 1)` is nonzero. -/
instance evenSide_neZero (n : ℕ) : NeZero (evenSide n) := ⟨by unfold evenSide; omega⟩

/-- The **per-axis single-site spin operator** `Ŝ_i^{(α)}` selected by `α : Fin 3`
(`0 ↦ (1)`, `1 ↦ (2)`, `2 ↦ (3)`). -/
noncomputable def spinSSiteOpAxis (α : Fin 3) (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  match α with
  | 0 => spinSSiteOp1 i N
  | 1 => spinSSiteOp2 i N
  | 2 => spinSSiteOp3 i N

/-! ## Finite-volume magnetization and infinite-volume correlation -/

/-- The **finite-volume magnetization** `⟨Ŝ_x^{(3)}⟩_{β,h}^L` at the embedded site `x`, on the even
torus of side `L = 2(n + 1)` (eq. (4.4.5)'s inner observable). -/
noncomputable def finiteVolMagnetizationS (ferro : Bool) (d N : ℕ) (β h : ℝ) (x : Fin d → ℤ)
    (n : ℕ) : ℝ :=
  thermalAverageReS β (heisenbergFieldHamiltonianS ferro d (evenSide n) N h)
    (spinSSiteOp3 (torusEmbed d (evenSide n) x) N)

/-- The **infinite-volume two-spin correlation** `⟨Ŝ_x^{(α)} Ŝ_y^{(α)}⟩_{β,0}^∞` at vanishing field
(eq. (4.4.4)), defined as the `liminf` over the even-volume sequence of the finite-volume
correlations (per footnote 41: the genuine `L↑∞` limit is not known to exist, so we use the sound
`liminf` cluster value). -/
noncomputable def infiniteVolSpinCorrLiminf (ferro : Bool) (d N : ℕ) (β : ℝ) (α : Fin 3)
    (x y : Fin d → ℤ) : ℝ :=
  liminf (fun n : ℕ =>
    thermalAverageReS β (heisenbergFieldHamiltonianS ferro d (evenSide n) N 0)
      (spinSSiteOpAxis α (torusEmbed d (evenSide n) x) N *
        spinSSiteOpAxis α (torusEmbed d (evenSide n) y) N)) atTop

/-! ## Theorem 4.22 -/

/-- **Tasaki Theorem 4.22, eq. (4.4.5) (no SSB in one dimension at any nonzero temperature),
AXIOM.**  For the one-dimensional ferromagnetic (`ferro = true`, uniform field) or antiferromagnetic
(`ferro = false`, staggered field) Heisenberg model with any spin `S = N/2`, the magnetization
vanishes in the iterated limit `lim_{h↓0} lim_{L↑∞} ⟨Ŝ_x^{(3)}⟩_{β,h}^L = 0`, for any
`β ∈ [0, ∞)`.

The order of the limits is essential (outer `h↓0`, inner `L↑∞`).  Stated soundly per footnote 41:
for every `ε > 0` there is a field threshold `δ > 0` such that for every `0 < h < δ` the
finite-volume magnetization is within `ε` of `0` along arbitrarily large even volumes
(`∃ n₀, ∀ n ≥ n₀, ∃ m ≥ n`, capturing the inner `liminf_{L↑∞} = 0`).  This is a small part of much
more general analyticity / cluster-expansion results that hold for any translationally invariant
short-ranged interaction in one dimension (Tasaki [4]). -/
axiom tasaki_4_22_magnetization_vanishes (N : ℕ) (ferro : Bool) (β : ℝ) (hβ : 0 ≤ β)
    (x : Fin 1 → ℤ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ m : ℕ, n ≤ m ∧
        |finiteVolMagnetizationS ferro 1 N β h x m| < ε

/-- **Tasaki Theorem 4.22, eq. (4.4.6) (exponential clustering in one dimension), AXIOM.**  For the
one-dimensional ferromagnetic or antiferromagnetic Heisenberg model with any spin `S = N/2`, and any
`β ∈ [0, ∞)`, there exist a correlation length `ξ(β) ∈ (0, ∞)` and a constant `C(β) ∈ (0, ∞)` such
that the infinite-volume two-spin correlation at vanishing field decays exponentially:
`|⟨Ŝ_x^{(α)} Ŝ_y^{(α)}⟩_{β,0}^∞| ≤ C(β) exp(−|x − y| / ξ(β))`, for every `α = 1, 2, 3` and
`x, y ∈ ℤ`, where `|x − y|` is the `ℓ¹` distance.  Hence the model is in the disordered phase;
`ξ(β)` is an upper bound for the correlation length.  Proved by one-dimensional cluster-expansion
methods
(Tasaki [4]); recorded as a documented axiom (the bound on the concrete `liminf` correlation, with
`ξ, C` existentially quantified as in the book). -/
axiom tasaki_4_22_exponential_clustering (N : ℕ) (ferro : Bool) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ ξ C : ℝ, 0 < ξ ∧ 0 < C ∧ ∀ (α : Fin 3) (x y : Fin 1 → ℤ),
      |infiniteVolSpinCorrLiminf ferro 1 N β α x y| ≤ C * Real.exp (-(intL1Dist x y) / ξ)

end LatticeSystem.Quantum
