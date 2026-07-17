import LatticeSystem.Quantum.SpinS.LiebSchultzMattis
import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra
import LatticeSystem.Quantum.SpinS.RingDistance

/-!
# Tasaki §6.2: the generalized Lieb–Schultz–Mattis variational bound (Lemma 6.4)

Lemma 6.1 (the low energy of the twisted state) generalizes far beyond the standard
antiferromagnetic Heisenberg chain: it holds for **any** short-ranged, `U(1)`-invariant chain
Hamiltonian
`Ĥ = Σ_{x=1}^{L} ĥ_x`  (eq. (6.2.23)),
where each local term `ĥ_x` acts only on sites within a fixed range `r` of `x` (with periodic
boundary conditions), is bounded `‖ĥ_x‖ ≤ h₀`, and is `U(1)`-invariant,
`(Û_θ^{(3)})† ĥ_x Û_θ^{(3)} = ĥ_x` — equivalently `[ĥ_x, Ŝ_tot^{(3)}] = 0`.

**Lemma 6.4** (eq. (6.2.24)): there is a constant `C > 0`, depending only on `S`, `r` and `h₀`, such
that for *any* ground state `Φ_GS` (uniqueness is **not** assumed) the twisted trial state has
energy `⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ − E_GS ≤ C/L`, for any `L`.

Tasaki further remarks that if `S` is a half-odd integer and the ground state is translation
invariant (`T̂ Φ_GS = e^{iα} Φ_GS`), then *the same orthogonality argument* (a generalization of
Lemma 6.2)
gives `0 ≤ E_1st − E_GS ≤ C/L`, as in Theorem 6.3 — now for a whole class of `U(1)`-invariant
short-ranged chains.  We do **not** formalize that gap consequence here: the formal Lemma 6.2
(`lsm_ground_twist_orthogonal`) is specialized to the antiferromagnetic Heisenberg chain, so
deriving it for a general `IsShortRangeU1Chain` would require a separate generalized orthogonality
lemma.

We record the locality of each `ĥ_x` through the commutant-form locality predicate `IsLocalRangeR`
(`ĥ_x` commutes with every single-site operator farther than `r` from `x`), the norm bound through
the `L²` operator norm `manyBodyOperatorNormS`, and `U(1)`-invariance through
`Commute (ĥ_x) Ŝ_tot^{(3)}`, all bundled into `IsShortRangeU1Chain`.  Lemma 6.4 itself (the `C/L`
variational bound, eq. (6.2.24)) is the documented axiom recorded here.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, Lemma 6.4, eqs. (6.2.23)–(6.2.24), pp. 162–163.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Locality marker (commutant form)** `IsLocalRangeR L N r x op`: the operator `op` acts only on
the sites within ring-distance `r` of `x` on `Fin L` (periodic boundary conditions), recorded as the
commutant condition that `op` commutes with *every* single-site operator `onSiteS y A` placed at a
site `y` strictly farther than `r` from `x`.  For a full matrix algebra this is equivalent, by the
factor double-commutant theorem, to `support(op) ⊆ {y : ringDist L x y ≤ r}`, so it is genuine
spatial locality (not merely "enough for Lemma 6.4").  The strong commutant form is deliberate: this
predicate is *shared* as the locality hypothesis of the intentional §7.1.3 Theorem 7.3 axiom
(`IsAKLTPerturbation.local_range`); a weaker form would enlarge that hypothesis class and make
`aklt_theorem_7_3` claim more, risking unsoundness.  For `y` within range the condition is vacuous,
so `op` may act arbitrarily on the local window. -/
def IsLocalRangeR (L N r : ℕ) (x : Fin L) (op : ManyBodyOpS (Fin L) N) : Prop :=
  ∀ y : Fin L, r < ringDist L x y →
    ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute op (onSiteS y A)

/-- **A short-ranged `U(1)`-invariant chain** of local terms `ĥ_x` (Tasaki eq. (6.2.23) and the
assumptions below it): each `ĥ_x` is self-adjoint (`hermitian`, so `Ĥ = Σ_x ĥ_x` is a genuine
Hamiltonian), `r`-local (`range`), bounded by `h₀` in the `L²` operator norm (`norm_le`), and
`U(1)`-invariant, i.e. commutes with the total spin `Ŝ_tot^{(3)}` (`u1_comm`). -/
structure IsShortRangeU1Chain (L N r : ℕ) (h₀ : ℝ)
    (h : Fin L → ManyBodyOpS (Fin L) N) : Prop where
  /-- Each local term `ĥ_x` is self-adjoint (Hermitian), so `Σ_x ĥ_x` is a Hermitian Hamiltonian. -/
  hermitian : ∀ x, (h x).IsHermitian
  /-- Each local term `ĥ_x` acts only on sites within range `r` of `x`. -/
  range : ∀ x, IsLocalRangeR L N r x (h x)
  /-- Each local term is bounded in the `L²` operator norm by `h₀`. -/
  norm_le : ∀ x, manyBodyOperatorNormS (h x) ≤ h₀
  /-- Each local term is `U(1)`-invariant: it commutes with the total spin `Ŝ_tot^{(3)}`. -/
  u1_comm : ∀ x, Commute (h x) (totalSpinSOp3 (Fin L) N)

/-- **Tasaki Lemma 6.4 (generalized LSM variational bound), AXIOM.**  For the class of short-ranged
`U(1)`-invariant chain Hamiltonians `Ĥ = Σ_x ĥ_x` (`IsShortRangeU1Chain`, range `r`, bound `h₀`,
spin `S = N/2`), there is a constant `C > 0` — depending only on `N`, `r` and `h₀` — such that for
**any** ground state `Φ_GS` (a nonzero eigenvector at the minimal energy `E_GS`; uniqueness is *not*
assumed) the Lieb–Schultz–Mattis trial state has energy bounded by `C/L` above the ground state
(eq. (6.2.24)):
`⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ − E_GS ≤ C/L`, for any `L`.

The constant `C` is uniform over the volume `L`, the local terms `ĥ`, and the ground state — it
depends only on `S`, `r`, `h₀`.  Tasaki remarks that for half-odd-integer `S` with a
translation-invariant ground state a generalized orthogonality argument then yields
`0 ≤ E_1st − E_GS ≤ C/L` (as in Theorem 6.3); that gap consequence is *not* formalized here (the
formal Lemma 6.2 is Heisenberg-chain-specific).  Recorded as a documented axiom. -/
axiom tasaki_lemma_6_4_general_trial_energy_bound (N r : ℕ) (h₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {L : ℕ} (h : Fin L → ManyBodyOpS (Fin L) N)
      (Φ_GS : (Fin L → Fin (N + 1)) → ℂ) (E_GS : ℝ), 0 < L →
      IsShortRangeU1Chain L N r h₀ h →
      (∑ x : Fin L, h x).mulVec Φ_GS = (E_GS : ℂ) • Φ_GS → Φ_GS ≠ 0 →
      IsGroundEnergy (∑ x : Fin L, h x) E_GS →
      expectationRatioRe (∑ x : Fin L, h x) (lsmTrialState L N Φ_GS) - E_GS ≤ C / (L : ℝ)

/-! ## The centered local twist generator `M̂_x` (Tasaki eqs. (6.2.26)–(6.2.27))

The discharge of Lemma 6.4 reduces the global LSM twist `Û_LSM = exp(−i Σ_y θ_y Ŝ_y^{(3)})`
conjugation of each local term `ĥ_x` to a conjugation by a *local* twist generated on the
range-`r` window `W_x = {y : ringDist L x y ≤ r}` of `x`.  The local generator is *centered*: the
raw linear twist angle `θ_y = 2π(y+1)/L` is replaced by the ring-distance-centered angle
`(2π/L)·δ(x,y)`, `δ(x,y)` the signed cyclic displacement of `y` from `x`.  Centering both keeps the
window generator small (`|(2π/L)δ| ≤ 2πr/L`) — the raw `θ_y − θ̄_x` spread would approach `2π`
across the periodic seam — and differs from the raw window sum only by a multiple of the window spin
`Σ_{y∈W_x} Ŝ_y^{(3)}` (which commutes with `ĥ_x`), so the two generate the same conjugation. -/

/-- The **range-`r` window** `W_x := {y : ringDist L x y ≤ r}` of consecutive ring sites around `x`
on `Fin L` (Tasaki §6.2, eq. (6.2.26)): the local support window of `ĥ_x`.  It is nonempty
(`x ∈ W_x`, since `ringDist L x x = 0 ≤ r`) and contains at most `2r+1` sites. -/
def window (L r : ℕ) (x : Fin L) : Finset (Fin L) :=
  Finset.univ.filter (fun y => ringDist L x y ≤ r)

/-- The **signed cyclic displacement** `δ(x,y)` from `x` to `y` on the ring `Fin L`: the shorter
cyclic arc length taken with a `+` sign when the forward arc `(y − x) mod L` is the shorter one and
a `−` sign otherwise, so that `|δ(x,y)| = ringDist L x y`.  It gives the ring-distance-centered
twist angle `(2π/L)·δ(x,y)` of `y` relative to `x` (Tasaki eq. (6.2.27)), free of the `2π` seam jump
of the raw linear angle `θ_y = 2π(y+1)/L` for windows that wrap around the periodic boundary. -/
def signedRingDisp (L : ℕ) (x y : Fin L) : ℤ :=
  if (y.val + L - x.val) % L ≤ (x.val + L - y.val) % L
    then (((y.val + L - x.val) % L : ℕ) : ℤ)
    else -(((x.val + L - y.val) % L : ℕ) : ℤ)

/-- The **centered local twist generator** `M̂_x := Σ_{y∈W_x} (2π/L)·δ(x,y) · Ŝ_y^{(3)}` (Tasaki
§6.2, eq. (6.2.27)), summed over the range-`r` window `W_x = window L r x` with the
ring-distance-centered angle coefficient `(2π/L)·signedRingDisp L x y`.  It is the local generator
obtained from the global LSM twist generator by restricting to the window and subtracting the common
central angle (a multiple of the window spin, which commutes with `ĥ_x`); exponentiated with `−i` it
gives the local twist operator `Û_x`. -/
noncomputable def localTwistGen (L N r : ℕ) (x : Fin L) : ManyBodyOpS (Fin L) N :=
  ∑ y ∈ window L r x,
    (((2 * Real.pi * (signedRingDisp L x y : ℝ)) / (L : ℝ) : ℝ) : ℂ) • spinSSiteOp3 y N

/-- The centered local twist generator is **Hermitian** (a real-coefficient sum of the Hermitian
on-site `Ŝ^{(3)}` operators), so its `−i`-exponential `Û_x` is unitary. -/
theorem localTwistGen_isHermitian (L N r : ℕ) (x : Fin L) :
    (localTwistGen L N r x).IsHermitian := by
  refine Matrix.isHermitian_sum _ (fun y _ => ?_)
  rw [spinSSiteOp3, Matrix.IsHermitian, Matrix.conjTranspose_smul]
  rw [(onSiteS_isHermitian y (spinSOp3_isHermitian N)).eq, Complex.star_def, Complex.conj_ofReal]

/-- The **local twist operator** `Û_x := exp(−i M̂_x)` generated by the centered local twist
generator `M̂_x = localTwistGen L N r x` (Tasaki §6.2, the local factor of `Û_LSM` after the
far-window and central-angle factors are removed, eqs. (6.2.26)–(6.2.27)). -/
noncomputable def localTwistOperator (L N r : ℕ) (x : Fin L) : ManyBodyOpS (Fin L) N :=
  NormedSpace.exp (-Complex.I • localTwistGen L N r x)

/-- The **local twist operator's adjoint** is `Û_x† = exp(+i M̂_x)`, since `M̂_x` is Hermitian
(the generic `conjTranspose_exp_neg_I_smul_of_isHermitian`). -/
theorem localTwistOperator_conjTranspose (L N r : ℕ) (x : Fin L) :
    (localTwistOperator L N r x).conjTranspose
      = NormedSpace.exp (Complex.I • localTwistGen L N r x) := by
  rw [localTwistOperator]
  exact conjTranspose_exp_neg_I_smul_of_isHermitian (localTwistGen_isHermitian L N r x)

/-- The **local twist operator is unitary**: `Û_x† Û_x = 1` (the generic
`conjTranspose_mul_exp_neg_I_smul_of_isHermitian`). -/
theorem localTwistOperator_unitary (L N r : ℕ) (x : Fin L) :
    (localTwistOperator L N r x).conjTranspose * localTwistOperator L N r x = 1 := by
  rw [localTwistOperator]
  exact conjTranspose_mul_exp_neg_I_smul_of_isHermitian (localTwistGen_isHermitian L N r x)

/-- The **local twist operator is unitary**: `Û_x Û_x† = 1` (the companion identity, generic
`exp_neg_I_smul_mul_conjTranspose_of_isHermitian`). -/
theorem localTwistOperator_unitary' (L N r : ℕ) (x : Fin L) :
    localTwistOperator L N r x * (localTwistOperator L N r x).conjTranspose = 1 := by
  rw [localTwistOperator]
  exact exp_neg_I_smul_mul_conjTranspose_of_isHermitian (localTwistGen_isHermitian L N r x)

end LatticeSystem.Quantum
