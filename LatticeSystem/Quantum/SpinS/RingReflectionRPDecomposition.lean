/-
The reflection-positive decomposition data and the crossing-bond interaction
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 9).

The Dyson–Lieb–Simon decomposition of a reflection-positive Hamiltonian has the form
`H = H_L + θ(H_L) − Σ_b C_b · θ(C_b)` with `H_L` and every `C_b` left-supported.  The crossing bonds
of the ring antiferromagnet, after the DLS/Marshall gauge (a π-rotation around axis 2 on the right
half), contribute exactly such a negative reflection-positive term.

This file records:

* `crossBondInteractionS x` — the per-bond interaction `Σ_α (Ŝ_x^α · θ(Ŝ_x^α))` at a left site `x`,
  and its gauge identity
  `crossBondInteractionS x = Ŝ_x^1 Ŝ_{r x}^1 − Ŝ_x^2 Ŝ_{r x}^2 + Ŝ_x^3 Ŝ_{r x}^3`
  (the gauged crossing bond), exhibiting the sign pattern that makes the AFM bond RP.
* the left-supportedness of the single-site spin operators `onSiteS x (Ŝ^α)` (`x < n`).
* `RPDecomposition` — the abstract DLS decomposition data — together with the fact that the
  exponential of its (nonnegative multiple of the) interaction term is a reflection-positive trace
  weight (the Gibbs interaction factor), via the interaction-exponential cone.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionExpSupport
import LatticeSystem.Quantum.SpinS.MultiSiteDot

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The single-site spin operator `onSiteS x Ŝ^{(1)}` at a left site is left-supported. -/
theorem onSiteS_spinSOp1_supportedOnLeft {x : Fin (2 * n)} (hx : (x : ℕ) < n) :
    SupportedOnLeftS n N (onSiteS x (spinSOp1 N)) := onSiteS_supportedOnLeft hx _

/-- The single-site spin operator `onSiteS x Ŝ^{(2)}` at a left site is left-supported. -/
theorem onSiteS_spinSOp2_supportedOnLeft {x : Fin (2 * n)} (hx : (x : ℕ) < n) :
    SupportedOnLeftS n N (onSiteS x (spinSOp2 N)) := onSiteS_supportedOnLeft hx _

/-- The single-site spin operator `onSiteS x Ŝ^{(3)}` at a left site is left-supported. -/
theorem onSiteS_spinSOp3_supportedOnLeft {x : Fin (2 * n)} (hx : (x : ℕ) < n) :
    SupportedOnLeftS n N (onSiteS x (spinSOp3 N)) := onSiteS_supportedOnLeft hx _

/-- `θ` on `onSiteS x Ŝ^{(1)}`: the site reflects and the (real) operator is unchanged. -/
theorem ringReflectionThetaS_onSiteS_spinSOp1 (x : Fin (2 * n)) :
    ringReflectionThetaS n N (onSiteS x (spinSOp1 N))
      = onSiteS (ringReflect n x) (spinSOp1 N) := by
  rw [ringReflectionThetaS_onSiteS, spinSOp1_map_conj]

/-- `θ` on `onSiteS x Ŝ^{(3)}`: the site reflects and the (real) operator is unchanged. -/
theorem ringReflectionThetaS_onSiteS_spinSOp3 (x : Fin (2 * n)) :
    ringReflectionThetaS n N (onSiteS x (spinSOp3 N))
      = onSiteS (ringReflect n x) (spinSOp3 N) := by
  rw [ringReflectionThetaS_onSiteS, spinSOp3_map_conj]

/-- `θ` on `onSiteS x Ŝ^{(2)}`: the site reflects and the (imaginary) operator is negated. -/
theorem ringReflectionThetaS_onSiteS_spinSOp2 (x : Fin (2 * n)) :
    ringReflectionThetaS n N (onSiteS x (spinSOp2 N))
      = -onSiteS (ringReflect n x) (spinSOp2 N) := by
  rw [ringReflectionThetaS_onSiteS, spinSOp2_map_conj,
    show (-spinSOp2 N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) = (-1 : ℂ) • spinSOp2 N from
      (neg_one_smul ℂ _).symm, onSiteS_smul, neg_one_smul]

/-- The **crossing-bond interaction** at a left site `x`: the reflection-positive term
`Σ_α Ŝ_x^α · θ(Ŝ_x^α)`. -/
noncomputable def crossBondInteractionS (x : Fin (2 * n)) (N : ℕ) : ManyBodyOpS (Fin (2 * n)) N :=
  onSiteS x (spinSOp1 N) * ringReflectionThetaS n N (onSiteS x (spinSOp1 N))
    + onSiteS x (spinSOp2 N) * ringReflectionThetaS n N (onSiteS x (spinSOp2 N))
    + onSiteS x (spinSOp3 N) * ringReflectionThetaS n N (onSiteS x (spinSOp3 N))

/-- **Gauge identity for the crossing bond.**  The crossing-bond interaction equals the gauged
antiferromagnetic crossing bond between `x` and its reflection `r x`:
`Σ_α Ŝ_x^α θ(Ŝ_x^α) = Ŝ_x^1 Ŝ_{r x}^1 − Ŝ_x^2 Ŝ_{r x}^2 + Ŝ_x^3 Ŝ_{r x}^3`.  The lone minus sign on
the `Ŝ^2` term is the sign flipped by the DLS/Marshall gauge, making all three components contribute
the same (negative) reflection-positive sign to `H`. -/
theorem crossBondInteractionS_eq (x : Fin (2 * n)) :
    crossBondInteractionS x N
      = onSiteS x (spinSOp1 N) * onSiteS (ringReflect n x) (spinSOp1 N)
        - onSiteS x (spinSOp2 N) * onSiteS (ringReflect n x) (spinSOp2 N)
        + onSiteS x (spinSOp3 N) * onSiteS (ringReflect n x) (spinSOp3 N) := by
  rw [crossBondInteractionS, ringReflectionThetaS_onSiteS_spinSOp1,
    ringReflectionThetaS_onSiteS_spinSOp2, ringReflectionThetaS_onSiteS_spinSOp3, mul_neg]
  abel

/-- The crossing-bond interaction is a nonnegative finite combination of `θ(C)·C` generators with
`C` left-supported, hence its exponential (with a nonnegative coefficient) is a reflection-positive
trace weight. -/
theorem crossBondInteractionS_exp_rpTraceWeight {x : Fin (2 * n)} (hx : (x : ℕ) < n) {t : ℝ}
    (ht : 0 ≤ t) : RPTraceWeightS n N (NormedSpace.exp ((t : ℂ) • crossBondInteractionS x N)) := by
  have hC : ∀ i : Fin 3, SupportedOnLeftS n N (![onSiteS x (spinSOp1 N), onSiteS x (spinSOp2 N),
      onSiteS x (spinSOp3 N)] i) := by
    intro i; fin_cases i
    · exact onSiteS_spinSOp1_supportedOnLeft hx
    · exact onSiteS_spinSOp2_supportedOnLeft hx
    · exact onSiteS_spinSOp3_supportedOnLeft hx
  have hkey : (t : ℂ) • crossBondInteractionS x N
      = (t : ℂ) • ∑ i : Fin 3, (1 : ℂ) • (ringReflectionThetaS n N
          (![onSiteS x (spinSOp1 N), onSiteS x (spinSOp2 N), onSiteS x (spinSOp3 N)] i)
        * ![onSiteS x (spinSOp1 N), onSiteS x (spinSOp2 N), onSiteS x (spinSOp3 N)] i) := by
    congr 1
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul]
    rw [crossBondInteractionS,
      (onSiteS_spinSOp1_supportedOnLeft hx).mul_theta_comm (onSiteS_spinSOp1_supportedOnLeft hx),
      (onSiteS_spinSOp2_supportedOnLeft hx).mul_theta_comm (onSiteS_spinSOp2_supportedOnLeft hx),
      (onSiteS_spinSOp3_supportedOnLeft hx).mul_theta_comm (onSiteS_spinSOp3_supportedOnLeft hx)]
  rw [hkey]
  exact rpInteractionExp_reflectionPositive _ hC _ (fun _ => zero_le_one) ht

/-- **Reflection-positive decomposition data** (Dyson–Lieb–Simon form).  A Hamiltonian admits an
RP decomposition when it can be written `H_L + θ(H_L) − Σ_b C_b · θ(C_b)` with `H_L` and every `C_b`
left-supported. -/
structure RPDecomposition (n N : ℕ) where
  /-- The left-supported part `H_L`. -/
  hLeft : ManyBodyOpS (Fin (2 * n)) N
  /-- `H_L` is left-supported. -/
  hLeftSupported : SupportedOnLeftS n N hLeft
  /-- The index type of the crossing bonds. -/
  bondιType : Type
  /-- The crossing bonds form a finite family. -/
  bondFintype : Fintype bondιType
  /-- The left-supported crossing operators `C_b`. -/
  bondOp : bondιType → ManyBodyOpS (Fin (2 * n)) N
  /-- Each `C_b` is left-supported. -/
  bondSupported : ∀ b, SupportedOnLeftS n N (bondOp b)

namespace RPDecomposition

variable (D : RPDecomposition n N)

/-- The interaction term `Σ_b C_b · θ(C_b)` of the decomposition. -/
noncomputable def interaction : ManyBodyOpS (Fin (2 * n)) N :=
  letI := D.bondFintype
  ∑ b, D.bondOp b * ringReflectionThetaS n N (D.bondOp b)

/-- The Hamiltonian `H_L + θ(H_L) − Σ_b C_b · θ(C_b)` reconstructed from the decomposition. -/
noncomputable def toHamiltonian : ManyBodyOpS (Fin (2 * n)) N :=
  D.hLeft + ringReflectionThetaS n N D.hLeft - D.interaction

/-- **The Gibbs interaction factor is a reflection-positive trace weight.**  For `t ≥ 0` the
exponential `exp (t · Σ_b C_b θ(C_b))` of the decomposition's interaction is a reflection-positive
trace weight — the interaction factor of the Gibbs weight `e^{-βH}` in the DLS argument. -/
theorem interaction_exp_rpTraceWeight {t : ℝ} (ht : 0 ≤ t) :
    RPTraceWeightS n N (NormedSpace.exp ((t : ℂ) • D.interaction)) := by
  letI := D.bondFintype
  have hkey : (t : ℂ) • D.interaction
      = (t : ℂ) • ∑ b, (1 : ℂ) •
          (ringReflectionThetaS n N (D.bondOp b) * D.bondOp b) := by
    congr 1
    rw [interaction]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [one_smul, (D.bondSupported b).mul_theta_comm (D.bondSupported b)]
  rw [hkey]
  exact rpInteractionExp_reflectionPositive _ D.bondSupported _ (fun _ => zero_le_one) ht

end RPDecomposition

end LatticeSystem.Quantum
