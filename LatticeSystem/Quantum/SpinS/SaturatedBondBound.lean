import LatticeSystem.Quantum.SpinS.GeneralSCasimirSpectrum

/-!
# Tasaki §2.4, eq. (2.4.5): the per-bond upper bound `Ŝ_x · Ŝ_y ≤ S²`

For two distinct sites carrying spin `S = N/2`, the Heisenberg bond operator satisfies
`S² · 1 − Ŝ_x · Ŝ_y ≥ 0`, i.e. `S²` is the largest eigenvalue of `Ŝ_x · Ŝ_y`.  Tasaki states
this on p. 32 without proof, right after computing `−Ŝ_x·Ŝ_y |Φ↑⟩ = −S² |Φ↑⟩` (eq. (2.4.5)),
and combines it with Lemma A.9 (p. 469) to read off the ferromagnetic ground-state energy
`E_GS = −|B| S²`.

The proof here is the elementary spectral one: the pair Casimir `Ĉ = (Ŝ_x + Ŝ_y)²`
(`bondCasimirS`, affine in `Ŝ_x·Ŝ_y`) has spectrum `{J(J+1) : J = 0,…,2S}`, recorded as the
annihilating polynomial `aeval_nodal_bondCasimirS`, and the degree-one polynomial
`q(t) = N(N+1)/2 − t/2` is nonnegative at every node and evaluates to `S²·1 − Ŝ_x·Ŝ_y` at `Ĉ`.
The Lagrange-interpolation route `posSemidef_aeval_of_aeval_nodal_eq_zero` then gives positivity.
`q` has degree `1`, so the route needs `1 ≤ N` (`S ≥ 1/2`), which is Tasaki's standing assumption
in §2.4; for `N = 0` the whole space is one-dimensional and the statement is off the critical path.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4, eq. (2.4.5) and the text below it, p. 32; Lemma A.9, p. 469.
-/

open Matrix
open scoped ComplexOrder

namespace LatticeSystem.Quantum

open LatticeSystem.Math
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Two-site bond bound** (Tasaki §2.4, eq. (2.4.5) and the text below it, p. 32).  On the
two-site space, `S² · 1 − Ŝ₀ · Ŝ₁` is positive semidefinite for `S = N/2` with `1 ≤ N`: the
degree-one polynomial `q(t) = N(N+1)/2 − t/2` evaluates at the pair Casimir `bondCasimirS 0 1 N`
to exactly this operator and is nonnegative at each Casimir node `J(J+1)`, `J = 0,…,N`. -/
theorem spinSDot_maxSpin_sub_posSemidef_two (hN : 1 ≤ N) :
    ((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS (Fin 2) N)
      - spinSDot (0 : Fin 2) 1 N).PosSemidef := by
  have hC : ∀ c : ℝ, Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 N) (Polynomial.C c)
      = (c : ℂ) • (1 : ManyBodyOpS (Fin 2) N) := fun c => by
    rw [Polynomial.aeval_C, IsScalarTower.algebraMap_apply ℝ ℂ (ManyBodyOpS (Fin 2) N),
      Algebra.algebraMap_eq_smul_one, Complex.coe_algebraMap]
  have haeval : Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 N)
      (Polynomial.C (-(1 / 2) : ℝ) * Polynomial.X
        + Polynomial.C (((N : ℝ) * ((N : ℝ) + 1)) / 2))
      = ((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS (Fin 2) N)
        - spinSDot (0 : Fin 2) 1 N) := by
    rw [map_add, map_mul, hC, hC, Polynomial.aeval_X, smul_mul_assoc, one_mul, bondCasimirS]
    push_cast
    match_scalars <;> ring
  rw [← haeval]
  refine posSemidef_aeval_of_aeval_nodal_eq_zero (bondCasimirS_isHermitian _ _ _)
    (casimirNode_injective N) (aeval_nodal_bondCasimirS N) ?_ fun J => ?_
  · rw [Polynomial.degree_linear (by norm_num : (-(1 / 2) : ℝ) ≠ 0), Fintype.card_fin]
    exact_mod_cast Nat.cast_lt.mpr (show 1 < N + 1 by omega)
  · rw [casimirNode]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hJle : ((J : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp J.isLt
    have hJ0 : (0 : ℝ) ≤ ((J : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- **Bond bound on a general vertex set** (Tasaki §2.4, eq. (2.4.5) and the text below it,
p. 32).  For distinct sites `x ≠ y` of `Λ`, `S² · 1 − Ŝ_x · Ŝ_y` is positive semidefinite when
`1 ≤ N`.  The bond operator is the two-site block embedding `onEmbS ![x, y]`
(`spinSDot_eq_onEmbS`), and `onEmbS` preserves the identity, scalar multiples, differences and
positive semidefiniteness, so the two-site bound transports verbatim. -/
theorem spinSDot_maxSpin_sub_posSemidef (hN : 1 ≤ N) {x y : Λ} (hxy : x ≠ y) :
    ((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS Λ N) - spinSDot x y N).PosSemidef := by
  have hemb : ((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS Λ N) - spinSDot x y N)
      = onEmbS ![x, y] ((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS (Fin 2) N)
        - spinSDot (0 : Fin 2) 1 N) := by
    simp only [sub_eq_add_neg, onEmbS_add, onEmbS_neg, onEmbS_smul, onEmbS_one,
      spinSDot_eq_onEmbS hxy N]
  rw [hemb]
  exact onEmbS_posSemidef (injective_bondEmb hxy) (spinSDot_maxSpin_sub_posSemidef_two hN)

end LatticeSystem.Quantum
