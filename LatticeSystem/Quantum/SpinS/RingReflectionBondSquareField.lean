/-
The ring bond-square field Hamiltonian and its reduction to the linear-core field Hamiltonian
(Tasaki §4.1 Theorem 4.2, reflection-positivity bond-square layer, PR-BS1).

Tasaki's field Hamiltonian (4.1.48), book p.86, couples the staggered field *quadratically* inside
the bond-square `½{Ŝ³ₓ + Ŝ³_y − (−1)ˣh_x − (−1)ʸh_y}²`.  The square form is the faithful object; the
linear-core form `ringFieldHamiltonian n N (kOf h) + C(h)·1` is a *proved* identity `(★)`, obtained
by expanding the square, completing the isotropic dot product with the `Ŝ³Ŝ³` cross term,
cancelling the single-ion terms against `−d Σ (Ŝ³ₓ)²` (`d = 1`), and regrouping the linear and
scalar parts.  The scalar constant `C(h) ≥ 0` (proved in PR-BS2) is what repairs the inequality
direction of the reflection bound; `(★)` and Hermiticity are all that PR-BS1 provides.

See `.self-local/docs/math-tasaki-4-1-48-bond-square-reduction.md` (issue #4777).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionFieldPartitionSymmetry
import LatticeSystem.Quantum.SpinS.RingReflectionRightEqTheta

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Staggered field** `f_x = (−1)ˣ h_x` (Tasaki §4.1 (4.1.48), book p.86, the raw staggered field
before folding the sign into the per-site coupling).  The sign convention `even ↦ +1` matches
`ringStaggeredSublattice`. -/
private def ringBondSquareStagField (h : Fin (2 * n) → ℝ) (x : Fin (2 * n)) : ℝ :=
  (-1) ^ (x : ℕ) * h x

/-- **Per-site linear field** `kOf h` consumed by `ringFieldHamiltonian` in the reduction `(★)`:
`kOf h z = −(f_z + f_{z+1}) − (f_{z−1} + f_z) = −(2 f_z + f_{z−1} + f_{z+1})`, the two incident ring
bonds `{z, z+1}` and `{z−1, z}` of site `z` (Tasaki §4.1, `b̃`-field (4.1.38), book p.84, in the
`f`-parametrization).  The predecessor is expressed as the group inverse `z − 1` of the cyclic
successor (`ringBondSucc n (z − 1) = z` on the even ring), so no separate predecessor definition is
introduced. -/
noncomputable def ringBondSquareLinField (n : ℕ) [NeZero n] (h : Fin (2 * n) → ℝ) :
    Fin (2 * n) → ℝ :=
  fun z => -(ringBondSquareStagField h z + ringBondSquareStagField h (ringBondSucc n z))
    - (ringBondSquareStagField h (z - 1) + ringBondSquareStagField h z)

/-- **Scalar constant** `C(h) = ½ Σ_bonds (f_x + f_{x+1})²` of the reduction `(★)` (Tasaki §4.1
(4.1.37)/(4.1.48), book pp.84–86), summed over the `2n` cyclic bonds `{z, z+1}`.  Its
nonnegativity (consumed in PR-BS2 via `e^{−βC} ≤ 1`) is not needed here. -/
noncomputable def ringBondSquareConst (n : ℕ) (h : Fin (2 * n) → ℝ) : ℝ :=
  (1 / 2) * ∑ x : Fin (2 * n),
    (ringBondSquareStagField h x + ringBondSquareStagField h (ringBondSucc n x)) ^ 2

/-- **Ring bond-square field Hamiltonian** (Tasaki §4.1 (4.1.48), book p.86): the isotropic ring
Heisenberg Hamiltonian with the staggered field coupled quadratically inside the bond-square
`½{Ŝ³ₓ + Ŝ³_y − f_x − f_y}²`, minus the single-ion term `Σ_x (Ŝ³ₓ)²` (`d = 1`).  The bond sum runs
over the `2n` directed cyclic bonds `(x, x+1)` via `ringBondSucc`.  This square form is the faithful
object; the equivalent linear-core form is the proved identity
`ringBondSquareFieldHamiltonian_eq`. -/
noncomputable def ringBondSquareFieldHamiltonian (n N : ℕ) (h : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  (∑ x : Fin (2 * n),
      (onSiteS x (spinSOp1 N) * onSiteS (ringBondSucc n x) (spinSOp1 N)
        + onSiteS x (spinSOp2 N) * onSiteS (ringBondSucc n x) (spinSOp2 N)
        + (1 / 2 : ℂ) • (onSiteS x (spinSOp3 N) + onSiteS (ringBondSucc n x) (spinSOp3 N)
            - (ringBondSquareStagField h x : ℂ) • 1
            - (ringBondSquareStagField h (ringBondSucc n x) : ℂ) • 1) ^ 2))
    - ∑ x : Fin (2 * n), onSiteS x (spinSOp3 N) ^ 2

/-- **Per-bond expansion of the bond-square.**  Expanding `½{A − F}²` with the operator
`A = Ŝ³ₓ + Ŝ³_y` and the central scalar `F = f_x + f_y` (`y = x+1`), the `Ŝ³ₓŜ³_y` cross term
completes the isotropic dot product `spinSDot`, leaving two half single-ion terms, a linear field
term `−F(Ŝ³ₓ + Ŝ³_y)`, and the scalar `½F²·1` (Tasaki §4.1 (4.1.48), book p.86).  The cross term is
symmetrised by `onSiteS_mul_onSiteS_of_ne` (`x ≠ x+1`). -/
private theorem ringBondSquare_bondTerm_expand (n N : ℕ) (h : Fin (2 * n) → ℝ) (x : Fin (2 * n))
    (hxy : x ≠ ringBondSucc n x) :
    onSiteS x (spinSOp1 N) * onSiteS (ringBondSucc n x) (spinSOp1 N)
      + onSiteS x (spinSOp2 N) * onSiteS (ringBondSucc n x) (spinSOp2 N)
      + (1 / 2 : ℂ) • (onSiteS x (spinSOp3 N) + onSiteS (ringBondSucc n x) (spinSOp3 N)
          - (ringBondSquareStagField h x : ℂ) • 1
          - (ringBondSquareStagField h (ringBondSucc n x) : ℂ) • 1) ^ 2
      = spinSDot x (ringBondSucc n x) N
        + (1 / 2 : ℂ) • onSiteS x (spinSOp3 N) ^ 2
        + (1 / 2 : ℂ) • onSiteS (ringBondSucc n x) (spinSOp3 N) ^ 2
        - ((ringBondSquareStagField h x + ringBondSquareStagField h (ringBondSucc n x) : ℝ) : ℂ)
            • onSiteS x (spinSOp3 N)
        - ((ringBondSquareStagField h x + ringBondSquareStagField h (ringBondSucc n x) : ℝ) : ℂ)
            • onSiteS (ringBondSucc n x) (spinSOp3 N)
        + ((1 / 2 * (ringBondSquareStagField h x
            + ringBondSquareStagField h (ringBondSucc n x)) ^ 2 : ℝ) : ℂ) • 1 := by
  have hPQ := onSiteS_mul_onSiteS_of_ne (N := N) hxy (spinSOp3 N) (spinSOp3 N)
  rw [spinSDot_def]
  simp only [pow_two, sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul]
  rw [← hPQ]
  push_cast
  module

/-- **Single-ion cancellation** (Tasaki §4.1, book p.86): summed over the ring, each half single-ion
term `½(Ŝ³ₓ)²` appears with degree `2`, so `Σ_x[½(Ŝ³ₓ)² + ½(Ŝ³_{x+1})²] = Σ_x (Ŝ³ₓ)²`, cancelling
the `d = 1` single-ion term of the Hamiltonian.  The `x+1` sum is reindexed by the successor
bijection `ringBondSucc_bijective`. -/
private theorem ringBondSquare_diag_cancel (n N : ℕ) [NeZero n] :
    (∑ x, (1 / 2 : ℂ) • onSiteS x (spinSOp3 N) ^ 2
        + ∑ x, (1 / 2 : ℂ) • onSiteS (ringBondSucc n x) (spinSOp3 N) ^ 2
        : ManyBodyOpS (Fin (2 * n)) N)
      = ∑ x, onSiteS x (spinSOp3 N) ^ 2 := by
  rw [Fintype.sum_bijective (ringBondSucc n) ringBondSucc_bijective
      (fun x => (1 / 2 : ℂ) • onSiteS (ringBondSucc n x) (spinSOp3 N) ^ 2)
      (fun z => (1 / 2 : ℂ) • onSiteS z (spinSOp3 N) ^ 2) (fun _ => rfl),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← add_smul, show (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 by norm_num, one_smul]

/-- **Linear regrouping** (Tasaki §4.1 (4.1.38), book p.84): the two per-bond linear terms collect,
per site `z`, into the field coefficient `kOf h z = ringBondSquareLinField n h z`.  The
target-endpoint sum `Σ_x F_x·Ŝ³_{x+1}` is reindexed by the successor bijection to a per-site sum,
with the predecessor expressed as the group inverse `z − 1`. -/
private theorem ringBondSquare_lin_regroup (n N : ℕ) [NeZero n] (h : Fin (2 * n) → ℝ) :
    (-(∑ x, ((ringBondSquareStagField h x
          + ringBondSquareStagField h (ringBondSucc n x) : ℝ) : ℂ) • onSiteS x (spinSOp3 N))
        - ∑ x, ((ringBondSquareStagField h x
          + ringBondSquareStagField h (ringBondSucc n x) : ℝ) : ℂ)
            • onSiteS (ringBondSucc n x) (spinSOp3 N)
        : ManyBodyOpS (Fin (2 * n)) N)
      = ∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N) := by
  have hsucc : ∀ x : Fin (2 * n), ringBondSucc n x - 1 = x := fun x => by
    rw [ringBondSucc_eq_add_one, add_sub_cancel_right]
  have hE : (∑ x, ((ringBondSquareStagField h x
        + ringBondSquareStagField h (ringBondSucc n x) : ℝ) : ℂ)
          • onSiteS (ringBondSucc n x) (spinSOp3 N))
      = ∑ z, ((ringBondSquareStagField h (z - 1)
          + ringBondSquareStagField h z : ℝ) : ℂ) • onSiteS z (spinSOp3 N) := by
    refine Fintype.sum_bijective (ringBondSucc n) ringBondSucc_bijective _ _ (fun x => ?_)
    rw [hsucc x]
  rw [hE, Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) =>
      show (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)
        = -(((ringBondSquareStagField h z
              + ringBondSquareStagField h (ringBondSucc n z) : ℝ) : ℂ) • onSiteS z (spinSOp3 N))
          - ((ringBondSquareStagField h (z - 1)
              + ringBondSquareStagField h z : ℝ) : ℂ) • onSiteS z (spinSOp3 N)
        from by
          simp only [ringBondSquareLinField]
          push_cast
          module),
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- **Reduction identity `(★)`** (Tasaki §4.1 (4.1.48), book p.86): the bond-square field
Hamiltonian equals the linear-core field Hamiltonian at the regrouped field `ringBondSquareLinField`
plus the scalar constant `ringBondSquareConst`.  Proved by per-bond expansion
(`ringBondSquare_bondTerm_expand`), single-ion cancellation (`ringBondSquare_diag_cancel`), linear
regrouping (`ringBondSquare_lin_regroup`), and factoring the scalar constant.  This is the sole
load-bearing algebraic content feeding the reflection-positivity chain (PR-BS2 onward). -/
theorem ringBondSquareFieldHamiltonian_eq (n N : ℕ) [NeZero n] (h : Fin (2 * n) → ℝ) :
    ringBondSquareFieldHamiltonian n N h
      = ringFieldHamiltonian n N (ringBondSquareLinField n h)
        + (ringBondSquareConst n h : ℂ) • 1 := by
  have hxy : ∀ x : Fin (2 * n), x ≠ ringBondSucc n x := by
    intro x hx
    have hv := congrArg Fin.val hx
    rw [ringBondSucc_val] at hv
    have hlt := x.isLt
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    rcases Nat.lt_or_ge (x.val + 1) (2 * n) with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at hv; omega
    · have hz : (x.val + 1) % (2 * n) = 0 := by
        rw [show x.val + 1 = 2 * n by omega, Nat.mod_self]
      rw [hz] at hv; omega
  have hconst : (∑ x, ((1 / 2 * (ringBondSquareStagField h x
        + ringBondSquareStagField h (ringBondSucc n x)) ^ 2 : ℝ) : ℂ)
          • (1 : ManyBodyOpS (Fin (2 * n)) N))
      = (ringBondSquareConst n h : ℂ) • 1 := by
    rw [← Finset.sum_smul]
    congr 1
    rw [ringBondSquareConst]
    push_cast
    rw [Finset.mul_sum]
  rw [ringBondSquareFieldHamiltonian,
    Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      ringBondSquare_bondTerm_expand n N h x (hxy x))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [add_assoc (∑ x, spinSDot x (ringBondSucc n x) N), ringBondSquare_diag_cancel n N,
    ← heisenbergHamiltonianS_ringCoupling_eq_bondSum, ringFieldHamiltonian,
    ← ringBondSquare_lin_regroup n N h, ← hconst]
  abel

/-- **The bond-square field Hamiltonian is Hermitian.**  Via the reduction `(★)` it is the sum of
the Hermitian linear-core field Hamiltonian (`ringFieldHamiltonian_isHermitian`) and the real scalar
`ringBondSquareConst·1` (Tasaki §4.1, book p.86). -/
theorem ringBondSquareFieldHamiltonian_isHermitian (n N : ℕ) [NeZero n] (h : Fin (2 * n) → ℝ) :
    (ringBondSquareFieldHamiltonian n N h).IsHermitian := by
  rw [ringBondSquareFieldHamiltonian_eq]
  exact (ringFieldHamiltonian_isHermitian n N _).add
    (Matrix.isHermitian_one.smul (Complex.conj_ofReal _))

end LatticeSystem.Quantum

