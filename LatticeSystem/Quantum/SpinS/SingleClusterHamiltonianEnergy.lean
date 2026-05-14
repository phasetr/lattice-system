import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Energy real-part / im-part / sign properties for the single-
cluster Heisenberg Hamiltonian (build-speed companion)

Build-speed companion to `SingleClusterHamiltonian.lean`. Hosts
the trailing "energy hygiene" block on
`singleClusterGSEnergyS` / `singleClusterMaxEnergyS` real-part
non-positivity / non-negativity / strict-positivity, imaginary
parts vanishing, real-part formulas at `z = 1`, real-part formulas
at general `z`, the GS–Max gap formula, and the
`_re_lt_*_of_pos` / `_re_neg_of_pos` / `_re_pos_of_pos` strict
ordering theorems (originally lines 778..980 of the pre-#39
parent file).

Splitting these blocks out drops the parent from ~980 lines to
~777 lines.

No external consumers within the repo.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- **GS energy real-part sign** (γ-5 step 272):
`Re(singleClusterGSEnergyS z N) ≤ 0` for all `z, N : ℕ`.

This is the physical AFM ground-state energy bound: an antiferromagnetic
Heisenberg cluster has a non-positive ground-state energy. -/
theorem singleClusterGSEnergyS_re_le_zero (z N : ℕ) :
    (singleClusterGSEnergyS z N).re ≤ 0 := by
  have hcast : singleClusterGSEnergyS z N =
      ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold singleClusterGSEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]
  have h1 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have h2 : (0 : ℝ) ≤ (z : ℝ) * (N : ℝ) / 2 + 1 := by positivity
  nlinarith [mul_nonneg h1 h2]

/-- **Max-Casimir-sector energy real-part sign** (γ-5 step 272):
`0 ≤ Re(singleClusterMaxEnergyS z N)` for all `z, N : ℕ`.

The maximum Casimir sector contains the extremal aligned states `|Φ_⊤⟩`,
`|Φ_⊥⟩`, whose `H`-eigenvalue `z·(N/2)²` is non-negative. -/
theorem singleClusterMaxEnergyS_re_nonneg (z N : ℕ) :
    0 ≤ (singleClusterMaxEnergyS z N).re := by
  have hcast : singleClusterMaxEnergyS z N =
      (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
    unfold singleClusterMaxEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]
  positivity

/-- **GS energy ≤ Max energy** (γ-5 step 273):
`Re(singleClusterGSEnergyS z N) ≤ Re(singleClusterMaxEnergyS z N)`.

Consistency check that the two named eigenvalues from γ-5 steps 268, 269
sit in the correct order: the GS-sector eigenvalue lies (weakly) below
the maximum-Casimir-sector eigenvalue. The gap closes only at `N = 0`
(spin-`0` trivial case). -/
theorem singleClusterGSEnergyS_re_le_singleClusterMaxEnergyS_re (z N : ℕ) :
    (singleClusterGSEnergyS z N).re ≤ (singleClusterMaxEnergyS z N).re := by
  have hg : (singleClusterGSEnergyS z N).re =
      -((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) := by
    have hcast : singleClusterGSEnergyS z N =
        ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
      unfold singleClusterGSEnergyS; push_cast; ring
    rw [hcast, Complex.ofReal_re]
  have hm : (singleClusterMaxEnergyS z N).re =
      (z : ℝ) * (N : ℝ) ^ 2 / 4 := by
    have hcast : singleClusterMaxEnergyS z N =
        (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
      unfold singleClusterMaxEnergyS; push_cast; ring
    rw [hcast, Complex.ofReal_re]
  rw [hg, hm]
  have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (z : ℝ) * (N : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg h1 h2]

/-- **GS energy is real** (γ-5 step 274):
`Im(singleClusterGSEnergyS z N) = 0`. The Hermitian Hamiltonian has
real eigenvalues, in particular the Tasaki Problem 2.5.a target. -/
theorem singleClusterGSEnergyS_im_zero (z N : ℕ) :
    (singleClusterGSEnergyS z N).im = 0 := by
  have hcast : singleClusterGSEnergyS z N =
      ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold singleClusterGSEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_im]

/-- **Max-Casimir-sector energy is real** (γ-5 step 274):
`Im(singleClusterMaxEnergyS z N) = 0`. -/
theorem singleClusterMaxEnergyS_im_zero (z N : ℕ) :
    (singleClusterMaxEnergyS z N).im = 0 := by
  have hcast : singleClusterMaxEnergyS z N =
      (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
    unfold singleClusterMaxEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_im]

/-- **Dimer (z=1) ground-state energy** (γ-5 step 275):
`singleClusterGSEnergyS 1 N = −(N/2)·(N/2 + 1) = −S(S+1)` for `S = N/2`.

The canonical singlet eigenvalue of `Ŝ_0 · Ŝ_1` for two spin-`S` sites,
specialisation of γ-5 step 270 at `z = 1`. -/
theorem singleClusterGSEnergyS_one_eq (N : ℕ) :
    singleClusterGSEnergyS 1 N = -((N : ℂ) / 2) * ((N : ℂ) / 2 + 1) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Dimer (z=1) maximum-Casimir-sector energy** (γ-5 step 275):
`singleClusterMaxEnergyS 1 N = (N/2)² = S²` for `S = N/2`.

The canonical triplet eigenvalue of `Ŝ_0 · Ŝ_1` for two spin-`S` sites,
specialisation of γ-5 step 271 at `z = 1`. -/
theorem singleClusterMaxEnergyS_one_eq (N : ℕ) :
    singleClusterMaxEnergyS 1 N = ((N : ℂ) / 2) ^ 2 := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Trivial GS energy at N=0** (γ-5 step 276):
`singleClusterGSEnergyS z 0 = 0`. The spin-0 trivial case. -/
@[simp] theorem singleClusterGSEnergyS_zero_right (z : ℕ) :
    singleClusterGSEnergyS z 0 = 0 := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Trivial max-Casimir-sector energy at N=0** (γ-5 step 276):
`singleClusterMaxEnergyS z 0 = 0`. The spin-0 trivial case. -/
@[simp] theorem singleClusterMaxEnergyS_zero_right (z : ℕ) :
    singleClusterMaxEnergyS z 0 = 0 := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Trivial max-Casimir-sector energy at z=0** (γ-5 step 276):
`singleClusterMaxEnergyS 0 N = 0`. The single-site cluster (no leaves)
case. -/
@[simp] theorem singleClusterMaxEnergyS_zero_left (N : ℕ) :
    singleClusterMaxEnergyS 0 N = 0 := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **GS energy real-part closed form** (γ-5 step 278):
`Re(singleClusterGSEnergyS z N) = -(N/2)·(zN/2 + 1)` as an `ℝ` value.

Useful as a simp lemma for downstream real comparisons. -/
theorem singleClusterGSEnergyS_re_eq (z N : ℕ) :
    (singleClusterGSEnergyS z N).re =
      -((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) := by
  have hcast : singleClusterGSEnergyS z N =
      ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold singleClusterGSEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- **Max-Casimir-sector energy real-part closed form** (γ-5 step 278):
`Re(singleClusterMaxEnergyS z N) = z·N²/4` as an `ℝ` value. -/
theorem singleClusterMaxEnergyS_re_eq (z N : ℕ) :
    (singleClusterMaxEnergyS z N).re = (z : ℝ) * (N : ℝ) ^ 2 / 4 := by
  have hcast : singleClusterMaxEnergyS z N =
      (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
    unfold singleClusterMaxEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- **GS-Max energy gap** (γ-5 step 280):
`singleClusterMaxEnergyS z N - singleClusterGSEnergyS z N = (N/2)(zN+1) = S(2zS+1)`
for spin `S = N/2`.

Closed form for the energy difference between the two named eigenvalues
of γ-5 steps 270, 271. The gap is non-negative and grows linearly in
both `z` and `N²`. -/
theorem singleClusterMaxEnergyS_sub_singleClusterGSEnergyS (z N : ℕ) :
    singleClusterMaxEnergyS z N - singleClusterGSEnergyS z N =
      ((N : ℂ) / 2) * ((z : ℂ) * (N : ℂ) + 1) := by
  unfold singleClusterMaxEnergyS singleClusterGSEnergyS
  ring

/-- **Strict GS < Max gap** (γ-5 step 281):
`Re(singleClusterGSEnergyS z N) < Re(singleClusterMaxEnergyS z N)` for
`N ≥ 1`. The Casimir spectrum is non-degenerate at the GS / Max
sectors whenever the spin is non-trivial (`S ≥ 1/2`). -/
theorem singleClusterGSEnergyS_re_lt_singleClusterMaxEnergyS_re_of_pos
    (z : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (singleClusterGSEnergyS z N).re < (singleClusterMaxEnergyS z N).re := by
  rw [singleClusterGSEnergyS_re_eq, singleClusterMaxEnergyS_re_eq]
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (0 : ℝ) ≤ (z : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (z : ℝ) * (N : ℝ) := mul_nonneg h2 (by linarith)
  nlinarith [mul_nonneg h2 (sq_nonneg ((N : ℝ) - 1))]

/-- **Strict GS energy negativity** (γ-5 step 283):
`Re(singleClusterGSEnergyS z N) < 0` for `N ≥ 1`. Strengthens γ-5 step
272 to strict for non-trivial spin. -/
theorem singleClusterGSEnergyS_re_neg_of_pos
    (z : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (singleClusterGSEnergyS z N).re < 0 := by
  rw [singleClusterGSEnergyS_re_eq]
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (0 : ℝ) ≤ (z : ℝ) := by positivity
  nlinarith [mul_nonneg h2 (by linarith : (0 : ℝ) ≤ (N : ℝ))]

/-- **Strict max-Casimir-sector energy positivity** (γ-5 step 283):
`0 < Re(singleClusterMaxEnergyS z N)` for `z ≥ 1, N ≥ 1`. Strengthens
γ-5 step 272 to strict when both `z` and `N` are non-trivial. -/
theorem singleClusterMaxEnergyS_re_pos_of_pos
    {z N : ℕ} (hz : 1 ≤ z) (hN : 1 ≤ N) :
    0 < (singleClusterMaxEnergyS z N).re := by
  rw [singleClusterMaxEnergyS_re_eq]
  have h1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith [sq_nonneg ((N : ℝ) - 1)]


end LatticeSystem.Quantum

end LatticeSystem.Quantum
