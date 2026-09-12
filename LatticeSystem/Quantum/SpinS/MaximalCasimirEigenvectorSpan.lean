import LatticeSystem.Quantum.SpinS.CasimirSpectralBound
import LatticeSystem.Math.CommutingHermitianEigenvector

/-!
# Eigenvectors at the maximal total-spin eigenvalue

The remark following eq. (2.4.10), p. 34, describes the states of eq. (2.4.9), p. 33, as the
only ones carrying the *maximum* total spin `S_max = |Λ|S`. Carrying that reading needs two
results which are proved in different modules:

* `totalSpinSSquared_eigenspace_eq_span_ladderIterateUp` identifies the `(Ŝ_tot)²`-eigenspace
  at the explicit value `S_max(S_max + 1)`, `S_max = |V|·N/2`, with the span of the ladder
  family, and says nothing about where that value sits in the spectrum;
* `totalSpinSSquared_eigenvalue_re_le_sMax` bounds the real part of every `(Ŝ_tot)²`-eigenvalue
  by `S_max(S_max + 1)`, and is proved in a module which imports the one holding the eigenspace
  identification, so the two cannot be combined in either of them.

This module imports both and states the combination: an eigenvector whose eigenvalue is maximal
lies in the span of the ladder family. Reality of the eigenvalue, needed to pass from the real
part supplied by the bound to the complex eigenvalue carried by the eigenspace identification,
comes from the Hermitian total Casimir.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.,
Springer, 2020), §2.4: eq. (2.4.9), p. 33; Theorem 2.1 and the remark following eq. (2.4.10),
p. 34.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **An eigenvector at a maximal eigenvalue of `(Ŝ_tot)²` lies in the span of the ladder
family** — the remark following Tasaki eq. (2.4.10), p. 34, read as a statement about the top
of the spectrum rather than about one numerical value.

`hmax` expresses maximality of `γ` in the sense supplied by
`totalSpinSSquared_eigenvalue_re_le_sMax`, namely for real parts: no eigenvalue of `(Ŝ_tot)²`
with a non-zero eigenvector has a larger real part than `γ`. Under that hypothesis every
eigenvector `v` at `γ` lies in the span of `ladderIterateUp`, whose members are the
unnormalised `(Ŝ⁻_tot)^k Φ↑` of eq. (2.4.9), p. 33.

The inputs enter as follows. The spectral bound gives `γ.re ≤ S_max(S_max + 1)` with
`S_max = |V|·N/2`; the ladder iterates are themselves non-zero eigenvectors at
`S_max(S_max + 1)`, so `hmax` applied to one of them gives the reverse inequality and pins
`γ.re` to that value. Since `(Ŝ_tot)²` is Hermitian, `γ` is real, hence equal to
`saturatedFerromagnetCasimirEigenvalueS V N`, and the eigenspace identification
`totalSpinSSquared_eigenspace_eq_span_ladderIterateUp` then supplies the span. The bound alone
locates the value in the spectrum; the eigenspace identification alone describes the
eigenvectors at it.

No graph, coupling, connectivity or `1 ≤ N` hypothesis appears, in contrast with Theorem 2.1
itself (`heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro`),
because the remark constrains `(Ŝ_tot)²` alone. `[Nonempty V]` is inherited from the eigenspace
identification rather than known to be necessary. -/
theorem totalSpinSSquared_maximal_eigenvector_mem_span_ladderIterateUp
    [Nonempty V] {γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v)
    (hmax : ∀ (δ : ℂ) (w : (V → Fin (N + 1)) → ℂ), w ≠ 0 →
      (totalSpinSSquared V N).mulVec w = δ • w → δ.re ≤ γ.re) :
    v ∈ Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  have hCcast : saturatedFerromagnetCasimirEigenvalueS V N =
      ((((Fintype.card V : ℝ) * (N : ℝ) / 2) *
        ((Fintype.card V : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold saturatedFerromagnetCasimirEigenvalueS
    push_cast
    ring
  have hladder := ladderIterateUp_totalSpinSSquared_hasEigenvector (V := V) (N := N) 0
  have hladder_cas : (totalSpinSSquared V N).mulVec (ladderIterateUp V N 0) =
      saturatedFerromagnetCasimirEigenvalueS V N • ladderIterateUp V N 0 := by
    have h := hladder.1
    rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
  have hγ : γ = saturatedFerromagnetCasimirEigenvalueS V N := by
    refine Complex.ext (le_antisymm ?_ (hmax _ _ hladder.2 hladder_cas)) ?_
    · rw [hCcast, Complex.ofReal_re]
      exact totalSpinSSquared_eigenvalue_re_le_sMax hv hcas
    · obtain ⟨μ, hμ⟩ := LatticeSystem.Math.isHermitian_mulVec_eigenvalue_eq_ofReal
        (totalSpinSSquared_isHermitian V N) hv hcas
      have him : γ.im = 0 := by rw [← hμ]; exact Complex.ofReal_im μ
      rw [him, hCcast, Complex.ofReal_im]
  have hmem : v ∈ Module.End.eigenspace ((totalSpinSSquared V N).mulVecLin)
      (saturatedFerromagnetCasimirEigenvalueS V N) := by
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, ← hγ]
    exact hcas
  rwa [totalSpinSSquared_eigenspace_eq_span_ladderIterateUp] at hmem

end LatticeSystem.Quantum
