import LatticeSystem.Quantum.SpinS.RayleighInfMatrix

/-!
# Tasaki §3.4: the Kaplan–Horsch–von der Linden theorem (Theorem 3.2)

Tasaki's Theorem 3.2 (Kaplan–Horsch–von der Linden) shows that an infinitesimal symmetry-breaking
field triggers spontaneous symmetry breaking: with the order operator `Ô_L` and the field-perturbed
Hamiltonian `Ĥ_h = Ĥ − h·Ô_L`, the order parameter of the perturbed ground state obeys
`lim_{h↓0} lim_{L↑∞} ⟨Φ_GS,h| Ô_L/L^d |Φ_GS,h⟩ ≥ √q₀` (eq. (3.4.22)).

The heart of the proof (eq. (3.4.21)) is the **finite-volume variational lower bound**: since the
perturbed ground state `Φ_GS,h` minimizes `Ĥ_h`, for any trial state `Ξ`
`⟨Φ_GS,h| Ô_L |Φ_GS,h⟩ ≥ ⟨Ξ| Ô_L |Ξ⟩ + (1/h)(⟨Φ_GS,h|Ĥ|Φ_GS,h⟩ − ⟨Ξ|Ĥ|Ξ⟩)`,
which is `≥ ⟨Ξ| Ô_L |Ξ⟩ + (1/h)(E_GS − ⟨Ξ|Ĥ|Ξ⟩)`.
We discharge exactly this finite-dimensional core (axiom-free); taking `Ξ = Ξ₊` (the Horsch–von der
Linden state, with the essential bound `⟨Ξ₊| Ô_L/L^d |Ξ₊⟩ ≥ √q₀` and
`|E_GS − ⟨Ξ₊|Ĥ|Ξ₊⟩| ≤ C·L^{-d}/2`) and the double limit `L↑∞`, `h↓0` then gives Theorem 3.2 —
the thermodynamic/infinite-volume input.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, Theorem 3.2, eqs. (3.4.16)–(3.4.22), pp. 68–70.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The Rayleigh quotient of a real-scaled difference splits: `R(H − h·O) v = R(H) v − h·R(O) v`. -/
private theorem rayleighOnVec_sub_smul {n : Type*} [Fintype n]
    (H O : Matrix n n ℂ) (h : ℝ) (v : n → ℂ) :
    rayleighOnVec (H - (h : ℂ) • O) v = rayleighOnVec H v - h * rayleighOnVec O v := by
  unfold rayleighOnVec
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    Complex.sub_re, Complex.re_ofReal_mul]

/-- **Tasaki Theorem 3.2 (Kaplan–Horsch–von der Linden), finite-volume variational core.**  Let `H`
(`= Ĥ`) and `O` (`= Ô_L`) be matrices and `h > 0` a field strength.  If `Ψ` (`= Φ_GS,h`) is a ground
state of the field-perturbed Hamiltonian `H − h·O` — i.e. its Rayleigh energy is `≤` that of the
trial state `Ξ` (the variational/ground-state property) — and `E₀` is a lower bound for the
unperturbed energy `⟨Ψ, H Ψ⟩` (`= E_GS ≤ ⟨Φ_GS,h|Ĥ|Φ_GS,h⟩`), then the order parameter of `Ψ`
obeys
`⟨Ξ, O Ξ⟩ + (E₀ − ⟨Ξ, H Ξ⟩)/h ≤ ⟨Ψ, O Ψ⟩` (eq. (3.4.21)).

Proof: from `R(H − h·O) Ψ ≤ R(H − h·O) Ξ` and `R(H − h·O) = R(H) − h·R(O)`, rearrange (using
`h > 0`) to `R(O) Ξ + (R(H) Ψ − R(H) Ξ)/h ≤ R(O) Ψ`, then bound `R(H) Ψ ≥ E₀`. -/
theorem kaplan_horsch_vonderLinden_order_lower_bound {n : Type*} [Fintype n]
    (H O : Matrix n n ℂ) {h : ℝ} (hpos : 0 < h) (Ψ Ξ : n → ℂ) {E₀ : ℝ}
    (hvar : rayleighOnVec (H - (h : ℂ) • O) Ψ ≤ rayleighOnVec (H - (h : ℂ) • O) Ξ)
    (hE₀ : E₀ ≤ rayleighOnVec H Ψ) :
    rayleighOnVec O Ξ + (E₀ - rayleighOnVec H Ξ) / h ≤ rayleighOnVec O Ψ := by
  rw [rayleighOnVec_sub_smul, rayleighOnVec_sub_smul] at hvar
  -- hvar : R(H) Ψ − h·R(O) Ψ ≤ R(H) Ξ − h·R(O) Ξ
  have key : (E₀ - rayleighOnVec H Ξ) / h ≤ rayleighOnVec O Ψ - rayleighOnVec O Ξ := by
    rw [div_le_iff₀ hpos]
    nlinarith [hvar, hE₀]
  linarith [key]

end LatticeSystem.Quantum
