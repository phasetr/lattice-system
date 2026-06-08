import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandCAR
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandZeroEnergy

/-!
# Tasaki §11.4.3 Lemma 11.21: the local Hamiltonian annihilates the all-up state

Building blocks toward discharging `nonsingular_lemma_11_21` (Issue #4189). Tasaki's proof
(p. 430) hinges on `ĥ_p |Φα,all↑⟩ = 0`, which in turn rests on
`(Σ_σ â†_{p,σ} â_{p,σ}) |Φα,all↑⟩ = (1+2ν²) |Φα,all↑⟩`.  The `1+2ν²` is the self-overlap
`⟨α_p, α_p⟩ = ‖α_p‖²` of the single-particle state `α_p = e_{ext p} − ν(e_{int p}+e_{int p−1})`,
i.e. the value of the self-anticommutator `{â_{p,σ}, â†_{p,σ}} = ‖α_p‖²·1` (eq. (11.4.42), `d=1`).

This file starts with the geometric input: `Σ_x α_p(x)² = 1 + 2ν²` on a genuine chain (`p−1 ≠ p`,
i.e. `K ≥ 1`; the single-site `K = 0` case degenerates to `1 + ν²`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.),
§11.4.3, eqs. (11.4.42), (11.4.48)–(11.4.49), Lemma 11.21 (pp. 429–431).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Self-overlap of the flat-band single-particle state `α_p`**: `⟨α_p, α_p⟩ = 1 + 2ν²` on a
chain with at least two sites (`p − 1 ≠ p`).  The external site contributes `1²` and the two
distinct incident internal sites contribute `(−ν)²` each.  This is `‖α_p‖²`, the value of the
self-anticommutator `{â_{p,σ}, â†_{p,σ}}` (Tasaki eq. (11.4.42), `d = 1`). -/
theorem flatBandAlpha_dot_self (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (hp : p - 1 ≠ p) :
    ∑ x, flatBandAlpha K ν p x * flatBandAlpha K ν p x = 1 + 2 * ν ^ 2 := by
  rw [sum_deltaSite_split]
  have hext : (∑ q, flatBandAlpha K ν p (deltaExternalSite K q) *
      flatBandAlpha K ν p (deltaExternalSite K q)) = 1 := by
    rw [Finset.sum_congr rfl (fun q _ =>
      show flatBandAlpha K ν p (deltaExternalSite K q) *
          flatBandAlpha K ν p (deltaExternalSite K q) = if q = p then (1 : ℝ) else 0 from by
        rw [flatBandAlpha_deltaExternalSite]; by_cases hq : q = p <;> simp [hq])]
    rw [Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : ℝ)), if_pos (Finset.mem_univ p)]
  have hint : (∑ v, flatBandAlpha K ν p (deltaInternalSite K v) *
      flatBandAlpha K ν p (deltaInternalSite K v)) = 2 * ν ^ 2 := by
    rw [Finset.sum_congr rfl (fun v _ =>
      show flatBandAlpha K ν p (deltaInternalSite K v) *
          flatBandAlpha K ν p (deltaInternalSite K v)
            = (if v = p then ν ^ 2 else 0) + (if v = p - 1 then ν ^ 2 else 0) from by
        rw [flatBandAlpha_deltaInternalSite]
        by_cases h1 : v = p
        · have h2 : ¬ v = p - 1 := fun h2 => hp (h2.symm.trans h1)
          rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
        · by_cases h2 : v = p - 1
          · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
          · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2]; ring)]
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ p (fun _ => ν ^ 2), if_pos (Finset.mem_univ p),
      Finset.sum_ite_eq' Finset.univ (p - 1) (fun _ => ν ^ 2),
      if_pos (Finset.mem_univ (p - 1))]
    ring
  rw [hext, hint]

/-- **Self-anticommutator of the flat-band fermion operators** (Tasaki eq. (11.4.42), `d = 1`):
`{â_{p,σ}, â†_{p,σ}} = (1+2ν²)·1` on a genuine chain (`p − 1 ≠ p`).  Reduces, via the canonical
anticommutation relations, to the self-overlap `⟨α_p, α_p⟩ = 1+2ν²`. -/
theorem flatBandAAnnihilation_ACreation_anticomm_self (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (σ : Fin 2) (hp : p - 1 ≠ p) :
    flatBandAAnnihilation K ν p σ * flatBandACreation K ν p σ
      + flatBandACreation K ν p σ * flatBandAAnnihilation K ν p σ
      = ((1 + 2 * ν ^ 2 : ℝ) : ℂ) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) := by
  set c : Fin (2 * K + 2) → ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
    fun x => fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
    with hc
  set d : Fin (2 * K + 2) → ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
    fun y => fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y σ)
    with hd
  have hkey : flatBandAAnnihilation K ν p σ * flatBandACreation K ν p σ
      + flatBandACreation K ν p σ * flatBandAAnnihilation K ν p σ
      = ∑ x, ∑ y, ((flatBandAlpha K ν p x : ℂ) * (flatBandAlpha K ν p y : ℂ)) •
          (c x * d y + d y * c x) := by
    unfold flatBandAAnnihilation flatBandACreation
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm _ (flatBandAlpha K ν p y : ℂ),
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (flatBandAlpha K ν p y : ℂ),
      ← smul_add]
  rw [hkey]
  simp_rw [hc, hd, spinful_annihilation_creation_anticomm, and_true]
  rw [show (∑ x, ∑ y, ((flatBandAlpha K ν p x : ℂ) * (flatBandAlpha K ν p y : ℂ)) •
      (if x = y then (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) else 0))
      = ∑ x, ((flatBandAlpha K ν p x : ℂ) * (flatBandAlpha K ν p x : ℂ)) • (1 : _) from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_congr rfl (fun y _ => by rw [smul_ite, smul_zero]),
      Finset.sum_ite_eq Finset.univ x (fun y =>
        ((flatBandAlpha K ν p x : ℂ) * (flatBandAlpha K ν p y : ℂ)) • (1 : _)),
      if_pos (Finset.mem_univ x)]]
  rw [← Finset.sum_smul, show (∑ x, (flatBandAlpha K ν p x : ℂ) * (flatBandAlpha K ν p x : ℂ))
      = (((∑ x, flatBandAlpha K ν p x * flatBandAlpha K ν p x : ℝ)) : ℂ) from by
    push_cast; rfl, flatBandAlpha_dot_self K ν p hp]

/-- **`â_{p,↓}` annihilates the all-up `α` state.**  Each `ĉ_{x,↓}` annihilates `|Φα,all↑⟩`
(no down electrons), and `â_{p,↓}` is a linear combination of these. -/
theorem flatBandAAnnihilation_down_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    (flatBandAAnnihilation K ν p 1).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold flatBandAAnnihilation
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [Matrix.smul_mulVec, flatBandCDownAnnihilation_mulVec_alphaAllUpState, smul_zero]

/-- The spinful creation–creation anticommutation relation `{ĉ†_{x,σ}, ĉ†_{y,τ}} = 0`. -/
theorem spinful_creation_creation_anticomm (K : ℕ) (x y : Fin (2 * K + 2)) (σ τ : Fin 2) :
    fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ)
      + fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) = 0 := by
  by_cases h : spinfulIndex (2 * K + 1) x σ = spinfulIndex (2 * K + 1) y τ
  · rw [h, fermionMultiCreation_sq, add_zero]
  · exact fermionMultiCreation_anticomm_of_ne h

/-- **Creation–creation anticommutator of the flat-band operators**: `{â†_{p,σ}, â†_{q,τ}} = 0`.
The single-particle creation operators anticommute because the underlying `ĉ†` operators do. -/
theorem flatBandACreation_ACreation_anticomm (K : ℕ) (ν : ℝ) (p q : Fin (K + 1)) (σ τ : Fin 2) :
    flatBandACreation K ν p σ * flatBandACreation K ν q τ
      + flatBandACreation K ν q τ * flatBandACreation K ν p σ = 0 := by
  set c : Fin (2 * K + 2) → ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
    fun x => fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
    with hc
  set d : Fin (2 * K + 2) → ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
    fun y => fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ)
    with hd
  have hkey : flatBandACreation K ν p σ * flatBandACreation K ν q τ
      + flatBandACreation K ν q τ * flatBandACreation K ν p σ
      = ∑ x, ∑ y, ((flatBandAlpha K ν p x : ℂ) * (flatBandAlpha K ν q y : ℂ)) •
          (c x * d y + d y * c x) := by
    unfold flatBandACreation
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm _ (flatBandAlpha K ν q y : ℂ),
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (flatBandAlpha K ν q y : ℂ),
      ← smul_add]
  rw [hkey]
  refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
  rw [hc, hd, spinful_creation_creation_anticomm, smul_zero]

end LatticeSystem.Fermion
