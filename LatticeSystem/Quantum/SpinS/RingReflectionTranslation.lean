/-
Translation covariance of the reflection map θ
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 37).

The fixed-axis reflection map `θ = ringReflectionThetaS` reflects across the bond `(n−1, n)`.
Conjugating it by the ring translation `T = chainTranslationOp` shifts the reflection axis: the site
index passes through both `θ`'s bond reflection and the translation, so `T† · θ(onSiteS x A) · T`
and `T† · θ(Ŝ_x · Ŝ_y) · T` land on the translated–reflected sites
`finRotate (ringReflect x)` (and `finRotate (ringReflect y)`).  These pointwise covariance laws are
the foundation for reflections across every bond of the ring, needed to spread the single-axis
chessboard estimate over all bonds toward the Dyson–Lieb–Simon Gaussian domination.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionHamiltonian
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisOrthogonality

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Translation covariance of θ on a single-site operator.**  Conjugating `θ(onSiteS x A)` by the
ring translation moves the site to `finRotate (ringReflect x)`. -/
theorem chainTranslation_conj_ringReflectionThetaS_onSiteS (n N : ℕ) (x : Fin (2 * n))
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (chainTranslationOp (2 * n) N).conjTranspose * ringReflectionThetaS n N (onSiteS x A)
        * chainTranslationOp (2 * n) N
      = onSiteS (finRotate (2 * n) (ringReflect n x)) (A.map (starRingEnd ℂ)) := by
  rw [ringReflectionThetaS_onSiteS, chainTranslation_conj_onSiteS]

/-- **Translation covariance of θ on a two-site dot product.**  Conjugating `θ(Ŝ_x · Ŝ_y)` by the
ring translation moves both sites to `finRotate (ringReflect ·)`. -/
theorem chainTranslation_conj_ringReflectionThetaS_spinSDot (n N : ℕ) (x y : Fin (2 * n)) :
    (chainTranslationOp (2 * n) N).conjTranspose * ringReflectionThetaS n N (spinSDot x y N)
        * chainTranslationOp (2 * n) N
      = spinSDot (finRotate (2 * n) (ringReflect n x)) (finRotate (2 * n) (ringReflect n y)) N := by
  rw [ringReflectionThetaS_spinSDot, chainTranslation_conj_spinSDot]

end LatticeSystem.Quantum
