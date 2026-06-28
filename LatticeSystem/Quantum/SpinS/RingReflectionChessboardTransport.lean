/-
Translation transport of the reflection-positivity chessboard inequality
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 39).

Conjugation by the ring translation `τ(X) = T† · X · T` is a trace-preserving `*`-homomorphism
(`T T† = 1`), so applying it to all three trace arguments leaves the chessboard inequality fixed.
Hence any chessboard estimate transports to the translated data `(τM, τ(θA), τB)` — the weight `τM`
is the Marshall gauge relative to the *shifted* reflection plane.  Combined with the translation
covariance of `θ`, this carries the single-axis chessboard to every bond of the ring, the step
needed to assemble the Dyson–Lieb–Simon Gaussian domination from the fixed-plane estimate.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsChessboard
import LatticeSystem.Quantum.SpinS.RingTranslationGibbs

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- Conjugation of an operator by the ring translation, `τ(X) = T† · X · T`. -/
noncomputable def ringTranslateConj (n N : ℕ) (X : ManyBodyOpS (Fin (2 * n)) N) :
    ManyBodyOpS (Fin (2 * n)) N :=
  (chainTranslationOp (2 * n) N).conjTranspose * X * chainTranslationOp (2 * n) N

/-- Translation conjugation is multiplicative: `τ(X · Y) = τ(X) · τ(Y)` (since `T T† = 1`). -/
theorem ringTranslateConj_mul (X Y : ManyBodyOpS (Fin (2 * n)) N) :
    ringTranslateConj n N (X * Y) = ringTranslateConj n N X * ringTranslateConj n N Y := by
  set T := chainTranslationOp (2 * n) N with hT
  simp only [ringTranslateConj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T T.conjTranspose, chainTranslationOp_unitary', Matrix.one_mul]

/-- Translation conjugation preserves the trace. -/
theorem ringTranslateConj_trace (X : ManyBodyOpS (Fin (2 * n)) N) :
    (ringTranslateConj n N X).trace = X.trace :=
  trace_chainTranslation_conj X

/-- **Translation transport of the chessboard inequality.**  Given a chessboard estimate for bare
data `(M, θA, A, θB, B)`, the same estimate holds for the translation-conjugated data
`(τM, τ(θA), τA, τ(θB), τB)` — the trace values are unchanged because `τ` is a trace-preserving
`*`-homomorphism. -/
theorem chessboard_ringTranslateConj_of {M A B TA TB : ManyBodyOpS (Fin (2 * n)) N}
    (hfixed : ((M * (TA * B)).trace.re) ^ 2
      ≤ (M * (TA * A)).trace.re * (M * (TB * B)).trace.re) :
    ((ringTranslateConj n N M * (ringTranslateConj n N TA * ringTranslateConj n N B)).trace.re) ^ 2
      ≤ (ringTranslateConj n N M
          * (ringTranslateConj n N TA * ringTranslateConj n N A)).trace.re
        * (ringTranslateConj n N M
          * (ringTranslateConj n N TB * ringTranslateConj n N B)).trace.re := by
  simp only [← ringTranslateConj_mul, ringTranslateConj_trace]
  exact hfixed

end LatticeSystem.Quantum
