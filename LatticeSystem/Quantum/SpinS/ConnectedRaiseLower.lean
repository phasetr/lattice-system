import LatticeSystem.Quantum.SpinS.ConfigDist
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.unusedSectionVars false

/-!
# Connected-graph spin-`S` configuration reachability
(Tasaki §4.4 prerequisite — Issue #4609 PR1)

For the spin-`S` raise/lower step relation `RaiseLowerStepS` (defined in
`LatticeSystem/Quantum/SpinS/RaiseLower.lean`), this module proves the
spin-`S` analogue of the spin-`1/2` connectivity result
`swapReachable_of_reachable_of_ne`
(`LatticeSystem/Quantum/MarshallLiebMattis/Connectivity.lean`):

  **On a connected graph, any two configurations with equal
  magnetization sum are raise/lower reachable.**

The key new ingredient (beyond the already available complete-graph
version `raiseLowerReachableS_completeGraph_of_eq_magSumS`) is the
*single-quantum walk transport* lemma: along any `G`-walk from `x` to
`y`, one can transport a single magnetization quantum from `x` (lowered
by `1`) to `y` (raised by `1`) using only `RaiseLowerStepS` moves along
the edges of the walk. The overflow-free routing at an intermediate
vertex `v` is the spin-`S` counterpart of Tasaki's three-edge swap
decomposition (p. 41): if `v` has room (`(σ v).val < N`) we push the
quantum into `v` first and pull it out by recursion; if `v` is full
(`(σ v).val = N`) we recurse first to make room, then push into `v`.

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, pp. 41–42 (Property (iii) — spin-`1/2`
  template); generalised here to spin-`S`.

Tracked in #4609.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## The single-quantum transport configuration -/

/-- The configuration obtained from `σ` by lowering at `x` (subtracting
`1`) and raising at `y` (adding `1`). The `Fin` values are well-defined
because lowering truncates at `0` (using `Nat` subtraction `(σ x).val - 1`)
and raising is taken modulo nothing — instead the raised value is only
used through `transportOne_apply_y` under the bound `(σ y).val < N`, so
here we clamp the raised value with `min` to keep the definition total.

Concretely we use `Function.update` to set `x ↦ (σ x).val - 1` and
`y ↦ min ((σ y).val + 1) N`. Whenever the caller guarantees
`0 < (σ x).val` and `(σ y).val < N`, the clamp is inactive and the
values are exactly `(σ x).val - 1` and `(σ y).val + 1`. -/
def transportOne (σ : V → Fin (N + 1)) (x y : V) : V → Fin (N + 1) :=
  Function.update (Function.update σ x
    ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩) y
    ⟨min ((σ y).val + 1) N, by omega⟩

omit [Fintype V] in
/-- `transportOne σ x y` at site `x` equals `(σ x).val - 1` (when
`x ≠ y`). -/
theorem transportOne_apply_x {σ : V → Fin (N + 1)} {x y : V} (hxy : x ≠ y) :
    (transportOne σ x y x).val = (σ x).val - 1 := by
  unfold transportOne
  rw [Function.update_of_ne hxy, Function.update_self]

omit [Fintype V] in
/-- `transportOne σ x y` at site `y` equals `min ((σ y).val + 1) N`, and
in particular `(σ y).val + 1` when `(σ y).val < N`. -/
theorem transportOne_apply_y {σ : V → Fin (N + 1)} {x y : V}
    (hy : (σ y).val < N) :
    (transportOne σ x y y).val = (σ y).val + 1 := by
  unfold transportOne
  rw [Function.update_self]
  simp only []
  omega

omit [Fintype V] in
/-- `transportOne σ x y` agrees with `σ` off `{x, y}`. -/
theorem transportOne_apply_off {σ : V → Fin (N + 1)} {x y z : V}
    (hzx : z ≠ x) (hzy : z ≠ y) : transportOne σ x y z = σ z := by
  unfold transportOne
  rw [Function.update_of_ne hzy, Function.update_of_ne hzx]

omit [Fintype V] in
/-- When `(σ y).val < N`, the `min`-clamp in `transportOne` is inactive,
so `transportOne σ x y` equals the explicit raise/lower update used by
`configDistS_decrease_of_over_under`. -/
theorem transportOne_eq_update_of_lt {σ : V → Fin (N + 1)} {x y : V}
    (hxy : x ≠ y) (hy : (σ y).val < N) :
    transportOne σ x y =
      Function.update (Function.update σ x
        ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩) y
        ⟨(σ y).val + 1, by have := (σ y).isLt; omega⟩ := by
  funext z
  apply Fin.ext
  by_cases hzy : z = y
  · subst hzy
    rw [transportOne_apply_y hy, Function.update_self]
  · by_cases hzx : z = x
    · subst hzx
      rw [transportOne_apply_x hxy, Function.update_of_ne hzy,
        Function.update_self]
    · rw [transportOne_apply_off hzx hzy, Function.update_of_ne hzy,
        Function.update_of_ne hzx]

/-! ## Single-edge transport step -/

omit [Fintype V] in
/-- For a `G`-adjacent pair `(x, y)` with `0 < (σ x).val` (so `x` can be
lowered) and `(σ y).val < N` (so `y` can be raised), transporting one
quantum from `x` to `y` is a single `RaiseLowerStepS`. -/
theorem raiseLowerStepS_transport {G : SimpleGraph V} {x y : V}
    (hadj : G.Adj x y) {σ : V → Fin (N + 1)}
    (hx : 0 < (σ x).val) (hy : (σ y).val < N) :
    RaiseLowerStepS G σ (transportOne σ x y) := by
  have hxy : x ≠ y := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
  refine ⟨x, y, hadj, Or.inr ⟨?_, ?_⟩, ?_⟩
  · -- `(transportOne σ x y x).val + 1 = (σ x).val`
    rw [transportOne_apply_x hxy]; omega
  · -- `(σ y).val + 1 = (transportOne σ x y y).val`
    rw [transportOne_apply_y hy]
  · intro k hkx hky
    exact transportOne_apply_off hkx hky

/-! ## Net-effect identities for nested transports -/

omit [Fintype V] in
/-- **Branch-1 net effect.** Pushing a quantum into the intermediate
vertex `v` first (`transportOne σ x v`) and then transporting it out of
`v` to `y` (`transportOne · v y`) has the same net effect as a single
transport `transportOne σ x y`, provided `x, v, y` are pairwise distinct
and `(σ v).val < N` (so the inner raise at `v` is exact). -/
theorem transportOne_transportOne_mid {σ : V → Fin (N + 1)} {x v y : V}
    (hxv : x ≠ v) (hvy : v ≠ y) (hxy : x ≠ y)
    (hvN : (σ v).val < N) (hyN : (σ y).val < N) :
    transportOne (transportOne σ x v) v y = transportOne σ x y := by
  funext z
  apply Fin.ext
  by_cases hzx : z = x
  · -- At `x`: outer untouched (`x ≠ v`, `x ≠ y`), inner lowers `x`.
    rw [hzx, transportOne_apply_off hxv hxy,
      transportOne_apply_x hxv, transportOne_apply_x hxy]
  · by_cases hzv : z = v
    · -- At `v`: outer lowers `v`, inner raised `v` (room `hvN`).
      rw [hzv, transportOne_apply_x hvy, transportOne_apply_y hvN,
        transportOne_apply_off (Ne.symm hxv) hvy]
      omega
    · by_cases hzy : z = y
      · -- At `y`: outer raises `y`, inner untouched (`y ≠ x`, `y ≠ v`).
        have hyroom : ((transportOne σ x v) y).val < N := by
          rw [transportOne_apply_off (Ne.symm hxy) (Ne.symm hvy)]; exact hyN
        rw [hzy, transportOne_apply_y hyroom,
          transportOne_apply_off (Ne.symm hxy) (Ne.symm hvy),
          transportOne_apply_y hyN]
      · -- Off `{x, v, y}`: nothing changes on either side.
        rw [transportOne_apply_off hzv hzy,
          transportOne_apply_off hzx hzv,
          transportOne_apply_off hzx hzy]

omit [Fintype V] in
/-- **Branch-2 net effect.** Making room at the full intermediate vertex
`v` first by transporting a quantum out of `v` to `y`
(`transportOne σ v y`) and then pushing a quantum from `x` into `v`
(`transportOne · x v`) has the same net effect as a single transport
`transportOne σ x y`, provided `x, v, y` are pairwise distinct,
`(σ v).val < N + 1` always holds, `0 < (σ v).val` (so the inner lower at
`v` is exact) and `(σ y).val < N` (so the inner raise at `y` is exact). -/
theorem transportOne_transportOne_full {σ : V → Fin (N + 1)} {x v y : V}
    (hxv : x ≠ v) (hvy : v ≠ y) (hxy : x ≠ y)
    (hvpos : 0 < (σ v).val) (hyN : (σ y).val < N) :
    transportOne (transportOne σ v y) x v = transportOne σ x y := by
  funext z
  apply Fin.ext
  by_cases hzx : z = x
  · -- At `x`: outer lowers `x`, inner untouched (`x ≠ v`, `x ≠ y`).
    rw [hzx, transportOne_apply_x hxv, transportOne_apply_off hxv hxy,
      transportOne_apply_x hxy]
  · by_cases hzv : z = v
    · -- At `v`: outer raises `v`, inner lowered `v` (`hvpos`).
      have hvroom : (transportOne σ v y v).val < N := by
        rw [transportOne_apply_x hvy]; omega
      rw [hzv, transportOne_apply_y hvroom, transportOne_apply_x hvy,
        transportOne_apply_off (Ne.symm hxv) hvy]
      omega
    · by_cases hzy : z = y
      · -- At `y`: outer untouched (`y ≠ x`, `y ≠ v`), inner raises `y`.
        rw [hzy, transportOne_apply_off (Ne.symm hxy) (Ne.symm hvy),
          transportOne_apply_y hyN, transportOne_apply_y hyN]
      · -- Off `{x, v, y}`: nothing changes on either side.
        rw [transportOne_apply_off hzx hzv,
          transportOne_apply_off hzv hzy,
          transportOne_apply_off hzx hzy]

/-! ## Single-quantum walk transport -/

omit [Fintype V] in
/-- **Single-quantum walk transport.** Along any `G`-walk from `x` to
`y` (with `x ≠ y`), one can transport a single magnetization quantum
from `x` to `y` (lowering `x`, raising `y`) using only `RaiseLowerStepS`
moves, provided `0 < (σ x).val` (room to lower `x`) and `(σ y).val < N`
(room to raise `y`).

Proof by induction on the walk, mirroring Tasaki's spin-`1/2`
three-edge decomposition (p. 41). For a `cons` walk `x → v → ⋯ → y`:
if `v = y` the walk is a single edge and we use
`raiseLowerStepS_transport` directly; otherwise we branch on whether `v`
has room (`(σ v).val < N`): if so we push into `v` first then recurse
(`transportOne_transportOne_mid`); if `v` is full we recurse first to
make room then push into `v` (`transportOne_transportOne_full`). -/
theorem raiseLowerReachableS_transportOne_of_walk {G : SimpleGraph V}
    {x y : V} (w : G.Walk x y) {σ : V → Fin (N + 1)} (hxy : x ≠ y)
    (hx : 0 < (σ x).val) (hy : (σ y).val < N) :
    RaiseLowerReachableS G σ (transportOne σ x y) := by
  induction w generalizing σ with
  | nil => exact absurd rfl hxy
  | @cons u v y' hadj p ih =>
    -- `hadj : G.Adj u v`, `p : G.Walk v y'`.
    have huv : u ≠ v := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
    by_cases hvy : v = y'
    · -- Single edge `u → y'`.
      subst hvy
      exact RaiseLowerReachableS.single (raiseLowerStepS_transport hadj hx hy)
    · -- Walk of length ≥ 2: branch on whether `v` has room.
      have huy : u ≠ y' := hxy
      by_cases hvN : (σ v).val < N
      · -- Branch 1: push into `v` first, then recurse `v → y'`.
        have hstep : RaiseLowerStepS G σ (transportOne σ u v) :=
          raiseLowerStepS_transport hadj hx hvN
        -- The pushed config has `v` positive and `y'` still has room.
        have hvpos : 0 < (transportOne σ u v v).val := by
          rw [transportOne_apply_y hvN]; omega
        have hyroom : (transportOne σ u v y').val < N := by
          rw [transportOne_apply_off (Ne.symm huy) (Ne.symm hvy)]; exact hy
        have hreach : RaiseLowerReachableS G (transportOne σ u v)
            (transportOne (transportOne σ u v) v y') :=
          ih (σ := transportOne σ u v) hvy hvpos hyroom
        have hnet : transportOne (transportOne σ u v) v y' =
            transportOne σ u y' :=
          transportOne_transportOne_mid huv hvy huy hvN hy
        rw [hnet] at hreach
        exact (RaiseLowerReachableS.single hstep).trans hreach
      · -- Branch 2: `v` is full; recurse first to make room, then push.
        have hvfull : (σ v).val = N := by have := (σ v).isLt; omega
        have hvpos : 0 < (σ v).val := by omega
        have hreach1 : RaiseLowerReachableS G σ (transportOne σ v y') :=
          ih (σ := σ) hvy hvpos hy
        -- After recursion, `u` still positive and `v` has room.
        have hupos : 0 < (transportOne σ v y' u).val := by
          rw [transportOne_apply_off huv huy]; exact hx
        have hvroom : (transportOne σ v y' v).val < N := by
          rw [transportOne_apply_x hvy]; omega
        have hstep : RaiseLowerStepS G (transportOne σ v y')
            (transportOne (transportOne σ v y') u v) :=
          raiseLowerStepS_transport hadj hupos hvroom
        have hnet : transportOne (transportOne σ v y') u v =
            transportOne σ u y' :=
          transportOne_transportOne_full huv hvy huy hvpos hy
        rw [hnet] at hstep
        exact hreach1.tail' hstep

omit [Fintype V] in
/-- For a connected graph, single-quantum transport from `x` to `y`
(with `x ≠ y`, room to lower `x` and to raise `y`) is reachable. -/
theorem raiseLowerReachableS_transportOne_of_connected {G : SimpleGraph V}
    (hG : G.Connected) {x y : V} (hxy : x ≠ y) {σ : V → Fin (N + 1)}
    (hx : 0 < (σ x).val) (hy : (σ y).val < N) :
    RaiseLowerReachableS G σ (transportOne σ x y) := by
  obtain ⟨w⟩ := hG.preconnected x y
  exact raiseLowerReachableS_transportOne_of_walk w hxy hx hy

/-! ## Main theorem: connected-graph equal-magnetization reachability -/

omit [DecidableEq V] in
/-- **Connected-graph reachability (Issue #4609 PR1).** On a connected
graph `G`, any two spin-`S` configurations with equal magnetization sum
are `RaiseLowerReachableS`.

The proof inducts on `configDistS σ σ'` exactly as the complete-graph
version `raiseLowerReachableS_completeGraph_of_eq_magSumS`, but replaces
the single direct edge step with the connected-graph single-quantum walk
transport `raiseLowerReachableS_transportOne_of_connected`. -/
theorem raiseLowerReachableS_of_connected (G : SimpleGraph V)
    (hG : G.Connected) {σ σ' : V → Fin (N + 1)}
    (hmag : magSumS σ = magSumS σ') :
    RaiseLowerReachableS G σ σ' := by
  classical
  -- Strong induction on `configDistS σ σ'`.
  suffices h : ∀ n, ∀ σ σ' : V → Fin (N + 1),
      magSumS σ = magSumS σ' → configDistS σ σ' ≤ n →
      RaiseLowerReachableS G σ σ' from
    h (configDistS σ σ') σ σ' hmag (le_refl _)
  intro n
  induction n with
  | zero =>
    intro σ σ' _ hd
    have hsigma : σ = σ' :=
      (configDistS_eq_zero_iff σ σ').mp (Nat.le_zero.mp hd)
    rw [hsigma]
    exact RaiseLowerReachableS.refl _ _
  | succ n ih =>
    intro σ σ' hmag hd
    by_cases hne : σ = σ'
    · rw [hne]; exact RaiseLowerReachableS.refl _ _
    · -- Over/under sites for the equal-magnetization pair.
      obtain ⟨⟨x, hover⟩, y, hunder⟩ :=
        exists_over_under_of_eq_magSumS hne hmag
      have hxy : x ≠ y := fun heq => by subst heq; omega
      -- `transportOne σ x y` is the distance-reducing intermediate.
      have hx : 0 < (σ x).val := by omega
      have hyN : (σ y).val < N := by have := (σ' y).isLt; omega
      -- The distance reduces by 2 (matches `configDistS_decrease`'s σ'').
      have hreduce : configDistS (transportOne σ x y) σ' + 2 =
          configDistS σ σ' := by
        rw [transportOne_eq_update_of_lt hxy hyN]
        exact configDistS_decrease_of_over_under hxy hover hunder
      -- Reachability of the transport, then the inductive tail.
      have hstep : RaiseLowerReachableS G σ (transportOne σ x y) :=
        raiseLowerReachableS_transportOne_of_connected hG hxy hx hyN
      have hmag_step : magSumS (transportOne σ x y) = magSumS σ :=
        magSumS_eq_of_raiseLowerReachableS hstep
      have hIH : RaiseLowerReachableS G (transportOne σ x y) σ' := by
        apply ih
        · rw [hmag_step]; exact hmag
        · omega
      exact hstep.trans hIH

end LatticeSystem.Quantum
