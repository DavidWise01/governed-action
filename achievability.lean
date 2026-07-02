/-
  Achievability skeleton for "The Irreducibility of Residual Exteriority".
  Lean 4 (no mathlib). Compile:  lean achievability.lean
  Machine-checks the IDEALIZED (zero-error) core of the matching upper bound:
  a verifier that is sound + complete for a fixed, exterior-chosen boundary B
  faithfully decides B; gating every action through it pre-action yields
  containment in an adequate A*; it never blocks admissible actions (liveness);
  and it genuinely rejects excluded ones (non-vacuity). The cryptographic /
  probabilistic layer (soundness error, horizon-dependence of λ, cost accounting)
  is analytic and lives in the companion note — see the footer.
-/

namespace Achievability

abbrev Trace (A : Type) := Nat → A

/-! ## The verifier faithfully decides the fixed boundary (sound + complete) -/

/-- A sound + complete verifier is an exact decision procedure for `B`:
    it passes an action iff the action is in the boundary. This is the
    exterior-supplied object — `B` is the spec (E_spec), the verifier's
    soundness is the trust (E_root); the agent supplies the per-action proofs. -/
theorem verifier_decides
    {A : Type} (V : A → Bool) (B : A → Prop)
    (Vsound : ∀ a, V a = true → B a)
    (Vcomplete : ∀ a, B a → V a = true)
    (a : A) : V a = true ↔ B a :=
  ⟨Vsound a, Vcomplete a⟩

/-! ## Correctness — pre-action gating into an adequate boundary gives containment -/

/-- CORRECTNESS: if `V` is sound for `B`, `B` is adequate (`B ⊆ A*`), and the agent
    gates every executed action through `V` *before* acting, then every executed
    action lies in `A*` — containment. No exterior information enters per action:
    the proofs are agent-generated and checked against the fixed `V`. -/
theorem achiev_correct
    {A : Type} (V : A → Bool) (B Astar : A → Prop)
    (Vsound : ∀ a, V a = true → B a)
    (Badeq : ∀ a, B a → Astar a)
    (tr : Trace A) (gated : ∀ t, V (tr t) = true) :
    ∀ t, Astar (tr t) := by
  intro t
  exact Badeq _ (Vsound _ (gated t))

/-- The gate composes to whole-trace admissibility w.r.t. `B` itself (independent
    of `A*`): per-action passing ⇒ every executed action is in the boundary. -/
theorem gate_composes
    {A : Type} (V : A → Bool) (B : A → Prop)
    (Vsound : ∀ a, V a = true → B a)
    (tr : Trace A) (gated : ∀ t, V (tr t) = true) :
    ∀ t, B (tr t) := by
  intro t; exact Vsound _ (gated t)

/-! ## Liveness — a complete verifier never blocks an admissible action -/

/-- LIVENESS: if `V` is complete for `B`, then every admissible action passes;
    the scheme does not over-restrict an honest agent (no false rejections). -/
theorem achiev_live
    {A : Type} (V : A → Bool) (B : A → Prop)
    (Vcomplete : ∀ a, B a → V a = true)
    {a : A} (hB : B a) : V a = true :=
  Vcomplete a hB

/-! ## Non-vacuity — a sound verifier genuinely rejects excluded actions -/

/-- NON-VACUITY: soundness forces the verifier to reject anything outside `B`.
    So when `B ≠ ⊤` (something is excluded), the gate actually bites — the
    certificate is not the empty `⊤`-certificate of the irreducibility note. -/
theorem rejects_excluded
    {A : Type} (V : A → Bool) (B : A → Prop)
    (Vsound : ∀ a, V a = true → B a)
    {a : A} (hnotB : ¬ B a) : V a = false := by
  cases hva : V a with
  | false => rfl
  | true => exact absurd (Vsound a hva) hnotB

end Achievability

/-
  Honest scope:
  • This is the ZERO-ERROR idealization: `Vsound`/`Vcomplete` are exact. A real
    proof system has soundness error 2^(-λ) per proof; over a horizon of T actions
    the union bound gives total error ≤ T·2^(-λ), so bounded total error ε needs
    λ ≥ log2(T/ε). That horizon-dependence is the companion note's analytic result,
    NOT captured here.
  • COST is not a theorem: the claim that exterior information = log2 N (to name B)
    + λ (trust anchor) + 0 (runtime) is an accounting argument under the
    information measure, made in the note. Here we only check that gating through
    a fixed, exterior-supplied, sound+complete verifier yields containment +
    liveness + genuine rejection.
  • Achievability is RELATIVE to the existence of such a proof system (SNARK/STARK/
    TEE attestation); it is not constructed from scratch.
  • Proofs are relative to these definitions; none assert any real verifier is
    sound or any real boundary adequate.
-/
