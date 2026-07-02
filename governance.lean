/-
  Machine-checked cores of "Governed Action Under Irreversibility".
  Lean 4 (no mathlib). Compile:  lean governance.lean
  Each theorem below is checked by the Lean kernel. Comments mark what each
  does and does NOT establish (the modeling content lives in the definitions).
-/

namespace Governed

/-! ## T1 — no complete, legitimate authority (dogmatic / cycle / regress horns) -/

variable {Locus : Type}

-- `G x y` : "x is y's boundary-setter (x governs y)".
/-- A *legitimacy predicate* must satisfy the recurrence from Lemma 2:
    every legitimate locus has a DISTINCT legitimate governor. We quantify over
    ALL predicates satisfying this, so results are not artifacts of one encoding. -/
def IsLegitimacyPred (G : Locus → Locus → Prop) (L : Locus → Prop) : Prop :=
  ∀ y, L y → ∃ x, x ≠ y ∧ G x y ∧ L x

/-- A *top* is a locus with no governor. -/
def IsTop (G : Locus → Locus → Prop) (T : Locus) : Prop :=
  ∀ x, ¬ G x T

/-- DOGMATIC HORN: an ungoverned top is never legitimate, under ANY legitimacy
    predicate. (A top's authority is self-asserted; the recurrence rejects it.) -/
theorem top_not_legit
    {G : Locus → Locus → Prop} {L : Locus → Prop}
    (hL : IsLegitimacyPred G L) {T : Locus} (hT : IsTop G T) : ¬ L T := by
  intro hLT
  obtain ⟨x, _, hGxT, _⟩ := hL T hLT
  exact hT x hGxT

/-- T1 (core): no structure is both COMPLETE (has a top) and fully LEGITIMATE. -/
theorem no_complete_legit
    {G : Locus → Locus → Prop} {L : Locus → Prop}
    (hL : IsLegitimacyPred G L)
    (complete : ∃ T, IsTop G T)
    (allLegit : ∀ y, L y) : False := by
  obtain ⟨T, hT⟩ := complete
  exact top_not_legit hL hT (allLegit T)

/-- CYCLE HORN: a locus whose only governor is itself cannot be legitimate
    (distinctness fails). Reflexive/self-governance is barred as a ground. -/
theorem no_self_ground
    {G : Locus → Locus → Prop} {L : Locus → Prop}
    (hL : IsLegitimacyPred G L) {y : Locus}
    (hLy : L y) (onlySelf : ∀ x, G x y → x = y) : False := by
  obtain ⟨x, hne, hGxy, _⟩ := hL y hLy
  exact hne (onlySelf x hGxy)

/-- REGRESS HORN: if legitimacy is the LEAST predicate closed under "has a
    distinct legitimate governor" (no self-grounding base case), it is
    UNINHABITED — completed legitimacy by infinite regress is unreachable. -/
inductive LegitLFP (G : Locus → Locus → Prop) : Locus → Prop where
  | step : ∀ {x y}, x ≠ y → G x y → LegitLFP G x → LegitLFP G y

theorem regress_empty {G : Locus → Locus → Prop} (y : Locus) :
    ¬ LegitLFP G y := by
  intro h
  induction h with
  | step _ _ _ ih => exact ih

/-! ## Lemma 2 corollary — self-set boundaries are ratchets (value monotonicity) -/

/-- The B-optimum is feasible under any superset B', so B' does at least as well:
    enlarging one's own admissible set never lowers attainable utility. An agent
    that controls its own boundary thus weakly prefers to enlarge it. -/
theorem value_monotone
    {A : Type} {u : A → Nat} {B B' : A → Prop}
    (hsub : ∀ a, B a → B' a)
    {aStar : A} (hB : B aStar) (hmax : ∀ a, B a → u a ≤ u aStar) :
    ∃ b, B' b ∧ ∀ a, B a → u a ≤ u b :=
  ⟨aStar, hsub aStar hB, hmax⟩

/-! ## Lemma 3 — outward feedback diverges to unbounded permission (over ℕ) -/

/-- With a per-step outward margin `η ≥ 1` (`θ t + η ≤ θ (t+1)`), the frontier
    grows at least linearly: `θ 0 + t·η ≤ θ t`. -/
theorem frontier_diverges
    (θ : Nat → Nat) (η : Nat)
    (step : ∀ t, θ t + η ≤ θ (t+1)) :
    ∀ t, θ 0 + t * η ≤ θ t := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    have hsm : (n + 1) * η = n * η + η := by
      rw [Nat.add_mul, Nat.one_mul]
    have h2 := step n
    omega

/-- Hence the frontier is UNBOUNDED: for every bound `M`, some time exceeds it.
    A frontier-walking optimizer drives the admissible set to the whole space. -/
theorem frontier_unbounded
    (θ : Nat → Nat) (η : Nat) (hη : 1 ≤ η)
    (step : ∀ t, θ t + η ≤ θ (t+1)) :
    ∀ M, ∃ t, M ≤ θ t := by
  intro M
  refine ⟨M, ?_⟩
  have hmono := frontier_diverges θ η step M
  have hMη : M ≤ M * η := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hη   -- η = 1 + k
    have hexp : M * η = M + M * k := by
      rw [hk, Nat.mul_add, Nat.mul_one]
    omega
  omega

/-! ## Lemma 2 — self-attested evidence is unverifiable (near-definitional) -/

/-- Under C4 (`Acc` rejects self-attested evidence), if the only evidence for
    containment is the agent's own attestation, the evaluator cannot accept it.
    This is modus tollens on the C4 hypothesis — included for completeness. -/
theorem selfattest_unverifiable
    {Evidence : Type} {AccE selfAttested : Evidence → Prop}
    (C4 : ∀ e, selfAttested e → ¬ AccE e)
    {ev : Evidence} (hself : selfAttested ev) : ¬ AccE ev :=
  C4 ev hself

end Governed

/-
  NOT captured here (honest scope):
  • Lemma 1 (set-level/pre-action) is a timing argument over an execution model;
    its content is the latency/irreversibility setup, not a finite proposition.
  • T1's "infinite ⇒ inert (non-binding)" step encodes a semantics of "authority
    is exercised" that is a modeling choice, not formalized above. What IS checked:
    a top is not legitimate (dogmatic), self-grounding fails (cycle), and
    least-fixed-point legitimacy is empty (regress).
  • These are proofs RELATIVE to the definitions; they do not assert the
    constraints obtain in any real system.
-/
