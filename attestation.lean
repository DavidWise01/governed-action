/-
  Extensions to "Attestation and the Relocation of Exteriority".
  Lean 4 (no mathlib). Compile:  lean attestation.lean
  Machine-checks: the discharge of checking-exteriority (Thm A), the three
  relocation residues (i: spec, ii: root, iii: timing), the capstone sufficiency,
  and the IRREDUCIBILITY cores (zero exterior spec ⇒ vacuous certificate;
  zero exterior root ⇒ acceptance impossible). Honest scope in the footer.
-/

namespace Attestation

/-! ## Theorem A — sound attestation discharges *checking*-exteriority

   Containment (φ) follows from the verifier's acceptance under soundness,
   with NO hypothesis that the checker is exterior to the selector. The prover's
   identity does not appear, so the agent may run the prover itself.
   (Near-definitional, like L2; the weight is in the residues below.) -/
theorem discharge {accepts φ : Prop} (sound : accepts → φ) (h : accepts) : φ :=
  sound h

/-! ## Residue (i) — a self-chosen specification ratchets to vacuity

   Specs compared by an admissible-set map; a *weaker* spec admits at least as
   much. Agent value is monotone in the admissible set, so the agent's best under
   any spec is matched under the weaker (vacuous) spec: a self-specifying agent
   has no incentive to keep a binding spec. (This is the value-monotonicity
   ratchet, restated for spec-weakness.) -/
theorem spec_self_ratchets
    {A : Type} {u : A → Nat} {adm admWeaker : A → Prop}
    (weaker : ∀ a, adm a → admWeaker a)
    {aStar : A} (hin : adm aStar)
    (hmax : ∀ a, adm a → u a ≤ u aStar) :
    ∃ b, admWeaker b ∧ ∀ a, adm a → u a ≤ u b :=
  ⟨aStar, weaker aStar hin, hmax⟩

/-! ## Traces and containment (for residues iii and the capstone) -/

abbrev Trace (A : Type) := Nat → A

/-- Containment: every executed action is admissible. -/
def Contained {A : Type} (adm : A → Prop) (tr : Trace A) : Prop :=
  ∀ t, adm (tr t)

/-! ## Residue (i), irreducibility core — a vacuous spec certifies nothing

   If the agent controls the spec (zero exterior specification), residue (i)
   drives it to the vacuous predicate `fun _ => True`. That predicate is
   satisfied by EVERY trace — including one that violates the intended (strict)
   property. So a certificate against an agent-chosen spec carries no information
   about what the evaluator actually cared about. -/
theorem vacuous_certifies_nothing
    {A : Type} (admStrict : A → Prop) (tr : Trace A)
    (someViolation : ∃ t, ¬ admStrict (tr t)) :
    Contained (fun _ => True) tr ∧ ¬ Contained admStrict tr := by
  refine ⟨fun _ => trivial, ?_⟩
  obtain ⟨t₀, hv⟩ := someViolation
  intro h
  exact hv (h t₀)

/-! ## Residue (ii), irreducibility core — self-attested soundness collapses to C4

   E accepts evidence only if it is not self-attested (C4). If the SOUNDNESS of
   the verifier is itself only the agent's own attestation (zero exterior trust
   root), E cannot accept it, and the discharge chain breaks: acceptance is
   impossible, so no containment is verified. -/
theorem root_selfattested_fails
    {Ev : Type} {AccE selfAttested : Ev → Prop}
    (C4 : ∀ e, selfAttested e → ¬ AccE e)
    {soundnessClaim : Ev} (hself : selfAttested soundnessClaim) :
    ¬ AccE soundnessClaim :=
  C4 soundnessClaim hself

/-! ## Residue (iii) — detection after an irreversible act is too late;
       pre-action gating suffices -/

/-- PRE-ACTION SUFFICIENCY: if every executed action was admissible (gated before
    execution), containment holds. Feasible because (Lemma 1) the boundary is a
    fixed predicate, so "admissible" is cheap pre-action membership. -/
theorem preaction_sufficient
    {A : Type} (adm : A → Prop) (tr : Trace A)
    (gate : ∀ t, adm (tr t)) : Contained adm tr := by
  intro t; exact gate t

/-- POST-ACTION INSUFFICIENCY: containment is a property of the (already-fixed)
    trace; a verdict computed afterward is read-only on the trace and does not
    enter `Contained`, so it cannot make a violating trace contained. Here: a
    single violation already falsifies containment. -/
theorem postaction_insufficient
    {A : Type} (adm : A → Prop) (tr : Trace A)
    {t₀ : Nat} (violation : ¬ adm (tr t₀)) :
    ¬ Contained adm tr := by
  intro h; exact violation (h t₀)

/-! ## Relocation (capstone) — the three exterior conditions are sufficient

   Given an exterior/adequate spec `adm`, soundness usable because the trust root
   is exterior (`sound : accepts → ∀ t, adm (tr t)`, certifying the whole trace
   pre-action), and an acceptance `h`, containment follows. Necessity of each
   condition is the content of the three residue lemmas above. -/
theorem relocation
    {A : Type} (adm : A → Prop) (tr : Trace A)
    {accepts : Prop}
    (sound : accepts → (∀ t, adm (tr t)))
    (h : accepts) :
    Contained adm tr := by
  intro t; exact sound h t

end Attestation

/-
  Honest scope:
  • discharge (Thm A) and root_selfattested_fails are near-definitional
    (modus ponens / modus tollens on the soundness and C4 hypotheses).
  • spec_self_ratchets is the value-monotonicity ratchet (same proof as
    governance.lean's `value_monotone`), restated for specification-weakness.
  • vacuous_certifies_nothing is the SPEC irreducibility core: zero exterior
    specification ⇒ the certificate is empty (true of every trace, including a
    violating one). It does not, by itself, fix the magnitude (≥1 bit — modeled
    in the quantification note).
  • postaction_insufficient encodes "detection cannot undo" as: a violating trace
    is not contained, and the verdict does not appear in `Contained`. The full
    timing/latency execution model is not formalized (as in governance.lean).
  • relocation proves SUFFICIENCY of the three exterior conditions; necessity is
    carried by the residue lemmas, not bundled into one iff.
  • Proofs are relative to these definitions; none assert any real attestation
    scheme is sound, nor any real spec adequate.
-/
