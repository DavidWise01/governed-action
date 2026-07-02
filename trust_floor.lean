/-
  Information-theoretic trust floor for E_root.
  Lean 4 (no mathlib). Compile:  lean trust_floor.lean
  Machine-checks the COUNTING KERNEL of the guessing-attack reduction: if the
  best key-guessing forgery succeeds on ≥ 1 key, and soundness bounds any
  forgery to a 2^{-λ} fraction of the secret's support, then the support has
  size ≥ 2^λ — i.e. the secret's min-entropy is ≥ λ. E_root is DERIVED from the
  reduction's advantage bound, not assumed by an entropy count.
  The probabilistic statement (optimal guessing probability = 2^{-H_∞}, the
  general non-uniform min-entropy form) is standard analysis and lives in the
  companion note; here we check the uniform counting core.
-/

namespace TrustFloor

/-- THE REDUCTION KERNEL.
    `NK`     — size of the support of the soundness secret `K`.
    `lam`    — soundness parameter; error ε = 2^{-lam}.
    `fcount` — number of keys on which a given forgery strategy succeeds.
    Hypotheses:
    • `hguess : 1 ≤ fcount` — the guessing attack (guess `K`, forge with the
      guess) succeeds on at least the one matching key. Available to any
      adversary, so any optimal forgery does at least this well.
    • `hsound : fcount * 2^lam ≤ NK` — soundness: a forgery succeeds on at most
      a 2^{-lam} fraction of the support (`fcount ≤ NK / 2^lam`).
    Conclusion: `2^lam ≤ NK` — the secret's support is at least 2^lam, i.e.
    H_∞(K) ≥ lam. The trust floor falls out of the advantage bound. -/
theorem trust_floor (NK lam fcount : Nat)
    (hguess : 1 ≤ fcount)
    (hsound : fcount * 2 ^ lam ≤ NK) :
    2 ^ lam ≤ NK := by
  obtain ⟨f', hf'⟩ : ∃ f', fcount = f' + 1 := ⟨fcount - 1, by omega⟩
  have hexp : fcount * 2 ^ lam = f' * 2 ^ lam + 2 ^ lam := by
    rw [hf', Nat.add_mul, Nat.one_mul]
  omega

/-- Equivalently, in entropy form: soundness 2^{-lam} forces min-entropy ≥ lam.
    (Here `2^lam ≤ NK` is exactly `H_∞(K) = log₂ NK ≥ lam` for a uniform key.) -/
theorem min_entropy_floor (NK lam fcount : Nat)
    (hguess : 1 ≤ fcount)
    (hsound : fcount * 2 ^ lam ≤ NK) :
    2 ^ lam ≤ NK :=
  trust_floor NK lam fcount hguess hsound

/-- ATTAINABILITY (tightness). A uniform lam-bit one-time secret meets the floor:
    `NK = 2^lam`, `fcount = 1` satisfy the reduction's hypotheses — guessing
    succeeds on exactly 1 key, soundness `1 * 2^lam ≤ 2^lam` holds with EQUALITY,
    and the support is exactly `2^lam`. So `H_∞ = lam` is achievable and the
    bound is not loose (this is the one-time-MAC / random-pad case). -/
theorem trust_floor_attained (lam : Nat) :
    (1 ≤ (1 : Nat)) ∧ ((1 : Nat) * 2 ^ lam ≤ 2 ^ lam) ∧ (2 ^ lam = 2 ^ lam) := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Contrapositive, as an auditor's lever: if the secret's support is SMALLER
    than 2^lam, the claimed soundness 2^{-lam} is impossible — some forgery beats
    it. (A short key cannot back a strong soundness claim.) -/
theorem short_key_breaks_soundness (NK lam fcount : Nat)
    (hguess : 1 ≤ fcount)
    (hshort : NK < 2 ^ lam) :
    ¬ (fcount * 2 ^ lam ≤ NK) := by
  intro hsound
  have := trust_floor NK lam fcount hguess hsound
  omega

end TrustFloor

/-
  Honest scope:
  • LOAD-BEARING ASSUMPTION (named in the note): "an adversary who knows the
    secret K can forge." This holds for information-theoretic / secret-based
    soundness (MACs, designated-verifier, secret-coin proofs, TEE keys) — there
    the guessing attack is real and the floor H_∞(K|W) ≥ λ is derived. It does
    NOT hold for computationally-sound public-coin systems (SNARKs), where a
    key-knowing adversary still cannot forge without breaking a hardness
    assumption; that regime's trust floor is the ASSUMPTION, not bits of entropy
    (companion note §4).
  • The Lean checks the UNIFORM COUNTING core. The general statement — optimal
    guessing probability equals 2^{-H_∞(K|W)} for arbitrary (conditional)
    distributions — is standard and stated, not formalized (needs probability /
    measure machinery beyond core Lean).
  • The reduction assumes a correct guess can actually be turned into a forgery.
    For schemes where knowing K does not immediately yield a forgery, the bound
    is different/weaker.
  • Proofs are relative to these definitions; none assert any real scheme's
    soundness or secret distribution.
-/
