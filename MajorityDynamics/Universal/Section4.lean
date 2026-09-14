import MajorityDynamics.Universal.ResponseSymmetry
import MajorityDynamics.Universal.Coherence
import MajorityDynamics.Universal.Nondegeneracy
import MajorityDynamics.Universal.ArrayIndependence
import MajorityDynamics.Analysis.GaussianSplit.Whitening

/-!
# Closed Section 4: the universal sequences and coherent response

`section4 : Section4Theorem` packages all Section 4 results for the actual
recursively constructed arrays. Every internal Gaussian, algebraic, symmetry,
and induction premise is supplied. There are no literature axioms or pending
mathematical inputs. The paper's day `k` is the array index `n = k - 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

/-- `thm:coherence`, with the analytic split theorem completely discharged. -/
theorem coherence (n : ℕ) (s : History (n + 1)) :
    0 < ε (n + 1) (append s false) ∧ ε (n + 1) (append s true) < 0 :=
  coherence_of_affine_split
    GaussianSplit.affine_positive_split n s

/-- Positive current lead, including the initial day where it equals two. -/
theorem ε_lead_positive (n : ℕ) :
    0 < ∑ t, character (Fin.last n) t * ε n t :=
  ε_lead_pos_of_affine_split
    GaussianSplit.affine_positive_split n

/-- All four clauses of `cor:sign-identities`, on the actual arrays. -/
structure SignIdentitiesTheorem : Prop where
  earlier : ∀ n (r : Fin n), ∑ t, character r.castSucc t * ε n t = 0
  total : ∀ n, ∑ t, ε n t = 0
  lead_formula : ∀ n, ∑ t, character (Fin.last n) t * ε n t =
    2 * ∑ s : History n, ε n (append s false)
  initial_lead : ∑ t, character (Fin.last 0) t * ε 0 t = 2
  lead_positive : ∀ n, 0 < ∑ t, character (Fin.last n) t * ε n t
  proportions : ∀ n r, ∑ t, character r t * ν n t = 0
  separation : ∀ n s (r : Fin n), 0 < sign (bits (n + 1) s r.succ) *
    imbalance r.castSucc (WithLp.toLp 2 (fun t => ν n t * μ n s t))

theorem sign_identities : SignIdentitiesTheorem where
  earlier := ε_earlier_signed_sum
  total := ε_sum_zero
  lead_formula := ε_lead_sum
  initial_lead := ε_initial_lead
  lead_positive := ε_lead_positive
  proportions := ν_signed_sum
  separation n s := (mem_historyCone s _).mp (weightedRow_mem n s)

/-- The complete Section 4 contract, including the Gaussian family and the
generic history-specific mean bijection as well as both recursions. -/
structure Section4Theorem : Prop where
  recursion : UniversalRecursionTheorem
  mean_bijection : ∀ (n : ℕ) (s : History (n + 1)) (v : History (n + 1) → ℝ),
    (∀ t, 0 < v t) →
      ∃ f : MajorityDynamics.StrongBijection (historyCone s), f.toFun = meanMap s v
  gaussian_coordinates : ∀ n (s t : History (n + 1)),
    MeasurePreserving (fun W : History (n + 1) → Row (n + 1) => W s t)
      (dayArrayLaw n) (gaussianReal (γ n s t) (ν n t).toNNReal)
  gaussian_independence : ∀ n,
    iIndepFun (fun p : History (n + 1) × History (n + 1) =>
      fun W : History (n + 1) → Row (n + 1) => W p.1 p.2) (dayArrayLaw n)
  initial_response : ∀ s, ε 0 s = sign (last s)
  beta_defining : ∀ n s t, ∑ u, β n s u * conditionalCovariance n s u t = ε n t
  beta_unique : ∀ n s (b : History (n + 1) → ℝ),
    (∀ t, ∑ u, b u * conditionalCovariance n s u t = ε n t) → b = β n s
  beta_covariance : ∀ n s t,
    ProbabilityTheory.covariance (B n s) (fun x => x t) (historyLaw n s) = ε n t
  response_recursion : ∀ n s b,
    ε (n + 1) (append s b) = ν (n + 1) (append s b) *
      ((∫ x, B n s x ∂childLaw n s b) - (∫ x, B n s x ∂historyLaw n s))
  sibling_cancellation : ∀ n s,
    ε (n + 1) (append s false) + ε (n + 1) (append s true) = 0
  response_flip : ∀ n s, ε n (flip s) = -ε n s
  beta_flip : ∀ n s t, β n (flip s) (flip t) = -β n s t
  coherent : ∀ n s,
    0 < ε (n + 1) (append s false) ∧ ε (n + 1) (append s true) < 0
  signs : SignIdentitiesTheorem
  nondegeneracy : ∀ n, UniversalNondegeneracy n (φStar n) (ζStar n)
  initial_separation_constant : ζStar 0 = 1

/-- Closed proof of every Section 4 obligation. -/
theorem section4 : Section4Theorem where
  recursion := main
  mean_bijection := @conditionalMean_bijection
  gaussian_coordinates n s t := arrayLaw_coordinate (ν n) (ν_positive n) (γ n) s t
  gaussian_independence := dayArrayLaw_independent_coordinates
  initial_response := ε_zero
  beta_defining := β_spec
  beta_unique := β_unique
  beta_covariance := B_covariance_coordinate
  response_recursion := ε_recursion
  sibling_cancellation := ε_siblings
  response_flip := ε_flip
  beta_flip := β_flip
  coherent := coherence
  signs := sign_identities
  nondegeneracy := universal_nondegeneracy
  initial_separation_constant := ζStar_zero

end MajorityDynamics.Universal
