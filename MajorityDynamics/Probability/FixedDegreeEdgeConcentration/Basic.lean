import MajorityDynamics.Probability.FixedDegreeSampling.Conditioning

noncomputable section
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open MajorityDynamics.Probability.FixedDegreeSampling

/-- Original sparse density interval. -/
def DensityWindow (θ T p : ℝ) (N : ℕ) : Prop :=
  T⁻¹ * (N : ℝ)^(-θ) < p ∧ p < T * (N : ℝ)^(-θ)

/-- The original C.1 graph hypotheses; no realization is assumed. -/
structure GraphInput {V : Type*} [Fintype V] (N m : ℕ) (p T : ℝ) (d : V → ℕ) : Prop where
  card : Fintype.card V = N
  bounded : ∀ v, d v ≤ N - 1
  total : ∑ v, d v = 2*m
  count_window : |(m : ℝ) - p*N*(N-1)/2| ≤ T*N^2*p/Real.sqrt (p*N)
  degree_window : ∀ v, |(d v : ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)

/-- Both sides use the same right-side degree-error scale, as in C.1. -/
structure BipartiteInput {L R : Type*} [Fintype L] [Fintype R]
    (ell N m : ℕ) (p T : ℝ) (a : L → ℕ) (b : R → ℕ) : Prop where
  card_left : Fintype.card L = ell
  card_right : Fintype.card R = N
  size_lower : (N : ℝ)/T ≤ ell
  size_upper : (ell : ℝ) ≤ T*N
  bounded_left : ∀ v, a v ≤ N
  bounded_right : ∀ w, b w ≤ ell
  total_left : ∑ v, a v = m
  total_right : ∑ w, b w = m
  count_window : |(m : ℝ)-p*ell*N| ≤ T*N^2*p/Real.sqrt (p*N)
  degree_left : ∀ v, |(a v : ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)
  degree_right : ∀ w, |(b w : ℝ)-p*ell| ≤ (p*N)^((4:ℝ)/7)

/-- The literal coefficient-one error threshold in C.1. -/
def edgeThreshold (N : ℕ) (p : ℝ) : ℝ :=
  (N : ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N

/-- A uniform marginal preparation class. Its dimension may differ from the
reference N (in particular after one vertex is removed). -/
structure GraphWindow {V : Type*} [Fintype V]
    (N n m : ℕ) (p K A : ℝ) (d : V → ℕ) : Prop where
  card : Fintype.card V = n
  size_lower : (N : ℝ)/K ≤ n
  size_upper : (n : ℝ) ≤ K*N
  bounded : ∀ v, d v ≤ n-1
  total : ∑ v, d v = 2*m
  degree_window : ∀ v, |(d v : ℝ)-p*N| ≤ A*(p*N)^((4:ℝ)/7)+1
  realized : (graphFamily d).Nonempty

/-- Reference-scale windows are stable under deleting either side. -/
structure BipartiteWindow {L R : Type*} [Fintype L] [Fintype R]
    (N ell n m : ℕ) (p K A : ℝ) (a : L → ℕ) (b : R → ℕ) : Prop where
  card_left : Fintype.card L = ell
  card_right : Fintype.card R = n
  size_left_lower : (N : ℝ)/K ≤ ell
  size_left_upper : (ell : ℝ) ≤ K*N
  size_right_lower : (N : ℝ)/K ≤ n
  size_right_upper : (n : ℝ) ≤ K*N
  bounded_left : ∀ v, a v ≤ n
  bounded_right : ∀ w, b w ≤ ell
  total_left : ∑ v, a v = m
  total_right : ∑ w, b w = m
  degree_left : ∀ v, |(a v : ℝ)-p*n| ≤ A*(p*N)^((4:ℝ)/7)+1
  degree_right : ∀ w, |(b w : ℝ)-p*ell| ≤ A*(p*N)^((4:ℝ)/7)+1
  realized : (bipartiteFamily a b).Nonempty

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
