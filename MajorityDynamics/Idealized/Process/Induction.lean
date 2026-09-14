import MajorityDynamics.Idealized.Process.Finite
import MajorityDynamics.Idealized.Process.Symmetry

/-! # Finite-horizon construction from the uniform analytic induction step -/

noncomputable section
open Filter
open scoped Topology

namespace MajorityDynamics.Idealized.Process

def initialData (N : ℕ) (p : Binomial.Probability) : Data where
  state
    | 0 => initialState N p
    | _ + 1 => ⟨fun _ => 0, fun _ _ => 0⟩
  tilt _ _ _ := p

theorem initialData_specification (N : ℕ) (p : Binomial.Probability)
    (h : LevelEstimates N p 1 (initialState N p)) :
    Specification N p 1 1 (initialData N p) where
  initial := rfl
  solvable n hn := by omega
  evolution n hn := by omega
  symmetry n hn := by
    have : n = 0 := by omega
    subst n
    exact initialState_symmetric N p
  tilt_symmetry n hn := by omega
  estimates n hn := by
    have : n = 0 := by omega
    subst n
    exact h
  tilt_estimates n hn := by omega

def Data.advance (a : Data) (n : ℕ) (q : Local.Tilt n) : Data where
  state := Function.update a.state (n + 1) (nextState (a.state n) q)
  tilt := Function.update a.tilt n q

theorem Specification.advance {N n ell ell' : ℕ} {p : Binomial.Probability}
    {a : Data} (h : Specification N p (n + 1) ell a)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hell : ell ≤ ell')
    (q : Local.Tilt n) (hsolve : Solvable (a.state n) q)
    (hqsym : TiltSymmetric q) (hqest : TiltEstimates N p ell' q)
    (hnextsym : StateSymmetric (nextState (a.state n) q))
    (hnextest : LevelEstimates N p ell' (nextState (a.state n) q)) :
    Specification N p (n + 2) ell' (a.advance n q) := by
  classical
  constructor
  · constructor
    · simpa [Data.advance] using h.initial
    · intro j hj
      by_cases he : j = n
      · subst j
        simpa [Data.advance] using hsolve
      · have hjn : j + 1 < n + 1 := by omega
        have hjs : j ≠ n + 1 := by omega
        simpa [Data.advance, he, hjs] using h.solvable j hjn
    · intro j hj
      by_cases he : j = n
      · subst j
        simp [Data.advance]
      · have hjn : j + 1 < n + 1 := by omega
        have hjs : j ≠ n + 1 := by omega
        have hjsucc : j + 1 ≠ n + 1 := by omega
        simpa [Data.advance, he, hjs, hjsucc] using h.evolution j hjn
  · intro j hj
    by_cases he : j = n + 1
    · subst j
      simpa [Data.advance] using hnextsym
    · have hjn : j < n + 1 := by omega
      simpa [Data.advance, he] using h.symmetry j hjn
  · intro j hj
    by_cases he : j = n
    · subst j
      simpa [Data.advance] using hqsym
    · have hjn : j + 1 < n + 1 := by omega
      simpa [Data.advance, he] using h.tilt_symmetry j hjn
  · intro j hj
    by_cases he : j = n + 1
    · subst j
      simpa [Data.advance] using hnextest
    · have hjn : j < n + 1 := by omega
      simpa [Data.advance, he] using (h.estimates j hjn).mono hlog hell
  · intro j hj
    by_cases he : j = n
    · subst j
      simpa [Data.advance] using hqest
    · have hjn : j + 1 < n + 1 := by omega
      simpa [Data.advance, he] using (h.tilt_estimates j hjn).mono hlog hell

/-- This structural reduction is supplied the internally proved analytic step
by `idealized_process`; it makes the uniformity and finite induction explicit.
-/
theorem idealized_process_of_step (step : OneStepTheorem) : IdealizedProcessTheorem := by
  intro θ hθlo hθhi D hD T hT
  have finite : ∀ d : ℕ, ∃ ell : ℕ, 1 ≤ ell ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability,
        Binomial.Approximation.Density θ T N p →
          ∃ a : Data, Specification N p (d + 1) ell a := by
    intro d
    induction d with
    | zero =>
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_initialState_estimates
      refine ⟨1, le_rfl, max N₀ 1, le_max_right _ _, ?_⟩
      intro N hN p _hp
      have hbase := hN₀ N ((le_max_left _ _).trans hN)
      exact ⟨initialData N p, initialData_specification N p (hbase.2.2 p)⟩
    | succ d ih =>
      obtain ⟨ell, hell, N₀, hN₀, hf⟩ := ih
      obtain ⟨ell', hell', N₁, _hN₁, hstep⟩ := step θ T hθlo hθhi hT d ell hell
      have hlog := (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
          (eventually_ge_atTop (1 : ℝ))
      obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hlog
      refine ⟨ell', hell.trans hell', max N₀ (max N₁ N₂),
        hN₀.trans (le_max_left _ _), ?_⟩
      intro N hN p hp
      have hn₀ : N₀ ≤ N := (le_max_left _ _).trans hN
      have hn₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
      have hn₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
      obtain ⟨a, ha⟩ := hf N hn₀ p hp
      obtain ⟨q, hq, hqsym, hqest, hnsym, hnest⟩ :=
        hstep N hn₁ p hp (a.state d) (ha.symmetry d (by omega)) (ha.estimates d (by omega))
      exact ⟨a.advance d q, ha.advance (hN₂ N hn₂) hell' q hq hqsym hqest hnsym hnest⟩
  obtain ⟨ell, hell, N₀, hN₀, hf⟩ := finite (D - 1)
  refine ⟨ell, hell, N₀, hN₀, ?_⟩
  intro N hN p hp
  obtain ⟨a, ha⟩ := hf N hN p hp
  have hd : D - 1 + 1 = D := by omega
  rw [hd] at ha
  exact ⟨a, ha, fun b hb => recursion_determined ha.toRecursion hb⟩

end MajorityDynamics.Idealized.Process
